//! PdfCraft patch: receive local files through the core Wayland data-device protocol (#634).
//!
//! Preserve winit 0.30's file events. Unlike SCTK 0.19's data-device delegation, this receiver
//! owns offers until their asynchronous reads finish, even after another drag enters. No clipboard
//! implementation is installed: selection offers on this connection are discarded.

use std::io;
use std::os::fd::AsFd;
use std::os::unix::ffi::OsStringExt;
use std::path::PathBuf;
use std::time::Duration;

use ahash::AHashMap;
use calloop::generic::Generic;
use calloop::timer::{TimeoutAction, Timer};
use calloop::{Interest, Mode, PostAction, RegistrationToken};
use rustix::pipe::{pipe_with, PipeFlags};
use sctk::compositor::SurfaceData;
use sctk::globals::GlobalData;
use sctk::reexports::client::backend::ObjectId;
use sctk::reexports::client::globals::GlobalList;
use sctk::reexports::client::protocol::wl_data_device::{self, WlDataDevice};
use sctk::reexports::client::protocol::wl_data_device_manager::{DndAction, WlDataDeviceManager};
use sctk::reexports::client::protocol::wl_data_offer::{self, WlDataOffer};
use sctk::reexports::client::{
    event_created_child, Connection, Dispatch, Proxy, QueueHandle, WEnum,
};
use tracing::warn;

use crate::dpi::LogicalPosition;
use crate::event::WindowEvent;
use crate::platform_impl::wayland::state::WinitState;
use crate::platform_impl::wayland::{self, DeviceId, WindowId};

const URI_LIST: &str = "text/uri-list";
const MAX_URI_LIST: usize = 1024 * 1024;
const MAX_FILES: usize = 1024;
const MAX_OFFERS: usize = 16;
const TRANSFER_TIMEOUT: Duration = Duration::from_secs(30);

pub struct DndState {
    pub manager: Option<WlDataDeviceManager>,
    offers: AHashMap<ObjectId, Offer>,
}

impl DndState {
    pub fn new(globals: &GlobalList, qh: &QueueHandle<WinitState>) -> Self {
        Self { manager: globals.bind(qh, 1..=3, GlobalData).ok(), offers: AHashMap::default() }
    }

    fn active(&self, device: &WlDataDevice) -> Option<ObjectId> {
        self.offers.iter().find_map(|(id, offer)| {
            (offer.device == device.id() && offer.window.is_some() && !offer.data.dropped)
                .then(|| id.clone())
        })
    }
}

struct Offer {
    proxy: WlDataOffer,
    device: ObjectId,
    uri_list: bool,
    source_actions: DndAction,
    action: DndAction,
    window: Option<WindowId>,
    data: TransferData,
    reader: Option<RegistrationToken>,
    timeout: Option<RegistrationToken>,
}

impl Offer {
    fn new(proxy: WlDataOffer, device: ObjectId) -> Self {
        Self {
            proxy,
            device,
            uri_list: false,
            source_actions: DndAction::empty(),
            action: DndAction::empty(),
            window: None,
            data: TransferData::default(),
            reader: None,
            timeout: None,
        }
    }

    fn copy_selected(&self) -> bool {
        // Before protocol version 3 all drag-and-drop operations have implicit Copy semantics.
        self.proxy.version() < 3
            || (self.action == DndAction::Copy && self.source_actions.contains(DndAction::Copy))
    }

    fn read_finished(&mut self, handle: &calloop::LoopHandle<'_, WinitState>) {
        // The reader callback removes itself on return; never remove it reentrantly.
        self.reader = None;
        // The deadline bounds the read, not the user's time hovering over a window.
        if let Some(token) = self.timeout.take() {
            handle.remove(token);
        }
    }
}

#[derive(Default)]
struct TransferData {
    bytes: Vec<u8>,
    paths: Option<Vec<PathBuf>>,
    dropped: bool,
}

impl TransferData {
    fn append(&mut self, bytes: &[u8]) -> io::Result<()> {
        if bytes.len() > MAX_URI_LIST.saturating_sub(self.bytes.len()) {
            return Err(io::Error::new(io::ErrorKind::InvalidData, "file URI list exceeds 1 MiB"));
        }
        self.bytes
            .try_reserve(bytes.len())
            .map_err(|error| io::Error::new(io::ErrorKind::Other, error))?;
        self.bytes.extend_from_slice(bytes);
        Ok(())
    }

    fn read_done(&mut self) -> bool {
        self.paths = parse_uri_list(&self.bytes);
        self.bytes = Vec::new();
        self.paths.is_some()
    }

    fn take_drop(&mut self) -> Option<Vec<PathBuf>> {
        if self.dropped {
            self.paths.take()
        } else {
            None
        }
    }
}

impl WinitState {
    fn dnd_cursor(&mut self, id: &ObjectId, x: f64, y: f64) {
        if !x.is_finite() || !y.is_finite() {
            return;
        }
        let Some(window_id) = self.dnd.offers.get(id).and_then(|offer| offer.window) else {
            return;
        };
        let Some(window) = self.windows.get_mut().get(&window_id) else { return };
        // A poisoned or temporarily held window lock must not kill or stall a file transfer.
        let Ok(window) = window.try_lock() else { return };
        let scale = window.scale_factor();
        if !scale.is_finite() || scale <= 0.0 {
            return;
        }
        let position = LogicalPosition::new(x, y).to_physical(scale);
        drop(window);
        let device_id = crate::event::DeviceId(crate::platform_impl::DeviceId::Wayland(DeviceId));
        self.events_sink
            .push_window_event(WindowEvent::CursorMoved { device_id, position }, window_id);
        self.dispatched_events = true;
    }

    fn dnd_hover(&mut self, window: WindowId) {
        if !self.windows.get_mut().contains_key(&window) {
            return;
        }
        // egui clears ALL hovered paths on a drop/cancel. Rebuild the current hover when an older
        // asynchronous drop completes, so it cannot clear a newer drag's hover or duplicate paths.
        self.events_sink.push_window_event(WindowEvent::HoveredFileCancelled, window);
        for offer in self.dnd.offers.values() {
            if offer.window == Some(window) && !offer.data.dropped && offer.copy_selected() {
                if let Some(paths) = &offer.data.paths {
                    for path in paths {
                        self.events_sink
                            .push_window_event(WindowEvent::HoveredFile(path.clone()), window);
                    }
                }
            }
        }
        self.dispatched_events = true;
    }

    fn dnd_remove(&mut self, id: &ObjectId, finish: bool) {
        let Some(mut offer) = self.dnd.offers.remove(id) else { return };
        if let Some(token) = offer.reader.take() {
            self.loop_handle.remove(token);
        }
        if let Some(token) = offer.timeout.take() {
            self.loop_handle.remove(token);
        }
        if offer.proxy.is_alive() {
            if finish && offer.data.dropped && offer.copy_selected() && offer.proxy.version() >= 3 {
                offer.proxy.finish();
            }
            offer.proxy.destroy();
        }
        if let Some(window) = offer.window {
            self.dnd_hover(window);
            if !finish
                && !offer.data.dropped
                && self.windows.get_mut().contains_key(&window)
                && !self
                    .dnd
                    .offers
                    .values()
                    .any(|other| other.window == Some(window) && !other.data.dropped)
            {
                // wl_pointer does not report target motion/leave while a drag owns it. Clear our
                // synthetic position on cancellation, including read failures before Leave.
                let device_id =
                    crate::event::DeviceId(crate::platform_impl::DeviceId::Wayland(DeviceId));
                self.events_sink.push_window_event(WindowEvent::CursorLeft { device_id }, window);
                self.dispatched_events = true;
            }
        }
    }

    pub(crate) fn dnd_remove_device(&mut self, device: &WlDataDevice) {
        let ids: Vec<_> = self
            .dnd
            .offers
            .iter()
            .filter(|(_, offer)| offer.device == device.id())
            .map(|(id, _)| id.clone())
            .collect();
        for id in ids {
            self.dnd_remove(&id, false);
        }
    }

    pub(crate) fn dnd_remove_window(&mut self, window: WindowId) {
        let ids: Vec<_> = self
            .dnd
            .offers
            .iter()
            .filter(|(_, offer)| offer.window == Some(window))
            .map(|(id, _)| id.clone())
            .collect();
        for id in ids {
            self.dnd_remove(&id, false);
        }
    }

    fn dnd_deliver(&mut self, id: &ObjectId) {
        let Some(offer) = self.dnd.offers.get_mut(id) else { return };
        if !offer.copy_selected() {
            // Only Copy is supported; never leave a completed, rejected drop without a reader
            // or deadline if the compositor sends an unexpected action change after Drop.
            if offer.data.dropped {
                self.dnd_remove(id, false);
            }
            return;
        }
        let Some(paths) = offer.data.take_drop() else { return };
        let window = offer.window.filter(|window| self.windows.get_mut().contains_key(window));
        if let Some(window) = window {
            for path in paths {
                self.events_sink.push_window_event(WindowEvent::DroppedFile(path), window);
            }
            self.dispatched_events = true;
        }
        self.dnd_remove(id, window.is_some());
    }

    fn dnd_read(&mut self, id: &ObjectId) -> io::Result<()> {
        let (read, write) = pipe_with(PipeFlags::CLOEXEC)?;
        // Set ONLY the receiving end nonblocking; a source may use ordinary blocking writes.
        rustix::io::ioctl_fionbio(&read, true)?;
        let key = id.clone();
        let reader = self
            .loop_handle
            .insert_source(
                Generic::new(read, Interest::READ, Mode::Level),
                move |_, pipe, state: &mut WinitState| {
                    if !state.dnd.offers.contains_key(&key) {
                        return Ok(PostAction::Remove);
                    }
                    let mut chunk = [0; 8192];
                    let result = match rustix::io::read(&*pipe, &mut chunk) {
                        Ok(0) => None,
                        Ok(n) => {
                            let result = chunk
                                .get(..n)
                                .ok_or_else(|| {
                                    io::Error::new(
                                        io::ErrorKind::InvalidData,
                                        "invalid file transfer read length",
                                    )
                                })
                                .and_then(|bytes| match state.dnd.offers.get_mut(&key) {
                                    Some(offer) => offer.data.append(bytes),
                                    None => Ok(()),
                                });
                            Some(result)
                        },
                        Err(rustix::io::Errno::AGAIN | rustix::io::Errno::INTR) => {
                            return Ok(PostAction::Continue)
                        },
                        Err(error) => Some(Err(error.into())),
                    };
                    if matches!(result, Some(Ok(()))) {
                        return Ok(PostAction::Continue);
                    }
                    if let Some(offer) = state.dnd.offers.get_mut(&key) {
                        offer.read_finished(&state.loop_handle);
                    }
                    match result {
                        None => {
                            let ready = state.dnd.offers.get_mut(&key).and_then(|offer| {
                                offer.data.read_done().then_some((offer.window, offer.data.dropped))
                            });
                            match ready {
                                Some((_, true)) => state.dnd_deliver(&key),
                                Some((Some(window), false)) => state.dnd_hover(window),
                                _ => state.dnd_remove(&key, false),
                            }
                        },
                        Some(Err(error)) => {
                            warn!("Wayland file drop: {error}");
                            state.dnd_remove(&key, false);
                        },
                        Some(Ok(())) => {},
                    }
                    Ok(PostAction::Remove)
                },
            )
            .map_err(|error| error.error)?;
        if let Some(offer) = self.dnd.offers.get_mut(id) {
            offer.reader = Some(reader);
            offer.proxy.receive(URI_LIST.to_owned(), write.as_fd());
        }
        let key = id.clone();
        let timeout = self
            .loop_handle
            .insert_source(
                Timer::from_duration(TRANSFER_TIMEOUT),
                move |_, _, state: &mut WinitState| {
                    if let Some(offer) = state.dnd.offers.get_mut(&key) {
                        offer.timeout = None;
                        warn!("Wayland file drop: transfer timed out");
                    }
                    state.dnd_remove(&key, false);
                    TimeoutAction::Drop
                },
            )
            .map_err(|error| error.error)?;
        if let Some(offer) = self.dnd.offers.get_mut(id) {
            offer.timeout = Some(timeout);
        }
        Ok(())
    }
}

impl Dispatch<WlDataDeviceManager, GlobalData> for WinitState {
    fn event(
        _: &mut Self,
        _: &WlDataDeviceManager,
        _: <WlDataDeviceManager as Proxy>::Event,
        _: &GlobalData,
        _: &Connection,
        _: &QueueHandle<Self>,
    ) {
    }
}

impl Dispatch<WlDataDevice, ()> for WinitState {
    event_created_child!(WinitState, WlDataDevice, [0 => (WlDataOffer, ())]);

    fn event(
        state: &mut Self,
        device: &WlDataDevice,
        event: wl_data_device::Event,
        _: &(),
        _: &Connection,
        _: &QueueHandle<Self>,
    ) {
        match event {
            wl_data_device::Event::DataOffer { id } => {
                if state.dnd.offers.len() >= MAX_OFFERS {
                    warn!("Wayland file drop: too many pending offers");
                    id.destroy();
                    return;
                }
                state.dnd.offers.insert(id.id(), Offer::new(id, device.id()));
            },
            wl_data_device::Event::Enter { serial, surface, x, y, id } => {
                if let Some(old) = state.dnd.active(device) {
                    state.dnd_remove(&old, false);
                }
                let Some(proxy) = id else { return };
                let key = proxy.id();
                let parent = surface
                    .data::<SurfaceData>()
                    .and_then(|data| data.parent_surface())
                    .unwrap_or(&surface);
                let window = wayland::make_wid(parent);
                let Some(offer) = state.dnd.offers.get_mut(&key) else { return };
                if offer.device != device.id()
                    || !offer.uri_list
                    || (proxy.version() >= 3 && !offer.source_actions.contains(DndAction::Copy))
                    || !state.windows.get_mut().contains_key(&window)
                {
                    proxy.accept(serial, None);
                    state.dnd_remove(&key, false);
                    return;
                }
                offer.window = Some(window);
                proxy.accept(serial, Some(URI_LIST.to_owned()));
                if proxy.version() >= 3 {
                    proxy.set_actions(DndAction::Copy, DndAction::Copy);
                }
                if let Err(error) = state.dnd_read(&key) {
                    warn!("Wayland file drop: cannot receive URI list: {error}");
                    state.dnd_remove(&key, false);
                    return;
                }
                state.dnd_cursor(&key, x, y);
            },
            wl_data_device::Event::Motion { x, y, .. } => {
                if let Some(id) = state.dnd.active(device) {
                    state.dnd_cursor(&id, x, y);
                }
            },
            wl_data_device::Event::Leave => {
                if let Some(id) = state.dnd.active(device) {
                    state.dnd_remove(&id, false);
                }
            },
            wl_data_device::Event::Drop => {
                if let Some(id) = state.dnd.active(device) {
                    if let Some(offer) = state.dnd.offers.get_mut(&id) {
                        if !offer.copy_selected() {
                            state.dnd_remove(&id, false);
                            return;
                        }
                        offer.data.dropped = true;
                    }
                    state.dnd_deliver(&id);
                }
            },
            wl_data_device::Event::Selection { id: Some(offer) } => {
                state.dnd_remove(&offer.id(), false)
            },
            _ => {},
        }
    }
}

impl Dispatch<WlDataOffer, ()> for WinitState {
    fn event(
        state: &mut Self,
        proxy: &WlDataOffer,
        event: wl_data_offer::Event,
        _: &(),
        _: &Connection,
        _: &QueueHandle<Self>,
    ) {
        let Some(offer) = state.dnd.offers.get_mut(&proxy.id()) else { return };
        match event {
            wl_data_offer::Event::Offer { mime_type } => offer.uri_list |= mime_type == URI_LIST,
            wl_data_offer::Event::SourceActions { source_actions } => {
                offer.source_actions = match source_actions {
                    WEnum::Value(actions) => actions,
                    WEnum::Unknown(_) => DndAction::empty(),
                };
            },
            wl_data_offer::Event::Action { dnd_action } => {
                offer.action = match dnd_action {
                    WEnum::Value(action) => action,
                    WEnum::Unknown(_) => DndAction::empty(),
                };
                if let Some(window) = offer.window {
                    state.dnd_hover(window);
                }
            },
            _ => {},
        }
    }
}

/// Decode local file URIs without interpreting filename bytes as UTF-8 or trimming their spaces.
fn parse_uri_list(data: &[u8]) -> Option<Vec<PathBuf>> {
    if data.len() > MAX_URI_LIST {
        return None;
    }
    let mut paths = Vec::new();
    for line in data.split(|byte| *byte == b'\n') {
        let line = line.strip_suffix(b"\r").unwrap_or(line);
        if line.is_empty() || line.starts_with(b"#") {
            continue;
        }
        if let Some(path) = file_uri(line) {
            if paths.len() == MAX_FILES {
                return None;
            }
            paths.push(path);
        }
    }
    (!paths.is_empty()).then_some(paths)
}

fn file_uri(uri: &[u8]) -> Option<PathBuf> {
    let mut parts = uri.splitn(2, |byte| *byte == b':');
    if !parts.next()?.eq_ignore_ascii_case(b"file") {
        return None;
    }
    let mut path = parts.next()?;
    if let Some(rest) = path.strip_prefix(b"//") {
        let slash = rest.iter().position(|byte| *byte == b'/')?;
        let host = rest.get(..slash)?;
        if !host.is_empty() && !host.eq_ignore_ascii_case(b"localhost") {
            return None;
        }
        path = rest.get(slash..)?;
    }
    if !path.starts_with(b"/") || path.iter().any(|byte| matches!(byte, 0..=31 | 127 | b'?' | b'#'))
    {
        return None;
    }
    let mut decoded = Vec::new();
    decoded.try_reserve(path.len()).ok()?;
    let mut bytes = path.iter().copied();
    while let Some(byte) = bytes.next() {
        let byte = if byte == b'%' {
            let high = (bytes.next()? as char).to_digit(16)?;
            let low = (bytes.next()? as char).to_digit(16)?;
            u8::try_from(high * 16 + low).ok()?
        } else {
            byte
        };
        if byte == 0 {
            return None;
        }
        decoded.push(byte);
    }
    Some(PathBuf::from(std::ffi::OsString::from_vec(decoded)))
}

#[cfg(test)]
mod tests {
    use super::*;
    use sctk::reexports::client::protocol::wl_registry::WlRegistry;
    use std::os::unix::ffi::OsStrExt;

    // Allocate distinct typed proxy identities on a socket whose peer never dispatches. This
    // exercises the real offer map without a compositor, a WinitState, or a new test dependency.
    impl Dispatch<WlRegistry, ()> for WinitState {
        fn event(
            _: &mut Self,
            _: &WlRegistry,
            _: <WlRegistry as Proxy>::Event,
            _: &(),
            _: &Connection,
            _: &QueueHandle<Self>,
        ) {
        }
    }

    #[test]
    fn leaving_a_new_drag_preserves_an_older_drop_waiting_for_eof() {
        let (socket, _peer) = std::os::unix::net::UnixStream::pair().unwrap();
        let connection = Connection::from_socket(socket).unwrap();
        let queue = connection.new_event_queue::<WinitState>();
        let qh = queue.handle();
        let registry = connection.display().get_registry(&qh, ());
        let device: WlDataDevice = registry.bind(1, 3, &qh, ());
        let first: WlDataOffer = registry.bind(2, 3, &qh, ());
        let second: WlDataOffer = registry.bind(3, 3, &qh, ());
        let first_id = first.id();
        let second_id = second.id();
        assert_ne!(first_id, second_id);
        let mut old = Offer::new(first, device.id());
        assert!(!old.copy_selected());
        old.action = DndAction::Move;
        old.source_actions = DndAction::Copy | DndAction::Move;
        assert!(!old.copy_selected(), "never deliver a negotiated Move");
        old.action = DndAction::Copy;
        assert!(old.copy_selected());
        old.window = Some(WindowId(1));
        old.data.dropped = true;
        old.data.append(b"file:///tmp/old").unwrap();
        let mut state = DndState { manager: None, offers: AHashMap::default() };
        state.offers.insert(first_id.clone(), old);
        assert_eq!(state.active(&device), None, "a dropped transfer is no longer the active drag");
        let mut new = Offer::new(second, device.id());
        new.window = Some(WindowId(1));
        new.data.append(b"file:///tmp/new.pdf\n").unwrap();
        assert!(new.data.read_done());
        state.offers.insert(second_id.clone(), new);
        assert_eq!(state.active(&device), Some(second_id.clone()));
        // Leave selects only the current hover, retaining the previous drop and its own bytes.
        state.offers.remove(&state.active(&device).unwrap());
        assert_eq!(state.active(&device), None);
        let old = state.offers.get_mut(&first_id).unwrap();
        old.data.append(b".pdf\n").unwrap();
        assert!(old.data.read_done());
        assert_eq!(old.data.take_drop(), Some(vec![PathBuf::from("/tmp/old.pdf")]));
        assert!(old.data.take_drop().is_none());
    }

    #[test]
    fn completed_hover_disarms_its_read_deadline() {
        let (socket, _peer) = std::os::unix::net::UnixStream::pair().unwrap();
        let connection = Connection::from_socket(socket).unwrap();
        let proxy = WlDataOffer::inert(connection.backend().downgrade());
        let mut offer = Offer::new(proxy, ObjectId::null());
        let event_loop = calloop::EventLoop::<WinitState>::try_new().unwrap();
        let handle = event_loop.handle();
        let token =
            handle.insert_source(Timer::immediate(), |_, _, _| TimeoutAction::Drop).unwrap();
        offer.timeout = Some(token);
        offer.data.append(b"file:///tmp/hover.pdf\n").unwrap();
        assert!(offer.data.read_done());
        offer.read_finished(&handle);
        assert!(offer.timeout.is_none());
        assert!(
            handle.disable(&token).is_err(),
            "the timer must be unregistered, not just forgotten"
        );
        assert!(offer.data.paths.is_some(), "a completed hover remains valid until drop or leave");
        assert!(offer.data.take_drop().is_none(), "hovering must not open the file");
    }

    #[test]
    fn local_files_keep_order_spaces_unicode_and_percent_bytes() {
        let paths = parse_uri_list(b"# files\r\nfile:///tmp/one.pdf\r\nfile://LOCALHOST/tmp/drop%20%C3%BC%20b.pdf\nFILE:/tmp/%2520%23%3F.pdf\nfile:///tmp/last.pdf \r\n").unwrap();
        assert_eq!(
            paths,
            ["/tmp/one.pdf", "/tmp/drop ü b.pdf", "/tmp/%20#?.pdf", "/tmp/last.pdf "]
                .map(PathBuf::from)
        );
        assert_eq!(
            parse_uri_list("file:///tmp/生 ü.pdf\n".as_bytes()),
            Some(vec![PathBuf::from("/tmp/生 ü.pdf")])
        );
    }

    #[test]
    fn encoded_delimiters_are_filename_bytes_not_list_or_uri_syntax() {
        assert_eq!(
            parse_uri_list(b"file:///tmp/%0A%0D%23%3F%25.pdf\r\n"),
            Some(vec![PathBuf::from("/tmp/\n\r#?%.pdf")])
        );
    }

    #[test]
    fn non_utf8_filename_bytes_are_not_replaced() {
        let paths = parse_uri_list(b"file:///tmp/%FF.pdf\nfile:///tmp/raw\xfe.pdf\n").unwrap();
        assert_eq!(paths[0].as_os_str().as_bytes(), b"/tmp/\xff.pdf");
        assert_eq!(paths[1].as_os_str().as_bytes(), b"/tmp/raw\xfe.pdf");
    }

    #[test]
    fn malformed_remote_and_non_file_entries_are_ignored() {
        let invalid = b"https://example.org/a.pdf\nfile://remote/tmp/a.pdf\nfile://user@localhost/tmp/a.pdf\nfile:relative.pdf\nfile:///tmp/%00.pdf\nfile:///tmp/bad%2\nfile:///tmp/bad%GG\nfile:///tmp/a?query\nfile:///tmp/a#fragment\nfile:///tmp/raw\0.pdf\n";
        assert!(parse_uri_list(invalid).is_none());
        let mut mixed = invalid.to_vec();
        mixed.extend_from_slice(b"file:///tmp/valid.pdf\n");
        assert_eq!(parse_uri_list(&mixed), Some(vec![PathBuf::from("/tmp/valid.pdf")]));
    }

    #[test]
    fn uri_bytes_and_file_counts_are_bounded() {
        let mut transfer = TransferData::default();
        transfer.append(&vec![b'#'; MAX_URI_LIST]).unwrap();
        assert!(transfer.append(b"x").is_err());
        assert_eq!(transfer.bytes.len(), MAX_URI_LIST);
        assert!(parse_uri_list(&vec![b'x'; MAX_URI_LIST + 1]).is_none());
        let list = b"file:///tmp/a.pdf\n".repeat(MAX_FILES);
        assert_eq!(parse_uri_list(&list).unwrap().len(), MAX_FILES);
        assert!(parse_uri_list(&b"file:///tmp/a.pdf\n".repeat(MAX_FILES + 1)).is_none());
    }

    #[test]
    fn a_drop_waits_for_eof_and_can_be_taken_only_once() {
        let mut transfer = TransferData { dropped: true, ..Default::default() };
        transfer.append(b"file:///tmp/drop%20").unwrap();
        assert!(transfer.take_drop().is_none());
        transfer.append(b"%C3%BC.pdf\n").unwrap();
        assert!(transfer.read_done());
        assert!(transfer.bytes.is_empty());
        assert_eq!(transfer.take_drop(), Some(vec![PathBuf::from("/tmp/drop ü.pdf")]));
        assert!(transfer.take_drop().is_none());
    }

    #[test]
    fn reading_during_hover_does_not_open_a_file() {
        let mut transfer = TransferData::default();
        transfer.append(b"file:///tmp/a.pdf\n").unwrap();
        assert!(transfer.read_done());
        assert!(transfer.take_drop().is_none());
        transfer.dropped = true;
        assert!(transfer.take_drop().is_some());
    }

    #[test]
    fn nonblocking_pipe_reports_would_block_then_data_then_eof() {
        let (read, write) = pipe_with(PipeFlags::CLOEXEC).unwrap();
        rustix::io::ioctl_fionbio(&read, true).unwrap();
        let mut bytes = [0; 4];
        assert_eq!(rustix::io::read(&read, &mut bytes), Err(rustix::io::Errno::AGAIN));
        rustix::io::write(&write, b"data").unwrap();
        assert_eq!(rustix::io::read(&read, &mut bytes).unwrap(), 4);
        assert_eq!(&bytes, b"data");
        drop(write);
        assert_eq!(rustix::io::read(&read, &mut bytes).unwrap(), 0);
    }
}
