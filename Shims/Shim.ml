open Unix
open Util
open Misc
open Protocol
(* open Debug *)

(* Hashtables of size 17, obviously not ideal *)
let read_fds : (Unix.file_descr, coq_Address) Hashtbl.t = Hashtbl.create 17
let write_fds : (coq_Address, Unix.file_descr) Hashtbl.t = Hashtbl.create 17

type lstate = { 
            me: coq_Address;
            nodes : coq_Address list
           }

let the_lstate : lstate option ref = ref None
let listen_fd : file_descr = socket PF_INET SOCK_STREAM 0

let get_name_for_read_fd (fd: file_descr): coq_Address =
  Hashtbl.find read_fds fd

let send_chunk (fd : file_descr) (buf : bytes) : unit =
  let len = Bytes.length buf in
  let n = Unix.send fd (Util.raw_bytes_of_int len) 0 4 [] in
  if n < 4 then
    failwith "send_chunk: message header failed to send all at once.";
  let n = Unix.send fd buf 0 len [] in
  if n < len then
    failwith (Printf.sprintf "send_chunk: message of length %d failed to send all at once." len)

let recv_or_close (fd:file_descr) (buf:bytes) (offs: int) (len: int) (flags:msg_flag list): int =
  let n = recv fd buf offs len flags in
  if n = 0 then
    failwith "recv_or_close: other side closed connection.";
  n

let receive_chunk (fd : file_descr) : bytes =
  let buf4 = Bytes.make 4 '\x00' in
  let n = recv_or_close fd buf4 0 4 [] in
  if n < 4 then
    failwith "receive_chunk: message header did not arrive all at once.";
  let len = Util.int_of_raw_bytes buf4 in
  let buf = Bytes.make len '\x00' in
  let n = recv_or_close fd buf 0 len [] in
  if n < len then
    failwith
        (Printf.sprintf "receive_chunk: message of length %d did not arrive all at once." len);
  buf

let get_lstate (err_msg: string): lstate =
  match !the_lstate with
  | None -> failwith (err_msg ^ " called before the_lstate was set")
  | Some lstate -> lstate

let get_write_fd (node: coq_Address): file_descr =
  try Hashtbl.find write_fds node
  with Not_found ->
    let write_fd = socket PF_INET SOCK_STREAM 0 in
    let entry = gethostbyname node.ip in
    let node_addr = ADDR_INET (Array.get entry.h_addr_list 0, (int_of_nat node.port)) in
    connect write_fd node_addr;
    Hashtbl.add write_fds node write_fd;
    write_fd

let recv_data_msg (packet: coq_Packet): unit = 
  let src = packet.src in
  let msg = packet.msg in
  let lstate = get_lstate "recv_data_msg" in
  Printf.printf "Got data from (%s,%i) msg: %s\n" src.ip (int_of_nat src.port) (printHelp msg);
  Printf.printf "Me: (%s,%i)\n" lstate.me.ip (int_of_nat lstate.me.port)

(* Still need to implement hs = dom(bf) U {#tx|tx e tp} *)
let recv_connect_msg (packet: coq_Packet) (fd: file_descr): unit = 
  Hashtbl.add read_fds fd packet.src;
  let lstate = get_lstate "recv_connect_msg" in
  
  (* Debug *)
  Printf.printf "Length lstate.nodes: %i\n" (List.length lstate.nodes);
  (* End Debug *)
  
  if not (List.mem packet.src lstate.nodes) 
    then 
        the_lstate := Some {me = lstate.me; nodes = lstate.nodes @ [packet.src]};
  Printf.printf "done processing new connection from node (%s,%i)\n" packet.src.ip (int_of_nat packet.src.port)

let setup (lstate: lstate): unit =
  Printexc.record_backtrace true;
  the_lstate := Some lstate;
  Printf.printf "listening on port %d" (int_of_nat lstate.me.port); print_newline ();
  setsockopt listen_fd SO_REUSEADDR true;
  bind listen_fd (ADDR_INET (inet_addr_any, (int_of_nat lstate.me.port)));
  listen listen_fd 10

let get_all_read_fds (): file_descr list =
  Hashtbl.fold (fun fd _ acc -> fd :: acc) read_fds []
  
let serialize (packet: coq_Packet): bytes =
  Marshal.to_bytes packet []

let deserialize (s: bytes): coq_Packet =
  Marshal.from_bytes s 0

let recv_packet (fd: file_descr):coq_Packet =
  let chunk = receive_chunk fd in
  let packet = deserialize chunk in
  let src = packet.src in 
  let msg = printHelp packet.msg in
  Printf.printf "Packet recieved from (%s, %i). Msg: %s\n" src.ip (int_of_nat src.port) msg;
  packet

let send_packet (packet:coq_Packet): unit =
  let dst = packet.dst in
  Printf.printf "\nsending msg dst (%s,%i)\n" dst.ip (int_of_nat dst.port);
  let fd = get_write_fd dst in
  let serializedPacket = serialize packet in
  send_chunk fd serializedPacket

let recv_addr_msg (packet: coq_Packet) (addresses: coq_Address list): unit =
  let lstate = get_lstate "recv_addr_msg" in
  let locAddr = lstate.nodes in
  let lsDiff = List.filter (fun x -> not (List.mem x locAddr)) addresses in
  let unionAddr = locAddr @ lsDiff in 
  let ps1 = List.map (fun x -> {src = lstate.me; dst = x; msg= ConnectMsg}) lsDiff in
  let ps2 = List.map (fun x -> {src = lstate.me; dst = x; msg= AddrMsg (llist_to_dList unionAddr)}) unionAddr in
  let ps = ps1 @ ps2 in

  print_endline "------ Begin recv_addr_msg ------";
  print_endline "LocAddr\n";
  printAddrList (llist_to_dList locAddr);
  print_newline ();

  print_endline "lsDiff\n";
  printAddrList (llist_to_dList lsDiff);
  print_newline ();

  print_endline "unionAddr\n";
  printAddrList (llist_to_dList unionAddr);
  print_newline ();

  print_endline "------ End recv_addr_msg ------";
  the_lstate := Some {me = lstate.me; nodes = unionAddr};
  
  (* Send all packets that have been created *)
  List.iter (fun x -> send_packet x) ps

(* Add new message types here *)
let recv_msg (node_fd:file_descr): unit = 
  let packet = recv_packet node_fd in
  match packet.msg with
  | ConnectMsg -> recv_connect_msg packet node_fd
  | AddrMsg ls -> recv_addr_msg packet (dList_to_Llist ls)
  | GetDataMsg data -> recv_data_msg packet
  | _ -> print_endline "nothing matched"

(* Is used in 'check_for_new_connections' to iterate over list of file_descr *)
let new_conn (): unit =
  print_endline "new connection!";
  let (node_fd, _) = accept listen_fd in
  recv_msg node_fd

(* Deal with new connections *)
let check_for_new_connections () =
  let fds = [listen_fd] in
  let (ready_fds, _, _) = select fds [] [] 0.0 in
  Printf.printf "Length of ready_fds: %i\n" (List.length ready_fds);
  List.iter (fun _ -> new_conn ()) ready_fds    

(* Close sockets *)

let closeSockets () =
  let rfds = get_all_read_fds () in
  List.iter (close) rfds;
  close listen_fd