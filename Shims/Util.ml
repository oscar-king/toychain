open Misc
(* type procAddress = mkAddr {
  ip: string;
  port: int
} *)

type procAddress = coq_Address

type procMessage = 
  | NullMsg
  | ConnectMsg 
  | AddrMsg of (procAddress list)
  | DataMsg of string

type procPacket = {
  src:procAddress;
  dst:procAddress;
  msg:procMessage
  }

type nat =
| O
| S of nat

let printAddrList ls = 
  List.iter (fun x -> Printf.printf "Address:\t (%s,%i)\n" x.ip x.port) ls

let printHelp (msg: procMessage)= 
  match msg with
 | ConnectMsg -> "ConnectMsg"
 | AddrMsg ls -> "AddrMsg"
 | DataMsg a -> a
 | NullMsg -> "NullMsg"

let rec add n m =
  match n with
  | O -> m
  | S p -> S (add p m)

(** val mul : nat -> nat -> nat **)

let rec mul n m =
  match n with
  | O -> O
  | S p -> add m (mul p m)

let int_natlike_rec = fun fO fS ->
 let rec loop acc i = if i <= 0 then acc else loop (fS acc) (i-1)
 in loop fO

let nat_of_int =
  int_natlike_rec O (fun x -> S x)

let int_of_nat =
  let rec loop acc = function
  | O -> acc
  | S n0 -> loop (succ acc) n0
  in loop 0

let nat_of_string s = nat_of_int (int_of_string s)
let string_of_nat n = string_of_int (int_of_nat n)

let raw_bytes_of_int (x : int) : bytes =
  let buf = Bytes.make 4 '\x00' in
  Bytes.set buf 0 (char_of_int (x land 0xff));
  Bytes.set buf 1 (char_of_int ((x lsr 8) land 0xff));
  Bytes.set buf 2 (char_of_int ((x lsr 16) land 0xff));
  Bytes.set buf 3 (char_of_int ((x lsr 24) land 0xff));
  buf

let int_of_raw_bytes (buf : bytes) : int =
   (int_of_char (Bytes.get buf 0)) lor
  ((int_of_char (Bytes.get buf 1)) lsl 8) lor
  ((int_of_char (Bytes.get buf 2)) lsl 16) lor
  ((int_of_char (Bytes.get buf 3)) lsl 24)

let print_list (a_printer : out_channel -> 'a -> unit) (f : out_channel) (l : 'a list) =
  let rec go f = function
    | [] ->  ()
    | [a] ->  a_printer f a
    | a :: l -> Printf.fprintf f "%a; " a_printer a; go f l
  in Printf.fprintf f "[%a]" go l

let getIP = function
    | (_,(x,_)) -> Some x
    | _ -> None

let getPort = function
    | (_,(_,x)) -> Some x
    | _ -> None

let getName = function
    | (x,(_,_)) -> Some x
    | _ -> None