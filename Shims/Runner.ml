open Wrappers
open Util
open Shim
open Misc

let aux lstate = 
    let me = lstate in
    match (int_of_nat me.me.port) with
        | 9001 -> send_action_wrapper {src = me.me; dst = {ip = (127,0,0,1); port = nat_of_int 9002}; msg = ConnectMsg}
        | 9002 -> send_action_wrapper {src = me.me; dst = {ip = (127,0,0,1); port = nat_of_int 9003}; msg = ConnectMsg};
                  send_action_wrapper {src = me.me; dst = {ip = (127,0,0,1); port = nat_of_int 9001}; msg = AddrMsg (llist_to_dList me.nodes)};
                  send_action_wrapper {src = me.me; dst = {ip = (127,0,0,1); port = nat_of_int 9003}; msg = AddrMsg (llist_to_dList me.nodes)};
        | 9003 -> send_action_wrapper {src = me.me; dst = me.me; msg = ConnectMsg};
        | _ -> send_action_wrapper {src = me.me; dst = me.me; msg = ConnectMsg}

let node_run () = 
    let counter = ref 0 in
    let lstate = get_lstate "node_run" in
    let _ = tryrecv_action_wrapper () in
    aux lstate;
    let _ = tryrecv_action_wrapper () in
    while !counter<10 do 
        Unix.sleep 1;
        let _ = tryrecv_action_wrapper () in 
        counter:= !counter+1; 
    done