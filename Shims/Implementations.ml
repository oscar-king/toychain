open Canonicals
open Parameters
open Blocks

let rec pow a = function
| 0 -> 1
| 1 -> a
| n -> 
let b = pow a (n / 2) in
b * b * (if n mod 2 = 0 then 1 else a)

let genBlock = {prevBlockHash = Obj.magic "0000000"; txs = Obj.magic []; proof = Obj.magic ([], "0000000")}

let mkProof (address:coq_Address) (blkChain: coq_Blockchain) (txpool: coq_TxPool) (time:coq_Timestamp) : (coq_TxPool * coq_VProof) option = 
  let x = (address, blkChain, txpool, time) in 
  let hashX = Hashtbl.hash x in 
  begin
    match hashX > Random.int ((pow 2 30)-1) with 
      | true -> Some (txpool, (string_of_int hashX))
      | false -> None
  end

let fcr (b1 : coq_Blockchain) (b2 : coq_Blockchain): bool =
  let b1_hash = Hashtbl.hash b1 in
  let b2_hash = Hashtbl.hash b2 in
  b1_hash > b2_hash

let vaf (proof: coq_VProof) (b1 : coq_Blockchain) (txpool: coq_TxPool) : bool = 
  true

let tpExtend (tp: coq_TxPool) (bt: coq_BlockTree) (tx: coq_Transaction) : coq_TxPool = 
  tp

let txValid  (tx: coq_Transaction) (bc :coq_Blockchain): bool = true