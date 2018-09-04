From Toychain
Require Import SeqFacts Chains Blocks Forests SystemSetup Protocol Network.
Require Extraction.

(* Extract Constant Hash  => "unit".
Extract Constant VProof => "unit".
Extract Constant Transaction => "unit". *)
(* Extract Constant block  => "coq_Block". *)
(* Extract Constant TxPool  => "list coq_Transaction". *)
(* Extract Constant Blockchain  => "list block". *)
(* Extract Constant BlockTree  => "unit". *)
Extract Constant Timestamp  => "float".

(* Extract Constant Address => "procAddress". *)
(* Extract Constant peers_t => "procAddress list". *)
(* Extract Constant genProof => "Type". *)
(* Extract Constant txValid => "Type". *)

(* Extract Constant hashT => "Type". *)
(* Extract Constant hashB => "Type". *)
(* Extract Constant VAF => "Type". *)
(* Extract Constant FCR => "Type". *)
(* Extract Constant tpExtend => "Type". *)
(* Extract Constant GenesisBlock => "block". *)


Cd "Extraction".
    Cd "Extracted".
        Separate Extraction Packet Toychain.Protocol.Init procMsg procInt initWorld.
    Cd "..".
Cd "..".
Print Extraction Inline.

(* Message MessageType State  *)