From Toychain
Require Import SeqFacts Chains Blocks Forests SystemSetup Network Protocol Misc.
Require Extraction.
Require String.

(* 
    The realisations made (some of which are commented out) are for test purposes. e.g. I don't plan on extracting VProof to unit.
 *)


(* Extract Constant Hash  => "string". *)
(* Extract Constant VProof => "unit". *)
(* Extract Constant Transaction => "string". *)
(* Extract Constant block  => "coq_Block". *)
(* Extract Constant TxPool  => "list coq_Transaction". *)
(* Extract Constant Blockchain  => "list block". *)
(* Extract Constant BlockTree  => "unit". *)
Extract Constant Timestamp  => "float".
Extract Inductive String.string => "string" ["EmptyString" "String"].

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

(* Cd "Extraction".
    Cd "Extracted".
        Separate Extraction SystemSetup.
    Cd "..".
Cd "..".
Print Extraction Inline. *)

(* Message MessageType State  *)