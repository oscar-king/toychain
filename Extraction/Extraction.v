From Toychain
Require Import SeqFacts Chains Blocks Forests SystemSetup Network Protocol Misc.
Require Extraction.
Require String.
Require Import ExtrOcamlBasic.

Extraction Inline ssrbool.SimplPred.
Extraction Inline ssrbool.simpl_pred.
(* Extraction Inline ssrbool.simpl_rel. *)

Extract Constant Hash  => "string".
Extract Constant VProof => "string".
Extract Constant Timestamp  => "float".

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
        Separate Extraction Toychain.Protocol.Init procMsg procInt initWorld.
    Cd "..".
Cd "..".


