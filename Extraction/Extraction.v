From Toychain
Require Import SeqFacts Chains Blocks Forests SystemSetup Network Protocol Misc.
Require Extraction.
Require String.
Require Import ExtrOcamlBasic.


(* 
    The realisations made (some of which are commented out) are for test purposes. e.g. I don't plan on extracting VProof to unit.
 *)

Extraction Inline ssrbool.SimplPred.
Extraction Inline ssrbool.simpl_pred.
(* Extraction Inline ssrbool.simpl_rel. *)

Extract Constant Hash  => "string".
Extract Constant VProof => "string".
Extract Constant Timestamp  => "float".
<<<<<<< HEAD
(* Extract Inductive String.string => "string" ["EmptyString" "String"]. *)
(* Extract Inductive list => "list" [ "[]" "(::)" ]. *)
(*Extract Inductive prod => "(*)"  [ "(,)" ].*)
(* Extract Inductive bool => "bool" [ "true" "false" ]. *)
(* Extract Inductive option => "option" ["Some" "None"]. *)
=======
Extract Inductive String.string => "string" ["EmptyString" "String"].
Extract Inductive list => "list" [ "[]" "(::)" ].
Extract Inductive prod => "(*)"  [ "(,)" ].
Extract Inductive bool => "bool" [ "true" "false" ].
Extract Inductive option => "option" ["Some" "None"].
Extraction Inline negb.
Extraction Inline fst.
>>>>>>> parent of 186d08d... Still fixing issues

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
<<<<<<< HEAD
        Separate Extraction Toychain.Protocol.Init procMsg procInt initWorld. 
=======
        Separate Extraction Packet Message Toychain.Protocol.Init procMsg procInt initWorld.
>>>>>>> parent of 186d08d... Still fixing issues
    Cd "..".
Cd "..".
