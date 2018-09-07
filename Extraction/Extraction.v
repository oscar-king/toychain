From Toychain
Require Import SeqFacts Chains Blocks Forests SystemSetup Network Protocol Misc.
Require Extraction.
Require String.

(* 
    The realisations made (some of which are commented out) are for test purposes. e.g. I don't plan on extracting VProof to unit.
 *)


Extract Constant Hash  => "string".
Extract Constant VProof => "string".
Extract Constant Timestamp  => "float".
Extract Inductive String.string => "string" ["EmptyString" "String"].
Extract Inductive list => "list" [ "[]" "(::)" ].
Extract Inductive prod => "(*)"  [ "(,)" ].
Extract Inductive bool => "bool" [ "true" "false" ].
Extract Inductive option => "option" ["Some" "None"].
Extraction Inline negb.
Extraction Inline fst.

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
        Separate Extraction Packet Message Toychain.Protocol.Init procMsg procInt initWorld.
    Cd "..".
Cd "..".
Print Extraction Inline.