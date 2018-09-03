(* Cd "Extraction". *)
From Toychain
Require Import SeqFacts Chains Blocks Forests SystemSetup Protocol.
Require Extraction.

Extract Inlined Constant Hash  => "Type".
Extract Inlined Constant VProof => "Type".
Extract Inlined Constant Transaction => "Type".
Extract Inlined Constant block  => "Type".
Extract Inlined Constant TxPool  => "Type".
Extract Inlined Constant Blockchain  => "Type".
Extract Inlined Constant BlockTree  => "Type".
Extract Inlined Constant Timestamp  => "Type".

(* Extract Inlined Constant Address => "Type".
Extract Constant peers_t => "coq_Address list".
Extract Constant genProof => "Type".
Extract Constant txValid => "Type".
Extract Constant hashT => "Type".
Extract Constant hashB => "Type".
Extract Constant VAF => "Type".
Extract Constant FCR => "Type".
Extract Constant tpExtend => "Type".
Extract Constant GenesisBlock => "block". *)

Cd "Extraction".
    Cd "Extracted".
    Recursive Extraction Packet.
    Separate Extraction Message MessageType State Init procMsg procInt.
    Cd "..".
Cd "..".
