From mathcomp.ssreflect
Require Import ssreflect ssrbool ssrnat eqtype ssrfun seq fintype path.
Require Import Eqdep.
From fcsl
Require Import pred prelude ordtype pcm finmap unionmap heap.
From Toychain
Require Import SeqFacts Chains Blocks Misc.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Require Extraction.


(* These have all been defined in Misc *)
(* Parameter Transaction : Misc.Transaction. *)
(* Parameter Hash : Misc.Hash. *)
(* Parameter VProof : Misc.VProof. *)
(* Parameter Address : Misc.Address. *)

Definition block: Type := @Block [ordType of Misc.Hash] [eqType of Misc.Transaction] [eqType of Misc.VProof].
Definition TxPool: Type := seq Misc.Transaction.
Definition Blockchain := seq block.
Definition BlockTree := union_map [ordType of Misc.Hash] block.

Parameter Timestamp : Type.

(* TODO: GenesisBlock still needs defining *)
Parameter GenesisBlock : block.

(* These functions need to be implemented *)
Parameter hashT : Misc.Transaction -> Misc.Hash.
Parameter hashB : block -> [ordType of Misc.Hash].
Parameter genProof : Misc.Address -> Blockchain -> TxPool -> Timestamp -> option (TxPool * Misc.VProof).
Parameter VAF : Misc.VProof -> Blockchain -> TxPool -> bool.
Parameter FCR : Blockchain -> Blockchain -> bool.

(* Transaction is valid and consistent with the given chain *)
Parameter txValid : Misc.Transaction -> Blockchain -> bool.
Parameter tpExtend : TxPool -> BlockTree -> Misc.Transaction -> TxPool.