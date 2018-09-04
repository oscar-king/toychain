From mathcomp.ssreflect
Require Import ssreflect ssrbool ssrnat eqtype ssrfun seq fintype path.
Require Import Eqdep.
From fcsl
Require Import pred prelude ordtype pcm finmap unionmap heap.
From Toychain
Require Import SeqFacts Chains Blocks.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Require Extraction.



Parameter Hash : ordType.
Parameter VProof : eqType.
Parameter Transaction : eqType.

Definition block: Type := @Block Hash Transaction VProof.
Definition TxPool: Type := seq Transaction.
Definition Blockchain := seq block.
Definition BlockTree := union_map Hash block.

Parameter Timestamp : Type.
Parameter Address : finType.
Parameter GenesisBlock : block.
Parameter hashT : Transaction -> Hash.
Parameter hashB : block -> Hash.
Parameter genProof : Address -> Blockchain -> TxPool -> Timestamp -> option (TxPool * VProof).
Parameter VAF : VProof -> Blockchain -> TxPool -> bool.
Parameter FCR : Blockchain -> Blockchain -> bool.

(* Transaction is valid and consistent with the given chain *)
Parameter txValid : Transaction -> Blockchain -> bool.
Parameter tpExtend : TxPool -> BlockTree -> Transaction -> TxPool.

