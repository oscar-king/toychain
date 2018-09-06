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
(* 
Parameter Transaction : Transaction.

Parameter Hash : ordType.
Parameter VProof : eqType.

Definition block: Type := @Block Hash [eqType of Misc.Transaction] VProof.
Definition TxPool: Type := seq Misc.Transaction.
Definition Blockchain := seq block.
Definition BlockTree := union_map Hash block.

Parameter Timestamp : Type.
Parameter Address : Address.
Parameter GenesisBlock : block.

(* These functions need to be implemented *)
Parameter hashT : Misc.Transaction -> Hash.
Parameter hashB : block -> Hash.
Parameter genProof : Misc.Address -> Blockchain -> TxPool -> Timestamp -> option (TxPool * VProof).
Parameter VAF : VProof -> Blockchain -> TxPool -> bool.
Parameter FCR : Blockchain -> Blockchain -> bool.

(* Transaction is valid and consistent with the given chain *)
Parameter txValid : Misc.Transaction -> Blockchain -> bool.
Parameter tpExtend : TxPool -> BlockTree -> Misc.Transaction -> TxPool. *)

(* Structure setup1 := set1 {
    Transaction:eqType;
    Hash:ordType;
    VProof:eqType;
    Timestamp:Type;
    Address:finType;
}.

Parameter sysSet1:setup1.
Definition block: Type := @Block sysSet1.Hash sysSet1.Transaction sysSet1.VProof.
Definition TxPool: Type := seq sysSet1.Transaction.
Definition Blockchain := seq block.
Definition BlockTree := union_map sysSet1.Hash block. *)


Parameter Transaction : eqType.

Parameter Hash : ordType.
Parameter VProof : eqType.

Definition block: Type := @Block Hash Transaction VProof.
Definition TxPool: Type := seq Transaction.
Definition Blockchain := seq block.
Definition BlockTree := union_map Hash block.

Parameter Timestamp : Type.
Parameter Address : Address.
Parameter GenesisBlock : block.

(* These functions need to be implemented *)
Parameter hashT : Transaction -> Hash.
Parameter hashB : block -> Hash.
Parameter genProof : Misc.Address -> Blockchain -> TxPool -> Timestamp -> option (TxPool * VProof).
Parameter VAF : VProof -> Blockchain -> TxPool -> bool.
Parameter FCR : Blockchain -> Blockchain -> bool.

(* Transaction is valid and consistent with the given chain *)
Parameter txValid : Transaction -> Blockchain -> bool.
Parameter tpExtend : TxPool -> BlockTree -> Transaction -> TxPool.
