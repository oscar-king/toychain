From mathcomp.ssreflect
Require Import ssreflect ssrbool ssrnat eqtype ssrfun seq path choice fintype.
Require Import Eqdep.
From fcsl
Require Import pred prelude ordtype pcm finmap unionmap heap.
From Toychain
Require Import SeqFacts Chains.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Require Import String.


Section Types.

    Record Address: Type := mkAddr {
        ip:nat*nat*nat*nat;
        port:nat
    }.

    Record Transaction:Type := mkTx {
        from:Address;
        to:Address;
        val:nat
    }.

    Parameter Hash:Type.

    Parameter VProof:Type.
End Types.

Section Canonicals_for_Types.
    (* Implicit Types ip ipn: nat*nat*nat*nat.
    Theorem ip_eq: forall ip ipn, {ip = ipn} + {ip <> ipn}.
    Proof.
        repeat decide equality.
    Qed. *)

    (* Axiom IPAddr_eqMixin : Equality.mixin_of IPAddr.
    Canonical IPAddr_eqType := Eval hnf in EqType IPAddr IPAddr_eqMixin.
     *)

    Definition addr_eq (a b: Address):bool := andb (ip a == ip b) (port a == port b).

    (* (ip_eq (ip a) (ip b)) && (port a==port b). *)

    (* Definition addr_eq (a b: Address):bool := (string_dec (ip a) (ip b)) && (port a==port b). *)


    Lemma eq_addrP : Equality.axiom addr_eq. 
    Admitted.

    Canonical addr_eqMixin:= Eval hnf in EqMixin eq_addrP.

    Canonical AddrEqType := Eval hnf in EqType Address addr_eqMixin.

    Axiom AddrChoiceMixin : Choice.mixin_of AddrEqType. 

    Canonical Addr_ChoiceType := Eval hnf in ChoiceType Address AddrChoiceMixin.

    Axiom AddrCountMixin : Finite.mixin_of AddrEqType.

    Canonical Addr_CountType := Eval hnf in CountType Address AddrCountMixin.

    Axiom AddrFinMixin : Finite.mixin_of Addr_CountType.
    Canonical AddrFinType := Eval hnf in FinType Address AddrCountMixin.

    Definition trans_eq (a b:Transaction):bool := ((from a) == (from b)) && ((to a) == (to b)) && ((val a) == (val b)).
    Lemma eq_transP : Equality.axiom trans_eq.

    Proof.
        case=>sa da ma [sb] db mb; rewrite/trans_eq/=.
        case P1: (sa == sb)=>/=; last by constructor 2; case=>/eqP; rewrite P1.
        case P2: (da == db)=>/=; last by constructor 2; case=> _ /eqP; rewrite P2.
        case P3: (ma == mb)=>/=; last by constructor 2; case=> _ _ /eqP; rewrite P3.
        by constructor 1; move/eqP: P1=><-; move/eqP: P2=><-; move/eqP: P3=><-.
    Qed.

    Canonical Trans_eqMixin := Eval hnf in EqMixin eq_transP.
    Canonical Trans_eqType := Eval hnf in EqType Transaction Trans_eqMixin.

    Axiom Hash_eqMixin : Equality.mixin_of Hash.
    Canonical Hash_eqType := Eval hnf in EqType Hash Hash_eqMixin.

    Axiom Hash_ordMixin : Ordered.mixin_of Hash_eqType.
    Canonical Hash_ordType := Eval hnf in OrdType Hash Hash_ordMixin.

    Axiom VProof_eqMixin : Equality.mixin_of VProof.
    Canonical VProof_eqType := Eval hnf in EqType VProof VProof_eqMixin.
 
End Canonicals_for_Types.

