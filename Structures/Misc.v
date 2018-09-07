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

Record Address: Type := mkAddr {
    ip:string;
    port:nat
}.

Definition addr_eq (a b: Address) := (string_dec (ip a) (ip b)) && (port a==port b).

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



Record Transaction:Type := mkTx {
    from:Address;
    to:Address;
    val:nat;
}.

Definition trans_eq (a b:Transaction):= ((from a) == (from b)) && ((to a) == (to b)) && ((val a) == (val b)).
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