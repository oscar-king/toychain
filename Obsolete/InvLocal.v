From mathcomp.ssreflect
Require Import ssreflect ssrbool ssrnat eqtype ssrfun seq.
From mathcomp
Require Import path.
Require Import Eqdep pred prelude idynamic ordtype pcm finmap unionmap heap.
Require Import Blockchain Protocol Semantics States BlockchainProperties SeqFacts.
Require Import InvMisc.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.


(**********************************************************************)
(* Local Invariant: Blockchain Growth. *)

(* Every node n's local blockchain cost doesnt decrease as the system
   evolves.  *)
(**********************************************************************)


(* Auxiliary lemmas *)

Lemma btChain_extend :
  forall (bt : BlockTree) (b extension : Block),
    let bc := (btChain bt) in
    b \notin bc ->
    prevBlockHash extension == hashB (bcLast bc) ->
    btChain (btExtend bt b) = rcons bc extension.
Proof.
Admitted.

Lemma btChain_fork :
  forall (bt : BlockTree) (bc : Blockchain) (b : Block),
  let: bc' := btChain (btExtend bt b) in
    btChain bt = bc ->
    b \notin bc ->
    prevBlockHash (bcLast bc') != hashB (bcLast bc) ->
    fork bc bc'.
Proof.
Admitted.

Lemma btExtend_withNew_sameOrBetter :
  forall (bt : BlockTree) (b : Block), let: bt' := btExtend bt b in
    b ∉ bt ->
      b \in btChain bt' = (btChain bt' > btChain bt).
Proof.
Admitted.

Lemma btExtend_withNew_mem (bt : BlockTree) (b : Block) :
    let bc := btChain bt in
    let: bc' := btChain (btExtend bt b) in
    b \notin bc ->
    bc != bc' = (b \in bc').
Proof.
move=>/= Nin; apply/Bool.eq_true_iff_eq; split; last first.
- by move=>In; apply/negbT/negP=>/eqP Z; rewrite Z In in Nin.
move=>Neq.
Admitted.

Lemma procMsg_bc_prefix_or_fork bc bc' (s1 : State) from (m : Message) (ts : Timestamp):
  let: s2 := (procMsg s1 from m ts).1 in
  valid (blockTree s1) ->
  has_init_block (blockTree s1) ->
  btChain (blockTree s1) = bc  ->
  btChain (blockTree s2) = bc' ->
  bc = bc' \/ (([bc <<< bc'] \/ fork bc bc') /\ bc' > bc).
Proof.
  move=>V H; move: m ts; case =>[|prs||b|t|sh|h] ts hbc;
    do? local_bc_no_change s1 hbc hbc'.
- case: s1 hbc V H =>/= _ _ bt _ hbc V H; case B: (b ∈ bt).
  + move: (btExtend_withDup_noEffect B)=><-<-.
    by rewrite hbc; left.

  move=>hbc'; rewrite -hbc -hbc'.
  (* Extension – note that b is not necessarily the last block in bc' *)
  case E: (prevBlockHash (bcLast bc') == hashB (bcLast bc)).
  + right. split; move/negbT/btChain_mem: B; rewrite hbc=>/(_ V H) B;
    rewrite -hbc in B E; move: (btChain_extend B E)=>->; rewrite -cats1 hbc.
    by left; exists (bcLast bc'), [::].
    by apply CFR_ext.

  (* Fork *)
  + right; move: (B)=>B'; move/negbT in B.
    move/negbT/btChain_mem in B'; rewrite hbc in B'; rewrite -hbc' in E.
    move:(B' V H)=>{B'}B'.
    move/negbT in E; specialize (btChain_fork hbc B' E)=> F; split. right.
    by rewrite -hbc in F; apply F.
    move: (btExtend_withNew_sameOrBetter B)=><-; rewrite -hbc in B'.
    move: (btExtend_withNew_mem B')=><-; rewrite hbc' in F.
    by rewrite hbc hbc'; move: (bc_fork_neq F).

rewrite /procMsg/=; case: s1 V H hbc=>n? bt ?/=V H hbc.
by case:ifP=>//=_<-; left.
Qed.

Lemma procInt_bc_same_or_extension :
  forall (s1 : State) (t : InternalTransition) ts,
    let s2 := (procInt s1 t ts).1 in
    let bc := btChain (blockTree s1) in
    let bc' := btChain (blockTree s2) in
    bc = bc' \/ [bc <<< bc'].
Proof.
move=>s1 t ts=>/=; destruct s1; case t=>/=; first by left.
case hP: (genProof _)=>[pf|]; last by left.
case vP: (VAF _)=>/=; last by left. right.
set B :=
  {| height := height (last GenesisBlock (btChain blockTree)) + 1;
     prevBlockHash := hashB (last GenesisBlock (btChain blockTree));
     txs := [seq t0 <- txPool | txValid t0 (btChain blockTree)];
     proof := pf
  |}.
(*TODO: this is a trivial statement, but we might need a new axiom *)
assert (B \notin (btChain blockTree)). by admit.
assert (prevBlockHash B == hashB (bcLast (btChain blockTree))) by done.
by move: (btChain_extend H H0)->; exists B, [::]; rewrite cats1.
Admitted.

(* The invariant *)

Lemma local_chain_grows_fork_step (w w' : World) q n bc bc':
  n \in dom (localState w) ->
  holds n w (has_chain bc) ->
  system_step w w' q ->
  holds n w' (has_chain bc') ->
  bc = bc' \/ (([bc <<< bc'] \/ fork bc bc') /\ bc' > bc).
Proof.
move=>D H1 S H2; move: (Coh_step S)=>C2.
case: S=>[[C]Z|p [n' prs bt pool] [c1 c2 c3] c4 c5 ?? F|
          proc t s1 [c1 c2 c3] c4 c5 ? F].

(* 0 steps *)
- by subst w'; rewrite (has_chain_func D H1 H2); left.
(* Step is procedding a message *)

(* Receiving a message *)
- have E: (n' = (dst p)) by move/eqP: (c2 (dst p) _ F). subst n'.

  (* Two sub-cases: (dst p) =? n *)
  case N : (n == dst p);[move/eqP:N=>N; subst n|]; last first.
  (* Message not to us: don't really care about the outcome of procMsg! *)
  + set pms := (procMsg _ _); case: pms=>st' ms Z; subst w'.
    rewrite /holds/= findU N/= in H2.
    by rewrite -(has_chain_func D H1 H2); left.
  rewrite [procMsg _ _ _ _]surjective_pairing=>Z;
  (* Avoiding premature unfolding. *)
  set Pm := nosimpl (procMsg _ _ _ _) in Z; subst w'.
  rewrite /holds/= findU eqxx/= c1 in H2.
  move/(H2 Pm.1): (erefl (Some Pm.1))=>{H2} H2.
  move: (H1 _ F)=>{H1 C2}/=H1.
  move: (c3 _ _ F) (c5 _ _ F)=>V H.
  by apply: (@procMsg_bc_prefix_or_fork bc bc'
        {| id := dst p; peers := prs; blockTree := bt; txPool := pool |}
        (src p) (msg p) (ts q)); move/eqP: H2; move/eqP: H1.

(* Internal transition *)
(* Two sub-cases: proc =? n *)
case N : (n == proc);[move/eqP:N=>N; subst n|]; last first.
- set pms := (procInt _ _ _). case: pms=>st' ms Z. subst w'.
  rewrite /holds/= findU N/= in H2.
  by left; rewrite -(has_chain_func D H1 H2).

(* Another interesting part of the proof: n == proc.
   Consider all branches of procInt and proof the property for each one.
   Don't hesitate to introduce auxiliary lemmas. *)
rewrite [procInt _ _ _]surjective_pairing=>Z.
set Pi := nosimpl (procInt _ _ _) in Z; subst w'.
rewrite /holds/= findU eqxx/= c1 in H2. rewrite /holds F in H1.
have: (Some s1 = Some s1). by []. move=> eq. move: (H1 s1 eq)=>hbc. clear eq.
have: (Some Pi.1 = Some Pi.1). by []. move=> eq. move: (H2 Pi.1 eq)=>hbc'. clear eq.
rewrite /has_chain in hbc hbc'. move/eqP in hbc. move/eqP in hbc'.
specialize (procInt_bc_same_or_extension s1 t (ts q))=>/=.
case=>/=; rewrite -hbc -hbc'; first by left.
move=>Pf; right; split; first by left.
by move: Pf=>[] eh [] et ->; apply CFR_ext.
Qed.

(* Big-step case, proven by induction *)
Lemma local_chain_grows_fork (w w' : World) n bc bc':
  n \in dom (localState w) ->
  holds n w (has_chain bc) ->
  reachable w w' ->
  holds n w' (has_chain bc') ->
  bc = bc' \/ (([bc <<< bc'] \/ fork bc bc') /\ bc' > bc).
Proof.
move=>D H1 [m]R H2.
elim: m w' R bc' H2=>/=[w'<-|q m Hi w' [via][R S]] bc' H2.
- by left; move/(has_chain_func D H1 (bc':=bc')):H2=><-.
have D': n \in dom (localState via).
- suff R' : reachable w via by rewrite -(steps_nodes R').
  by exists m.
suff X : exists bc1, holds n via (has_chain bc1).
- case: X=>bc1 H; move: (Hi _ R _ H)=>P1.
  move: (local_chain_grows_fork_step D' H S H2)=>P2.
  case P1; case P2; clear P1 P2.
  - by move=><-<-; left.
  - case; case=> HH Gt Eq; right; split; rewrite -Eq in Gt; do? by [].
      by rewrite -Eq in HH; left.
      by rewrite -Eq in HH; right.

  - move=> Eq; case; case=> HH Gt; right; split; rewrite Eq in Gt; do? by [].
      by rewrite Eq in HH; left.
      by rewrite Eq in HH; right.

  (* Reasoning about forks *)
  case; case=> HH Gt; case; case=>HH' Gt';
  right; split; do? by move: (CFR_trans Gt Gt').
  (* --bc---bc1---bc' *)
  by left; move: (bc_spre_trans HH' HH).

  (*   /--bc
   * --
   *   \-----bc1---bc'
   *)
  by right; move: (bc_fork_prefix HH' (bc_spre_pre HH)).

  (*      /-- bc1                /---bc--bc1
   * --bc-               OR   ---
   *      \------- bc'           \-------------bc'
   *)
  case: (bc_relP bc bc').
  - by move/eqP=>Eq; subst bc'; contradict HH; move/norP=>[] _=>/norP;
       move/sprefixP in HH'; rewrite HH'=>/andP.
  - by move=>F; right.
  - by move=>Spf; left; apply/sprefixP.
  - by move/sprefixP=>Spf; move/sprefixP:(bc_spre_trans Spf HH')=>C;
       contradict HH; move/norP=>[] _=>/norP; rewrite C=>/andP.

  (*  /-bc                      /--bc-----------bc'
   *---------bc1          OR  --
   *      \---------bc'         \-------bc1
   * This is the most interesting case -- only provable if respecting CFR *)
  case: (bc_relP bc bc').
  - by move/eqP=>Eq; subst bc'; move: (CFR_trans Gt' Gt)=>C;
       contradict C; apply: CFR_nrefl.
  - by move=> F; right.
  - by move=>Spf; left; apply/sprefixP.
  - by move/sprefixP=>[b][ext] Eq; subst bc; move: (CFR_trans Gt Gt')=>C;
       move: (CFR_ext bc' b ext)=>C'; move: (CFR_excl C C').

rewrite /holds/has_chain.
move/um_eta: D';case; case=>id ps bt t [][->]_.
by exists (btChain (blockTree {|
    id := id; peers := ps; blockTree := bt; txPool := t |}))=>st[]<-.
Qed.


(* TODO: Prove more complicated scenario a la Kiayias et al: the
"rollback" is no more than a contstant number of septs; *)

