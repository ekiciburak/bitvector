From BV Require Import BVList InvCond.
Require Import List Bool NArith Psatz (*Int63*) ZArith Nnat.

Include RAW2BITVECTOR(RAWBITVECTOR_LIST).

Theorem bvadd_dep: forall (n : N), forall (s t : bitvector n),
    iff 
    (exists (x : bitvector n), bv_eq (bv_add x s) t = true)
    True.
Proof. intros n s t.
        split; intro A.
        - easy.
        - exists (bv_subt' t s).
          now rewrite bv_add_subst_opp.
Qed.

Theorem bvand_eq : forall (n : N), forall (s t : bitvector n), 
  iff 
    (exists (x : bitvector n), bv_eq (bv_and x s) t = true) 
    (bv_eq (bv_and t s) t = true).
Proof. intros.
       destruct s as (s, H0).
       destruct t as (t, H1).
       unfold bv_and, bv_eq, bv in *. cbn.
       specialize (bvand_eq n s t H0 H1); intros.
       destruct H as (H, Ha).
       split; intros.
       rewrite RAWBITVECTOR_LIST.bv_eq_reflect. apply H.
       destruct H2 as ((x, Hx), p).
       rewrite RAWBITVECTOR_LIST.bv_eq_reflect in p.
       exists x. split; easy.
       rewrite RAWBITVECTOR_LIST.bv_eq_reflect in H2.
       specialize (Ha H2).
       destruct Ha as (x, (Hx, p)).
       exists (@MkBitvector n x Hx).
       now rewrite RAWBITVECTOR_LIST.bv_eq_reflect.
Qed.

Theorem bvor_eq : forall (n : N), forall (s t : bitvector n), 
   iff 
    (exists (x : bitvector n), bv_eq (bv_or x s) t = true) 
    (bv_eq (bv_or t s) t = true).
Proof. intros.
       destruct s as (s, H0).
       destruct t as (t, H1).
       unfold bv_or, bv_eq, bv in *. cbn.
       specialize (bvor_eq n s t H0 H1); intros.
       destruct H as (H, Ha).
       split; intros.
       rewrite RAWBITVECTOR_LIST.bv_eq_reflect. apply H.
       destruct H2 as ((x, Hx), p).
       rewrite RAWBITVECTOR_LIST.bv_eq_reflect in p.
       exists x. split; easy.
       rewrite RAWBITVECTOR_LIST.bv_eq_reflect in H2.
       specialize (Ha H2).
       destruct Ha as (x, (Hx, p)).
       exists (@MkBitvector n x Hx).
       now rewrite RAWBITVECTOR_LIST.bv_eq_reflect.
Qed.

Theorem bvshl_eq : forall (n : N), forall (s t : bitvector n),
    iff
     (exists (x : bitvector n), bv_eq (bv_shl x s) t = true)
     (bv_eq (bv_shl (bv_shr t s) s) t = true).
Proof. intros.
       destruct s as (s, H0).
       destruct t as (t, H1).
       unfold bv_shl, bv_eq, bv in *. cbn.
       specialize (bvshl_eq n s t H0 H1); intros.
       destruct H as (H, Ha).
       split; intros.
       rewrite RAWBITVECTOR_LIST.bv_eq_reflect. apply H.
       destruct H2 as ((x, Hx), p).
       rewrite RAWBITVECTOR_LIST.bv_eq_reflect in p.
       exists x. split; easy.
       rewrite RAWBITVECTOR_LIST.bv_eq_reflect in H2.
       specialize (Ha H2).
       destruct Ha as (x, (Hx, p)).
       exists (@MkBitvector n x Hx).
       now rewrite RAWBITVECTOR_LIST.bv_eq_reflect.
Qed.

Theorem bvashr_eq : forall (n : N), forall (s t : bitvector n),
   iff
    (exists (x : bitvector n), (bv_eq (bv_ashr_a x s) t = true))
    (((bv_ult s (nat2bv (N.to_nat n) n) = true) 
      ->  bv_eq (bv_ashr_a (bv_shl t s) s) t = true)
                        /\
     ((bv_ult s (nat2bv (N.to_nat n) n) = false) 
      ->  bv_eq t (bv_not (zeros n)) = true \/ (bv_eq t (zeros n) = true))).
Proof. intros.
       destruct s as (s, H).
       destruct t as (t, H0).
       unfold bv_ult, bv_ashr_a, nat2bv, bv_not, bv_eq, bv, wf. cbn in *.
       rewrite !RAWBITVECTOR_LIST.bv_eq_reflect.
       specialize (InvCond.bvashr_eq n s t H H0); intros.
       rewrite H, H0 in H1. split; intros.
       apply H1.
       destruct H2 as ((x, Hx), p).
       exists x. split. easy.
       now rewrite RAWBITVECTOR_LIST.bv_eq_reflect in p.
       apply H1 in H2.
       destruct H2 as (x, (Hx, p)).
       exists (@MkBitvector n x Hx).
       now rewrite RAWBITVECTOR_LIST.bv_eq_reflect.
Qed.


Theorem bvashr_ult2_ltr : forall (n : N), forall (s t : bitvector n),
    (exists (x : bitvector n), (bv_ult (bv_ashr_a s x) t = true)) ->
    (((bv_ult s t = true) \/ (bv_slt s (zeros n)) = false) /\ 
    (bv_eq t (zeros n)) = false).
Proof. intros. 
        destruct H as (x, H2).
        destruct s as (s, H).
        destruct t as (t, H0).
        destruct x as (x, H1).
        unfold bv_ult, bv_slt, bv_ashr_a, bv_eq, bv in *. cbn in *.
        specialize (InvCond.bvashr_ult2_ltr n s t H H0); intros.
        rewrite H, H0 in H3. apply H3.
        exists x. easy.
Qed.

Theorem bvashr_ult2_rtl : forall (n : N), forall (s t : bitvector n),
     (((bv_ult s t = true) \/ (bv_slt s (zeros n)) = false) /\
     (bv_eq t (zeros n)) = false) ->
     (exists (x : bitvector n), (bv_ult (bv_ashr_a s x) t = true)).
Proof. intros. 
        destruct H as (H1, H2).
        destruct s as (s, H).
        destruct t as (t, H0).
        unfold bv_ult, bv_slt, bv_ashr_a, bv_eq, bv in *. cbn in *.
        specialize (InvCond.bvashr_ult2_rtl n s t H H0); intros.
        rewrite H0, H in H3.
        assert ((RAWBITVECTOR_LIST.bv_ult s t = true \/
                 RAWBITVECTOR_LIST.bv_slt s (RAWBITVECTOR_LIST.zeros n) = false) /\
                 RAWBITVECTOR_LIST.bv_eq t (RAWBITVECTOR_LIST.zeros n) = false). 
        split; easy.
        specialize (H3 H4).
        destruct H3 as (x, (Hx, p)).
        exists (@MkBitvector n x Hx). easy.
Qed.

Theorem bvashr_ugt2_ltr: forall (n : N), forall (s t : bitvector n),
    (exists (x : bitvector n), (bv_ugt (bv_ashr_a s x) t = true)) ->
    ((bv_slt s (bv_shr_a s (bv_not t)) = true) \/ (bv_ult t s = true)).
Proof. intros. 
        destruct H as (x, H2).
        destruct s as (s, H).
        destruct t as (t, H0).
        destruct x as (x, H1).
        unfold bv_ugt, bv_ult, bv_slt, bv_ashr_a, bv in *. cbn in *.
        specialize (InvCond.bvashr_ugt2_ltr n s t H H0); intros.
        apply H3.
        exists x. easy.
Qed.

Theorem bvashr_ugt2_rtl: forall (n : N), forall (s t : bitvector n),
    ((bv_slt s (bv_shr_a s (bv_not t)) = true) \/ (bv_ult t s = true)) ->
    (exists (x : bitvector n), (bv_ugt (bv_ashr_a s x) t = true)).
Proof. intros. 
        destruct s as (s, Hs).
        destruct t as (t, Ht).
        unfold bv_ugt, bv_ult, bv_slt, bv_ashr_a, bv in *. cbn in *.
        specialize (bvashr_ugt2_rtl n s t Hs Ht); intros.
        unfold RAWBITVECTOR_LIST.bv_not, RAWBITVECTOR_LIST.bits in H0.
        specialize (H0 H).
        destruct H0 as (x, (Hx, p)).
        exists (@MkBitvector n x Hx). easy.
Qed.

Theorem bvshr_ugt_rtl : forall (n : N), forall (s t : bitvector n), 
    (bv_ult t (bv_shr (bv_not s) s) = true) -> 
    (exists (x : bitvector n), bv_ugt (bv_shr x s) t = true).
Proof. intros.
       destruct s as (s, H0).
       destruct t as (t, H1).
       unfold bv_ugt, bv_ult, bv_shr, bv in *. cbn in *.
       specialize (bvshr_ugt_rtl n s t H0 H1); intros.
       unfold RAWBITVECTOR_LIST.bv_not, RAWBITVECTOR_LIST.bits in *.
       rewrite RAWBITVECTOR_LIST.bv_shr_eq in H.
       specialize (H2 H).
       destruct H2 as (x, (Hx, p)).
       exists (@MkBitvector n x Hx).
       now rewrite RAWBITVECTOR_LIST.bv_shr_eq.
Qed.

Theorem bvshl_neq_ltr: forall (n : N), forall (s t : bitvector n), 
    (exists (x : bitvector n), bv_eq (bv_shl x s) t = false) ->
    bv_eq t (zeros n) = false \/ 
    bv_ult s (nat2bv (N.to_nat n) n) = true.
Proof. intros.
       destruct s as (s, H0).
       destruct t as (t, H1).
       unfold bv_ult, bv_ashr_a, bv_eq, bv in *. cbn in *.
       specialize (bvshl_neq_ltr n s t H0 H1); intros.
       rewrite H0, H1 in H2. apply H2.
       destruct H as ((x, Hx), p).
       exists (@MkBitvector n x Hx). cbn in *.
       split. easy. now rewrite <- RAWBITVECTOR_LIST.bv_shl_eq.
Qed.





