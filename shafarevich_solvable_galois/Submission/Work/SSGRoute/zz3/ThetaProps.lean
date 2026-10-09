import Mathlib
import Submission.Work.SSGRoute.zz3.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute.zz3

open scoped commutatorElement
open Work.CohomologicalShrinking
open Work.SSGRoute.ZZ3

set_option maxHeartbeats 8000000

/-! # Properties of the `θ`-map for the `(3,3)` diagonal graded step

We prove the three structural properties of `θ = thetaFun n` that the `G = ℤ/2` graded step
`E(n,(3,3)) → E(n,(4,1))` needs:

* `θ 0 = 1`;
* `θ` is additive (`θ (g+h) = θ g * θ h`), i.e. it is a homomorphism of `𝔽₂`-vector spaces;
* `θ` is equivariant for the action of `dm ∈ Gm = ℤ/2`: `θ (dTT n g) = dm • θ g`.

The route is: the classes `X w = mkQ n (lcF n w)` of the left-nested commutators
`lcF n w = [[w₀,w₁],w₂]` are involutions (`X w · X w = 1`) that commute pairwise, so the
map `g ↦ ∏_w X w ^ (g w).val` is additive; and the `dm`-action sends `X w` to `X (sigP n w)`. -/

/-! ## Generic monoid/list algebra -/

/-- In a monoid with `x * x = 1`, the power `x ^ n` only depends on `n mod 2`. -/
theorem pow_eq_pow_mod_two {M : Type*} [Monoid M] (x : M) (hx : x * x = 1) (n : ℕ) :
    x ^ n = x ^ (n % 2) := by
  conv_lhs => rw [← Nat.div_add_mod n 2]
  rw [pow_add, pow_mul, pow_two, hx, one_pow, one_mul]

/-- The exponent law in `𝔽₂` for an involution. -/
theorem pow_val_add_zmod_two {M : Type*} [Monoid M] (x : M) (hx : x * x = 1)
    (a b : ZMod 2) : x ^ (a + b).val = x ^ a.val * x ^ b.val := by
  rw [ZMod.val_add, ← pow_eq_pow_mod_two x hx (a.val + b.val), pow_add]

/-- **Additivity of the "product over a list" map.**  If `X : ι → M` is a family of pairwise
commuting involutions, then the map `c ↦ ∏_i X i ^ (c i).val` is additive on `ι → ZMod 2`. -/
theorem list_prod_zmod2_add {M : Type*} [Monoid M] {ι : Type*} (X : ι → M)
    (hsq : ∀ i, X i * X i = 1) (hcomm : ∀ i j, Commute (X i) (X j))
    (L : List ι) (c d : ι → ZMod 2) :
    (L.map (fun i => X i ^ (c i + d i).val)).prod
      = (L.map (fun i => X i ^ (c i).val)).prod * (L.map (fun i => X i ^ (d i).val)).prod := by
  induction L with
  | nil => simp
  | cons i L ih =>
    simp only [List.map_cons, List.prod_cons] at *
    rw [ih, pow_val_add_zmod_two (X i) (hsq i) (c i) (d i)]
    have hc : Commute (X i ^ (d i).val) (L.map (fun j => X j ^ (c j).val)).prod :=
      Commute.list_prod_right _ _ (fun y hy => by
        obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hy
        exact ((hcomm i j).pow_left (d i).val).pow_right (c j).val)
    simp only [mul_assoc]
    congr 1
    rw [← mul_assoc, hc.eq, mul_assoc]

/-- The product of a list mapped through `F` is unchanged by reindexing along `e`, provided
`e` is a permutation of `L` and the values commute. -/
theorem prod_map_perm {M : Type*} [Monoid M] {ι : Type*} (L Le : List ι) (h : Le.Perm L)
    (F : ι → M) (hpair : (L.map F).Pairwise Commute) : (L.map F).prod = (Le.map F).prod :=
  List.Perm.prod_eq' (List.Perm.map F h).symm hpair

/-- Reindexing identity for an involution `e`. -/
theorem prod_reindex_invol {M : Type*} [Monoid M] {ι : Type*} (L : List ι) (e : ι ≃ ι)
    (hinv : ∀ w, e (e w) = w) (hperm : (L.map e).Perm L) (X : ι → M) (c : ι → ZMod 2)
    (hpair : (L.map (fun w => X w ^ (c (e w)).val)).Pairwise Commute) :
    (L.map (fun w => X w ^ (c (e w)).val)).prod
      = (L.map (fun w => X (e w) ^ (c w).val)).prod := by
  have hF : (fun w => X (e w) ^ (c w).val) = (fun w => X w ^ (c (e w)).val) ∘ e := by
    funext w
    show X (e w) ^ (c w).val = X (e w) ^ (c (e (e w))).val
    rw [hinv w]
  rw [hF, ← List.map_map]
  exact prod_map_perm L (L.map e) hperm (fun v => X v ^ (c (e v)).val) hpair

/-! ## The element `mkQ` and the involution `dTT` -/

/-- `mkQ` as a monoid homomorphism. -/
noncomputable def mkQHom (n : ℕ) : FreeGroup (XX n) →*
    flowQuotient 2 Gm n (tauSucc 3 3).1 (tauSucc 3 3).2 :=
  (QuotientGroup.mk' ((flowTerm 2 Gm n (tauSucc 3 3).1 (tauSucc 3 3).2).subgroupOf
    (⊤ : Subgroup (FreeGroup (XX n))))).comp
    (Subgroup.topEquiv (G := FreeGroup (XX n))).symm.toMonoidHom

theorem mkQHom_apply (n : ℕ) (y : FreeGroup (XX n)) : mkQHom n y = mkQ n y := rfl

theorem mkQ_mul (n : ℕ) (a b : FreeGroup (XX n)) : mkQ n (a * b) = mkQ n a * mkQ n b := by
  rw [← mkQHom_apply n (a * b), ← mkQHom_apply n a, ← mkQHom_apply n b]
  exact map_mul (mkQHom n) a b

theorem mkQ_one (n : ℕ) : mkQ n 1 = 1 := by
  rw [← mkQHom_apply n 1]
  exact map_one (mkQHom n)

theorem mkQ_eq_one_iff (n : ℕ) (y : FreeGroup (XX n)) :
    mkQ n y = 1 ↔ y ∈ flowTerm 2 Gm n (tauSucc 3 3).1 (tauSucc 3 3).2 := by
  rw [mkQ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]

theorem mkQHom_eq_one_iff (n : ℕ) (y : FreeGroup (XX n)) :
    mkQHom n y = 1 ↔ y ∈ flowTerm 2 Gm n (tauSucc 3 3).1 (tauSucc 3 3).2 :=
  mkQ_eq_one_iff n y

theorem mkQHom_commutator (n : ℕ) (a b : FreeGroup (XX n)) :
    ⁅mkQHom n a, mkQHom n b⁆ = mkQHom n ⁅a, b⁆ :=
  (map_commutatorElement (mkQHom n) a b).symm

/-! ## Group-theoretic facts about `lcF` -/

/-- The left-nested commutator of a triple of generators lies in `P₂` of the `2`-central
series of the free group. -/
theorem lcF_mem (n : ℕ) (w : Idx n) :
    lcF n w ∈ Work.Shrinking.pCentralSeries 2 (FreeGroup (XX n)) 2 := by
  have hof : List.ofFn w = [w 0, w 1, w 2] := by
    rw [List.ofFn_eq_map]; rfl
  rw [lcF, hof, Work.SSGRoute.prop5.lc_eq_gpFold]
  have h := Work.SSGRoute.prop5.gpFold_mem (X := XX n) [w 1, w 2] 1 le_rfl
    (u := FreeGroup.of (w 0)) (Subgroup.mem_top _)
  exact (Work.ProP.lowerCentralSeries_le_pCentralSeries 2 (FreeGroup (XX n)) 2) h

/-- `flowTerm 2 Gm n 4 1` is the third term `P₃` of the `2`-central series of `F(n)`. -/
theorem flowTerm_eq (n : ℕ) :
    flowTerm 2 Gm n (tauSucc 3 3).1 (tauSucc 3 3).2
      = Work.Shrinking.pCentralSeries 2 (Work.Shrinking.freeOperatorGroup Gm n) 3 := by
  change flowTerm 2 Gm n 4 1
    = Work.Shrinking.pCentralSeries 2 (Work.Shrinking.freeOperatorGroup Gm n) 3
  show Work.CohomologicalShrinking.refinedTerm 2 (Work.Shrinking.freeOperatorGroup Gm n) 4 1
    = Work.Shrinking.pCentralSeries 2 (Work.Shrinking.freeOperatorGroup Gm n) 3
  rw [refinedTerm, centralSeries_one, inf_top_eq,
    sup_eq_left.mpr (pSeries_antitone 2 _ (by norm_num : 4 ≤ 5))]

/-- Squares of the commutators lie in `flowTerm`. -/
theorem lcF_sq_mem (n : ℕ) (w : Idx n) :
    (lcF n w) ^ 2 ∈ flowTerm 2 Gm n (tauSucc 3 3).1 (tauSucc 3 3).2 := by
  rw [flowTerm_eq]
  exact Work.Shrinking.pow_mem_pCentralSeries_succ 2 _ (lcF_mem n w)

/-- Commutators of the commutators lie in `flowTerm`. -/
theorem lcF_commutator_mem (n : ℕ) (v w : Idx n) :
    ⁅lcF n v, lcF n w⁆ ∈ flowTerm 2 Gm n (tauSucc 3 3).1 (tauSucc 3 3).2 := by
  rw [flowTerm_eq]
  exact (Work.Shrinking.commutator_le_pCentralSeries_succ 2 _ 2).2
    (Subgroup.commutator_mem_commutator (lcF_mem n v) (lcF_mem n w))

/-- The classes `X w = mkQ n (lcF n w)` are involutions. -/
theorem Xsq (n : ℕ) (w : Idx n) : mkQ n (lcF n w) * mkQ n (lcF n w) = 1 := by
  rw [← mkQ_mul, ← pow_two, mkQ_eq_one_iff]
  exact lcF_sq_mem n w

/-- The classes `X w` commute pairwise. -/
theorem Xcomm (n : ℕ) (v w : Idx n) :
    Commute (mkQ n (lcF n v)) (mkQ n (lcF n w)) := by
  rw [← mkQHom_apply n (lcF n v), ← mkQHom_apply n (lcF n w),
    ← commutatorElement_eq_one_iff_commute, mkQHom_commutator, mkQHom_eq_one_iff]
  exact lcF_commutator_mem n v w

/-! ## The action of `dm` -/

/-- The permutation `sigP n` as an equivalence. -/
def eIdx (n : ℕ) : Idx n ≃ Idx n where
  toFun w := sigP n w
  invFun w := sigP n w
  left_inv w := sigP_invol n w
  right_inv w := sigP_invol n w

theorem eIdx_apply (n : ℕ) (w : Idx n) : eIdx n w = sigP n w := rfl

theorem eIdx_invol (n : ℕ) (w : Idx n) : eIdx n (eIdx n w) = w := sigP_invol n w

/-- `freeGroupCongr` commutes with the left-nested commutator word. -/
theorem freeGroupCongr_lc {X : Type*} (σ : X ≃ X) (L : List X) :
    FreeGroup.freeGroupCongr σ (Work.SSGRoute.prop5.lc L)
      = Work.SSGRoute.prop5.lc (L.map σ) := by
  have hgp : ∀ (u : FreeGroup X) (vs : List X),
      FreeGroup.freeGroupCongr σ (Work.SSGRoute.prop5.gpFold u vs)
        = Work.SSGRoute.prop5.gpFold (FreeGroup.freeGroupCongr σ u) (vs.map σ) := by
    intro u vs
    induction vs generalizing u with
    | nil => rfl
    | cons y vs ihv =>
      show FreeGroup.freeGroupCongr σ (Work.SSGRoute.prop5.gpFold ⁅u, FreeGroup.of y⁆ vs)
          = Work.SSGRoute.prop5.gpFold ⁅FreeGroup.freeGroupCongr σ u, FreeGroup.of (σ y)⁆ (vs.map σ)
      rw [ihv ⁅u, FreeGroup.of y⁆]
      have h : (FreeGroup.freeGroupCongr σ) (FreeGroup.of y) = FreeGroup.of (σ y) := by
        rw [FreeGroup.freeGroupCongr_apply, FreeGroup.map.of]
      rw [map_commutatorElement, h]
  induction L with
  | nil => rfl
  | cons x rest ih =>
    rw [List.map_cons, Work.SSGRoute.prop5.lc_eq_gpFold, Work.SSGRoute.prop5.lc_eq_gpFold, hgp]
    have h : (FreeGroup.freeGroupCongr σ) (FreeGroup.of x) = FreeGroup.of (σ x) := by
      rw [FreeGroup.freeGroupCongr_apply, FreeGroup.map.of]
    rw [h]

/-- The involution `dTT` acts by `dm • lcF n w = lcF n (sigP n w)`. -/
theorem dm_smul_lcF (n : ℕ) (w : Idx n) :
    dm • lcF n w = lcF n (eIdx n w) := by
  show FreeGroup.freeGroupCongr (sg n) (lcF n w) = lcF n (eIdx n w)
  rw [lcF, freeGroupCongr_lc]
  congr 1

/-- The `dm`-action on `mkQ`. -/
theorem flowAction_mkQ_aux (n i j : ℕ) (y : FreeGroup (XX n)) :
    flowAction 2 Gm n i j dm
        (QuotientGroup.mk' ((flowTerm 2 Gm n i j).subgroupOf ⊤) ⟨y, Subgroup.mem_top y⟩)
      = QuotientGroup.mk' ((flowTerm 2 Gm n i j).subgroupOf ⊤) ⟨dm • y, Subgroup.mem_top _⟩ := by
  simp only [flowAction, Work.Shrinking.quotActionHom]
  show Work.Shrinking.quotAut ⊤ (flowTerm 2 Gm n i j) dm
      (Subgroup.map_top_of_surjective
        (MulEquiv.toMonoidHom (MulDistribMulAction.toMulAut Gm (Work.Shrinking.freeOperatorGroup Gm n) dm))
        (MulDistribMulAction.toMulAut Gm (Work.Shrinking.freeOperatorGroup Gm n) dm).surjective)
      (map_refinedTerm_eq 2
        (MulDistribMulAction.toMulAut Gm (Work.Shrinking.freeOperatorGroup Gm n) dm) i j)
      (QuotientGroup.mk' ((flowTerm 2 Gm n i j).subgroupOf ⊤) ⟨y, Subgroup.mem_top y⟩)
    = QuotientGroup.mk' ((flowTerm 2 Gm n i j).subgroupOf ⊤) ⟨dm • y, Subgroup.mem_top _⟩
  rw [Work.Shrinking.quotAut_mk]
  congr 1

theorem flowAction_mkQ (n : ℕ) (y : FreeGroup (XX n)) :
    flowAction 2 Gm n (tauSucc 3 3).1 (tauSucc 3 3).2 dm (mkQ n y) = mkQ n (dm • y) := by
  rw [mkQ]
  exact flowAction_mkQ_aux n (tauSucc 3 3).1 (tauSucc 3 3).2 y

/-! ## The index list and the main theorem -/

/-- The (arbitrary) linear order enumeration of `Idx n` used by `thetaFun`. -/
noncomputable def idxList (n : ℕ) : List (Idx n) :=
  letI : DecidableRel (α := Idx n) WellOrderingRel := Classical.decRel _
  letI : LinearOrder (Idx n) := linearOrderOfSTO WellOrderingRel
  (Finset.univ : Finset (Idx n)).sort (· ≤ ·)

theorem thetaFun_eq (n : ℕ) (g : TT n) :
    thetaFun n g = ((idxList n).map (fun w => (mkQ n (lcF n w)) ^ ((g w).val))).prod := rfl

theorem idxList_map_perm (n : ℕ) (e : Idx n ≃ Idx n) : ((idxList n).map e).Perm (idxList n) := by
  have hmem : ∀ b : Idx n, b ∈ idxList n := by
    intro b
    simp only [idxList, Finset.mem_sort, Finset.mem_univ]
  have hnd : (idxList n).Nodup := by
    simp only [idxList]
    exact Finset.sort_nodup _ _
  rw [List.perm_iff_count]
  intro a
  have h1 : (idxList n).count (e.symm a) = 1 := by
    rw [List.Nodup.count hnd]; simp [hmem (e.symm a)]
  have h2 : (idxList n).count a = 1 := by
    rw [List.Nodup.count hnd]; simp [hmem a]
  conv_lhs => rw [show a = e (e.symm a) from (e.apply_symm_apply a).symm]
  rw [List.count_map_of_injective (idxList n) e e.injective (e.symm a), h1, h2]

theorem thetaFun_add (n : ℕ) (g h : TT n) :
    thetaFun n (g + h) = thetaFun n g * thetaFun n h := by
  rw [thetaFun_eq, thetaFun_eq, thetaFun_eq]
  simp only [Pi.add_apply]
  exact list_prod_zmod2_add (fun w => mkQ n (lcF n w)) (Xsq n) (Xcomm n) (idxList n) g h

theorem thetaFun_dTT (n : ℕ) (g : TT n) :
    thetaFun n (dTT n g)
      = flowAction 2 Gm n (tauSucc 3 3).1 (tauSucc 3 3).2 dm (thetaFun n g) := by
  rw [thetaFun_eq, thetaFun_eq]
  simp only [dTT_apply]
  rw [map_list_prod]
  have happ : ∀ w : Idx n,
      flowAction 2 Gm n (tauSucc 3 3).1 (tauSucc 3 3).2 dm (mkQ n (lcF n w))
        = mkQ n (lcF n (eIdx n w)) := by
    intro w
    rw [flowAction_mkQ, dm_smul_lcF]
  have hstep : ((flowAction 2 Gm n (tauSucc 3 3).1 (tauSucc 3 3).2 dm) ∘
        (fun w : Idx n => (mkQ n (lcF n w)) ^ ((g w).val)))
      = (fun w : Idx n => (mkQ n (lcF n (eIdx n w))) ^ ((g w).val)) := by
    funext w
    simp only [Function.comp_apply]
    rw [map_pow, happ w]
  rw [List.map_map, hstep]
  have hpair : ((idxList n).map (fun v : Idx n =>
        mkQ n (lcF n v) ^ ((g (eIdx n v)).val))).Pairwise Commute := by
    rw [List.pairwise_map]
    haveI : Std.Refl (fun a b : Idx n =>
        Commute (mkQ n (lcF n a) ^ ((g (eIdx n a)).val))
          (mkQ n (lcF n b) ^ ((g (eIdx n b)).val))) := ⟨fun a => Commute.refl _⟩
    exact List.pairwise_of_reflexive_of_forall_ne (fun a _ b _ _ =>
      ((Xcomm n a b).pow_left ((g (eIdx n a)).val)).pow_right ((g (eIdx n b)).val))
  exact prod_reindex_invol (idxList n) (eIdx n) (fun w => eIdx_invol n w)
    (idxList_map_perm n (eIdx n)) (fun v => mkQ n (lcF n v)) g hpair

theorem ThetaProps (n : ℕ) :
    Work.SSGRoute.ZZ3.thetaFun n (0 : Work.SSGRoute.ZZ3.TT n) = 1 ∧
    (∀ g h : Work.SSGRoute.ZZ3.TT n,
        Work.SSGRoute.ZZ3.thetaFun n (g + h)
          = Work.SSGRoute.ZZ3.thetaFun n g * Work.SSGRoute.ZZ3.thetaFun n h) ∧
    (∀ g : Work.SSGRoute.ZZ3.TT n,
        Work.SSGRoute.ZZ3.thetaFun n (Work.SSGRoute.ZZ3.dTT n g)
          = Work.CohomologicalShrinking.flowAction 2 Work.SSGRoute.ZZ3.Gm n
              (Work.CohomologicalShrinking.tauSucc 3 3).1
              (Work.CohomologicalShrinking.tauSucc 3 3).2 Work.SSGRoute.ZZ3.dm
              (Work.SSGRoute.ZZ3.thetaFun n g)) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [thetaFun_eq]
    exact List.prod_eq_one (fun x hx => by
      obtain ⟨w, _, rfl⟩ := List.mem_map.mp hx
      simp)
  · intro g h; exact thetaFun_add n g h
  · intro g; exact thetaFun_dTT n g

end Work.SSGRoute.zz3
