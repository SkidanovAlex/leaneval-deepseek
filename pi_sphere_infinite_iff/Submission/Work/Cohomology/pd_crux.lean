import Mathlib
import Submission.Work.Cohomology.exists_capH
import Submission.Work.Cohomology.pd_hatcher_data

/-!
# The crux square of Poincaré–Lefschetz duality (Hatcher's Lemma 3.36, third square)

This file proves `Work.Cohomology.pd_crux`, the elementwise chain-level identity underlying the
*crux square* of the gluing in the Milnor exotic sphere project.

Setting: `φ, φA, φB` are degree-`k` cochains on `M` with `φ = φA - φB`,
`φA ∈ C^k(M, Kᶜ)`, `φB ∈ C^k(M, Lᶜ)` and `φ ∈ C^k(M, Kᶜ) ∩ C^k(M, Lᶜ)` a cocycle.  The chains
`α₁, α₂, α₃` of degree `k + (mj+1)` are supported in `U ∖ L`, `U ∩ V` and `V ∖ K` respectively,
and `α₁ + α₂ + α₃` is a cycle.

The conclusion is that

`d(cap φ (mj+1) α₁) - (-1)^(k+1) • cap (dφA) mj (capIdx k mj ▸ α₂)`

is a boundary (degree `mj`).  The explicit witness is `- cap φA (mj+1) α₂`.

The mathematical content is Hatcher's computation of the crux square: the boundary formula
`cap_d` for the cocycle `φ` gives `d(cap φ (mj+1) α₁) = (-1)^k • cap φ mj (dα₁)`; since
`dα₁ ∈ Lᶜ` and `φB` kills `Lᶜ`-chains, this is `(-1)^k • cap φA mj (dα₁)`; using
`dα₁ = -(dα₂ + dα₃)` and the fact that `dα₃ ∈ Kᶜ` is killed by `φA`, one obtains

`d(cap φ (mj+1) α₁) = (-1)^(k+1) • cap φA mj (dα₂)`.

On the other hand `cap_d` for `φA` and `α₂` expresses `d(cap φA (mj+1) α₂)` in terms of `dα₂` and
`cap (dφA) mj (capIdx k mj ▸ α₂)`, which identifies the second term of the goal up to the boundary
`d(cap φA (mj+1) α₂)`.

## Main statements

* `cap_eq_zero_of_mem_range_inclChains` — the cap product of a cochain vanishing on `A` with a
  chain supported in a subset `B ⊆ A` vanishes;
* `boundary_mem_range_inclChains` — the boundary of a chain supported in `B` is supported in `B`;
* `pd_crux` — the goal.
-/

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
set_option linter.unusedVariables false

open CategoryTheory AlgebraicTopology Simplicial CategoryTheory.Limits
open scoped Simplicial

namespace Work.Cohomology

noncomputable section

/-! ## Elementary vanishing and support lemmas -/

/-- **The cap product with a relative cochain kills chains supported in a smaller set.**  If
`φ` vanishes on the `k`-chains supported in `A` and `x` is a `(k+m)`-chain supported in `B ⊆ A`,
then `cap φ m x = 0`. -/
theorem cap_eq_zero_of_mem_range_inclChains (M : TopCat) (A B : Set M) (hBA : B ⊆ A) {k m : ℕ}
    (φ : Cochain ℤ (TopCat.toSSet.obj M) k) (hφ : φ ∈ relKern ℤ M A k)
    {x : (singularChains ℤ M).X (k+m)}
    (hx : x ∈ LinearMap.range ((inclChains M B).f (k+m)).hom) :
    cap ℤ (TopCat.toSSet.obj M) φ m x = 0 := by
  obtain ⟨y, rfl⟩ := hx
  have hmap : (inclChains M A).f (k+m) ≫ capHom ℤ (TopCat.toSSet.obj M) φ m = 0 := by
    rw [inclChains, chainMap_f_eq]
    exact capMap_comp_chainComplexMap ℤ M A ⟨φ, hφ⟩ m
  have h2 := congrArg (fun (g : _ ⟶ _) => (ModuleCat.Hom.hom g)
      ((ModuleCat.Hom.hom ((inclChainsSub M B A hBA).f (k+m))) y)) hmap
  have hfin : (ModuleCat.Hom.hom ((inclChains M B).f (k+m))) y
      = (ModuleCat.Hom.hom ((inclChains M A).f (k+m)))
          ((ModuleCat.Hom.hom ((inclChainsSub M B A hBA).f (k+m))) y) := by
    rw [← inclChainsSub_comp M B A hBA, HomologicalComplex.comp_f]
    rfl
  rw [hfin]
  exact h2

/-- **The boundary of a chain supported in `B` is supported in `B`**: naturality of the chain map
`inclChains M B`. -/
theorem boundary_mem_range_inclChains (M : TopCat) (B : Set M) {k mj : ℕ}
    {α : (singularChains ℤ M).X (k + (mj+1))}
    (h : α ∈ LinearMap.range ((inclChains M B).f (k+(mj+1))).hom) :
    (singularChains ℤ M).d (k+(mj+1)) (k+mj) α ∈
      LinearMap.range ((inclChains M B).f (k+mj)).hom := by
  obtain ⟨a', rfl⟩ := h
  refine ⟨(singularChains ℤ (TopCat.of B)).d (k+(mj+1)) (k+mj) a', ?_⟩
  exact (congrArg (fun (g : _ ⟶ _) => (ModuleCat.Hom.hom g) a')
    (HomologicalComplex.Hom.comm (inclChains M B) (k+(mj+1)) (k+mj))).symm

/-- The cap product is additive in the cochain. -/
theorem cap_add' {R : Type} [CommRing R] {X : SSet} {n m : ℕ} (α β : Cochain R X n) :
    cap R X (α + β) m = cap R X α m + cap R X β m := by
  show (capHom R X (α + β) m).hom = (capHom R X α m).hom + (capHom R X β m).hom
  rw [capHom_add, ModuleCat.hom_add]

/-- The cap product is homogeneous in the cochain. -/
theorem cap_smul' {R : Type} [CommRing R] {X : SSet} {n m : ℕ} (r : R) (α : Cochain R X n) :
    cap R X (r • α) m = r • cap R X α m := by
  show (capHom R X (r • α) m).hom = r • (capHom R X α m).hom
  rw [capHom_smul, ModuleCat.hom_smul]

/-- The cap product is additive in the cochain, negated form. -/
theorem cap_neg' {R : Type} [CommRing R] {X : SSet} {n m : ℕ} (α : Cochain R X n) :
    cap R X (-α) m = - cap R X α m := by
  have h : (-α : Cochain R X n) = (-1:R) • α := (neg_one_smul R α).symm
  rw [h, cap_smul', neg_one_smul]

/-- The cap product is additive in the cochain, subtraction form. -/
theorem cap_sub' {R : Type} [CommRing R] {X : SSet} {n m : ℕ} (α β : Cochain R X n) :
    cap R X (α - β) m = cap R X α m - cap R X β m := by
  rw [sub_eq_add_neg, cap_add', cap_neg', sub_eq_add_neg]

/-- The scalar identity closing the crux computation: for `r * s = -1`,
`r • x - r • (x - s • y) = -y`. -/
theorem pd_crux_algebra {A : Type*} [AddCommGroup A] (r s : ℤ) (x y : A) (h : r*s = -1) :
    r • x - r • (x - s • y) = -y := by
  rw [zsmul_sub, sub_sub_self, ← mul_smul, h, neg_one_zsmul]

/-! ## The crux square -/

theorem pd_crux {M : TopCat} {U V : Set M} {K L : Set M} (hKU : K ⊆ U) (hLV : L ⊆ V)
    {k mj : ℕ}
    (α₁ α₂ α₃ : (singularChains ℤ M).X (k + (mj + 1)))
    (φ φA φB : Cochain ℤ (TopCat.toSSet.obj M) k)
    (hφA : φA ∈ relKern ℤ M Kᶜ k) (hφB : φB ∈ relKern ℤ M Lᶜ k)
    (hφ : φ ∈ relKern ℤ M Kᶜ k) (hφ' : φ ∈ relKern ℤ M Lᶜ k)
    (hlift : φ = φA - φB)
    (hα₁ : ∃ a', (inclChains M (U \ L)).f (k + (mj + 1)) a' = α₁)
    (hα₂ : ∃ b', (inclChains M (U ∩ V)).f (k + (mj + 1)) b' = α₂)
    (hα₃ : ∃ d', (inclChains M (V \ K)).f (k + (mj + 1)) d' = α₃)
    (hd : (singularChains ℤ M).d (k + (mj + 1)) (k + mj) (α₁ + α₂ + α₃) = 0)
    (hφd : cochainDiff ℤ (TopCat.toSSet.obj M) (n := k) φ = 0) :
    (ModuleCat.Hom.hom ((chainC ℤ (TopCat.toSSet.obj M)).d (mj + 1) mj)
        (cap ℤ (TopCat.toSSet.obj M) φ (mj + 1) α₁)
      - (-1 : ℤ) ^ (k + 1) •
          cap ℤ (TopCat.toSSet.obj M) (cochainDiff ℤ (TopCat.toSSet.obj M) (n := k) φA) mj
            ((capIdx k mj) ▸ α₂))
      ∈ LinearMap.range (ModuleCat.Hom.hom ((chainC ℤ (TopCat.toSSet.obj M)).d (mj + 1) mj)) := by
  -- `U ∖ L ⊆ Lᶜ` and `V ∖ K ⊆ Kᶜ`
  have hUsum : U \ L ⊆ Lᶜ := fun x hx => hx.2
  have hVsum : V \ K ⊆ Kᶜ := fun x hx => hx.2
  -- the boundary of `α₁` written in terms of `α₂`, `α₃`, from `d(α₁ + α₂ + α₃) = 0`
  have hda1 : (ModuleCat.Hom.hom ((singularChains ℤ M).d (k+(mj+1)) (k+mj))) α₁
      = - (ModuleCat.Hom.hom ((singularChains ℤ M).d (k+(mj+1)) (k+mj))) α₂
        - (ModuleCat.Hom.hom ((singularChains ℤ M).d (k+(mj+1)) (k+mj))) α₃ := by
    have h1 : (ModuleCat.Hom.hom ((singularChains ℤ M).d (k+(mj+1)) (k+mj))) α₁
        + (ModuleCat.Hom.hom ((singularChains ℤ M).d (k+(mj+1)) (k+mj))) α₂
        + (ModuleCat.Hom.hom ((singularChains ℤ M).d (k+(mj+1)) (k+mj))) α₃ = 0 := by
      rw [← map_add, ← map_add]; exact hd
    rw [show (-(ModuleCat.Hom.hom ((singularChains ℤ M).d (k+(mj+1)) (k+mj))) α₂
          - (ModuleCat.Hom.hom ((singularChains ℤ M).d (k+(mj+1)) (k+mj))) α₃)
        = -((ModuleCat.Hom.hom ((singularChains ℤ M).d (k+(mj+1)) (k+mj))) α₂
            + (ModuleCat.Hom.hom ((singularChains ℤ M).d (k+(mj+1)) (k+mj))) α₃) by abel]
    rw [eq_neg_iff_add_eq_zero, ← add_assoc]; exact h1
  -- `φB` kills the boundary of `α₁` (supported in `U ∖ L ⊆ Lᶜ`)
  have hφBzero : cap ℤ (TopCat.toSSet.obj M) φB mj
      ((ModuleCat.Hom.hom ((singularChains ℤ M).d (k+(mj+1)) (k+mj))) α₁) = 0 :=
    cap_eq_zero_of_mem_range_inclChains M Lᶜ (U\L) hUsum φB hφB
      (boundary_mem_range_inclChains M (U\L) hα₁)
  -- `φA` kills the boundary of `α₃` (supported in `V ∖ K ⊆ Kᶜ`)
  have hφA3zero : cap ℤ (TopCat.toSSet.obj M) φA mj
      ((ModuleCat.Hom.hom ((singularChains ℤ M).d (k+(mj+1)) (k+mj))) α₃) = 0 :=
    cap_eq_zero_of_mem_range_inclChains M Kᶜ (V\K) hVsum φA hφA
      (boundary_mem_range_inclChains M (V\K) hα₃)
  -- `cap φ mj (dα₁) = - cap φA mj (dα₂)`
  have hcaprelSC : cap ℤ (TopCat.toSSet.obj M) φ mj
      ((ModuleCat.Hom.hom ((singularChains ℤ M).d (k+(mj+1)) (k+mj))) α₁)
      = - cap ℤ (TopCat.toSSet.obj M) φA mj
          ((ModuleCat.Hom.hom ((singularChains ℤ M).d (k+(mj+1)) (k+mj))) α₂) := by
    rw [hlift, cap_sub', LinearMap.sub_apply, hφBzero, sub_zero, hda1,
      map_sub, map_neg, hφA3zero, sub_zero]
  -- the same identity, in the `chainC` presentation used by `cap`
  have hcaprel : cap ℤ (TopCat.toSSet.obj M) φ mj
      ((ModuleCat.Hom.hom ((chainC ℤ (TopCat.toSSet.obj M)).d (k+(mj+1)) (k+mj))) α₁)
      = - cap ℤ (TopCat.toSSet.obj M) φA mj
          ((ModuleCat.Hom.hom ((chainC ℤ (TopCat.toSSet.obj M)).d (k+(mj+1)) (k+mj))) α₂) :=
    hcaprelSC
  -- the left hand side of the crux identity
  have hA : (ModuleCat.Hom.hom ((chainC ℤ (TopCat.toSSet.obj M)).d (mj + 1) mj))
        (cap ℤ (TopCat.toSSet.obj M) φ (mj + 1) α₁)
      = (-1:ℤ)^(k+1) • cap ℤ (TopCat.toSSet.obj M) φA mj
          ((ModuleCat.Hom.hom ((chainC ℤ (TopCat.toSSet.obj M)).d (k+(mj+1)) (k+mj))) α₂) := by
    rw [cap_d ℤ (TopCat.toSSet.obj M) (n := k) (m := mj) φ α₁, hφd]
    simp only [cap_zero, LinearMap.zero_apply, sub_zero]
    rw [hcaprel, capd_neg_one_pow_succ k, neg_zsmul, smul_neg]
    exact congrArg Neg.neg (int_smul_eq_zsmul
      (inferInstance : Module ℤ (↑((chainC ℤ (TopCat.toSSet.obj M)).X mj))) ((-1:ℤ)^k) _)
  have h1kself : (-1:ℤ)^k * (-1:ℤ)^k = 1 := by
    rw [← pow_add]; exact Even.neg_one_pow ⟨k, rfl⟩
  have hscal : (-1:ℤ)^(k+1) * (-1:ℤ)^k = -1 := by
    rw [← pow_add]; exact Odd.neg_one_pow ⟨k, by ring⟩
  -- the second term of the goal, in terms of `cap φA mj (dα₂)` and the boundary
  -- `d (cap φA (mj+1) α₂)`
  have hP : cap ℤ (TopCat.toSSet.obj M) (cochainDiff ℤ (TopCat.toSSet.obj M) (n := k) φA) mj
        ((capIdx k mj) ▸ α₂)
      = cap ℤ (TopCat.toSSet.obj M) φA mj
          ((ModuleCat.Hom.hom ((chainC ℤ (TopCat.toSSet.obj M)).d (k+(mj+1)) (k+mj))) α₂)
        - (-1:ℤ)^k • (ModuleCat.Hom.hom ((chainC ℤ (TopCat.toSSet.obj M)).d (mj+1) mj))
            (cap ℤ (TopCat.toSSet.obj M) φA (mj+1) α₂) := by
    have hcd2' : (ModuleCat.Hom.hom ((chainC ℤ (TopCat.toSSet.obj M)).d (mj+1) mj))
          (cap ℤ (TopCat.toSSet.obj M) φA (mj+1) α₂)
        = (-1:ℤ)^k • (cap ℤ (TopCat.toSSet.obj M) φA mj
            ((ModuleCat.Hom.hom ((chainC ℤ (TopCat.toSSet.obj M)).d (k+(mj+1)) (k+mj))) α₂)
            - cap ℤ (TopCat.toSSet.obj M) (cochainDiff ℤ (TopCat.toSSet.obj M) (n := k) φA) mj
                ((capIdx k mj) ▸ α₂)) :=
      (cap_d ℤ (TopCat.toSSet.obj M) (n := k) (m := mj) φA α₂).trans
        (int_smul_eq_zsmul (inferInstance : Module ℤ
          (↑((chainC ℤ (TopCat.toSSet.obj M)).X mj))) ((-1:ℤ)^k) _)
    have hstep : (-1:ℤ)^k • (ModuleCat.Hom.hom ((chainC ℤ (TopCat.toSSet.obj M)).d (mj+1) mj))
          (cap ℤ (TopCat.toSSet.obj M) φA (mj+1) α₂)
        = cap ℤ (TopCat.toSSet.obj M) φA mj
            ((ModuleCat.Hom.hom ((chainC ℤ (TopCat.toSSet.obj M)).d (k+(mj+1)) (k+mj))) α₂)
          - cap ℤ (TopCat.toSSet.obj M) (cochainDiff ℤ (TopCat.toSSet.obj M) (n := k) φA) mj
              ((capIdx k mj) ▸ α₂) := by
      have h1 := congrArg (fun z => (-1:ℤ)^k • z) hcd2'
      rw [← mul_smul, h1kself, one_zsmul] at h1
      exact h1
    exact ((congrArg (fun z => cap ℤ (TopCat.toSSet.obj M) φA mj
          ((ModuleCat.Hom.hom ((chainC ℤ (TopCat.toSSet.obj M)).d (k+(mj+1)) (k+mj))) α₂) - z)
        hstep).trans (sub_sub_self _ _)).symm
  -- the witness is `- cap φA (mj+1) α₂`
  refine ⟨- cap ℤ (TopCat.toSSet.obj M) φA (mj + 1) α₂, ?_⟩
  rw [map_neg, hA, hP]
  exact (pd_crux_algebra ((-1:ℤ)^(k+1)) ((-1:ℤ)^k) _ _ hscal).symm

end

end Work.Cohomology
