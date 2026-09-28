import Mathlib
import Submission.Work.Cohomology.exists_capH
import Submission.Work.Cohomology.pd_good

/-!
# The weak crux identity for Poincaré–Lefschetz duality

Let `M` be a topological space, `K, L ⊆ M` and `φ = φA - φB` a degree-`k` cochain whose
restriction `φA` vanishes on chains supported in `Kᶜ` and whose `φB` vanishes on chains supported
in `Lᶜ`.  Assume `φ` is a cocycle, `α₁ + α₂ + α₃` is a cycle of degree `k + (mj+1)`, the boundary
`d α₁` is supported in `Lᶜ` and `d α₃` is supported in `Kᶜ`.

Then the *chain-level computation of the crux square* (Hatcher, Lemma 3.36) says that

  `d (α₁ ⌢ φ) - (-1)^(k+1) (α₂ ⌢ δφA)`

is again a boundary.  The proof actually shows the sharper identity

  `d (α₁ ⌢ φ) - (-1)^(k+1) (α₂ ⌢ δφA) = - d (α₂ ⌢ φA)`,

which is exactly the statement that the "crux" square of the Mayer–Vietoris comparison of the
Poincaré–Lefschetz duality maps commutes up to the boundary of the "middle" term.

The ingredients are:

* the boundary formula for the cap product `cap_d`;
* the identities `α₁ ⌢ φ = α₁ ⌢ φA` (since `φ = φA - φB` and `d α₁` is supported in `Lᶜ`) and
  `α₃ ⌢ φA = 0` (since `d α₃` is supported in `Kᶜ`);
* the distributive laws for the differential.

## Sign conventions

With the chain-level differential `d = Σ_i (-1)^i δ_i` and the coboundary `δα = α ∘ d`
(`cochainDiff`, the plain transpose, no sign), the boundary formula reads

  `d (c ⌢ α) = (-1)^n • ((d c) ⌢ α - c ⌢ (δα))`   (for `deg c = n + (m+1)`),

see `Work.Cohomology.cap_d`.
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option linter.unusedVariables false
set_option maxHeartbeats 800000

open CategoryTheory AlgebraicTopology Simplicial CategoryTheory.Limits
open scoped Simplicial

namespace Work.Cohomology

noncomputable section

/-! ## The cap product with a difference of cochains -/

/-- The cap product is additive in the cochain, in the "difference" form. -/
lemma capHom_sub_cochain {R : Type} [CommRing R] {X : SSet} {n m : ℕ}
    (α β : Cochain R X n) :
    capHom R X (α - β) m = capHom R X α m - capHom R X β m := by
  have h : (-β : Cochain R X n) = (-1 : R) • β := (neg_one_smul R β).symm
  rw [sub_eq_add_neg, capHom_add, h, capHom_smul, neg_one_smul, sub_eq_add_neg]

/-- The cap product with a difference of cochains, evaluated on a chain. -/
lemma cap_sub_apply {R : Type} [CommRing R] {X : SSet} {n m : ℕ}
    (α β : Cochain R X n) (c : ↑((X.chainComplex (ModuleCat.of R R)).X (n + m))) :
    cap R X (α - β) m c = cap R X α m c - cap R X β m c := by
  rw [cap, capHom_sub_cochain, ModuleCat.hom_sub, LinearMap.sub_apply, cap, cap]

/-! ## The cap product with a relative cochain kills chains supported in the subspace -/

/-- **The cap product of a relative cochain with a chain supported in the subspace vanishes.**  If
`φ ∈ C^n(X,A)` (i.e. `φ` vanishes on chains supported in `A`) then `φ` kills, under the cap
product, every chain coming from `A`. -/
lemma cap_inclChains_eq_zero (X : TopCat) (A : Set X) {n : ℕ}
    (φ : Cochain ℤ (TopCat.toSSet.obj X) n) (hφ : φ ∈ relKern ℤ X A n) (m : ℕ)
    (u : (singularChains ℤ (TopCat.of A)).X (n + m)) :
    cap ℤ (TopCat.toSSet.obj X) φ m ((inclChains X A).f (n + m) u) = 0 := by
  have h := capMap_comp_chainComplexMap ℤ X A (⟨φ, hφ⟩ : relKern ℤ X A n) m
  have h2 := congrArg ModuleCat.Hom.hom h
  simp only [ModuleCat.hom_comp, ModuleCat.hom_zero] at h2
  rw [cap]
  rw [inclChains, chainMap_f_eq]
  exact LinearMap.congr_fun h2 u

/-! ## The crux identity -/

/-- **The weak crux identity of Poincaré–Lefschetz duality.**  Under the hypotheses of
`pd_crux_weak`, the element `d (α₁ ⌢ φ) - (-1)^(k+1) (α₂ ⌢ δφA)` is a boundary; indeed it is
`- d (α₂ ⌢ φA)`. -/
theorem pd_crux_weak {M : TopCat} {K L : Set M} {k mj : ℕ}
    (α₁ α₂ α₃ : (singularChains ℤ M).X (k + (mj + 1)))
    (φ φA φB : Cochain ℤ (TopCat.toSSet.obj M) k)
    (hφA : φA ∈ relKern ℤ M Kᶜ k) (hφB : φB ∈ relKern ℤ M Lᶜ k)
    (hφ : φ ∈ relKern ℤ M Kᶜ k)
    (hlift : φ = φA - φB)
    (hL : ∃ e', (inclChains M Lᶜ).f (k + mj) e'
      = (singularChains ℤ M).d (k + (mj + 1)) (k + mj) α₁)
    (hK : ∃ f', (inclChains M Kᶜ).f (k + mj) f'
      = (singularChains ℤ M).d (k + (mj + 1)) (k + mj) α₃)
    (hd : (singularChains ℤ M).d (k + (mj + 1)) (k + mj) (α₁ + α₂ + α₃) = 0)
    (hφd : cochainDiff ℤ (TopCat.toSSet.obj M) (n := k) φ = 0) :
    (ModuleCat.Hom.hom ((chainC ℤ (TopCat.toSSet.obj M)).d (mj + 1) mj)
        (cap ℤ (TopCat.toSSet.obj M) φ (mj + 1) α₁)
      - (-1 : ℤ) ^ (k + 1) •
          cap ℤ (TopCat.toSSet.obj M) (cochainDiff ℤ (TopCat.toSSet.obj M) (n := k) φA) mj
            ((capIdx k mj) ▸ α₂))
      ∈ LinearMap.range (ModuleCat.Hom.hom ((chainC ℤ (TopCat.toSSet.obj M)).d (mj + 1) mj)) := by
  obtain ⟨e', he'⟩ := hL
  obtain ⟨f', hf'⟩ := hK
  -- `d α₁` is supported in `Lᶜ`, where `φB` vanishes
  have hzeroB : cap ℤ (TopCat.toSSet.obj M) φB mj
      ((singularChains ℤ M).d (k + (mj + 1)) (k + mj) α₁) = 0 := by
    rw [← he']
    exact cap_inclChains_eq_zero M Lᶜ φB hφB mj e'
  -- `d α₃` is supported in `Kᶜ`, where `φA` vanishes
  have hzeroA : cap ℤ (TopCat.toSSet.obj M) φA mj
      ((singularChains ℤ M).d (k + (mj + 1)) (k + mj) α₃) = 0 := by
    rw [← hf']
    exact cap_inclChains_eq_zero M Kᶜ φA hφA mj f'
  -- the boundary of `α₁` is minus the sum of the boundaries of `α₂` and `α₃`
  have hdα : (singularChains ℤ M).d (k + (mj + 1)) (k + mj) α₁
      = - ((singularChains ℤ M).d (k + (mj + 1)) (k + mj) α₂
            + (singularChains ℤ M).d (k + (mj + 1)) (k + mj) α₃) := by
    have h := hd
    rw [map_add, map_add, add_assoc] at h
    exact eq_neg_of_add_eq_zero_left h
  -- the cap of `d α₁` with `φ` is the cap of `d α₂` with `φA`, up to sign
  have hP : cap ℤ (TopCat.toSSet.obj M) φ mj
        ((singularChains ℤ M).d (k + (mj + 1)) (k + mj) α₁)
      = - cap ℤ (TopCat.toSSet.obj M) φA mj
          ((singularChains ℤ M).d (k + (mj + 1)) (k + mj) α₂) := by
    rw [hlift, cap_sub_apply, hzeroB, sub_zero, hdα, map_neg, map_add, hzeroA, add_zero]
  -- the boundary formula for the cocycle `φ` applied to `α₁`
  have hA : (ModuleCat.Hom.hom ((chainC ℤ (TopCat.toSSet.obj M)).d (mj + 1) mj))
        (cap ℤ (TopCat.toSSet.obj M) φ (mj + 1) α₁)
      = (-1 : ℤ) ^ k • cap ℤ (TopCat.toSSet.obj M) φ mj
          ((singularChains ℤ M).d (k + (mj + 1)) (k + mj) α₁) := by
    have h := cap_d ℤ (TopCat.toSSet.obj M) (n := k) (m := mj) φ α₁
    rw [hφd, cap_zero, LinearMap.zero_apply, sub_zero] at h
    exact h.trans
      (int_smul_eq_zsmul (inferInstance : Module ℤ (↑((chainC ℤ (TopCat.toSSet.obj M)).X mj)))
        ((-1 : ℤ) ^ k) (cap ℤ (TopCat.toSSet.obj M) φ mj
          ((singularChains ℤ M).d (k + (mj + 1)) (k + mj) α₁)))
  -- the boundary formula for `φA` applied to `α₂`
  have hB : (ModuleCat.Hom.hom ((chainC ℤ (TopCat.toSSet.obj M)).d (mj + 1) mj))
        (cap ℤ (TopCat.toSSet.obj M) φA (mj + 1) α₂)
      = (-1 : ℤ) ^ k • (cap ℤ (TopCat.toSSet.obj M) φA mj
            ((singularChains ℤ M).d (k + (mj + 1)) (k + mj) α₂)
          - cap ℤ (TopCat.toSSet.obj M) (cochainDiff ℤ (TopCat.toSSet.obj M) (n := k) φA) mj
            ((capIdx k mj) ▸ α₂)) := by
    have h := cap_d ℤ (TopCat.toSSet.obj M) (n := k) (m := mj) φA α₂
    exact h.trans
      (int_smul_eq_zsmul (inferInstance : Module ℤ (↑((chainC ℤ (TopCat.toSSet.obj M)).X mj)))
        ((-1 : ℤ) ^ k) (cap ℤ (TopCat.toSSet.obj M) φA mj
            ((singularChains ℤ M).d (k + (mj + 1)) (k + mj) α₂)
          - cap ℤ (TopCat.toSSet.obj M) (cochainDiff ℤ (TopCat.toSSet.obj M) (n := k) φA) mj
            ((capIdx k mj) ▸ α₂)))
  -- the arithmetic combination
  have key : (ModuleCat.Hom.hom ((chainC ℤ (TopCat.toSSet.obj M)).d (mj + 1) mj)
        (cap ℤ (TopCat.toSSet.obj M) φ (mj + 1) α₁)
      - (-1 : ℤ) ^ (k + 1) •
          cap ℤ (TopCat.toSSet.obj M) (cochainDiff ℤ (TopCat.toSSet.obj M) (n := k) φA) mj
            ((capIdx k mj) ▸ α₂))
      = - (ModuleCat.Hom.hom ((chainC ℤ (TopCat.toSSet.obj M)).d (mj + 1) mj)
        (cap ℤ (TopCat.toSSet.obj M) φA (mj + 1) α₂)) := by
    rw [hA, hP, hB]
    rw [zsmul_neg]
    rw [show (-1 : ℤ) ^ (k + 1) = -(-1 : ℤ) ^ k by rw [pow_succ]; ring, neg_zsmul, zsmul_sub]
    abel
  rw [LinearMap.mem_range]
  exact ⟨- cap ℤ (TopCat.toSSet.obj M) φA (mj + 1) α₂, by rw [map_neg, ← key]⟩

end

end Work.Cohomology
