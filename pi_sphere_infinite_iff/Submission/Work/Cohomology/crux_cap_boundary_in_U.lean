import Mathlib
import Submission.Work.Cohomology.pd_crux_weak
import Submission.Work.Cohomology.pd_hatcher_decomp
import Submission.Work.Cohomology.cap_mem_range_inclChains

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

open CategoryTheory AlgebraicTopology Simplicial CategoryTheory.Limits
open scoped Simplicial

namespace Work.Cohomology

noncomputable section

theorem crux_cap_boundary_in_U {M : TopCat} {U V K L : Set M} (hKU : K ⊆ U) (hLV : L ⊆ V) {k mj : ℕ} (α₁ α₂ α₃ : (Work.Cohomology.singularChains ℤ M).X (k + (mj + 1))) (φ φA φB : Work.Cohomology.Cochain ℤ (TopCat.toSSet.obj M) k) (hφA : φA ∈ Work.Cohomology.relKern ℤ M Kᶜ k) (hφB : φB ∈ Work.Cohomology.relKern ℤ M Lᶜ k) (hlift : φ = φA - φB) (hα₁ : ∃ a', (Work.Cohomology.inclChains M (U \ L)).f (k + (mj + 1)) a' = α₁) (hα₂ : ∃ b', (Work.Cohomology.inclChains M (U ∩ V)).f (k + (mj + 1)) b' = α₂) (hα₃ : ∃ d', (Work.Cohomology.inclChains M (V \ K)).f (k + (mj + 1)) d' = α₃) (hL : ∃ e', (Work.Cohomology.inclChains M Lᶜ).f (k + mj) e' = (Work.Cohomology.singularChains ℤ M).d (k + (mj + 1)) (k + mj) α₁) (hK : ∃ f', (Work.Cohomology.inclChains M Kᶜ).f (k + mj) f' = (Work.Cohomology.singularChains ℤ M).d (k + (mj + 1)) (k + mj) α₃) (hd : (Work.Cohomology.singularChains ℤ M).d (k + (mj + 1)) (k + mj) (α₁ + α₂ + α₃) = 0) (hφd : Work.Cohomology.cochainDiff ℤ (TopCat.toSSet.obj M) (n := k) φ = 0) : ∃ γ ∈ LinearMap.range (((Work.Cohomology.inclChains M U).f (mj + 1)).hom), (ModuleCat.Hom.hom ((Work.Cohomology.chainC ℤ (TopCat.toSSet.obj M)).d (mj + 1) mj)) γ = (-1 : ℤ) ^ (k + 1) • Work.Cohomology.cap ℤ (TopCat.toSSet.obj M) (Work.Cohomology.cochainDiff ℤ (TopCat.toSSet.obj M) (n := k) φA) mj ((Work.Cohomology.capIdx k mj) ▸ α₂) := by
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

  -- the witness: the two `U`-supported chains
  refine ⟨cap ℤ (TopCat.toSSet.obj M) φ (mj + 1) α₁
      + cap ℤ (TopCat.toSSet.obj M) φA (mj + 1) α₂, ?_, ?_⟩
  · exact add_mem
      (mem_range_inclChains_of_subset (M := M) (S := U \ L) (T := U)
        (fun x hx => hx.1) (cap_mem_range_inclChains (M := M) (U \ L) k (mj + 1) φ hα₁))
      (mem_range_inclChains_of_subset (M := M) (S := U ∩ V) (T := U)
        (fun x hx => hx.1) (cap_mem_range_inclChains (M := M) (U ∩ V) k (mj + 1) φA hα₂))
  · rw [map_add]
    have hk := key
    rw [sub_eq_iff_eq_add] at hk
    rw [hk]
    abel

end

end Work.Cohomology
