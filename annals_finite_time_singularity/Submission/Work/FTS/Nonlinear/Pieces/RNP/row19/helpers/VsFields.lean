/-
# Field bounds extracted from `StarPkg` (`row19`)

The proof of `abs_DthIter_four_VsW_le` (see `../NOTES_abs_DthIter_four_VsW_le_stage2.md`)
works with the *unweighted* bounds

* `|V z θ| ≤ M`, `|(z+1)^k ∂_z^k V| ≤ M` (`k ≤ 4`),
* `|(z+1)^k ∂_z^k D_θ^j V| ≤ M` (`1 ≤ j`, `j+k ≤ 4`),
* the same three families for the `dU`-field function `∂_θ U`,
* `|D_θ^j V| ≤ M` (`j ≥ 1`), `|D_θ^j (∂_θU)| ≤ M` (`j ≥ 1`),

all with the *same* constant `M := 2·(max Cs 0 · α)` (the factor `2` absorbs the
angular weight `Λ = (α+sin 2θ)·sin(2θ)^{α/5} ≤ 2`).  These are what
`helpers.PsiParticular` consumes.
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS.Vocab
import Submission.Work.FTS.Nonlinear.Defs
import Submission.Work.Construction.Defs
import Submission.Work.Spaces.WlInf_terms
import Submission.Work.Spaces.ProductRuleInW

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open Set Filter

namespace Work.FTS.Nonlinear.Pieces.RNP.row19

set_option autoImplicit false

/-- The angular weight `Λ` is at most `2` for `0 < α ≤ 1`, `θ ∈ Iθ`. -/
theorem lam_le_two {α θ : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) (hθ : θ ∈ Work.Spaces.Iθ) :
    (α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5) ≤ 2 := by
  have hs0 : 0 ≤ Real.sin (2 * θ) :=
    Real.sin_nonneg_of_mem_Icc ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩
  have hs1 : Real.sin (2 * θ) ≤ 1 := Real.sin_le_one _
  have hr : (Real.sin (2 * θ)) ^ (α / 5) ≤ 1 :=
    Real.rpow_le_one hs0 hs1 (by linarith : (0:ℝ) ≤ α / 5)
  have hr0 : 0 ≤ (Real.sin (2 * θ)) ^ (α / 5) := Real.rpow_nonneg hs0 _
  have h1 : α + Real.sin (2 * θ) ≤ 1 + 1 := add_le_add hα1 hs1
  nlinarith [hr, hr0, hs0, hs1, h1]

/-- `Λ ≥ 0`. -/
theorem lam_nonneg {α θ : ℝ} (hα : 0 < α) (hθ : θ ∈ Work.Spaces.Iθ) :
    0 ≤ (α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5) := by
  have hs0 : 0 ≤ Real.sin (2 * θ) :=
    Real.sin_nonneg_of_mem_Icc ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩
  exact mul_nonneg (by linarith) (Real.rpow_nonneg hs0 _)

/-- **The `V`-field bounds.**  With `M := 2·(max Cs 0 · α)`: the pointwise bounds of the
`𝒲^{4,∞}`-field of `V = Vop (PhiTil α (Fstar α) Φs)`. -/
theorem Vs_field_bounds {α Cs : ℝ} {Φs : Work.FTS.Galerkin.Fn} (hα : 0 < α) (hα1 : α ≤ 1)
    (hs : Work.FTS.Nonlin.StarPkg α Cs Φs) :
    (∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      |Work.Construction.Vop (Work.FTS.Nonlin.PhiTs α Φs) z θ| ≤ 2 * (max Cs 0 * α)) ∧
    (∀ k : ℕ, k ≤ 4 → ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      |(z + 1) ^ k * Work.Spaces.pzIter k
          (Work.Construction.Vop (Work.FTS.Nonlin.PhiTs α Φs)) z θ| ≤ 2 * (max Cs 0 * α)) ∧
    (∀ k j : ℕ, 1 ≤ j → j + k ≤ 4 → ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      |(z + 1) ^ k * Work.Spaces.pzIter k
          (Work.Spaces.DthIter j (Work.Construction.Vop (Work.FTS.Nonlin.PhiTs α Φs))) z θ|
        ≤ 2 * (max Cs 0 * α)) ∧
    (∀ j : ℕ, 1 ≤ j → j ≤ 4 → ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      |Work.Spaces.DthIter j (Work.Construction.Vop (Work.FTS.Nonlin.PhiTs α Φs)) z θ|
        ≤ 2 * (max Cs 0 * α)) := by
  have hle : Work.Spaces.WlInf α 4 (Work.Construction.Vop (Work.FTS.Nonlin.PhiTs α Φs))
      ≤ max Cs 0 * α :=
    le_trans hs.V.2 (mul_le_mul_of_nonneg_right (le_max_left Cs 0) hα.le)
  have hM0 : 0 ≤ max Cs 0 * α := mul_nonneg (le_max_right Cs 0) hα.le
  have hle2 : Work.Spaces.WlInf α 4 (Work.Construction.Vop (Work.FTS.Nonlin.PhiTs α Φs))
      ≤ 2 * (max Cs 0 * α) := by linarith
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro z hz θ hθ
    have h : |(z + 1) ^ 0 * Work.Spaces.pzIter 0
        (Work.Construction.Vop (Work.FTS.Nonlin.PhiTs α Φs)) z θ| ≤ max Cs 0 * α :=
      le_trans (Work.Spaces.WlInf_z_bound α 4 _ hs.V.1 0 (by norm_num) z θ hz hθ) hle
    rw [pow_zero, Work.Spaces.pzIter_zero, one_mul] at h
    exact h.trans (by linarith)
  · intro k hk z hz θ hθ
    exact (Work.Spaces.WlInf_z_bound α 4 _ hs.V.1 k hk z θ hz hθ).trans hle2
  · intro k j hj hjk z hz θ hθ
    have h := Work.Spaces.pz_Dth_sup_bound α hα 4 _ hs.V.1 j k hj (by omega) z θ hz hθ
    have hz0 : (0 : ℝ) ≤ z := hz
    have hz1 : (0 : ℝ) < z + 1 := by linarith
    have hpow : (0 : ℝ) < (z + 1) ^ k := pow_pos hz1 k
    have hlam := lam_le_two hα hα1 hθ
    rw [div_mul_eq_mul_div] at h
    have h2 : (z + 1) ^ k * |Work.Spaces.pzIter k (Work.Spaces.DthIter j
          (Work.Construction.Vop (Work.FTS.Nonlin.PhiTs α Φs))) z θ|
        ≤ Work.Spaces.WlInf α 4 (Work.Construction.Vop (Work.FTS.Nonlin.PhiTs α Φs))
          * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)) := by
      have h' := mul_le_mul_of_nonneg_left h hpow.le
      rwa [mul_div_cancel₀ _ (ne_of_gt hpow)] at h'
    have h3 : (z + 1) ^ k * |Work.Spaces.pzIter k (Work.Spaces.DthIter j
          (Work.Construction.Vop (Work.FTS.Nonlin.PhiTs α Φs))) z θ|
        = |(z + 1) ^ k * Work.Spaces.pzIter k (Work.Spaces.DthIter j
          (Work.Construction.Vop (Work.FTS.Nonlin.PhiTs α Φs))) z θ| := by
      rw [abs_mul, abs_of_pos hpow]
    rw [h3] at h2
    refine h2.trans ?_
    exact (mul_le_mul hle hlam (lam_nonneg hα hθ) hM0).trans (le_of_eq (by ring))
  · intro j hj hj4 z hz θ hθ
    have h := Work.Spaces.pz_Dth_sup_bound α hα 4 _ hs.V.1 j 0 hj (by omega) z θ hz hθ
    simp only [pow_zero, div_one] at h
    refine h.trans ?_
    exact (mul_le_mul hle (lam_le_two hα hα1 hθ) (lam_nonneg hα hθ) hM0).trans
      (le_of_eq (by ring))

/-- **The `dU`-field bounds.**  With `M := 2·(max Cs 0 · α)`: the pointwise bounds of the
`𝒲^{5,∞}`-field of `∂_θU = pth (Uop (PhiTil α (Fstar α) Φs))`. -/
theorem dU_field_bounds {α Cs : ℝ} {Φs : Work.FTS.Galerkin.Fn} (hα : 0 < α) (hα1 : α ≤ 1)
    (hs : Work.FTS.Nonlin.StarPkg α Cs Φs) :
    (∀ k : ℕ, k ≤ 5 → ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      |(z + 1) ^ k * Work.Spaces.pzIter k
          (Work.Spaces.pth (Work.Construction.Uop α (Work.FTS.Nonlin.PhiTs α Φs))) z θ|
        ≤ 2 * (max Cs 0 * α)) ∧
    (∀ k j : ℕ, 1 ≤ j → j + k ≤ 5 → ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      |(z + 1) ^ k * Work.Spaces.pzIter k (Work.Spaces.DthIter j
          (Work.Spaces.pth (Work.Construction.Uop α (Work.FTS.Nonlin.PhiTs α Φs)))) z θ|
        ≤ 2 * (max Cs 0 * α)) ∧
    (∀ j : ℕ, 1 ≤ j → j ≤ 5 → ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      |Work.Spaces.DthIter j
          (Work.Spaces.pth (Work.Construction.Uop α (Work.FTS.Nonlin.PhiTs α Φs))) z θ|
        ≤ 2 * (max Cs 0 * α)) := by
  have hle : Work.Spaces.WlInf α 5 (Work.Spaces.pth (Work.Construction.Uop α
        (Work.FTS.Nonlin.PhiTs α Φs))) ≤ max Cs 0 * α :=
    le_trans hs.dU.2 (mul_le_mul_of_nonneg_right (le_max_left Cs 0) hα.le)
  have hM0 : 0 ≤ max Cs 0 * α := mul_nonneg (le_max_right Cs 0) hα.le
  have hle2 : Work.Spaces.WlInf α 5 (Work.Spaces.pth (Work.Construction.Uop α
        (Work.FTS.Nonlin.PhiTs α Φs))) ≤ 2 * (max Cs 0 * α) := by linarith
  refine ⟨?_, ?_, ?_⟩
  · intro k hk z hz θ hθ
    exact (Work.Spaces.WlInf_z_bound α 5 _ hs.dU.1 k hk z θ hz hθ).trans hle2
  · intro k j hj hjk z hz θ hθ
    have h := Work.Spaces.pz_Dth_sup_bound α hα 5 _ hs.dU.1 j k hj (by omega) z θ hz hθ
    have hz0 : (0 : ℝ) ≤ z := hz
    have hz1 : (0 : ℝ) < z + 1 := by linarith
    have hpow : (0 : ℝ) < (z + 1) ^ k := pow_pos hz1 k
    have hlam := lam_le_two hα hα1 hθ
    rw [div_mul_eq_mul_div] at h
    have h2 : (z + 1) ^ k * |Work.Spaces.pzIter k (Work.Spaces.DthIter j
          (Work.Spaces.pth (Work.Construction.Uop α (Work.FTS.Nonlin.PhiTs α Φs)))) z θ|
        ≤ Work.Spaces.WlInf α 5 (Work.Spaces.pth (Work.Construction.Uop α
            (Work.FTS.Nonlin.PhiTs α Φs)))
          * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)) := by
      have h' := mul_le_mul_of_nonneg_left h hpow.le
      rwa [mul_div_cancel₀ _ (ne_of_gt hpow)] at h'
    have h3 : (z + 1) ^ k * |Work.Spaces.pzIter k (Work.Spaces.DthIter j
          (Work.Spaces.pth (Work.Construction.Uop α (Work.FTS.Nonlin.PhiTs α Φs)))) z θ|
        = |(z + 1) ^ k * Work.Spaces.pzIter k (Work.Spaces.DthIter j
          (Work.Spaces.pth (Work.Construction.Uop α (Work.FTS.Nonlin.PhiTs α Φs)))) z θ| := by
      rw [abs_mul, abs_of_pos hpow]
    rw [h3] at h2
    refine h2.trans ?_
    exact (mul_le_mul hle hlam (lam_nonneg hα hθ) hM0).trans (le_of_eq (by ring))
  · intro j hj hj5 z hz θ hθ
    have h := Work.Spaces.pz_Dth_sup_bound α hα 5 _ hs.dU.1 j 0 hj (by omega) z θ hz hθ
    simp only [pow_zero, div_one] at h
    refine h.trans ?_
    exact (mul_le_mul hle (lam_le_two hα hα1 hθ) (lam_nonneg hα hθ) hM0).trans
      (le_of_eq (by ring))

end Work.FTS.Nonlinear.Pieces.RNP.row19
