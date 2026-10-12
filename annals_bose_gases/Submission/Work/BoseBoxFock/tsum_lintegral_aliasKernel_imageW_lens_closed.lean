import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFock.aliasImgTerm_low_ne_top
import Submission.Work.BoseBoxFock.aliasImgTerm_tail_sum_le
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.tsum_lintegral_aliasKernel_imageW_lens_closed`

The `ℝ≥0∞`-summability of the image series of the first-moment deficit at the **closed-ball**
support class `tsupport g ⊆ closedBall 0 (ℓ/2)` (the class of the admissible states
`g = χ_Λ·h`):

    ∑'_m ∫⁻_u ofReal(‖𝒢(u)‖ · imgW ℓ m u) ≠ ⊤ ,   𝒢 = aliasKernel g ,  imgW ℓ m u = ‖u−ℓm‖⁻⁴ .

This is the closed-ball twin of `Work.BoseBoxFock.tsum_lintegral_aliasKernel_imageW_lens`
(open-ball class), and the analytic input of `aliasImageIdentity_closed`.

**Route.**  The lattice is split at the sup-norm `‖m‖ = 1`:

* `box 1 = {-1,0,1}³` is exactly the index set `{m | ‖m‖ ≤ 1}`, whose translates `ℓ • latVec m`
  can meet the ball `closedBall 0 ℓ`; the *lens* bound
  `‖𝒢(u)‖ ≤ C(ℓ²−‖u‖²)^{3/2} ≤ C(2ℓ)^{3/2}‖u − ℓ m‖^{3/2}` turns the `‖u − ℓ m‖⁻⁴` singularity
  into the locally integrable `‖u − ℓ m‖^{-5/2}`, so each such term is finite
  (`aliasImgTerm_low_ne_top`); a finite sum of finite terms is finite.
* for `2 ≤ ‖m‖` the reverse triangle inequality `‖u − ℓ m‖ ≥ ℓ(‖m‖ − 1)` on the ball gives the
  summable lattice weight `(‖m‖−1)⁻⁴`, bounded by `200` over any finite set of indices
  (`aliasImgTerm_tail_sum_le`, via `lattice_sum_inv_fourth_le`).

Every finite partial sum is then dominated by the sum of those two finite quantities, and
`∑' = ⨆_{s finite} ∑_{m ∈ s}` (`ENNReal.tsum_eq_iSup_sum`) finishes.
-/

namespace Work.BoseBoxFock

open MeasureTheory
open scoped Real BigOperators ENNReal

local notation "E3" => EuclideanSpace ℝ (Fin 3)

theorem tsum_lintegral_aliasKernel_imageW_lens_closed {ℓ : ℝ} (hℓ : 0 < ℓ)
    {g : EuclideanSpace ℝ (Fin 3) → ℂ} (hg : ContDiff ℝ (⊤ : ENat) g)
    (hgsupp : tsupport g ⊆ Metric.closedBall 0 (ℓ / 2)) :
    (∑' m : Fin 3 → ℤ, ∫⁻ u : EuclideanSpace ℝ (Fin 3),
        ENNReal.ofReal (‖Work.BoseBoxFock.aliasKernel g u‖ *
          Work.BoseBoxFock.imgW ℓ m u)) ≠ ⊤ := by
  change (∑' m : Fin 3 → ℤ, aliasImgTerm ℓ g m) ≠ ⊤
  rw [ENNReal.tsum_eq_iSup_sum]
  -- the low indices `box 1 = {m | ‖m‖ ≤ 1}`
  have hlow_mem : ∀ m : Fin 3 → ℤ, m ∈ box 1 ↔ ‖m‖ ≤ 1 := by
    intro m
    constructor
    · intro hm
      rw [pi_norm_le_iff_of_nonneg zero_le_one]
      intro i
      rw [Int.norm_eq_abs]
      have h1 : (m i).natAbs ≤ 1 := (mem_box_iff 1 m).mp hm i
      have h2 := (natAbs_le_iff (m i) 1).mp h1
      rw [abs_le]
      exact_mod_cast h2
    · intro hm
      rw [mem_box_iff]
      intro i
      have h1 : ‖m i‖ ≤ 1 := (pi_norm_le_iff_of_nonneg zero_le_one).mp hm i
      rw [Int.norm_eq_abs] at h1
      rw [natAbs_le_iff]
      exact_mod_cast (abs_le.mp h1)
  -- the low block is a finite sum of finite terms
  have hT1 : (∑ m ∈ box 1, aliasImgTerm ℓ g m) ≠ ⊤ := by
    rw [ENNReal.sum_ne_top]
    intro m hm
    by_cases hm0 : m = 0
    · subst hm0
      simp [aliasImgTerm, imgW_zero]
    · exact aliasImgTerm_low_ne_top hℓ hg hgsupp m hm0 ((hlow_mem m).mp hm)
  -- the far block
  have hT2 : ENNReal.ofReal ((∫ x : E3, ‖g x‖ ^ 2) * ℓ ^ (-(4 : ℝ)) * 200)
      * (MeasureTheory.volume (Metric.closedBall (0 : E3) ℓ)) < ⊤ :=
    ENNReal.mul_lt_top ENNReal.ofReal_lt_top
      (isCompact_closedBall (0 : E3) ℓ).measure_lt_top
  -- the bound for every finite partial sum
  have hbound : ∀ s : Finset (Fin 3 → ℤ), (∑ m ∈ s, aliasImgTerm ℓ g m)
      ≤ (∑ m ∈ box 1, aliasImgTerm ℓ g m)
        + ENNReal.ofReal ((∫ x : E3, ‖g x‖ ^ 2) * ℓ ^ (-(4 : ℝ)) * 200)
          * (MeasureTheory.volume (Metric.closedBall (0 : E3) ℓ)) := by
    intro s
    rw [← Finset.sum_filter_add_sum_filter_not (s := s) (p := fun m => ‖m‖ ≤ 1)
      (f := fun m => aliasImgTerm ℓ g m)]
    refine add_le_add ?_ ?_
    · refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
      · intro m hm
        exact (hlow_mem m).mpr (Finset.mem_filter.mp hm).2
      · intro m _ _
        exact bot_le
    · refine aliasImgTerm_tail_sum_le hℓ hg hgsupp _ ?_
      intro m hm
      have h1 : ¬ (‖m‖ ≤ 1) := (Finset.mem_filter.mp hm).2
      have h2 : (1 : ℝ) < (K m : ℝ) := by
        rw [← NormEqKcast m]
        exact not_le.mp h1
      have h3 : (1 : ℕ) < K m := by exact_mod_cast h2
      calc (2 : ℝ) ≤ (K m : ℝ) := by exact_mod_cast (show (2 : ℕ) ≤ K m from h3)
        _ = ‖m‖ := (NormEqKcast m).symm
  refine ne_of_lt (lt_of_le_of_lt (iSup_le hbound) ?_)
  exact ENNReal.add_lt_top.mpr ⟨lt_top_iff_ne_top.mpr hT1, hT2⟩

end Work.BoseBoxFock
