import Mathlib
import Submission.Work.BMF.mr_direct_range_defs
import Submission.Work.BMF.mr_direct.range_defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

open Work.BMF.mrDirect
open MeasureTheory

namespace Work.BMF.mr_direct

/-- Set-integral version of `Work.BMF.mrDirect.mainTermR_integral_le`: the mean square of the
main term `Σ_j Q_j(t) R_j(t)` over a measurable set `u ⊆ [-S,S]` is at most the number of window
indices times the sum of the mean squares of the individual products.  (Pointwise
`‖Σ_j f_j‖² ≤ card · Σ_j ‖f_j‖²`, integrated over `u`.)

Template: `Work.BMF.mrDirect.mainTermR_integral_le` in
`Submission/Work/BMF/mr_direct/range_defs.lean` (same statement with `(-S)..S` in place of `u`),
using `sq_sum_le_card_mul_sum_sq` and `MeasureTheory.integral_finsetSum` /
`MeasureTheory.integral_const_mul` for the set integral. -/
lemma mainTermR_set_integral_le (c b : ℕ → ℂ) (K P Q A B S : ℝ) (hA : 0 < A) (hS : 0 ≤ S)
    (u : Set ℝ) (hu : MeasurableSet u) (husub : u ⊆ Set.Icc (-S) S) :
    (∫ t in u, ‖∑ j ∈ Work.BMF.mrDirect.indexSet K P Q,
        Work.BMF.mrDirect.primePoly c K j t *
          Work.BMF.mrDirect.remPolyR b P Q K A B j t‖ ^ 2)
      ≤ ((Work.BMF.mrDirect.indexSet K P Q).card : ℝ) *
          (∑ j ∈ Work.BMF.mrDirect.indexSet K P Q,
            ∫ t in u, ‖Work.BMF.mrDirect.primePoly c K j t *
              Work.BMF.mrDirect.remPolyR b P Q K A B j t‖ ^ 2) := by
  -- any continuous real-valued function is integrable on the measurable set `u ⊆ [-S,S]`
  have integ_of_cont : ∀ {f : ℝ → ℝ}, Continuous f →
      Integrable f (volume.restrict u) := by
    intro f hf
    have h1 : Integrable f (volume.restrict (Set.Icc (-S) S)) :=
      hf.integrableOn_Icc (μ := volume) (a := -S) (b := S)
    exact h1.mono_measure (Measure.restrict_mono husub le_rfl)
  have hcont_j : ∀ j : ℕ, Continuous
      fun t => ‖primePoly c K j t * remPolyR b P Q K A B j t‖ ^ 2 := fun j =>
    ((continuous_primePoly_R c K j).mul (continuous_remPolyR b P Q K A B j hA)).norm.pow 2
  have hcont_F : Continuous
      fun t => ‖∑ j ∈ indexSet K P Q, primePoly c K j t * remPolyR b P Q K A B j t‖ ^ 2 :=
    (continuous_MT_R b c K P Q A B hA).norm.pow 2
  have hcont_G : Continuous fun t => ((indexSet K P Q).card : ℝ) *
      ∑ j ∈ indexSet K P Q, ‖primePoly c K j t * remPolyR b P Q K A B j t‖ ^ 2 :=
    Continuous.mul continuous_const (continuous_finsetSum _ fun j _ => hcont_j j)
  have hint_j : ∀ j ∈ indexSet K P Q,
      Integrable (fun t => ‖primePoly c K j t * remPolyR b P Q K A B j t‖ ^ 2)
        (volume.restrict u) := fun j _ => integ_of_cont (hcont_j j)
  have hint_F : Integrable
      (fun t => ‖∑ j ∈ indexSet K P Q, primePoly c K j t * remPolyR b P Q K A B j t‖ ^ 2)
      (volume.restrict u) := integ_of_cont hcont_F
  have hint_G : Integrable
      (fun t => ((indexSet K P Q).card : ℝ) *
        ∑ j ∈ indexSet K P Q, ‖primePoly c K j t * remPolyR b P Q K A B j t‖ ^ 2)
      (volume.restrict u) := integ_of_cont hcont_G
  -- pointwise `‖Σ_j f_j‖² ≤ card · Σ_j ‖f_j‖²`
  have hpt : ∀ t : ℝ,
      ‖∑ j ∈ indexSet K P Q, primePoly c K j t * remPolyR b P Q K A B j t‖ ^ 2
        ≤ ((indexSet K P Q).card : ℝ) *
          ∑ j ∈ indexSet K P Q, ‖primePoly c K j t * remPolyR b P Q K A B j t‖ ^ 2 := by
    intro t
    calc ‖∑ j ∈ indexSet K P Q, primePoly c K j t * remPolyR b P Q K A B j t‖ ^ 2
        ≤ (∑ j ∈ indexSet K P Q, ‖primePoly c K j t * remPolyR b P Q K A B j t‖) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) (norm_sum_le _ _) 2
      _ ≤ _ := sq_sum_le_card_mul_sum_sq
  -- the constant/cardinality factor comes out of the integral
  have hInt : (∫ t in u, ((indexSet K P Q).card : ℝ) *
        ∑ j ∈ indexSet K P Q, ‖primePoly c K j t * remPolyR b P Q K A B j t‖ ^ 2)
      = ((indexSet K P Q).card : ℝ) *
        (∑ j ∈ indexSet K P Q,
          ∫ t in u, ‖primePoly c K j t * remPolyR b P Q K A B j t‖ ^ 2) := by
    rw [MeasureTheory.integral_const_mul,
      MeasureTheory.integral_finsetSum _ (fun j hj => hint_j j hj)]
  calc (∫ t in u, ‖∑ j ∈ indexSet K P Q,
          primePoly c K j t * remPolyR b P Q K A B j t‖ ^ 2)
      ≤ ∫ t in u, ((indexSet K P Q).card : ℝ) *
          ∑ j ∈ indexSet K P Q, ‖primePoly c K j t * remPolyR b P Q K A B j t‖ ^ 2 :=
        MeasureTheory.integral_mono_ae hint_F hint_G (Filter.Eventually.of_forall hpt)
    _ = ((indexSet K P Q).card : ℝ) *
          (∑ j ∈ indexSet K P Q,
            ∫ t in u, ‖primePoly c K j t * remPolyR b P Q K A B j t‖ ^ 2) := hInt

end Work.BMF.mr_direct
