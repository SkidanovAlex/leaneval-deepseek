import Mathlib
import Submission.Work.FITop4.Defs4
import Submission.Work.FITop3.Assembly.cauchy_exists

set_option autoImplicit false

namespace Work.FITop4.Red4

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-- **The Cauchy–Schwarz step (5.17) of the paper, in the form the reduction consumes.**

`Dform Pa f β` is (5.18), `Σ_{w ∈ boxM} f(|w|²)·|X_w|²` with the blocks
`X_w = Σ_{z ∈ boxN} β_z Z(Re wz)`; on the dyadic annulus `annM Pa` the majorant satisfies
`f ≥ 1`, and `annM Pa ⊆ boxM Pa`, so `Σ_{w ∈ annM} |X_w|² ≤ Dform Pa f β`.  Cauchy–Schwarz over
the finitely many `w`'s, together with the count `card (annM Pa) ≤ 100·M`
(`Work.FITop3.Assembly.card_annM_le`), gives the factor `100·M`:

  `(Σ_{w ∈ annM} |X_w|)² ≤ (card annM)·Σ_{w ∈ annM} |X_w|² ≤ 100·M·Dform Pa f β`.

This is the `Bfree`-free half of `Work.FITop3.Assembly.cauchy_exists`: the norm of the *sum* of
the blocks `Bfree` is replaced by the sum of the norms of the blocks, which is what the
`Σ_m |Σ_n ⋯|` form `BformPi`/`BformAtil` of (4.3) produces. -/
theorem sum_norm_inner_le (Pa : Work.FITop.Params) (f : ℤ → ℝ) (β : GaussianInt → ℂ)
    (hMaj : IsMajorant Pa f) :
    (∑ w ∈ Work.FITop3.annM Pa, ‖∑ z ∈ Work.FITop.boxN Pa, β z * Work.FITop3.Zc w z‖) ^ 2
      ≤ 100 * Pa.M * Dform Pa f β := by
  obtain ⟨hf0, hf1, hfann, hfsupp, hfd1, hfd2⟩ := hMaj
  set X : GaussianInt → ℂ :=
    fun w => ∑ z ∈ Work.FITop.boxN Pa, β z * Work.FITop3.Zc w z with hX
  have hcard : (0 : ℝ) ≤ ((Work.FITop3.annM Pa).card : ℝ) := by positivity
  have hCS : (∑ w ∈ Work.FITop3.annM Pa, ‖X w‖) ^ 2
      ≤ ((Work.FITop3.annM Pa).card : ℝ) * ∑ w ∈ Work.FITop3.annM Pa, ‖X w‖ ^ 2 :=
    sq_sum_le_card_mul_sum_sq
  have hDform_eq : Dform Pa f β
      = ∑ w ∈ Work.FITop.boxM Pa, f (Work.FIPlan.gnorm w) * ‖X w‖ ^ 2 := by
    simp only [Dform, Work.FITop3.Dform, Complex.normSq_eq_norm_sq, hX]
  have hDnn : (0 : ℝ) ≤ Dform Pa f β := by
    rw [hDform_eq]
    exact Finset.sum_nonneg fun w _ => mul_nonneg (hf0 _) (sq_nonneg _)
  have hle : ∑ w ∈ Work.FITop3.annM Pa, ‖X w‖ ^ 2 ≤ Dform Pa f β := by
    rw [hDform_eq]
    have hsub : Work.FITop3.annM Pa ⊆ Work.FITop.boxM Pa := Work.FITop3.annM_subset_boxM Pa
    have hpt : ∀ w ∈ Work.FITop3.annM Pa,
        ‖X w‖ ^ 2 ≤ f (Work.FIPlan.gnorm w) * ‖X w‖ ^ 2 := by
      intro w hw
      obtain ⟨_, hMlt, hMle⟩ := Work.FITop3.mem_annM.mp hw
      have h1 : 1 ≤ f (Work.FIPlan.gnorm w) := hfann w hMlt hMle
      nlinarith [sq_nonneg ‖X w‖]
    calc ∑ w ∈ Work.FITop3.annM Pa, ‖X w‖ ^ 2
        ≤ ∑ w ∈ Work.FITop3.annM Pa, f (Work.FIPlan.gnorm w) * ‖X w‖ ^ 2 :=
          Finset.sum_le_sum hpt
      _ ≤ ∑ w ∈ Work.FITop.boxM Pa, f (Work.FIPlan.gnorm w) * ‖X w‖ ^ 2 :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub
            (fun w _ _ => mul_nonneg (hf0 _) (sq_nonneg _))
  calc (∑ w ∈ Work.FITop3.annM Pa, ‖X w‖) ^ 2
      ≤ ((Work.FITop3.annM Pa).card : ℝ) * ∑ w ∈ Work.FITop3.annM Pa, ‖X w‖ ^ 2 := hCS
    _ ≤ ((Work.FITop3.annM Pa).card : ℝ) * Dform Pa f β := mul_le_mul_of_nonneg_left hle hcard
    _ ≤ 100 * Pa.M * Dform Pa f β :=
        mul_le_mul_of_nonneg_right (Work.FITop3.Assembly.card_annM_le Pa) hDnn

end

end Work.FITop4.Red4
