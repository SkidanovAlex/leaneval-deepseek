import Mathlib
import Submission.Commons.Analysis.CalderonZygmund.cz_weak_type_one_measurable_bounded

namespace Commons.Analysis.CalderonZygmund

open _root_.MeasureTheory

set_option autoImplicit false

/-- Weak-type (1,1) bound for a lacunary family of Calderón--Zygmund kernels combined as a
finite sum.  This is the "linearised" version of the second-order Calderón--Zygmund estimate:
the bound only depends on the sum of the individual kernel norms `Aker * K1`, so that the
finite sum can be handled by a single application of the measurable-bounded case with
`K = ∑ N ∈ D, KN N`. -/
theorem cz_weak_type_one_lintegral {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H] [CompleteSpace H] (D : Finset ℝ) (KN : ℝ → ℝ → ℂ) (A2 Aker K1 Bk : ℝ) (hK1 : 1 ≤ K1) (hA2 : 0 < A2) (hAker : 0 < Aker) (hKbdd : ∀ N ∈ D, ∀ x : ℝ, ‖KN N x‖ ≤ Bk) (hmeas : ∀ N ∈ D, Measurable (KN N)) (hker : ∀ L : ℝ, 0 < L → ∀ y : ℝ, |y| ≤ L / 2 → ∑ N ∈ D, ∫⁻ x in {x : ℝ | 50 * L ≤ |x|}, ‖KN N (x - y) - KN N x‖ₑ ≤ ENNReal.ofReal (Aker * K1)) (hstrong : ∀ f : ℝ → H, MeasureTheory.Integrable f → MeasureTheory.eLpNorm (fun x : ℝ => ∫ y : ℝ, (∑ N ∈ D, KN N (x - y)) • f y) 2 MeasureTheory.volume ≤ ENNReal.ofReal A2 * MeasureTheory.eLpNorm f 2 MeasureTheory.volume) (f : ℝ → H) (hf : MeasureTheory.Integrable f) : ∀ α : ℝ, 0 < α → MeasureTheory.volume {x : ℝ | α < ‖∫ y : ℝ, (∑ N ∈ D, KN N (x - y)) • f y‖} ≤ ENNReal.ofReal ((24 * A2 ^ 2 + 4 * Aker * K1 + 100) / α) * MeasureTheory.eLpNorm f 1 MeasureTheory.volume := by
  -- The combined kernel `K = ∑ N ∈ D, KN N`.
  have hB : ∀ z : ℝ, ‖∑ N ∈ D, KN N z‖ ≤ ∑ N ∈ D, Bk := by
    intro z
    calc ‖∑ N ∈ D, KN N z‖ ≤ ∑ N ∈ D, ‖KN N z‖ := norm_sum_le D (fun N => KN N z)
      _ ≤ ∑ N ∈ D, Bk := Finset.sum_le_sum (fun N hN => hKbdd N hN z)
  have hKmeas : Measurable (fun z : ℝ => ∑ N ∈ D, KN N z) :=
    Finset.measurable_sum D (fun N hN => hmeas N hN)
  -- The Hörmander-type condition for the combined kernel, with constant `Aker * K1`.
  have hkerK : ∀ L : ℝ, 0 < L → ∀ y : ℝ, |y| ≤ L / 2 →
      ∫⁻ x in {x : ℝ | 50 * L ≤ |x|},
        ‖(∑ N ∈ D, KN N (x - y)) - (∑ N ∈ D, KN N x)‖ₑ ≤ ENNReal.ofReal (Aker * K1) := by
    intro L hL y hy
    have hpt : ∀ x : ℝ, ‖(∑ N ∈ D, KN N (x - y)) - (∑ N ∈ D, KN N x)‖ₑ
        ≤ ∑ N ∈ D, ‖KN N (x - y) - KN N x‖ₑ := by
      intro x
      rw [← Finset.sum_sub_distrib]
      exact enorm_sum_le D (fun N => KN N (x - y) - KN N x)
    calc ∫⁻ x in {x : ℝ | 50 * L ≤ |x|}, ‖(∑ N ∈ D, KN N (x - y)) - (∑ N ∈ D, KN N x)‖ₑ
        ≤ ∫⁻ x in {x : ℝ | 50 * L ≤ |x|}, ∑ N ∈ D, ‖KN N (x - y) - KN N x‖ₑ :=
          lintegral_mono (fun x => hpt x)
      _ = ∑ N ∈ D, ∫⁻ x in {x : ℝ | 50 * L ≤ |x|}, ‖KN N (x - y) - KN N x‖ₑ := by
          refine lintegral_finsetSum D (fun N hN => ?_)
          have hshift : Measurable (fun x : ℝ => x - y) := measurable_id.sub measurable_const
          exact (((hmeas N hN).comp hshift).sub (hmeas N hN)).enorm
      _ ≤ ENNReal.ofReal (Aker * K1) := hker L hL y hy
  intro α hα
  have key := cz_weak_type_one_measurable_bounded (fun z : ℝ => ∑ N ∈ D, KN N z) A2 (Aker * K1)
    (∑ N ∈ D, Bk) hA2 (mul_nonneg (le_of_lt hAker) (by linarith)) hB hKmeas hkerK hstrong f hf α hα
  simpa only [mul_assoc] using key

end Commons.Analysis.CalderonZygmund
