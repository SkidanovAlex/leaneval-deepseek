/-
  WilC4/hsq_hyper : every nonnegative hyperreal is a square.

  Needed to apply the formula-level tools of `WilC2` in the model `HR` (they take
  `hsq : ∀ x, 0 ≤ x → ∃ z, x = z * z` to interpret the definable order of the language).
  The proof is on representatives: `0 ≤ x` is `0 ≤ f a` for almost all `a`, and each such
  `f a` is the square of `Real.sqrt (f a)`.
-/
import Mathlib
import Submission.Work.WilC4.HyperRealCompat

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open Classical FirstOrder FirstOrder.Language
open WilkiesDesign WilkiesDesign.CG

namespace Work.WilC4

/-- The hyperreal field is closed under square roots (it is a real closed field, by Łoś from
`ℝ`); here only the square-root property is needed. -/
theorem hsq_hyper : ∀ x : HR, 0 ≤ x → ∃ z : HR, x = z * z := by
  intro x hx
  obtain ⟨f, hf⟩ : ∃ f : ℕ → ℝ, (↑f : HR) = x := ⟨Quotient.out x, (Quotient.out_eq x)⟩
  have h2 : ∀ᶠ a in (Filter.hyperfilter ℕ : Filter ℕ), 0 ≤ f a := by
    have h3 : (0 : HR) ≤ ↑f := hf ▸ hx
    simpa only [Filter.Germ.coe_nonneg, Filter.Germ.coe_zero] using h3
  refine ⟨↑(fun a => Real.sqrt (f a)), ?_⟩
  rw [← hf]
  rw [← Filter.Germ.coe_mul]
  refine Filter.Germ.coe_eq.mpr ?_
  filter_upwards [h2] with a ha
  simp only [Pi.mul_apply, ← pow_two]
  exact (Real.sq_sqrt ha).symm

end Work.WilC4
