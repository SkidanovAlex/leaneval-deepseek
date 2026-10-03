import Mathlib
import Submission.Work.FIArea7.UniCharTerm6
import Submission.Work.FIArea7.WUniOmega6Pull6CharLow_aux
import Submission.Work.FIArea7.card_gBox_filter_mod
import Submission.Work.FIArea7.SumChiDefs
import Submission.Work.FIArea7.sum_normSq_fourier_mul
import Submission.Work.FIArea7.card_uniClassFn_fibre_le
import Submission.Work.FIArea7.uniSChar_eq_sum_uniClassFn
import Submission.Work.FIArea7.sum_uniClassFn_normSq_le

set_option autoImplicit false

namespace Work.FIArea7

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-- **Plancherel plus the box fibre count for the §17 character sums.**
`uniSChar Pa Q ε v k χ = Σ_{z ∈ gBox (radN Pa)} unitCoeff Q (uniCoeff ε v k) z · χ(unitClassD Q z)`
is the Fourier transform, over the unit group `G = (ℤ[i]/Q)^*`, of the class function
`a ↦ Σ_{z : unitClassD Q z = a} unitCoeff Q (uniCoeff ε v k) z`; hence Plancherel
`Σ_χ |S_χ|² = |G|·Σ_a |g_a|²`, and each `|g_a|²` is bounded by `M·Σ_{z ≡ a} ‖v z‖²` by
Cauchy–Schwarz, with `M` the number of box points in a class mod `Q`. -/
theorem sumChiNormUniSCharSq {Pa : Work.FITop.Params} (Q : ℕ) [NeZero Q]
    (ε : GaussianInt → ℤ) (v : GaussianInt → ℂ) (k : ℤ)
    (hε : ∀ z : GaussianInt, ‖((ε z : ℤ) : ℂ)‖ ≤ 1) :
    ∑ χ : AddChar (Additive (Work.FIArea7.GaussUnit Q)) ℂ,
        ‖Work.FIArea7.uniSChar Pa Q ε v k χ‖ ^ 2
      ≤ (Fintype.card (Work.FIArea7.GaussUnit Q) : ℝ)
          * ((((2 * Work.FITop.radN Pa + 1).toNat / Q + 1 : ℕ)) : ℝ) ^ 2
          * ∑ z ∈ Work.FIPlan.gBox (Work.FITop.radN Pa), ‖v z‖ ^ 2 := by
  -- 1. `uniSChar` is the Fourier transform of the class function `uniClassFn`
  --    (`unitCoeff` vanishes off the units, so the box sum regroups over the classes).
  have hstep : (∑ χ : AddChar (Additive (GaussUnit Q)) ℂ, ‖uniSChar Pa Q ε v k χ‖ ^ 2)
      = ∑ χ : AddChar (Additive (GaussUnit Q)) ℂ,
          ‖∑ a : GaussUnit Q, uniClassFn Pa Q (uniCoeff ε v k) a * χ (Additive.ofMul a)‖ ^ 2 := by
    refine Finset.sum_congr rfl fun χ _ => ?_
    rw [uniSChar_eq_sum_uniClassFn Pa Q ε v k χ]
  -- 2. Plancherel over the character table of `G = (ℤ[i]/Q)^*`.
  have hplan : (∑ χ : AddChar (Additive (GaussUnit Q)) ℂ,
          ‖∑ a : GaussUnit Q, uniClassFn Pa Q (uniCoeff ε v k) a * χ (Additive.ofMul a)‖ ^ 2)
      = (Fintype.card (GaussUnit Q) : ℝ)
          * ∑ a : GaussUnit Q, ‖uniClassFn Pa Q (uniCoeff ε v k) a‖ ^ 2 :=
    sum_normSq_fourier_mul _
  rw [hstep, hplan]
  -- 3. Cauchy–Schwarz on each class, using the box fibre count and `‖uniCoeff ε v k‖ ≤ ‖v‖`.
  refine le_trans (mul_le_mul_of_nonneg_left
    (sum_uniClassFn_normSq_le Pa Q ε v k hε (((2 * Work.FITop.radN Pa + 1).toNat / Q + 1 : ℕ))
      (fun a => card_uniClassFn_fibre_le Pa Q a)) (Nat.cast_nonneg _)) (le_of_eq ?_)
  ring

end

end Work.FIArea7
