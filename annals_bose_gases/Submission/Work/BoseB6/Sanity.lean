import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.BoseB6.BogHamDiag
import Submission.Work.BoseB6.Scaled
import Submission.Work.BoseBox.pairBogolubov_identity
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Node B6 — non-vacuity checks

The audit's standing worry is a statement that is true only because its
hypotheses are uninhabitable.  This module instantiates the two interfaces of
the chapter at explicit data:

* `bogHamInterfaceExample` — a one-pair `BogHamInterface` (FS's `𝒜 = 2`,
  `ℬ = 1`, `𝒞 = 0`, i.e. `τ/ρ_zŴ₁` in a `1 : 2` ratio, `s = √3`) with
  `q = −(𝒜−√(𝒜²−ℬ²))` and `Kbog = ½q`, so `sum_pairGround_le` applies and gives
  a concrete lower bound on a concrete real number;
* `scaledKernelExample` — a `ScaledKernel` (the FS `β`-interface) with
  `β ≡ 8π` on `[0,1]` and `0` beyond, `B = 8π`, `η = 16π`, `T = 1`.

Both are non-trivial inhabitants, so the hypotheses of `sum_pairGround_le`,
`bogHamDiag_fs` and `fsTau_bounds` are consistent.
-/

noncomputable section

open scoped BigOperators

namespace Work.BoseB6

/-- A one-pair instance of **B4's interface** for `thm:BogHamDiag`: FS's
`𝒜 = 2`, `ℬ = 1` (`s = √3 > 0`), `𝒞 = 0`, the pair form value
`q = −(𝒜−√(𝒜²−ℬ²))`, and `Kbog = ½q` (the mode decomposition for a single
pair). -/
def bogHamInterfaceExample : BogHamInterface (Fin 1) where
  Kbog := -(1 / 2) * bogZeroPoint 2 1
  A := fun _ => 2
  B := fun _ => 1
  Ccoef := fun _ => 0
  q := fun _ => -bogZeroPoint 2 1
  Apos := by intro k; norm_num
  Bsmall := by intro k; norm_num
  AplusB := by intro k; norm_num
  decomp := by
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    ring
  pairGround := by
    intro k
    simp only [bogKappaErr, mul_zero, zero_pow, div_zero, add_zero]
    linarith [bogZeroPoint_nonneg (A := (2 : ℝ)) (B := 1) (by norm_num) (by norm_num)]

/-- `sum_pairGround_le` applied to the explicit one-pair interface: a concrete
non-vacuous instance, `Kbog = −½(2−√3)`. -/
theorem bogHamInterfaceExample_bound :
    -(1 / 2) * ((∑ k, bogZeroPoint (bogHamInterfaceExample.A k) (bogHamInterfaceExample.B k)) +
        (∑ k, bogKappaErr (bogHamInterfaceExample.A k) (bogHamInterfaceExample.B k)
          (bogHamInterfaceExample.Ccoef k))) ≤ bogHamInterfaceExample.Kbog :=
  sum_pairGround_le bogHamInterfaceExample

/-- A `ScaledKernel` (FS's scaled kernel `β(t) = a⁻¹Ŵ₁(√(ρ_z a)t)` interface):
`β = 8π` on `[0,1]`, `0` beyond, `B = 8π`, `η = 16π`, `T = 1`.  This shows the
hypotheses of the `lem:BogIntegral` interface are consistent (in particular
`β(0) = 8π`). -/
def scaledKernelExample : ScaledKernel where
  β := fun r => if r ≤ 1 then 8 * Real.pi else 0
  B := 8 * Real.pi
  η := 16 * Real.pi
  T := 1
  Bnn := by positivity
  ηnn := by positivity
  Tnn := by norm_num
  nonneg := by
    intro r
    split
    · positivity
    · exact le_refl 0
  bound := by
    intro r
    split
    · exact le_refl _
    · exact le_of_lt (by positivity)
  close := by
    intro r hr
    by_cases h1 : r ≤ 1
    · rw [if_pos h1, sub_self, abs_zero]
      nlinarith [Real.pi_pos, hr]
    · rw [if_neg h1]
      have hr1 : 1 ≤ r := le_of_not_ge h1
      have h8 : (0 : ℝ) < 8 * Real.pi := by positivity
      rw [abs_of_nonpos (by linarith)]
      nlinarith [Real.pi_pos, hr1]
  support := by
    intro r hr
    rw [if_neg (by linarith)]

/-- The FS `Ŵ₁(0) = 8πa` normalisation for the example kernel: `β(0) = 8π`. -/
theorem scaledKernelExample_beta_zero : scaledKernelExample.β 0 = 8 * Real.pi :=
  scaledKernelExample.beta_zero

end Work.BoseB6
