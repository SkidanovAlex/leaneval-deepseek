/-
# ZeroFreeTables/P9/prim/SigmaP3L_eq_moments

`SigmaP3L` is HB's `Σ(s,χ)` of (8.4) with a free logarithmic scale `L` and the
coefficient-correct weight `u(y) = α + α²y + (1/3)α³y²` (`α = a + λ₁`):

`Σ(s,χ) = L⁻¹ Σ_n Λ(n) Re(χ(n)n^{-s}) u(log n / L)`.

Expanding `u` and splitting the (absolutely convergent, `Re s > 1`) series into its three
logarithmic moments `M_j = Σ_n Λ(n) Re(χ(n)n^{-s}) (log n)^j` gives the polynomial identity

`Σ(s,χ) = (α/L)·M₀ + (α/L)²·M₁ + (1/3)(α/L)³·M₂`,

which is the algebraic half of the computation `Σ(s,χ) = -Σ_ρ Re P₃(α/((s-ρ)L)) + O(1)` of
HB §8.  The analytic input is the absolute convergence (`SummableVonMangoldtLogPow`); the
rest is linearity of the sum.
-/
import Mathlib
import Submission.Work.ZeroFreeTables.P9.SigmaP3LCoeffs
import Submission.Work.ZeroFreeTables.P3.SummableVonMangoldtLogPow

open ArithmeticFunction
open scoped Classical BigOperators
noncomputable section

set_option maxHeartbeats 1000000

namespace Work.ZeroFreeTables.P9.prim

open Work.ZeroFreeTables

/-- The `n`-th summand of the twisted von Mangoldt series, `Re(χ(n) / n^s)`, agrees with
`chiTwistRe`: `χ(n)/n^s = χ(n)·n^{-s}`. -/
lemma chiTwistRe_eq_div {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (s : ℂ) (n : ℕ) :
    chiTwistRe χ s n = (χ (n : ZMod N) / (n : ℂ) ^ s).re := by
  rw [chiTwistRe, Complex.cpow_neg, div_eq_mul_inv]

/-- `|Re(χ(n) n^{-s})| ≤ n^{-Re s}`, from `‖χ(n)‖ ≤ 1` and `‖n^{-s}‖ = n^{-Re s}`. -/
lemma chiTwistRe_abs_le {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) {s : ℂ}
    (hs : 1 < s.re) (n : ℕ) :
    |chiTwistRe χ s n| ≤ (n : ℝ) ^ (-s.re) := by
  have hsne : (-s).re ≠ 0 := by rw [Complex.neg_re]; linarith
  rw [chiTwistRe]
  calc |((χ (n:ZMod N) : ℂ) * (n:ℂ)^(-s)).re|
      ≤ ‖(χ (n:ZMod N) : ℂ) * (n:ℂ)^(-s)‖ := Complex.abs_re_le_norm _
    _ = ‖(χ (n:ZMod N) : ℂ)‖ * ‖(n:ℂ)^(-s)‖ := norm_mul _ _
    _ = ‖(χ (n:ZMod N) : ℂ)‖ * (n:ℝ)^(-s.re) := by
          rw [Complex.norm_natCast_cpow_of_re_ne_zero n hsne, Complex.neg_re]
    _ ≤ 1 * (n:ℝ)^(-s.re) :=
          mul_le_mul_of_nonneg_right (DirichletCharacter.norm_le_one χ _)
            (Real.rpow_nonneg (Nat.cast_nonneg n) _)
    _ = (n:ℝ)^(-s.re) := one_mul _

/-- Absolute convergence of the `j`-th logarithmic moment
`Σ_n Λ(n) Re(χ(n)n^{-s}) (log n)^j` for `Re s > 1`. -/
lemma summable_vonMangoldtMoment {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (j : ℕ)
    {s : ℂ} (hs : 1 < s.re) :
    Summable (fun n : ℕ => ArithmeticFunction.vonMangoldt n * chiTwistRe χ s n *
      (Real.log n) ^ j) := by
  refine Summable.of_norm_bounded (P3.SummableVonMangoldtLogPow hs j) fun n => ?_
  have hlog : 0 ≤ Real.log (n:ℝ) := Real.log_natCast_nonneg n
  have hL : 0 ≤ ArithmeticFunction.vonMangoldt n := ArithmeticFunction.vonMangoldt_nonneg
  rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg hL, abs_of_nonneg (pow_nonneg hlog j)]
  refine le_trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (chiTwistRe_abs_le χ hs n) hL) (pow_nonneg hlog j)) ?_
  rw [Real.rpow_neg (Nat.cast_nonneg n), div_eq_mul_inv]
  exact le_of_eq (by ring)

theorem SigmaP3L_eq_moments {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) {s : ℂ} (hs : 1 < s.re) (a lam₁ L : ℝ) : Work.ZeroFreeTables.SigmaP3L N L χ s a lam₁ = ((a + lam₁) / L) * Work.ZeroFreeTables.vonMangoldtMoment χ s 0 + ((a + lam₁) / L) ^ 2 * Work.ZeroFreeTables.vonMangoldtMoment χ s 1 + (1 / 3) * ((a + lam₁) / L) ^ 3 * Work.ZeroFreeTables.vonMangoldtMoment χ s 2 := by
  set α : ℝ := a + lam₁ with hα
  have hsummG : ∀ j : ℕ, Summable (fun n : ℕ => ArithmeticFunction.vonMangoldt n * chiTwistRe χ s n *
      (Real.log n) ^ j) := fun j => summable_vonMangoldtMoment χ j hs
  have hM0 : vonMangoldtMoment χ s 0 = ∑' n : ℕ, ArithmeticFunction.vonMangoldt n * chiTwistRe χ s n := by
    have hab : vonMangoldtMoment χ s 0
        = ∑' n : ℕ, ArithmeticFunction.vonMangoldt n * chiTwistRe χ s n * (Real.log n)^0 := rfl
    rw [hab]
    exact tsum_congr fun n => by ring
  have hM1 : vonMangoldtMoment χ s 1 = ∑' n : ℕ, ArithmeticFunction.vonMangoldt n * chiTwistRe χ s n * Real.log n := by
    have hab : vonMangoldtMoment χ s 1
        = ∑' n : ℕ, ArithmeticFunction.vonMangoldt n * chiTwistRe χ s n * (Real.log n)^1 := rfl
    rw [hab]
    exact tsum_congr fun n => by ring
  have hM2 : vonMangoldtMoment χ s 2 = ∑' n : ℕ, ArithmeticFunction.vonMangoldt n * chiTwistRe χ s n * (Real.log n) ^ 2 := rfl
  have hsumA : Summable (fun n : ℕ => ArithmeticFunction.vonMangoldt n * chiTwistRe χ s n * α) := by
    simpa only [pow_zero, mul_one] using (hsummG 0).mul_right α
  have hsumB : Summable (fun n : ℕ => (α^2 * L⁻¹) *
      (ArithmeticFunction.vonMangoldt n * chiTwistRe χ s n * Real.log n)) := by
    simpa only [pow_one] using (hsummG 1).mul_left (α^2 * L⁻¹)
  have hsumC : Summable (fun n : ℕ => ((1/3) * α^3 * (L⁻¹)^2) *
      (ArithmeticFunction.vonMangoldt n * chiTwistRe χ s n * (Real.log n)^2)) := by
    exact (hsummG 2).mul_left ((1/3) * α^3 * (L⁻¹)^2)
  have htsumA : ∑' n : ℕ, ArithmeticFunction.vonMangoldt n * chiTwistRe χ s n * α
      = α * vonMangoldtMoment χ s 0 := by
    rw [tsum_mul_right, ← hM0, mul_comm]
  have htsumB : ∑' n : ℕ, (α^2 * L⁻¹) *
      (ArithmeticFunction.vonMangoldt n * chiTwistRe χ s n * Real.log n)
      = (α^2 * L⁻¹) * vonMangoldtMoment χ s 1 := by
    rw [tsum_mul_left, ← hM1]
  have htsumC : ∑' n : ℕ, ((1/3) * α^3 * (L⁻¹)^2) *
      (ArithmeticFunction.vonMangoldt n * chiTwistRe χ s n * (Real.log n)^2)
      = ((1/3) * α^3 * (L⁻¹)^2) * vonMangoldtMoment χ s 2 := by
    rw [tsum_mul_left, ← hM2]
  have hPQR : ∑' n : ℕ, ((ArithmeticFunction.vonMangoldt n * chiTwistRe χ s n * α)
        + ((α^2 * L⁻¹) * (ArithmeticFunction.vonMangoldt n * chiTwistRe χ s n * Real.log n))
        + (((1/3) * α^3 * (L⁻¹)^2) * (ArithmeticFunction.vonMangoldt n * chiTwistRe χ s n * (Real.log n)^2)))
      = α * vonMangoldtMoment χ s 0 + (α^2 * L⁻¹) * vonMangoldtMoment χ s 1
        + ((1/3) * α^3 * (L⁻¹)^2) * vonMangoldtMoment χ s 2 := by
    rw [Summable.tsum_add (hsumA.add hsumB) hsumC, Summable.tsum_add hsumA hsumB, htsumA, htsumB, htsumC]
  have hpoint : ∀ n : ℕ, ArithmeticFunction.vonMangoldt n * chiTwistRe χ s n *
        (α + α^2 * (Real.log n / L) + (1/3) * α^3 * (Real.log n / L)^2)
      = (ArithmeticFunction.vonMangoldt n * chiTwistRe χ s n * α)
        + ((α^2 * L⁻¹) * (ArithmeticFunction.vonMangoldt n * chiTwistRe χ s n * Real.log n))
        + (((1/3) * α^3 * (L⁻¹)^2) * (ArithmeticFunction.vonMangoldt n * chiTwistRe χ s n * (Real.log n)^2)) := by
    intro n; ring
  have hsplit : ∑' n : ℕ, ArithmeticFunction.vonMangoldt n * chiTwistRe χ s n *
        (α + α^2 * (Real.log n / L) + (1/3) * α^3 * (Real.log n / L)^2)
      = α * vonMangoldtMoment χ s 0 + (α^2 * L⁻¹) * vonMangoldtMoment χ s 1
        + ((1/3) * α^3 * (L⁻¹)^2) * vonMangoldtMoment χ s 2 := by
    rw [tsum_congr hpoint, hPQR]
  have hSigma : SigmaP3L N L χ s a lam₁ = L⁻¹ * ∑' n : ℕ, ArithmeticFunction.vonMangoldt n * chiTwistRe χ s n *
        (α + α^2 * (Real.log n / L) + (1/3) * α^3 * (Real.log n / L)^2) := by
    simp only [SigmaP3L]
    rw [← hα]
    congr 1
    exact tsum_congr fun n => by rw [chiTwistRe_eq_div]
  rw [hSigma, hsplit]
  simp only [div_eq_mul_inv]
  ring

end Work.ZeroFreeTables.P9.prim
