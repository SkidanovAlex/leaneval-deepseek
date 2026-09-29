import Mathlib
import Submission.Work.C17.seventeen_defs
import Submission.CDT.LogMIdentities
import Submission.Work.CLift.defs
import Submission.Work.CLift.analytic
import Submission.Work.C17f.deriv_hasSum_powSeries
import Submission.Work.C17f.abs_summable_powSeries

/-!
# `Pfun` solves the operator `M` on its disc of convergence

This is the function-level form of `Submission.CDT.logP_ode`: the power series
`f = logP a b ra rb rab r0` satisfies `M(f) = rhoMx a b ra rb rab` coefficientwise, and on the
disc of convergence of `f` the evaluation `evA` (which is `Pfun` by definition) is compatible
with products, sums and (via `deriv_hasSum_powSeries`) with differentiation.  Hence

`P₂(z)·Pfun''(z) + P₁(z)·Pfun'(z) + P₀(z)·Pfun(z) = rhoMx(z)`  for `‖z‖ < x_s`.
-/

namespace Work.C17f

open PowerSeries
open scoped BigOperators

noncomputable section

/-! ## The right-hand side, as a polynomial -/

/-- `−b + 3aX − 3bX² + aX³`, the first summand of the right-hand side of `logP_ode`. -/
def RaP (a b : ℚ) : Polynomial ℚ :=
  Polynomial.C (-b) * Polynomial.X ^ 0 + Polynomial.C (3 * a) * Polynomial.X ^ 1
    + Polynomial.C (-(3 * b)) * Polynomial.X ^ 2 + Polynomial.C a * Polynomial.X ^ 3

/-- `−a + 3bX − 3aX² + bX³`, the second summand of the right-hand side of `logP_ode`. -/
def RbP (a b : ℚ) : Polynomial ℚ :=
  Polynomial.C (-a) * Polynomial.X ^ 0 + Polynomial.C (3 * b) * Polynomial.X ^ 1
    + Polynomial.C (-(3 * a)) * Polynomial.X ^ 2 + Polynomial.C b * Polynomial.X ^ 3

/-- `−1 + 2X² − X⁴`, the third summand of the right-hand side of `logP_ode`. -/
def RabP : Polynomial ℚ :=
  Polynomial.C (-1) * Polynomial.X ^ 0 + Polynomial.C (2 : ℚ) * Polynomial.X ^ 2
    + Polynomial.C (-1) * Polynomial.X ^ 4

lemma RaP_coe (a b : ℚ) :
    ((RaP a b : Polynomial ℚ) : PowerSeries ℚ) = Submission.CDT.RaFam a b := by
  simp only [RaP, Submission.CDT.RaFam]; push_cast; ring

lemma RbP_coe (a b : ℚ) :
    ((RbP a b : Polynomial ℚ) : PowerSeries ℚ) = Submission.CDT.RbFam a b := by
  simp only [RbP, Submission.CDT.RbFam]; push_cast; ring

lemma RabP_coe (a b : ℚ) :
    ((RabP : Polynomial ℚ) : PowerSeries ℚ) = Submission.CDT.RabFam a b := by
  simp only [RabP, Submission.CDT.RabFam]; push_cast; ring

/-- `rhoMx` is the polynomial of which `C ra * RaFam + C rb * RbFam + C rab * RabFam` is the
power-series expansion. -/
lemma rhoMx_eq_poly (a b : ℚ) (ra rb rab : ℤ) :
    Work.C17.rhoMx a b ra rb rab
      = Polynomial.C (ra : ℚ) * RaP a b + Polynomial.C (rb : ℚ) * RbP a b
        + Polynomial.C (rab : ℚ) * RabP := by
  rw [Work.C17.rhoMx, RaP, RbP, RabP]
  simp only [pow_zero, mul_one, map_mul, map_add, map_neg, map_one, map_ofNat, map_natCast]
  ring

/-- Evaluation of the right-hand side of the ODE. -/
lemma evA_rhoMx (a b : ℚ) (ra rb rab : ℤ) (z : ℂ) :
    Work.CLift.evA (PowerSeries.C (ra : ℚ) * Submission.CDT.RaFam a b
        + PowerSeries.C (rb : ℚ) * Submission.CDT.RbFam a b
        + PowerSeries.C (rab : ℚ) * Submission.CDT.RabFam a b) z
      = (Work.C17.rhoMx a b ra rb rab).eval₂ (algebraMap ℚ ℂ) z := by
  have hcoe : PowerSeries.C (ra : ℚ) * Submission.CDT.RaFam a b
        + PowerSeries.C (rb : ℚ) * Submission.CDT.RbFam a b
        + PowerSeries.C (rab : ℚ) * Submission.CDT.RabFam a b
      = ((Polynomial.C (ra : ℚ) * RaP a b + Polynomial.C (rb : ℚ) * RbP a b
          + Polynomial.C (rab : ℚ) * RabP : Polynomial ℚ) : PowerSeries ℚ) := by
    simp only [Polynomial.coe_add, Polynomial.coe_mul, Polynomial.coe_C, RaP_coe a b,
      RbP_coe a b, RabP_coe a b]
  rw [hcoe, Work.CLift.evA_coe_poly, ← rhoMx_eq_poly a b ra rb rab]

/-! ## Summability of products -/

/-- A polynomial, viewed as a power series, is absolutely summable at every point. -/
lemma summable_norm_coe_poly (p : Polynomial ℚ) (z : ℂ) :
    Summable (fun k : ℕ => ‖((PowerSeries.coeff k (p : PowerSeries ℚ) : ℚ) : ℂ) * z ^ k‖) := by
  refine summable_of_ne_finset_zero (s := Finset.range (p.natDegree + 1)) fun k hk => ?_
  rw [Finset.mem_range, not_lt] at hk
  rw [Polynomial.coeff_coe, Polynomial.coeff_eq_zero_of_natDegree_lt hk]
  simp

/-- The Cauchy product of two absolutely summable series is pointwise given by the antidiagonal
sums. -/
lemma antidiag_term (A B : PowerSeries ℚ) (z : ℂ) (n : ℕ) :
    (∑ kl ∈ Finset.HasAntidiagonal.antidiagonal n,
        ((PowerSeries.coeff kl.1 A : ℚ) : ℂ) * z ^ kl.1
          * (((PowerSeries.coeff kl.2 B : ℚ) : ℂ) * z ^ kl.2))
      = ((PowerSeries.coeff n (A * B) : ℚ) : ℂ) * z ^ n := by
  rw [PowerSeries.coeff_mul]
  push_cast
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun kl hkl => ?_
  rw [Finset.HasAntidiagonal.mem_antidiagonal] at hkl
  rw [← hkl, pow_add]
  ring

/-- The product of two absolutely summable power series is absolutely summable. -/
lemma summable_norm_coeff_mul (A B : PowerSeries ℚ) (z : ℂ)
    (hA : Summable fun k => ‖((PowerSeries.coeff k A : ℚ) : ℂ) * z ^ k‖)
    (hB : Summable fun k => ‖((PowerSeries.coeff k B : ℚ) : ℂ) * z ^ k‖) :
    Summable fun n => ‖((PowerSeries.coeff n (A * B) : ℚ) : ℂ) * z ^ n‖ :=
  (summable_norm_sum_mul_antidiagonal_of_summable_norm hA hB).congr
    fun n => congrArg norm (antidiag_term A B z n)

/-- Summability is preserved by adding two power series. -/
lemma summable_coeff_add (A B : PowerSeries ℚ) (z : ℂ)
    (hA : Summable fun k => ((PowerSeries.coeff k A : ℚ) : ℂ) * z ^ k)
    (hB : Summable fun k => ((PowerSeries.coeff k B : ℚ) : ℂ) * z ^ k) :
    Summable fun k => ((PowerSeries.coeff k (A + B) : ℚ) : ℂ) * z ^ k := by
  refine (hA.add hB).congr fun k => ?_
  simp only [map_add]
  push_cast
  ring

/-! ## The main theorem -/

theorem Pfun_solves_M (a b : ℚ) (ra rb rab r0 : ℤ)
    (hconv : ∀ z : ℂ, ‖z‖ < Work.C17.xs a b →
      HasSum (fun n : ℕ => ((PowerSeries.coeff n (Submission.CDT.logP a b ra rb rab r0) : ℚ) : ℂ) * z ^ n)
        (Work.C17.Pfun a b ra rb rab r0 z)) :
    ∀ z : ℂ, ‖z‖ < Work.C17.xs a b →
      (Work.C17.P2x a b).eval₂ (algebraMap ℚ ℂ) z * deriv (deriv (Work.C17.Pfun a b ra rb rab r0)) z
        + (Work.C17.P1x a b).eval₂ (algebraMap ℚ ℂ) z * deriv (Work.C17.Pfun a b ra rb rab r0) z
        + (Work.C17.P0x a b).eval₂ (algebraMap ℚ ℂ) z * Work.C17.Pfun a b ra rb rab r0 z
      = (Work.C17.rhoMx a b ra rb rab).eval₂ (algebraMap ℚ ℂ) z := by
  intro z hz
  set f : PowerSeries ℚ := Submission.CDT.logP a b ra rb rab r0 with hf
  set F : ℂ → ℂ := Work.C17.Pfun a b ra rb rab r0 with hF
  set c : ℕ → ℂ := fun n => ((PowerSeries.coeff n f : ℚ) : ℂ) with hc
  set r : ℝ := Work.C17.xs a b with hr
  have hconv' : ∀ w : ℂ, ‖w‖ < r → HasSum (fun n : ℕ => c n * w ^ n) (F w) := hconv
  -- derivative transfer
  have hA1 := Work.C17f.deriv_hasSum_powSeries c r F hconv'
  have hA2 : ∀ w : ℂ, ‖w‖ < r →
      HasSum (fun n : ℕ => (((n : ℂ) + 1) * c (n + 1)) * w ^ n) (deriv F w) :=
    fun w hw => (hA1 w hw).congr fun n => by ring
  have hA3 := Work.C17f.deriv_hasSum_powSeries (fun n : ℕ => ((n : ℂ) + 1) * c (n + 1)) r
    (deriv F) hA2
  have hd : Work.CLift.evA (PowerSeries.derivative (R := ℚ) f) z = deriv F z := by
    rw [Work.CLift.evA, ← (hA1 z hz).tsum_eq]
    refine tsum_congr fun n => ?_
    rw [PowerSeries.coeff_derivative]
    simp only [hc]
    push_cast
    ring
  have hdd : Work.CLift.evA (PowerSeries.derivative (R := ℚ) (PowerSeries.derivative (R := ℚ) f)) z
      = deriv (deriv F) z := by
    rw [Work.CLift.evA, ← (hA3 z hz).tsum_eq]
    refine tsum_congr fun n => ?_
    rw [PowerSeries.coeff_derivative, PowerSeries.coeff_derivative]
    simp only [hc]
    push_cast
    ring
  have hfz : Work.CLift.evA f z = F z := by
    rw [Work.CLift.evA]
    exact (hconv' z hz).tsum_eq.symm
  -- absolute summability of the coefficient series and its derived series
  have habs := Work.C17f.abs_summable_powSeries c r F hconv' z hz
  have h0n : Summable fun k : ℕ => ‖((PowerSeries.coeff k f : ℚ) : ℂ) * z ^ k‖ := by
    simpa only [hc] using habs.1
  have h1n : Summable fun k : ℕ =>
      ‖((PowerSeries.coeff k (PowerSeries.derivative (R := ℚ) f) : ℚ) : ℂ) * z ^ k‖ := by
    refine habs.2.1.congr fun k => ?_
    rw [PowerSeries.coeff_derivative]
    simp only [hc]
    push_cast
    ring
  have h2n : Summable fun k : ℕ =>
      ‖((PowerSeries.coeff k (PowerSeries.derivative (R := ℚ) (PowerSeries.derivative (R := ℚ) f)) : ℚ) : ℂ)
        * z ^ k‖ := by
    refine habs.2.2.congr fun k => ?_
    rw [PowerSeries.coeff_derivative, PowerSeries.coeff_derivative]
    simp only [hc]
    push_cast
    ring
  have hP2n : Summable fun k : ℕ =>
      ‖((PowerSeries.coeff k (Submission.CDT.logPAP2 a b) : ℚ) : ℂ) * z ^ k‖ := by
    rw [← Work.C17.coe_P2x a b]
    exact summable_norm_coe_poly (Work.C17.P2x a b) z
  have hP1n : Summable fun k : ℕ =>
      ‖((PowerSeries.coeff k (Submission.CDT.logPAP1 a b) : ℚ) : ℂ) * z ^ k‖ := by
    rw [← Work.C17.coe_P1x a b]
    exact summable_norm_coe_poly (Work.C17.P1x a b) z
  have hP0n : Summable fun k : ℕ =>
      ‖((PowerSeries.coeff k (Submission.CDT.logPAP0 a b) : ℚ) : ℂ) * z ^ k‖ := by
    rw [← Work.C17.coe_P0x a b]
    exact summable_norm_coe_poly (Work.C17.P0x a b) z
  -- the three products
  have hA0 : Summable fun n : ℕ =>
      ((PowerSeries.coeff n (Submission.CDT.logPAP2 a b
        * PowerSeries.derivative (R := ℚ) (PowerSeries.derivative (R := ℚ) f)) : ℚ) : ℂ) * z ^ n :=
    (summable_norm_coeff_mul _ _ z hP2n h2n).of_norm
  have hB0 : Summable fun n : ℕ =>
      ((PowerSeries.coeff n (Submission.CDT.logPAP1 a b
        * PowerSeries.derivative (R := ℚ) f) : ℚ) : ℂ) * z ^ n :=
    (summable_norm_coeff_mul _ _ z hP1n h1n).of_norm
  have hC0 : Summable fun n : ℕ =>
      ((PowerSeries.coeff n (Submission.CDT.logPAP0 a b * f) : ℚ) : ℂ) * z ^ n :=
    (summable_norm_coeff_mul _ _ z hP0n h0n).of_norm
  have hAB : Summable fun n : ℕ =>
      ((PowerSeries.coeff n (Submission.CDT.logPAP2 a b
          * PowerSeries.derivative (R := ℚ) (PowerSeries.derivative (R := ℚ) f)
        + Submission.CDT.logPAP1 a b * PowerSeries.derivative (R := ℚ) f) : ℚ) : ℂ) * z ^ n :=
    summable_coeff_add _ _ z hA0 hB0
  have hE2 : Work.CLift.evA (Submission.CDT.logPAP2 a b
        * PowerSeries.derivative (R := ℚ) (PowerSeries.derivative (R := ℚ) f)) z
      = (Work.C17.P2x a b).eval₂ (algebraMap ℚ ℂ) z * deriv (deriv F) z := by
    rw [Work.CLift.evA_mul _ _ _ hP2n h2n, ← Work.C17.coe_P2x a b, Work.CLift.evA_coe_poly, hdd]
  have hE1 : Work.CLift.evA (Submission.CDT.logPAP1 a b * PowerSeries.derivative (R := ℚ) f) z
      = (Work.C17.P1x a b).eval₂ (algebraMap ℚ ℂ) z * deriv F z := by
    rw [Work.CLift.evA_mul _ _ _ hP1n h1n, ← Work.C17.coe_P1x a b, Work.CLift.evA_coe_poly, hd]
  have hE0 : Work.CLift.evA (Submission.CDT.logPAP0 a b * f) z
      = (Work.C17.P0x a b).eval₂ (algebraMap ℚ ℂ) z * F z := by
    rw [Work.CLift.evA_mul _ _ _ hP0n h0n, ← Work.C17.coe_P0x a b, Work.CLift.evA_coe_poly, hfz]
  have hode : Submission.CDT.logPAODE a b f
      = PowerSeries.C (ra : ℚ) * Submission.CDT.RaFam a b
        + PowerSeries.C (rb : ℚ) * Submission.CDT.RbFam a b
        + PowerSeries.C (rab : ℚ) * Submission.CDT.RabFam a b :=
    Submission.CDT.logP_ode a b ra rb rab r0
  have hLHS : Work.CLift.evA (Submission.CDT.logPAODE a b f) z
      = (Work.C17.P2x a b).eval₂ (algebraMap ℚ ℂ) z * deriv (deriv F) z
        + (Work.C17.P1x a b).eval₂ (algebraMap ℚ ℂ) z * deriv F z
        + (Work.C17.P0x a b).eval₂ (algebraMap ℚ ℂ) z * F z := by
    rw [Work.C17.logPAODE_eq a b f, Work.C17.coe_P2x a b, Work.C17.coe_P1x a b,
      Work.C17.coe_P0x a b]
    rw [Work.CLift.evA_add _ _ _ hAB hC0, Work.CLift.evA_add _ _ _ hA0 hB0, hE2, hE1, hE0]
  calc (Work.C17.P2x a b).eval₂ (algebraMap ℚ ℂ) z * deriv (deriv F) z
        + (Work.C17.P1x a b).eval₂ (algebraMap ℚ ℂ) z * deriv F z
        + (Work.C17.P0x a b).eval₂ (algebraMap ℚ ℂ) z * F z
      = Work.CLift.evA (Submission.CDT.logPAODE a b f) z := hLHS.symm
    _ = Work.CLift.evA (PowerSeries.C (ra : ℚ) * Submission.CDT.RaFam a b
          + PowerSeries.C (rb : ℚ) * Submission.CDT.RbFam a b
          + PowerSeries.C (rab : ℚ) * Submission.CDT.RabFam a b) z := by rw [hode]
    _ = (Work.C17.rhoMx a b ra rb rab).eval₂ (algebraMap ℚ ℂ) z := evA_rhoMx a b ra rb rab z

end

end Work.C17f
