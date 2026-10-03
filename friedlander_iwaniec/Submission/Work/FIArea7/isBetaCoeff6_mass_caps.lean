/-
# `Work.FIArea7.isBetaCoeff6_mass_caps` — the two mass caps of the round-6 coefficient

The coefficient class of (4.13)+(5.13)+(5.7) is *structural*: a non-zero value of `β` can only
occur in the polar box (5.14), free of small primes (5.8), with `τ(|z|²) ≤ Pa.τ` (5.9) and
`|z|²` squarefree, and its size is dominated by `τ(|z|²)`
(`IsBetaCoeff6.support`, `IsBetaCoeff6.noSmallPrimes`, `IsBetaCoeff6.squarefree_gnorm`, and the
explicit formula).  That is the predicate `Work.FIArea7.IsPolarCoeff`
(`Submission/Work/FIArea7/PolarCoeff6.lean`, a copy of area 6's structural class, whose original
module is stale with respect to the `IsAxisFree` clause of `IsBetaCoeff6` and no longer compiles).

For that class area 6 already contains the two elementary estimates

* `IsPolarCoeff.card_support_le`: the support count `#supp β ≤ 200(θ²N + θ√N + 1)`;
* `Work.FIArea7.vsq_polar6`: the `L²`-mass `Σ_z‖β z‖² ≤ 1000(θN + √N + 1)(log(N+2))³`.

This file records `IsBetaCoeff6 → IsPolarCoeff` and glues the two together; the result is the
per-coefficient bundle an area-7 assembly consumes.
-/
import Mathlib
import Submission.Work.FITop4.Areas6
import Submission.Work.FIArea7.Area7Char6
import Submission.Work.FIArea7.PolarCoeff6
import Submission.Work.FIArea7.vsq_polar6

set_option autoImplicit false

namespace Work.FIArea7

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-- **A round-6 coefficient is structural.**  The explicit formula of (4.13)+(5.13)+(5.7) gives
every clause of `IsPolarCoeff`: support in the polar box (5.14), freedom of small primes (5.8),
the `τ`-bound (5.9), squarefreeness of `|z|²` (the Möbius factor), and `‖β z‖ ≤ τ(|z|²)`. -/
theorem isBetaCoeff6_toIsPolarCoeff {Pa : Work.FITop.Params} {φ : ℝ} {z0 : GaussianInt}
    {β : GaussianInt → ℂ} (h : Work.FITop4.IsBetaCoeff6 Pa φ z0 β) :
    IsPolarCoeff Pa φ β := by
  obtain ⟨q, p, -, -, hq0, hq1, -, -, hp0, hp1, -, -, hform⟩ := h
  constructor
  · intro z hz
    rw [hform z] at hz
    by_cases hc : Work.FITop4.InPolarBox Pa φ z ∧ Work.FITop4.NoSmallPrimes Pa z ∧
        (((Work.FIPlan.gnorm z).divisors.card : ℝ) ≤ Pa.τ) ∧ Work.FITop4.SameClass8 z z0
        ∧ Work.FITop4.IsAxisFree Pa z
    · rw [if_pos hc] at hz
      have hmu : (ArithmeticFunction.moebius (Work.FIPlan.gnorm z) : ℂ) ≠ 0 :=
        (mul_ne_zero_iff.mp (mul_ne_zero_iff.mp hz).1).2
      have hmuZ : ArithmeticFunction.moebius (Work.FIPlan.gnorm z) ≠ 0 := by
        intro h0
        exact hmu (by rw [h0]; norm_num)
      exact ⟨hc.1, hc.2.1, hc.2.2.1,
        ArithmeticFunction.moebius_ne_zero_iff_squarefree.mp hmuZ⟩
    · rw [if_neg hc] at hz
      exact absurd rfl hz
  · intro z
    rw [hform z]
    split_ifs with hz
    · have hqp : ‖(((q (Complex.arg z.toComplex - φ) * p (Work.FIPlan.gnorm z) : ℝ)) : ℂ)‖ ≤ 1 := by
        rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hq0 _) (hp0 _))]
        have h2 : q (Complex.arg z.toComplex - φ) * p (Work.FIPlan.gnorm z) ≤ 1 * 1 :=
          mul_le_mul (hq1 _) (hp1 _) (hp0 _) (by norm_num)
        linarith
      have hμ : ‖(ArithmeticFunction.moebius (Work.FIPlan.gnorm z) : ℂ)‖ ≤ 1 :=
        Work.FITop3.norm_moebius_le_one _
      have hγ : ‖((Work.FIPlan.gammaTrunc Pa.C (Work.FIPlan.gnorm z) : ℝ) : ℂ)‖
          ≤ ((Work.FIPlan.gnorm z).divisors.card : ℝ) := by
        rw [Complex.norm_real, Real.norm_eq_abs]
        exact Work.FITop3.abs_gammaTrunc_le _ _
      calc ‖(((q (Complex.arg z.toComplex - φ) * p (Work.FIPlan.gnorm z) : ℝ)) : ℂ)
              * (ArithmeticFunction.moebius (Work.FIPlan.gnorm z) : ℂ)
              * ((Work.FIPlan.gammaTrunc Pa.C (Work.FIPlan.gnorm z) : ℝ) : ℂ)‖
          = ‖(((q (Complex.arg z.toComplex - φ) * p (Work.FIPlan.gnorm z) : ℝ)) : ℂ)‖
              * ‖(ArithmeticFunction.moebius (Work.FIPlan.gnorm z) : ℂ)‖
              * ‖((Work.FIPlan.gammaTrunc Pa.C (Work.FIPlan.gnorm z) : ℝ) : ℂ)‖ := by
            rw [norm_mul, norm_mul]
        _ ≤ 1 * 1 * ((Work.FIPlan.gnorm z).divisors.card : ℝ) := by gcongr
        _ = ((Work.FIPlan.gnorm z).divisors.card : ℝ) := by ring
    · simp

theorem isBetaCoeff6_mass_caps :
    ∀ {Pa : Work.FITop.Params} {φ : ℝ} {z0 : GaussianInt} {β : GaussianInt → ℂ},
      Work.FITop4.IsBetaCoeff6 Pa φ z0 β →
      (((Work.FIPlan.gBox (Work.FITop.radN Pa)).filter (fun z => β z ≠ 0)).card : ℝ)
          ≤ 200 * (Pa.θ ^ 2 * Pa.N + Pa.θ * Real.sqrt Pa.N + 1) ∧
      (∑ z ∈ Work.FIPlan.gBox (Work.FITop.radN Pa), ‖β z‖ ^ 2)
          ≤ 1000 * (Pa.θ * Pa.N + Real.sqrt Pa.N + 1) * (Real.log (2 + Pa.N)) ^ 3 := by
  intro Pa φ z0 β hβ
  have hp : IsPolarCoeff Pa φ β := isBetaCoeff6_toIsPolarCoeff hβ
  exact ⟨by simpa only [Work.FITop.boxN] using IsPolarCoeff.card_support_le Pa φ β hp,
    by simpa only [Work.FITop.boxN] using vsq_polar6 Pa φ β hp⟩

end

end Work.FIArea7
