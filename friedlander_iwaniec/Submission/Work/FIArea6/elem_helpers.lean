/-
# `Submission.Work.FIArea6.elem_helpers` — elementwise lemmas for the Area-6 estimate

These are the *elementary* (no analysis) facts about the frozen vocabulary that the elementary
bound for `UcutMod` uses; see `NOTES.md` §3 of this directory.

* `abs_jacobiSym_le_one`;
* `beta_norm_le_divisors` — on its support, `IsBetaCoeff` gives `‖β z‖ ≤ τ(|z|²)`
  (via the already-proved `Defs3.abs_gammaTrunc_le`);
* `beta_support` — the support of `β` is contained in the polar box with `τ(|z|²) ≤ Pa.τ`.
-/
import Mathlib
import Submission.Work.FITop3.Defs3
import Submission.Work.FITop3.Smooth
import Submission.Work.FITop3.Smooth.sm_props
import Submission.Work.FITop3.Majorant.majorant_props
import Submission.Work.FITop3.Witness.exists_primary_norm

set_option autoImplicit false

namespace Work.FIArea6

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-- `|jacobiSym a b| ≤ 1` (the symbol takes the values `0, ±1`). -/
lemma abs_jacobiSym_le_one (a : ℤ) (b : ℕ) : |jacobiSym a b| ≤ 1 := by
  rcases jacobiSym.trichotomy a b with h | h | h <;> simp [h]

/-- **On the support of an `IsBetaCoeff` coefficient, `‖β z‖ ≤ τ(|z|²)`.**
This is the elementary size bound (4.13): `β z = q(arg z − φ)p(|z|²)μ(|z|²)γ(|z|²;C)` with
`0 ≤ q, p ≤ 1` and `|γ(n;C)| ≤ τ(n)` (`Defs3.abs_gammaTrunc_le`). -/
lemma beta_norm_le_divisors {Pa : Work.FITop.Params} {φ : ℝ} {β : GaussianInt → ℂ}
    (hβ : Work.FITop3.IsBetaCoeff Pa φ β) (z : GaussianInt) :
    ‖β z‖ ≤ (((Work.FIPlan.gnorm z).divisors.card : ℕ) : ℝ) := by
  obtain ⟨q, p, hq0, hq1, -, -, -, hp0, hp1, -, -, -, hform⟩ := hβ
  rw [hform z]
  split_ifs with hz
  · have hqp : ‖(((q (Complex.arg z.toComplex - φ) * p (Work.FIPlan.gnorm z) : ℝ)) : ℂ)‖ ≤ 1 := by
      rw [Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (mul_nonneg (hq0 _) (hp0 _))]
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
      _ ≤ 1 * 1 * ((Work.FIPlan.gnorm z).divisors.card : ℝ) := by
          gcongr
      _ = ((Work.FIPlan.gnorm z).divisors.card : ℝ) := by ring
  · simp

/-- **The support of `β`.**  If `β z ≠ 0` then `z` lies in the polar box (5.14) — in particular
`Pa.N < |z|² ≤ (1+Pa.θ) * Pa.N` — it is free of the primes `≤ Pa.Pz` (5.8), and
`τ(|z|²) ≤ Pa.τ` (5.9). -/
lemma beta_support {Pa : Work.FITop.Params} {φ : ℝ} {β : GaussianInt → ℂ}
    (hβ : Work.FITop3.IsBetaCoeff Pa φ β) {z : GaussianInt} (hz : β z ≠ 0) :
    Work.FITop3.InPolarBox Pa φ z ∧ Work.FITop3.NoSmallPrimes Pa z
      ∧ (((Work.FIPlan.gnorm z).divisors.card : ℕ) : ℝ) ≤ Pa.τ := by
  obtain ⟨q, p, -, -, -, -, -, -, -, -, -, -, hform⟩ := hβ
  rw [hform z] at hz
  by_contra hc
  rw [if_neg hc] at hz
  exact hz rfl

/-- The support is annulus-confined: if `β z ≠ 0` then `Pa.N < |z|²` and `|z|² ≤ (1+Pa.θ) * Pa.N`,
so in particular `|z|² ≤ 2 * Pa.N`. -/
lemma beta_support_norm {Pa : Work.FITop.Params} {φ : ℝ} {β : GaussianInt → ℂ}
    (hβ : Work.FITop3.IsBetaCoeff Pa φ β) {z : GaussianInt} (hz : β z ≠ 0) :
    Pa.N < ((Work.FIPlan.gnorm z : ℕ) : ℝ) ∧
      ((Work.FIPlan.gnorm z : ℕ) : ℝ) ≤ (1 + Pa.θ) * Pa.N := by
  have h := (beta_support hβ hz).1
  exact ⟨h.2.1, h.2.2.1⟩

end

end Work.FIArea6
