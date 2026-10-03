import Mathlib
import Submission.Work.FIArea4.S15prim_defs
import Submission.Work.FITop4.Defs6

set_option autoImplicit false

namespace Work.FIArea4

open scoped BigOperators

attribute [local instance] Classical.propDecidable

/-- **Primitivity of a round-4/round-6 coefficient.**  The round-4 predicate
`Work.FITop4.IsBetaCoeff` (used by the corrected kernel of round 6) strengthens
`Work.FITop3.IsBetaCoeff` only in the *smoothness* clauses of the mollifiers, and the proof of
`Work.FIArea4.IsBetaCoeff.primitive` uses exactly one thing about the coefficient: the *shape* of
its support, `β z ≠ 0 → InPolarBox … ∧ NoSmallPrimes … ∧ (τ-bound)`, with
`β z = q(arg z − φ)·p(|z|²)·μ(|z|²)·γ(|z|²;C)` there.  Both predicates share that shape, so the
same argument applies verbatim: the polar box makes `Re z` odd (primary) and the Möbius factor
makes `|z|²` squarefree, whence `(Re z, 2 Im z) = 1`. -/
theorem IsBetaCoeff4.primitive {Pa : Work.FITop.Params} {φ : ℝ} {β : GaussianInt → ℂ}
    (hb : Work.FITop4.IsBetaCoeff Pa φ β) :
    ∀ z : GaussianInt, β z ≠ 0 → Nat.Coprime z.re.natAbs (2 * z.im.natAbs) := by
  intro z hz
  obtain ⟨q, p, -, -, -, -, -, -, -, -, -, -, hβ⟩ := hb
  rw [hβ z] at hz
  split_ifs at hz with hcond
  · have hmu : ArithmeticFunction.moebius (Work.FIPlan.gnorm z) ≠ 0 := by
      have h1 : ((q (Complex.arg z.toComplex - φ) * p (Work.FIPlan.gnorm z) : ℝ) : ℂ) *
          (ArithmeticFunction.moebius (Work.FIPlan.gnorm z) : ℂ) *
          (Work.FIPlan.gammaTrunc Pa.C (Work.FIPlan.gnorm z) : ℂ) ≠ 0 := hz
      exact Int.cast_ne_zero.mp (mul_ne_zero_iff.mp (mul_ne_zero_iff.mp h1).1).2
    have hsq : Squarefree (Work.FIPlan.gnorm z) :=
      ArithmeticFunction.moebius_ne_zero_iff_squarefree.mp hmu
    have hprimary : Odd z.re := hcond.1.1.1
    have hcop2 : Nat.Coprime z.re.natAbs 2 :=
      Nat.coprime_two_right.mpr (Int.natAbs_odd.mpr hprimary)
    have hcops : Nat.Coprime z.re.natAbs z.im.natAbs := by
      rw [Nat.coprime_iff_gcd_eq_one]
      by_contra hne1
      obtain ⟨pp, hpp, hpd⟩ := Nat.exists_prime_and_dvd hne1
      have hpr : pp ∣ z.re.natAbs := dvd_trans hpd (Nat.gcd_dvd_left _ _)
      have hps : pp ∣ z.im.natAbs := dvd_trans hpd (Nat.gcd_dvd_right _ _)
      have hpp2 : pp * pp ∣ Work.FIPlan.gnorm z := by
        rw [gnorm_eq_re_sq_add_im_sq, ← pow_two pp]
        exact Nat.dvd_add (pow_dvd_pow_of_dvd hpr 2) (pow_dvd_pow_of_dvd hps 2)
      exact (Nat.squarefree_iff_prime_squarefree.mp hsq pp hpp) hpp2
    exact hcop2.mul_right hcops
  · exact absurd rfl hz

/-- **A round-6 coefficient is a primitive box coefficient.**

`Work.FITop4.IsBetaCoeff6` is the round-4 coefficient `Work.FITop4.IsBetaCoeff` restricted to one
class modulo eight (5.7) and to the axis-free region of §5; `exists_toBetaCoeff` exhibits that
round-4 array `β'`, of which `β` is the restriction:
`β z = if SameClass8 z z0 ∧ IsAxisFree Pa z then β' z else 0`.  Both required components of
`IsPrimBoxCoeff` transfer from `β'`:

* the box predicate `Work.FITop3.IsBoxCoeff` (norm bound `‖β z‖ ≤ τ(|z|²)`, support in the polar
  box with `(z, Π) = 1`) follows from `β'`'s by `Work.FITop4.IsBetaCoeff.toBoxCoeff` — restricting
  the support only shrinks it;
* primitivity `(Re z, 2 Im z) = 1` is `IsBetaCoeff4.primitive` applied to `β'`. -/
theorem prim_of_beta6 {Pa : Work.FITop.Params} {φ : ℝ} {z0 : GaussianInt} {β : GaussianInt → ℂ}
    (h : Work.FITop4.IsBetaCoeff6 Pa φ z0 β) : Work.FIArea4.IsPrimBoxCoeff Pa φ β := by
  obtain ⟨β', hβ', hEq⟩ := Work.FITop4.IsBetaCoeff6.exists_toBetaCoeff h
  have hbox : Work.FITop3.IsBoxCoeff Pa φ β' := Work.FITop4.IsBetaCoeff.toBoxCoeff hβ'
  have hprim := IsBetaCoeff4.primitive hβ'
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro z
    rw [hEq z]
    split_ifs with hc
    · exact hbox.1 z
    · simp
  · intro z hz
    rw [hEq z] at hz
    split_ifs at hz with hc
    · exact hbox.2 z hz
    · exact absurd rfl hz
  · intro z hz
    rw [hEq z] at hz
    split_ifs at hz with hc
    · exact hprim z hz
    · exact absurd rfl hz

end Work.FIArea4
