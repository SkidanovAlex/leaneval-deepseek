import Mathlib
import Submission.Work.FITop3.Defs3
import Submission.Work.FITop3.Smooth
import Submission.Work.FITop3.Smooth.sm_props
import Submission.Work.FITop3.Majorant.majorant_props
import Submission.Work.FITop3.Witness.exists_primary_norm

/-!
# FI §15: the primitive coefficient predicate `IsPrimBoxCoeff`

The frozen round-3 hypothesis `Work.FITop3.IsBoxCoeff` requires only
`‖β z‖ ≤ τ(|z|²)`, support in the polar box (5.14) and `(z,Π) = 1`.  It admits
coefficients supported on **non-primitive** Gaussian integers (`z = 3+6i` is primary with
`(r,s) = 3`), whereas *FI* §15 uses primitivity essentially:

* (15.2) "Since `(r₁,s₁) = 1` we always have one or both cases" — the dichotomy
  `z₂/z₁ ≡ r₂/r₁` if `p ∤ r₁`, `z₂/z₁ ≡ s₂/s₁` if `p ∤ s₁` needs `p ∤ r₁` or `p ∤ s₁`;
* the `e`-decomposition `(d,r₁) = (d,r₂) = e` of (15.2) needs `(r₁,s₁) = 1` to conclude
  `p | r₁ ∧ p | d ⟹ p | r₂`;
* every sharp variance estimate available here (FI Props 12.1, 13.1, 14.1 —
  `Work.FIArea4.p12_all`, `p14_all`) carries FI's (11.6) hypothesis `(r, 2s) = 1` on the
  support of the array.

For a *primary* `z`, `r = Re z` is odd; and `|z|²` squarefree forces `(r,s) = 1`.  Together these
give `(r, 2s) = 1`, FI (11.6).  The predicate below is therefore the correct hypothesis for the
§15 chain.  (This is exactly the primitivity of `IsBetaCoeff`/round-6's `IsBetaCoeff6`, which has
the factor `μ(|z|²)`.)
-/

namespace Work.FIArea4

open scoped BigOperators

noncomputable section

/-- **FI (11.6) for the frozen coefficient predicate**: `β` is a box coefficient (5.14) whose
support is primitive, `(Re z, 2 Im z) = 1`. -/
def IsPrimBoxCoeff (Pa : Work.FITop.Params) (φ : ℝ) (β : GaussianInt → ℂ) : Prop :=
  Work.FITop3.IsBoxCoeff Pa φ β ∧
    ∀ z : GaussianInt, β z ≠ 0 → Nat.Coprime z.re.natAbs (2 * z.im.natAbs)

/-- `IsPrimBoxCoeff` implies `IsBoxCoeff`. -/
lemma IsPrimBoxCoeff.toBoxCoeff {Pa : Work.FITop.Params} {φ : ℝ} {β : GaussianInt → ℂ}
    (h : IsPrimBoxCoeff Pa φ β) : Work.FITop3.IsBoxCoeff Pa φ β := h.1

/-- The support of an `IsPrimBoxCoeff` family satisfies `(Re, 2 Im) = 1`. -/
lemma IsPrimBoxCoeff.coprime {Pa : Work.FITop.Params} {φ : ℝ} {β : GaussianInt → ℂ}
    (h : IsPrimBoxCoeff Pa φ β) {z : GaussianInt} (hz : β z ≠ 0) :
    Nat.Coprime z.re.natAbs (2 * z.im.natAbs) := h.2 z hz

/-- An `IsPrimBoxCoeff` family is supported in the polar box. -/
lemma IsPrimBoxCoeff.inPolarBox {Pa : Work.FITop.Params} {φ : ℝ} {β : GaussianInt → ℂ}
    (h : IsPrimBoxCoeff Pa φ β) {z : GaussianInt} (hz : β z ≠ 0) :
    Work.FITop3.InPolarBox Pa φ z := ((h.1.2 z hz)).1

/-- `gnorm z = (Re z)² + (Im z)²` in `ℕ`. -/
lemma gnorm_eq_re_sq_add_im_sq (z : GaussianInt) :
    Work.FIPlan.gnorm z = z.re.natAbs ^ 2 + z.im.natAbs ^ 2 := by
  have h1 : z.re * z.re = ((z.re.natAbs ^ 2 : ℕ) : ℤ) := by
    rw [← Int.natAbs_mul_self (a := z.re)]; push_cast; ring
  have h2 : z.im * z.im = ((z.im.natAbs ^ 2 : ℕ) : ℤ) := by
    rw [← Int.natAbs_mul_self (a := z.im)]; push_cast; ring
  rw [Work.FIPlan.gnorm, Zsqrtd.norm_def]
  have h3 : z.re * z.re - -1 * z.im * z.im
      = ((z.re.natAbs ^ 2 + z.im.natAbs ^ 2 : ℕ) : ℤ) := by
    rw [show z.re * z.re - -1 * z.im * z.im = z.re * z.re + z.im * z.im by ring]
    rw [h1, h2]; push_cast; ring
  rw [h3, Int.natAbs_natCast]

/-- **`IsBetaCoeff` implies primitivity.**  If `β z ≠ 0` then (5.13) forces `(z,Π) = 1`, the
polar box (hence `IsPrimary`, hence `Re z` odd) and `μ(|z|²) ≠ 0` (hence `|z|²` squarefree, hence
`(Re z, Im z) = 1`); together `(Re z, 2 Im z) = 1`, FI (11.6). -/
theorem IsBetaCoeff.primitive {Pa : Work.FITop.Params} {φ : ℝ} {β : GaussianInt → ℂ}
    (hb : Work.FITop3.IsBetaCoeff Pa φ β) :
    ∀ z : GaussianInt, β z ≠ 0 → Nat.Coprime z.re.natAbs (2 * z.im.natAbs) := by
  intro z hz
  obtain ⟨q, p, hq0, hq1, hqsupp, -, -, hp0, hp1, hpsupp, -, -, hβ⟩ := hb
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

end

end Work.FIArea4
