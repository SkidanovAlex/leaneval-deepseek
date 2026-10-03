/-
# Round-6 §15, self-contained: the diagonal (`Δ = 0`) bound `diagSum6_le`

A self-contained copy of the diagonal layer of FI §15 for the round-6 coefficient `S15coef6`
(the *ratio* symbol `(z₂/z₁|d)`), depending only on `A6psi.Dng6Defs` (and hence not on the
frozen `S15red.DiagAux`, which pulls in the §15 variance-half module).

On the support of an `IsPrimBoxCoeff` the pairs with `Δ(z₁,z₂) = 0` collapse to the diagonal
`z₂ = z₁`, each contributing at most `2‖β z‖²`.
-/
import Mathlib
import Submission.Work.FIArea4.A6psi.Dng6Defs

namespace Work.FIArea4.A6psi
namespace Diag6

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-! ## 1. `Δ` in coordinates, and the rigidity of `Δ = 0` on a primitive box -/

lemma Delta_eq_re_mul_im_sub (z1 z2 : GaussianInt) :
    Work.FIPlan.Delta z1 z2 = z1.re * z2.im - z2.re * z1.im := by
  unfold Work.FIPlan.Delta
  rw [Zsqrtd.im_mul, Zsqrtd.re_star, Zsqrtd.im_star]
  ring

lemma Delta_eq_zero_iff (z1 z2 : GaussianInt) :
    Work.FIPlan.Delta z1 z2 = 0 ↔ z1.re * z2.im = z2.re * z1.im := by
  rw [Delta_eq_re_mul_im_sub]
  constructor <;> intro h <;> linarith

lemma Delta_eq_zero_of_absDelta_eq_zero {z1 z2 : GaussianInt}
    (h : Work.FIPlan.absDelta z1 z2 = 0) : Work.FIPlan.Delta z1 z2 = 0 := by
  unfold Work.FIPlan.absDelta at h
  exact Int.natAbs_eq_zero.mp h

lemma coprime_re_im_of_coprime_two {z : GaussianInt}
    (h : Nat.Coprime z.re.natAbs (2 * z.im.natAbs)) :
    Nat.Coprime z.re.natAbs z.im.natAbs :=
  h.coprime_dvd_right (dvd_mul_left z.im.natAbs 2)

lemma exists_int_multiple_of_coprime_mul_eq {a b c d : ℤ} (hcop : Nat.Coprime a.natAbs b.natAbs)
    (h : a * d = c * b) : ∃ k : ℤ, c = k * a ∧ d = k * b := by
  obtain ⟨u, v, huv⟩ : IsCoprime a b := Int.isCoprime_iff_nat_coprime.mpr hcop
  refine ⟨u * c + v * d, ?_, ?_⟩
  · calc c = c * 1 := (mul_one c).symm
      _ = c * (u * a + v * b) := by rw [huv]
      _ = u * a * c + v * (c * b) := by ring
      _ = u * a * c + v * (a * d) := by rw [← h]
      _ = (u * c + v * d) * a := by ring
  · calc d = d * 1 := (mul_one d).symm
      _ = d * (u * a + v * b) := by rw [huv]
      _ = u * (a * d) + v * b * d := by ring
      _ = u * (c * b) + v * b * d := by rw [h]
      _ = (u * c + v * d) * b := by ring

lemma Delta_eq_zero_or_neg {z1 z2 : GaussianInt}
    (h1 : Nat.Coprime z1.re.natAbs (2 * z1.im.natAbs))
    (h2 : Nat.Coprime z2.re.natAbs (2 * z2.im.natAbs))
    (hd : Work.FIPlan.Delta z1 z2 = 0) : z2 = z1 ∨ z2 = -z1 := by
  have hΔ : z1.re * z2.im = z2.re * z1.im := Delta_eq_zero_iff z1 z2 |>.mp hd
  obtain ⟨k, hk1, hk2⟩ :=
    exists_int_multiple_of_coprime_mul_eq (coprime_re_im_of_coprime_two h1) hΔ
  have hgcd1 : Nat.gcd z1.re.natAbs z1.im.natAbs = 1 :=
    Nat.coprime_iff_gcd_eq_one.mp (coprime_re_im_of_coprime_two h1)
  have hgcd2 : Nat.gcd z2.re.natAbs z2.im.natAbs = 1 :=
    Nat.coprime_iff_gcd_eq_one.mp (coprime_re_im_of_coprime_two h2)
  have hkn : k.natAbs = 1 := by
    have hg : Nat.gcd (k * z1.re).natAbs (k * z1.im).natAbs
        = k.natAbs * Nat.gcd z1.re.natAbs z1.im.natAbs := by
      rw [Int.natAbs_mul, Int.natAbs_mul, Nat.gcd_mul_left]
    rw [hk1, hk2, hg, hgcd1, mul_one] at hgcd2
    exact hgcd2
  have hk' : k = 1 ∨ k = -1 := by
    have hmul : k * k = 1 := by
      have h1' : k.natAbs = (1 : ℤ).natAbs := by simpa using hkn
      have := Int.natAbs_eq_iff_mul_self_eq.mp h1'
      simpa using this
    have hsq : k ^ 2 = 1 := by rw [pow_two]; exact hmul
    exact sq_eq_one_iff.mp hsq
  rcases hk' with hk' | hk'
  · left
    exact Zsqrtd.ext (by rw [hk1, hk', one_mul]) (by rw [hk2, hk', one_mul])
  · right
    refine Zsqrtd.ext ?_ ?_
    · rw [hk1, hk', Zsqrtd.re_neg]; ring
    · rw [hk2, hk', Zsqrtd.im_neg]; ring

lemma not_isPrimary_neg {z : GaussianInt} (h : Work.FIPlan.IsPrimary z) :
    ¬ Work.FIPlan.IsPrimary (-z) := by
  intro h'
  have h1 : z.im ≡ z.re - 1 [ZMOD 4] := h.2.2
  have h2 : -z.im ≡ -z.re - 1 [ZMOD 4] := by simpa using h'.2.2
  have h3 : z.im ≡ z.re + 1 [ZMOD 4] := by
    have hneg := Int.ModEq.neg h2
    have e1 : -(-z.im) = z.im := by ring
    have e2 : -(-z.re - 1) = z.re + 1 := by ring
    rwa [e1, e2] at hneg
  have h4 : z.re - 1 ≡ z.re + 1 [ZMOD 4] := h1.symm.trans h3
  have h5 : (4 : ℤ) ∣ (z.re + 1) - (z.re - 1) := Int.modEq_iff_dvd.mp h4
  have h6 : (z.re + 1) - (z.re - 1) = 2 := by ring
  rw [h6] at h5
  norm_num at h5

lemma diag_eq_of_absDelta_eq_zero {Pa : Work.FITop.Params} {φ : ℝ} {β : GaussianInt → ℂ}
    (hβ : Work.FIArea4.IsPrimBoxCoeff Pa φ β) {z1 z2 : GaussianInt}
    (hd : Work.FIPlan.absDelta z1 z2 = 0) (h1 : β z1 ≠ 0) (h2 : β z2 ≠ 0) : z2 = z1 := by
  rcases Delta_eq_zero_or_neg (Work.FIArea4.IsPrimBoxCoeff.coprime hβ h1)
      (Work.FIArea4.IsPrimBoxCoeff.coprime hβ h2)
      (Delta_eq_zero_of_absDelta_eq_zero hd) with h | h
  · exact h
  · exfalso
    exact not_isPrimary_neg (hβ.inPolarBox h1).1 (h ▸ (hβ.inPolarBox h2).1)

/-! ## 2. Modulus bounds for the character and the phase -/

lemma S15y_nonneg (X j d : ℕ) (z1 z2 : GaussianInt) : 0 ≤ Work.FIArea4.S15y X j d z1 z2 := by
  unfold Work.FIArea4.S15y; positivity

lemma norm_S15theta_eq_one (ℓ : ℤ) (z1 z2 : GaussianInt) :
    ‖Work.FIArea4.S15theta ℓ z1 z2‖ = 1 := by
  rw [Work.FIArea4.S15theta, Complex.norm_exp]
  simp

lemma norm_S15phase_le (X j : ℕ) (u t : ℝ) (i : Work.FIArea4.S15Id) :
    ‖Work.FIArea4.S15phase X j u t i‖ ≤ 1 := by
  rw [Work.FIArea4.S15phase, norm_mul]
  have h1 : ‖Complex.exp (2 * Real.pi * Complex.I
      * ((u : ℂ) * ((Work.FIArea4.S15x i.1.1 i.1.2 : ℝ) : ℂ)))‖ = 1 := by
    rw [Complex.norm_exp]
    simp [Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im]
  rw [h1, one_mul]
  rcases eq_or_lt_of_le (S15y_nonneg X j i.2 i.1.1 i.1.2) with h | h
  · rw [← h, show (((0:ℝ):ℂ)) = (0:ℂ) from by norm_num, Complex.cpow_def]
    split_ifs <;> simp
  · rw [Complex.norm_cpow_eq_rpow_re_of_pos h]; simp

/-! ## 3. The diagonal bound -/

/-- The summand of the *diagonal* part of the round-6 per-modulus sum. -/
def diagTerm6 (X j d : ℕ) (β : GaussianInt → ℂ) (ℓ : ℤ) (u t : ℝ)
    (z1 z2 : GaussianInt) : ℂ :=
  if Work.FIPlan.absDelta z1 z2 = 0 ∧ X < d
    then S15coef6 β ((z1, z2), d) * Work.FIArea4.S15theta ℓ z1 z2
      * Work.FIArea4.S15phase X j u t ((z1, z2), d)
    else 0

lemma norm_diagTerm6_le (X j d : ℕ) (β : GaussianInt → ℂ) (ℓ : ℤ) (u t : ℝ)
    (z1 z2 : GaussianInt) :
    ‖diagTerm6 X j d β ℓ u t z1 z2‖ ≤ 2 * ‖β z1‖ * ‖β z2‖ := by
  unfold diagTerm6
  by_cases hc : Work.FIPlan.absDelta z1 z2 = 0 ∧ X < d
  · rw [if_pos hc, norm_mul, norm_mul, norm_S15theta_eq_one, mul_one]
    have h1 := norm_S15coef6_le β ((z1, z2), d)
    have h2 := norm_S15phase_le X j u t ((z1, z2), d)
    calc ‖S15coef6 β ((z1, z2), d)‖ * ‖Work.FIArea4.S15phase X j u t ((z1, z2), d)‖
        ≤ (2 * ‖β ((z1, z2), d).1.1‖ * ‖β ((z1, z2), d).1.2‖) * 1 :=
          mul_le_mul h1 h2 (norm_nonneg _) (by positivity)
      _ = 2 * ‖β z1‖ * ‖β z2‖ := by simp
  · rw [if_neg hc, norm_zero]; positivity

theorem diagSum6_le (Pa : Work.FITop.Params) (X j d : ℕ) (φ : ℝ) (β : GaussianInt → ℂ)
    (ℓ : ℤ) (u t : ℝ) (hβ : Work.FIArea4.IsPrimBoxCoeff Pa φ β) :
    ‖diagSum6 Pa X j d β ℓ u t‖ ≤ 2 * ∑ z ∈ Work.FITop.boxN Pa, ‖β z‖ ^ 2 := by
  classical
  have haux : ‖∑ z1 ∈ Work.FITop.boxN Pa, ∑ z2 ∈ Work.FITop.boxN Pa,
      diagTerm6 X j d β ℓ u t z1 z2‖ ≤ 2 * ∑ z ∈ Work.FITop.boxN Pa, ‖β z‖ ^ 2 := by
    have hle : ∀ z1 ∈ Work.FITop.boxN Pa, ∀ z2 ∈ Work.FITop.boxN Pa,
        ‖diagTerm6 X j d β ℓ u t z1 z2‖
          ≤ (if z2 = z1 then 2 * ‖β z1‖ ^ 2 else 0) := by
      intro z1 _ z2 _
      by_cases hz : z2 = z1
      · rw [if_pos hz, hz]
        calc ‖diagTerm6 X j d β ℓ u t z1 z1‖ ≤ 2 * ‖β z1‖ * ‖β z1‖ :=
              norm_diagTerm6_le X j d β ℓ u t z1 z1
          _ = 2 * ‖β z1‖ ^ 2 := by ring
      · rw [if_neg hz]
        have hzero : diagTerm6 X j d β ℓ u t z1 z2 = 0 := by
          unfold diagTerm6
          by_cases hc : Work.FIPlan.absDelta z1 z2 = 0 ∧ X < d
          · have hcoef : S15coef6 β ((z1, z2), d) = 0 := by
              by_cases hb1 : β z1 = 0
              · exact S15coef6_eq_zero_of β d (Or.inl hb1)
              · refine S15coef6_eq_zero_of β d (Or.inr ?_)
                by_contra hb2
                exact hz (diag_eq_of_absDelta_eq_zero hβ hc.1 hb1 hb2)
            rw [if_pos hc, hcoef]; ring
          · rw [if_neg hc]
        rw [hzero, norm_zero]
    have hkey : ∀ z1 ∈ Work.FITop.boxN Pa,
        ∑ z2 ∈ Work.FITop.boxN Pa, ‖diagTerm6 X j d β ℓ u t z1 z2‖
          ≤ 2 * ‖β z1‖ ^ 2 := by
      intro z1 hz1
      calc ∑ z2 ∈ Work.FITop.boxN Pa, ‖diagTerm6 X j d β ℓ u t z1 z2‖
          ≤ ∑ z2 ∈ Work.FITop.boxN Pa, (if z2 = z1 then 2 * ‖β z1‖ ^ 2 else 0) :=
            Finset.sum_le_sum (hle z1 hz1)
        _ = 2 * ‖β z1‖ ^ 2 := by rw [Finset.sum_ite_eq', if_pos hz1]
    calc ‖∑ z1 ∈ Work.FITop.boxN Pa, ∑ z2 ∈ Work.FITop.boxN Pa,
          diagTerm6 X j d β ℓ u t z1 z2‖
        ≤ ∑ z1 ∈ Work.FITop.boxN Pa,
            ‖∑ z2 ∈ Work.FITop.boxN Pa, diagTerm6 X j d β ℓ u t z1 z2‖ :=
          norm_sum_le _ _
      _ ≤ ∑ z1 ∈ Work.FITop.boxN Pa,
            ∑ z2 ∈ Work.FITop.boxN Pa, ‖diagTerm6 X j d β ℓ u t z1 z2‖ :=
          Finset.sum_le_sum (fun z1 _ => norm_sum_le _ _)
      _ ≤ ∑ z1 ∈ Work.FITop.boxN Pa, 2 * ‖β z1‖ ^ 2 := Finset.sum_le_sum hkey
      _ = 2 * ∑ z1 ∈ Work.FITop.boxN Pa, ‖β z1‖ ^ 2 := by rw [Finset.mul_sum]
  have hpoint : ∀ z1 z2 : GaussianInt, diagTerm6 X j d β ℓ u t z1 z2
      = (if Work.FIPlan.absDelta z1 z2 = 0 ∧ X < d then
          S15coef6 β ((z1, z2), d) * Work.FIArea4.S15theta ℓ z1 z2
            * Work.FIArea4.S15phase X j u t ((z1, z2), d) else 0) := fun _ _ => rfl
  have hEq : (∑ z1 ∈ Work.FITop.boxN Pa, ∑ z2 ∈ Work.FITop.boxN Pa,
        diagTerm6 X j d β ℓ u t z1 z2) = diagSum6 Pa X j d β ℓ u t := by
    unfold diagSum6
    refine Finset.sum_congr rfl (fun z1 _ => Finset.sum_congr rfl (fun z2 _ => ?_))
    exact hpoint z1 z2
  rw [← hEq]
  exact haux

end

end Diag6
end Work.FIArea4.A6psi
