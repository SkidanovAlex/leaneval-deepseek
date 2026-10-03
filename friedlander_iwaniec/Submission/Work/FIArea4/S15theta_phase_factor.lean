import Mathlib
import Submission.Work.FIArea4.S15stratumDefs

namespace Work.FIArea4

/-!
# FI §15: the `z`-factorisation of `S15theta · S15phase`

The angular character `S15theta` and the phase `S15phase` of the §15 pair sums factor as

`S15theta ℓ z₁ z₂ · S15phase X j u t ((z₁,z₂),d)
   = S15zf u t ℓ z₁ · conj (S15zfV u t ℓ z₂) · (4·X·2^j·d)^{-it}`,

i.e. into a `z₁`-factor, a `z₂`-factor and the `d`-only factor `(4·X·2^j·d)^{-it}` of modulus one.
The elementary analytic ingredients are the behaviour of the complex power under conjugation
(`Complex.conj_cpow`) and its multiplicativity for non-negative real bases
(`Complex.mul_cpow_ofReal_nonneg`, `Complex.div_cpow_ofReal_nonneg`).
-/

/-- Conjugation commutes with `Complex.exp`. -/
private lemma starRingEnd_exp (w : ℂ) :
    (starRingEnd ℂ) (Complex.exp w) = Complex.exp ((starRingEnd ℂ) w) :=
  (Complex.exp_conj w).symm

/-- For a non-negative real base, conjugation of a complex power acts on the exponent. -/
private lemma starRingEnd_ofReal_cpow {a : ℝ} (ha : 0 ≤ a) (w : ℂ) :
    (starRingEnd ℂ) ((a : ℂ) ^ w) = (a : ℂ) ^ ((starRingEnd ℂ) w) := by
  have hx : (a : ℂ).arg ≠ Real.pi := by
    rw [Complex.arg_ofReal_of_nonneg ha]; exact Real.pi_ne_zero.symm
  have h := Complex.conj_cpow (a : ℂ) ((starRingEnd ℂ) w) hx
  simp only [Complex.conj_ofReal, Complex.conj_conj] at h
  exact h.symm

/-- Conjugation of the (purely imaginary) phase exponent `2πi·u·x` with `x : ℝ`. -/
private lemma starRingEnd_arg1 (u x : ℝ) :
    (starRingEnd ℂ) (2 * (Real.pi : ℂ) * Complex.I * ((u : ℂ) * ((x : ℝ) : ℂ)))
      = -(2 * (Real.pi : ℂ) * Complex.I * ((u : ℂ) * ((x : ℝ) : ℂ))) := by
  simp only [map_mul, map_ofNat, Complex.conj_ofReal, Complex.conj_I]
  ring

/-- Conjugation of the (purely imaginary) angular exponent `iℓx` with `x : ℝ`. -/
private lemma starRingEnd_arg2 (ℓ : ℤ) (x : ℝ) :
    (starRingEnd ℂ) (Complex.I * (ℓ : ℂ) * ((x : ℝ) : ℂ))
      = -(Complex.I * (ℓ : ℂ) * ((x : ℝ) : ℂ)) := by
  simp only [map_mul, Complex.conj_ofReal, Complex.conj_I, map_intCast]
  ring

/-- Conjugation of `-i·t` with `t : ℝ`. -/
private lemma starRingEnd_neg_I_t (t : ℝ) :
    (starRingEnd ℂ) (-(Complex.I * (t : ℂ))) = Complex.I * (t : ℂ) := by
  simp only [map_neg, map_mul, Complex.conj_ofReal, Complex.conj_I]
  ring

/-- The explicit conjugate of the `z₂`-factor `S15zfV`. -/
private lemma star_S15zfV (u t : ℝ) (ℓ : ℤ) (z : GaussianInt) :
    star (S15zfV u t ℓ z)
      = Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I * ((u : ℂ) * (((z.im : ℝ) / (z.re : ℝ) : ℝ) : ℂ))))
        * ((((z.re.natAbs : ℝ)) : ℂ) ^ (Complex.I * (t : ℂ)))
        * Complex.exp (Complex.I * (ℓ : ℂ) * (((z.toComplex.arg : ℝ)) : ℂ)) := by
  unfold S15zfV
  rw [Complex.star_def]
  simp only [map_mul, map_inv₀]
  rw [starRingEnd_exp, starRingEnd_arg1, starRingEnd_exp, starRingEnd_arg2]
  rw [starRingEnd_ofReal_cpow (Nat.cast_nonneg z.re.natAbs), starRingEnd_neg_I_t]
  have h3 : ∀ w : ℂ, (Complex.exp (-w))⁻¹ = Complex.exp w := fun w => by
    rw [Complex.exp_neg, inv_inv]
  rw [h3]

/-- Splitting of the `y`-power into the `z₁`-, `z₂`- and `d`-parts. -/
private lemma S15y_cpow_split (X j d : ℕ) (t : ℝ) (z1 z2 : GaussianInt) :
    ((((z1.re * z2.re).natAbs : ℝ) / (4 * (X:ℝ) * (2:ℝ)^j * (d:ℝ)) : ℝ) : ℂ) ^ (Complex.I * (t:ℂ))
      = (((z1.re.natAbs : ℝ) : ℂ) ^ (Complex.I * (t:ℂ)))
        * (((z2.re.natAbs : ℝ) : ℂ) ^ (Complex.I * (t:ℂ)))
        * (((4 * (X:ℝ) * (2:ℝ)^j * (d:ℝ) : ℝ) : ℂ) ^ (-(Complex.I * (t:ℂ)))) := by
  have hA : (0:ℝ) ≤ ((z1.re * z2.re).natAbs : ℝ) := Nat.cast_nonneg _
  have hB : (0:ℝ) ≤ 4 * (X:ℝ) * (2:ℝ)^j * (d:ℝ) := by positivity
  rw [Complex.ofReal_div, Complex.div_cpow_ofReal_nonneg hA hB]
  rw [div_eq_mul_inv, ← Complex.cpow_neg]
  have hmul : (((z1.re * z2.re).natAbs : ℝ) : ℂ)
      = ((z1.re.natAbs:ℝ):ℂ) * ((z2.re.natAbs:ℝ):ℂ) := by
    rw [← Complex.ofReal_mul, Int.natAbs_mul, Nat.cast_mul]
  rw [hmul, Complex.mul_cpow_ofReal_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)]

/-- The final bookkeeping: reassembling the exponentials into the two separated factors. -/
private lemma final_key (P1 P2 A1 A2 m1 m2 Dp : ℂ) :
    Complex.exp (A2 - A1) * (Complex.exp (P1 - P2) * (m1 * m2 * Dp))
      = Complex.exp P1 * m1 * (Complex.exp A1)⁻¹ * (Complex.exp (-P2) * m2 * Complex.exp A2) * Dp := by
  rw [← Complex.exp_neg]
  rw [show Complex.exp P1 * m1 * Complex.exp (-A1) * (Complex.exp (-P2) * m2 * Complex.exp A2) * Dp
        = (Complex.exp P1 * Complex.exp (-P2)) * (Complex.exp (-A1) * Complex.exp A2) * (m1 * m2 * Dp) by ring]
  rw [← Complex.exp_add, ← Complex.exp_add]
  rw [show P1 + -P2 = P1 - P2 by ring, show -A1 + A2 = A2 - A1 by ring]
  ring

theorem S15theta_phase_factor (X j d : ℕ) (u t : ℝ) (ℓ : ℤ) (z1 z2 : GaussianInt) :
    Work.FIArea4.S15theta ℓ z1 z2 * Work.FIArea4.S15phase X j u t ((z1, z2), d)
      = Work.FIArea4.S15zf u t ℓ z1 * star (Work.FIArea4.S15zfV u t ℓ z2)
        * ((((4 : ℝ) * (X : ℝ) * (2 : ℝ) ^ j * (d : ℝ)) : ℝ) : ℂ)
            ^ (-(Complex.I * (t : ℂ))) := by
  simp only [S15theta, S15phase, S15x, S15y, S15zf]
  rw [star_S15zfV, S15y_cpow_split]
  have h1 : Complex.I * (ℓ:ℂ) * (((GaussianInt.toComplex z2).arg - (GaussianInt.toComplex z1).arg : ℝ) : ℂ)
          = Complex.I * (ℓ:ℂ) * (((GaussianInt.toComplex z2).arg:ℝ):ℂ)
            - Complex.I * (ℓ:ℂ) * (((GaussianInt.toComplex z1).arg:ℝ):ℂ) := by
    rw [Complex.ofReal_sub]; ring
  have h2 : 2 * (Real.pi:ℂ) * Complex.I * ((u:ℂ) * (((z1.im:ℝ)/(z1.re:ℝ) - (z2.im:ℝ)/(z2.re:ℝ) : ℝ):ℂ))
          = 2 * (Real.pi:ℂ) * Complex.I * ((u:ℂ) * (((z1.im:ℝ)/(z1.re:ℝ):ℝ):ℂ))
            - 2 * (Real.pi:ℂ) * Complex.I * ((u:ℂ) * (((z2.im:ℝ)/(z2.re:ℝ):ℝ):ℂ)) := by
    rw [Complex.ofReal_sub]; ring
  rw [h1, h2]
  exact final_key _ _ _ _ _ _ _

end Work.FIArea4
