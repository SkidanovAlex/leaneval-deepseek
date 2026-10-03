import Mathlib
import Submission.Work.FIArea2.Sec6Defs

namespace Work.FIArea2

/-! ## Elementary coordinate facts -/

/-- `|z|²` is the sum of the squares of the coordinates, as a real number. -/
lemma gnorm_cast_sq_real (z : GaussianInt) :
    ((Work.FIPlan.gnorm z : ℕ) : ℝ) = (z.re : ℝ) ^ 2 + (z.im : ℝ) ^ 2 := by
  rw [Work.FIPlan.gnorm, GaussianInt.natAbs_norm_eq, Nat.cast_add, Nat.cast_mul, Nat.cast_mul]
  rw [Nat.cast_natAbs, Nat.cast_natAbs]
  rw [Int.cast_abs, Int.cast_abs, ← sq, ← sq, sq_abs, sq_abs]

/-- `Re(z̄₁z₂) = r₁r₂ + s₁s₂` with real coordinates. -/
lemma star_mul_re_real (z1 z2 : GaussianInt) :
    (((star z1 * z2).re : ℤ) : ℝ) = (z1.re : ℝ) * (z2.re : ℝ) + (z1.im : ℝ) * (z2.im : ℝ) := by
  have h : (star z1 * z2).re = z1.re * z2.re + z1.im * z2.im := by
    simp [Zsqrtd.re_mul]
  rw [h]; push_cast; ring

lemma gnorm_eq_zero_iff' (z : GaussianInt) : Work.FIPlan.gnorm z = 0 ↔ z = 0 := by
  constructor
  · intro h
    have h2 : ((Work.FIPlan.gnorm z : ℕ) : ℝ) = 0 := by exact_mod_cast h
    rw [gnorm_cast_sq_real] at h2
    have hre : (z.re : ℝ) = 0 := by nlinarith [sq_nonneg (z.re : ℝ), sq_nonneg (z.im : ℝ)]
    have him : (z.im : ℝ) = 0 := by nlinarith [sq_nonneg (z.re : ℝ), sq_nonneg (z.im : ℝ)]
    refine Zsqrtd.ext ?_ ?_
    · have : z.re = 0 := by exact_mod_cast hre
      simpa using this
    · have : z.im = 0 := by exact_mod_cast him
      simpa using this
  · intro h; subst h; simp [Work.FIPlan.gnorm]

lemma gnorm_pos_of_ne_zero {z : GaussianInt} (hz : z ≠ 0) : 0 < Work.FIPlan.gnorm z :=
  Nat.pos_of_ne_zero fun h => hz ((gnorm_eq_zero_iff' z).mp h)

/-! ## The substitution identity

Pure algebra: with `s₁² = |Δ|/|z₂|`, `s₂² = |Δ|/|z₁|` the change of variables
`t_j = s_j τ_j` multiplies the quadratic form `|t₁²z₂ − t₂²z₁|²` by `|Δ|²` and turns it into
the quartic `g(τ) = τ₁⁴ − 2γτ₁²τ₂² + τ₂⁴` with `γ = Re(z̄₁z₂)/(|z₁||z₂|)`. -/

lemma quartic_scaling_identity (a b c d τ1 τ2 D G1 G2 : ℝ)
    (hD : D ≠ 0) (hG1 : G1 = a^2+b^2) (hG2 : G2 = c^2+d^2)
    (hG1pos : 0 < G1) (hG2pos : 0 < G2) :
    (((D/Real.sqrt G2) * τ1^2 * c - (D/Real.sqrt G1)*τ2^2*a)^2
     + ((D/Real.sqrt G2)*τ1^2*d - (D/Real.sqrt G1)*τ2^2*b)^2)/D^2
    = τ1^4 - 2*((a*c+b*d)/Real.sqrt (G1*G2))*τ1^2*τ2^2 + τ2^4 := by
  rw [Real.sqrt_mul (le_of_lt hG1pos)]
  subst hG1; subst hG2
  have h1 : Real.sqrt (a^2+b^2) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hG1pos)
  have h2 : Real.sqrt (c^2+d^2) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hG2pos)
  field_simp
  ring_nf
  rw [Real.sq_sqrt (le_of_lt hG2pos), Real.sq_sqrt (le_of_lt hG1pos)]
  ring

/-- The argument of `phiOf f z₁ z₂` after the §6 scaling `t_j = s_j τ_j` equals
`g(τ) = τ₁⁴ − 2γτ₁²τ₂² + τ₂⁴`. -/
lemma phiOf_arg_eq (z1 z2 : GaussianInt) (hd : Work.FIPlan.absDelta z1 z2 ≠ 0) (τ : ℝ × ℝ) :
    (((secScale₁ z1 z2 * τ.1) ^ 2 * (z2.re : ℝ)
        - (secScale₂ z1 z2 * τ.2) ^ 2 * (z1.re : ℝ)) ^ 2
      + ((secScale₁ z1 z2 * τ.1) ^ 2 * (z2.im : ℝ)
        - (secScale₂ z1 z2 * τ.2) ^ 2 * (z1.im : ℝ)) ^ 2)
      / (((Work.FIPlan.absDelta z1 z2 : ℕ) : ℝ)) ^ 2
    = gQuartic (gamOf z1 z2) τ := by
  have hz1 : z1 ≠ 0 := by
    intro h
    apply hd
    simp [Work.FIPlan.absDelta, Work.FIPlan.Delta, h]
  have hz2 : z2 ≠ 0 := by
    intro h
    apply hd
    simp [Work.FIPlan.absDelta, Work.FIPlan.Delta, h]
  have hDpos : 0 < ((Work.FIPlan.absDelta z1 z2 : ℕ) : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero hd
  have hG1pos : 0 < ((Work.FIPlan.gnorm z1 : ℕ) : ℝ) := by
    exact_mod_cast gnorm_pos_of_ne_zero hz1
  have hG2pos : 0 < ((Work.FIPlan.gnorm z2 : ℕ) : ℝ) := by
    exact_mod_cast gnorm_pos_of_ne_zero hz2
  have hs1 : (secScale₁ z1 z2) ^ 2
      = ((Work.FIPlan.absDelta z1 z2 : ℕ) : ℝ)
        / Real.sqrt (((Work.FIPlan.gnorm z2 : ℕ) : ℝ)) := by
    rw [secScale₁, Real.sq_sqrt (div_nonneg (le_of_lt hDpos) (Real.sqrt_nonneg _))]
  have hs2 : (secScale₂ z1 z2) ^ 2
      = ((Work.FIPlan.absDelta z1 z2 : ℕ) : ℝ)
        / Real.sqrt (((Work.FIPlan.gnorm z1 : ℕ) : ℝ)) := by
    rw [secScale₂, Real.sq_sqrt (div_nonneg (le_of_lt hDpos) (Real.sqrt_nonneg _))]
  have hgam : gamOf z1 z2
      = ((z1.re : ℝ) * (z2.re : ℝ) + (z1.im : ℝ) * (z2.im : ℝ))
        / Real.sqrt ((((Work.FIPlan.gnorm z1 : ℕ) : ℝ)
          * (((Work.FIPlan.gnorm z2 : ℕ) : ℝ)))) := by
    rw [gamOf, star_mul_re_real]
  rw [mul_pow, mul_pow, hs1, hs2, hgam]
  unfold gQuartic
  exact quartic_scaling_identity (z1.re : ℝ) (z1.im : ℝ) (z2.re : ℝ) (z2.im : ℝ) τ.1 τ.2
    (((Work.FIPlan.absDelta z1 z2 : ℕ) : ℝ))
    (((Work.FIPlan.gnorm z1 : ℕ) : ℝ)) (((Work.FIPlan.gnorm z2 : ℕ) : ℝ))
    (ne_of_gt hDpos) (gnorm_cast_sq_real z1) (gnorm_cast_sq_real z2) hG1pos hG2pos

lemma phiOf_comp_secScale (f : ℝ → ℝ) (z1 z2 : GaussianInt)
    (hd : Work.FIPlan.absDelta z1 z2 ≠ 0) (τ : ℝ × ℝ) :
    phiOf f z1 z2 (secScale₁ z1 z2 * τ.1, secScale₂ z1 z2 * τ.2)
      = f (gQuartic (gamOf z1 z2) τ) := by
  unfold phiOf
  congr 1
  exact phiOf_arg_eq z1 z2 hd τ

end Work.FIArea2
