import Mathlib
import Submission.Work.LinnikContract.Defs
import Submission.Work.LinnikAreas.DhK.Defs
import Submission.Commons.NumberTheory.Linnik.completedL_zero_strip

/-!
# `Work.LinnikAreas.DhK.Reduction`

Elementary reductions used by the Deuring–Heilbronn (Turán) argument:

* a zero of `zeroMult χ` is a zero of `completedLFunction χ.primitiveCharacter`, and lies in the
  critical strip `0 < Re u < 1`;
* a real character takes the values `0, ±1`, so `1 + χ n` has non-negative real part;
* the elementary "trivial zeros" lemma: for real `ω < c`,
  `Re (1/(c-ω)^{2j} + 1/(c+iγ'-ω)^{2j}) ≥ 0`.
-/

open scoped Classical BigOperators
noncomputable section

namespace Work.LinnikAreas.DhK

open DirichletCharacter

/-- A non-principal character of level `q` forces `2 ≤ q`. -/
lemma two_le_of_ne_one {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q} (h : χ ≠ 1) : 2 ≤ q := by
  by_contra hq
  have hqpos : 0 < q := Nat.pos_of_ne_zero (NeZero.ne q)
  have hq1 : q = 1 := by omega
  exact h (DirichletCharacter.level_one' χ hq1)

/-- The primitive character inducing a non-principal character is non-principal. -/
lemma primitiveCharacter_ne_one {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hχ : χ ≠ 1) : χ.primitiveCharacter ≠ 1 := by
  intro h
  exact hχ (by rw [← DirichletCharacter.changeLevel_primitiveCharacter χ, h,
    DirichletCharacter.changeLevel_one χ.conductor_dvd_level])

/-- A `zeroMult`-zero is an ordinary zero of the completed `L`-function of the primitive
character inducing `χ`. -/
lemma completedLFunction_primitive_eq_zero_of_zeroMult {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) [NeZero χ.conductor] {u : ℂ}
    (hz : Work.LinnikContract.zeroMult χ u ≠ 0) :
    DirichletCharacter.completedLFunction χ.primitiveCharacter u = 0 := by
  exact apply_eq_zero_of_analyticOrderNatAt_ne_zero
    (by simpa only [Work.LinnikContract.zeroMult] using hz)

/-- `zeroMult`-zeros lie in the critical strip. -/
lemma zeroMult_strip {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) [NeZero χ.conductor]
    (hχ : χ ≠ 1) {u : ℂ}
    (hz : Work.LinnikContract.zeroMult χ u ≠ 0) : 0 < u.re ∧ u.re < 1 := by
  have hψne : χ.primitiveCharacter ≠ 1 := primitiveCharacter_ne_one hχ
  exact Commons.NumberTheory.Linnik.completedL_zero_strip χ.primitiveCharacter hψne
    (DirichletCharacter.primitiveCharacter_isPrimitive χ)
    (completedLFunction_primitive_eq_zero_of_zeroMult χ hz)

/-- A `zeroMult`-zero of `χ` is (with positive multiplicity) a non-trivial zero of `ζ_K`. -/
lemma kMult_pos_of_zeroMult {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    [NeZero χ.conductor] {u : ℂ} (hz : Work.LinnikContract.zeroMult χ u ≠ 0) :
    0 < kMult χ.primitiveCharacter u := by
  have h : analyticOrderNatAt
      (DirichletCharacter.completedLFunction χ.primitiveCharacter) u ≠ 0 := by
    simpa only [Work.LinnikContract.zeroMult] using hz
  simp only [kMult]
  omega

/-- A character of order dividing `2` is real-valued: `1 + χ n` has non-negative real part. -/
lemma one_add_re_nonneg {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ^ 2 = 1)
    (n : ℕ) : 0 ≤ 1 + (χ (n : ZMod q)).re := by
  have h2 : ((χ (n : ZMod q)) : ℂ) ^ 2 = (1 : DirichletCharacter ℂ q) (n : ZMod q) := by
    have h := DFunLike.congr_fun hχ (n : ZMod q)
    simpa [pow_two] using h
  rcases eq_or_ne ((1 : DirichletCharacter ℂ q) (n : ZMod q)) 1 with h1 | h1
  · have hfac : (χ (n : ZMod q) - 1) * (χ (n : ZMod q) + 1) = 0 := by
      have h0 : ((χ (n : ZMod q)) : ℂ) ^ 2 - 1 = 0 := by rw [h2, h1]; ring
      linear_combination h0
    rcases mul_eq_zero.mp hfac with h | h
    · rw [sub_eq_zero] at h; rw [h]; norm_num
    · rw [add_eq_zero_iff_eq_neg] at h; rw [h]; simp
  · have hnu : ¬ IsUnit (n : ZMod q) := fun hu => h1 (MulChar.one_apply hu)
    rw [MulCharClass.map_nonunit χ hnu]; simp

/-- **The elementary "trivial zeros" bound**: for real `ω < c` and real `γ'`, the real part of
`1/(c-ω)^{2j} + 1/(c+iγ'-ω)^{2j}` is non-negative. -/
lemma trivialZero_term_nonneg {c γ' ω : ℝ} (j : ℕ) (h : ω < c) :
    0 ≤ (1 / ((c : ℂ) - (ω : ℂ)) ^ (2 * j)).re
      + (1 / ((c : ℂ) + Complex.I * (γ' : ℂ) - (ω : ℂ)) ^ (2 * j)).re := by
  set d : ℝ := c - ω with hd
  have hdpos : 0 < d := by rw [hd]; linarith
  set D : ℝ := d ^ 2 + γ' ^ 2 with hD
  have hDpos : 0 < D := by rw [hD]; positivity
  have hdD : d ^ 2 ≤ D := by rw [hD]; nlinarith [sq_nonneg γ']
  have hcast : (c : ℂ) - (ω : ℂ) = ((d : ℝ) : ℂ) := by rw [hd]; push_cast; ring
  have h1 : (1 / ((c : ℂ) - (ω : ℂ)) ^ (2 * j)).re = 1 / d ^ (2 * j) := by
    rw [hcast]
    have hcast' : (1 : ℂ) / (((d : ℝ) : ℂ)) ^ (2 * j) = (((1 / d ^ (2 * j) : ℝ)) : ℂ) := by
      push_cast; ring
    rw [hcast', Complex.ofReal_re]
  have hz : (c : ℂ) + Complex.I * (γ' : ℂ) - (ω : ℂ) = (d : ℂ) + Complex.I * (γ' : ℂ) := by
    rw [hd]; push_cast; ring
  set z : ℂ := (d : ℂ) + Complex.I * (γ' : ℂ) with hzdef
  have hznorm : ‖z‖ ^ 2 = D := by
    have : ‖z‖ ^ 2 = z.re ^ 2 + z.im ^ 2 := by
      rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]; ring
    rw [this, hzdef, hD]
    simp only [Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, mul_zero, mul_one, zero_sub,
      sub_zero, add_zero]
    ring
  have h2 : -(1 / D ^ j) ≤ (1 / ((c : ℂ) + Complex.I * (γ' : ℂ) - (ω : ℂ)) ^ (2 * j)).re := by
    rw [hz]
    have hne : z ^ (2 * j) ≠ 0 := by
      apply pow_ne_zero
      intro h0
      have : ‖z‖ = 0 := by rw [h0]; simp
      have hD0 : D = 0 := by rw [← hznorm, this]; simp
      exact hDpos.ne' hD0
    have hnorm : ‖(1 / z ^ (2 * j) : ℂ)‖ = 1 / D ^ j := by
      rw [norm_div, norm_one, norm_pow]
      have hpow : ‖z‖ ^ (2 * j) = D ^ j := by
        rw [show 2 * j = 2 * j by ring, pow_mul, hznorm]
      rw [hpow]
    have hle := (abs_le.mp (Complex.abs_re_le_norm (1 / z ^ (2 * j) : ℂ))).1
    calc -(1 / D ^ j) = -‖(1 / z ^ (2 * j) : ℂ)‖ := by rw [hnorm]
      _ ≤ (1 / z ^ (2 * j) : ℂ).re := hle
  have h3 : 1 / D ^ j ≤ 1 / d ^ (2 * j) := by
    apply one_div_le_one_div_of_le
    · positivity
    · calc d ^ (2 * j) = (d ^ 2) ^ j := by rw [← pow_mul]
        _ ≤ D ^ j := pow_le_pow_left₀ (by positivity) hdD j
  linarith [h1, h2, h3]

end Work.LinnikAreas.DhK

end
