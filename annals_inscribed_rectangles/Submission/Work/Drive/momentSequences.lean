import Mathlib

/-!
# `momentSequences`

We exhibit explicit sequences `a b : ℕ → ℝ` with `b m = 2^m` such that
`∑' m, a m * (b m)^j = (-1)^j` for every `j : ℕ`, with absolute convergence.

The idea is elementary: `2 ≡ -1 (mod 3)`, hence `2^j ≡ (-1)^j (mod 3)`, and therefore the
entire function `F x = (2/√3) · sin (2πx/3)` satisfies `F (2^j) = (-1)^j`.  Taking for `a`
the sequence of Taylor coefficients of `F` at `0`, the moment `∑' m, a m * (b m)^j` is
`∑' m, a m * (2^j)^m = F (2^j) = (-1)^j`, the interchange of the power series being
justified by absolute convergence (the coefficients decay like `(2π/3)^m / m!`).
-/

namespace Work.Drive

namespace MomentSeq

noncomputable section

/-- The nodes `b m = 2^m`. -/
def bseq (m : ℕ) : ℝ := (2 : ℝ) ^ m

lemma bseq_pos (m : ℕ) : 0 < bseq m := pow_pos (by norm_num) m

lemma bseq_mono : Monotone bseq := by
  refine monotone_nat_of_le_succ (fun m => ?_)
  simp only [bseq]
  exact pow_le_pow_right₀ (by norm_num) (Nat.le_succ m)

lemma bseq_tendsto : Filter.Tendsto bseq Filter.atTop Filter.atTop :=
  tendsto_pow_atTop_atTop_of_one_lt (by norm_num)

/-- The Taylor coefficients at `0` of the entire function `(2/√3) • sin (2πx/3)`. -/
def aseq (m : ℕ) : ℝ :=
  (2 / Real.sqrt 3) * (Complex.I ^ m).im * (2 * Real.pi / 3) ^ m / (m.factorial : ℝ)

lemma im_div_ofReal (z : ℂ) (s : ℝ) : (z / (s : ℂ)).im = z.im * s⁻¹ := by
  rw [div_eq_mul_inv, ← Complex.ofReal_inv, Complex.mul_im, Complex.ofReal_im,
    Complex.ofReal_re]
  ring

lemma im_mul_I_pow_ofReal (y : ℝ) (m : ℕ) :
    ((Complex.I * (y : ℂ)) ^ m).im = (Complex.I ^ m).im * y ^ m := by
  rw [mul_pow, ← Complex.ofReal_pow, Complex.mul_im, Complex.ofReal_im, Complex.ofReal_re]
  ring

/-- The `m`-th term of the tsum defining `(2/√3) sin (2πx/3)`. -/
lemma aseq_mul_pow_eq (x : ℝ) (m : ℕ) :
    aseq m * x ^ m = (2 / Real.sqrt 3) *
      ((Complex.I * (((2 * Real.pi * x / 3 : ℝ)) : ℂ)) ^ m / (m.factorial : ℂ)).im := by
  rw [aseq]
  conv_rhs => rw [← Complex.ofReal_natCast]
  rw [im_div_ofReal (s := (m.factorial : ℝ)), im_mul_I_pow_ofReal]
  have h : (2 * Real.pi * x / 3 : ℝ) = (2 * Real.pi / 3) * x := by ring
  rw [h, mul_pow]
  ring

/-- The power series of `(2/√3) sin (2πx/3)`. -/
theorem tsum_aseq_mul_pow (x : ℝ) :
    ∑' m : ℕ, aseq m * x ^ m = (2 / Real.sqrt 3) * Real.sin (2 * Real.pi * x / 3) := by
  have hz : HasSum
      (fun m : ℕ => (Complex.I * (((2 * Real.pi * x / 3 : ℝ)) : ℂ)) ^ m / (m.factorial : ℂ))
      (Complex.exp (Complex.I * (((2 * Real.pi * x / 3 : ℝ)) : ℂ))) := by
    have h := NormedSpace.expSeries_div_hasSum_exp
      (Complex.I * (((2 * Real.pi * x / 3 : ℝ)) : ℂ))
    simpa only [Complex.exp_eq_exp_ℂ] using h
  have hzi : HasSum
      (fun m : ℕ =>
        ((Complex.I * (((2 * Real.pi * x / 3 : ℝ)) : ℂ)) ^ m / (m.factorial : ℂ)).im)
      ((Complex.exp (Complex.I * (((2 * Real.pi * x / 3 : ℝ)) : ℂ))).im) :=
    hz.map Complex.imCLM Complex.imCLM.continuous
  rw [tsum_congr (fun m => aseq_mul_pow_eq x m), tsum_mul_left, hzi.tsum_eq]
  congr 1
  rw [show Complex.I * (((2 * Real.pi * x / 3 : ℝ)) : ℂ)
        = (((2 * Real.pi * x / 3 : ℝ)) : ℂ) * Complex.I by ring,
      Complex.exp_ofReal_mul_I]
  simp only [Complex.add_im, Complex.ofReal_im, zero_add, Complex.mul_im, Complex.I_im,
    Complex.I_re, mul_zero, add_zero, Complex.ofReal_re]
  ring

lemma abs_aseq_le (m : ℕ) :
    |aseq m| ≤ (2 / Real.sqrt 3) * (2 * Real.pi / 3) ^ m / (m.factorial : ℝ) := by
  have hc : (0 : ℝ) < 2 / Real.sqrt 3 :=
    div_pos (by norm_num) (Real.sqrt_pos.mpr (by norm_num))
  have hI : |(Complex.I ^ m).im| ≤ 1 := by
    have h1 := Complex.abs_im_le_norm (Complex.I ^ m)
    rwa [norm_pow, Complex.norm_I, one_pow] at h1
  have hp : (0 : ℝ) ≤ (2 * Real.pi / 3) ^ m := by positivity
  have hf : (0 : ℝ) < (m.factorial : ℝ) := by exact_mod_cast m.factorial_pos
  rw [aseq, abs_div, abs_mul, abs_mul, abs_of_pos hc, abs_of_nonneg hp, abs_of_pos hf]
  have h2 : (2 / Real.sqrt 3) * |(Complex.I ^ m).im| ≤ (2 / Real.sqrt 3) :=
    mul_le_of_le_one_right hc.le hI
  have h3 : (0 : ℝ) ≤ (2 * Real.pi / 3) ^ m / (m.factorial : ℝ) := div_nonneg hp hf.le
  calc (2 / Real.sqrt 3) * |(Complex.I ^ m).im| * (2 * Real.pi / 3) ^ m / (m.factorial : ℝ)
      = ((2 / Real.sqrt 3) * |(Complex.I ^ m).im|)
          * ((2 * Real.pi / 3) ^ m / (m.factorial : ℝ)) := by ring
    _ ≤ (2 / Real.sqrt 3) * ((2 * Real.pi / 3) ^ m / (m.factorial : ℝ)) :=
        mul_le_mul_of_nonneg_right h2 h3
    _ = (2 / Real.sqrt 3) * (2 * Real.pi / 3) ^ m / (m.factorial : ℝ) := by ring

/-- The power series of `(2/√3) sin (2πx/3)` converges absolutely everywhere. -/
lemma summable_aseq_mul_pow (x : ℝ) : Summable (fun m : ℕ => aseq m * x ^ m) := by
  have hmain : Summable
      (fun m : ℕ => (2 / Real.sqrt 3) * ((2 * Real.pi / 3 * |x|) ^ m / (m.factorial : ℝ))) :=
    (Real.summable_pow_div_factorial (2 * Real.pi / 3 * |x|)).mul_left (2 / Real.sqrt 3)
  refine Summable.of_norm_bounded hmain (fun m => ?_)
  have h1 := abs_aseq_le m
  calc ‖aseq m * x ^ m‖ = |aseq m| * |x| ^ m := by rw [Real.norm_eq_abs, abs_mul, abs_pow]
    _ ≤ ((2 / Real.sqrt 3) * (2 * Real.pi / 3) ^ m / (m.factorial : ℝ)) * |x| ^ m := by
          gcongr
    _ = (2 / Real.sqrt 3) * ((2 * Real.pi / 3 * |x|) ^ m / (m.factorial : ℝ)) := by
          rw [mul_pow]; ring

/-- `sin (2^j · 2π/3) = (-1)^j √3/2`. -/
lemma sin_cos_two_pow (j : ℕ) :
    Real.sin ((2 : ℝ) ^ j * (2 * Real.pi / 3)) = (-1 : ℝ) ^ j * (Real.sqrt 3 / 2) ∧
    Real.cos ((2 : ℝ) ^ j * (2 * Real.pi / 3)) = -(1 / 2) := by
  induction j with
  | zero =>
      simp only [pow_zero, one_mul]
      constructor
      · rw [show (2 * Real.pi / 3 : ℝ) = Real.pi - Real.pi / 3 by ring, Real.sin_pi_sub,
          Real.sin_pi_div_three]
      · rw [show (2 * Real.pi / 3 : ℝ) = Real.pi - Real.pi / 3 by ring, Real.cos_pi_sub,
          Real.cos_pi_div_three]
  | succ j ih =>
      obtain ⟨hs, hc⟩ := ih
      have h2 : (2 : ℝ) ^ (j + 1) * (2 * Real.pi / 3)
          = 2 * ((2 : ℝ) ^ j * (2 * Real.pi / 3)) := by rw [pow_succ]; ring
      rw [h2, Real.sin_two_mul, Real.cos_two_mul, hs, hc, pow_succ]
      refine ⟨?_, ?_⟩ <;> ring

end

end MomentSeq

open MomentSeq

theorem momentSequences :
    ∃ (a b : ℕ → ℝ), (∀ m : ℕ, 0 < b m) ∧ Monotone b ∧
      Filter.Tendsto b Filter.atTop Filter.atTop ∧
      (∀ j : ℕ, Summable (fun m : ℕ => a m * (b m) ^ j)) ∧
      (∀ j : ℕ, ∑' m : ℕ, a m * (b m) ^ j = (-1 : ℝ) ^ j) := by
  refine ⟨MomentSeq.aseq, MomentSeq.bseq, MomentSeq.bseq_pos, MomentSeq.bseq_mono,
    MomentSeq.bseq_tendsto, ?_, ?_⟩
  · intro j
    have h : (fun m : ℕ => MomentSeq.aseq m * (MomentSeq.bseq m) ^ j)
        = (fun m : ℕ => MomentSeq.aseq m * ((2 : ℝ) ^ j) ^ m) := by
      funext m
      rw [MomentSeq.bseq, ← pow_mul, ← pow_mul, Nat.mul_comm]
    rw [h]
    exact MomentSeq.summable_aseq_mul_pow _
  · intro j
    have h : (fun m : ℕ => MomentSeq.aseq m * (MomentSeq.bseq m) ^ j)
        = (fun m : ℕ => MomentSeq.aseq m * ((2 : ℝ) ^ j) ^ m) := by
      funext m
      rw [MomentSeq.bseq, ← pow_mul, ← pow_mul, Nat.mul_comm]
    rw [h, MomentSeq.tsum_aseq_mul_pow]
    have harg : 2 * Real.pi * (2 : ℝ) ^ j / 3 = (2 : ℝ) ^ j * (2 * Real.pi / 3) := by ring
    rw [harg, (MomentSeq.sin_cos_two_pow j).1]
    have h2 : (2 / Real.sqrt 3) * (Real.sqrt 3 / 2) = 1 := by
      rw [div_mul_div_comm, mul_comm (Real.sqrt 3) 2]
      exact div_self (by positivity)
    calc (2 / Real.sqrt 3) * ((-1 : ℝ) ^ j * (Real.sqrt 3 / 2))
        = (-1 : ℝ) ^ j * ((2 / Real.sqrt 3) * (Real.sqrt 3 / 2)) := by ring
      _ = (-1 : ℝ) ^ j := by rw [h2, mul_one]

end Work.Drive
