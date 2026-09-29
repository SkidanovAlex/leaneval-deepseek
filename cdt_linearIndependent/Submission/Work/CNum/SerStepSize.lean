import Mathlib
import Submission.Work.CNum.SerUpDefs
import Submission.Work.CNum.ceil_div_abs_le

/-!
# `Work.CNum.SerStepSize` — size of the mantissas produced by one `serUp` step

This is the *size* half of the state invariant `SerInv` of `Submission.Work.CNum.SerUpDefs`:
if `(px, py)` is an approximate value of `c^(k+1)` (`c = spt x y`) with error at most
`m2r pe ≤ 3`, and `R = srad x y e ≤ m2r σ < 1`, then the mantissas `snx`, `sny` of the
upward-rounded (`-Int.ediv (-·) SC`) product `(SC+px, py)·(x,y)/SC` fit into `2^34`.

The argument is elementary.  Since `‖c‖ ≤ R < 1` we have `‖c^(k+1)‖ ≤ 1`, hence
`‖spt px py‖ ≤ m2r pe + 1 ≤ 4`, so `|px|, |py| ≤ 4·SC` and (as `R < 1`) `|x|, |y| ≤ SC`.
The ceiling divisions `snx`, `sny` of `(px·x - py·y)/SC` and `(px·y + py·x)/SC` therefore
differ from a real number of modulus at most `8·SC²/SC = 8·SC` by at most `1 < SC`, which
gives `|snx|, |sny| ≤ 8·SC + 1 = 2^33 + 1` and `|SC + snx| ≤ 9·SC + 1 < 2^34`.
-/

namespace Work.CNum

open Work.ANum

/-- The complex number `(x : ℂ) + y·i` is `SC` times `spt x y`. -/
lemma spt_mul_SC (x y : ℤ) : spt x y * ((SC : ℝ) : ℂ) = ((x : ℝ) + (y : ℝ) * Complex.I) := by
  simp only [spt]
  exact div_mul_cancel₀ _ (by norm_num [SC])

/-- Real norm of the cast `((SC : ℝ) : ℂ)`. -/
lemma norm_SC_complex : ‖(((SC : ℝ) : ℂ))‖ = (SC : ℝ) := by
  have h : Complex.normSq (((SC : ℝ) : ℂ)) = (SC : ℝ) * (SC : ℝ) := Complex.normSq_ofReal (SC : ℝ)
  rw [Complex.normSq_eq_norm_sq] at h
  have h0 : (0 : ℝ) ≤ (SC : ℝ) := by exact_mod_cast SC_pos.le
  nlinarith [norm_nonneg (((SC : ℝ) : ℂ))]

/-- `‖(x : ℂ) + y·i‖ = SC · ‖spt x y‖`. -/
lemma norm_add_mul_I (x y : ℤ) :
    ‖((x : ℝ) + (y : ℝ) * Complex.I)‖ = ‖spt x y‖ * (SC : ℝ) := by
  rw [← spt_mul_SC x y, norm_mul, norm_SC_complex]

/-- The real part of `spt x y` is bounded by its norm. -/
lemma abs_re_le_SC_mul_norm_spt (x y : ℤ) : |(x : ℝ)| ≤ (SC : ℝ) * ‖spt x y‖ := by
  have h3 := Complex.abs_re_le_norm ((x : ℝ) + (y : ℝ) * Complex.I)
  rw [norm_add_mul_I] at h3
  simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im, Complex.I_re,
    zero_mul, sub_zero] at h3
  rw [mul_comm] at h3 ⊢
  simpa using h3

/-- The imaginary part of `spt x y` is bounded by its norm. -/
lemma abs_im_le_SC_mul_norm_spt (x y : ℤ) : |(y : ℝ)| ≤ (SC : ℝ) * ‖spt x y‖ := by
  have h3 := Complex.abs_im_le_norm ((x : ℝ) + (y : ℝ) * Complex.I)
  rw [norm_add_mul_I] at h3
  simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re, Complex.I_re,
    Complex.I_im, zero_mul, add_zero] at h3
  rw [mul_comm] at h3 ⊢
  simpa using h3

/-- An integer bounded in modulus (over `ℝ`) by `m` has `natAbs` at most `m`. -/
lemma natAbs_le_of_abs_le_real {n : ℤ} {m : ℕ} (h : |(n : ℝ)| ≤ (m : ℝ)) : n.natAbs ≤ m := by
  have h1 : -((m : ℤ)) ≤ n := by
    have : -(m : ℝ) ≤ (n : ℝ) := (abs_le.mp h).1
    exact_mod_cast this
  have h2 : n ≤ (m : ℤ) := by
    have : (n : ℝ) ≤ (m : ℝ) := (abs_le.mp h).2
    exact_mod_cast this
  omega

theorem SerStepSize {x y e σ : ℤ} {k : ℕ} {px py pe : ℤ} (he : 0 ≤ e) (hσlt : Work.ANum.m2r σ < 1) (hRσ : Work.CNum.srad x y e ≤ Work.ANum.m2r σ) (hpe3 : Work.ANum.m2r pe ≤ 3) (hp5 : ‖Work.CNum.spt x y ^ (k + 1) - Work.CNum.spt px py‖ ≤ Work.ANum.m2r pe) : Int.natAbs (Work.ANum.SC + Work.CNum.snx x y px py) ≤ 2 ^ 34 ∧ Int.natAbs (Work.CNum.sny x y px py) ≤ 2 ^ 34 := by
  have hSCposR : (0 : ℝ) < (SC : ℝ) := SC_posR
  have hSCposZ : (0 : ℤ) < SC := SC_pos
  have hme : (0 : ℝ) ≤ m2r e := by
    show (0 : ℝ) ≤ (e : ℝ) / (SC : ℝ)
    exact div_nonneg (by exact_mod_cast he) hSCposR.le
  -- `‖c‖ ≤ R ≤ m2r σ < 1`
  have hc_le : ‖spt x y‖ ≤ m2r σ := by
    have h1 : ‖spt x y‖ ≤ srad x y e := by
      show ‖spt x y‖ ≤ ‖spt x y‖ + m2r e
      linarith
    linarith
  have hc1 : ‖spt x y‖ ≤ 1 := le_of_lt (lt_of_le_of_lt hc_le hσlt)
  have hpow : ‖spt x y ^ (k + 1)‖ ≤ 1 := by
    rw [norm_pow]
    exact pow_le_one₀ (norm_nonneg (spt x y)) hc1
  -- `‖p‖ ≤ 4`
  have hp4 : ‖spt px py‖ ≤ 4 := by
    have h1 : ‖spt px py‖ ≤ ‖spt px py - spt x y ^ (k + 1)‖ + ‖spt x y ^ (k + 1)‖ := by
      have := norm_add_le (spt px py - spt x y ^ (k + 1)) (spt x y ^ (k + 1))
      rwa [sub_add_cancel] at this
    have h2 : ‖spt px py - spt x y ^ (k + 1)‖ = ‖spt x y ^ (k + 1) - spt px py‖ :=
      norm_sub_rev (spt px py) (spt x y ^ (k + 1))
    rw [h2] at h1
    linarith
  -- coordinate bounds
  have hpx : |(px : ℝ)| ≤ 4 * (SC : ℝ) := by
    have h := abs_re_le_SC_mul_norm_spt px py
    nlinarith [norm_nonneg (spt px py)]
  have hpy : |(py : ℝ)| ≤ 4 * (SC : ℝ) := by
    have h := abs_im_le_SC_mul_norm_spt px py
    nlinarith [norm_nonneg (spt px py)]
  have hx : |(x : ℝ)| ≤ (SC : ℝ) := by
    have h := abs_re_le_SC_mul_norm_spt x y
    nlinarith [norm_nonneg (spt x y)]
  have hy : |(y : ℝ)| ≤ (SC : ℝ) := by
    have h := abs_im_le_SC_mul_norm_spt x y
    nlinarith [norm_nonneg (spt x y)]
  -- products
  have hmul : ∀ a b : ℤ, |(a : ℝ)| ≤ 4 * (SC : ℝ) → |(b : ℝ)| ≤ (SC : ℝ) →
      |(a : ℝ) * (b : ℝ)| ≤ 4 * (SC : ℝ) * (SC : ℝ) := by
    intro a b ha hb
    rw [abs_mul]
    nlinarith [abs_nonneg (a : ℝ), abs_nonneg (b : ℝ), hSCposR]
  have hA : |(((px * x - py * y : ℤ)) : ℝ)| ≤ 8 * (SC : ℝ) * (SC : ℝ) := by
    have hcast : ((px * x - py * y : ℤ) : ℝ) = (px : ℝ) * (x : ℝ) - (py : ℝ) * (y : ℝ) := by
      push_cast; ring
    rw [hcast]
    have h1 := hmul px x hpx hx
    have h2 := hmul py y hpy hy
    have h3 : |(px : ℝ) * (x : ℝ) - (py : ℝ) * (y : ℝ)| ≤
        |(px : ℝ) * (x : ℝ)| + |(py : ℝ) * (y : ℝ)| := by
      have h := abs_add_le ((px : ℝ) * (x : ℝ)) (-((py : ℝ) * (y : ℝ)))
      rw [abs_neg] at h
      exact h
    linarith
  have hB : |(((px * y + py * x : ℤ)) : ℝ)| ≤ 8 * (SC : ℝ) * (SC : ℝ) := by
    have hcast : ((px * y + py * x : ℤ) : ℝ) = (px : ℝ) * (y : ℝ) + (py : ℝ) * (x : ℝ) := by
      push_cast; ring
    rw [hcast]
    have h1 := hmul px y hpx hy
    have h2 := hmul py x hpy hx
    have h3 := abs_add_le ((px : ℝ) * (y : ℝ)) ((py : ℝ) * (x : ℝ))
    linarith
  -- ceiling bounds
  have key : ∀ a : ℤ, |(a : ℝ)| ≤ 8 * (SC : ℝ) * (SC : ℝ) →
      |((( -Int.ediv (-a) SC : ℤ)) : ℝ)| ≤ 8 * (SC : ℝ) + 1 := by
    intro a ha
    have h := ceil_div_abs_le a SC hSCposZ
    have hdiv : |(a : ℝ)| / (SC : ℝ) ≤ 8 * (SC : ℝ) := by
      rw [div_le_iff₀ hSCposR]; linarith
    linarith
  have h34 : (9 * (SC : ℝ) + 1) ≤ ((2 ^ 34 : ℕ) : ℝ) := by norm_num [SC]
  have h8 : (8 * (SC : ℝ) + 1) ≤ ((2 ^ 34 : ℕ) : ℝ) := by linarith [h34]
  constructor
  · have hsnx : |((snx x y px py : ℤ) : ℝ)| ≤ 8 * (SC : ℝ) + 1 := by
      show |((( -Int.ediv (-(px * x - py * y)) SC : ℤ)) : ℝ)| ≤ _
      exact key (px * x - py * y) hA
    have h1 : |(((SC + snx x y px py : ℤ)) : ℝ)| ≤ 9 * (SC : ℝ) + 1 := by
      rw [show ((SC + snx x y px py : ℤ) : ℝ) = (SC : ℝ) + ((snx x y px py : ℤ) : ℝ) by
        push_cast; ring]
      have h2 := abs_add_le (SC : ℝ) ((snx x y px py : ℤ) : ℝ)
      rw [abs_of_pos hSCposR] at h2
      linarith
    exact natAbs_le_of_abs_le_real (le_trans h1 h34)
  · have hsny : |((sny x y px py : ℤ) : ℝ)| ≤ 8 * (SC : ℝ) + 1 := by
      show |((( -Int.ediv (-(px * y + py * x)) SC : ℤ)) : ℝ)| ≤ _
      exact key (px * y + py * x) hB
    exact natAbs_le_of_abs_le_real (le_trans hsny h8)

end Work.CNum
