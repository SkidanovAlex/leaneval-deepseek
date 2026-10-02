import Mathlib

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.Normal

/-- For every real `a` there is an integer `k` with `|a - 2πk| ≤ π`. -/
lemma cosint_exists_int_close_two_pi (a : ℝ) :
    ∃ k : ℤ, |a - (k : ℝ) * (2 * Real.pi)| ≤ Real.pi := by
  refine ⟨⌊a / (2 * Real.pi) + 1 / 2⌋, ?_⟩
  have hpi : (0 : ℝ) < 2 * Real.pi := by positivity
  have hk : |a / (2 * Real.pi) - ((⌊a / (2 * Real.pi) + 1 / 2⌋ : ℤ) : ℝ)| ≤ 1 / 2 := by
    have h1 : ((⌊a / (2 * Real.pi) + 1 / 2⌋ : ℤ) : ℝ) ≤ a / (2 * Real.pi) + 1 / 2 :=
      Int.floor_le _
    have h2 : a / (2 * Real.pi) + 1 / 2 < ((⌊a / (2 * Real.pi) + 1 / 2⌋ : ℤ) : ℝ) + 1 :=
      Int.lt_floor_add_one _
    rw [abs_le]
    constructor <;> linarith
  have hfac : a - ((⌊a / (2 * Real.pi) + 1 / 2⌋ : ℤ) : ℝ) * (2 * Real.pi)
      = (a / (2 * Real.pi) - ((⌊a / (2 * Real.pi) + 1 / 2⌋ : ℤ) : ℝ)) * (2 * Real.pi) := by
    rw [sub_mul, div_mul_cancel₀ _ (ne_of_gt hpi)]
  rw [hfac, abs_mul, abs_of_pos hpi]
  calc |a / (2 * Real.pi) - ((⌊a / (2 * Real.pi) + 1 / 2⌋ : ℤ) : ℝ)| * (2 * Real.pi)
      ≤ (1 / 2) * (2 * Real.pi) := mul_le_mul_of_nonneg_right hk (le_of_lt hpi)
    _ = Real.pi := by ring

/-- `2 ≤ cosh 2`. -/
lemma cosint_cosh_two_ge_two : (2 : ℝ) ≤ Real.cosh 2 := by
  have hexp : (4 : ℝ) < Real.exp 2 := by
    rw [show (2 : ℝ) = 1 + 1 by norm_num, Real.exp_add]
    nlinarith [Real.exp_one_gt_d9, Real.exp_pos 1]
  rw [Real.cosh_eq]
  have := Real.exp_pos (-2)
  linarith

/-- For `t ≥ 0` one has `cosh t + 1 ≤ cosh (t + 2)`. -/
lemma cosint_cosh_add_two_ge (t : ℝ) (ht : 0 ≤ t) : Real.cosh t + 1 ≤ Real.cosh (t + 2) := by
  rw [Real.cosh_add]
  have hsinh : 0 ≤ Real.sinh t * Real.sinh 2 :=
    mul_nonneg (Real.sinh_nonneg_iff.mpr ht) (Real.sinh_nonneg_iff.mpr (by norm_num))
  have hc : 1 ≤ Real.cosh t := Real.one_le_cosh t
  nlinarith [hsinh, hc, cosint_cosh_two_ge_two, Real.cosh_pos t]

/-- For `t ≥ 0`, the number `arcosh ⌈cosh t⌉` lies in `[t, t+2]`. -/
lemma cosint_arcosh_ceil_cosh_bounds (t : ℝ) (ht : 0 ≤ t) :
    t ≤ Real.arcosh (Nat.ceil (Real.cosh t)) ∧
      Real.arcosh (Nat.ceil (Real.cosh t)) ≤ t + 2 := by
  have hcpos : 0 < Real.cosh t := Real.cosh_pos t
  have hNpos : (0 : ℝ) < ((Nat.ceil (Real.cosh t) : ℕ) : ℝ) := by
    have h1 := Nat.le_ceil (Real.cosh t)
    have h2 := Real.cosh_pos t
    linarith
  constructor
  · calc t = Real.arcosh (Real.cosh t) := (Real.arcosh_cosh ht).symm
      _ ≤ Real.arcosh ((Nat.ceil (Real.cosh t) : ℕ) : ℝ) :=
          (Real.arcosh_le_arcosh hcpos hNpos).mpr (Nat.le_ceil _)
  · have hlt := Nat.ceil_lt_add_one (le_of_lt hcpos)
    have hle := cosint_cosh_add_two_ge t ht
    have hkey : ((Nat.ceil (Real.cosh t) : ℕ) : ℝ) ≤ Real.cosh (t + 2) := by linarith
    calc Real.arcosh ((Nat.ceil (Real.cosh t) : ℕ) : ℝ)
        ≤ Real.arcosh (Real.cosh (t + 2)) :=
          (Real.arcosh_le_arcosh hNpos (Real.cosh_pos _)).mpr hkey
      _ = t + 2 := Real.arcosh_cosh (by linarith)

/-- For `t ≥ 0` there is a positive integer `N` with `|arcosh N - t| ≤ 2`. -/
lemma cosint_exists_nat_arcosh_close (t : ℝ) (ht : 0 ≤ t) :
    ∃ N : ℕ, 1 ≤ N ∧ |Real.arcosh N - t| ≤ 2 := by
  refine ⟨Nat.ceil (Real.cosh t), ?_, ?_⟩
  · have h : (1 : ℝ) ≤ ((Nat.ceil (Real.cosh t) : ℕ) : ℝ) := by
      have := Nat.le_ceil (Real.cosh t)
      have := Real.one_le_cosh t
      linarith
    exact_mod_cast h
  · have hb := cosint_arcosh_ceil_cosh_bounds t ht
    rw [abs_le]
    constructor <;> linarith [hb.1, hb.2]

theorem exists_cos_eq_int_of_ball (c : ℂ) {ρ : ℝ} (hρ : 4 < ρ) :
    ∃ w : ℂ, w ∈ Metric.ball c ρ ∧ ∃ n : ℤ, Complex.cos w = (n : ℂ) := by
  obtain ⟨k, hk⟩ := cosint_exists_int_close_two_pi c.re
  obtain ⟨N, hN1, hN2⟩ := cosint_exists_nat_arcosh_close |c.im| (abs_nonneg c.im)
  have hNpos : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN1
  set y : ℝ := if 0 ≤ c.im then (Real.arcosh N : ℝ) else -(Real.arcosh N : ℝ) with hy
  have hcoshy : Real.cosh y = (N : ℝ) := by
    rw [hy]
    split_ifs with h
    · exact Real.cosh_arcosh hNpos
    · rw [Real.cosh_neg]; exact Real.cosh_arcosh hNpos
  have hy_abs : |y - c.im| = abs (Real.arcosh N - |c.im|) := by
    rw [hy]
    split_ifs with h
    · rw [abs_of_nonneg h]
    · rw [abs_of_neg (not_le.mp h)]
      have hsq : -Real.arcosh N - c.im = -(Real.arcosh N + c.im) := by ring
      rw [hsq, abs_neg]
      congr 1
      ring
  set w : ℂ := (k : ℂ) * ((2 : ℝ) * Real.pi) + (y : ℂ) * Complex.I with hw
  have hcosw : Complex.cos w = ((N : ℤ) : ℂ) := by
    rw [hw]
    have harg : (k : ℂ) * ((2 : ℝ) * Real.pi) + (y : ℂ) * Complex.I
        = (y : ℂ) * Complex.I + ((k : ℤ) : ℂ) * (2 * ↑Real.pi) := by push_cast; ring
    rw [harg, Complex.cos_add_int_mul_two_pi, Complex.cos_mul_I, ← Complex.ofReal_cosh,
      hcoshy]
    simp
  have hmem : w ∈ Metric.ball c ρ := by
    rw [Metric.mem_ball, Complex.dist_eq]
    have hDre : (w - c).re = (k : ℝ) * (2 * Real.pi) - c.re := by
      rw [hw]
      simp only [Complex.sub_re, Complex.add_re, Complex.mul_re,
        Complex.ofReal_re, Complex.ofReal_im, Complex.intCast_re, Complex.intCast_im,
        Complex.I_re, Complex.I_im, mul_zero, mul_one, sub_zero, zero_mul, add_zero]
    have hDim : (w - c).im = y - c.im := by
      rw [hw]
      simp only [Complex.sub_im, Complex.add_im, Complex.mul_im,
        Complex.ofReal_re, Complex.ofReal_im, Complex.intCast_re, Complex.intCast_im,
        Complex.I_re, Complex.I_im, mul_zero, mul_one, zero_mul, add_zero]
      ring
    have hnormsq : Complex.normSq (w - c)
        = ((k : ℝ) * (2 * Real.pi) - c.re) ^ 2 + (y - c.im) ^ 2 := by
      rw [Complex.normSq_apply, hDre, hDim]
      ring
    have hbnd : Complex.normSq (w - c) < ρ ^ 2 := by
      rw [hnormsq]
      have h1 : ((k : ℝ) * (2 * Real.pi) - c.re) ^ 2 ≤ Real.pi ^ 2 := by
        have h := abs_le.mp hk
        rw [sq_le_sq, abs_of_pos Real.pi_pos]
        rw [abs_le]
        exact ⟨by linarith [h.2], by linarith [h.1]⟩
      have h2 : (y - c.im) ^ 2 ≤ 4 := by
        rw [← sq_abs, hy_abs]
        nlinarith [hN2, abs_nonneg (Real.arcosh N - |c.im|)]
      have hpi2 : Real.pi ^ 2 + 4 < ρ ^ 2 := by
        nlinarith [Real.pi_lt_d2, Real.pi_pos, hρ]
      linarith
    have h4 : ‖w - c‖ ^ 2 < ρ ^ 2 := by
      rw [← Complex.normSq_eq_norm_sq]
      exact hbnd
    nlinarith [norm_nonneg (w - c), hρ]
  exact ⟨w, hmem, ⟨(N : ℤ), hcosw⟩⟩

end Work.Normal
