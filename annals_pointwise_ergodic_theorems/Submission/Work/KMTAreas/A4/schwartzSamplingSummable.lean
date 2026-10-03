/-
# Summability of a Schwartz function sampled on an arithmetic progression

For a Schwartz function `φ : ℝ → ℂ`, a shift `a : ℝ` and a step `c ≠ 0`, the series

  `∑_{n : ℤ} ‖φ (a + c * n)‖`

converges.

The proof has the two standard ingredients:

* the Schwartz decay bound `‖φ y‖ ≤ C / |y| ^ 2` for `|y| ≥ 1` (one Schwartz seminorm
  controls it), and
* the summability of the shifted `p`-series `∑_{n : ℤ} 1 / |x + n| ^ 2` (Mathlib's
  `Real.summable_one_div_int_add_rpow`), which by the scaling `a + c n = c (n + a/c)`
  gives the summable comparison series `∑_n 1 / |a + c n| ^ 2`.

The decay bound is available only away from `0`, i.e. for all but finitely many `n`
(those `n` with `|a + c n| < 1` form a finite set, since `n` is then bounded by
`(1 + |a|)/|c|`); summability is insensitive to finitely many terms
(`Summable.of_norm_bounded_eventually`, along the cofinite filter).
-/
import Mathlib

namespace Work.KMTAreas.A4

open Filter

/-- For a positive real exponent written as the literal `2`, `x ^ (2 : ℝ) = x ^ 2`
(natural power).  Used to pass between the real-power form of the Schwartz decay
bound and the natural-power form of the comparison series. -/
lemma rpow_two_real (x : ℝ) : x ^ (2 : ℝ) = x ^ 2 := by
  rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]

/-- Purely algebraic identity used to compare the scaled `p`-series with `1 / |a + c n| ^ 2`;
it holds unconditionally because division by zero is `0` in a field. -/
lemma div_mul_div_one_eq (C X Y : ℝ) : (C / X) * (1 / Y) = C * (1 / (X * Y)) := by
  rw [div_mul_div_comm, mul_one, div_eq_mul_one_div]

/-- Schwartz decay in the form needed for the sampled series: there is `C` with
`‖φ y‖ ≤ C / |y| ^ 2` for every `y` with `|y| ≥ 1`. -/
lemma schwartz_decay_inv_sq (φ : SchwartzMap ℝ ℂ) :
    ∃ C : ℝ, 0 < C ∧ ∀ y : ℝ, 1 ≤ |y| → ‖φ y‖ ≤ C * (1 / |y| ^ (2 : ℝ)) := by
  obtain ⟨C, hCpos, hC⟩ := φ.decay 2 0
  simp only [norm_iteratedFDeriv_zero, Real.norm_eq_abs] at hC
  refine ⟨C, hCpos, fun y hy => ?_⟩
  have hy1 : 0 < |y| := lt_of_lt_of_le one_pos hy
  have hy2 : 0 < |y| ^ (2 : ℝ) := Real.rpow_pos_of_pos hy1 2
  rw [mul_one_div, le_div_iff₀ hy2]
  calc ‖φ y‖ * |y| ^ (2 : ℝ) = |y| ^ 2 * ‖φ y‖ := by rw [rpow_two_real]; ring
    _ ≤ C := hC y

/-- The set of integers `n` with `|a + c * n| ≥ 1` is cofinite when `c ≠ 0`: indeed
`|a + c n| < 1` forces `|n| < (1 + |a|) / |c|`, so the exceptional set is contained in an
integer interval. -/
lemma finite_int_near_scaled (a c : ℝ) (hc : c ≠ 0) :
    {n : ℤ | ¬ (1 ≤ |a + c * (n : ℝ)|)}.Finite := by
  have hcpos : 0 < |c| := abs_pos.mpr hc
  set M : ℝ := (1 + |a|) / |c| with hMdef
  refine (Set.finite_Icc (-⌈M⌉ : ℤ) ⌈M⌉).subset ?_
  intro n hn
  have hlt : |a + c * (n : ℝ)| < 1 := lt_of_not_ge hn
  have hb : |(n : ℝ)| < M := by
    have hmul : |c * (n : ℝ)| = |c| * |(n : ℝ)| := by rw [abs_mul]
    have h2 : |c * (n : ℝ)| ≤ |a + c * (n : ℝ)| + |a| := by
      have h : |c * (n : ℝ)| = |a + c * (n : ℝ) - a| := by
        rw [show a + c * (n : ℝ) - a = c * (n : ℝ) from by ring]
      rw [h]
      exact abs_sub (a + c * (n : ℝ)) a
    have h3 : |c| * |(n : ℝ)| < 1 + |a| := by rw [hmul] at h2; linarith
    rw [hMdef, lt_div_iff₀ hcpos]
    linarith
  obtain ⟨hlo, hhi⟩ := abs_lt.mp hb
  have hceil : (M : ℝ) ≤ ((⌈M⌉ : ℤ) : ℝ) := Int.le_ceil M
  rw [Set.mem_Icc]
  constructor
  · have h : ((-⌈M⌉ : ℤ) : ℝ) ≤ (n : ℝ) := by
      push_cast
      linarith
    exact_mod_cast h
  · have h : (n : ℝ) ≤ ((⌈M⌉ : ℤ) : ℝ) := by linarith
    exact_mod_cast h

theorem schwartzSamplingSummable (φ : SchwartzMap ℝ ℂ) {c a : ℝ} (hc : c ≠ 0) :
    Summable (fun n : ℤ => ‖φ (a + c * (n : ℝ))‖) := by
  obtain ⟨C, hCpos, hCdecay⟩ := schwartz_decay_inv_sq φ
  -- the decay bound applies for all but finitely many `n`
  have hev : ∀ᶠ n : ℤ in Filter.cofinite, 1 ≤ |a + c * (n : ℝ)| :=
    Filter.eventually_cofinite.mpr (finite_int_near_scaled a c hc)
  -- the comparison series: after rescaling it is Mathlib's shifted p-series at exponent 2
  have hcomp : Summable (fun n : ℤ => C * (1 / |a + c * (n : ℝ)| ^ (2 : ℝ))) := by
    have hshift : Summable (fun n : ℤ => 1 / |(n : ℝ) + a / c| ^ (2 : ℝ)) :=
      (Real.summable_one_div_int_add_rpow (a / c) 2).mpr one_lt_two
    have hconst : Summable (fun n : ℤ =>
        (C / |c| ^ (2 : ℝ)) * (1 / |(n : ℝ) + a / c| ^ (2 : ℝ))) := hshift.mul_left _
    refine hconst.congr (fun n => ?_)
    have harg : |a + c * (n : ℝ)| = |c| * |(n : ℝ) + a / c| := by
      rw [show a + c * (n : ℝ) = c * ((n : ℝ) + a / c) from by
        rw [mul_add, mul_div_cancel₀ a hc]; ring]
      rw [abs_mul]
    rw [harg, Real.mul_rpow (abs_nonneg c) (abs_nonneg _)]
    exact div_mul_div_one_eq C _ _
  refine Summable.of_norm_bounded_eventually hcomp ?_
  filter_upwards [hev] with n hn
  simpa using hCdecay (a + c * (n : ℝ)) hn

end Work.KMTAreas.A4
