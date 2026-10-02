/-
# The single-zero contribution to `winSum`

`Work.LinnikAreas.DhRepel.winSum χ s δ` is the windowed sum of `Re (1/(s-ρ))` over the zeros `ρ`
of the completed `L`-function `Λ(·,χ)` lying within distance `δ` of the point `1 + i·Im s`.

This file records the trivial-but-essential lower bound: *any single* such zero already
contributes at least its own term to the sum.  Concretely, if `u` is a zero of `L(·,χ)` (with
`0 < Re u`, so by the theory of the completed `L`-function it is a zero of `Λ(·,χ)` inside the
critical strip) with `Im u = Im s`, and `‖1 + i·Im s - u‖ ≤ δ`, then

`1/(Re s - Re u) ≤ winSum χ s δ`.

Indeed `Re s > 1 > Re u` shows that `1/(s - u)` is a positive real number equal to
`1/(Re s - Re u)`, the multiplicity of `u` as a zero of `Λ(·,χ)` is at least `1`, and every
summand of `winSum` is non-negative.

The only ingredients are: the completed `L`-function vanishes wherever `L` does; its zeros in
the strip have positive real part (`completedL_zero_strip`); a zero of an analytic function
inside the ball has non-zero divisor (`divisor_ne_zero_of_analytic_eq_zero`, proved here); and the
pointwise non-negativity of the summands of `winSum`.
-/
import Mathlib
import Submission.Work.LinnikContract.Defs
import Submission.Work.LinnikAreas.OtherCharRepel.completedLFunction_analyticOrderAt_ne_top
import Submission.Work.LinnikAreas.DhRepel.l52Hyp_supply

open Complex DirichletCharacter Metric
open scoped Real Topology BigOperators
noncomputable section

namespace Work.LinnikAreas.OtherCharRepel

/-- If an analytic function on a closed ball vanishes at an interior point where its vanishing
order is finite, then the divisor of the function on that ball does not vanish there. -/
private lemma divisor_ne_zero_of_analytic_eq_zero {f : ℂ → ℂ} {a : ℂ} {ρ : ℝ}
    (hf : AnalyticOnNhd ℂ f (Metric.closedBall a ρ)) {u : ℂ}
    (hu : u ∈ Metric.closedBall a ρ) (hz : f u = 0) (htop : analyticOrderAt f u ≠ ⊤) :
    (MeromorphicOn.divisor f (Metric.closedBall a ρ)) u ≠ 0 := by
  rw [MeromorphicOn.AnalyticOnNhd.divisor_apply hf hu]
  have hne0 : analyticOrderAt f u ≠ 0 := by
    intro h
    rcases (analyticOrderAt_eq_zero).mp h with hna | hne
    · exact hna (hf u hu)
    · exact hne hz
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp htop
  rw [← hn] at hne0 ⊢
  simp only [ENat.map_natCast, WithTop.untop₀_coe]
  have hn0 : n ≠ 0 := WithTop.coe_ne_zero.mp hne0
  simpa using hn0

/-- If `u` and `s` have the same imaginary part then `s - u` is the real number
`Re s - Re u`. -/
private lemma sub_eq_ofReal_of_im_eq {s u : ℂ} (h : u.im = s.im) :
    s - u = ((s.re - u.re : ℝ) : ℂ) := by
  apply Complex.ext
  · simp [Complex.sub_re]
  · simp [Complex.sub_im, h]

/-- For `u` and `s` with the same imaginary part, `Re (1/(s-u)) = 1/(Re s - Re u)`. -/
private lemma re_one_div_sub {s u : ℂ} (h : u.im = s.im) :
    (1/(s-u)).re = 1/(s.re - u.re) := by
  rw [sub_eq_ofReal_of_im_eq h, one_div, one_div, ← Complex.ofReal_inv, Complex.ofReal_re]

theorem one_div_le_winSum {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1)
    (hχprim : χ.IsPrimitive) {s u : ℂ} {δ : ℝ} (hs : 1 < s.re)
    (hu : DirichletCharacter.LFunction χ u = 0) (hum : u.im = s.im) (hure : 0 < u.re)
    (hwin : ‖(1 : ℂ) + (s.im : ℂ) * Complex.I - u‖ ≤ δ) :
    1 / (s.re - u.re) ≤ Work.LinnikAreas.DhRepel.winSum χ s δ := by
  classical
  -- `u ≠ 0`, so the relation between `L` and `Λ` applies at `u`
  have hu_ne : u ≠ 0 := by
    intro h0
    rw [h0] at hure
    simp at hure
  -- `u` is a zero of the completed `L`-function as well
  have hc : DirichletCharacter.completedLFunction χ u = 0 := by
    have hrel := DirichletCharacter.LFunction_eq_completed_div_gammaFactor χ u (Or.inl hu_ne)
    have hg : χ.gammaFactor u ≠ 0 := by
      rcases χ.even_or_odd with h | h
      · rw [h.gammaFactor_def]
        exact Gammaℝ_ne_zero_of_re_pos (by simpa using hure)
      · rw [h.gammaFactor_def]
        exact Gammaℝ_ne_zero_of_re_pos (by simp only [Complex.add_re, Complex.one_re]; linarith)
    have h0 : DirichletCharacter.completedLFunction χ u / χ.gammaFactor u = 0 := by
      rw [← hrel]; exact hu
    exact (div_eq_zero_iff).mp h0 |>.resolve_right hg
  -- zeros of `Λ` lie in the critical strip, so `Re u < 1`
  obtain ⟨hu_pos, hu_lt1⟩ := Commons.NumberTheory.Linnik.completedL_zero_strip χ hχ hχprim hc
  -- hence `u` lies in the divisor ball of radius `|Im s| + 2`
  have hmem : u ∈ Metric.closedBall (0 : ℂ) (|s.im| + 2) := by
    rw [Metric.mem_closedBall, dist_zero_right]
    have h1 : ‖u‖ ≤ |u.re| + |u.im| := Complex.norm_le_abs_re_add_abs_im u
    rw [abs_of_pos hure, hum] at h1
    linarith
  have hf_an : AnalyticOnNhd ℂ (DirichletCharacter.completedLFunction χ)
      (Metric.closedBall (0:ℂ) (|s.im| + 2)) :=
    fun z _ => (DirichletCharacter.differentiable_completedLFunction hχ).analyticAt z
  -- the multiplicity of `u` is non-zero
  have hdu : (MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
      (Metric.closedBall (0:ℂ) (|s.im| + 2))) u ≠ 0 :=
    divisor_ne_zero_of_analytic_eq_zero hf_an hmem hc
      (completedLFunction_analyticOrderAt_ne_top χ hχ u)
  -- the summand of `winSum`
  set W : ℂ → ℝ := fun v =>
    ((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
        (Metric.closedBall (0:ℂ) (|s.im| + 2))) v : ℤ) *
      (if ‖(1:ℂ) + (s.im : ℂ) * Complex.I - v‖ ≤ δ then ((1/(s-v)).re) else 0) with hW
  have hWsum : (∑ᶠ v : ℂ, W v) = Work.LinnikAreas.DhRepel.winSum χ s δ := by
    rw [hW]; rfl
  -- its value at `u`
  have hWu : W u =
      ((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
        (Metric.closedBall (0:ℂ) (|s.im| + 2))) u : ℝ) * (1/(s.re - u.re)) := by
    rw [hW]; dsimp only
    rw [if_pos hwin, re_one_div_sub hum]
  -- the multiplicity at `u` is at least one
  have hdu_ge : (1:ℝ) ≤ ((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
      (Metric.closedBall (0:ℂ) (|s.im| + 2))) u : ℝ) := by
    have h0 : (0:ℝ) ≤ ((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
        (Metric.closedBall (0:ℂ) (|s.im| + 2))) u : ℝ) :=
      Work.LinnikAreas.DhRepel.divisor_nonneg χ hχ (|s.im| + 2) u
    have h0' : (0:ℤ) ≤ (MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
        (Metric.closedBall (0:ℂ) (|s.im| + 2))) u := by exact_mod_cast h0
    have h1' : (1:ℤ) ≤ (MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
        (Metric.closedBall (0:ℂ) (|s.im| + 2))) u := by omega
    exact_mod_cast h1'
  have hXpos : 0 < 1/(s.re - u.re) := by
    apply one_div_pos.mpr; linarith
  have hterm : 1/(s.re - u.re) ≤ W u := by
    rw [hWu]
    have := mul_le_mul_of_nonneg_right hdu_ge (le_of_lt hXpos)
    simpa using this
  -- every summand is non-negative
  have hWnonneg : ∀ v, 0 ≤ W v := by
    intro v
    rw [hW]; dsimp only
    by_cases hdv : (MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
        (Metric.closedBall (0:ℂ) (|s.im| + 2))) v = 0
    · rw [hdv]; simp
    · have hkern : 0 ≤ (1/(s-v)).re :=
        Work.LinnikAreas.DhRepel.kernel_first_nonneg χ hχ hχprim hs hdv
      have hdn : 0 ≤ ((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
          (Metric.closedBall (0:ℂ) (|s.im| + 2))) v : ℝ) :=
        Work.LinnikAreas.DhRepel.divisor_nonneg χ hχ (|s.im| + 2) v
      have hif : 0 ≤ (if ‖(1:ℂ) + (s.im : ℂ) * Complex.I - v‖ ≤ δ then ((1/(s-v)).re) else 0) := by
        split_ifs with h
        · exact hkern
        · exact le_refl 0
      exact mul_nonneg hdn hif
  have hfs : Function.HasFiniteSupport W := by
    rw [hW]
    exact Work.LinnikAreas.DhRepel.finiteSupport_window χ hχ
  have hsum := single_le_finsum u hfs hWnonneg
  rw [hWsum] at hsum
  exact le_trans hterm hsum

end Work.LinnikAreas.OtherCharRepel
