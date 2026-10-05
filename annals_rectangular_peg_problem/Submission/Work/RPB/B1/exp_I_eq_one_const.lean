import Mathlib

namespace Work.RPB.B1

/-- If `|k * 2π| < π` for an integer `k`, then `k = 0`. -/
private lemma int_cast_mul_two_pi_eq_zero {k : ℤ}
    (h : |(k : ℝ) * (2 * Real.pi)| < Real.pi) : k = 0 := by
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  rcases lt_trichotomy k 0 with hk | hk | hk
  · have hk1 : (k : ℝ) ≤ -1 := by
      have : k ≤ -1 := by omega
      exact_mod_cast this
    have hle : (k : ℝ) * (2 * Real.pi) ≤ -2 * Real.pi := by nlinarith
    have hlt := (abs_lt.mp h).1
    nlinarith
  · exact hk
  · have hk1 : (1 : ℝ) ≤ (k : ℝ) := by
      have : (1 : ℤ) ≤ k := by omega
      exact_mod_cast this
    have hle : 2 * Real.pi ≤ (k : ℝ) * (2 * Real.pi) := by nlinarith
    have hlt := (abs_lt.mp h).2
    nlinarith

/-- If a continuous real-valued function `ψ` satisfies `exp (ψ s * I) = 1` for all `s`,
then `ψ` is constant. Indeed every value of `ψ` is an integer multiple of `2π`, so `ψ` is
locally constant; since `ℝ` is preconnected it is globally constant. -/
theorem exp_I_eq_one_const {ψ : ℝ → ℝ} (hψ : Continuous ψ)
    (h : ∀ s, Complex.exp ((ψ s : ℂ) * Complex.I) = 1) : ∀ s, ψ s = ψ 0 := by
  -- Every value of `ψ` is an integer multiple of `2 * π`.
  have hmem : ∀ s, ∃ n : ℤ, ψ s = (n : ℝ) * (2 * Real.pi) := by
    intro s
    obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.mp (h s)
    refine ⟨n, ?_⟩
    have h2 : (ψ s : ℂ) * Complex.I = ((n : ℂ) * (2 * Real.pi)) * Complex.I := by
      rw [hn]; ring
    have h3 : (ψ s : ℂ) = (n : ℂ) * (2 * Real.pi) :=
      mul_right_cancel₀ Complex.I_ne_zero h2
    have h4 : (ψ s : ℂ) = (((n : ℝ) * (2 * Real.pi) : ℝ) : ℂ) := by
      rw [h3]; push_cast; ring
    exact Complex.ofReal_injective h4
  -- Hence `ψ` is locally constant: on a ball of radius where `ψ t` is within `π` of `ψ s`,
  -- the difference `ψ t - ψ s` is an integer multiple of `2π` of absolute value `< π`.
  have hloc : IsLocallyConstant ψ := by
    rw [IsLocallyConstant.iff_exists_open ψ]
    intro s
    obtain ⟨m, hm⟩ := hmem s
    obtain ⟨δ, hδpos, hδ⟩ :=
      (Metric.continuousAt_iff.mp (hψ.continuousAt (x := s))) Real.pi Real.pi_pos
    refine ⟨Metric.ball s δ, Metric.isOpen_ball, Metric.mem_ball_self hδpos, ?_⟩
    intro t ht
    obtain ⟨n, hn⟩ := hmem t
    have ht' : dist t s < δ := ht
    have hdist : |ψ t - ψ s| < Real.pi := by
      have := hδ ht'
      rwa [Real.dist_eq] at this
    have hkey : |((n - m : ℤ) : ℝ) * (2 * Real.pi)| < Real.pi := by
      have hdiff : ψ t - ψ s = ((n - m : ℤ) : ℝ) * (2 * Real.pi) := by
        rw [hn, hm]; push_cast; ring
      rwa [hdiff] at hdist
    have hzero : n - m = 0 := int_cast_mul_two_pi_eq_zero hkey
    have hnm : n = m := by omega
    rw [hn, hm, hnm]
  -- A locally constant function on the preconnected space `ℝ` is constant.
  intro s
  exact hloc.apply_eq_of_preconnectedSpace s 0

end Work.RPB.B1
