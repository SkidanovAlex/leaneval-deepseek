import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.SmoothTransition

namespace Commons.Analysis.Calculus

/-- Chain rule for an affine rescaling of `Real.smoothTransition`:
the `a`-th derivative picks up a factor `c ^ a`. -/
lemma iteratedDeriv_smoothTransition_comp (a : ℕ) (c t : ℝ) :
    iteratedDeriv a (fun s : ℝ => Real.smoothTransition (c * s - 1)) t
      = c ^ a * iteratedDeriv a Real.smoothTransition (c * t - 1) := by
  have hf : ContDiff ℝ (a : ℕ∞) (fun z : ℝ => Real.smoothTransition (z - 1)) :=
    Real.smoothTransition.contDiff.comp (contDiff_id.sub contDiff_const)
  have hchain := congrFun (iteratedDeriv_comp_const_mul (n := a) hf c) t
  have hshift := congrFun
    (iteratedDeriv_comp_sub_const (n := a) (f := Real.smoothTransition) (s := 1)) (c * t)
  rw [hchain, hshift]

/-- For `a ≥ 1`, the `a`-th derivative of `Real.smoothTransition` vanishes on `(-∞,0)`. -/
lemma iteratedDeriv_succ_smoothTransition_eq_zero_of_neg (b : ℕ) {x : ℝ} (hx : x < 0) :
    iteratedDeriv (b + 1) Real.smoothTransition x = 0 := by
  have hfg : Set.EqOn Real.smoothTransition (fun _ : ℝ => 0) (Set.Iio 0) :=
    fun y hy => Real.smoothTransition.zero_of_nonpos hy.le
  have h := Set.EqOn.iteratedDeriv_of_isOpen hfg isOpen_Iio (b + 1)
  rw [h hx]
  simp

/-- For `a ≥ 1`, the `a`-th derivative of `Real.smoothTransition` vanishes on `(1,∞)`. -/
lemma iteratedDeriv_succ_smoothTransition_eq_zero_of_one_lt (b : ℕ) {x : ℝ} (hx : 1 < x) :
    iteratedDeriv (b + 1) Real.smoothTransition x = 0 := by
  have hfg : Set.EqOn Real.smoothTransition (fun _ : ℝ => 1) (Set.Ioi 1) :=
    fun y hy => Real.smoothTransition.one_of_one_le hy.le
  have h := Set.EqOn.iteratedDeriv_of_isOpen hfg isOpen_Ioi (b + 1)
  rw [h hx, iteratedDeriv_const]
  simp

/-- A uniform bound on the `(b+1)`-st derivative of `Real.smoothTransition` on all of `ℝ`. -/
lemma exists_pos_abs_iteratedDeriv_succ_smoothTransition_bound (b : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ, |iteratedDeriv (b + 1) Real.smoothTransition x| ≤ C := by
  have hcont : Continuous (iteratedDeriv (b + 1) Real.smoothTransition) := by
    have h : ContDiff ℝ ((b + 1 : ℕ) : WithTop ℕ∞) Real.smoothTransition :=
      Real.smoothTransition.contDiff
    exact h.continuous_iteratedDeriv (b + 1) le_rfl
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn hcont.continuousOn
  refine ⟨max M 1, lt_max_of_lt_right zero_lt_one, fun x => ?_⟩
  by_cases hx : x ∈ Set.Icc (0 : ℝ) 1
  · have hx' : |iteratedDeriv (b + 1) Real.smoothTransition x| ≤ M := by
      simpa [Real.norm_eq_abs] using hM x hx
    exact hx'.trans (le_max_left _ _)
  · rw [Set.mem_Icc, not_and_or] at hx
    push Not at hx
    rcases hx with hx | hx
    · rw [iteratedDeriv_succ_smoothTransition_eq_zero_of_neg b hx, abs_zero]
      exact le_of_lt (lt_max_of_lt_right zero_lt_one)
    · rw [iteratedDeriv_succ_smoothTransition_eq_zero_of_one_lt b hx, abs_zero]
      exact le_of_lt (lt_max_of_lt_right zero_lt_one)

/-- **Derivative bounds for a rescaled cutoff.**  For each `a` the `a`-th derivative of
`x ↦ smoothTransition (c * x - 1)` is bounded by a constant (depending only on `a`) times `c ^ a`. -/
theorem iteratedDeriv_smoothTransition_scale_bound (a : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (c : ℝ), 0 < c → ∀ t : ℝ,
      |iteratedDeriv a (fun s : ℝ => Real.smoothTransition (c * s - 1)) t| ≤ C * c ^ a := by
  cases a with
  | zero =>
    refine ⟨1, one_pos, fun c _ t => ?_⟩
    rw [iteratedDeriv_smoothTransition_comp]
    simp only [iteratedDeriv_zero, pow_zero, one_mul]
    rw [abs_le]
    exact ⟨by linarith [Real.smoothTransition.nonneg (c * t - 1)], Real.smoothTransition.le_one _⟩
  | succ b =>
    obtain ⟨C, hCpos, hC⟩ := exists_pos_abs_iteratedDeriv_succ_smoothTransition_bound b
    refine ⟨C, hCpos, fun c hc t => ?_⟩
    rw [iteratedDeriv_smoothTransition_comp]
    rw [abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ c ^ (b + 1))]
    calc c ^ (b + 1) * |iteratedDeriv (b + 1) Real.smoothTransition (c * t - 1)|
        ≤ c ^ (b + 1) * C := mul_le_mul_of_nonneg_left (hC (c * t - 1)) (by positivity)
      _ = C * c ^ (b + 1) := by ring

end Commons.Analysis.Calculus