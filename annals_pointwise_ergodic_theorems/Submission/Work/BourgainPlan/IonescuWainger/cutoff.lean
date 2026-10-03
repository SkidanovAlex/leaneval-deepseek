import Mathlib

/-!
# The smoothed band cut-off used in the Magyar–Stein–Wainger sampling principle

For `ε > 0` we use the plateau
`plateau ε ξ = smoothTransition ((ξ+1/2)/ε) * (1 - smoothTransition ((ξ-1/2+ε)/ε))`,
which is `C^∞`, supported in the Nyquist band `[-1/2,1/2]`, equals `1` on `[-1/2+ε, 1/2-ε]`,
and increases to the indicator of `[-1/2,1/2]` as `ε ↓ 0`.
-/

namespace Work.BourgainPlan.IonescuWainger

open scoped BigOperators

noncomputable section

/-- The smoothed cut-off of the Nyquist band: `C^∞`, supported in `[-1/2,1/2]`, equal to `1` on
`[-1/2+ε, 1/2-ε]`. -/
def plateau (ε ξ : ℝ) : ℝ :=
  Real.smoothTransition ((ξ + 1/2) / ε) * (1 - Real.smoothTransition ((ξ - 1/2 + ε) / ε))

lemma plateau_contDiff (ε : ℝ) : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (plateau ε) := by
  unfold plateau
  refine ContDiff.mul ?_ (ContDiff.sub contDiff_const ?_)
  · exact (Real.smoothTransition.contDiff (n := (⊤ : ℕ∞))).comp
      ((contDiff_id.add contDiff_const).div_const ε)
  · exact (Real.smoothTransition.contDiff (n := (⊤ : ℕ∞))).comp
      (((contDiff_id.sub contDiff_const).add contDiff_const).div_const ε)

lemma plateau_continuous (ε : ℝ) : Continuous (plateau ε) := (plateau_contDiff ε).continuous

lemma plateau_nonneg (ε : ℝ) (ξ : ℝ) : 0 ≤ plateau ε ξ := by
  unfold plateau
  have h2 : Real.smoothTransition ((ξ - 1/2 + ε) / ε) ≤ 1 := Real.smoothTransition.le_one _
  have h1 : 0 ≤ Real.smoothTransition ((ξ + 1/2) / ε) := Real.smoothTransition.nonneg _
  have : 0 ≤ 1 - Real.smoothTransition ((ξ - 1/2 + ε) / ε) := by linarith
  exact mul_nonneg h1 this

lemma plateau_le_one (ε : ℝ) (hε : 0 < ε) (ξ : ℝ) : plateau ε ξ ≤ 1 := by
  unfold plateau
  have h1 : Real.smoothTransition ((ξ + 1/2) / ε) ≤ 1 := Real.smoothTransition.le_one _
  have h2 : 0 ≤ Real.smoothTransition ((ξ - 1/2 + ε) / ε) := Real.smoothTransition.nonneg _
  have h3 : 0 ≤ 1 - Real.smoothTransition ((ξ - 1/2 + ε) / ε) :=
    by linarith [Real.smoothTransition.le_one ((ξ - 1/2 + ε) / ε)]
  have h4 : 1 - Real.smoothTransition ((ξ - 1/2 + ε) / ε) ≤ 1 :=
    by linarith [Real.smoothTransition.nonneg ((ξ - 1/2 + ε) / ε)]
  exact mul_le_one₀ h1 h3 h4

lemma plateau_eq_zero_of_le (ε : ℝ) (hε : 0 < ε) {ξ : ℝ} (h : ξ ≤ -(1/2)) : plateau ε ξ = 0 := by
  unfold plateau
  have h1 : (ξ + 1/2) / ε ≤ 0 := div_nonpos_iff.mpr (Or.inr ⟨by linarith, hε.le⟩)
  rw [Real.smoothTransition.zero_of_nonpos h1, zero_mul]

lemma plateau_eq_zero_of_ge (ε : ℝ) (hε : 0 < ε) {ξ : ℝ} (h : (1/2) ≤ ξ) : plateau ε ξ = 0 := by
  unfold plateau
  have h1 : 1 ≤ (ξ - 1/2 + ε) / ε := by rw [le_div_iff₀ hε]; linarith
  rw [Real.smoothTransition.one_of_one_le h1, sub_self, mul_zero]

lemma plateau_eq_one (ε : ℝ) (hε : 0 < ε) {ξ : ℝ}
    (hlo : -(1/2) + ε ≤ ξ) (hhi : ξ ≤ (1/2) - ε) : plateau ε ξ = 1 := by
  unfold plateau
  have h1 : 1 ≤ (ξ + 1/2) / ε := by rw [le_div_iff₀ hε]; linarith
  have h2 : (ξ - 1/2 + ε) / ε ≤ 0 := by
    rw [div_nonpos_iff]; exact Or.inr ⟨by linarith, hε.le⟩
  rw [Real.smoothTransition.one_of_one_le h1, Real.smoothTransition.zero_of_nonpos h2, sub_zero,
    mul_one]

lemma plateau_support (ε : ℝ) (hε : 0 < ε) :
    Function.support (plateau ε) ⊆ Set.Icc (-(1/2):ℝ) (1/2) := by
  intro ξ hξ
  rw [Function.mem_support] at hξ
  refine ⟨?_, ?_⟩
  · by_contra h
    exact hξ (plateau_eq_zero_of_le ε hε (not_le.mp h).le)
  · by_contra h
    exact hξ (plateau_eq_zero_of_ge ε hε (not_le.mp h).le)

/-- For every `ξ` in the open band, `plateau ε ξ = 1` as soon as `ε` is small enough. -/
lemma plateau_eq_one_of_lt (ε ξ : ℝ) (hε : 0 < ε)
    (hε' : ε < min (ξ + 1/2) (1/2 - ξ)) : plateau ε ξ = 1 :=
  plateau_eq_one ε hε (by linarith [hε', min_le_left (ξ + 1/2) (1/2 - ξ)])
    (by linarith [hε', min_le_right (ξ + 1/2) (1/2 - ξ)])

end

end Work.BourgainPlan.IonescuWainger
