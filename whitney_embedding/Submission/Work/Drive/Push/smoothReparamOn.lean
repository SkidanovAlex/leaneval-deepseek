import Mathlib
import Submission.Work.Drive.Push.spineUnknottingLocal

namespace Work.Drive.Push

/-- The `C^∞` "cascade" factor `σ((t+ρ)/ρ)·σ((1+ρ-t)/ρ)`, equal to `1` on `[0,1]` and
vanishing outside `[-ρ, 1+ρ]`; it always lies in `[0,1]`. -/
private noncomputable def reparamFactorOn (ρ : ℝ) (t : ℝ) : ℝ :=
  Real.smoothTransition ((t + ρ) / ρ) * Real.smoothTransition ((1 + ρ - t) / ρ)

private lemma reparamFactorOn_nonneg (ρ : ℝ) (t : ℝ) : 0 ≤ reparamFactorOn ρ t :=
  mul_nonneg (Real.smoothTransition.nonneg _) (Real.smoothTransition.nonneg _)

private lemma reparamFactorOn_le_one (ρ : ℝ) (t : ℝ) : reparamFactorOn ρ t ≤ 1 := by
  calc reparamFactorOn ρ t
      ≤ 1 * Real.smoothTransition ((1 + ρ - t) / ρ) :=
        mul_le_mul_of_nonneg_right (Real.smoothTransition.le_one _)
          (Real.smoothTransition.nonneg _)
    _ = Real.smoothTransition ((1 + ρ - t) / ρ) := one_mul _
    _ ≤ 1 := Real.smoothTransition.le_one _

/-- **A smooth reparametrisation of `ℝ` which is the identity on `[0,1]` and whose image lies in
`[-ρ, 1+ρ]`.** -/
theorem smoothReparamOn (ρ : ℝ) (hρ : 0 < ρ) :
    ∃ φ : ℝ → ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ ∧
      (∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 → φ t = t) ∧
      (∀ t : ℝ, φ t ∈ Set.Icc (-ρ) (1 + ρ)) := by
  refine ⟨fun t => t * reparamFactorOn ρ t, ?_, ?_, ?_⟩
  · -- smoothness: a product of smooth factors
    show ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun t : ℝ => t * (Real.smoothTransition ((t + ρ) / ρ) *
        Real.smoothTransition ((1 + ρ - t) / ρ)))
    fun_prop
  · -- the identity on `[0,1]`
    intro t ht
    have h1 : Real.smoothTransition ((t + ρ) / ρ) = 1 :=
      Real.smoothTransition.one_of_one_le (by rw [le_div_iff₀ hρ]; linarith [ht.1])
    have h2 : Real.smoothTransition ((1 + ρ - t) / ρ) = 1 :=
      Real.smoothTransition.one_of_one_le (by rw [le_div_iff₀ hρ]; linarith [ht.2])
    simp [reparamFactorOn, h1, h2]
  · -- the range bound `φ t ∈ [-ρ, 1+ρ]`
    intro t
    constructor
    · -- lower bound
      rcases le_total t 0 with ht | ht
      · rcases le_total (-ρ) t with h1 | h1
        · have hle : t ≤ t * reparamFactorOn ρ t := by
            simpa using mul_le_mul_of_nonpos_left (reparamFactorOn_le_one ρ t) ht
          linarith
        · have hz : Real.smoothTransition ((t + ρ) / ρ) = 0 :=
            Real.smoothTransition.zero_of_nonpos
              (div_nonpos_of_nonpos_of_nonneg (by linarith) (le_of_lt hρ))
          have h0 : t * reparamFactorOn ρ t = 0 := by simp [reparamFactorOn, hz]
          show -ρ ≤ t * reparamFactorOn ρ t
          rw [h0]; linarith
      · have hge : 0 ≤ t * reparamFactorOn ρ t :=
          mul_nonneg ht (reparamFactorOn_nonneg ρ t)
        linarith
    · -- upper bound
      rcases le_total 0 t with ht | ht
      · rcases le_total t (1 + ρ) with h2 | h2
        · have hle : t * reparamFactorOn ρ t ≤ t := by
            simpa using mul_le_mul_of_nonneg_left (reparamFactorOn_le_one ρ t) ht
          linarith
        · have hz : Real.smoothTransition ((1 + ρ - t) / ρ) = 0 :=
            Real.smoothTransition.zero_of_nonpos
              (div_nonpos_of_nonpos_of_nonneg (by linarith) (le_of_lt hρ))
          have h0 : t * reparamFactorOn ρ t = 0 := by simp [reparamFactorOn, hz]
          show t * reparamFactorOn ρ t ≤ 1 + ρ
          rw [h0]; linarith
      · have hle : t * reparamFactorOn ρ t ≤ 0 :=
          mul_nonpos_of_nonpos_of_nonneg ht (reparamFactorOn_nonneg ρ t)
        linarith

end Work.Drive.Push
