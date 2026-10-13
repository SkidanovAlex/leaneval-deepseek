import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.SmoothTransition

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongLWP.Sobolev.EqcAux

/-- A smooth (C^∞) cutoff function which is `1` on `[a,b]` and `0` outside `[a',b']`,
whenever `a' < a` and `b < b'`.

It is built as a product of two translates of `Real.smoothTransition`:
`x ↦ st ((x - a')/(a - a')) * st ((b' - x)/(b' - b))`. -/
theorem smoothIntervalCutoff {a' a b b' : ℝ} (h1 : a' < a) (h3 : b < b') :
    ∃ g : ℝ → ℝ, (∀ n : ℕ, ContDiff ℝ n g) ∧ HasCompactSupport g ∧
      (∀ x, 0 ≤ g x) ∧ (∀ x, g x ≤ 1) ∧
      (∀ x ∈ Set.Icc a b, g x = 1) ∧ (∀ x ∉ Set.Icc a' b', g x = 0) := by
  set c1 : ℝ := (a - a')⁻¹ with hc1def
  set c2 : ℝ := (b' - b)⁻¹ with hc2def
  have hc1pos : 0 < c1 := by rw [hc1def]; exact inv_pos.mpr (by linarith)
  have hc2pos : 0 < c2 := by rw [hc2def]; exact inv_pos.mpr (by linarith)
  have h1ne : a - a' ≠ 0 := by linarith
  have h3ne : b' - b ≠ 0 := by linarith
  have hzero : ∀ x : ℝ, x ∉ Set.Icc a' b' →
      Real.smoothTransition (c1 * (x - a')) * Real.smoothTransition (c2 * (b' - x)) = 0 := by
    intro x hx
    simp only [Set.mem_Icc, not_and_or, not_le] at hx
    rcases hx with hx | hx
    · rw [Real.smoothTransition.zero_of_nonpos
          (le_of_lt (mul_neg_of_pos_of_neg hc1pos (by linarith))), zero_mul]
    · rw [Real.smoothTransition.zero_of_nonpos
          (le_of_lt (mul_neg_of_pos_of_neg hc2pos (by linarith))), mul_zero]
  have hcs : HasCompactSupport
      (fun x : ℝ => Real.smoothTransition (c1 * (x - a')) *
        Real.smoothTransition (c2 * (b' - x))) :=
    HasCompactSupport.intro' (K := Set.Icc a' b') isCompact_Icc isClosed_Icc hzero
  have hsm : ∀ n : ℕ, ContDiff ℝ n
      (fun x : ℝ => Real.smoothTransition (c1 * (x - a')) *
        Real.smoothTransition (c2 * (b' - x))) := by
    intro n
    have h1n : ContDiff ℝ n (fun x : ℝ => Real.smoothTransition (c1 * (x - a'))) :=
      Real.smoothTransition.contDiff.comp
        (contDiff_const.mul (contDiff_id.sub contDiff_const))
    have h2n : ContDiff ℝ n (fun x : ℝ => Real.smoothTransition (c2 * (b' - x))) :=
      Real.smoothTransition.contDiff.comp
        (contDiff_const.mul (contDiff_const.sub contDiff_id))
    exact h1n.mul h2n
  have hnn : ∀ x : ℝ, 0 ≤ Real.smoothTransition (c1 * (x - a')) *
      Real.smoothTransition (c2 * (b' - x)) :=
    fun x => mul_nonneg (Real.smoothTransition.nonneg _) (Real.smoothTransition.nonneg _)
  have hle : ∀ x : ℝ, Real.smoothTransition (c1 * (x - a')) *
      Real.smoothTransition (c2 * (b' - x)) ≤ 1 := by
    intro x
    have hp2 : 0 ≤ Real.smoothTransition (c2 * (b' - x)) := Real.smoothTransition.nonneg _
    calc Real.smoothTransition (c1 * (x - a')) * Real.smoothTransition (c2 * (b' - x))
        ≤ 1 * Real.smoothTransition (c2 * (b' - x)) :=
          mul_le_mul_of_nonneg_right (Real.smoothTransition.le_one _) hp2
      _ = Real.smoothTransition (c2 * (b' - x)) := one_mul _
      _ ≤ 1 := Real.smoothTransition.le_one _
  have hone : ∀ x ∈ Set.Icc a b, Real.smoothTransition (c1 * (x - a')) *
      Real.smoothTransition (c2 * (b' - x)) = 1 := by
    intro x hx
    have he1 : 1 ≤ c1 * (x - a') := by
      have h : c1 * (a - a') ≤ c1 * (x - a') :=
        mul_le_mul_of_nonneg_left (by linarith [hx.1]) (le_of_lt hc1pos)
      have h' : c1 * (a - a') = 1 := by rw [hc1def, inv_mul_cancel₀ h1ne]
      linarith
    have he2 : 1 ≤ c2 * (b' - x) := by
      have h : c2 * (b' - b) ≤ c2 * (b' - x) :=
        mul_le_mul_of_nonneg_left (by linarith [hx.2]) (le_of_lt hc2pos)
      have h' : c2 * (b' - b) = 1 := by rw [hc2def, inv_mul_cancel₀ h3ne]
      linarith
    rw [Real.smoothTransition.one_of_one_le he1, Real.smoothTransition.one_of_one_le he2,
      mul_one]
  exact ⟨fun x => Real.smoothTransition (c1 * (x - a')) *
      Real.smoothTransition (c2 * (b' - x)), hsm, hcs, hnn, hle, hone, hzero⟩

end Work.FTS.StrongLWP.Sobolev.EqcAux
