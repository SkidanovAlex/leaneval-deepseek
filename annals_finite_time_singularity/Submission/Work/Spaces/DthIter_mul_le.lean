import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.Spaces.Defs
import Submission.Work.Spaces.pz_aux
import Submission.Work.Spaces.DthIter_mul

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Real Topology

namespace Work.Spaces

theorem DthIter_mul_le (i : ℕ) (f g : ℝ → ℝ → ℝ)
    (hf : Work.Spaces.SmoothInt f) (hg : Work.Spaces.SmoothInt g) :
    ∃ C : ℝ, 0 < C ∧ ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      |Work.Spaces.DthIter i (fun z θ => f z θ * g z θ) z θ| ≤
        C * ∑ a ∈ Finset.range (i + 1),
          |Work.Spaces.DthIter a f z θ| * |Work.Spaces.DthIter (i - a) g z θ| := by
  set S : ℝ := ∑ a ∈ Finset.range (i + 1), (i.choose a : ℝ) with hSdef
  have hSnn : 0 ≤ S := by
    rw [hSdef]
    exact Finset.sum_nonneg (fun a _ => Nat.cast_nonneg (i.choose a))
  refine ⟨1 + S, by linarith, ?_⟩
  intro z hz θ hθ
  have hzIoi : z ∈ Set.Ioi (-1 : ℝ) := by
    simp only [Iz, Set.mem_Ici] at hz
    simp only [Set.mem_Ioi]
    linarith
  by_cases hθint : θ ∈ Set.Ioo 0 (π / 2)
  · -- interior point: apply the Leibniz identity for `D_θ^i`
    have hid := DthIter_mul i f g z (Set.Ioo 0 (π / 2)) isOpen_Ioo
      (hf.contDiffOn_theta_slice hzIoi) (hg.contDiffOn_theta_slice hzIoi) θ hθint
    rw [hid]
    have hc0 : ∀ a ∈ Finset.range (i + 1), (0 : ℝ) ≤ (i.choose a : ℝ) :=
      fun a _ => Nat.cast_nonneg (i.choose a)
    have hcS : ∀ a ∈ Finset.range (i + 1), (i.choose a : ℝ) ≤ 1 + S := by
      intro a ha
      have h1 : (i.choose a : ℝ) ≤ S := by
        rw [hSdef]
        exact Finset.single_le_sum (fun b _ => Nat.cast_nonneg (i.choose b)) ha
      linarith
    calc |∑ a ∈ Finset.range (i + 1),
            (i.choose a : ℝ) * (DthIter a f z θ * DthIter (i - a) g z θ)|
        ≤ ∑ a ∈ Finset.range (i + 1),
            |(i.choose a : ℝ) * (DthIter a f z θ * DthIter (i - a) g z θ)| :=
          Finset.abs_sum_le_sum_abs _ _
      _ = ∑ a ∈ Finset.range (i + 1),
            (i.choose a : ℝ) * (|DthIter a f z θ| * |DthIter (i - a) g z θ|) := by
          apply Finset.sum_congr rfl
          intro a ha
          rw [abs_mul, abs_of_nonneg (hc0 a ha), abs_mul]
      _ ≤ ∑ a ∈ Finset.range (i + 1),
            (1 + S) * (|DthIter a f z θ| * |DthIter (i - a) g z θ|) := by
          apply Finset.sum_le_sum
          intro a ha
          exact mul_le_mul_of_nonneg_right (hcS a ha)
            (mul_nonneg (abs_nonneg _) (abs_nonneg _))
      _ = (1 + S) * ∑ a ∈ Finset.range (i + 1),
            |DthIter a f z θ| * |DthIter (i - a) g z θ| := by
          rw [Finset.mul_sum]
  · -- boundary point: `θ = 0` or `θ = π/2`
    have hsin : Real.sin (2 * θ) = 0 := sin_two_mul_eq_zero_of_mem_Iθ_of_not_mem_Ioo hθ hθint
    rcases Nat.eq_zero_or_pos i with hi0 | hipos
    · subst hi0
      simp only [DthIter_zero, Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
        Nat.sub_zero]
      rw [abs_mul]
      have h1 : (1 : ℝ) ≤ 1 + S := by linarith
      calc |f z θ| * |g z θ| = 1 * (|f z θ| * |g z θ|) := by ring
        _ ≤ (1 + S) * (|f z θ| * |g z θ|) :=
            mul_le_mul_of_nonneg_right h1 (mul_nonneg (abs_nonneg _) (abs_nonneg _))
    · obtain ⟨i', rfl⟩ := Nat.exists_eq_succ_of_ne_zero hipos.ne'
      rw [DthIter_succ_eq_zero_of_sin_eq_zero i' (fun z θ => f z θ * g z θ) hsin, abs_zero]
      exact mul_nonneg (by linarith)
        (Finset.sum_nonneg (fun a _ => mul_nonneg (abs_nonneg _) (abs_nonneg _)))

end Work.Spaces
