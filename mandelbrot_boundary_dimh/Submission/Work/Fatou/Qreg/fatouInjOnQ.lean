import Mathlib
import Submission.Work.Interfaces.Fatou
import Submission.Work.Fatou.Qreg.InjGeom

/-!
# Shishikura, Proposition A.2.1 (0): a near-translation on `𝒬(b₁,b₂)` is univalent

This file proves `MandelDim.FatouInjOnQ`: if `F` is holomorphic on Shishikura's region
`Qreg b₁ b₂` with `‖F z - (z+1)‖ ≤ 1/32` and `‖F' z - 1‖ ≤ 1/32` there, then `F` is injective
on that region.

Two points `z₁ ≠ z₂` with `F z₁ = F z₂` satisfy `d := ‖z₁ - z₂‖ ≤ 1/16` by the value estimate;
`Qreg` is the complement of two closed `π/2`-cones with apices `b₁`, `b₂` more than `4` apart, and
any two points of it at distance `≤ 1/2` can be joined inside it by a polygonal path of length at
most `8 d` (`exists_mid`, out of the half-plane decompositions in `InjGeom`); the mean value
inequality on the two straight pieces gives
`‖F z₂ - F z₁ - (z₂ - z₁)‖ ≤ (1/32) · 8 d = d/4 < d`, and `F z₁ = F z₂` forces `d = 0`.
-/

namespace Work.Fatou.Qreg

open MandelDim Set Metric Filter
open scoped Topology

noncomputable section

/-- Any two points of `Qreg b₁ b₂` at distance at most `1/2` are joined inside `Qreg b₁ b₂` by a
polygonal path of total length at most `8` times their distance. -/
theorem exists_mid (b₁ b₂ : Option ℂ) (hadm : QAdm b₁ b₂) {z₁ z₂ : ℂ}
    (h₁ : z₁ ∈ Qreg b₁ b₂) (h₂ : z₂ ∈ Qreg b₁ b₂) (hd : ‖z₁ - z₂‖ ≤ 1 / 2) :
    ∃ p ∈ Qreg b₁ b₂, segment ℝ z₁ p ⊆ Qreg b₁ b₂ ∧ segment ℝ p z₂ ⊆ Qreg b₁ b₂ ∧
      ‖z₁ - p‖ + ‖p - z₂‖ ≤ 8 * ‖z₁ - z₂‖ := by
  rcases b₁ with _ | a <;> rcases b₂ with _ | c
  · rw [Qreg_none_none]
    exact ⟨z₁, trivial, subset_univ _, subset_univ _, by
      simp only [sub_self, norm_zero, zero_add]
      exact le_mul_of_one_le_left (norm_nonneg _) (by norm_num)⟩
  · rw [Qreg_none_some] at h₁ h₂
    rw [Qreg_none_some]
    exact pathSingleR h₁ h₂ (le_trans hd (by norm_num))
  · rw [Qreg_some_none] at h₁ h₂
    rw [Qreg_some_none]
    exact pathSingleP h₁ h₂ (le_trans hd (by norm_num))
  · rw [Qreg_some_some] at h₁ h₂
    rw [Qreg_some_some]
    have hadm' : a.re + 4 < c.re := by simpa [QAdm] using hadm
    exact exists_mid_pair hadm' h₁ h₂ hd

theorem fatouInjOnQ : MandelDim.FatouInjOnQ := by
  intro b₁ b₂ F hadm hNT
  obtain ⟨hdiff, hNT'⟩ := hNT
  have hval : ∀ z ∈ Qreg b₁ b₂, ‖F z - (z + 1)‖ ≤ 1 / 32 := fun z hz => (hNT' z hz).1
  have hder : ∀ z ∈ Qreg b₁ b₂, ‖deriv F z - 1‖ ≤ 1 / 32 := fun z hz => (hNT' z hz).2
  have hQ : IsOpen (Qreg b₁ b₂) := isOpen_Qreg b₁ b₂
  intro z₁ hz₁ z₂ hz₂ heq
  -- the value estimate bounds the distance by `1/16`
  have hd : ‖z₁ - z₂‖ ≤ 1 / 16 := by
    have h₁ := hval z₁ hz₁
    have h₂ := hval z₂ hz₂
    have hsub : z₁ - z₂ = (F z₂ - (z₂ + 1)) - (F z₁ - (z₁ + 1)) := by rw [heq]; ring
    rw [hsub]
    calc ‖(F z₂ - (z₂ + 1)) - (F z₁ - (z₁ + 1))‖
        ≤ ‖F z₁ - (z₁ + 1)‖ + ‖F z₂ - (z₂ + 1)‖ := by
          have hsplit : (F z₂ - (z₂ + 1)) - (F z₁ - (z₁ + 1)) =
              -((F z₁ - (z₁ + 1)) - (F z₂ - (z₂ + 1))) := by ring
          rw [hsplit, norm_neg]
          exact norm_sub_le _ _
      _ ≤ 1 / 32 + 1 / 32 := add_le_add h₁ h₂
      _ = 1 / 16 := by norm_num
  obtain ⟨p, hpQ, hseg₁, hseg₂, hlen⟩ :=
    exists_mid b₁ b₂ hadm hz₁ hz₂ (le_trans hd (by norm_num))
  -- the derivative estimate makes `F - id` Lipschitz on every straight piece inside `Qreg`
  have hMVT : ∀ {x y : ℂ}, segment ℝ x y ⊆ Qreg b₁ b₂ → x ∈ Qreg b₁ b₂ → y ∈ Qreg b₁ b₂ →
      ‖(F y - y) - (F x - x)‖ ≤ (1 / 32) * ‖y - x‖ := by
    intro x y hxy hx hy
    have hA : ∀ w ∈ segment ℝ x y, DifferentiableAt ℂ (F - fun z : ℂ => z) w := fun w hw =>
      ((hdiff w (hxy hw)).differentiableAt (hQ.mem_nhds (hxy hw))).sub differentiableAt_id
    have hB : ∀ w ∈ segment ℝ x y, ‖deriv (F - fun z : ℂ => z) w‖ ≤ (1 / 32 : ℝ) := by
      intro w hw
      have h₁' : DifferentiableAt ℂ F w :=
        (hdiff w (hxy hw)).differentiableAt (hQ.mem_nhds (hxy hw))
      have h₂' : DifferentiableAt ℂ (fun z : ℂ => z) w := differentiableAt_id
      have hdsub : deriv (F - fun z : ℂ => z) w =
          deriv F w - deriv (fun z : ℂ => z) w := deriv_sub h₁' h₂'
      have hdid : deriv (fun z : ℂ => z) w = 1 := by
          rw [show (fun z : ℂ => z) = id from rfl, deriv_id]
      rw [hdsub, hdid]
      exact hder w (hxy hw)
    have hx' : x ∈ segment ℝ x y := left_mem_segment (𝕜 := ℝ) x y
    have hy' : y ∈ segment ℝ x y := right_mem_segment (𝕜 := ℝ) x y
    exact Convex.norm_image_sub_le_of_norm_deriv_le (s := segment ℝ x y)
      (f := F - fun z : ℂ => z) hA hB (convex_segment x y) hx' hy'
  have h₁ := hMVT hseg₁ hz₁ hpQ
  have h₂ := hMVT hseg₂ hpQ hz₂
  have hstep : ‖z₂ - p‖ + ‖p - z₁‖ ≤ 8 * ‖z₁ - z₂‖ := by
    rw [norm_sub_rev z₂ p, norm_sub_rev p z₁]
    linarith [hlen]
  have hbound : ‖(F z₂ - z₂) - (F z₁ - z₁)‖ ≤ (1 / 32) * (8 * ‖z₁ - z₂‖) := by
    calc ‖(F z₂ - z₂) - (F z₁ - z₁)‖
        ≤ ‖(F z₂ - z₂) - (F p - p)‖ + ‖(F p - p) - (F z₁ - z₁)‖ := by
          have hsplit : (F z₂ - z₂) - (F z₁ - z₁) =
              ((F z₂ - z₂) - (F p - p)) + ((F p - p) - (F z₁ - z₁)) := by ring
          rw [hsplit]
          exact norm_add_le _ _
      _ ≤ (1 / 32) * ‖z₂ - p‖ + (1 / 32) * ‖p - z₁‖ := add_le_add h₂ h₁
      _ = (1 / 32) * (‖z₂ - p‖ + ‖p - z₁‖) := by ring
      _ ≤ (1 / 32) * (8 * ‖z₁ - z₂‖) :=
          mul_le_mul_of_nonneg_left hstep (by norm_num)
  have hEq : ‖(F z₂ - z₂) - (F z₁ - z₁)‖ = ‖z₁ - z₂‖ := by
    have hz : (F z₂ - z₂) - (F z₁ - z₁) = -(z₂ - z₁) := by rw [heq]; ring
    rw [hz, norm_neg, norm_sub_rev]
  have hsmall : ‖z₁ - z₂‖ ≤ (1 / 32) * (8 * ‖z₁ - z₂‖) :=
    calc ‖z₁ - z₂‖ = ‖(F z₂ - z₂) - (F z₁ - z₁)‖ := hEq.symm
      _ ≤ (1 / 32) * (8 * ‖z₁ - z₂‖) := hbound
  have hzero : ‖z₁ - z₂‖ = 0 := by
    have hlin : (1 / 32 : ℝ) * (8 * ‖z₁ - z₂‖) = ‖z₁ - z₂‖ / 4 := by ring
    linarith [hsmall, hlin, norm_nonneg (z₁ - z₂)]
  exact sub_eq_zero.mp (norm_eq_zero.mp hzero)

end

end Work.Fatou.Qreg
