/-
# The `γ`-weighted slice weight `σ_γ(θ) = sin(2θ)^{2-γ}` and its elementary facts

This module collects the vocabulary for the `γ`-weighted slice boundary-limit lemma
`Work.FTS.EllipticEst.Prop.aslotTwoShift_sliceBoundaryLimit_gam`: the weight

  `sgam α θ = sin(2θ)^{2-γ}`,  `γ = Work.Spaces.gam α = 1 + α/10`

(with `0 < α ≤ 1/4`, so that `2 - γ ∈ [39/40, 1)` and `γ - 2 ∈ (-1, -39/40]`),
together with the elementary facts about it:

* positivity, nonnegativity, continuity, the identification of its reciprocal
  `(sgam α θ)^{-1} = sin(2θ)^{γ-2}`, and the symmetry `θ ↦ π/2 - θ` of the weight;
* Jordan's inequality `sin(2θ) ≥ (4/π)·min θ (π/2 - θ)` on `[0, π/2]` and the resulting
  pointwise domination of the reciprocal `sgam^{-1}` by `(4/π)^{γ-2}·(t^{γ-2} + (π/2-t)^{γ-2})`
  (resp. by a single power of `t` on `(0, π/4)` and of `π/2 - t` on `(π/4, π/2)`).

These are the `η`-free inputs of the proof; the analytic content (the reciprocal-mass bounds
and the `L²`-domination of `deriv f`) is built on top of them in the companion modules.
-/
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Submission.Work.Spaces.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.Prop.AslotGam

set_option autoImplicit false

/-- The `γ`-weighted angular weight `sgam α θ = sin(2θ)^{2-γ}`, `γ = 1 + α/10`. -/
def sgam (α θ : ℝ) : ℝ := (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α)

/-! ## Elementary facts about `γ` -/

theorem gam_sub_two_nonpos {α : ℝ} (hα4 : α ≤ 1 / 4) : Work.Spaces.gam α - 2 ≤ 0 := by
  rw [Work.Spaces.gam]; linarith

theorem gam_sub_two_gt_neg_one {α : ℝ} (hα : 0 < α) : -1 < Work.Spaces.gam α - 2 := by
  rw [Work.Spaces.gam]; linarith

theorem gam_sub_two_neg {α : ℝ} (hα4 : α ≤ 1 / 4) : Work.Spaces.gam α - 2 < 0 := by
  rw [Work.Spaces.gam]; linarith

theorem two_sub_gam_pos {α : ℝ} (hα4 : α ≤ 1 / 4) : 0 < 2 - Work.Spaces.gam α := by
  rw [Work.Spaces.gam]; linarith

theorem gam_lt_two {α : ℝ} (hα4 : α ≤ 1 / 4) : Work.Spaces.gam α < 2 := by
  rw [Work.Spaces.gam]; linarith

theorem four_div_pi_pos : (0 : ℝ) < 4 / Real.pi := by positivity

theorem four_div_pi_le_two : (4 : ℝ) / Real.pi ≤ 2 := by
  rw [div_le_iff₀ Real.pi_pos]; nlinarith [Real.pi_gt_three]

/-! ## The weight and its reciprocal -/

theorem sin_two_pos {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) : 0 < Real.sin (2 * θ) :=
  Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])

theorem sgam_pos {α θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) : 0 < sgam α θ :=
  Real.rpow_pos_of_pos (sin_two_pos hθ) _

theorem sgam_nonneg {α θ : ℝ} (hθ : θ ∈ Set.Icc 0 (Real.pi / 2)) : 0 ≤ sgam α θ :=
  Real.rpow_nonneg
    (Real.sin_nonneg_of_mem_Icc ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩) _

theorem sgam_le_one {α θ : ℝ} (hα : α ≤ 1) (hθ : θ ∈ Set.Icc 0 (Real.pi / 2)) :
    sgam α θ ≤ 1 := by
  have hγ : 0 ≤ 2 - Work.Spaces.gam α := by rw [Work.Spaces.gam]; linarith
  have hsin : 0 ≤ Real.sin (2 * θ) :=
    Real.sin_nonneg_of_mem_Icc ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩
  exact Real.rpow_le_one hsin (Real.sin_le_one _) hγ

theorem sgam_continuousOn (α : ℝ) : ContinuousOn (sgam α) (Set.Ioo 0 (Real.pi / 2)) := by
  refine ContinuousOn.rpow_const ?_ ?_
  · exact Real.continuous_sin.comp_continuousOn
      ((continuous_const.mul continuous_id).continuousOn)
  · intro θ hθ
    exact Or.inl (ne_of_gt (sin_two_pos hθ))

theorem sgam_inv_eq {α θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    (sgam α θ)⁻¹ = (Real.sin (2 * θ)) ^ (Work.Spaces.gam α - 2) := by
  rw [sgam, ← Real.rpow_neg (le_of_lt (sin_two_pos hθ))]
  congr 1
  ring

/-- The weight is invariant under the reflection `θ ↦ π/2 - θ`. -/
theorem sgam_sub_symm (α : ℝ) (u : ℝ) :
    sgam α (Real.pi / 2 - u) = sgam α u := by
  rw [sgam, sgam, show 2 * (Real.pi / 2 - u) = Real.pi - 2 * u by ring, Real.sin_pi_sub]

/-! ## Jordan's inequality and the resulting pointwise domination -/

/-- Jordan's inequality in the form needed here:
`(4/π)·min θ (π/2 - θ) ≤ sin(2θ)` on `[0, π/2]`. -/
theorem four_div_pi_mul_min_le_sin_two {θ : ℝ} (hθ : θ ∈ Set.Icc 0 (Real.pi / 2)) :
    (4 / Real.pi) * min θ (Real.pi / 2 - θ) ≤ Real.sin (2 * θ) := by
  have hpi := Real.pi_pos
  have h0 : (0 : ℝ) ≤ θ := hθ.1
  have h2 : θ ≤ Real.pi / 2 := hθ.2
  rcases le_total θ (Real.pi / 4) with h | h
  · have hm : min θ (Real.pi / 2 - θ) = θ := min_eq_left (by linarith)
    rw [hm]
    have h1 : 2 / Real.pi * (2 * θ) ≤ Real.sin (2 * θ) :=
      Real.mul_le_sin (by linarith) (by linarith)
    have h2' : 2 / Real.pi * (2 * θ) = (4 / Real.pi) * θ := by ring
    linarith [h1, h2'.symm.le, h2'.le]
  · have hm : min θ (Real.pi / 2 - θ) = Real.pi / 2 - θ := min_eq_right (by linarith)
    rw [hm]
    have h1 : 2 / Real.pi * (2 * (Real.pi / 2 - θ)) ≤ Real.sin (2 * (Real.pi / 2 - θ)) :=
      Real.mul_le_sin (by linarith) (by linarith)
    have hs : Real.sin (2 * (Real.pi / 2 - θ)) = Real.sin (2 * θ) := by
      rw [show 2 * (Real.pi / 2 - θ) = Real.pi - 2 * θ by ring, Real.sin_pi_sub]
    rw [hs] at h1
    have h2' : 2 / Real.pi * (2 * (Real.pi / 2 - θ)) = (4 / Real.pi) * (Real.pi / 2 - θ) := by ring
    linarith [h1, h2'.symm.le, h2'.le]

theorem min_rpow_le_sum {a b c : ℝ} (ha : 0 < a) (hb : 0 < b) :
    (min a b) ^ c ≤ a ^ c + b ^ c := by
  rcases le_total a b with h | h
  · rw [min_eq_left h]
    exact le_add_of_nonneg_right (Real.rpow_nonneg (le_of_lt hb) c)
  · rw [min_eq_right h]
    exact le_add_of_nonneg_left (Real.rpow_nonneg (le_of_lt ha) c)

/-- Pointwise domination of the reciprocal weight:
on `(0, π/2)`, `(sgam α t)^{-1} = sin(2t)^{γ-2} ≤ (4/π)^{γ-2}·(t^{γ-2} + (π/2-t)^{γ-2})`. -/
theorem sgam_inv_le {α t : ℝ} (hα4 : α ≤ 1 / 4) (ht : t ∈ Set.Ioo 0 (Real.pi / 2)) :
    (sgam α t)⁻¹ ≤ (4 / Real.pi) ^ (Work.Spaces.gam α - 2) *
      (t ^ (Work.Spaces.gam α - 2) + (Real.pi / 2 - t) ^ (Work.Spaces.gam α - 2)) := by
  have hc : Work.Spaces.gam α - 2 ≤ 0 := gam_sub_two_nonpos hα4
  have h4pi : 0 < 4 / Real.pi := four_div_pi_pos
  have h2t : 0 < Real.pi / 2 - t := by linarith [ht.2, Real.pi_pos]
  have hmpos : 0 < min t (Real.pi / 2 - t) := lt_min ht.1 h2t
  have hbase : (4 / Real.pi) * min t (Real.pi / 2 - t) ≤ Real.sin (2 * t) :=
    four_div_pi_mul_min_le_sin_two ⟨le_of_lt ht.1, le_of_lt ht.2⟩
  have hpos : 0 < (4 / Real.pi) * min t (Real.pi / 2 - t) := mul_pos h4pi hmpos
  have hstep : (Real.sin (2 * t)) ^ (Work.Spaces.gam α - 2)
      ≤ ((4 / Real.pi) * min t (Real.pi / 2 - t)) ^ (Work.Spaces.gam α - 2) :=
    Real.rpow_le_rpow_of_nonpos hpos hbase hc
  rw [Real.mul_rpow (le_of_lt h4pi) (le_of_lt hmpos)] at hstep
  rw [sgam_inv_eq ht]
  refine hstep.trans ?_
  exact mul_le_mul_of_nonneg_left (min_rpow_le_sum ht.1 h2t)
    (Real.rpow_nonneg (le_of_lt h4pi) _)

/-- Pointwise domination on the left half of the interval:
for `t ∈ (0, π/4)`, `(sgam α t)^{-1} ≤ (4/π)^{γ-2}·t^{γ-2}`. -/
theorem sgam_inv_le_left {α t : ℝ} (hα4 : α ≤ 1 / 4) (ht : t ∈ Set.Ioo 0 (Real.pi / 4)) :
    (sgam α t)⁻¹ ≤ (4 / Real.pi) ^ (Work.Spaces.gam α - 2) * t ^ (Work.Spaces.gam α - 2) := by
  have hc : Work.Spaces.gam α - 2 ≤ 0 := gam_sub_two_nonpos hα4
  have h4pi : 0 < 4 / Real.pi := four_div_pi_pos
  have hmem : t ∈ Set.Icc 0 (Real.pi / 2) :=
    ⟨le_of_lt ht.1, by linarith [ht.2, Real.pi_pos]⟩
  have hm : min t (Real.pi / 2 - t) = t := min_eq_left (by linarith [ht.2, Real.pi_pos])
  have hbase : (4 / Real.pi) * t ≤ Real.sin (2 * t) := by
    have h := four_div_pi_mul_min_le_sin_two hmem
    rwa [hm] at h
  have hpos : 0 < (4 / Real.pi) * t := mul_pos h4pi ht.1
  have hstep : (Real.sin (2 * t)) ^ (Work.Spaces.gam α - 2)
      ≤ ((4 / Real.pi) * t) ^ (Work.Spaces.gam α - 2) :=
    Real.rpow_le_rpow_of_nonpos hpos hbase hc
  rw [Real.mul_rpow (le_of_lt h4pi) (le_of_lt ht.1)] at hstep
  rwa [sgam_inv_eq ⟨ht.1, by linarith [ht.2, Real.pi_pos]⟩]

/-- Pointwise domination on the right half of the interval:
for `t ∈ (π/4, π/2)`, `(sgam α t)^{-1} ≤ (4/π)^{γ-2}·(π/2 - t)^{γ-2}`. -/
theorem sgam_inv_le_right {α t : ℝ} (hα4 : α ≤ 1 / 4)
    (ht : t ∈ Set.Ioo (Real.pi / 4) (Real.pi / 2)) :
    (sgam α t)⁻¹ ≤ (4 / Real.pi) ^ (Work.Spaces.gam α - 2) *
      (Real.pi / 2 - t) ^ (Work.Spaces.gam α - 2) := by
  have hc : Work.Spaces.gam α - 2 ≤ 0 := gam_sub_two_nonpos hα4
  have h4pi : 0 < 4 / Real.pi := four_div_pi_pos
  have hmem : t ∈ Set.Icc 0 (Real.pi / 2) :=
    ⟨by linarith [ht.1, Real.pi_pos], le_of_lt ht.2⟩
  have hm : min t (Real.pi / 2 - t) = Real.pi / 2 - t := min_eq_right (by linarith [ht.1])
  have hbase : (4 / Real.pi) * (Real.pi / 2 - t) ≤ Real.sin (2 * t) := by
    have h := four_div_pi_mul_min_le_sin_two hmem
    rwa [hm] at h
  have hpos : 0 < Real.pi / 2 - t := by linarith [ht.2]
  have hstep : (Real.sin (2 * t)) ^ (Work.Spaces.gam α - 2)
      ≤ ((4 / Real.pi) * (Real.pi / 2 - t)) ^ (Work.Spaces.gam α - 2) :=
    Real.rpow_le_rpow_of_nonpos (mul_pos h4pi hpos) hbase hc
  rw [Real.mul_rpow (le_of_lt h4pi) (le_of_lt hpos)] at hstep
  rwa [sgam_inv_eq ⟨by linarith [ht.1, Real.pi_pos], ht.2⟩]

end Work.FTS.EllipticEst.Prop.AslotGam
