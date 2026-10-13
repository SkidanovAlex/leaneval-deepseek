/-
# `Work.FTS.GalBasis.cc.PsiCutLayer` — the vanishing of `cutB`'s `θ`-derivatives off the layers

`cutB N θ = s((N+1)θ - 1) · s((N+1)(π/2 - θ) - 1)` is *locally constant* at every `θ` outside
the two transition intervals `[1/(N+1), 2/(N+1)]` and `[π/2 - 2/(N+1), π/2 - 1/(N+1)]` (the
*layers* of `NotInThetaLayer N`): left of the first layer the first factor vanishes, in the
middle both factors are `1`, and above the second layer the second factor vanishes.
Consequently all positive `D_θ`-iterates of `cutB N` vanish there, and hence so do the mixed
derivatives `mixed j i (psiCut N)` for `i ≥ 1` — the last clause of `psiCut_spec`.
-/
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS.GalBasis.cc.CutDefs
import Submission.Work.FTS.GalBasis.cc.psiCut_mixed_factor

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.GalBasis.cc

set_option autoImplicit false
set_option linter.unusedVariables false

/-- `DthIter1` kills functions that are constant on an open set. -/
theorem DthIter1_eq_zero_of_open_const {f : ℝ → ℝ} {U : Set ℝ} {θ : ℝ} (hU : IsOpen U)
    (hθ : θ ∈ U) (hconst : ∀ w ∈ U, f w = f θ) :
    ∀ k, 1 ≤ k → ∀ v ∈ U, DthIter1 k f v = 0 := by
  intro k
  induction k with
  | zero => intro hk; omega
  | succ k ih =>
      intro _ v hv
      rcases Nat.eq_zero_or_pos k with hk0 | hkpos
      · subst hk0
        rw [DthIter1_succ, DthIter1_zero]
        show Real.sin (2 * v) * deriv f v = 0
        have hev : f =ᶠ[𝓝 v] fun _ => f θ := by
          filter_upwards [hU.mem_nhds hv] with w hw
          exact hconst w hw
        rw [hev.deriv_eq, deriv_const, mul_zero]
      · rw [DthIter1_succ]
        show Real.sin (2 * v) * deriv (DthIter1 k f) v = 0
        have hev : (fun w => DthIter1 k f w) =ᶠ[𝓝 v] fun _ => (0 : ℝ) := by
          filter_upwards [hU.mem_nhds hv] with w hw
          exact ih hkpos w hw
        rw [hev.deriv_eq, deriv_const, mul_zero]

/-- Outside the two angular layers, `cutB N` is constant on an open neighbourhood. -/
theorem cutB_local_const (N : ℕ) {θ : ℝ} (h : NotInThetaLayer N θ) :
    ∃ U : Set ℝ, IsOpen U ∧ θ ∈ U ∧ ∀ w ∈ U, cutB N w = cutB N θ := by
  have hN : (0 : ℝ) < (N : ℝ) + 1 := by positivity
  have hNe : ((N : ℝ) + 1) ≠ 0 := ne_of_gt hN
  simp only [NotInThetaLayer, tlo, thi, Set.mem_Icc, not_and_or, not_le] at h
  obtain ⟨h1, h2⟩ := h
  rcases h1 with h1 | h1
  · -- left of the first layer
    refine ⟨Set.Iio (1 / ((N : ℝ) + 1)), isOpen_Iio, h1, fun w hw => ?_⟩
    have hw' : ((N : ℝ) + 1) * w - 1 < 0 := by
      have hlt : w < 1 / ((N : ℝ) + 1) := hw
      have h := (lt_div_iff₀ hN).mp hlt
      nlinarith
    have hθ' : ((N : ℝ) + 1) * θ - 1 < 0 := by
      have h := (lt_div_iff₀ hN).mp h1
      nlinarith
    simp only [cutB, Real.smoothTransition.zero_of_nonpos hw'.le,
      Real.smoothTransition.zero_of_nonpos hθ'.le, zero_mul]
  · rcases h2 with h2 | h2
    · -- the middle: both factors are one
      refine ⟨Set.Ioo (2 / ((N : ℝ) + 1)) (Real.pi / 2 - 2 / ((N : ℝ) + 1)), isOpen_Ioo,
        ⟨h1, h2⟩, fun w hw => ?_⟩
      have hw1 : 1 ≤ ((N : ℝ) + 1) * w - 1 := by
        have h2' : (2 : ℝ) < ((N : ℝ) + 1) * w := by
          have h := mul_lt_mul_of_pos_left hw.1 hN
          rw [show ((N : ℝ) + 1) * (2 / ((N : ℝ) + 1)) = 2 from by field_simp] at h
          linarith
        linarith
      have hw2 : 1 ≤ ((N : ℝ) + 1) * (Real.pi / 2 - w) - 1 := by
        have hlt : 2 / ((N : ℝ) + 1) < Real.pi / 2 - w := by linarith [hw.2]
        have h := mul_lt_mul_of_pos_left hlt hN
        rw [show ((N : ℝ) + 1) * (2 / ((N : ℝ) + 1)) = 2 from by field_simp] at h
        linarith
      have hθ1 : 1 ≤ ((N : ℝ) + 1) * θ - 1 := by
        have h2' : (2 : ℝ) < ((N : ℝ) + 1) * θ := by
          have h := mul_lt_mul_of_pos_left h1 hN
          rw [show ((N : ℝ) + 1) * (2 / ((N : ℝ) + 1)) = 2 from by field_simp] at h
          linarith
        linarith
      have hθ2 : 1 ≤ ((N : ℝ) + 1) * (Real.pi / 2 - θ) - 1 := by
        have hlt : 2 / ((N : ℝ) + 1) < Real.pi / 2 - θ := by linarith [h2]
        have h := mul_lt_mul_of_pos_left hlt hN
        rw [show ((N : ℝ) + 1) * (2 / ((N : ℝ) + 1)) = 2 from by field_simp] at h
        linarith
      simp only [cutB, Real.smoothTransition.one_of_one_le hw1,
        Real.smoothTransition.one_of_one_le hw2, Real.smoothTransition.one_of_one_le hθ1,
        Real.smoothTransition.one_of_one_le hθ2, mul_one]
    · -- above the second layer: the second factor vanishes
      refine ⟨Set.Ioi (Real.pi / 2 - 1 / ((N : ℝ) + 1)), isOpen_Ioi, h2, fun w hw => ?_⟩
      have hw' : ((N : ℝ) + 1) * (Real.pi / 2 - w) - 1 < 0 := by
        have hw'' : Real.pi / 2 - 1 / ((N : ℝ) + 1) < w := hw
        have hlt : Real.pi / 2 - w < 1 / ((N : ℝ) + 1) := by linarith
        have h := (lt_div_iff₀ hN).mp hlt
        nlinarith
      have hθ' : ((N : ℝ) + 1) * (Real.pi / 2 - θ) - 1 < 0 := by
        have hlt : Real.pi / 2 - θ < 1 / ((N : ℝ) + 1) := by linarith [h2]
        have h := (lt_div_iff₀ hN).mp hlt
        nlinarith
      simp only [cutB, Real.smoothTransition.zero_of_nonpos hw'.le,
        Real.smoothTransition.zero_of_nonpos hθ'.le, mul_zero]

/-- **The vanishing of the angular derivatives off the layers.** -/
theorem psiCut_layer_zero' (N j i : ℕ) (hi : 1 ≤ i) (z θ : ℝ) (h : NotInThetaLayer N θ) :
    Work.Spaces.mixed j i (psiCut N) z θ = 0 := by
  obtain ⟨U, hU, hθU, hconst⟩ := cutB_local_const N h
  rw [psiCut_mixed_factor N j i z θ, DthIter_const_apply i (cutB N) z θ,
    DthIter1_eq_zero_of_open_const hU hθU hconst i hi θ hθU, mul_zero]

end Work.FTS.GalBasis.cc
