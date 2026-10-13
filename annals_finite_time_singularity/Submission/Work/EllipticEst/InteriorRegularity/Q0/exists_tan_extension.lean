/-
Interior regularity of `bslOp α`: cut-off functions for the Sobolev tower.

* `exists_bump`: a smooth compactly supported function, supported in a prescribed ball and equal
  to `1` on a smaller ball — the nested cut-offs of the tower;
* `exists_tan_extension`: a smooth compactly supported function agreeing with `tan θ` on a
  prescribed ball contained in the strip (used to replace the unbounded coefficient `tan θ` of
  the localized equation by a compactly supported one).
-/
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Submission.Work.EllipticEst.InteriorRegularity.Strip

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter Metric

namespace Work.EllipticEst.InteriorRegularity.Q0

set_option autoImplicit false
set_option linter.unusedVariables false

/-- The strip `{0 < θ < π/2}` is open. -/
theorem isOpen_stripE_fts : IsOpen Work.EllipticEst.InteriorRegularity.stripE := by
  rw [Work.EllipticEst.InteriorRegularity.stripE]
  refine isOpen_Ioo.preimage ?_
  fun_prop

/-- **Existence of a smooth compactly supported extension of `tan θ`.**

If the closed ball `closedBall x₀ r` is contained in the strip `{0 < θ < π/2}`, then `tan (x 1)`
agrees on the ball `ball x₀ r` with a smooth compactly supported function `tt : E2 → ℂ`. -/
theorem exists_tan_extension {x₀ : E2} {r : ℝ}
    (hr : Metric.closedBall x₀ r ⊆ Work.EllipticEst.InteriorRegularity.stripE) :
    ∃ tt : E2 → ℂ, (∀ n : ℕ, ContDiff ℝ n tt) ∧ HasCompactSupport tt ∧
      ∀ x ∈ Metric.ball x₀ r, tt x = (Real.tan (x 1) : ℂ) := by
  rcases le_or_gt r 0 with hrle | hrpos
  · refine ⟨0, fun n => contDiff_const, HasCompactSupport.zero, ?_⟩
    intro x hx
    exfalso
    rw [Metric.mem_ball] at hx
    linarith [dist_nonneg (x := x) (y := x₀)]
  · obtain ⟨δ, hδpos, hδsub⟩ :=
      (isCompact_closedBall x₀ r).exists_cthickening_subset_open isOpen_stripE_fts hr
    let f : ContDiffBump x₀ := ⟨r, r + δ, hrpos, by linarith⟩
    have hrIn : f.rIn = r := rfl
    have hrOut : f.rOut = r + δ := rfl
    have hρ_smooth : ∀ n : ℕ, ContDiff ℝ n (fun y : E2 => ((f y : ℝ) : ℂ)) := fun n => by
      have hf : ContDiff ℝ n (f : E2 → ℝ) := f.contDiff (n := n)
      have hc : ContDiff ℝ n (fun t : ℝ => (t : ℂ)) :=
        ContinuousLinearMap.contDiff (n := n) Complex.ofRealCLM
      have h := hc.comp hf
      simpa only [Function.comp_def] using h
    have hρ_supp : tsupport (fun y : E2 => ((f y : ℝ) : ℂ)) ⊆
        Work.EllipticEst.InteriorRegularity.stripE := by
      have h1 : tsupport (fun y : E2 => ((f y : ℝ) : ℂ)) = tsupport (f : E2 → ℝ) := by
        simp only [tsupport]
        congr 1
        ext y
        simp only [Function.mem_support, ne_eq, Complex.ofReal_eq_zero]
      rw [h1, ContDiffBump.tsupport_eq, hrOut]
      rw [show closedBall x₀ (r + δ) = cthickening δ (closedBall x₀ r) from by
        rw [cthickening_closedBall hδpos.le hrpos.le x₀, add_comm]]
      exact hδsub
    have hρ_compact : HasCompactSupport (fun y : E2 => ((f y : ℝ) : ℂ)) := by
      have h := f.hasCompactSupport.comp_left (g := fun t : ℝ => (t : ℂ)) Complex.ofReal_zero
      simpa only [Function.comp_def, Complex.ofRealCLM_apply] using h
    have hsplit : (fun x : E2 => ((f x : ℝ) : ℂ) * (Real.tan (x 1) : ℂ))
        = (fun x : E2 => ((f x : ℝ) : ℂ)) * (fun x : E2 => (Real.tan (x 1) : ℂ)) := by
      funext x
      rw [Pi.mul_apply]
    refine ⟨fun x : E2 => ((f x : ℝ) : ℂ) * (Real.tan (x 1) : ℂ), ?_, ?_, ?_⟩
    · intro n
      rw [hsplit, contDiff_iff_contDiffAt]
      intro x
      by_cases hx : x ∈ Work.EllipticEst.InteriorRegularity.stripE
      · have hx1 : x 1 ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) := by
          have h := hx
          simp only [Work.EllipticEst.InteriorRegularity.stripE, Set.mem_setOf_eq] at h
          exact ⟨by linarith [h.1, Real.pi_pos], by linarith [h.2]⟩
        have htan : ContDiffAt ℝ n (fun y : E2 => (Real.tan (y 1) : ℂ)) x := by
          have h2 : ContDiffAt ℝ n (fun y : E2 => y 1) x := by fun_prop
          have h1 : ContDiffAt ℝ n Real.tan (x 1) :=
            Real.contDiffAt_tan.mpr (Real.cos_pos_of_mem_Ioo hx1).ne'
          have h3 : ContDiffAt ℝ n (fun z : ℝ => (z : ℂ)) (Real.tan (x 1)) :=
            Complex.ofRealCLM.contDiff.contDiffAt
          have h4 := h3.comp x (h1.comp x h2)
          simpa only [Function.comp_def, Complex.ofRealCLM_apply] using h4
        have h5 := (hρ_smooth n).contDiffAt.mul htan
        exact h5
      · have hx' : x ∉ tsupport (fun y : E2 => ((f y : ℝ) : ℂ)) :=
          fun h => hx (hρ_supp h)
        have hmem : (tsupport (fun y : E2 => ((f y : ℝ) : ℂ)))ᶜ ∈ 𝓝 x :=
          (isClosed_tsupport _).isOpen_compl.mem_nhds hx'
        have hev : (fun y : E2 => ((f y : ℝ) : ℂ)) =ᶠ[𝓝 x] 0 := by
          filter_upwards [hmem] with y hy
          exact image_eq_zero_of_notMem_tsupport
            (f := fun y : E2 => ((f y : ℝ) : ℂ)) hy
        have hevtt : (fun y : E2 => ((f y : ℝ) : ℂ) * (Real.tan (y 1) : ℂ))
            =ᶠ[𝓝 x] 0 := by
          filter_upwards [hev] with y hy
          simp [hy]
        exact (contDiffAt_const (c := (0 : ℂ))).congr_of_eventuallyEq hevtt
    · rw [hsplit]
      exact HasCompactSupport.mul_right hρ_compact
    · intro x hx
      have hxmem : x ∈ Metric.closedBall x₀ f.rIn := by
        rw [Metric.mem_closedBall, hrIn]
        rw [Metric.mem_ball] at hx
        exact le_of_lt hx
      have h1 : (f x : ℝ) = 1 := f.one_of_mem_closedBall hxmem
      simp only [h1, Complex.ofReal_one, one_mul]

end Work.EllipticEst.InteriorRegularity.Q0
