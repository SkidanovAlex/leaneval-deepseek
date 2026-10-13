import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Normed.Order.Lattice
import Submission.Work.FTS.Apriori.Limit.Defs
import Submission.Work.FTS.Apriori.Limit.SlotCalc
import Submission.Work.FTS.Apriori.Limit.TestQClosure
import Submission.Work.FTS.Apriori.Limit.SupportBox
import Submission.Work.FTS.LocData.SmoothChain

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology ENNReal
open MeasureTheory Set Filter
namespace Work.FTS.Apriori.Limit
set_option autoImplicit false
open Work.FTS.LocData (SmoothQuad)

/-! ## Small vanishing lemmas for the partial derivatives -/

theorem pz_eq_zero_of_forall_lt {W : ℝ → ℝ → ℝ} {A : ℝ} (hA : ∀ z θ, z < A → W z θ = 0) :
    ∀ z θ, z < A → Work.Spaces.pz W z θ = 0 := by
  intro z θ hz
  have hev : (fun z' => W z' θ) =ᶠ[𝓝 z] (fun _ => (0 : ℝ)) := by
    filter_upwards [Iio_mem_nhds hz] with z' hz'
    exact hA z' θ hz'
  rw [Work.Spaces.pz, Filter.EventuallyEq.deriv_eq hev]
  simp

theorem pz_eq_zero_of_forall_gt {W : ℝ → ℝ → ℝ} {B : ℝ} (hB : ∀ z θ, B < z → W z θ = 0) :
    ∀ z θ, B < z → Work.Spaces.pz W z θ = 0 := by
  intro z θ hz
  have hev : (fun z' => W z' θ) =ᶠ[𝓝 z] (fun _ => (0 : ℝ)) := by
    filter_upwards [Ioi_mem_nhds hz] with z' hz'
    exact hB z' θ hz'
  rw [Work.Spaces.pz, Filter.EventuallyEq.deriv_eq hev]
  simp

theorem pz_eq_zero_of_forall_theta_lt {W : ℝ → ℝ → ℝ} {C : ℝ}
    (hC : ∀ z θ, θ < C → W z θ = 0) : ∀ z θ, θ < C → Work.Spaces.pz W z θ = 0 := by
  intro z θ hθ
  rw [Work.Spaces.pz]
  rw [show (fun z' => W z' θ) = fun _ => (0 : ℝ) from funext (fun z' => hC z' θ hθ)]
  simp

theorem pz_eq_zero_of_forall_theta_gt {W : ℝ → ℝ → ℝ} {D : ℝ}
    (hD : ∀ z θ, D < θ → W z θ = 0) : ∀ z θ, D < θ → Work.Spaces.pz W z θ = 0 := by
  intro z θ hθ
  rw [Work.Spaces.pz]
  rw [show (fun z' => W z' θ) = fun _ => (0 : ℝ) from funext (fun z' => hD z' θ hθ)]
  simp

theorem pth_eq_zero_of_forall_theta_lt {W : ℝ → ℝ → ℝ} {C : ℝ}
    (hC : ∀ z θ, θ < C → W z θ = 0) : ∀ z θ, θ < C → Work.Spaces.pth W z θ = 0 := by
  intro z θ hθ
  have hev : (fun θ' => W z θ') =ᶠ[𝓝 θ] (fun _ => (0 : ℝ)) := by
    filter_upwards [Iio_mem_nhds hθ] with θ' hθ'
    exact hC z θ' hθ'
  rw [Work.Spaces.pth, Filter.EventuallyEq.deriv_eq hev]
  simp

theorem pth_eq_zero_of_forall_theta_gt {W : ℝ → ℝ → ℝ} {D : ℝ}
    (hD : ∀ z θ, D < θ → W z θ = 0) : ∀ z θ, D < θ → Work.Spaces.pth W z θ = 0 := by
  intro z θ hθ
  have hev : (fun θ' => W z θ') =ᶠ[𝓝 θ] (fun _ => (0 : ℝ)) := by
    filter_upwards [Ioi_mem_nhds hθ] with θ' hθ'
    exact hD z θ' hθ'
  rw [Work.Spaces.pth, Filter.EventuallyEq.deriv_eq hev]
  simp

