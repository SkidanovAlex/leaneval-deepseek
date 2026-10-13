import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Normed.Order.Lattice
import Submission.Work.FTS.Regularity.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open Filter Topology

namespace Work.FTS.Regularity

theorem dzProfFullZero {α S : ℝ} {A B : ℝ → ℝ} {g : ℝ → ℝ → ℝ → ℝ}
    (h : RegPkg α S A B g) :
    ∃ L : ℝ, 0 < L ∧ ∀ z θ τ : ℝ, L < z → θ ∈ Work.Spaces.Iθ → τ ∈ Set.Icc 0 S →
      deriv (fun z' => profFull α g z' θ τ) z = 0 := by
  obtain ⟨L, hLpos, hL⟩ := h.hsupp
  refine ⟨L, hLpos, fun z θ τ hz _ hτ => ?_⟩
  have hev : (fun z' => profFull α g z' θ τ) =ᶠ[𝓝 z] (fun _ => (0 : ℝ)) := by
    filter_upwards [isOpen_Ioi.mem_nhds (show z ∈ Set.Ioi L from hz)] with z' hz'
    exact hL τ hτ z' θ hz'.le
  rw [hev.deriv_eq]
  simp

end Work.FTS.Regularity
