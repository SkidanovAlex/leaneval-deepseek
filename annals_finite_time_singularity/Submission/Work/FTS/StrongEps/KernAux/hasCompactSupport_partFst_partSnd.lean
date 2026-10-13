import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Topology.UniformSpace.Uniformizable

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.KernAux

/-- The first partial derivative of a compactly supported function again has compact support.

Reason: if `p` is outside the (closed) topological support of `F`, then `F` vanishes on a whole
neighbourhood of `p`, hence so does the slice `s ↦ F (s, p.2)` near `p.1`, so its derivative at
`p.1` vanishes.  Thus the support of `∂₁F` is contained in `tsupport F`. -/
theorem hasCompactSupport_deriv_fst (F : ℝ × ℝ → ℝ) (hF : HasCompactSupport F) :
    HasCompactSupport (fun p : ℝ × ℝ => deriv (fun s : ℝ => F (s, p.2)) p.1) := by
  refine HasCompactSupport.of_support_subset_isCompact hF ?_
  intro p hp
  rw [Function.mem_support] at hp
  by_contra hcon
  refine hp ?_
  have h0 : F =ᶠ[nhds p] 0 := notMem_tsupport_iff_eventuallyEq.mp hcon
  have hcont : ContinuousAt (fun s : ℝ => (s, p.2)) p.1 :=
    continuousAt_id.prodMk continuousAt_const
  have hg : (fun s : ℝ => F (s, p.2)) =ᶠ[nhds p.1] (fun _ => 0) :=
    hcont.tendsto.eventually h0
  rw [hg.deriv_eq, deriv_const]

/-- The second partial derivative of a compactly supported function again has compact support. -/
theorem hasCompactSupport_deriv_snd (F : ℝ × ℝ → ℝ) (hF : HasCompactSupport F) :
    HasCompactSupport (fun p : ℝ × ℝ => deriv (fun t : ℝ => F (p.1, t)) p.2) := by
  refine HasCompactSupport.of_support_subset_isCompact hF ?_
  intro p hp
  rw [Function.mem_support] at hp
  by_contra hcon
  refine hp ?_
  have h0 : F =ᶠ[nhds p] 0 := notMem_tsupport_iff_eventuallyEq.mp hcon
  have hcont : ContinuousAt (fun t : ℝ => (p.1, t)) p.2 :=
    continuousAt_const.prodMk continuousAt_id
  have hg : (fun t : ℝ => F (p.1, t)) =ᶠ[nhds p.2] (fun _ => 0) :=
    hcont.tendsto.eventually h0
  rw [hg.deriv_eq, deriv_const]

theorem hasCompactSupport_partFst_partSnd (F : ℝ × ℝ → ℝ) (hF : HasCompactSupport F) :
    HasCompactSupport (fun p : ℝ × ℝ => deriv (fun s : ℝ => F (s, p.2)) p.1) ∧
    HasCompactSupport (fun p : ℝ × ℝ => deriv (fun t : ℝ => F (p.1, t)) p.2) :=
  ⟨hasCompactSupport_deriv_fst F hF, hasCompactSupport_deriv_snd F hF⟩

end Work.FTS.StrongEps.KernAux
