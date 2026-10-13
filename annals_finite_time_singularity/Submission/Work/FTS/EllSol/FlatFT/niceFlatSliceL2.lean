import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Order.CompletePartialOrder
import Mathlib.Topology.UniformSpace.Uniformizable
import Submission.Work.FTS.EllSol.FlatFT.Defs
import Submission.Work.Spaces.Defs
import Submission.Work.Spaces.CurrySmooth
import Submission.Work.FTS.EllipticEst.RegQ.pthU_slot_alg

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllSol.FlatFT

theorem niceFlatSliceL2 (g : ℝ → ℝ → ℝ) (hg : Work.FTS.EllSol.FlatFT.NiceFlat g) {θ₁ : ℝ}
    (hθ₁ : θ₁ ∈ Set.Ioo 0 (Real.pi / 2)) :
    MeasureTheory.Integrable (fun z : ℝ => (g z θ₁) ^ 2) ∧
      MeasureTheory.Integrable (fun z : ℝ => (Work.Spaces.pth g z θ₁) ^ 2) := by
  obtain ⟨hsm, h0, hπ, N, hN⟩ := hg
  have hU : IsOpen ((Set.univ : Set ℝ) ×ˢ Set.Ioo 0 (Real.pi / 2)) :=
    isOpen_univ.prod isOpen_Ioo
  -- a point outside `[-N,N]` satisfies `N < |z|`, where `g` vanishes identically
  have hmem : ∀ z : ℝ, z ∉ Set.Icc (-N) N → N < |z| := by
    intro z hz
    exact not_le.mp (fun h => hz (abs_le.mp h))
  -- the `z`-slices of `g` and of `∂_θ g` at the fixed interior angle `θ₁` are continuous
  have hslice_cont : Continuous (fun z : ℝ => g z θ₁) := by
    have h1 : ContDiffOn ℝ 2 (fun z : ℝ => (z, θ₁)) Set.univ := by fun_prop
    have h2 := hsm.comp h1 (fun z _ => ⟨trivial, hθ₁⟩)
    have h3 : ContDiffOn ℝ 2 (fun z : ℝ => g z θ₁) Set.univ := by
      simpa [Function.comp_def, Function.uncurry] using h2
    simpa [continuousOn_univ] using h3.continuousOn
  have hpth_cont : Continuous (fun z : ℝ => Work.Spaces.pth g z θ₁) := by
    have hfd : ContinuousOn
        (fun p : ℝ × ℝ =>
          fderivWithin ℝ (Function.uncurry g) ((Set.univ : Set ℝ) ×ˢ Set.Ioo 0 (Real.pi / 2)) p)
        ((Set.univ : Set ℝ) ×ˢ Set.Ioo 0 (Real.pi / 2)) :=
      hsm.continuousOn_fderivWithin hU.uniqueDiffOn (by norm_num)
    have hcomp : Continuous
        ((fun p : ℝ × ℝ =>
            fderivWithin ℝ (Function.uncurry g) ((Set.univ : Set ℝ) ×ˢ Set.Ioo 0 (Real.pi / 2)) p)
          ∘ (fun z : ℝ => (z, θ₁))) :=
      hfd.comp_continuous (by fun_prop) (fun z => ⟨trivial, hθ₁⟩)
    have hcl : Continuous (fun z : ℝ =>
        fderivWithin ℝ (Function.uncurry g) ((Set.univ : Set ℝ) ×ˢ Set.Ioo 0 (Real.pi / 2))
          (z, θ₁) (0, 1)) :=
      hcomp.clm_apply continuous_const
    refine hcl.congr (fun z => ?_)
    have hd : DifferentiableAt ℝ (Function.uncurry g) (z, θ₁) :=
      (hsm.differentiableOn (by norm_num)).differentiableAt (hU.mem_nhds ⟨trivial, hθ₁⟩)
    rw [fderivWithin_of_isOpen hU ⟨trivial, hθ₁⟩]
    exact (Work.Spaces.pth_eq_fderiv hd).symm
  -- both slices are supported in `[-N,N]`
  refine ⟨?_, ?_⟩
  · exact ((hslice_cont.pow 2)).integrable_of_hasCompactSupport
      (HasCompactSupport.intro (K := Set.Icc (-N) N) isCompact_Icc
        (fun z hz => by simp [hN z θ₁ (hmem z hz)]))
  · exact ((hpth_cont.pow 2)).integrable_of_hasCompactSupport
      (HasCompactSupport.intro (K := Set.Icc (-N) N) isCompact_Icc
        (fun z hz => by
          simp [Work.Spaces.pth, show (fun θ' : ℝ => g z θ') = fun _ : ℝ => (0 : ℝ) from
            funext (fun θ' => hN z θ' (hmem z hz))]))

end Work.FTS.EllSol.FlatFT
