import Mathlib
import Submission.Work.RPB1a.Nodes
import Submission.Work.RPB1a.jordan_domain_of_loop
import Submission.Work.RPB1a.collar_side
import Submission.Work.RPB1a.discLoopFamily
import Submission.Work.RPB1a.analytic_extension_of_collar
import Submission.Work.RPB1a.curveIsotopy_of_loopFamily
import Submission.Work.RPB1a.exists_homothetic_image_of_division
import Submission.Work.RPB.B1a.loopFamily_chain
import Submission.Work.RPB.B1a.riemannMapNodeSmooth

/-!
# Node B1: `Work.RPB.B1a.exists_curveIsotopy`

Every smooth embedding `γ : Circle → ℂ` is, up to a homothety `lam > 0` and a translation `b`, the
time-`1` curve of a `Work.RPV.CurveIsotopy`, i.e. of an isotopy of embedded area-`π` curves starting
at the unit circle.  This is node B1 of the rectangular-peg route.

The proof is the geometric chain of `Work.RPB.B1chain.loopFamily_chain_of_nodes` — the
smooth-boundary variant of `Work.RPB1a.loopFamily_chain_of_nodes` — applied to the in-house node
instantiations:

* `Work.RPB1a.jordan_domain_of_loop` (N4) and `Work.RPB1a.collar_side` (N4b): the smooth loop bounds
  a Jordan domain and one half of its collar lies inside;
* `Work.RPB.B1a.riemannMapNodeSmooth` (N6, smooth-boundary form): the conformal map of the disc onto
  that domain, extending continuously and injectively to the closed disc — assembled in
  `Submission/Work/RPB/B1a/riemannMapNodeSmooth.lean` from `Work.RPB.B1a.riemannMap_exists` (the
  ported Riemann-mapping result) and `Work.RPB.B1a.caratheodory_boundary_of_smooth`;
* `Work.RPB1a.analytic_extension_of_collar` (N7): the Schwarz-reflection extension across the
  analytic boundary;
* `Work.RPB1a.discLoopFamily` (N8): the level circles of that extension.

The two normalisation steps are `Work.RPB1a.curveIsotopy_of_loopFamily` (area `π` and start at the
unit circle) and `Work.RPB1a.exists_homothetic_image_of_division` (the homothety-translation).

Note this file deliberately does **not** import `Submission.Work.RPB1a.NodeHypotheses` or
`Held`: the node instances are supplied here directly from the individual node files, so that the
import closure contains no placeholder.
-/

open Complex Set Metric
open scoped ContDiff Real

set_option autoImplicit false

noncomputable section

namespace Work.RPB.B1a

theorem exists_curveIsotopy (γ : Circle → ℂ) (hγ : Work.RPV.IsSmoothJordan γ) :
    ∃ CI : Work.RPV.CurveIsotopy, ∃ (lam : ℝ) (b : ℂ), 0 < lam ∧
      ∀ t, CI.c 1 t ∈ (fun z => (lam : ℂ) * z + b) '' Set.range γ := by
  have hN4 : Work.RPB1a.JordanDomainNode :=
    fun v hv => Work.RPB1a.jordan_domain_of_loop v hv
  have hN4b : Work.RPB1a.CollarSideNode :=
    fun v D hDo hDfr hDdisj hDext Γ ρ hρ0 hρ1 hΓc hΓi hΓo hΓcirc =>
      Work.RPB1a.collar_side v D hDo hDfr hDdisj hDext Γ ρ hρ0 hρ1 hΓc hΓi hΓo hΓcirc
  have hN6 : RiemannMapNodeSmooth := riemannMapNodeSmooth
  have hN7 : Work.RPB1a.ReflectionNode :=
    fun v hv D hDo hDfr hDdisj Γ ρ hρ0 hρ1 hΓd hΓi hΓd' hΓcirc hin hout Φ hΦc hΦd hΦi hΦim hΦs =>
      Work.RPB1a.analytic_extension_of_collar v hv D hDo hDfr hDdisj Γ ρ hρ0 hρ1 hΓd hΓi hΓd'
        hΓcirc hin hout Φ hΦc hΦd hΦi hΦim hΦs
  have hN8 : Work.RPB1a.LevelCirclesNode :=
    fun F R hR hFd hFi hFd' a ha hFa => Work.RPB1a.discLoopFamily F R hR hFd hFi hFd' a ha hFa
  obtain ⟨a₀, F0, e, ha₀, _he, c, hc, hc0, hc1⟩ :=
    Work.RPB.B1chain.loopFamily_chain_of_nodes hN4 hN4b hN6 hN7 hN8 γ hγ
  obtain ⟨CI, lam₁, hlam₁, hCI⟩ := Work.RPB1a.curveIsotopy_of_loopFamily c hc hc0
  obtain ⟨lam, hlam, b, hb⟩ := Work.RPB1a.exists_homothetic_image_of_division γ hlam₁ ha₀ F0 e
  exact ⟨CI, lam, b, hlam, fun t => by rw [hCI t, hc1 t]; exact hb t⟩

end Work.RPB.B1a
