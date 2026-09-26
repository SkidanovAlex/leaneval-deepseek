/-
# Gluing two charts with different centres

`Work.LayerCont.exists_mdifferentiableOn_glue` (`GlueBasic.lean`) is the algebraic step of the
gluing: two holomorphic functions on two open sets that agree on the intersection glue.  The
obligation it leaves is the *agreement*, and that is the identity theorem.

`Work.LayerCont.FarTail.eqOn_of_mdifferentiableOn_ball_of_eqOn` supplies it for two charts with the
**same centre**.  Here we prove the general form — two holomorphic functions on a *preconnected*
open set that agree on a non-empty open subset agree everywhere — and apply it to close the first
genuine gluing case: two charts whose balls have different centres.

The only geometric input is `IsPreconnected (B₀ ∩ B₁)`, which holds because hyperbolic balls are
Euclidean discs (`work in progress`: discharge it by `UpperHalfPlane.image_coe_ball` + convexity of
the intersection of two discs).
-/
import Mathlib
import Submission.Work.LayerCont.GlueBasic
import Submission.Work.LayerCont.FarTail.Transfer

set_option linter.unusedVariables false

noncomputable section

open UpperHalfPlane MeasureTheory Filter Topology
open scoped Topology Manifold

namespace Work.LayerCont.Glue

open Work.Asymptotics Work.LayerCont

/-- **The identity theorem on a preconnected open set.**  Two holomorphic functions on a
preconnected open `U ⊆ ℍ` which agree on a non-empty open subset `V ⊆ U` agree on all of `U`. -/
theorem eqOn_of_mdifferentiableOn_of_preconnected {U : Set UpperHalfPlane} (hUopen : IsOpen U)
    (hUconn : IsPreconnected U) {F G : UpperHalfPlane → ℂ}
    (hF : MDifferentiableOn (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) F U)
    (hG : MDifferentiableOn (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) G U)
    {V : Set UpperHalfPlane} (hVsub : V ⊆ U) (hVopen : IsOpen V) (hVne : V.Nonempty)
    (hV : Set.EqOn F G V) : Set.EqOn F G U := by
  set W : Set ℂ := (fun z : UpperHalfPlane => (z : ℂ)) '' U with hW
  have hWopen : IsOpen W := by
    rw [hW]; exact Work.LayerCont.FarTail.coe_image_isOpen hUopen
  have hWconn : IsPreconnected W := by
    rw [hW]
    exact hUconn.image (fun z : UpperHalfPlane => (z : ℂ))
      UpperHalfPlane.continuous_coe.continuousOn
  have hdiffF : DifferentiableOn ℂ (F ∘ UpperHalfPlane.ofComplex) W := by
    intro z hz
    obtain ⟨τ, hτ, rfl⟩ := hz
    exact (UpperHalfPlane.mdifferentiableAt_iff.mp
      (hF.mdifferentiableAt (s := U) (hUopen.mem_nhds hτ))).differentiableWithinAt
  have hdiffG : DifferentiableOn ℂ (G ∘ UpperHalfPlane.ofComplex) W := by
    intro z hz
    obtain ⟨τ, hτ, rfl⟩ := hz
    exact (UpperHalfPlane.mdifferentiableAt_iff.mp
      (hG.mdifferentiableAt (s := U) (hUopen.mem_nhds hτ))).differentiableWithinAt
  obtain ⟨v, hv⟩ := hVne
  have hvW : (v : ℂ) ∈ W := ⟨v, hVsub hv, rfl⟩
  have hvimg : (v : ℂ) ∈ (fun z : UpperHalfPlane => (z : ℂ)) '' V := ⟨v, hv, rfl⟩
  have hev : (F ∘ UpperHalfPlane.ofComplex) =ᶠ[𝓝 (v : ℂ)]
      (G ∘ UpperHalfPlane.ofComplex) := by
    filter_upwards [(Work.LayerCont.FarTail.coe_image_isOpen hVopen).mem_nhds hvimg] with z hz
    obtain ⟨w, hw, rfl⟩ := hz
    have hw' : UpperHalfPlane.ofComplex (w : ℂ) = w := by
      apply UpperHalfPlane.ext
      rw [UpperHalfPlane.ofComplex_apply_of_im_pos w.im_pos]
    simp only [Function.comp_apply, hw']
    exact hV hw
  have hEqOn := AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq
    (hdiffF.analyticOnNhd hWopen) (hdiffG.analyticOnNhd hWopen) hWconn hvW hev
  intro τ hτ
  have h := hEqOn ⟨τ, hτ, rfl⟩
  have hτ' : UpperHalfPlane.ofComplex (τ : ℂ) = τ := by
    apply UpperHalfPlane.ext
    rw [UpperHalfPlane.ofComplex_apply_of_im_pos τ.im_pos]
  simpa only [Function.comp_apply, hτ'] using h

/-- **The first gluing case: two charts with different centres.**  If `F` is holomorphic on
`B(c₀,ε₀)`, `G` on `B(c₁,ε₁)`, the intersection is preconnected, and the two agree on a non-empty
open subset of the intersection, then they glue to a holomorphic function on the union. -/
theorem exists_glue_two_balls {c₀ c₁ : UpperHalfPlane} {ε₀ ε₁ : ℝ} {F G : UpperHalfPlane → ℂ}
    (hF : MDifferentiableOn (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) F
      (Metric.ball c₀ ε₀))
    (hG : MDifferentiableOn (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) G
      (Metric.ball c₁ ε₁))
    (hconn : IsPreconnected (Metric.ball c₀ ε₀ ∩ Metric.ball c₁ ε₁))
    {V : Set UpperHalfPlane} (hVsub : V ⊆ Metric.ball c₀ ε₀ ∩ Metric.ball c₁ ε₁)
    (hVopen : IsOpen V) (hVne : V.Nonempty) (hV : Set.EqOn F G V) :
    ∃ K : UpperHalfPlane → ℂ,
      MDifferentiableOn (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) K
        (Metric.ball c₀ ε₀ ∪ Metric.ball c₁ ε₁) ∧
      Set.EqOn K F (Metric.ball c₀ ε₀) ∧ Set.EqOn K G (Metric.ball c₁ ε₁) := by
  have hUopen : IsOpen (Metric.ball c₀ ε₀ ∩ Metric.ball c₁ ε₁) :=
    Metric.isOpen_ball.inter Metric.isOpen_ball
  have hagree : Set.EqOn F G (Metric.ball c₀ ε₀ ∩ Metric.ball c₁ ε₁) :=
    eqOn_of_mdifferentiableOn_of_preconnected hUopen hconn (hF.mono Set.inter_subset_left)
      (hG.mono Set.inter_subset_right) hVsub hVopen hVne hV
  exact Work.LayerCont.exists_mdifferentiableOn_glue Metric.isOpen_ball Metric.isOpen_ball hF hG
    hagree

end Work.LayerCont.Glue
