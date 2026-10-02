import Mathlib
import Submission.Work.Tubular.modelClassPunct_fibre_span_top
import Submission.Work.Thom.ChartOrientation

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1600000

/-!
# The local Thom class restricts to a generator on every fibre

`Work.Thom.localThomOfChart Z n e i W hW` is by construction the pullback of the punctured model
class `Work.Thom.Mpun n ↥W` along the chart homeomorphism
`Work.Thom.chartHomeo Z n e i W hW : ↥(Z.proj ⁻¹' W) ≃ₜ ↥W × ℝⁿ`.  Its fibrewise-generator
property — the restriction to the fibre over a point `b ∈ W` generates the relative cohomology of
the fibre pair `(Z.proj ⁻¹' {b}, (Z.proj ⁻¹' {b}) ∩ Z⁰)` — therefore follows from the corresponding
property of the model class (`Work.Tubular.modelClassPunct_fibre_span_top`) transported along the
homeomorphism (`Work.Tubular.span_singleton_map_eq_top`, using
`Work.Thom.bijective_relCohMap_of_homeomorphA`), after restricting the class from `W` to the
singleton `{b}` by `Work.Thom.localThomOfChart_restrict`.

The restriction to the singleton is not cosmetic: the span of `Mpun n ↥W` itself is *not* `⊤` for a
general base `W` (over `B = S¹` the relative group `H¹(B × ℝ, B × (ℝ∖0))` has rank `2`), so the
reduction of the base to a point has to happen before the model class enters.
-/

open CategoryTheory Limits
open scoped Topology

namespace Work.Tubular

noncomputable section

theorem localThomOfChart_fibre_span_top {B : Type} [TopologicalSpace B] {F : Type}
    [NormedAddCommGroup F] [NormedSpace ℝ F] {ι : Type}
    (Z : Work.TangentClasses.RealBundle B F ι) (n : ℕ)
    (e : F ≃L[ℝ] EuclideanSpace ℝ (Fin n)) (i : ι) (W : Set B) (hW : W ⊆ Z.baseSet i)
    (b : ↥W) :
    Submodule.span ℤ
      { ((Work.Cohomology.pdCohMap (TopCat.of Z.TotalSpace) (Work.Thom.zeroComplement Z)
            (Z.proj ⁻¹' W) (Z.proj ⁻¹' ({(b : B)} : Set B)) (Set.preimage_mono (by
              intro y hy
              rw [Set.mem_singleton_iff] at hy
              exact hy ▸ b.2)) n).hom
          (Work.Thom.localThomOfChart Z n e i W hW).τ) }
      = ⊤ := by
  -- the singleton `{b}` lies in the chart `baseSet i`
  have hsing : ({(b : B)} : Set B) ⊆ W := by
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    exact hy ▸ b.2
  have hsub : ({(b : B)} : Set B) ⊆ Z.baseSet i := fun y hy => hW (hsing hy)
  -- restrict the local Thom class of the chart piece `W` to the fibre over `b`
  have hgoal :
      (Work.Cohomology.pdCohMap (TopCat.of Z.TotalSpace) (Work.Thom.zeroComplement Z)
          (Z.proj ⁻¹' W) (Z.proj ⁻¹' ({(b : B)} : Set B)) (Set.preimage_mono (by
            intro y hy
            rw [Set.mem_singleton_iff] at hy
            exact hy ▸ b.2)) n).hom (Work.Thom.localThomOfChart Z n e i W hW).τ
        = (Work.Thom.localThomOfChart Z n e i ({(b : B)} : Set B) hsub).τ :=
    Work.Thom.localThomOfChart_restrict Z n e i ({(b : B)} : Set B) W hsub hW hsing
  rw [hgoal, Work.Thom.localThomOfChart_tau]
  -- the class over the singleton is the chart pullback of the model class; transport the generator
  refine span_singleton_map_eq_top _ ?_ (Work.Thom.Mpun n ↥({(b : B)} : Set B)) ?_
  · exact (Work.Thom.bijective_relCohMap_of_homeomorphA _ _
      (Work.Thom.chartHomeo Z n e i ({(b : B)} : Set B) hsub)
      (Work.Thom.chartHomeo_mem_punct Z n e i ({(b : B)} : Set B) hsub) ℤ n).2
  · rw [← Work.Thom.Mpun_natural n B ({(b : B)} : Set B)]
    exact modelClassPunct_fibre_span_top n B (b : B)

end

end Work.Tubular
