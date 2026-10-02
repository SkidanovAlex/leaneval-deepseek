import Mathlib
import Submission.Work.Surgery.Boundary

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The boundary of a manifold with boundary is a smooth manifold

This file proves `Work.Surgery.bnd_isManifold`: for a `C^∞` manifold `M` with boundary modelled on
the half-space `EuclideanHalfSpace (n + 1)`, the boundary

`∂M = (𝓡∂ (n + 1)).boundary M`

endowed with the preferred atlas `Work.Surgery.boundaryChartedSpace` (whose charts are the
restrictions of the extended charts of `M`, followed by the deletion of the first coordinate) is a
smooth `n`-manifold, modelled on the boundaryless model `𝓡 n` on `EuclideanSpace ℝ (Fin n)`.

## The argument

`IsManifold.mk`-style: by `isManifold_of_contDiffOn` it suffices to check that every transition
`(boundaryChartAt x).symm ≫ₕ boundaryChartAt y` between two boundary charts is `C^∞` on its source.
Unfolding the formulas `Work.Surgery.boundaryChartAt_apply` and `Work.Surgery.boundaryChartAt_symm`
shows that this transition is

`w ↦ tailCLM n ((extChartAt 𝓡∂ y.1) ((extChartAt 𝓡∂ x.1).symm (consZeroCLM n w)))`,

i.e. the composition of the smooth transition `(extChartAt y.1) ∘ (extChartAt x.1).symm` of the
ambient charts (`contDiffOn_extChartAt_comp_symm`) with the linear maps `consZeroCLM n` (insert a
zero) and `tailCLM n` (delete the first coordinate); the maps-to condition is exactly the statement
that a boundary point of `M` is sent to a boundary point, read in charts.
-/

open scoped Manifold Topology ContDiff
open Function

namespace Work.Surgery

variable {n : ℕ}

section Helpers

variable {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace (n + 1)) M]
    [IsManifold (𝓡∂ (n + 1)) (∞ : WithTop ℕ∞) M]

/-- **The transition between two extended charts of `M` is smooth.**  The composite
`(extChartAt 𝓡∂ y) ∘ (extChartAt 𝓡∂ x).symm` (a map between the model space
`EuclideanSpace ℝ (Fin (n+1))` and itself) is `C^∞` on `(extChartAt 𝓡∂ x).target ∩
(extChartAt 𝓡∂ x).symm ⁻¹' (chartAt _ y).source`. -/
theorem contDiffOn_extChartAt_comp_symm (x y : M) :
    ContDiffOn ℝ (∞ : WithTop ℕ∞)
      (fun z => extChartAt (𝓡∂ (n + 1)) y ((extChartAt (𝓡∂ (n + 1)) x).symm z))
      ((extChartAt (𝓡∂ (n + 1)) x).target ∩
        (extChartAt (𝓡∂ (n + 1)) x).symm ⁻¹' (chartAt (EuclideanHalfSpace (n + 1)) y).source) := by
  rw [← contMDiffOn_iff_contDiffOn]
  have h1 := contMDiffOn_extChartAt_symm (I := 𝓡∂ (n + 1)) (x := x) (n := (∞ : WithTop ℕ∞))
  have h2 := contMDiffOn_extChartAt (I := 𝓡∂ (n + 1)) (x := y) (n := (∞ : WithTop ℕ∞))
  exact h2.comp' h1

/-- **The formula for a transition of boundary charts.**  On the source of the composite partial
homeomorphism `(boundaryChartAt x).symm ≫ₕ boundaryChartAt y`, its value at `w` is obtained by
reading `w` in the chart of `M` at `x` (reinserting a zero first coordinate), and expressing the
result in the chart of `M` at `y`, then deleting the first coordinate. -/
theorem boundaryChartAt_trans_apply (x y : (𝓡∂ (n + 1)).boundary M) {w : EuclideanSpace ℝ (Fin n)}
    (hw : w ∈ ((boundaryChartAt x).symm.trans (boundaryChartAt y)).source) :
    ((boundaryChartAt x).symm.trans (boundaryChartAt y)) w
      = tailCLM n (extChartAt (𝓡∂ (n + 1)) y.1
          ((extChartAt (𝓡∂ (n + 1)) x.1).symm (consZeroCLM n w))) := by
  rw [OpenPartialHomeomorph.trans_apply]
  rw [OpenPartialHomeomorph.trans_source, OpenPartialHomeomorph.symm_source] at hw
  obtain ⟨hw1, hw2⟩ := hw
  rw [Set.mem_preimage] at hw2
  rw [boundaryChartAt_apply y _ hw2]
  rw [boundaryChartAt_symm x w hw1]

/-- **The transition between two boundary charts is smooth.** -/
theorem contDiffOn_boundary_transition (x y : (𝓡∂ (n + 1)).boundary M) :
    ContDiffOn ℝ (∞ : WithTop ℕ∞)
      (fun w => ((boundaryChartAt x).symm.trans (boundaryChartAt y)) w)
      ((boundaryChartAt x).symm.trans (boundaryChartAt y)).source := by
  set f := (boundaryChartAt x).symm.trans (boundaryChartAt y) with hf
  -- inserting a zero coordinate lands in the domain of the ambient transition
  have hmaps : Set.MapsTo (consZeroCLM n) f.source
      ((extChartAt (𝓡∂ (n + 1)) x.1).target ∩
        (extChartAt (𝓡∂ (n + 1)) x.1).symm ⁻¹'
          (chartAt (EuclideanHalfSpace (n + 1)) y.1).source) := by
    intro w hw
    rw [hf, OpenPartialHomeomorph.trans_source, OpenPartialHomeomorph.symm_source] at hw
    obtain ⟨hw1, hw2⟩ := hw
    rw [Set.mem_preimage, boundaryChartAt_source] at hw2
    rw [Set.mem_ofPred_eq] at hw2
    rw [boundaryChartAt_symm x w hw1, extChartAt_source] at hw2
    rw [boundaryChartAt_target] at hw1
    rw [Set.mem_ofPred_eq] at hw1
    exact ⟨hw1, hw2⟩
  have hG := contDiffOn_extChartAt_comp_symm (n := n) (M := M) x.1 y.1
  have h1 : ContDiffOn ℝ (∞ : WithTop ℕ∞) (fun w => extChartAt (𝓡∂ (n + 1)) y.1
      ((extChartAt (𝓡∂ (n + 1)) x.1).symm (consZeroCLM n w))) f.source :=
    hG.comp ((consZeroCLM n).contDiff.contDiffOn) hmaps
  have h2 : ContDiffOn ℝ (∞ : WithTop ℕ∞) (fun w => tailCLM n
      (extChartAt (𝓡∂ (n + 1)) y.1
        ((extChartAt (𝓡∂ (n + 1)) x.1).symm (consZeroCLM n w)))) f.source :=
    (tailCLM n).contDiff.contDiffOn.comp h1 (fun _ _ => Set.mem_univ _)
  exact h2.congr (fun w hw => boundaryChartAt_trans_apply x y (by rwa [hf] at hw))

end Helpers

/-- **The boundary of a smooth manifold with boundary is a smooth manifold.**  With the preferred
charted-space structure `Work.Surgery.boundaryChartedSpace` on `∂M`, the boundary of a `C^∞`
`(n+1)`-manifold with boundary is a `C^∞` `n`-manifold modelled on `EuclideanSpace ℝ (Fin n)`. -/
theorem bnd_isManifold (n : ℕ) {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace (n + 1)) M]
    [IsManifold (modelWithCornersEuclideanHalfSpace (n + 1)) (∞ : WithTop ℕ∞) M] :
    @IsManifold ℝ _ (EuclideanSpace ℝ (Fin n)) _ _ (EuclideanSpace ℝ (Fin n)) _
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) (∞ : WithTop ℕ∞)
      ((modelWithCornersEuclideanHalfSpace (n + 1)).boundary M) _
      (Work.Surgery.boundaryChartedSpace (n := n) (M := M)) := by
  let : ChartedSpace (EuclideanSpace ℝ (Fin n))
      ((𝓡∂ (n + 1)).boundary M) :=
    Work.Surgery.boundaryChartedSpace (n := n) (M := M)
  refine isManifold_of_contDiffOn (𝓘(ℝ, EuclideanSpace ℝ (Fin n))) (∞ : WithTop ℕ∞)
    ((𝓡∂ (n + 1)).boundary M) ?_
  intro e e' he he'
  obtain ⟨x, rfl⟩ := he
  obtain ⟨y, rfl⟩ := he'
  refine (contDiffOn_boundary_transition x y).congr_mono (fun w hw => ?_) (fun w hw => ?_)
  · simp [modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm]
  · simpa using hw

end Work.Surgery
