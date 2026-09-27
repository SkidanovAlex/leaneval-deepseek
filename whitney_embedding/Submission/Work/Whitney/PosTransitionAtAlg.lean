import Mathlib
import Submission.Work.Whitney.ArcFraming

/-!
# Algebraic properties of `PosTransitionAt`

`PosTransitionAt e f x` (see `Submission/Work/Whitney/ArcFraming.lean`) is the positivity of the
determinant of the differential, at `e x`, of the chart transition `f ∘ e.symm`.  This file
collects the two structural facts that make it a "sign of the transition" relation:

* `posTransitionAt_comm` : it is symmetric;
* `posTransitionAt_trans_iff`, `posTransitionAt_trans_iff'` : at a point lying in the sources of
  three smooth charts it is transitive, moreover it may be "multiplied" by a known positive
  transition.

The proofs are the chain rule for the transition cocycle together with the multiplicativity of
`LinearMap.det`.
-/

namespace Work.Whitney

open scoped Manifold ContDiff
open Topology Filter

set_option linter.unusedSectionVars false

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ((⊤ : ℕ∞) : WithTop ℕ∞) M]

/-- The determinant of a composite of continuous linear endomorphisms is the product. -/
lemma det_comp_clm {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (A B : E →L[ℝ] E) : (A.comp B).det = A.det * B.det := by
  rw [ContinuousLinearMap.det, ContinuousLinearMap.det, ContinuousLinearMap.det,
    ContinuousLinearMap.toLinearMap_comp, LinearMap.det_comp]

/-- A chart transition between two smooth charts is differentiable where both are defined. -/
lemma chart_transition_differentiableAt
    {a b : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n))}
    (ha : Work.Whitney.IsSmoothChart a) (hb : Work.Whitney.IsSmoothChart b)
    {x : M} (hx : x ∈ a.source) (hxb : x ∈ b.source) :
    DifferentiableAt ℝ (fun u : EuclideanSpace ℝ (Fin n) => b (a.symm u)) (a x) := by
  have hbC : ContMDiffAt (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
      (𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ((⊤ : ℕ∞) : WithTop ℕ∞) b (a.symm (a x)) := by
    rw [a.left_inv hx]
    exact hb.1.contMDiffAt (b.open_source.mem_nhds hxb)
  have ha_symmC : ContMDiffAt (𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ((⊤ : ℕ∞) : WithTop ℕ∞) a.symm (a x) :=
    ha.2.contMDiffAt (a.open_target.mem_nhds (a.map_source hx))
  exact ((ContMDiffAt.comp (x := a x) hbC ha_symmC).contDiffAt).differentiableAt (by simp)

/-- **The two chart transitions at a common point are inverse up to determinant.**

If `a`, `b` are smooth charts and `x` lies in both sources, then the derivatives at `a x` of
`b ∘ a.symm` and at `b x` of `a ∘ b.symm` are mutually inverse, so their determinants multiply
to `1`. -/
lemma det_transition_mul
    {a b : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n))}
    (ha : Work.Whitney.IsSmoothChart a) (hb : Work.Whitney.IsSmoothChart b)
    {x : M} (hx : x ∈ a.source) (hxb : x ∈ b.source) :
    (fderiv ℝ (fun u : EuclideanSpace ℝ (Fin n) => b (a.symm u)) (a x)).det *
      (fderiv ℝ (fun u : EuclideanSpace ℝ (Fin n) => a (b.symm u)) (b x)).det = 1 := by
  have hHdiff : DifferentiableAt ℝ (fun u : EuclideanSpace ℝ (Fin n) => a (b.symm u)) (b x) :=
    chart_transition_differentiableAt hb ha hxb hx
  have hGdiff : DifferentiableAt ℝ (fun u : EuclideanSpace ℝ (Fin n) => b (a.symm u))
      ((fun u : EuclideanSpace ℝ (Fin n) => a (b.symm u)) (b x)) := by
    show DifferentiableAt ℝ (fun u : EuclideanSpace ℝ (Fin n) => b (a.symm u)) (a (b.symm (b x)))
    rw [b.left_inv hxb]
    exact chart_transition_differentiableAt ha hb hx hxb
  have hGH : (fun u : EuclideanSpace ℝ (Fin n) => b (a.symm (a (b.symm u)))) =ᶠ[𝓝 (b x)] id := by
    have h1 : ∀ᶠ u in 𝓝 (b x), u ∈ b.target := b.open_target.mem_nhds (b.map_source hxb)
    have h2 : ∀ᶠ u in 𝓝 (b x), b.symm u ∈ a.source :=
      (b.continuousAt_symm (b.map_source hxb)).preimage_mem_nhds
        (a.open_source.mem_nhds (by rw [b.left_inv hxb]; exact hx))
    refine (h1.and h2).mono ?_
    intro u hu
    simp only [id_eq]
    rw [a.left_inv hu.2, b.right_inv hu.1]
  have hcomp := fderiv_comp (x := b x) (f := fun u : EuclideanSpace ℝ (Fin n) => a (b.symm u))
    (g := fun u : EuclideanSpace ℝ (Fin n) => b (a.symm u)) hGdiff hHdiff
  have hcomp' : fderiv ℝ (fun u : EuclideanSpace ℝ (Fin n) => b (a.symm (a (b.symm u)))) (b x) =
      (fderiv ℝ (fun u : EuclideanSpace ℝ (Fin n) => b (a.symm u)) (a x)).comp
        (fderiv ℝ (fun u : EuclideanSpace ℝ (Fin n) => a (b.symm u)) (b x)) := by
    simpa [Function.comp_def, b.left_inv hxb] using hcomp
  have hid : fderiv ℝ (fun u : EuclideanSpace ℝ (Fin n) => b (a.symm (a (b.symm u)))) (b x) =
      ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n)) := by
    rw [hGH.fderiv_eq, fderiv_id]
  have h2 := congrArg ContinuousLinearMap.det hcomp'
  rw [hid, det_comp_clm] at h2
  rw [show ContinuousLinearMap.det (ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n))) = 1 from by
    rw [ContinuousLinearMap.det]
    change LinearMap.det (LinearMap.id : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] _) = 1
    rw [LinearMap.det_id]] at h2
  exact h2.symm

/-- **The transition cocycle.**  With three smooth charts through a common point `x`, the
determinant of the `a → b` transition factors through `g`. -/
lemma det_transition_comp
    {a g b : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n))}
    (ha : Work.Whitney.IsSmoothChart a) (hg : Work.Whitney.IsSmoothChart g)
    (hb : Work.Whitney.IsSmoothChart b)
    {x : M} (hxa : x ∈ a.source) (hxg : x ∈ g.source) (hxb : x ∈ b.source) :
    (fderiv ℝ (fun u : EuclideanSpace ℝ (Fin n) => b (a.symm u)) (a x)).det =
      (fderiv ℝ (fun u : EuclideanSpace ℝ (Fin n) => b (g.symm u)) (g x)).det *
        (fderiv ℝ (fun u : EuclideanSpace ℝ (Fin n) => g (a.symm u)) (a x)).det := by
  have hIn : DifferentiableAt ℝ (fun u : EuclideanSpace ℝ (Fin n) => g (a.symm u)) (a x) :=
    chart_transition_differentiableAt ha hg hxa hxg
  have hOut : DifferentiableAt ℝ (fun u : EuclideanSpace ℝ (Fin n) => b (g.symm u))
      ((fun u : EuclideanSpace ℝ (Fin n) => g (a.symm u)) (a x)) := by
    show DifferentiableAt ℝ (fun u : EuclideanSpace ℝ (Fin n) => b (g.symm u)) (g (a.symm (a x)))
    rw [a.left_inv hxa]
    exact chart_transition_differentiableAt hg hb hxg hxb
  have hagree : (fun u : EuclideanSpace ℝ (Fin n) => b (g.symm (g (a.symm u)))) =ᶠ[𝓝 (a x)]
      (fun u : EuclideanSpace ℝ (Fin n) => b (a.symm u)) := by
    have h1 : ∀ᶠ u in 𝓝 (a x), a.symm u ∈ g.source :=
      (a.continuousAt_symm (a.map_source hxa)).preimage_mem_nhds
        (g.open_source.mem_nhds (by rw [a.left_inv hxa]; exact hxg))
    refine h1.mono fun u hu => ?_
    show b (g.symm (g (a.symm u))) = b (a.symm u)
    rw [g.left_inv hu]
  have hcompG : fderiv ℝ (fun u : EuclideanSpace ℝ (Fin n) => b (g.symm (g (a.symm u)))) (a x) =
      (fderiv ℝ (fun u : EuclideanSpace ℝ (Fin n) => b (g.symm u)) (g x)).comp
        (fderiv ℝ (fun u : EuclideanSpace ℝ (Fin n) => g (a.symm u)) (a x)) := by
    have := fderiv_comp (x := a x) (f := fun u : EuclideanSpace ℝ (Fin n) => g (a.symm u))
      (g := fun u : EuclideanSpace ℝ (Fin n) => b (g.symm u)) hOut hIn
    simpa only [Function.comp_def, a.left_inv hxa] using this
  calc (fderiv ℝ (fun u : EuclideanSpace ℝ (Fin n) => b (a.symm u)) (a x)).det
      = (fderiv ℝ (fun u : EuclideanSpace ℝ (Fin n) => b (g.symm (g (a.symm u)))) (a x)).det := by
        rw [hagree.fderiv_eq]
    _ = ((fderiv ℝ (fun u : EuclideanSpace ℝ (Fin n) => b (g.symm u)) (g x)).comp
          (fderiv ℝ (fun u : EuclideanSpace ℝ (Fin n) => g (a.symm u)) (a x))).det := by rw [hcompG]
    _ = _ := by rw [det_comp_clm]

/-- `PosTransitionAt` is symmetric. -/
lemma posTransitionAt_comm
    {a b : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n))}
    (ha : Work.Whitney.IsSmoothChart a) (hb : Work.Whitney.IsSmoothChart b)
    {x : M} (hx : x ∈ a.source) (hxb : x ∈ b.source) :
    (Work.Whitney.PosTransitionAt a b x ↔ Work.Whitney.PosTransitionAt b a x) := by
  have h := det_transition_mul ha hb hx hxb
  rw [Work.Whitney.PosTransitionAt, Work.Whitney.PosTransitionAt]
  constructor
  · intro hA
    rw [eq_inv_of_mul_eq_one_right h]
    exact inv_pos.mpr hA
  · intro hB
    have h' : (fderiv ℝ (fun u : EuclideanSpace ℝ (Fin n) => a (b.symm u)) (b x)).det *
        (fderiv ℝ (fun u : EuclideanSpace ℝ (Fin n) => b (a.symm u)) (a x)).det = 1 := by
      rw [mul_comm]; exact h
    rw [eq_inv_of_mul_eq_one_right h']
    exact inv_pos.mpr hB

/-- At a common point of three smooth charts, a positive transition `a → g` may be cancelled. -/
lemma posTransitionAt_trans_iff
    {a g b : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n))}
    (ha : Work.Whitney.IsSmoothChart a) (hg : Work.Whitney.IsSmoothChart g)
    (hb : Work.Whitney.IsSmoothChart b)
    {x : M} (hxa : x ∈ a.source) (hxg : x ∈ g.source) (hxb : x ∈ b.source)
    (hag : Work.Whitney.PosTransitionAt a g x) :
    (Work.Whitney.PosTransitionAt a b x ↔ Work.Whitney.PosTransitionAt g b x) := by
  have hdet := det_transition_comp ha hg hb hxa hxg hxb
  rw [Work.Whitney.PosTransitionAt] at hag ⊢
  rw [hdet]
  exact mul_pos_iff_of_pos_right hag

/-- At a common point of three smooth charts, a positive transition `g → b` may be cancelled. -/
lemma posTransitionAt_trans_iff'
    {a g b : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n))}
    (ha : Work.Whitney.IsSmoothChart a) (hg : Work.Whitney.IsSmoothChart g)
    (hb : Work.Whitney.IsSmoothChart b)
    {x : M} (hxa : x ∈ a.source) (hxg : x ∈ g.source) (hxb : x ∈ b.source)
    (hgb : Work.Whitney.PosTransitionAt g b x) :
    (Work.Whitney.PosTransitionAt a b x ↔ Work.Whitney.PosTransitionAt a g x) := by
  have hdet := det_transition_comp ha hg hb hxa hxg hxb
  rw [Work.Whitney.PosTransitionAt] at hgb ⊢
  rw [hdet]
  exact mul_pos_iff_of_pos_left hgb

end Work.Whitney
