import Mathlib

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

open Filter
open scoped Topology

namespace Work.PTGeometric

/-- A `C^n` open partial homeomorphism of a real normed space (`n ≠ 0`) has a surjective Fréchet
derivative at every point of its target: the derivative of `e` at `e.symm y` is a left inverse of
`fderiv ℝ (⇑e.symm) y` by the chain rule applied to `e.symm ∘ e = id`. -/
lemma surjective_fderiv_symm_of_contDiffOn
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] {n : WithTop ℕ∞} (hn : n ≠ 0)
    (e : OpenPartialHomeomorph X X)
    (h1 : ContDiffOn ℝ n (⇑e) e.source) (h2 : ContDiffOn ℝ n (⇑e.symm) e.target)
    {y : X} (hy : y ∈ e.target) :
    HasFDerivAt (⇑e.symm) (fderiv ℝ (⇑e.symm) y) y ∧
      Function.Surjective (fderiv ℝ (⇑e.symm) y) := by
  have hdy : DifferentiableAt ℝ (⇑e.symm) y :=
    (h2.differentiableOn hn).differentiableAt (e.open_target.mem_nhds hy)
  refine ⟨hdy.hasFDerivAt, ?_⟩
  let x : X := ⇑e.symm y
  have hy' : y ∈ e.symm.source := by rwa [e.symm_source]
  have hx_src : x ∈ e.source := by
    simpa only [x, OpenPartialHomeomorph.symm_target] using e.symm.map_source hy'
  have hxy : ⇑e x = y := e.right_inv hy
  have hdx : DifferentiableAt ℝ (⇑e) x :=
    (h1.differentiableOn hn).differentiableAt (e.open_source.mem_nhds hx_src)
  have h2' : HasFDerivAt (⇑e.symm) (fderiv ℝ (⇑e.symm) (⇑e x)) (⇑e x) := by
    rw [hxy]; exact hdy.hasFDerivAt
  have hcomp : HasFDerivAt ((⇑e.symm) ∘ (⇑e))
      ((fderiv ℝ (⇑e.symm) (⇑e x)) ∘SL (fderiv ℝ (⇑e) x)) x :=
    h2'.comp x hdx.hasFDerivAt
  have hev : ((⇑e.symm) ∘ (⇑e)) =ᶠ[𝓝 x] id := by
    filter_upwards [e.open_source.mem_nhds hx_src] with z hz
    exact e.left_inv hz
  have hcomp_id : HasFDerivAt id
      ((fderiv ℝ (⇑e.symm) (⇑e x)) ∘SL (fderiv ℝ (⇑e) x)) x :=
    hcomp.congr_of_eventuallyEq hev.symm
  have hleft : (fderiv ℝ (⇑e.symm) (⇑e x)) ∘SL (fderiv ℝ (⇑e) x) = 1 :=
    hcomp_id.unique (hasFDerivAt_id x)
  have hsurj : Function.Surjective (fderiv ℝ (⇑e.symm) (⇑e x)) := by
    intro z
    exact ⟨(fderiv ℝ (⇑e) x) z, by
      rw [← ContinuousLinearMap.comp_apply, hleft]
      rfl⟩
  rw [← hxy]
  exact hsurj

end Work.PTGeometric
