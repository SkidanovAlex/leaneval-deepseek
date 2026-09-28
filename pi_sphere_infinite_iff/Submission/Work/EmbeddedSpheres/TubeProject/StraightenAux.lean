import Mathlib

/-!
# Auxiliary chart-theoretic facts for straightening a line

This file collects the bookkeeping that the straightening of a curve into a coordinate line needs,
in the vocabulary of Mathlib's `IsManifold.maximalAtlas`:

* `mem_contDiffGroupoid_self_iff` : membership of a partial homeomorphism of the model space in the
  `C^n` groupoid, unfolded into `ContDiffOn` of the map and of its inverse.
* `mem_maximalAtlas_modelWithCornersSelf` : for the model space, the maximal atlas is exactly the
  `C^n` groupoid.
* `contDiffOn_and_symm_of_mem_maximalAtlas_self` : a chart of the model space in the maximal atlas
  is `C^n` with `C^n` inverse.
* `injective_fderiv_of_mem_maximalAtlas_self` : the derivative of such a chart is injective.
* `trans_mem_maximalAtlas_of_mem_groupoid` : composing a chart in the maximal atlas of a manifold
  with an element of the structure groupoid (a `C^n` partial diffeomorphism of the model) gives
  again a chart in the maximal atlas.
* `subRight_mem_contDiffGroupoid` : translations of the model space are smooth (partial)
  diffeomorphisms.
-/

open scoped Manifold ContDiff Topology

open Set Function

namespace Work.EmbeddedSpheres.TubeProject

section SelfModel

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Membership in the `C^n` structure groupoid of the *model space* `E`: a partial homeomorphism of
`E` is in the groupoid exactly when it and its inverse are `C^n` on their source and target. -/
theorem mem_contDiffGroupoid_self_iff (n : ℕ∞ω) (e : OpenPartialHomeomorph E E) :
    e ∈ contDiffGroupoid n (𝓘(ℝ, E)) ↔
      ContDiffOn ℝ n (e : E → E) e.source ∧ ContDiffOn ℝ n (↑e.symm) e.target := by
  rw [contDiffGroupoid, mem_groupoid_of_pregroupoid]
  unfold contDiffPregroupoid
  simp only [ModelWithCorners.range_eq_univ, inter_univ]
  exact Iff.rfl

/-- For the model space `E`, the maximal atlas of the self model is exactly the `C^n` groupoid. -/
theorem mem_maximalAtlas_self_iff (n : ℕ∞ω) (e : OpenPartialHomeomorph E E) :
    e ∈ (contDiffGroupoid n (𝓘(ℝ, E))).maximalAtlas E ↔ e ∈ contDiffGroupoid n (𝓘(ℝ, E)) := by
  constructor
  · intro h
    have h1 : OpenPartialHomeomorph.refl E ∈ atlas E E := by simp
    have h2 := (h _ h1).2
    simpa using h2
  · intro h
    exact StructureGroupoid.mem_maximalAtlas_of_mem_groupoid _ h

/-- For the model space `E`, the maximal atlas of the self model is exactly the `C^n` groupoid. -/
theorem mem_maximalAtlas_modelWithCornersSelf (n : ℕ∞ω) (e : OpenPartialHomeomorph E E) :
    e ∈ IsManifold.maximalAtlas (𝓘(ℝ, E)) n E ↔ e ∈ contDiffGroupoid n (𝓘(ℝ, E)) := by
  rw [IsManifold.maximalAtlas]
  exact mem_maximalAtlas_self_iff n e

/-- A chart of the model space lying in the maximal atlas is `C^n` on its source, and its inverse
is `C^n` on its target. -/
theorem contDiffOn_and_symm_of_mem_maximalAtlas_self (n : ℕ∞ω) (e : OpenPartialHomeomorph E E)
    (he : e ∈ IsManifold.maximalAtlas (𝓘(ℝ, E)) n E) :
    ContDiffOn ℝ n (e : E → E) e.source ∧ ContDiffOn ℝ n (↑e.symm) e.target :=
  (mem_contDiffGroupoid_self_iff n e).1 ((mem_maximalAtlas_modelWithCornersSelf n e).1 he)

/-- The derivative of a chart of the model space lying in the maximal atlas is injective at every
point of its source. -/
theorem injective_fderiv_of_mem_maximalAtlas_self (n : ℕ∞ω) (hn : n ≠ 0)
    (e : OpenPartialHomeomorph E E) (he : e ∈ IsManifold.maximalAtlas (𝓘(ℝ, E)) n E)
    {x : E} (hx : x ∈ e.source) : Function.Injective (fderiv ℝ (e : E → E) x) := by
  obtain ⟨h1, h2⟩ := contDiffOn_and_symm_of_mem_maximalAtlas_self n e he
  have hxe : e x ∈ e.target := e.map_source hx
  have hd1 : DifferentiableAt ℝ (e : E → E) x :=
    (h1.contDiffAt (e.open_source.mem_nhds hx)).differentiableAt hn
  have hd2 : DifferentiableAt ℝ (↑e.symm : E → E) (e x) :=
    (h2.contDiffAt (e.open_target.mem_nhds hxe)).differentiableAt hn
  have heq : ((↑e.symm : E → E) ∘ (e : E → E)) =ᶠ[𝓝 x] id := by
    filter_upwards [e.eventually_left_inverse hx] with y hy using hy
  have hder : fderiv ℝ (↑e.symm) (e x) ∘SL fderiv ℝ (e : E → E) x
      = ContinuousLinearMap.id ℝ E := by
    have h : fderiv ℝ ((↑e.symm : E → E) ∘ (e : E → E)) x = fderiv ℝ (id : E → E) x :=
      Filter.EventuallyEq.fderiv_eq heq
    rw [fderiv_comp x hd2 hd1, fderiv_id] at h
    exact h
  have hzero : ∀ v : E, fderiv ℝ (e : E → E) x v = 0 → v = 0 := by
    intro v hv
    have h := congrArg (fun (L : E →L[ℝ] E) => L v) hder
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply, hv, map_zero] at h
    exact h.symm
  intro v w hvw
  have h1' : fderiv ℝ (e : E → E) x (v - w) = 0 := by rw [map_sub, hvw, sub_self]
  exact sub_eq_zero.mp (hzero (v - w) h1')

end SelfModel

section ChartComposition

variable {H : Type*} [TopologicalSpace H] {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E'] {I : ModelWithCorners 𝕜 E' H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

/-- Composing a chart of the maximal atlas with an element of the structure groupoid (that is, with
a partial diffeomorphism of the model) gives again a chart of the maximal atlas. -/
theorem trans_mem_maximalAtlas_of_mem_groupoid {n : ℕ∞ω} {e : OpenPartialHomeomorph M H}
    {f : OpenPartialHomeomorph H H} (he : e ∈ IsManifold.maximalAtlas I n M)
    (hf : f ∈ contDiffGroupoid n I) : e ≫ₕ f ∈ IsManifold.maximalAtlas I n M := by
  rw [IsManifold.mem_maximalAtlas_iff] at he ⊢
  intro e' he'
  refine ⟨?_, ?_⟩
  · rw [OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm, OpenPartialHomeomorph.trans_assoc]
    exact (contDiffGroupoid n I).trans ((contDiffGroupoid n I).symm hf) (he e' he').1
  · rw [← OpenPartialHomeomorph.trans_assoc]
    exact (contDiffGroupoid n I).trans (he e' he').2 hf

end ChartComposition

section Translation

variable {E : Type*} [NormedAddCommGroup E]

/-- The translation `y ↦ y - z` of the model space, as an open partial homeomorphism with source
and target all of `E`. -/
def subRightOpenPartialHomeomorph (z : E) : OpenPartialHomeomorph E E where
  toFun := fun y => y - z
  invFun := fun y => y + z
  source := univ
  target := univ
  map_source' := by intro x _; trivial
  map_target' := by intro x _; trivial
  left_inv' := by intro x _; simp
  right_inv' := by intro x _; simp
  open_source := isOpen_univ
  open_target := isOpen_univ
  continuousOn_toFun := by fun_prop
  continuousOn_invFun := by fun_prop

@[simp]
theorem subRightOpenPartialHomeomorph_apply (z y : E) :
    subRightOpenPartialHomeomorph z y = y - z := rfl

@[simp]
theorem subRightOpenPartialHomeomorph_source (z : E) :
    (subRightOpenPartialHomeomorph z).source = univ := rfl

@[simp]
theorem subRightOpenPartialHomeomorph_target (z : E) :
    (subRightOpenPartialHomeomorph z).target = univ := rfl

/-- Translations of the model space are smooth partial diffeomorphisms. -/
theorem subRight_mem_contDiffGroupoid (n : ℕ∞ω) (z : E) [NormedSpace ℝ E] :
    subRightOpenPartialHomeomorph z ∈ contDiffGroupoid n (𝓘(ℝ, E)) := by
  rw [mem_contDiffGroupoid_self_iff]
  constructor
  · have hfun : ((subRightOpenPartialHomeomorph z : OpenPartialHomeomorph E E) : E → E)
        = fun y => y - z := rfl
    rw [hfun, subRightOpenPartialHomeomorph_source]
    exact (contDiff_id.sub contDiff_const).contDiffOn
  · have hfun : (((subRightOpenPartialHomeomorph z : OpenPartialHomeomorph E E).symm : E → E))
        = fun y : E => y + z := by
      funext y
      rfl
    rw [hfun]
    exact (contDiff_id.add contDiff_const).contDiffOn

end Translation

section ExtendSelf

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- For the self model, the extension of a partial homeomorphism is the map itself. -/
@[simp] theorem extend_self_apply (e : OpenPartialHomeomorph E E) (x : E) :
    e.extend (𝓘(ℝ, E)) x = e x := rfl

/-- For the self model, the extension of a partial homeomorphism is the map itself. -/
@[simp] theorem extend_self_source (e : OpenPartialHomeomorph E E) :
    (e.extend (𝓘(ℝ, E))).source = e.source :=
  OpenPartialHomeomorph.extend_source e

/-- For the self model, the target of the extension of a partial homeomorphism is its target. -/
@[simp] theorem extend_self_target (e : OpenPartialHomeomorph E E) :
    (e.extend (𝓘(ℝ, E))).target = e.target := by
  rw [OpenPartialHomeomorph.extend_target]
  simp

/-- For the self model, the extension of the inverse is the inverse. -/
@[simp] theorem extend_self_symm_apply (e : OpenPartialHomeomorph E E) (y : E) :
    (e.extend (𝓘(ℝ, E))).symm y = e.symm y := rfl

end ExtendSelf

end Work.EmbeddedSpheres.TubeProject
