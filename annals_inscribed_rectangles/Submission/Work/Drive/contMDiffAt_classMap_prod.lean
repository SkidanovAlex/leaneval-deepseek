import Mathlib
import Submission.Work.Drive.chartPertData
import Submission.Work.Drive.contMDiffAt_projRot
import Submission.Work.Drive.contDiffAt_projCoordFun_classEquiv

/-!
# The class perturbation `[v] ↦ [(1 + L (t)) v]` is `C^∞` in `(t, [v])`

`Work.Drive.classMap t : ℝP³ → ℝP³` is the projectivisation of the quaternionic left multiplication
`1 + L (t)` (`Submission/Work/Drive/chartPertData.lean`); it is the action on the projective factor of
the chart perturbation of the capping space.

This file proves that the map `(t, p) ↦ classMap t p` is `C^∞` at every point of the *product*
manifold `ℝ⁴ × ℝP³` (with the product charted structure `prodChartedSpace`), i.e. `classMap` is a
`C^∞` action of the parameter on `ℝP³`.  The proof follows
`Submission/Work/Drive/contMDiffAt_projRot.lean` (the same statement for the rotation `projRot`):

* choose the preferred projective charts `i` at `p₀` and `j` at `classMap t₀ p₀`;
* by `contMDiffAt_iff` and `extChartAt_prod`, everything reduces to the chart expression
  `(t, x) ↦ projChartMap j (classMap t (projChartInv i x))` on the flat space `ℝ⁴ × ℝ³`, which is
  `(t, x) ↦ projCoordFun j (classEquiv t (projSection i x))` and is smooth where the denominator
  `(classEquiv t (projSection i x)).ofLp j` does not vanish
  (`Work.Drive.contDiffAt_projChartMap_classMap`, on top of
  `Work.Drive.contDiffAt_projCoordFun_classEquiv`);
* continuity follows from the continuity of `x ↦ projChartMap i x`, of
  `(t, x) ↦ classEquiv t (projSection i x)` and of `Projectivization.mk`, together with
  `projChartInv_projChartMap`.
-/

namespace Work.Drive

open scoped Manifold ContDiff LinearAlgebra.Projectivization
open Set Filter

set_option linter.style.haveILetI false

noncomputable section

/-- **The chart coordinates of the class perturbation are `C^∞` where the denominator does not
vanish.**  For `(t₀, x₀)` with `(classEquiv t₀ (projSection i x₀)).ofLp j ≠ 0`, the composite of the
`j`-th chart with the perturbed `i`-th chart inverse,
`(t, x) ↦ projChartMap j (classMap t (projChartInv i x))`, is `C^∞` at `(t₀, x₀)`.  It rewrites as
`(t, x) ↦ projCoordFun j (classEquiv t (projSection i x))`. -/
lemma contDiffAt_projChartMap_classMap (i j : Fin 4) (t₀ : Eucl 3)
    (x₀ : EuclideanSpace ℝ (Fin 3))
    (hj : (classEquiv t₀ (projSection (n := 3) i x₀)).ofLp j ≠ 0) :
    ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun u : Eucl 3 × EuclideanSpace ℝ (Fin 3) =>
        projChartMap j (classMap u.1 (projChartInv i u.2))) (t₀, x₀) := by
  have hfun : (fun u : Eucl 3 × EuclideanSpace ℝ (Fin 3) =>
        projChartMap j (classMap u.1 (projChartInv i u.2)))
      = fun u => projCoordFun j (classEquiv u.1 (projSection (n := 3) i u.2)) := by
    funext u
    simp only [projChartInv, classMap_mk, projChartMap_mk]
  rw [hfun]
  exact ContDiffAt.fun_comp (x := (t₀, x₀)) (g := projCoordFun (n := 3) j)
    (f := fun u : Eucl 3 × EuclideanSpace ℝ (Fin 3) =>
      classEquiv u.1 (projSection (n := 3) i u.2))
    (contDiffAt_projCoordFun (n := 3) j _ hj) ((contDiff_classEquiv_projSection i).contDiffAt)

theorem contMDiffAt_classMap_prod (t₀ : Work.Drive.Eucl 3)
    (p₀ : Projectivization ℝ (Work.Drive.Eucl 3)) :
    letI : ChartedSpace (EuclideanSpace ℝ (Fin 3))
        (Projectivization ℝ (Work.Drive.Eucl 3)) := Work.Drive.projCharted 3
    letI : ChartedSpace (ModelProd (EuclideanSpace ℝ (Fin 4)) (EuclideanSpace ℝ (Fin 3)))
        (Work.Drive.Eucl 3 × Projectivization ℝ (Work.Drive.Eucl 3)) :=
      prodChartedSpace (EuclideanSpace ℝ (Fin 4)) (EuclideanSpace ℝ (Fin 4))
        (EuclideanSpace ℝ (Fin 3)) (Projectivization ℝ (Work.Drive.Eucl 3))
    ContMDiffAt (ModelWithCorners.prod (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4)))
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 3))))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 3))) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun q : Work.Drive.Eucl 3 × Projectivization ℝ (Work.Drive.Eucl 3) =>
        Work.Drive.classMap q.1 q.2) (t₀, p₀) := by
  letI : ChartedSpace (EuclideanSpace ℝ (Fin 3)) (Projectivization ℝ (Eucl 3)) := projCharted 3
  -- the source model with corners, in the `ModelProd` form
  let Is : ModelWithCorners ℝ (Eucl 3 × EuclideanSpace ℝ (Fin 3))
      (ModelProd (Eucl 3) (EuclideanSpace ℝ (Fin 3))) :=
    modelWithCornersSelf ℝ (Eucl 3 × EuclideanSpace ℝ (Fin 3))
  have hIs : Is = (modelWithCornersSelf ℝ (Eucl 3)).prod
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 3))) := modelWithCornersSelf_prod

  letI : ChartedSpace (EuclideanSpace ℝ (Fin 3)) (Projectivization ℝ (Eucl 3)) := projCharted 3
  let Is : ModelWithCorners ℝ (Eucl 3 × EuclideanSpace ℝ (Fin 3))
      (ModelProd (Eucl 3) (EuclideanSpace ℝ (Fin 3))) :=
    modelWithCornersSelf ℝ (Eucl 3 × EuclideanSpace ℝ (Fin 3))
  have hIs : Is = (modelWithCornersSelf ℝ (Eucl 3)).prod
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 3))) := modelWithCornersSelf_prod
  rw [← hIs]
  set i : Fin (3 + 1) := Classical.choose (exists_mem_projChartSource p₀) with hi
  have hpi : p₀ ∈ projChartSource i :=
    Classical.choose_spec (exists_mem_projChartSource p₀)
  set j : Fin (3 + 1) := Classical.choose (exists_mem_projChartSource (classMap t₀ p₀)) with hj
  have hpj : classMap t₀ p₀ ∈ projChartSource j :=
    Classical.choose_spec (exists_mem_projChartSource (classMap t₀ p₀))
  have hjne : (classEquiv t₀ (projSection (n := 3) i (projChartMap i p₀))).ofLp j ≠ 0 := by
    have h1 : classMap t₀ (projChartInv i (projChartMap i p₀)) ∈ projChartSource j := by
      rw [projChartInv_projChartMap hpi]; exact hpj
    rw [projChartInv, classMap_mk] at h1
    exact (mem_projChartSource_iff' (classEquiv_ne_zero (projSection_ne_zero i _))).mp h1
  have hchart : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun u : Eucl 3 × EuclideanSpace ℝ (Fin 3) =>
        projChartMap j (classMap u.1 (projChartInv i u.2))) (t₀, projChartMap i p₀) :=
    contDiffAt_projChartMap_classMap i j t₀ (projChartMap i p₀) hjne
  have tgt : (↑(extChartAt (𝓡 3) (classMap t₀ p₀)) :
        Projectivization ℝ (Eucl 3) → EuclideanSpace ℝ (Fin 3)) = projChartMap j := by
    rw [extChartAt_coe, modelWithCornersSelf_coe, Function.id_comp]
    rw [show (chartAt (EuclideanSpace ℝ (Fin 3)) (classMap t₀ p₀)) = projChart j from rfl]
    rfl
  have src : (↑(extChartAt Is (t₀, p₀)).symm :
        Eucl 3 × EuclideanSpace ℝ (Fin 3) → Eucl 3 × Projectivization ℝ (Eucl 3))
      = fun x => (x.1, projChartInv i x.2) := by
    rw [hIs, extChartAt_prod, PartialEquiv.prod_coe_symm]
    funext x
    simp only [extChartAt_model_space_eq_id, PartialEquiv.refl_symm, PartialEquiv.refl_coe,
      extChartAt_coe_symm, modelWithCornersSelf_coe_symm, Function.comp_apply, id_eq]
    rw [show (chartAt (EuclideanSpace ℝ (Fin 3)) p₀) = projChart i from rfl]
    rfl
  have hpt : (↑(extChartAt Is (t₀, p₀)) :
        Eucl 3 × Projectivization ℝ (Eucl 3) → Eucl 3 × EuclideanSpace ℝ (Fin 3)) (t₀, p₀)
      = (t₀, projChartMap i p₀) := by
    rw [hIs, extChartAt_prod, PartialEquiv.prod_coe]
    simp only [extChartAt_model_space_eq_id, extChartAt_coe, modelWithCornersSelf_coe,
      Function.comp_apply, id_eq, PartialEquiv.refl_coe]
    rw [show (chartAt (EuclideanSpace ℝ (Fin 3)) p₀) = projChart i from rfl]
    rfl
  have hG : (↑(extChartAt (𝓡 3) (classMap t₀ p₀)) ∘
        (fun q : Eucl 3 × Projectivization ℝ (Eucl 3) => classMap q.1 q.2) ∘
          ↑(extChartAt Is (t₀, p₀)).symm)
      = (fun u : Eucl 3 × EuclideanSpace ℝ (Fin 3) =>
          projChartMap j (classMap u.1 (projChartInv i u.2))) := by
    funext q
    rw [Function.comp_apply, Function.comp_apply, src, tgt]
  rw [contMDiffAt_iff]
  refine ⟨?_, ?_⟩
  · have hΨ : ContinuousAt (fun q : Eucl 3 × Projectivization ℝ (Eucl 3) =>
        (q.1, projChartMap i q.2)) (t₀, p₀) :=
      continuousAt_fst.prodMk ((contMDiffAt_projChartMap 3 i p₀ hpi).continuousAt.comp
        continuousAt_snd)
    have hW : ContinuousAt (fun u : Eucl 3 × EuclideanSpace ℝ (Fin 3) =>
        (⟨classEquiv u.1 (projSection (n := 3) i u.2),
          classEquiv_ne_zero (projSection_ne_zero i u.2)⟩ : {v : Eucl 3 // v ≠ 0}))
        (t₀, projChartMap i p₀) :=
      ContinuousAt.codRestrict
        (f := fun u : Eucl 3 × EuclideanSpace ℝ (Fin 3) =>
          classEquiv u.1 (projSection (n := 3) i u.2))
        (fun u => classEquiv_ne_zero (projSection_ne_zero i u.2))
        (x := (t₀, projChartMap i p₀))
        ((contDiff_classEquiv_projSection i).continuous.continuousAt)
    have hcomp₁ : ContinuousAt (fun q : Eucl 3 × Projectivization ℝ (Eucl 3) =>
        (⟨classEquiv q.1 (projSection (n := 3) i (projChartMap i q.2)),
          classEquiv_ne_zero (projSection_ne_zero i (projChartMap i q.2))⟩ : {v : Eucl 3 // v ≠ 0}))
        (t₀, p₀) :=
      ContinuousAt.comp (f := fun q : Eucl 3 × Projectivization ℝ (Eucl 3) =>
          (q.1, projChartMap i q.2)) hW hΨ
    have hcont' : ContinuousAt (fun q : Eucl 3 × Projectivization ℝ (Eucl 3) =>
        Projectivization.mk ℝ (classEquiv q.1 (projSection (n := 3) i (projChartMap i q.2)))
          (classEquiv_ne_zero (projSection_ne_zero i (projChartMap i q.2)))) (t₀, p₀) :=
      (continuous_projectivizationMk ℝ (Eucl 3)).continuousAt.comp hcomp₁
    have hcont : ContinuousAt (fun q : Eucl 3 × Projectivization ℝ (Eucl 3) =>
        classMap q.1 (projChartInv i (projChartMap i q.2))) (t₀, p₀) := by
      refine hcont'.congr ?_
      filter_upwards with q
      simp only [projChartInv, classMap_mk]
    refine hcont.congr ?_
    filter_upwards [((isOpen_projChartSource i).preimage continuous_snd).mem_nhds hpi]
      with q hq
    rw [projChartInv_projChartMap hq]
  · rw [show Set.range (↑Is) = Set.univ from by
        simp only [Is, modelWithCornersSelf_coe, Set.range_id],
      contDiffWithinAt_univ, hG, hpt]
    exact hchart


end

end Work.Drive
