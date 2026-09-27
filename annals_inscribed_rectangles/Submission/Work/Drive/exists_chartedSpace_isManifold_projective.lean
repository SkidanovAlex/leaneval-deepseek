import Mathlib
import Submission.Work.Drive.ProjectiveDefs
import Submission.Work.Drive.ProjectiveTopology
import Submission.Work.Drive.sphere_quotient_projective
import Submission.Work.Drive.ProjectiveChartDefs
import Submission.Work.Drive.contDiffOn_projTransFun
import Submission.Work.Drive.isOpenQuotientMap_subtype_image

/-!
# `ℝPⁿ` is a smooth `n`-manifold

The projectivisation `ℝPⁿ = Projectivization ℝ (EuclideanSpace ℝ (Fin (n+1)))`, with the quotient
topology `Work.Drive.instTopologicalSpaceProjectivization` coming from the non-zero vectors, is
covered by the `n + 1` classical affine charts `[v] ↦ (v_j/v_i)_{j ≠ i}` on the open sets where a
representative has non-zero `i`-th coordinate.  The charts are open partial homeomorphisms onto the
model space `ℝⁿ = EuclideanSpace ℝ (Fin n)` (this is where the topology enters, through the fact
that `Projectivization.mk` is an *open* quotient map), and their changes of coordinates are the
rational maps `projTransFun i i'` of `Submission/Work/Drive/ProjectiveChartDefs`, which are smooth
on their domains.  Hence `ℝPⁿ` is a smooth `n`-manifold: the main result of this file,
`Work.Drive.exists_chartedSpace_isManifold_projective`.
-/

namespace Work.Drive

open Manifold
open scoped Manifold ContDiff LinearAlgebra.Projectivization
open Set

noncomputable section

variable {n : ℕ}

/-! ## The canonical map to `ℝPⁿ` is an open quotient map -/

lemma isOpenQuotientMap_projQuot (n : ℕ) : IsOpenQuotientMap (projQuot n) :=
  ⟨fun p => ⟨⟨p.rep, p.rep_nonzero⟩, Projectivization.mk_rep p⟩,
    continuous_projectivizationMk ℝ (Eucl n), isOpenMap_projectivizationMk ℝ (Eucl n)⟩

/-! ## The chart sources are open -/

lemma isOpen_setOf_ofLp_ne (n : ℕ) (i : Fin (n + 1)) : IsOpen {v : Eucl n | v.ofLp i ≠ 0} := by
  have h : Continuous (fun v : Eucl n => v.ofLp i) := by fun_prop
  exact isOpen_ne.preimage h

lemma isOpen_projChartSource (i : Fin (n + 1)) : IsOpen (projChartSource i) := by
  rw [projChartSource]
  exact (isOpenQuotientMap_projQuot n).isOpenMap _
    ((isOpen_setOf_ofLp_ne n i).preimage continuous_subtype_val)

/-! ## The chart maps are continuous on their sources -/

lemma continuousOn_projChartMap (i : Fin (n + 1)) :
    ContinuousOn (projChartMap i) (projChartSource i) := by
  set A : Set {v : Eucl n // v ≠ 0} := {v | v.1.ofLp i ≠ 0} with hAdef
  have hA : IsOpen A := (isOpen_setOf_ofLp_ne n i).preimage continuous_subtype_val
  have hsat : projQuot n ⁻¹' (projQuot n '' A) = A := by
    ext v
    constructor
    · rintro ⟨w, hw, hwv⟩
      obtain ⟨c, hc⟩ := (Projectivization.mk_eq_mk_iff ℝ w.1 v.1 w.2 v.2).mp hwv
      have hcoe : w.1.ofLp i = (c : ℝ) * v.1.ofLp i := by
        rw [← hc, Units.smul_def, PiLp.smul_apply, smul_eq_mul]
      intro h0
      exact hw (by rw [hcoe, h0, mul_zero])
    · intro hv
      exact ⟨v, hv, rfl⟩
  let qs : A → projQuot n '' A :=
    fun v => ⟨projQuot n v.1, Set.mem_image_of_mem (projQuot n) v.2⟩
  have hres : IsOpenQuotientMap qs :=
    isOpenQuotientMap_subtype_image (isOpenQuotientMap_projQuot n) hA hsat
  rw [continuousOn_iff_continuous_domRestrict]
  rw [show projChartSource i = projQuot n '' A from rfl]
  refine hres.continuous_comp_iff.mp ?_
  show Continuous (fun v : A => projChartMap i (projQuot n v.1))
  have hfun : (fun v : A => projChartMap i (projQuot n v.1)) = fun v => projCoordFun i v.1.1 := by
    funext v
    rw [projQuot, projChartMap_mk]
  rw [hfun]
  show Continuous (fun v : A =>
    WithLp.toLp 2 (fun j : Fin n => v.1.1.ofLp (i.succAbove j) / v.1.1.ofLp i))
  refine (PiLp.continuous_toLp 2 (fun _ : Fin n => ℝ)).comp ?_
  refine continuous_pi (fun j => ?_)
  exact Continuous.div (by fun_prop) (by fun_prop) (fun v => v.2)

lemma continuous_projChartInv (i : Fin (n + 1)) : Continuous (projChartInv i) := by
  have hsec : Continuous (fun x : EuclideanSpace ℝ (Fin n) => projSection i x) := by
    show Continuous (fun x : EuclideanSpace ℝ (Fin n) =>
      WithLp.toLp 2 (Fin.insertNth (α := fun _ => ℝ) i (1 : ℝ) x.ofLp))
    refine (PiLp.continuous_toLp 2 (fun _ : Fin (n + 1) => ℝ)).comp ?_
    exact continuous_const.finInsertNth i (by fun_prop)
  have hσ : Continuous (fun x : EuclideanSpace ℝ (Fin n) =>
      (⟨projSection i x, projSection_ne_zero i x⟩ : {v : Eucl n // v ≠ 0})) :=
    Continuous.subtype_mk hsec _
  refine ((continuous_projectivizationMk ℝ (Eucl n)).comp hσ).congr (fun x => ?_)
  exact projectivizationMk_congr ℝ (Eucl n)

/-! ## The charts -/

/-- The `i`-th classical affine chart on `ℝPⁿ`: the open partial homeomorphism sending a point to
its projective coordinates `(v_j/v_i)_{j ≠ i}`. -/
def projChart (i : Fin (n + 1)) :
    OpenPartialHomeomorph (Projectivization ℝ (Eucl n)) (EuclideanSpace ℝ (Fin n)) where
  toFun := projChartMap i
  invFun := projChartInv i
  source := projChartSource i
  target := univ
  map_source' := fun _ _ => mem_univ _
  map_target' := fun x _ => projChartInv_mem_projChartSource i x
  left_inv' := fun p hp => projChartInv_projChartMap hp
  right_inv' := fun x _ => projChartMap_projChartInv i x
  continuousOn_toFun := continuousOn_projChartMap i
  continuousOn_invFun := (continuous_projChartInv i).continuousOn
  open_source := isOpen_projChartSource i
  open_target := isOpen_univ

@[simp] lemma projChart_apply (i : Fin (n + 1)) (p : Projectivization ℝ (Eucl n)) :
    projChart i p = projChartMap i p := rfl

@[simp] lemma projChart_symm_apply (i : Fin (n + 1)) (x : EuclideanSpace ℝ (Fin n)) :
    (projChart i).symm x = projChartInv i x := rfl

@[simp] lemma projChart_source (i : Fin (n + 1)) : (projChart i).source = projChartSource i := rfl

@[simp] lemma projChart_target (i : Fin (n + 1)) : (projChart i).target = univ := rfl

/-! ## Smoothness of the changes of coordinates -/

lemma contDiffOn_trans {i i' : Fin (n + 1)} :
    ContDiffOn ℝ ∞ (↑((projChart i).symm ≫ₕ (projChart i')) :
        EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
      ((projChart i).symm ≫ₕ (projChart i')).source := by
  have hsrc : ((projChart i).symm ≫ₕ (projChart i')).source = projTransSource i i' := by
    ext x
    simp only [OpenPartialHomeomorph.trans_source, Set.mem_inter_iff, Set.mem_preimage,
      OpenPartialHomeomorph.symm_source, projChart_target, projChart_source, projChart_symm_apply,
      Set.mem_univ, true_and]
    exact projChartInv_mem_projChartSource_iff i i' x
  have hfun : ∀ x ∈ ((projChart i).symm ≫ₕ (projChart i')).source,
      (↑((projChart i).symm ≫ₕ (projChart i')) : EuclideanSpace ℝ (Fin n) →
        EuclideanSpace ℝ (Fin n)) x = projTransFun i i' x := by
    intro x _
    rw [OpenPartialHomeomorph.trans_apply]
    exact projChartMap_projChartInv_eq_transFun i i' x
  rw [hsrc]
  exact ((contDiffOn_projTransFun n i i').of_le le_top).congr
    (fun x hx => hfun x (by rw [hsrc]; exact hx))

/-! ## The main theorem -/

open Manifold in
open scoped Manifold ContDiff in
open scoped LinearAlgebra.Projectivization in
/-- **`ℝPⁿ` is a smooth manifold.**  For every `n` the projectivisation of `ℝ^{n+1}` carries a
charted-space structure with model `ℝⁿ`, compatible with the quotient topology
`Work.Drive.instTopologicalSpaceProjectivization`, for which it is a smooth (`C^∞`) `n`-manifold.
The charts are the classical projective charts `[v] ↦ (v_j / v_i)_{j ≠ i}` on the open sets where the
`i`-th coordinate of a representative does not vanish. -/
theorem exists_chartedSpace_isManifold_projective (n : ℕ) :
    ∃ C : ChartedSpace (EuclideanSpace ℝ (Fin n))
        (Projectivization ℝ (EuclideanSpace ℝ (Fin (n + 1)))),
      letI := C
      IsManifold (𝓡 n) ∞ (Projectivization ℝ (EuclideanSpace ℝ (Fin (n + 1)))) := by
  have hcover : ∀ p : Projectivization ℝ (Eucl n), ∃ i : Fin (n + 1), p ∈ projChartSource i := by
    intro p
    have h : ∃ i : Fin (n + 1), p.rep.ofLp i ≠ 0 := by
      by_contra hcon
      push_neg at hcon
      refine p.rep_nonzero ?_
      ext k
      exact hcon k
    obtain ⟨i, hi⟩ := h
    exact ⟨i, by
      rw [← Projectivization.mk_rep p]
      exact (mem_projChartSource_iff' p.rep_nonzero).mpr hi⟩
  let C : ChartedSpace (EuclideanSpace ℝ (Fin n)) (Projectivization ℝ (Eucl n)) :=
    { atlas := Set.range (projChart (n := n))
      chartAt := fun p => projChart (Classical.choose (hcover p))
      mem_chart_source := fun p => Classical.choose_spec (hcover p)
      chart_mem_atlas := fun p => Set.mem_range_self _ }
  refine ⟨C, ?_⟩
  letI : ChartedSpace (EuclideanSpace ℝ (Fin n)) (Projectivization ℝ (Eucl n)) := C
  haveI : HasGroupoid (Projectivization ℝ (Eucl n)) (contDiffGroupoid ∞ (𝓡 n)) :=
    hasGroupoid_of_pregroupoid _ (fun {e e'} he he' => by
      obtain ⟨i, rfl⟩ := he
      obtain ⟨i', rfl⟩ := he'
      have key := @contDiffOn_trans n i i'
      simpa only [contDiffPregroupoid, modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm,
        Set.range_id, Set.preimage_id, Set.inter_univ, Function.comp_def, id_eq] using key)
  exact IsManifold.mk' (𝓡 n) ∞ _

end

end Work.Drive
