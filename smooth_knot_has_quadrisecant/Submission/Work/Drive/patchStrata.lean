import Mathlib
import Submission.Work.Drive.Prelude
import Submission.Work.Drive.quadFamilyDefs
import Submission.Work.Drive.quadRich
import Submission.Work.Drive.quadJoint
import Submission.Work.Drive.rankPatchDefs
import Submission.Work.Drive.rank_patchA
import Submission.Work.Drive.rank_patchB
import Submission.Work.Drive.rank_patchM
import Submission.Work.Drive.rankZeroSetTool
import Submission.Work.Drive.tangencyBadSet

/-!
# The patch strata of the bad locus are small

This file starts piece **P1** of the route recorded in
`Submission/Work/Drive/NOTES_noInflection_route.md`: for each of the three patches
`y_x = 0` (`x ∈ {a,b,m}`) of the bad locus

    bad ⟺ (y_a = 0) ∨ (y_b = 0) ∨ (y_m = 0) ∨ (y_a ∥ y_b ∥ y_m)

the set of *coefficients* `c` of the perturbation family `curve r 4 c = r + corr 4 c` for which
the patch condition holds somewhere in a compact, separated parameter region `K ⊆ ℝ³` has empty
interior in the coefficient space `QCoeff 4`.

The mechanism (see the notes):

* the patch condition depends on the curve only through the *data*
  `curveData r c w = (r_c x, v_c x)_{x ∈ {w.1,w.2.1,w.2.2}} ∈ TripleData = Space⁶`;
* the partial derivative of `c ↦ curveData r c w` is the linear map `dataLin w`, which is
  **surjective** (`dataJet_surjective`, from the richness of the degree-four trigonometric family:
  `quadRich.scValueDeriv_surjective`);
* hence the derivative of `c ↦ patchA (curveData r c w)` has the same range as
  `fderiv ℝ patchA (curveData r c w)`, which has rank `≥ 4` (`rank_patchA`);
* and `4 > finrank ℝ (ℝ × ℝ × ℝ) = 3`, so the rank form of the implicit-function-theorem
  dimension count (`interior_zeroSet_projection_empty_of_rank`, proved in
  `exists_close_transverse_noInflection.lean`) applies.
-/

namespace Work.Drive

open LeanEval.KnotTheory.Quadrisecant

noncomputable section

/-! ## The data of the perturbed curve and the data-jet linear map -/

/-- The *linear* part of the data map: the value and the derivative of the correction at the
three parameters. -/
def dataLin (w : ℝ × ℝ × ℝ) : QCoeff 4 →ₗ[ℝ] TripleData where
  toFun c := (corr 4 c w.1, corr 4 c w.2.1, corr 4 c w.2.2,
    corrD 4 c w.1, corrD 4 c w.2.1, corrD 4 c w.2.2)
  map_add' c c' := by
    simp only [Prod.mk.injEq, Prod.mk_add_mk, corr_add, corrD_add]
  map_smul' a c := by
    simp only [Prod.mk.injEq, Prod.smul_mk, corr_smul, corrD_smul, RingHom.id_apply]

@[simp] lemma dataLin_apply (w : ℝ × ℝ × ℝ) (c : QCoeff 4) :
    dataLin w c = (corr 4 c w.1, corr 4 c w.2.1, corr 4 c w.2.2,
      corrD 4 c w.1, corrD 4 c w.2.1, corrD 4 c w.2.2) := rfl

/-- **Surjectivity of the data-jet map** (the differential surjectivity of the perturbation
family): the value and the derivative of the correction at three pairwise distinct
fundamental-domain parameters can be prescribed arbitrarily. -/
lemma dataLin_surjective {a b m : ℝ}
    (ha : a ∈ Set.Ico 0 (2 * Real.pi)) (hb : b ∈ Set.Ico 0 (2 * Real.pi))
    (hm : m ∈ Set.Ico 0 (2 * Real.pi)) (hab : a ≠ b) (ham : a ≠ m) (hbm : b ≠ m) :
    Function.Surjective (dataLin (a, b, m)) := by
  intro X
  obtain ⟨c, hc⟩ := dataJet_surjective ha hb hm hab ham hbm X
  exact ⟨c, hc⟩

/-- The patch-`A` badness map of the perturbed curve: collinearity of the triple together with
the tangency of the chord at the first point. -/
def psiA (r : ℝ → Space) : QCoeff 4 × (ℝ × ℝ × ℝ) → Space × Space :=
  fun p => patchA (curveData r p.1 p.2)

/-- The data map of the perturbed curve is `C¹` in `c` at fixed `w`, and its derivative is
`dataLin w` (the affine decomposition `curveData r c w = curveData r c₀ w + dataLin w (c - c₀)`
from `corr_add`/`corrD_add`). -/
lemma hasFDerivAt_curveData_slice {r : ℝ → Space} (hr : IsSmoothKnot r)
    (w : ℝ × ℝ × ℝ) (c₀ : QCoeff 4) :
    HasFDerivAt (fun c : QCoeff 4 => curveData r c w) (dataLin w).toContinuousLinearMap c₀ := by
  have key : ∀ c : QCoeff 4, curveData r c w = curveData r c₀ w + dataLin w (c - c₀) := by
    intro c
    have hc : c = c₀ + (c - c₀) := by abel
    rw [hc]
    simp only [curveData, dataLin_apply, curve, velCurve, Prod.mk_add_mk, corr_add, corrD_add,
      Prod.mk.injEq]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> abel
  have h2 : HasFDerivAt (fun c : QCoeff 4 => curveData r c₀ w + dataLin w (c - c₀))
      ((dataLin w).toContinuousLinearMap) c₀ := by
    have hsub : HasFDerivAt (fun c : QCoeff 4 => c - c₀) (1 : QCoeff 4 →L[ℝ] QCoeff 4) c₀ :=
      (hasFDerivAt_id c₀).sub_const c₀
    have hcomp := (dataLin w).toContinuousLinearMap.hasFDerivAt.comp c₀ hsub
    have h3 := hcomp.const_add (curveData r c₀ w)
    have h4 : (LinearMap.toContinuousLinearMap (dataLin w) ∘SL
        (1 : QCoeff 4 →L[ℝ] QCoeff 4)) = LinearMap.toContinuousLinearMap (dataLin w) := by
      rw [show (1 : QCoeff 4 →L[ℝ] QCoeff 4) = ContinuousLinearMap.id ℝ (QCoeff 4) from rfl,
        ContinuousLinearMap.comp_id]
    rw [h4] at h3
    exact h3
  exact h2.congr_of_eventuallyEq (Filter.Eventually.of_forall fun c => key c)

/-- The badness map of the patch `A` with the parameter triple packaged as
`EuclideanSpace ℝ (Fin 3)` (so that the implicit-function-theorem tool, which requires an inner
product space, applies). -/
def psiAe (r : ℝ → Space) : QCoeff 4 × EuclideanSpace ℝ (Fin 3) → Space × Space :=
  fun p => psiA r (p.1, (p.2 0, p.2 1, p.2 2))

/-- The badness map of the patch `A`, transported to the Euclidean target `Tgt = ℝ⁶` so that the
implicit-function-theorem tool (which requires inner product spaces on both variables) applies. -/
def psiAt (r : ℝ → Space) : QCoeff 4 × EuclideanSpace ℝ (Fin 3) → Tgt :=
  fun p => eTgt (psiAe r p)

/-- The finrank of a submodule is unchanged by the identifiable `eTgt`. -/
lemma finrank_map_eTgt (S : Submodule ℝ (Space × Space)) :
    Module.finrank ℝ (S.map (eTgt : (Space × Space) →ₗ[ℝ] Tgt)) = Module.finrank ℝ S :=
  (Submodule.equivMapOfInjective _ eTgt.injective S).finrank_eq.symm


/-- Function-level unfolding of `psiAe` (a local `let` or a pointwise `_apply` lemma cannot fire on
`ContDiff ℝ 1 (psiAe r)`, but this function-level `rfl` equation can). -/
lemma psiAe_eq (r : ℝ → Space) :
    psiAe r = fun p : QCoeff 4 × EuclideanSpace ℝ (Fin 3) =>
      psiA r (p.1, (p.2 0, p.2 1, p.2 2)) := rfl

/-- Function-level unfolding of `psiAt`. -/
lemma psiAt_eq (r : ℝ → Space) :
    psiAt r = fun p : QCoeff 4 × EuclideanSpace ℝ (Fin 3) =>
      eTgt (psiA r (p.1, (p.2 0, p.2 1, p.2 2))) := rfl

/-- Pointwise unfolding of `psiAe` (for use under binders). -/
@[simp] lemma psiAe_apply (r : ℝ → Space) (p : QCoeff 4 × EuclideanSpace ℝ (Fin 3)) :
    psiAe r p = psiA r (p.1, (p.2 0, p.2 1, p.2 2)) := rfl

/-- Pointwise unfolding of `psiAt` (for use under binders). -/
@[simp] lemma psiAt_apply (r : ℝ → Space) (p : QCoeff 4 × EuclideanSpace ℝ (Fin 3)) :
    psiAt r p = eTgt (psiA r (p.1, (p.2 0, p.2 1, p.2 2))) := rfl


/-- **The rewrite that collapses the unapplied site**: `ContDiff ℝ 1 (psiAe r)` is *definitionally*
the smoothness of the explicit lambda, so `rw [psiAe_eq]` closes it (`rwa` below). -/
lemma contDiff_psiAe_iff (r : ℝ → Space) :
    ContDiff ℝ 1 (psiAe r) ↔ ContDiff ℝ 1 (fun p : QCoeff 4 × EuclideanSpace ℝ (Fin 3) =>
      psiA r (p.1, (p.2 0, p.2 1, p.2 2))) := by
  rw [psiAe_eq]

/-- Same collapse for `psiAt`. -/
lemma contDiff_psiAt_iff (r : ℝ → Space) :
    ContDiff ℝ 1 (psiAt r) ↔ ContDiff ℝ 1 (fun p : QCoeff 4 × EuclideanSpace ℝ (Fin 3) =>
      eTgt (psiA r (p.1, (p.2 0, p.2 1, p.2 2)))) := by
  rw [psiAt_eq]

/-- Same collapse at the level of Fréchet derivatives. -/
lemma hasFDerivAt_psiAe_iff (r : ℝ → Space)
    (c₀ : QCoeff 4 × EuclideanSpace ℝ (Fin 3)) (L' : (QCoeff 4 × EuclideanSpace ℝ (Fin 3)) →L[ℝ] (Space × Space)) :
    HasFDerivAt (psiAe r) L' c₀ ↔ HasFDerivAt
      (fun p : QCoeff 4 × EuclideanSpace ℝ (Fin 3) =>
        psiA r (p.1, (p.2 0, p.2 1, p.2 2))) L' c₀ := by
  rw [psiAe_eq]


/-- **Site 1 of the rewrite pass.**  The joint smoothness of the patch-`A` badness map, in the
wrapper form: obtained from the explicit-lambda form by a single `rw [psiAe_eq]`, then
`ContDiff.comp` of `rpa_contDiff_patchA` with `contDiff_curveData_joint` through the triple
reindexing.  (In the proof of `patchA_bad_interior_empty` this is the `hPsiAe` step.) -/
lemma contDiff_psiAe (r : ℝ → Space) (hr : IsSmoothKnot r) : ContDiff ℝ 1 (psiAe r) := by
  rw [psiAe_eq]
  have h1 : ContDiff ℝ 1 (psiA r) := rpa_contDiff_patchA.comp (contDiff_curveData_joint hr)
  have h2 : ContDiff ℝ 1 (fun p : QCoeff 4 × EuclideanSpace ℝ (Fin 3) =>
      (p.1, (p.2 0, p.2 1, p.2 2))) := by fun_prop
  exact h1.comp h2

/-- **Site 2 of the rewrite pass.**  The joint smoothness of the transported badness map
`psiAt = eTgt ∘ psiAe`, by a single `rw [psiAt_eq]` and site 1.  (This is the `hPsi` step of the
main theorem, i.e. the `ContDiff ℝ 1 Ψ` hypothesis of the rank tool.) -/
lemma contDiff_psiAt (r : ℝ → Space) (hr : IsSmoothKnot r) : ContDiff ℝ 1 (psiAt r) := by
  rw [psiAt_eq]
  exact ((eTgt : (Space × Space) →L[ℝ] Tgt).contDiff).comp (contDiff_psiAe r hr)


/-- **Site 3 of the rewrite pass.**  The Fréchet derivative of `psiAe r` at `(c,u)`, in the wrapper
form: `rw [psiAe_eq]` reduces it to the `HasFDerivAt` of the explicit lambda, which follows from
site 1.  (This is the `hfull` step of the main theorem.)  The statement is given at the point
`(c + 0, u)` as well, which is the shape `HasFDerivAt.comp` needs. -/
lemma hasFDerivAt_psiAe (r : ℝ → Space) (hr : IsSmoothKnot r)
    (c : QCoeff 4) (u : EuclideanSpace ℝ (Fin 3)) :
    HasFDerivAt (psiAe r) (fderiv ℝ (psiAe r) (c, u)) (c, u) := by
  rw [psiAe_eq]
  exact ((contDiff_psiAe r hr).differentiable (by norm_num)).differentiableAt.hasFDerivAt

/-- Site 3 at the shifted point shape used inside the proof of
`patchA_bad_interior_empty`. -/
lemma hasFDerivAt_psiAe_shift (r : ℝ → Space) (hr : IsSmoothKnot r)
    (c : QCoeff 4) (u : EuclideanSpace ℝ (Fin 3)) :
    HasFDerivAt (psiAe r) (fderiv ℝ (psiAe r) (c + 0, u)) (c + 0, u) := by
  simpa only [add_zero] using hasFDerivAt_psiAe r hr c u


/-- **Site 4 of the rewrite pass (applied occurrence: the `hsliceA`/`hsliceDATA` pair).**
The derivative of the shifted data map and of the shifted patch map, in the plain vocabulary used
inside `patchA_bad_interior_empty`.  The points are written as `(… ) 0` so that
`HasFDerivAt.comp` sees matching terms. -/
lemma hasFDerivAt_curveData_shift {r : ℝ → Space} (hr : IsSmoothKnot r)
    (w : ℝ × ℝ × ℝ) (c : QCoeff 4) :
    HasFDerivAt (fun δ : QCoeff 4 => curveData r (c + δ) w)
      ((dataLin w).toContinuousLinearMap) 0 := by
  have hinner : HasFDerivAt (fun δ : QCoeff 4 => c + δ) (1 : QCoeff 4 →L[ℝ] QCoeff 4) 0 :=
    (hasFDerivAt_id (0 : QCoeff 4)).const_add c
  have hc0 : HasFDerivAt (fun c' : QCoeff 4 => curveData r c' w)
      ((dataLin w).toContinuousLinearMap) (c + 0) := by
    simpa using hasFDerivAt_curveData_slice hr w c
  have h := hc0.comp 0 hinner
  rw [show (1 : QCoeff 4 →L[ℝ] QCoeff 4) = ContinuousLinearMap.id ℝ (QCoeff 4) from rfl,
    ContinuousLinearMap.comp_id] at h
  simpa [Function.comp_def] using h

/-- The patch map along the same slice, with derivative
`(fderiv ℝ patchA (curveData r c w)).comp (dataLin w).toContinuousLinearMap`. -/
lemma hasFDerivAt_patchA_shift {r : ℝ → Space} (hr : IsSmoothKnot r)
    (w : ℝ × ℝ × ℝ) (c : QCoeff 4) :
    HasFDerivAt (fun δ : QCoeff 4 => patchA (curveData r (c + δ) w))
      ((fderiv ℝ patchA (curveData r c w)).comp (dataLin w).toContinuousLinearMap) 0 := by
  have hT : HasFDerivAt patchA
      (fderiv ℝ patchA ((fun δ : QCoeff 4 => curveData r (c + δ) w) 0))
      ((fun δ : QCoeff 4 => curveData r (c + δ) w) 0) := by
    simpa using (((rpa_contDiff_patchA.differentiable (by norm_num)).differentiableAt
      (x := curveData r c w)).hasFDerivAt)
  have h3 := hT.comp 0 (hasFDerivAt_curveData_shift hr w c)
  simpa [Function.comp_def] using h3


/-- **Site 5 of the rewrite pass.**  The `inl`-part of the derivative of `psiAe r` at `(c,u)` is the
slice derivative of the patch map: by uniqueness of derivatives, applied to the slice
`δ ↦ (c + δ, u)`.  This is the `hinl` step of `patchA_bad_interior_empty`, with the parameter triple
written out as `(u 0, u 1, u 2)` so that no `set`-bound variable is involved. -/
lemma fderiv_psiAe_comp_inl {r : ℝ → Space} (hr : IsSmoothKnot r)
    (c : QCoeff 4) (u : EuclideanSpace ℝ (Fin 3)) :
    (fderiv ℝ (psiAe r) (c, u)).comp
        (ContinuousLinearMap.inl ℝ (QCoeff 4) (EuclideanSpace ℝ (Fin 3)))
      = (fderiv ℝ patchA (curveData r c (u 0, u 1, u 2))).comp
        (dataLin (u 0, u 1, u 2)).toContinuousLinearMap := by
  have hfull := hasFDerivAt_psiAe_shift r hr c u
  have hslice : HasFDerivAt (fun δ : QCoeff 4 => (c + δ, u))
      (ContinuousLinearMap.inl ℝ (QCoeff 4) (EuclideanSpace ℝ (Fin 3))) 0 := by
    have h1 : HasFDerivAt (fun δ : QCoeff 4 => c + δ) (1 : QCoeff 4 →L[ℝ] QCoeff 4) 0 :=
      (hasFDerivAt_id (0 : QCoeff 4)).const_add c
    have h2 : HasFDerivAt (fun _ : QCoeff 4 => u)
        (0 : QCoeff 4 →L[ℝ] EuclideanSpace ℝ (Fin 3)) 0 := hasFDerivAt_const u 0
    have h3 := h1.prodMk h2
    rw [show ((1 : QCoeff 4 →L[ℝ] QCoeff 4).prod
        (0 : QCoeff 4 →L[ℝ] EuclideanSpace ℝ (Fin 3)))
        = ContinuousLinearMap.inl ℝ (QCoeff 4) (EuclideanSpace ℝ (Fin 3)) from by
      ext δ <;> simp] at h3
    exact h3
  have hcomp := hfull.comp 0 hslice
  rw [show (c + 0 : QCoeff 4) = c from add_zero c] at hcomp
  have h2 := hasFDerivAt_patchA_shift hr (u 0, u 1, u 2) c
  have h2' : HasFDerivAt (fun δ : QCoeff 4 => psiAe r (c + δ, u))
      ((fderiv ℝ patchA (curveData r c (u 0, u 1, u 2))).comp
        (dataLin (u 0, u 1, u 2)).toContinuousLinearMap) 0 := by
    simpa only [psiAe_apply, psiA, Function.comp_def] using h2
  exact hcomp.fderiv.symm.trans h2'.fderiv


/-- **Site 6 of the rewrite pass.**  The range inclusion (`hsub`): the range of the derivative of
`patchA` at the data is contained in the range of the derivative of `psiAe r` at `(c,u)`.  The
latter contains the `inl`-part (site 5), whose range equals the former because the data-jet map
`dataLin` is surjective (its range is everything, so composing with it does not shrink the range).
The parameter triple is spelled out as `(u 0, u 1, u 2)` throughout. -/
lemma range_fderiv_patchA_le_fderiv_psiAe {r : ℝ → Space} (hr : IsSmoothKnot r)
    (c : QCoeff 4) (u : EuclideanSpace ℝ (Fin 3))
    (ha : u 0 ∈ Set.Ico 0 (2 * Real.pi)) (hb : u 1 ∈ Set.Ico 0 (2 * Real.pi))
    (hm : u 2 ∈ Set.Ico 0 (2 * Real.pi)) (hab : u 0 ≠ u 1) (ham : u 0 ≠ u 2) (hbm : u 1 ≠ u 2) :
    (fderiv ℝ patchA (curveData r c (u 0, u 1, u 2))).range
      ≤ (fderiv ℝ (psiAe r) (c, u)).range := by
  have hsurj : Function.Surjective (dataLin (u 0, u 1, u 2)) :=
    dataLin_surjective ha hb hm hab ham hbm
  have h1 : (fderiv ℝ patchA (curveData r c (u 0, u 1, u 2))).range
      = ((fderiv ℝ patchA (curveData r c (u 0, u 1, u 2))).comp
          (dataLin (u 0, u 1, u 2)).toContinuousLinearMap).range := by
    rw [ContinuousLinearMap.toLinearMap_comp, LinearMap.range_comp,
      show (↑(LinearMap.toContinuousLinearMap (dataLin (u 0, u 1, u 2))) :
        QCoeff 4 →ₗ[ℝ] TripleData).range = ⊤ from LinearMap.range_eq_top.mpr hsurj,
      Submodule.map_top]
  rw [h1, ← fderiv_psiAe_comp_inl hr c u]
  exact LinearMap.range_comp_le_range _ _



/-- **Site 7 of the rewrite pass.**  The transport of the range along `eTgt` (`hrange`): since
`psiAt r = eTgt ∘ psiAe r` (function-level, `psiAt_eq`), the range of `fderiv ℝ (psiAt r)` at
`(c,u)` is the image under `eTgt` of the range of `fderiv ℝ (psiAe r)` there.  The image map is
spelled as `(eTgt : … →L …).toLinearMap`, i.e. in the canonical spelling produced by
`ContinuousLinearMap.toLinearMap_comp`. -/
lemma range_fderiv_psiAt_eq (r : ℝ → Space) (hr : IsSmoothKnot r)
    (c : QCoeff 4) (u : EuclideanSpace ℝ (Fin 3)) :
    (fderiv ℝ (psiAt r) (c, u)).range
      = (fderiv ℝ (psiAe r) (c, u)).range.map
          ((eTgt : (Space × Space) →L[ℝ] Tgt).toLinearMap) := by
  have hfull : HasFDerivAt (fun z : Space × Space => eTgt z) (eTgt : (Space × Space) →L[ℝ] Tgt)
      (psiAe r (c, u)) := eTgt.toContinuousLinearMap.hasFDerivAt
  have hslice : HasFDerivAt (psiAe r) (fderiv ℝ (psiAe r) (c, u)) (c, u) :=
    hasFDerivAt_psiAe r hr c u
  have hcomp := hfull.comp (c, u) hslice
  have hder : fderiv ℝ (psiAt r) (c, u)
      = (eTgt : (Space × Space) →L[ℝ] Tgt).comp (fderiv ℝ (psiAe r) (c, u)) := by
    rw [show psiAt r = (fun z : Space × Space => eTgt z) ∘ psiAe r from psiAt_eq r]
    exact hcomp.fderiv
  rw [hder, ContinuousLinearMap.toLinearMap_comp, LinearMap.range_comp]

/-- Bridge between the two coercions of `eTgt`: the `Submodule.map` along
`(eTgt : … →L …).toLinearMap` and along `(eTgt : … →ₗ …)` agree (definitionally the same map). -/
lemma map_eTgt_toLinearMap_eq (S : Submodule ℝ (Space × Space)) :
    S.map ((eTgt : (Space × Space) →L[ℝ] Tgt).toLinearMap)
      = S.map (eTgt : (Space × Space) →ₗ[ℝ] Tgt) := rfl



/-- **Site 8 of the rewrite pass (the `hcol`/`hx`/`h4` cluster).**  At a zero of the transported
badness map `psiAt r`, the patch-`A` conditions have rank `≥ 4`: the zero gives the collinearity of
the data (`eTgt_eq_zero_iff` + `Prod.ext`), injectivity of the knot on a period gives
`dataP ≠ dataQ`, and `rank_patchA` concludes.  The coefficient vector is named `c₀` to avoid
shadowing, and the parameter triple is written out as `(u 0, u 1, u 2)`. -/
lemma rank_patchA_of_psiAt_zero (r : ℝ → Space) (c₀ : QCoeff 4)
    (u : EuclideanSpace ℝ (Fin 3)) (hknot : IsSmoothKnot (curve r 4 c₀))
    (ha : u 0 ∈ Set.Ico 0 period) (hb : u 1 ∈ Set.Ico 0 period) (hab : u 0 ≠ u 1)
    (hz : psiAt r (c₀, u) = 0) :
    4 ≤ Module.finrank ℝ
      (LinearMap.range ((fderiv ℝ patchA (curveData r c₀ (u 0, u 1, u 2))).toLinearMap)) := by
  have hpat : patchA (curveData r c₀ (u 0, u 1, u 2)) = 0 := by
    have h1 : eTgt (patchA (curveData r c₀ (u 0, u 1, u 2))) = 0 := by
      simpa only [psiAt_apply, psiA] using hz
    obtain ⟨hcol', hya'⟩ := (eTgt_eq_zero_iff).mp h1
    exact Prod.ext hcol' hya'
  have hcol : dataColl (curveData r c₀ (u 0, u 1, u 2)) = 0 := congrArg Prod.fst hpat
  have hx : dataP (curveData r c₀ (u 0, u 1, u 2)) -
      dataQ (curveData r c₀ (u 0, u 1, u 2)) ≠ 0 := by
    intro h
    have hEq : dataP (curveData r c₀ (u 0, u 1, u 2)) =
        dataQ (curveData r c₀ (u 0, u 1, u 2)) := sub_eq_zero.mp h
    exact hab (hknot.injective_on_period ha hb (by simpa [dataP, dataQ, curveData] using hEq))
  exact rank_patchA (x := curveData r c₀ (u 0, u 1, u 2)) hx hcol

/-- **P1, patch `A`.**  If `K` is a compact parameter region whose members are pairwise distinct
fundamental-domain parameters, and if every coefficient in the ball `closedBall 0 ρ` gives a
smooth knot, then the set of coefficients for which the patch `y_a = 0` occurs somewhere on `K`
has empty interior.

Proof (the three steps in the docstring): `interior_zeroSet_projection_empty_of_rank` applied to
`Ψ = psiA r` with `V = QCoeff 4`, `W = ℝ × ℝ × ℝ`, `F = Space × Space`, using
`finrank W = 3 < 4 ≤ finrank (range (fderiv ℝ patchA (curveData r c w))) = finrank (range (fderiv ℝ Ψ p))`
(chain rule + surjectivity of `dataLin w` (`dataLin_surjective`) + `rank_patchA`). -/
theorem patchA_bad_interior_empty {r : ℝ → Space} (hr : IsSmoothKnot r)
    {ρ : ℝ} {K : Set (EuclideanSpace ℝ (Fin 3))} (hK : IsCompact K)
    (hknot : ∀ c ∈ Metric.closedBall (0 : QCoeff 4) ρ, IsSmoothKnot (curve r 4 c))
    (hsep : ∀ u ∈ K, u 0 ∈ Set.Ico 0 (2 * Real.pi) ∧ u 1 ∈ Set.Ico 0 (2 * Real.pi) ∧
      u 2 ∈ Set.Ico 0 (2 * Real.pi) ∧ u 0 ≠ u 1 ∧ u 0 ≠ u 2 ∧ u 1 ≠ u 2) :
    interior {c : QCoeff 4 | c ∈ Metric.closedBall 0 ρ ∧ ∃ u ∈ K, psiAt r (c, u) = 0} = ∅ := by
  refine Work.Proj.interior_zeroSet_projection_empty_of_rank (Ψ := psiAt r)
    (Kv := Metric.closedBall (0 : QCoeff 4) ρ) (K := K) (contDiff_psiAt r hr)
    (isCompact_closedBall _ _) hK ?_
  rintro ⟨c, u⟩ hp hp0
  obtain ⟨hc, huK⟩ := hp
  obtain ⟨hs1, hs2, hs3, hd1, hd2, hd3⟩ := hsep u huK
  have hrange : (fderiv ℝ (psiAt r) (c, u)).range
      = (fderiv ℝ (psiAe r) (c, u)).range.map (eTgt : (Space × Space) →ₗ[ℝ] Tgt) := by
    rw [range_fderiv_psiAt_eq r hr c u, map_eTgt_toLinearMap_eq]
  have h4 := rank_patchA_of_psiAt_zero r c u (hknot c hc)
    (by rw [show period = 2 * Real.pi from rfl]; exact hs1)
    (by rw [show period = 2 * Real.pi from rfl]; exact hs2) hd1 hp0
  have hsub := Submodule.finrank_mono
    (range_fderiv_patchA_le_fderiv_psiAe hr c u hs1 hs2 hs3 hd1 hd2 hd3)
  rw [hrange, finrank_map_eTgt]
  exact lt_of_lt_of_le (by rw [finrank_euclideanSpace_fin]; norm_num) (le_trans h4 hsub)

/-! ## The mirror for the patch `P_b` (same eight sites, names swapped) -/

def psiB (r : ℝ → Space) : QCoeff 4 × (ℝ × ℝ × ℝ) → Space × Space :=
  fun p => patchB (curveData r p.1 p.2)

/-- The data map of the perturbed curve is `C¹` in `c` at fixed `w`, and its derivative is
`dataLin w` (the affine decomposition `curveData r c w = curveData r c₀ w + dataLin w (c - c₀)`
from `corr_add`/`corrD_add`). -/
def psiBe (r : ℝ → Space) : QCoeff 4 × EuclideanSpace ℝ (Fin 3) → Space × Space :=
  fun p => psiB r (p.1, (p.2 0, p.2 1, p.2 2))

/-- The badness map of the patch `A`, transported to the Euclidean target `Tgt = ℝ⁶` so that the
implicit-function-theorem tool (which requires inner product spaces on both variables) applies. -/
def psiBt (r : ℝ → Space) : QCoeff 4 × EuclideanSpace ℝ (Fin 3) → Tgt :=
  fun p => eTgt (psiBe r p)

lemma psiBe_eq (r : ℝ → Space) :
    psiBe r = fun p : QCoeff 4 × EuclideanSpace ℝ (Fin 3) =>
      psiB r (p.1, (p.2 0, p.2 1, p.2 2)) := rfl

/-- Function-level unfolding of `psiBt`. -/
lemma psiBt_eq (r : ℝ → Space) :
    psiBt r = fun p : QCoeff 4 × EuclideanSpace ℝ (Fin 3) =>
      eTgt (psiB r (p.1, (p.2 0, p.2 1, p.2 2))) := rfl

/-- Pointwise unfolding of `psiBe` (for use under binders). -/
@[simp] lemma psiBe_apply (r : ℝ → Space) (p : QCoeff 4 × EuclideanSpace ℝ (Fin 3)) :
    psiBe r p = psiB r (p.1, (p.2 0, p.2 1, p.2 2)) := rfl

/-- Pointwise unfolding of `psiBt` (for use under binders). -/
@[simp] lemma psiBt_apply (r : ℝ → Space) (p : QCoeff 4 × EuclideanSpace ℝ (Fin 3)) :
    psiBt r p = eTgt (psiB r (p.1, (p.2 0, p.2 1, p.2 2))) := rfl


/-- **The rewrite that collapses the unapplied site**: `ContDiff ℝ 1 (psiBe r)` is *definitionally*
the smoothness of the explicit lambda, so `rw [psiBe_eq]` closes it (`rwa` below). -/
lemma contDiff_psiBe_iff (r : ℝ → Space) :
    ContDiff ℝ 1 (psiBe r) ↔ ContDiff ℝ 1 (fun p : QCoeff 4 × EuclideanSpace ℝ (Fin 3) =>
      psiB r (p.1, (p.2 0, p.2 1, p.2 2))) := by
  rw [psiBe_eq]

/-- Same collapse for `psiBt`. -/
lemma contDiff_psiBt_iff (r : ℝ → Space) :
    ContDiff ℝ 1 (psiBt r) ↔ ContDiff ℝ 1 (fun p : QCoeff 4 × EuclideanSpace ℝ (Fin 3) =>
      eTgt (psiB r (p.1, (p.2 0, p.2 1, p.2 2)))) := by
  rw [psiBt_eq]

/-- Same collapse at the level of Fréchet derivatives. -/
lemma hasFDerivAt_psiBe_iff (r : ℝ → Space)
    (c₀ : QCoeff 4 × EuclideanSpace ℝ (Fin 3)) (L' : (QCoeff 4 × EuclideanSpace ℝ (Fin 3)) →L[ℝ] (Space × Space)) :
    HasFDerivAt (psiBe r) L' c₀ ↔ HasFDerivAt
      (fun p : QCoeff 4 × EuclideanSpace ℝ (Fin 3) =>
        psiB r (p.1, (p.2 0, p.2 1, p.2 2))) L' c₀ := by
  rw [psiBe_eq]


/-- **Site 1 of the rewrite pass.**  The joint smoothness of the patch-`A` badness map, in the
wrapper form: obtained from the explicit-lambda form by a single `rw [psiBe_eq]`, then
`ContDiff.comp` of `rpb_contDiff_patchB` with `contDiff_curveData_joint` through the triple
reindexing.  (In the proof of `patchB_bad_interior_empty` this is the `hPsiAe` step.) -/
lemma contDiff_psiBe (r : ℝ → Space) (hr : IsSmoothKnot r) : ContDiff ℝ 1 (psiBe r) := by
  rw [psiBe_eq]
  have h1 : ContDiff ℝ 1 (psiB r) := rpb_contDiff_patchB.comp (contDiff_curveData_joint hr)
  have h2 : ContDiff ℝ 1 (fun p : QCoeff 4 × EuclideanSpace ℝ (Fin 3) =>
      (p.1, (p.2 0, p.2 1, p.2 2))) := by fun_prop
  exact h1.comp h2

/-- **Site 2 of the rewrite pass.**  The joint smoothness of the transported badness map
`psiBt = eTgt ∘ psiBe`, by a single `rw [psiBt_eq]` and site 1.  (This is the `hPsi` step of the
main theorem, i.e. the `ContDiff ℝ 1 Ψ` hypothesis of the rank tool.) -/
lemma contDiff_psiBt (r : ℝ → Space) (hr : IsSmoothKnot r) : ContDiff ℝ 1 (psiBt r) := by
  rw [psiBt_eq]
  exact ((eTgt : (Space × Space) →L[ℝ] Tgt).contDiff).comp (contDiff_psiBe r hr)


/-- **Site 3 of the rewrite pass.**  The Fréchet derivative of `psiBe r` at `(c,u)`, in the wrapper
form: `rw [psiBe_eq]` reduces it to the `HasFDerivAt` of the explicit lambda, which follows from
site 1.  (This is the `hfull` step of the main theorem.)  The statement is given at the point
`(c + 0, u)` as well, which is the shape `HasFDerivAt.comp` needs. -/
lemma hasFDerivAt_psiBe (r : ℝ → Space) (hr : IsSmoothKnot r)
    (c : QCoeff 4) (u : EuclideanSpace ℝ (Fin 3)) :
    HasFDerivAt (psiBe r) (fderiv ℝ (psiBe r) (c, u)) (c, u) := by
  rw [psiBe_eq]
  exact ((contDiff_psiBe r hr).differentiable (by norm_num)).differentiableAt.hasFDerivAt

/-- Site 3 at the shifted point shape used inside the proof of
`patchB_bad_interior_empty`. -/
lemma hasFDerivAt_psiBe_shift (r : ℝ → Space) (hr : IsSmoothKnot r)
    (c : QCoeff 4) (u : EuclideanSpace ℝ (Fin 3)) :
    HasFDerivAt (psiBe r) (fderiv ℝ (psiBe r) (c + 0, u)) (c + 0, u) := by
  simpa only [add_zero] using hasFDerivAt_psiBe r hr c u


/-- **Site 4 of the rewrite pass (applied occurrence: the `hsliceA`/`hsliceDATA` pair).**
The derivative of the shifted data map and of the shifted patch map, in the plain vocabulary used
inside `patchB_bad_interior_empty`.  The points are written as `(… ) 0` so that
`HasFDerivAt.comp` sees matching terms. -/
lemma hasFDerivAt_patchB_shift {r : ℝ → Space} (hr : IsSmoothKnot r)
    (w : ℝ × ℝ × ℝ) (c : QCoeff 4) :
    HasFDerivAt (fun δ : QCoeff 4 => patchB (curveData r (c + δ) w))
      ((fderiv ℝ patchB (curveData r c w)).comp (dataLin w).toContinuousLinearMap) 0 := by
  have hT : HasFDerivAt patchB
      (fderiv ℝ patchB ((fun δ : QCoeff 4 => curveData r (c + δ) w) 0))
      ((fun δ : QCoeff 4 => curveData r (c + δ) w) 0) := by
    simpa using (((rpb_contDiff_patchB.differentiable (by norm_num)).differentiableAt
      (x := curveData r c w)).hasFDerivAt)
  have h3 := hT.comp 0 (hasFDerivAt_curveData_shift hr w c)
  simpa [Function.comp_def] using h3


/-- **Site 5 of the rewrite pass.**  The `inl`-part of the derivative of `psiBe r` at `(c,u)` is the
slice derivative of the patch map: by uniqueness of derivatives, applied to the slice
`δ ↦ (c + δ, u)`.  This is the `hinl` step of `patchB_bad_interior_empty`, with the parameter triple
written out as `(u 0, u 1, u 2)` so that no `set`-bound variable is involved. -/
lemma fderiv_psiBe_comp_inl {r : ℝ → Space} (hr : IsSmoothKnot r)
    (c : QCoeff 4) (u : EuclideanSpace ℝ (Fin 3)) :
    (fderiv ℝ (psiBe r) (c, u)).comp
        (ContinuousLinearMap.inl ℝ (QCoeff 4) (EuclideanSpace ℝ (Fin 3)))
      = (fderiv ℝ patchB (curveData r c (u 0, u 1, u 2))).comp
        (dataLin (u 0, u 1, u 2)).toContinuousLinearMap := by
  have hfull := hasFDerivAt_psiBe_shift r hr c u
  have hslice : HasFDerivAt (fun δ : QCoeff 4 => (c + δ, u))
      (ContinuousLinearMap.inl ℝ (QCoeff 4) (EuclideanSpace ℝ (Fin 3))) 0 := by
    have h1 : HasFDerivAt (fun δ : QCoeff 4 => c + δ) (1 : QCoeff 4 →L[ℝ] QCoeff 4) 0 :=
      (hasFDerivAt_id (0 : QCoeff 4)).const_add c
    have h2 : HasFDerivAt (fun _ : QCoeff 4 => u)
        (0 : QCoeff 4 →L[ℝ] EuclideanSpace ℝ (Fin 3)) 0 := hasFDerivAt_const u 0
    have h3 := h1.prodMk h2
    rw [show ((1 : QCoeff 4 →L[ℝ] QCoeff 4).prod
        (0 : QCoeff 4 →L[ℝ] EuclideanSpace ℝ (Fin 3)))
        = ContinuousLinearMap.inl ℝ (QCoeff 4) (EuclideanSpace ℝ (Fin 3)) from by
      ext δ <;> simp] at h3
    exact h3
  have hcomp := hfull.comp 0 hslice
  rw [show (c + 0 : QCoeff 4) = c from add_zero c] at hcomp
  have h2 := hasFDerivAt_patchB_shift hr (u 0, u 1, u 2) c
  have h2' : HasFDerivAt (fun δ : QCoeff 4 => psiBe r (c + δ, u))
      ((fderiv ℝ patchB (curveData r c (u 0, u 1, u 2))).comp
        (dataLin (u 0, u 1, u 2)).toContinuousLinearMap) 0 := by
    simpa only [psiBe_apply, psiB, Function.comp_def] using h2
  exact hcomp.fderiv.symm.trans h2'.fderiv


/-- **Site 6 of the rewrite pass.**  The range inclusion (`hsub`): the range of the derivative of
`patchB` at the data is contained in the range of the derivative of `psiBe r` at `(c,u)`.  The
latter contains the `inl`-part (site 5), whose range equals the former because the data-jet map
`dataLin` is surjective (its range is everything, so composing with it does not shrink the range).
The parameter triple is spelled out as `(u 0, u 1, u 2)` throughout. -/
lemma range_fderiv_patchB_le_fderiv_psiBe {r : ℝ → Space} (hr : IsSmoothKnot r)
    (c : QCoeff 4) (u : EuclideanSpace ℝ (Fin 3))
    (ha : u 0 ∈ Set.Ico 0 (2 * Real.pi)) (hb : u 1 ∈ Set.Ico 0 (2 * Real.pi))
    (hm : u 2 ∈ Set.Ico 0 (2 * Real.pi)) (hab : u 0 ≠ u 1) (ham : u 0 ≠ u 2) (hbm : u 1 ≠ u 2) :
    (fderiv ℝ patchB (curveData r c (u 0, u 1, u 2))).range
      ≤ (fderiv ℝ (psiBe r) (c, u)).range := by
  have hsurj : Function.Surjective (dataLin (u 0, u 1, u 2)) :=
    dataLin_surjective ha hb hm hab ham hbm
  have h1 : (fderiv ℝ patchB (curveData r c (u 0, u 1, u 2))).range
      = ((fderiv ℝ patchB (curveData r c (u 0, u 1, u 2))).comp
          (dataLin (u 0, u 1, u 2)).toContinuousLinearMap).range := by
    rw [ContinuousLinearMap.toLinearMap_comp, LinearMap.range_comp,
      show (↑(LinearMap.toContinuousLinearMap (dataLin (u 0, u 1, u 2))) :
        QCoeff 4 →ₗ[ℝ] TripleData).range = ⊤ from LinearMap.range_eq_top.mpr hsurj,
      Submodule.map_top]
  rw [h1, ← fderiv_psiBe_comp_inl hr c u]
  exact LinearMap.range_comp_le_range _ _



/-- **Site 7 of the rewrite pass.**  The transport of the range along `eTgt` (`hrange`): since
`psiBt r = eTgt ∘ psiBe r` (function-level, `psiBt_eq`), the range of `fderiv ℝ (psiBt r)` at
`(c,u)` is the image under `eTgt` of the range of `fderiv ℝ (psiBe r)` there.  The image map is
spelled as `(eTgt : … →L …).toLinearMap`, i.e. in the canonical spelling produced by
`ContinuousLinearMap.toLinearMap_comp`. -/
lemma range_fderiv_psiBt_eq (r : ℝ → Space) (hr : IsSmoothKnot r)
    (c : QCoeff 4) (u : EuclideanSpace ℝ (Fin 3)) :
    (fderiv ℝ (psiBt r) (c, u)).range
      = (fderiv ℝ (psiBe r) (c, u)).range.map
          ((eTgt : (Space × Space) →L[ℝ] Tgt).toLinearMap) := by
  have hfull : HasFDerivAt (fun z : Space × Space => eTgt z) (eTgt : (Space × Space) →L[ℝ] Tgt)
      (psiBe r (c, u)) := eTgt.toContinuousLinearMap.hasFDerivAt
  have hslice : HasFDerivAt (psiBe r) (fderiv ℝ (psiBe r) (c, u)) (c, u) :=
    hasFDerivAt_psiBe r hr c u
  have hcomp := hfull.comp (c, u) hslice
  have hder : fderiv ℝ (psiBt r) (c, u)
      = (eTgt : (Space × Space) →L[ℝ] Tgt).comp (fderiv ℝ (psiBe r) (c, u)) := by
    rw [show psiBt r = (fun z : Space × Space => eTgt z) ∘ psiBe r from psiBt_eq r]
    exact hcomp.fderiv
  rw [hder, ContinuousLinearMap.toLinearMap_comp, LinearMap.range_comp]

/-- Bridge between the two coercions of `eTgt`: the `Submodule.map` along
`(eTgt : … →L …).toLinearMap` and along `(eTgt : … →ₗ …)` agree (definitionally the same map). -/
lemma rank_patchB_of_psiBt_zero (r : ℝ → Space) (c₀ : QCoeff 4)
    (u : EuclideanSpace ℝ (Fin 3)) (hknot : IsSmoothKnot (curve r 4 c₀))
    (ha : u 0 ∈ Set.Ico 0 period) (hb : u 1 ∈ Set.Ico 0 period) (hab : u 0 ≠ u 1)
    (hz : psiBt r (c₀, u) = 0) :
    4 ≤ Module.finrank ℝ
      (LinearMap.range ((fderiv ℝ patchB (curveData r c₀ (u 0, u 1, u 2))).toLinearMap)) := by
  have hpat : patchB (curveData r c₀ (u 0, u 1, u 2)) = 0 := by
    have h1 : eTgt (patchB (curveData r c₀ (u 0, u 1, u 2))) = 0 := by
      simpa only [psiBt_apply, psiB] using hz
    obtain ⟨hcol', hya'⟩ := (eTgt_eq_zero_iff).mp h1
    exact Prod.ext hcol' hya'
  have hcol : dataColl (curveData r c₀ (u 0, u 1, u 2)) = 0 := congrArg Prod.fst hpat
  have hx : dataP (curveData r c₀ (u 0, u 1, u 2)) -
      dataQ (curveData r c₀ (u 0, u 1, u 2)) ≠ 0 := by
    intro h
    have hEq : dataP (curveData r c₀ (u 0, u 1, u 2)) =
        dataQ (curveData r c₀ (u 0, u 1, u 2)) := sub_eq_zero.mp h
    exact hab (hknot.injective_on_period ha hb (by simpa [dataP, dataQ, curveData] using hEq))
  exact rank_patchB (x := curveData r c₀ (u 0, u 1, u 2)) hx hcol

/-- **P1, patch `A`.**  If `K` is a compact parameter region whose members are pairwise distinct
fundamental-domain parameters, and if every coefficient in the ball `closedBall 0 ρ` gives a
smooth knot, then the set of coefficients for which the patch `y_a = 0` occurs somewhere on `K`
has empty interior.

Proof (the three steps in the docstring): `interior_zeroSet_projection_empty_of_rank` applied to
`Ψ = psiB r` with `V = QCoeff 4`, `W = ℝ × ℝ × ℝ`, `F = Space × Space`, using
`finrank W = 3 < 4 ≤ finrank (range (fderiv ℝ patchB (curveData r c w))) = finrank (range (fderiv ℝ Ψ p))`
(chain rule + surjectivity of `dataLin w` (`dataLin_surjective`) + `rank_patchB`). -/
theorem patchB_bad_interior_empty {r : ℝ → Space} (hr : IsSmoothKnot r)
    {ρ : ℝ} {K : Set (EuclideanSpace ℝ (Fin 3))} (hK : IsCompact K)
    (hknot : ∀ c ∈ Metric.closedBall (0 : QCoeff 4) ρ, IsSmoothKnot (curve r 4 c))
    (hsep : ∀ u ∈ K, u 0 ∈ Set.Ico 0 (2 * Real.pi) ∧ u 1 ∈ Set.Ico 0 (2 * Real.pi) ∧
      u 2 ∈ Set.Ico 0 (2 * Real.pi) ∧ u 0 ≠ u 1 ∧ u 0 ≠ u 2 ∧ u 1 ≠ u 2) :
    interior {c : QCoeff 4 | c ∈ Metric.closedBall 0 ρ ∧ ∃ u ∈ K, psiBt r (c, u) = 0} = ∅ := by
  refine Work.Proj.interior_zeroSet_projection_empty_of_rank (Ψ := psiBt r)
    (Kv := Metric.closedBall (0 : QCoeff 4) ρ) (K := K) (contDiff_psiBt r hr)
    (isCompact_closedBall _ _) hK ?_
  rintro ⟨c, u⟩ hp hp0
  obtain ⟨hc, huK⟩ := hp
  obtain ⟨hs1, hs2, hs3, hd1, hd2, hd3⟩ := hsep u huK
  have hrange : (fderiv ℝ (psiBt r) (c, u)).range
      = (fderiv ℝ (psiBe r) (c, u)).range.map (eTgt : (Space × Space) →ₗ[ℝ] Tgt) := by
    rw [range_fderiv_psiBt_eq r hr c u, map_eTgt_toLinearMap_eq]
  have h4 := rank_patchB_of_psiBt_zero r c u (hknot c hc)
    (by rw [show period = 2 * Real.pi from rfl]; exact hs1)
    (by rw [show period = 2 * Real.pi from rfl]; exact hs2) hd1 hp0
  have hsub := Submodule.finrank_mono
    (range_fderiv_patchB_le_fderiv_psiBe hr c u hs1 hs2 hs3 hd1 hd2 hd3)
  rw [hrange, finrank_map_eTgt]
  exact lt_of_lt_of_le (by rw [finrank_euclideanSpace_fin]; norm_num) (le_trans h4 hsub)

/-! ## The mirror for the patch `P_m` (same eight sites, names swapped) -/

def psiM (r : ℝ → Space) : QCoeff 4 × (ℝ × ℝ × ℝ) → Space × Space :=
  fun p => patchM (curveData r p.1 p.2)

/-- The data map of the perturbed curve is `C¹` in `c` at fixed `w`, and its derivative is
`dataLin w` (the affine decomposition `curveData r c w = curveData r c₀ w + dataLin w (c - c₀)`
from `corr_add`/`corrD_add`). -/
def psiMe (r : ℝ → Space) : QCoeff 4 × EuclideanSpace ℝ (Fin 3) → Space × Space :=
  fun p => psiM r (p.1, (p.2 0, p.2 1, p.2 2))

/-- The badness map of the patch `A`, transported to the Euclidean target `Tgt = ℝ⁶` so that the
implicit-function-theorem tool (which requires inner product spaces on both variables) applies. -/
def psiMt (r : ℝ → Space) : QCoeff 4 × EuclideanSpace ℝ (Fin 3) → Tgt :=
  fun p => eTgt (psiMe r p)

lemma psiMe_eq (r : ℝ → Space) :
    psiMe r = fun p : QCoeff 4 × EuclideanSpace ℝ (Fin 3) =>
      psiM r (p.1, (p.2 0, p.2 1, p.2 2)) := rfl

/-- Function-level unfolding of `psiMt`. -/
lemma psiMt_eq (r : ℝ → Space) :
    psiMt r = fun p : QCoeff 4 × EuclideanSpace ℝ (Fin 3) =>
      eTgt (psiM r (p.1, (p.2 0, p.2 1, p.2 2))) := rfl

/-- Pointwise unfolding of `psiMe` (for use under binders). -/
@[simp] lemma psiMe_apply (r : ℝ → Space) (p : QCoeff 4 × EuclideanSpace ℝ (Fin 3)) :
    psiMe r p = psiM r (p.1, (p.2 0, p.2 1, p.2 2)) := rfl

/-- Pointwise unfolding of `psiMt` (for use under binders). -/
@[simp] lemma psiMt_apply (r : ℝ → Space) (p : QCoeff 4 × EuclideanSpace ℝ (Fin 3)) :
    psiMt r p = eTgt (psiM r (p.1, (p.2 0, p.2 1, p.2 2))) := rfl


/-- **The rewrite that collapses the unapplied site**: `ContDiff ℝ 1 (psiMe r)` is *definitionally*
the smoothness of the explicit lambda, so `rw [psiMe_eq]` closes it (`rwa` below). -/
lemma contDiff_psiMe_iff (r : ℝ → Space) :
    ContDiff ℝ 1 (psiMe r) ↔ ContDiff ℝ 1 (fun p : QCoeff 4 × EuclideanSpace ℝ (Fin 3) =>
      psiM r (p.1, (p.2 0, p.2 1, p.2 2))) := by
  rw [psiMe_eq]

/-- Same collapse for `psiMt`. -/
lemma contDiff_psiMt_iff (r : ℝ → Space) :
    ContDiff ℝ 1 (psiMt r) ↔ ContDiff ℝ 1 (fun p : QCoeff 4 × EuclideanSpace ℝ (Fin 3) =>
      eTgt (psiM r (p.1, (p.2 0, p.2 1, p.2 2)))) := by
  rw [psiMt_eq]

/-- Same collapse at the level of Fréchet derivatives. -/
lemma hasFDerivAt_psiMe_iff (r : ℝ → Space)
    (c₀ : QCoeff 4 × EuclideanSpace ℝ (Fin 3)) (L' : (QCoeff 4 × EuclideanSpace ℝ (Fin 3)) →L[ℝ] (Space × Space)) :
    HasFDerivAt (psiMe r) L' c₀ ↔ HasFDerivAt
      (fun p : QCoeff 4 × EuclideanSpace ℝ (Fin 3) =>
        psiM r (p.1, (p.2 0, p.2 1, p.2 2))) L' c₀ := by
  rw [psiMe_eq]


/-- **Site 1 of the rewrite pass.**  The joint smoothness of the patch-`A` badness map, in the
wrapper form: obtained from the explicit-lambda form by a single `rw [psiMe_eq]`, then
`ContDiff.comp` of `rpm_contDiff_patchM` with `contDiff_curveData_joint` through the triple
reindexing.  (In the proof of `patchM_bad_interior_empty` this is the `hPsiAe` step.) -/
lemma contDiff_psiMe (r : ℝ → Space) (hr : IsSmoothKnot r) : ContDiff ℝ 1 (psiMe r) := by
  rw [psiMe_eq]
  have h1 : ContDiff ℝ 1 (psiM r) := rpm_contDiff_patchM.comp (contDiff_curveData_joint hr)
  have h2 : ContDiff ℝ 1 (fun p : QCoeff 4 × EuclideanSpace ℝ (Fin 3) =>
      (p.1, (p.2 0, p.2 1, p.2 2))) := by fun_prop
  exact h1.comp h2

/-- **Site 2 of the rewrite pass.**  The joint smoothness of the transported badness map
`psiMt = eTgt ∘ psiMe`, by a single `rw [psiMt_eq]` and site 1.  (This is the `hPsi` step of the
main theorem, i.e. the `ContDiff ℝ 1 Ψ` hypothesis of the rank tool.) -/
lemma contDiff_psiMt (r : ℝ → Space) (hr : IsSmoothKnot r) : ContDiff ℝ 1 (psiMt r) := by
  rw [psiMt_eq]
  exact ((eTgt : (Space × Space) →L[ℝ] Tgt).contDiff).comp (contDiff_psiMe r hr)


/-- **Site 3 of the rewrite pass.**  The Fréchet derivative of `psiMe r` at `(c,u)`, in the wrapper
form: `rw [psiMe_eq]` reduces it to the `HasFDerivAt` of the explicit lambda, which follows from
site 1.  (This is the `hfull` step of the main theorem.)  The statement is given at the point
`(c + 0, u)` as well, which is the shape `HasFDerivAt.comp` needs. -/
lemma hasFDerivAt_psiMe (r : ℝ → Space) (hr : IsSmoothKnot r)
    (c : QCoeff 4) (u : EuclideanSpace ℝ (Fin 3)) :
    HasFDerivAt (psiMe r) (fderiv ℝ (psiMe r) (c, u)) (c, u) := by
  rw [psiMe_eq]
  exact ((contDiff_psiMe r hr).differentiable (by norm_num)).differentiableAt.hasFDerivAt

/-- Site 3 at the shifted point shape used inside the proof of
`patchM_bad_interior_empty`. -/
lemma hasFDerivAt_psiMe_shift (r : ℝ → Space) (hr : IsSmoothKnot r)
    (c : QCoeff 4) (u : EuclideanSpace ℝ (Fin 3)) :
    HasFDerivAt (psiMe r) (fderiv ℝ (psiMe r) (c + 0, u)) (c + 0, u) := by
  simpa only [add_zero] using hasFDerivAt_psiMe r hr c u


/-- **Site 4 of the rewrite pass (applied occurrence: the `hsliceA`/`hsliceDATA` pair).**
The derivative of the shifted data map and of the shifted patch map, in the plain vocabulary used
inside `patchM_bad_interior_empty`.  The points are written as `(… ) 0` so that
`HasFDerivAt.comp` sees matching terms. -/
lemma hasFDerivAt_patchM_shift {r : ℝ → Space} (hr : IsSmoothKnot r)
    (w : ℝ × ℝ × ℝ) (c : QCoeff 4) :
    HasFDerivAt (fun δ : QCoeff 4 => patchM (curveData r (c + δ) w))
      ((fderiv ℝ patchM (curveData r c w)).comp (dataLin w).toContinuousLinearMap) 0 := by
  have hT : HasFDerivAt patchM
      (fderiv ℝ patchM ((fun δ : QCoeff 4 => curveData r (c + δ) w) 0))
      ((fun δ : QCoeff 4 => curveData r (c + δ) w) 0) := by
    simpa using (((rpm_contDiff_patchM.differentiable (by norm_num)).differentiableAt
      (x := curveData r c w)).hasFDerivAt)
  have h3 := hT.comp 0 (hasFDerivAt_curveData_shift hr w c)
  simpa [Function.comp_def] using h3


/-- **Site 5 of the rewrite pass.**  The `inl`-part of the derivative of `psiMe r` at `(c,u)` is the
slice derivative of the patch map: by uniqueness of derivatives, applied to the slice
`δ ↦ (c + δ, u)`.  This is the `hinl` step of `patchM_bad_interior_empty`, with the parameter triple
written out as `(u 0, u 1, u 2)` so that no `set`-bound variable is involved. -/
lemma fderiv_psiMe_comp_inl {r : ℝ → Space} (hr : IsSmoothKnot r)
    (c : QCoeff 4) (u : EuclideanSpace ℝ (Fin 3)) :
    (fderiv ℝ (psiMe r) (c, u)).comp
        (ContinuousLinearMap.inl ℝ (QCoeff 4) (EuclideanSpace ℝ (Fin 3)))
      = (fderiv ℝ patchM (curveData r c (u 0, u 1, u 2))).comp
        (dataLin (u 0, u 1, u 2)).toContinuousLinearMap := by
  have hfull := hasFDerivAt_psiMe_shift r hr c u
  have hslice : HasFDerivAt (fun δ : QCoeff 4 => (c + δ, u))
      (ContinuousLinearMap.inl ℝ (QCoeff 4) (EuclideanSpace ℝ (Fin 3))) 0 := by
    have h1 : HasFDerivAt (fun δ : QCoeff 4 => c + δ) (1 : QCoeff 4 →L[ℝ] QCoeff 4) 0 :=
      (hasFDerivAt_id (0 : QCoeff 4)).const_add c
    have h2 : HasFDerivAt (fun _ : QCoeff 4 => u)
        (0 : QCoeff 4 →L[ℝ] EuclideanSpace ℝ (Fin 3)) 0 := hasFDerivAt_const u 0
    have h3 := h1.prodMk h2
    rw [show ((1 : QCoeff 4 →L[ℝ] QCoeff 4).prod
        (0 : QCoeff 4 →L[ℝ] EuclideanSpace ℝ (Fin 3)))
        = ContinuousLinearMap.inl ℝ (QCoeff 4) (EuclideanSpace ℝ (Fin 3)) from by
      ext δ <;> simp] at h3
    exact h3
  have hcomp := hfull.comp 0 hslice
  rw [show (c + 0 : QCoeff 4) = c from add_zero c] at hcomp
  have h2 := hasFDerivAt_patchM_shift hr (u 0, u 1, u 2) c
  have h2' : HasFDerivAt (fun δ : QCoeff 4 => psiMe r (c + δ, u))
      ((fderiv ℝ patchM (curveData r c (u 0, u 1, u 2))).comp
        (dataLin (u 0, u 1, u 2)).toContinuousLinearMap) 0 := by
    simpa only [psiMe_apply, psiM, Function.comp_def] using h2
  exact hcomp.fderiv.symm.trans h2'.fderiv


/-- **Site 6 of the rewrite pass.**  The range inclusion (`hsub`): the range of the derivative of
`patchM` at the data is contained in the range of the derivative of `psiMe r` at `(c,u)`.  The
latter contains the `inl`-part (site 5), whose range equals the former because the data-jet map
`dataLin` is surjective (its range is everything, so composing with it does not shrink the range).
The parameter triple is spelled out as `(u 0, u 1, u 2)` throughout. -/
lemma range_fderiv_patchM_le_fderiv_psiMe {r : ℝ → Space} (hr : IsSmoothKnot r)
    (c : QCoeff 4) (u : EuclideanSpace ℝ (Fin 3))
    (ha : u 0 ∈ Set.Ico 0 (2 * Real.pi)) (hb : u 1 ∈ Set.Ico 0 (2 * Real.pi))
    (hm : u 2 ∈ Set.Ico 0 (2 * Real.pi)) (hab : u 0 ≠ u 1) (ham : u 0 ≠ u 2) (hbm : u 1 ≠ u 2) :
    (fderiv ℝ patchM (curveData r c (u 0, u 1, u 2))).range
      ≤ (fderiv ℝ (psiMe r) (c, u)).range := by
  have hsurj : Function.Surjective (dataLin (u 0, u 1, u 2)) :=
    dataLin_surjective ha hb hm hab ham hbm
  have h1 : (fderiv ℝ patchM (curveData r c (u 0, u 1, u 2))).range
      = ((fderiv ℝ patchM (curveData r c (u 0, u 1, u 2))).comp
          (dataLin (u 0, u 1, u 2)).toContinuousLinearMap).range := by
    rw [ContinuousLinearMap.toLinearMap_comp, LinearMap.range_comp,
      show (↑(LinearMap.toContinuousLinearMap (dataLin (u 0, u 1, u 2))) :
        QCoeff 4 →ₗ[ℝ] TripleData).range = ⊤ from LinearMap.range_eq_top.mpr hsurj,
      Submodule.map_top]
  rw [h1, ← fderiv_psiMe_comp_inl hr c u]
  exact LinearMap.range_comp_le_range _ _



/-- **Site 7 of the rewrite pass.**  The transport of the range along `eTgt` (`hrange`): since
`psiMt r = eTgt ∘ psiMe r` (function-level, `psiMt_eq`), the range of `fderiv ℝ (psiMt r)` at
`(c,u)` is the image under `eTgt` of the range of `fderiv ℝ (psiMe r)` there.  The image map is
spelled as `(eTgt : … →L …).toLinearMap`, i.e. in the canonical spelling produced by
`ContinuousLinearMap.toLinearMap_comp`. -/
lemma range_fderiv_psiMt_eq (r : ℝ → Space) (hr : IsSmoothKnot r)
    (c : QCoeff 4) (u : EuclideanSpace ℝ (Fin 3)) :
    (fderiv ℝ (psiMt r) (c, u)).range
      = (fderiv ℝ (psiMe r) (c, u)).range.map
          ((eTgt : (Space × Space) →L[ℝ] Tgt).toLinearMap) := by
  have hfull : HasFDerivAt (fun z : Space × Space => eTgt z) (eTgt : (Space × Space) →L[ℝ] Tgt)
      (psiMe r (c, u)) := eTgt.toContinuousLinearMap.hasFDerivAt
  have hslice : HasFDerivAt (psiMe r) (fderiv ℝ (psiMe r) (c, u)) (c, u) :=
    hasFDerivAt_psiMe r hr c u
  have hcomp := hfull.comp (c, u) hslice
  have hder : fderiv ℝ (psiMt r) (c, u)
      = (eTgt : (Space × Space) →L[ℝ] Tgt).comp (fderiv ℝ (psiMe r) (c, u)) := by
    rw [show psiMt r = (fun z : Space × Space => eTgt z) ∘ psiMe r from psiMt_eq r]
    exact hcomp.fderiv
  rw [hder, ContinuousLinearMap.toLinearMap_comp, LinearMap.range_comp]

/-- Bridge between the two coercions of `eTgt`: the `Submodule.map` along
`(eTgt : … →L …).toLinearMap` and along `(eTgt : … →ₗ …)` agree (definitionally the same map). -/
lemma rank_patchM_of_psiMt_zero (r : ℝ → Space) (c₀ : QCoeff 4)
    (u : EuclideanSpace ℝ (Fin 3)) (hknot : IsSmoothKnot (curve r 4 c₀))
    (ha : u 0 ∈ Set.Ico 0 period) (hb : u 1 ∈ Set.Ico 0 period) (hab : u 0 ≠ u 1)
    (hz : psiMt r (c₀, u) = 0) :
    4 ≤ Module.finrank ℝ
      (LinearMap.range ((fderiv ℝ patchM (curveData r c₀ (u 0, u 1, u 2))).toLinearMap)) := by
  have hpat : patchM (curveData r c₀ (u 0, u 1, u 2)) = 0 := by
    have h1 : eTgt (patchM (curveData r c₀ (u 0, u 1, u 2))) = 0 := by
      simpa only [psiMt_apply, psiM] using hz
    obtain ⟨hcol', hya'⟩ := (eTgt_eq_zero_iff).mp h1
    exact Prod.ext hcol' hya'
  have hcol : dataColl (curveData r c₀ (u 0, u 1, u 2)) = 0 := congrArg Prod.fst hpat
  have hx : dataP (curveData r c₀ (u 0, u 1, u 2)) -
      dataQ (curveData r c₀ (u 0, u 1, u 2)) ≠ 0 := by
    intro h
    have hEq : dataP (curveData r c₀ (u 0, u 1, u 2)) =
        dataQ (curveData r c₀ (u 0, u 1, u 2)) := sub_eq_zero.mp h
    exact hab (hknot.injective_on_period ha hb (by simpa [dataP, dataQ, curveData] using hEq))
  exact rank_patchM (x := curveData r c₀ (u 0, u 1, u 2)) hx hcol

/-- **P1, patch `A`.**  If `K` is a compact parameter region whose members are pairwise distinct
fundamental-domain parameters, and if every coefficient in the ball `closedBall 0 ρ` gives a
smooth knot, then the set of coefficients for which the patch `y_a = 0` occurs somewhere on `K`
has empty interior.

Proof (the three steps in the docstring): `interior_zeroSet_projection_empty_of_rank` applied to
`Ψ = psiM r` with `V = QCoeff 4`, `W = ℝ × ℝ × ℝ`, `F = Space × Space`, using
`finrank W = 3 < 4 ≤ finrank (range (fderiv ℝ patchM (curveData r c w))) = finrank (range (fderiv ℝ Ψ p))`
(chain rule + surjectivity of `dataLin w` (`dataLin_surjective`) + `rank_patchM`). -/
theorem patchM_bad_interior_empty {r : ℝ → Space} (hr : IsSmoothKnot r)
    {ρ : ℝ} {K : Set (EuclideanSpace ℝ (Fin 3))} (hK : IsCompact K)
    (hknot : ∀ c ∈ Metric.closedBall (0 : QCoeff 4) ρ, IsSmoothKnot (curve r 4 c))
    (hsep : ∀ u ∈ K, u 0 ∈ Set.Ico 0 (2 * Real.pi) ∧ u 1 ∈ Set.Ico 0 (2 * Real.pi) ∧
      u 2 ∈ Set.Ico 0 (2 * Real.pi) ∧ u 0 ≠ u 1 ∧ u 0 ≠ u 2 ∧ u 1 ≠ u 2) :
    interior {c : QCoeff 4 | c ∈ Metric.closedBall 0 ρ ∧ ∃ u ∈ K, psiMt r (c, u) = 0} = ∅ := by
  refine Work.Proj.interior_zeroSet_projection_empty_of_rank (Ψ := psiMt r)
    (Kv := Metric.closedBall (0 : QCoeff 4) ρ) (K := K) (contDiff_psiMt r hr)
    (isCompact_closedBall _ _) hK ?_
  rintro ⟨c, u⟩ hp hp0
  obtain ⟨hc, huK⟩ := hp
  obtain ⟨hs1, hs2, hs3, hd1, hd2, hd3⟩ := hsep u huK
  have hrange : (fderiv ℝ (psiMt r) (c, u)).range
      = (fderiv ℝ (psiMe r) (c, u)).range.map (eTgt : (Space × Space) →ₗ[ℝ] Tgt) := by
    rw [range_fderiv_psiMt_eq r hr c u, map_eTgt_toLinearMap_eq]
  have h4 := rank_patchM_of_psiMt_zero r c u (hknot c hc)
    (by rw [show period = 2 * Real.pi from rfl]; exact hs1)
    (by rw [show period = 2 * Real.pi from rfl]; exact hs2) hd1 hp0
  have hsub := Submodule.finrank_mono
    (range_fderiv_patchM_le_fderiv_psiMe hr c u hs1 hs2 hs3 hd1 hd2 hd3)
  rw [hrange, finrank_map_eTgt]
  exact lt_of_lt_of_le (by rw [finrank_euclideanSpace_fin]; norm_num) (le_trans h4 hsub)


end

end Work.Drive
