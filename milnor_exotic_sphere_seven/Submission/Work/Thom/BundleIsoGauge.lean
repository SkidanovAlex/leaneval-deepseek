import Mathlib
import Submission.Work.Thom.CovDefs
import Submission.Work.Thom.Iso
import Submission.Work.Thom.IsoPunct
import Submission.Work.Thom.realification_homeo
import Submission.Work.Thom.ChartOrientation
import Submission.Work.Thom.isOrientedOver_of_det_pos

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

/-!
# The gauge of a bundle isomorphism, and the piece map of an isomorphism of Thom pairs

For two complex bundles `Z`, `Z'` over a common base `B` (same fibre, possibly different index
types) and a bundle isomorphism `e : Work.Thom.BundleIso Z Z'`:

* `Work.Thom.realifPieceHomeo Z W` — the identity homeomorphism between the piece over `W` of a
  complex bundle and the piece over `W` of its realification.  (`Z.TotalSpace` and
  `(realification Z).TotalSpace` carry *propositionally* equal, but not definitionally equal,
  `TopologicalSpace` instances; `realifPieceHomeo` is the only place where this is bridged, via
  `Work.Thom.continuous_id_realification` / `Work.Thom.continuous_id_realification_symm`.)
* `Work.Thom.pieceHomeoOfIso Z Z' e W` — the piece map induced by `e` in the world of `Z`/`Z'`;
* `Work.Thom.pieceMapIso Z Z' e W` — the induced continuous map of the pieces over `W ⊆ B` of the
  *realifications*, whose defining formula is `pieceMapIso_apply`:
  `(pieceMapIso Z Z' e W p).2 = e.hom p.1.1 p.1.2`;
* `Work.Thom.continuous_clm_of_continuous_apply` — the "matrix entries" criterion for the
  continuity of a family of endomorphisms of `ℝⁿ` (used to prove `Continuous (isoGauge …)`);
* `Work.Thom.isoGauge Z Z' e i i' …` — the **fibrewise linear gauge** comparing the chart `i` of
  `realification Z` with the chart `i'` of `realification Z'` through `e`: the composite
  `ℝ^{2m} --covE⁻¹--> ℂᵐ --(Z.coordChange)⁻¹--> ℂᵐ --e.hom x--> ℂᵐ --Z'.coordChange--> ℂᵐ --covE--> ℝ^{2m}`,
  which is `ℂ`-linear up to conjugation by `covE`, hence has **positive real determinant** (the
  complex orientation), with defining formula `isoGauge_apply`.

## The proof route for `localThomOfChart_iso` (module `localThomOfChart_iso.lean`)

The target is, for `W ⊆ (realification Z).baseSet i ∩ (realification Z').baseSet i'`,

`(relCohMap (pieceMapIso Z Z' e W) …).hom (localThomOfChart (realification Z') (2*m) covE i' W _).τ
   = (localThomOfChart (realification Z) (2*m) covE i W _).τ`.

Route (mirror `Work.Thom.localThomOfChart_realif_comap`, which is the same statement for a *base
change* instead of an isomorphism):

1. `rw [localThomOfChart_tau, localThomOfChart_tau]` (both sides are `relCohMap chartHomeo` of
   `Mpun (2*m) ↥W`).
2. `relCohMap_compA_apply` turns the left-hand side into `relCohMap (chartHomeo' ∘ pieceMapIso)`.
3. **The composite identity** (a computation in the transition functions):
   `(chartHomeo (realification Z') (2*m) covE i' W hWi').comp (pieceMapIso Z Z' e W)
     = (gaugeEnd (isoGauge Z Z' e i i' hWi hWi') hcont).comp
         (chartHomeo (realification Z) (2*m) covE i W hWi)`
   as `ContinuousMap`s.  Pointwise, using `chartHomeo_apply`, `gaugeEnd_apply`,
   `pieceMapIso_apply`, `isoGauge_apply`: the two sides are
   `(⟨x, p.2⟩, covE (Z'.coordChange (Z'.indexAt x) i' x (e.hom x p.1.2)))` and
   `(⟨x, p.2⟩, covE (Z'.coordChange (Z'.indexAt x) i' x (e.hom x (Z.coordChange i (Z.indexAt x) x
      (Z.coordChange (Z.indexAt x) i x p.1.2)))))`;
   these agree by the cocycle identity
   `Z.coordChange i (Z.indexAt x) x (Z.coordChange (Z.indexAt x) i x u) = u`
   (`VectorBundleCore.coordChange_comp` + `VectorBundleCore.coordChange_self`).
4. `hcont : Continuous (isoGauge …)`: by `continuous_clm_of_continuous_apply` it suffices to show
   continuity of `(x, v) ↦ isoGauge … x v`, whose formula (`isoGauge_apply`) is a composite of
   *application-level* continuous maps: `covE.symm`, the chart inverse
   `(Z.coordChange i (Z.indexAt x) x) (·)` — best written via `(Work.TangentClasses.RealBundle`'s
   `VectorBundleCore.localTriv_symm_apply`) — then `e.hom x (·)` (continuity from
   `e.continuous_hom`) and `Z'.coordChange (Z'.indexAt x) i' x (·)` (from
   `(Z'.localTriv i').continuousOn`), then `covE`.
5. **The determinant**: `isoGauge … x` is, as a linear map,
   `covE ∘ₗ (A x).restrictScalars ℝ ∘ₗ covE.symm` where
   `A x = Z'.coordChange (Z'.indexAt x) i' x ∘ₗ e.hom x ∘ₗ Z.coordChange i (Z.indexAt x) x`
   is `ℂ`-linear and bijective (each factor is: `VectorBundleCore.coordChange_bijective`,
   `BundleIso.left_inv/right_inv`).  Hence
   `LinearMap.det (isoGauge … x).toLinearMap = LinearMap.det ((A x).restrictScalars ℝ) > 0` by
   `LinearMap.det_conj` and `Work.Thom.det_restrictScalars_pos`.  (Rewrite
   `(realification Z).coordChange = (Z.coordChange).restrictScalars ℝ` by
   `realification_coordChange` + `ContinuousLinearMap.ext`.)
6. `rw [relCohMap_congrA … hcomp]`, `rw [← relCohMap_compA_apply …]` and
   `Work.Thom.Mpun_gaugeEnd_invariant (2*m) (by omega) (isoGauge …) hcont hdet` finish.

## The proof route for `localThomOfComplexCover_pdCohMap_subset` (its own module)

`(localThomOfComplexCover hm Z).τ = covHcover Z ▸ covWitness hm Z` is
`Work.Thom.localThomOfComplexCover_tau_eq` (`rfl`).  Transfer the restriction across the cast
(`Work.Thom.pdCohMap_cast_source`), apply `Work.Thom.covWitness_restrict` with the singleton
`S = {Fintype.equivFin ι i}` (note `covCC (Fintype.equivFin ι i) = i` and
`finInter (covU Z) {k} = covU Z k`), and then restrict from the chart piece `covU Z k` to `W` by
`Work.Thom.localThomOfChart_restrict`, composing the two restrictions with
`Work.Thom.pdcz_pdCohMap_comp_apply`.  The `covU Z k = (realification Z).baseSet i` identification
is `Work.Thom.realification_baseSet`.
-/

namespace Work.Thom

open Work.TangentClasses

noncomputable section

variable {B : Type} [TopologicalSpace B] {m : ℕ} {ι ι' : Type}

/-! ## The identification of a bundle with its realification, on a piece -/

/-- **The piece over `W` of a complex bundle and the piece over `W` of its realification are the
same topological space** (via the identity). -/
def realifPieceHomeo (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι) (W : Set B) :
    ↥(Z.proj ⁻¹' W) ≃ₜ ↥((realification Z).proj ⁻¹' W) where
  toFun := fun p => ⟨(p : Z.TotalSpace), p.2⟩
  invFun := fun p => ⟨(p : (realification Z).TotalSpace), p.2⟩
  left_inv := fun _ => rfl
  right_inv := fun _ => rfl
  continuous_toFun := by
    refine Continuous.subtype_mk (f := fun p : ↥(Z.proj ⁻¹' W) =>
      (id (p : Z.TotalSpace) : (realification Z).TotalSpace)) ?_ (fun p => p.2)
    exact (continuous_id_realification Z).comp continuous_subtype_val
  continuous_invFun := by
    refine Continuous.subtype_mk (f := fun p : ↥((realification Z).proj ⁻¹' W) =>
      (id (p : (realification Z).TotalSpace) : Z.TotalSpace)) ?_ (fun p => p.2)
    exact (continuous_id_realification_symm Z).comp continuous_subtype_val

@[simp] theorem realifPieceHomeo_apply (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι)
    (W : Set B) (p : ↥(Z.proj ⁻¹' W)) :
    ((realifPieceHomeo Z W p : ↥((realification Z).proj ⁻¹' W)) : (realification Z).TotalSpace)
      = (p : Z.TotalSpace) := rfl

@[simp] theorem realifPieceHomeo_symm_apply
    (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι)
    (W : Set B) (p : ↥((realification Z).proj ⁻¹' W)) :
    (((realifPieceHomeo Z W).symm p : ↥(Z.proj ⁻¹' W)) : Z.TotalSpace)
      = (p : (realification Z).TotalSpace) := rfl

/-! ## The piece homeomorphism induced by a bundle isomorphism -/

/-- **The homeomorphism of the pieces over `W ⊆ B` induced by a bundle isomorphism** `e : Z ≅ Z'`
(of the bundles themselves, not of their realifications). -/
def pieceHomeoOfIso (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι)
    (Z' : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι')
    (e : BundleIso Z Z') (W : Set B) :
    ↥(Z.proj ⁻¹' W) ≃ₜ ↥(Z'.proj ⁻¹' W) where
  toFun := fun p => ⟨e.toTotalSpace p.1, p.2⟩
  invFun := fun p => ⟨e.invTotalSpace p.1, p.2⟩
  left_inv := fun p => by
    apply Subtype.ext
    exact e.toTotalSpace_left_inv p.1
  right_inv := fun p => by
    apply Subtype.ext
    exact e.toTotalSpace_right_inv p.1
  continuous_toFun := Continuous.subtype_mk
    (f := fun p : ↥(Z.proj ⁻¹' W) => e.toTotalSpace (p : Z.TotalSpace))
    (e.continuous_hom.comp continuous_subtype_val) (fun p => p.2)
  continuous_invFun := Continuous.subtype_mk
    (f := fun p : ↥(Z'.proj ⁻¹' W) => e.invTotalSpace (p : Z'.TotalSpace))
    (e.continuous_inv.comp continuous_subtype_val) (fun p => p.2)

@[simp] theorem pieceHomeoOfIso_apply (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι)
    (Z' : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι')
    (e : BundleIso Z Z') (W : Set B) (p : ↥(Z.proj ⁻¹' W)) :
    ((pieceHomeoOfIso Z Z' e W p : ↥(Z'.proj ⁻¹' W)) : Z'.TotalSpace) = e.toTotalSpace p.1 := rfl

/-! ## The total-space map of a bundle isomorphism, on the realifications -/

/-- **The total-space map of a bundle isomorphism**, on the side of the realifications:
`p ↦ (p.1, e.hom p.1.1 p.1.2)`. -/
def totalMapIso (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι)
    (Z' : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι')
    (e : BundleIso Z Z') :
    C((realification Z).TotalSpace, (realification Z').TotalSpace) :=
  ⟨fun p => ⟨p.1, (e.hom p.1).restrictScalars ℝ p.2⟩, by
    have h := (continuous_id_realification Z').comp
      (e.continuous_hom.comp (continuous_id_realification_symm Z))
    convert h using 1 with p
    rfl⟩

/-- The defining formula of `Work.Thom.totalMapIso`. -/
theorem totalMapIso_apply (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι)
    (Z' : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι')
    (e : BundleIso Z Z') (p : (realification Z).TotalSpace) :
    ((totalMapIso Z Z' e p : (realification Z').TotalSpace)) =
      (⟨p.1, e.hom p.1 p.2⟩ : (realification Z').TotalSpace) := rfl

/-! ## The piece map of an isomorphism of the realifications -/

/-- **The map of the pieces over `W ⊆ B` induced by a bundle isomorphism**, on the side of the
realifications: `p ↦ (p.1, e.hom p.1.1 p.1.2)`. -/
def pieceMapIso (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι)
    (Z' : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι')
    (e : BundleIso Z Z') (W : Set B) :
    C(↥((realification Z).proj ⁻¹' W), ↥((realification Z').proj ⁻¹' W)) :=
  { toFun := fun p => ((realifPieceHomeo Z W).symm.trans ((pieceHomeoOfIso Z Z' e W).trans
      (realifPieceHomeo Z' W))) p
    continuous_toFun := ((realifPieceHomeo Z W).symm.trans ((pieceHomeoOfIso Z Z' e W).trans
      (realifPieceHomeo Z' W))).continuous_toFun }

/-- The defining formula of `Work.Thom.pieceMapIso`. -/
theorem pieceMapIso_apply (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι)
    (Z' : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι')
    (e : BundleIso Z Z') (W : Set B)
    (p : ↥((realification Z).proj ⁻¹' W)) :
    ((pieceMapIso Z Z' e W p : ↥((realification Z').proj ⁻¹' W)) : (realification Z').TotalSpace)
      = (⟨p.1.1, e.hom p.1.1 p.1.2⟩ : (realification Z').TotalSpace) := by
  show ((realifPieceHomeo Z' W) ((pieceHomeoOfIso Z Z' e W) ((realifPieceHomeo Z W).symm p))
    : (realification Z').TotalSpace) = _
  rfl

/-- `Work.Thom.pieceMapIso` carries the punctured part to the punctured part. -/
theorem pieceMapIso_mem (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι)
    (Z' : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι')
    (e : BundleIso Z Z') (W : Set B) :
    ∀ p ∈ pieceZero (realification Z) W,
      pieceMapIso Z Z' e W p ∈ pieceZero (realification Z') W := by
  intro p hp
  show (show EuclideanSpace ℂ (Fin m) from
    ((pieceMapIso Z Z' e W p : ↥((realification Z').proj ⁻¹' W)) :
      (realification Z').TotalSpace).2) ≠ 0
  have h1 : (show EuclideanSpace ℂ (Fin m) from
      (((pieceMapIso Z Z' e W p : ↥((realification Z').proj ⁻¹' W)) :
          (realification Z').TotalSpace).2))
      = e.hom p.1.1 p.1.2 := by
    rw [pieceMapIso_apply]
  rw [h1]
  exact e.hom_ne_zero hp

/-- The total-space map restricts to the piece map over `Set.univ`. -/
theorem totalMapIso_comp_subtype (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι)
    (Z' : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι') (e : BundleIso Z Z') :
    (totalMapIso Z Z' e).comp
        (⟨Subtype.val, continuous_subtype_val⟩ :
          C(↥((realification Z).proj ⁻¹' (Set.univ : Set B)), (realification Z).TotalSpace))
      = (⟨Subtype.val, continuous_subtype_val⟩ :
          C(↥((realification Z').proj ⁻¹' (Set.univ : Set B)),
            (realification Z').TotalSpace)).comp (pieceMapIso Z Z' e Set.univ) := by
  apply ContinuousMap.ext
  intro q
  simp only [ContinuousMap.comp_apply, ContinuousMap.coe_mk, pieceMapIso_apply,
    totalMapIso_apply]

/-! ## Continuity of a continuous-linear-map valued family from its evaluations -/

/-- **A family of endomorphisms of `ℝⁿ` is continuous as soon as all its evaluations are.**
This is the elementary "matrix entries" continuity: the evaluation map `T ↦ (T b i)ᵢ` on the
standard basis is a linear equivalence of finite-dimensional spaces, so it is a homeomorphism. -/
theorem continuous_clm_of_continuous_apply {X : Type} [TopologicalSpace X] {n : ℕ}
    (D : X → (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)))
    (h : Continuous fun p : X × EuclideanSpace ℝ (Fin n) => D p.1 p.2) : Continuous D := by
  classical
  let b : Module.Basis (Fin n) ℝ (EuclideanSpace ℝ (Fin n)) :=
    (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
  let L : (Fin n → EuclideanSpace ℝ (Fin n)) →ₗ[ℝ]
      (EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n)) :=
    (b.constr (M' := EuclideanSpace ℝ (Fin n)) ℝ).toLinearMap
  let Ψ : (Fin n → EuclideanSpace ℝ (Fin n)) →ₗ[ℝ]
      (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) :=
    (LinearMap.toContinuousLinearMap (𝕜 := ℝ)).toLinearMap.comp L
  have hΨ : Continuous Ψ := LinearMap.continuous_of_finiteDimensional Ψ
  have hL : ∀ (w : Fin n → EuclideanSpace ℝ (Fin n)) (i : Fin n), L w (b i) = w i := by
    intro w i
    show (b.constr (M' := EuclideanSpace ℝ (Fin n)) ℝ w) (b i) = w i
    rw [Module.Basis.constr_basis]
  have hD : ∀ x, Ψ (fun i => D x (b i)) = D x := by
    intro x
    apply ContinuousLinearMap.coe_injective
    apply b.ext
    intro i
    show L (fun i => D x (b i)) (b i) = D x (b i)
    rw [hL]
  have hcont : Continuous (fun x : X => fun i => D x (b i)) :=
    continuous_pi (fun i => h.comp (continuous_id.prodMk continuous_const))
  rw [show D = fun x => Ψ (fun i => D x (b i)) from funext (fun x => (hD x).symm)]
  exact hΨ.comp hcont

/-! ## The gauge of a bundle isomorphism between two charts -/

set_option maxHeartbeats 1600000 in
/-- **The fibrewise linear gauge comparing the chart `i` of `Z` with the chart `i'` of `Z'`
through the isomorphism `e`**, on `W ⊆ baseSet i ∩ baseSet i'`. -/
def isoGauge (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι)
    (Z' : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι')
    (e : BundleIso Z Z') (i : ι) (i' : ι')
    {W : Set B} (_hWi : W ⊆ (realification Z).baseSet i)
    (_hWi' : W ⊆ (realification Z').baseSet i') : ↥W → Gauge (2 * m) :=
  fun x =>
    let hx : EuclideanSpace ℂ (Fin m) →ₗ[ℝ] EuclideanSpace ℂ (Fin m) :=
      (e.hom (x : B)).restrictScalars ℝ
    ((covE (m := m) : EuclideanSpace ℂ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin (2 * m)))).comp
      (((realification Z').coordChange ((realification Z').indexAt (x : B)) i' (x : B)).comp
        (((LinearMap.toContinuousLinearMap (𝕜 := ℝ) hx).comp
          (((realification Z).coordChange i ((realification Z).indexAt (x : B)) (x : B)).comp
            ((covE (m := m)).symm :
              EuclideanSpace ℝ (Fin (2 * m)) →L[ℝ] EuclideanSpace ℂ (Fin m))))))

/-- The defining formula of `Work.Thom.isoGauge`. -/
theorem isoGauge_apply (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι)
    (Z' : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι')
    (e : BundleIso Z Z') (i : ι) (i' : ι')
    {W : Set B} (hWi : W ⊆ (realification Z).baseSet i)
    (hWi' : W ⊆ (realification Z').baseSet i') (x : ↥W)
    (v : EuclideanSpace ℝ (Fin (2 * m))) :
    isoGauge Z Z' e i i' hWi hWi' x v =
      (covE (m := m) : EuclideanSpace ℂ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin (2 * m)))
        ((realification Z').coordChange ((realification Z').indexAt (x : B)) i' (x : B)
          (e.hom (x : B)
            ((realification Z).coordChange i ((realification Z).indexAt (x : B)) (x : B)
              ((covE (m := m)).symm v)))) := by
  rw [isoGauge]
  rfl

end

end Work.Thom
