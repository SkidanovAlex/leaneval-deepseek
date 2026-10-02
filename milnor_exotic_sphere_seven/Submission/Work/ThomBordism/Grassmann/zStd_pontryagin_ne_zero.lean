import Mathlib
import Submission.Work.ThomBordism.Grassmann.zStdSetup
import Submission.Work.LerayHirsch.mv2_exact
import Submission.Work.Projective.CP2Cohomology
import Submission.Work.Agree.mapFibreIso
import Submission.Work.ThomBordism.Grassmann.p1RatPuncture
import Submission.Work.ThomBordism.Grassmann.zStd_UR_cohomology
import Submission.Work.ThomBordism.Grassmann.zStd_VR_cohomology
import Submission.Work.ThomBordism.Grassmann.zStd_UV_cohomology
import Submission.Work.Thom.LineGeom

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

/-!
# `Work.Thom.pontryagin1 zStd ≠ 0`

The crux `p₁(zStd) ≠ 0` for the standard rank-`2` real bundle `zStd = L_ℝ` over `ℂP²`
(`L = O(1)` the tautological dual), equivalently `c₂(ℂ ⊗_ℝ zStd) ≠ 0`, where
`W = realification (complexificationCore zStd)` is the rank-`4` real bundle whose top Chern class
is the Euler class of the canonical Thom class `Tthom`.

## Route

`pontryagin1 zStd = - Tthom.eulerClass` (`Work.ThomBordism.Grassmann.pontryagin1_zStd_eq`), so it
suffices that `Tthom.eulerClass ≠ 0`.  By the Gysin sequence of the sphere bundle of `W` over `ℂP²`
(`Work.Thom.gysin_exact_at_base`), `range (∪ e) = ker (gysinπ W 4)`; if `H⁴(W∖0) = 0` then
`∪ e : H⁰(ℂP²) → H⁴(ℂP²)` is surjective and, `H⁴(ℂP²) ≅ ℤ` being non-zero, `e ≠ 0`.

`H⁴(W∖0) = 0` comes from the two-set Mayer–Vietoris sequence (`Work.LerayHirsch.mv2_exact`) for the
cover of `X = W∖0` by the two open pieces `UR = {Re ≠ 0}`, `VR = {Im ≠ 0}`: the transition
functions of the complexification are block diagonal on `Re ⊕ Im`
(`Work.Thom.cxTrans_apply`, `Work.Thom.complexificationCore_coordChange_cxRePart`), so both
conditions are chart-independent; the exactness
`H³(UR ∩ VR) → H⁴(X) → H⁴(UR) ⊕ H⁴(VR)` exhibits `H⁴(X)` as a submodule of a trivial module as soon
as `H³(UR ∩ VR) = 0`.
-/

namespace Work.ThomBordism.Grassmann

open Work.TangentClasses
open CategoryTheory Limits

noncomputable section

/-- **The two pieces `UR = {Re ≠ 0}` and `VR = {Im ≠ 0}` cover the punctured total space of `W`.**
This is the decomposition of a complexified fibre into its real and imaginary parts
(`Work.Thom.cxOfReal_cxRePart_add_cxMulI_cxImPart`): a point whose real *and* imaginary parts vanish
is the zero vector. -/
theorem UR_union_VR : UR ∪ VR = Set.univ := by
  refine Set.eq_univ_of_forall fun p => ?_
  by_contra h
  rw [Set.mem_union, not_or] at h
  obtain ⟨h1, h2⟩ := h
  simp only [UR, VR, Set.mem_ofPred_eq, not_not] at h1 h2
  have hv : p.1.2 = 0 := by
    have h := Work.Thom.cxOfReal_cxRePart_add_cxMulI_cxImPart p.1.2
    rw [h1, h2, map_zero, map_zero, add_zero] at h
    exact h.symm
  exact p.2 hv

/-! ## Chart independence of the two conditions

The transition functions of `W = realification (complexificationCore zStd)` are block diagonal on
`Re ⊕ Im` (`Work.Thom.cxTrans_apply`): in every chart of `W` the trivialised real (resp. imaginary)
part is the transition function of `zStd` applied to the model real (resp. imaginary) part.  Since a
transition function between a chart and the chart at the base point is invertible
(`coordChange_indexAt_ne_zero_iff`), both non-vanishing conditions are chart independent. -/

/-- **A transition function of a bundle between a chart and the chart at the base point is
invertible**, hence preserves non-vanishing. -/
theorem coordChange_indexAt_ne_zero_iff {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {ι : Type*} (Z : RealBundle (Work.Projective.CP 2) F ι) (i : ι) (b : Work.Projective.CP 2)
    (hb : b ∈ Z.baseSet i) (v : F) :
    Z.coordChange (Z.indexAt b) i b v ≠ 0 ↔ v ≠ 0 := by
  constructor
  · intro h hv
    exact h (by rw [hv, map_zero])
  · intro hv h0
    have h1 : Z.coordChange i (Z.indexAt b) b (Z.coordChange (Z.indexAt b) i b v) = v := by
      have hcomp := Z.coordChange_comp (Z.indexAt b) i (Z.indexAt b) b
        ⟨⟨Z.mem_baseSet_at b, hb⟩, Z.mem_baseSet_at b⟩ v
      rw [Z.coordChange_self (Z.indexAt b) b (Z.mem_baseSet_at b) v] at hcomp
      exact hcomp
    rw [h0, map_zero] at h1
    exact hv h1.symm

/-- `W` and `zStd` have the same charts. -/
theorem W_baseSet_eq (i : Fin 3) : W.baseSet i = zStd.baseSet i := by
  simp only [W, E₂, Work.Thom.realification_baseSet, Work.Thom.complexificationCore_baseSet]

/-- `W` and `zStd` have the same index map. -/
theorem W_indexAt_eq (b : Work.Projective.CP 2) : W.indexAt b = zStd.indexAt b := by
  simp only [W, E₂, Work.Thom.realification_indexAt]
  rfl

/-- The real part of a transition function of `W` is the transition function of `zStd` applied to
the real part. -/
theorem cxRePart_coordChange_W (i j : Fin 3) (b : Work.Projective.CP 2)
    (v : EuclideanSpace ℂ (Fin 2)) :
    Work.Thom.cxRePart (W.coordChange i j b v) =
      zStd.coordChange i j b (Work.Thom.cxRePart v) := by
  simp only [W, E₂, Work.Thom.realification_coordChange,
    Work.Thom.complexificationCore_coordChange_cxRePart]

/-- The imaginary part of a transition function of `W` is the transition function of `zStd` applied
to the imaginary part. -/
theorem cxImPart_coordChange_W (i j : Fin 3) (b : Work.Projective.CP 2)
    (v : EuclideanSpace ℂ (Fin 2)) :
    Work.Thom.cxImPart (W.coordChange i j b v) =
      zStd.coordChange i j b (Work.Thom.cxImPart v) := by
  simp only [W, E₂, Work.Thom.realification_coordChange,
    Work.Thom.complexificationCore_coordChange_cxImPart]

/-- In a chart of `W`, the trivialised real part is the transition function of `zStd` applied to
the model real part. -/
theorem cxRePart_localTriv_W (i : Fin 3) (q : W.TotalSpace) :
    Work.Thom.cxRePart ((W.localTriv i q).2) =
      zStd.coordChange (W.indexAt q.1) i q.1 (Work.Thom.cxRePart q.2) := by
  rw [VectorBundleCore.localTriv_apply]
  exact cxRePart_coordChange_W (W.indexAt q.1) i q.1 q.2

/-- In a chart of `W`, the trivialised imaginary part is the transition function of `zStd` applied
to the model imaginary part. -/
theorem cxImPart_localTriv_W (i : Fin 3) (q : W.TotalSpace) :
    Work.Thom.cxImPart ((W.localTriv i q).2) =
      zStd.coordChange (W.indexAt q.1) i q.1 (Work.Thom.cxImPart q.2) := by
  rw [VectorBundleCore.localTriv_apply]
  exact cxImPart_coordChange_W (W.indexAt q.1) i q.1 q.2

/-- **Chart independence of the real-part condition.** -/
theorem cxRePart_localTriv_ne_zero_iff (i : Fin 3) (q : W.TotalSpace)
    (hq : q.1 ∈ W.baseSet i) :
    Work.Thom.cxRePart ((W.localTriv i q).2) ≠ 0 ↔ Work.Thom.cxRePart q.2 ≠ 0 := by
  rw [cxRePart_localTriv_W, W_indexAt_eq]
  exact coordChange_indexAt_ne_zero_iff zStd i q.1 (by rwa [← W_baseSet_eq]) _

/-- **Chart independence of the imaginary-part condition.** -/
theorem cxImPart_localTriv_ne_zero_iff (i : Fin 3) (q : W.TotalSpace)
    (hq : q.1 ∈ W.baseSet i) :
    Work.Thom.cxImPart ((W.localTriv i q).2) ≠ 0 ↔ Work.Thom.cxImPart q.2 ≠ 0 := by
  rw [cxImPart_localTriv_W, W_indexAt_eq]
  exact coordChange_indexAt_ne_zero_iff zStd i q.1 (by rwa [← W_baseSet_eq]) _

/-! ## Openness of the two pieces -/

/-- The chartwise piece of the real-part condition is open. -/
theorem isOpen_UR_piece (i : Fin 3) : IsOpen ((W.localTriv i).source ∩
    {q : W.TotalSpace | Work.Thom.cxRePart ((W.localTriv i q).2) ≠ 0}) := by
  have hcont : ContinuousOn (fun q : W.TotalSpace => Work.Thom.cxRePart ((W.localTriv i q).2))
      (W.localTriv i).source :=
    (LinearMap.continuous_of_finiteDimensional (Work.Thom.cxRePart (k := 2))).comp_continuousOn
      (continuous_snd.comp_continuousOn (W.localTriv i).continuousOn_toFun)
  exact hcont.isOpen_inter_preimage (W.localTriv i).open_source isOpen_ne

/-- The chartwise piece of the imaginary-part condition is open. -/
theorem isOpen_VR_piece (i : Fin 3) : IsOpen ((W.localTriv i).source ∩
    {q : W.TotalSpace | Work.Thom.cxImPart ((W.localTriv i q).2) ≠ 0}) := by
  have hcont : ContinuousOn (fun q : W.TotalSpace => Work.Thom.cxImPart ((W.localTriv i q).2))
      (W.localTriv i).source :=
    (LinearMap.continuous_of_finiteDimensional (Work.Thom.cxImPart (k := 2))).comp_continuousOn
      (continuous_snd.comp_continuousOn (W.localTriv i).continuousOn_toFun)
  exact hcont.isOpen_inter_preimage (W.localTriv i).open_source isOpen_ne

/-- **The real-part non-vanishing locus is open in the total space of `W`** (as a union of the
open chartwise pieces). -/
theorem isOpen_cxRePart_ne_zero :
    IsOpen {q : W.TotalSpace | Work.Thom.cxRePart q.2 ≠ 0} := by
  have hset : {q : W.TotalSpace | Work.Thom.cxRePart q.2 ≠ 0}
      = ⋃ i : Fin 3, ((W.localTriv i).source ∩
          {q : W.TotalSpace | Work.Thom.cxRePart ((W.localTriv i q).2) ≠ 0}) := by
    ext q
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_inter_iff]
    constructor
    · intro hq
      exact ⟨W.indexAt q.1,
        (VectorBundleCore.mem_localTriv_source W (W.indexAt q.1) q).mpr (W.mem_baseSet_at q.1),
        (cxRePart_localTriv_ne_zero_iff (W.indexAt q.1) q (W.mem_baseSet_at q.1)).mpr hq⟩
    · rintro ⟨i, hsrc, hne⟩
      exact (cxRePart_localTriv_ne_zero_iff i q
        ((VectorBundleCore.mem_localTriv_source W i q).mp hsrc)).mp hne
  rw [hset]
  exact isOpen_iUnion isOpen_UR_piece

/-- **The imaginary-part non-vanishing locus is open in the total space of `W`.** -/
theorem isOpen_cxImPart_ne_zero :
    IsOpen {q : W.TotalSpace | Work.Thom.cxImPart q.2 ≠ 0} := by
  have hset : {q : W.TotalSpace | Work.Thom.cxImPart q.2 ≠ 0}
      = ⋃ i : Fin 3, ((W.localTriv i).source ∩
          {q : W.TotalSpace | Work.Thom.cxImPart ((W.localTriv i q).2) ≠ 0}) := by
    ext q
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_inter_iff]
    constructor
    · intro hq
      exact ⟨W.indexAt q.1,
        (VectorBundleCore.mem_localTriv_source W (W.indexAt q.1) q).mpr (W.mem_baseSet_at q.1),
        (cxImPart_localTriv_ne_zero_iff (W.indexAt q.1) q (W.mem_baseSet_at q.1)).mpr hq⟩
    · rintro ⟨i, hsrc, hne⟩
      exact (cxImPart_localTriv_ne_zero_iff i q
        ((VectorBundleCore.mem_localTriv_source W i q).mp hsrc)).mp hne
  rw [hset]
  exact isOpen_iUnion isOpen_VR_piece

theorem isOpen_UR : IsOpen UR := isOpen_cxRePart_ne_zero.preimage continuous_subtype_val

theorem isOpen_VR : IsOpen VR := isOpen_cxImPart_ne_zero.preimage continuous_subtype_val


/-! ## The punctured total space of `zStd`

`zStd` is `mapFibre equivC1R2` of the realification of the tautological dual line bundle
`LR = realification (tautDual 2)`, so the two bundles are isomorphic
(`Work.Agree.nonempty_bundleIso_mapFibre_of_iso`) and their punctured total spaces are
homeomorphic; the punctured total space of `LR` is `ℂ³∖0 ≃ S⁵`, with vanishing cohomology in all
degrees `≠ 0, 5`. -/

section Punctured

/-- The tautological dual line bundle `O(1)` over `ℂP²`, as a *real* rank-`2` bundle. -/
abbrev LR : RealBundle (Work.Projective.CP 2) (EuclideanSpace ℂ (Fin 1)) (Fin 3) :=
  Work.Thom.realification (Work.Gen.tautDual 2)

/-- `zStd` is `LR` with its fibre changed along `equivC1R2`. -/
theorem zStd_eq_mapFibre : zStd = LR.mapFibre equivC1R2 := rfl

/-- Changing the fibre along the identity does not change the bundle. -/
theorem mapFibre_refl_eq (Z : RealBundle (Work.Projective.CP 2) (EuclideanSpace ℂ (Fin 1)) (Fin 3)) :
    Z.mapFibre (ContinuousLinearEquiv.refl ℝ (EuclideanSpace ℂ (Fin 1))) = Z := by
  refine RealBundle.ext rfl rfl ?_
  intro i j x
  rw [RealBundle.mapFibre_coordChange]
  ext v
  rfl

end Punctured

/-! ## What is proved here, and what remains (session notes)

**Proved, sorry-free.** The whole *assembly* of the proof of
`Work.Thom.pontryagin1 zStd ≠ 0` from the cohomological vanishings below (only
`zStd_UV_cohomology` is still open):

* `UR_union_VR` — the two pieces `UR = {Re ≠ 0}`, `VR = {Im ≠ 0}` cover `W∖0` (using
  `cxOfReal_cxRePart_add_cxMulI_cxImPart`);
* `coordChange_indexAt_ne_zero_iff` — a transition function between a chart and the chart at the base
  point is invertible;
* `W_baseSet_eq`, `W_indexAt_eq`, `cxRePart_coordChange_W`, `cxImPart_coordChange_W`,
  `cxRePart_localTriv_W`, `cxImPart_localTriv_W`,
  `cxRePart_localTriv_ne_zero_iff`, `cxImPart_localTriv_ne_zero_iff` — the two conditions are
  *chart independent* (the complexification transitions are block diagonal on `Re ⊕ Im`);
* `isOpen_UR`, `isOpen_VR` (via the chartwise decomposition `isOpen_cxRePart_ne_zero`);
* `subsingleton_cohomology_four_zeroComplement` — the two-set Mayer–Vietoris argument
  (`Work.LerayHirsch.mv2_exact`, `mv2_components`): `H³(UR ∩ VR) = 0` kills the connecting map, so
  `H⁴(W∖0)` embeds into `H⁴(UR) ⊕ H⁴(VR) = 0`;
* `exists_ne_zero_cohomology_four_cp2` (`H⁴(ℂP²;ℤ) ≅ ℤ ≠ 0` from
  `Work.Projective.singularCohomology_four_cp2`);
* `eulerClass_ne_zero` — the Gysin sequence of `W` over `ℂP²` (`Work.Thom.gysin_exact_at_base`,
  `gysinEuler_eq_cupEuler`): `H⁴(W∖0) = 0` forces `∪ e : H⁰(ℂP²) → H⁴(ℂP²)` to be onto, and since
  `H⁴(ℂP²) ≠ 0`, `Tthom.eulerClass ≠ 0`;
* and finally `zStd_pontryagin_ne_zero` from `pontryagin1_zStd_eq`.

**All three cohomological vanishings are proved** (the two below here, the overlap
`zStd_UV_cohomology : H³(UR ∩ VR) = 0` in `Submission/Work/ThomBordism/Grassmann/zStd_UV_cohomology.lean`,
where `UR ∩ VR` is identified with the punctured pullback bundle of `zStd` over
`zeroComplement zStd` and the pair sequence and the Thom isomorphism sandwich the degree):

* `Work.ThomBordism.Grassmann.zStd_UR_cohomology`, `Work.ThomBordism.Grassmann.zStd_VR_cohomology`
  (`Submission/Work/ThomBordism/Grassmann/zStd_UR_cohomology.lean`, `zStd_VR_cohomology.lean`):
  the straight-line retraction `(t,p) ↦ (1-t)·v + t·P(v)` (for `UR`: `P` = the fibrewise real part;
  for `VR`: `P = i ∘ Im`) is a homotopy equivalence with `zeroComplement zStd`, and `H⁴` of that
  space vanishes;
* `isZero_cohomology_two_zStd`, `isZero_cohomology_three_zStd`, `isZero_cohomology_four_zStd`
  (`ZStdURSupport.lean`) — `H^k(zeroComplement zStd) = 0` for `k = 2, 3, 4`.

(*For reference, the route taken for `zStd_UV_cohomology`: `UR ∩ VR` is homeomorphic to the punctured
total space of the pullback bundle `Z := Work.Thom.bundleComap zStd π` over
`B := zeroComplement zStd` (the map `⟨b, u + i·v⟩ ↦ ⟨(b,u), v⟩`, whose components are the bundle
morphisms `cxRePart`, `cxImPart : W → zStd`); the pair sequence of `(Z.TotalSpace, Z∖0)` together
with `Work.Thom.bijective_CohMap_bundleProj` and the Thom isomorphism
(`Work.Thom.ThomClass.thomEquiv`) gives the exact segment
`H³(B) → H³(Z∖0) → H⁴(Z,Z∖0) ≅ H²(B)`, i.e. `0 → H³(UR∩VR) → 0`.  Alternatively identify the
overlap with `(zeroComplement zStd) × ℂ*` by the ratio map `(b,u,v) ↦ (b,u,v/u)` (division in the
complex model fibre via `Work.Thom.equivC1R2`) and use the cover of `ℂ*` by two contractible open
half-planes together with `Work.Cohomology.cohomology_prod_contractible` and
`Work.LerayHirsch.mv2_exact`; or show `UR ∩ VR` is homotopy equivalent to `S⁵ × S¹` and quote
`Work.Cohomology.cohomology_prod_sphere`.

**The `zeroComplement zStd` input.**  `zStd = LR.mapFibre equivC1R2` with
`LR = realification (tautDual 2)`.  A bundle isomorphism `zStd ≅ LR` (fibrewise `equivC1R2.symm`;
continuity of the induced total-space maps by `Work.Thom.continuous_totalSpaceMap_clm_gen`, using
`Work.Thom.continuousOn_chartExpressionCLM_gen` for the chart expression of the identity of `LR`
and `RealBundle.mapFibre_coordChange` to unfold the transitions of `zStd`) yields a homeomorphism of
the punctured total spaces (`Work.Thom.BundleIso.punctHomeomorph` together with
`Work.Thom.zeroComplementCore_eq_zeroComplement`).  Since
`puncturedTautDualTwoHZero` (`Submission/Work/ThomBordism/Grassmann/p1Rat_ne_zero_via_probe.lean`,
proved) gives `IsZero (Coh ℤ k ↥(zeroComplement LR))` for `k ≠ 0, 5`, homotopy invariance
(`Work.Cohomology.cohomologyIso_of_homotopyEquiv`) gives
`Subsingleton (Work.Thom.Coh ℤ 4 ↥(zeroComplement zStd))` and then, along the deformation
retractions, the two vanishings for `UR` and `VR`.
-/

/-- **`H²` of the punctured total space of `zStd` vanishes** (it is `ℂ³∖0 ≃ S⁵`). -/
theorem isZero_cohomology_two_zStd :
    CategoryTheory.Limits.IsZero (Work.Thom.Coh ℤ 2 ↥(Work.Thom.zeroComplement zStd)) := by
  obtain ⟨iso⟩ := Work.Cohomology.cohomologyIso_of_homotopyEquiv
    punctHomeoTautDualTwoR.toHomotopyEquiv 2
  exact CategoryTheory.Limits.IsZero.of_iso
    (puncturedTautDualTwoHZero 2 (by norm_num) (by norm_num)) iso.symm

/-- **`H³` of the punctured total space of `zStd` vanishes** (it is `ℂ³∖0 ≃ S⁵`). -/
theorem isZero_cohomology_three_zStd :
    CategoryTheory.Limits.IsZero (Work.Thom.Coh ℤ 3 ↥(Work.Thom.zeroComplement zStd)) := by
  obtain ⟨iso⟩ := Work.Cohomology.cohomologyIso_of_homotopyEquiv
    punctHomeoTautDualTwoR.toHomotopyEquiv 3
  exact CategoryTheory.Limits.IsZero.of_iso
    (puncturedTautDualTwoHZero 3 (by norm_num) (by norm_num)) iso.symm

/-! ## The three vanishing inputs

These are the geometric inputs of the Mayer–Vietoris argument, stated as separate lemmas so that
they can be proved independently.  Each of them is a statement about a putative
`ℂ`-line-bundle-with-norm presentation of `zStd`. -/

/-! ## Mayer–Vietoris -/

/-- A point of a biproduct of `ℤ`-modules whose two projections vanish is zero. -/
lemma biprod_apply_eq_zero_of_fst_snd {A X Y : ModuleCat ℤ} (f : A ⟶ X ⊞ Y) (a : A)
    (h₁ : (biprod.fst : X ⊞ Y ⟶ X).hom (ModuleCat.Hom.hom f a) = 0)
    (h₂ : (biprod.snd : X ⊞ Y ⟶ Y).hom (ModuleCat.Hom.hom f a) = 0) :
    ModuleCat.Hom.hom f a = 0 := by
  have htot := congrArg (fun (g : X ⊞ Y ⟶ X ⊞ Y) => ModuleCat.Hom.hom g (ModuleCat.Hom.hom f a))
    biprod.total
  simp only [ModuleCat.hom_add, ModuleCat.hom_comp, LinearMap.add_apply, LinearMap.comp_apply,
    ModuleCat.hom_id, LinearMap.id_apply] at htot
  rw [h₁, h₂, map_zero, map_zero, add_zero] at htot
  exact htot.symm

theorem subsingleton_cohomology_four_zeroComplement
    (hUR : Subsingleton (Work.Thom.Coh ℤ 4 ↥UR))
    (hVR : Subsingleton (Work.Thom.Coh ℤ 4 ↥VR))
    (hUV : Subsingleton (Work.Thom.Coh ℤ 3 ↥(UR ∩ VR))) :
    Subsingleton (Work.Thom.Coh ℤ 4 ↥(Work.Thom.zeroComplement W)) := by
  haveI := hUR
  haveI := hVR
  haveI := hUV
  have hmv := Work.LerayHirsch.mv2_exact UR VR isOpen_UR isOpen_VR UR_union_VR
  -- the connecting map out of the (trivial) overlap vanishes
  have hdelta : (Work.LerayHirsch.mv2δ UR VR isOpen_UR isOpen_VR UR_union_VR 3).hom = 0 :=
    LinearMap.ext fun x => by
      rw [Subsingleton.elim x 0]
      exact map_zero _
  -- so the kernel of the restriction map to the two pieces is trivial
  have hker : (Work.LerayHirsch.mv2F UR VR 4).hom.ker = ⊥ := by
    rw [← hmv.2.2.1 3, hdelta]
    exact LinearMap.range_zero
  have hcomp := Work.LerayHirsch.mv2_components UR VR 4
  refine ⟨fun a b => ?_⟩
  have h₁ : (biprod.fst : Work.Thom.Coh ℤ 4 ↥UR ⊞ Work.Thom.Coh ℤ 4 ↥VR ⟶
      Work.Thom.Coh ℤ 4 ↥UR).hom
        ((Work.LerayHirsch.mv2F UR VR 4).hom (a - b)) = 0 := by
    have h := congrArg ModuleCat.Hom.hom hcomp.1
    rw [ModuleCat.hom_comp] at h
    exact (congrFun (congrArg DFunLike.coe h) (a - b)).trans (Subsingleton.elim _ _)
  have h₂ : (biprod.snd : Work.Thom.Coh ℤ 4 ↥UR ⊞ Work.Thom.Coh ℤ 4 ↥VR ⟶
      Work.Thom.Coh ℤ 4 ↥VR).hom
        ((Work.LerayHirsch.mv2F UR VR 4).hom (a - b)) = 0 := by
    have h := congrArg ModuleCat.Hom.hom hcomp.2.1
    rw [ModuleCat.hom_comp] at h
    exact (congrFun (congrArg DFunLike.coe h) (a - b)).trans (Subsingleton.elim _ _)
  have h0 : (Work.LerayHirsch.mv2F UR VR 4).hom (a - b) = 0 :=
    biprod_apply_eq_zero_of_fst_snd _ (a - b) h₁ h₂
  have hmem : a - b ∈ (Work.LerayHirsch.mv2F UR VR 4).hom.ker := h0
  rw [hker] at hmem
  exact sub_eq_zero.mp (by simpa using hmem)

/-! ## The Gysin step -/

/-- `H⁴(ℂP²;ℤ)` is non-trivial. -/
theorem exists_ne_zero_cohomology_four_cp2 :
    ∃ x : Work.Thom.Coh ℤ 4 (Work.Projective.CP 2), x ≠ 0 := by
  obtain ⟨e⟩ := Work.Projective.singularCohomology_four_cp2
  refine ⟨e.inv.hom (1 : ↑(ModuleCat.of ℤ ℤ)), fun h => ?_⟩
  have hcomp : e.hom.hom (e.inv.hom (1 : ↑(ModuleCat.of ℤ ℤ))) = (1 : ↑(ModuleCat.of ℤ ℤ)) := by
    have h := congrArg ModuleCat.Hom.hom e.inv_hom_id
    rw [ModuleCat.hom_comp, ModuleCat.hom_id] at h
    exact congrFun (congrArg DFunLike.coe h) 1
  rw [h, map_zero] at hcomp
  exact one_ne_zero hcomp.symm

/-- **The Euler class of the canonical Thom class of `W` does not vanish**, given that
`H⁴(W∖0) = 0`: the Gysin sequence `H⁰(ℂP²) --∪e--> H⁴(ℂP²) → H⁴(W∖0)` makes `∪e` surjective, and
`H⁴(ℂP²;ℤ) ≠ 0`. -/
theorem eulerClass_ne_zero
    (hX : Subsingleton (Work.Thom.Coh ℤ 4 ↥(Work.Thom.zeroComplement W))) :
    Tthom.eulerClass ≠ 0 := by
  haveI := hX
  have hπ : Work.Thom.gysinπ W 4 = 0 := LinearMap.ext fun x => Subsingleton.elim _ _
  have hsurj : ∀ y : Work.Thom.Coh ℤ 4 (Work.Projective.CP 2),
      ∃ x, Work.Thom.gysinEuler Tthom 0 x = y := by
    intro y
    have h := Work.Thom.gysin_exact_at_base Tthom 0
    have hy : y ∈ Set.range (Work.Thom.gysinEuler Tthom 0) := by
      rw [h]
      simp only [Set.mem_setOf_eq]
      rw [show Work.Thom.gysinπ W 4 y = 0 from by rw [hπ]; rfl]
    exact hy
  intro he
  obtain ⟨x, hx⟩ := exists_ne_zero_cohomology_four_cp2
  obtain ⟨y, hy⟩ := hsurj x
  refine hx ?_
  rw [← hy, Work.Thom.gysinEuler_eq_cupEuler Tthom 0 y, he]
  exact Work.Cohomology.cupH'_zero_right (R := ℤ) (X := TopCat.toSSet.obj (TopCat.of (Work.Projective.CP 2))) 0 4 y

/-! ## The target -/

/-- **`Work.Thom.pontryagin1 zStd ≠ 0`**: the first Pontryagin class of the realification of the
tautological dual line bundle over `ℂP²` does not vanish. -/
theorem zStd_pontryagin_ne_zero :
    Work.Thom.pontryagin1 Work.ThomBordism.Grassmann.zStd ≠ 0 := by
  rw [pontryagin1_zStd_eq]
  exact neg_ne_zero.mpr (eulerClass_ne_zero (subsingleton_cohomology_four_zeroComplement
    Work.ThomBordism.Grassmann.zStd_UR_cohomology
    Work.ThomBordism.Grassmann.zStd_VR_cohomology
    Work.ThomBordism.Grassmann.zStd_UV_cohomology))

end

end Work.ThomBordism.Grassmann
