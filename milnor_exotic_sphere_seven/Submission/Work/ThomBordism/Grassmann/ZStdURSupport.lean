import Mathlib
import Submission.Work.ThomBordism.Grassmann.zStdSetup
import Submission.Work.ThomBordism.Grassmann.p1RatPuncture
import Submission.Work.Agree.mapFibreIso
import Submission.Work.Thom.LineGeom

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# Support for `zStd_UR_cohomology`

This module collects the reusable geometric input of the proof that `H⁴` of the piece
`UR = {Re ≠ 0}` of the punctured total space of `W = realification (complexificationCore zStd)`
vanishes:

* `Work.ThomBordism.Grassmann.continuous_totalSpaceMap_intertwine` — a general continuity
  criterion: a *constant* fibrewise continuous linear map `T : F →L F'` between two real bundles
  over the same base, intertwining the transition functions, induces a continuous map of total
  spaces `⟨b,v⟩ ↦ ⟨b, T v⟩`;
* `Work.ThomBordism.Grassmann.zStdUR_W_baseSet`, `zStdUR_W_indexAt` — `W` and `zStd` have the same charts;
* `Work.ThomBordism.Grassmann.cxRePart_W_coordChange`, `cxOfReal_zStd_coordChange` — the
  real-part map `W → zStd` and the inclusion `zStd → W` are bundle morphisms;
* `Work.ThomBordism.Grassmann.continuous_rhoTotal`, `continuous_etaTotal`, `continuous_Ptot` —
  the three induced maps of total spaces are continuous;
* `Work.ThomBordism.Grassmann.bundleIsoRealificationTautDual`,
  `Work.ThomBordism.Grassmann.punctHomeoRealificationTautDual` — the bundle isomorphism
  `realification (tautDual 2) ≅ zStd` and the induced homeomorphism of the punctured total spaces;
* `Work.ThomBordism.Grassmann.isZero_cohomology_four_zStd` — `H⁴` of the punctured total space of
  `zStd` vanishes.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

open Work.TangentClasses

namespace Work.ThomBordism.Grassmann

noncomputable section

/-! ## A general continuity criterion for constant fibrewise linear maps -/

/-- The `clmGen` of the identity bundle isomorphism is the identity. -/
theorem clmGen_refl {B : Type} [TopologicalSpace B] {F : Type} [NormedAddCommGroup F]
    [NormedSpace ℝ F] [FiniteDimensional ℝ F] {ι : Type} (Z : VectorBundleCore ℝ B F ι)
    (b : B) : (Work.Thom.BundleIso.refl Z).clmGen b = 1 := by
  ext v
  rfl

/-- **Continuity of the total-space map of a constant fibrewise linear map intertwining the
transition functions.**  If `T : F →L[ℝ] F'` and `T` intertwines the transition functions of `Z`
and `Z'` (`T (g_{ij} v) = g'_{ij} (T v)`, in the chart-independent form below), then
`⟨b,v⟩ ↦ ⟨b, T v⟩` is continuous. -/
theorem continuous_totalSpaceMap_intertwine
    {B : Type} [TopologicalSpace B] {F F' : Type}
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    [NormedAddCommGroup F'] [NormedSpace ℝ F'] [FiniteDimensional ℝ F'] {ι : Type}
    (Z : VectorBundleCore ℝ B F ι) (Z' : VectorBundleCore ℝ B F' ι)
    (T : F →L[ℝ] F')
    (hbase : ∀ i, Z'.baseSet i = Z.baseSet i) (hidx : ∀ b, Z'.indexAt b = Z.indexAt b)
    (hT : ∀ (i j : ι) (b : B) (v : F), b ∈ Z.baseSet i ∩ Z'.baseSet j →
      T (Z.coordChange i j b v) = Z'.coordChange i j b (T v)) :
    Continuous (fun p : Z.TotalSpace => (⟨p.1, T p.2⟩ : Z'.TotalSpace)) := by
  refine Work.Thom.continuous_totalSpaceMap_clm_gen Z Z' (ContinuousMap.id B) (fun _ => T) ?_
  intro i₁ i₂
  simp only [ContinuousMap.id_apply]
  rw [show ⇑(ContinuousMap.id B) ⁻¹' Z'.baseSet i₂ = Z'.baseSet i₂ from Set.preimage_id]
  have hch : ContinuousOn (fun b : B => ((Z'.coordChange (Z'.indexAt b) i₂ b).comp
      ((Work.Thom.BundleIso.refl Z').clmGen b)).comp (Z'.coordChange i₁ (Z'.indexAt b) b))
      (Z.baseSet i₁ ∩ Z'.baseSet i₂) := by
    rw [← hbase i₁]
    exact Work.Thom.continuousOn_chartExpressionCLM_gen Z' Z' (Work.Thom.BundleIso.refl Z') i₁ i₂
  have G2c : ContinuousOn (fun b : B => (((Z'.coordChange (Z'.indexAt b) i₂ b).comp
      ((Work.Thom.BundleIso.refl Z').clmGen b)).comp (Z'.coordChange i₁ (Z'.indexAt b) b)).comp T)
      (Z.baseSet i₁ ∩ Z'.baseSet i₂) := hch.clm_comp continuousOn_const
  have heq1 : Set.EqOn (fun b : B => ((Z'.coordChange (Z'.indexAt b) i₂ b).comp
      (Z'.coordChange i₁ (Z'.indexAt b) b)).comp T)
      (fun b : B => (((Z'.coordChange (Z'.indexAt b) i₂ b).comp
        ((Work.Thom.BundleIso.refl Z').clmGen b)).comp (Z'.coordChange i₁ (Z'.indexAt b) b)).comp T)
      (Z.baseSet i₁ ∩ Z'.baseSet i₂) := by
    intro b _
    ext v
    simp only [ContinuousLinearMap.comp_apply, clmGen_refl]
    rfl
  have G1c : ContinuousOn (fun b : B => ((Z'.coordChange (Z'.indexAt b) i₂ b).comp
      (Z'.coordChange i₁ (Z'.indexAt b) b)).comp T) (Z.baseSet i₁ ∩ Z'.baseSet i₂) :=
    ContinuousOn.congr G2c heq1
  have heq2 : Set.EqOn (fun b : B => (Z'.coordChange (Z'.indexAt b) i₂ b).comp
      (T.comp (Z.coordChange i₁ (Z.indexAt b) b)))
      (fun b : B => ((Z'.coordChange (Z'.indexAt b) i₂ b).comp
        (Z'.coordChange i₁ (Z'.indexAt b) b)).comp T) (Z.baseSet i₁ ∩ Z'.baseSet i₂) := by
    intro b hb
    ext v
    show (Z'.coordChange (Z'.indexAt b) i₂ b) (T (Z.coordChange i₁ (Z.indexAt b) b v)) =
      (Z'.coordChange (Z'.indexAt b) i₂ b) ((Z'.coordChange i₁ (Z'.indexAt b) b) (T v))
    rw [← hidx b, hT i₁ (Z'.indexAt b) b v ⟨hb.1, Z'.mem_baseSet_at b⟩]
  exact ContinuousOn.congr G1c heq2

/-! ## `W` and `zStd` have the same charts -/

theorem zStdUR_W_baseSet (i : Fin 3) : zStd.baseSet i = W.baseSet i := by
  simp only [W, E₂, Work.Thom.realification_baseSet,
    Work.Thom.complexificationCore_baseSet]

theorem zStdUR_W_indexAt (b : Work.Projective.CP 2) : zStd.indexAt b = W.indexAt b := by
  simp only [W, E₂, Work.Thom.realification_indexAt,
    Work.Thom.complexificationCore_indexAt]

/-- The real part of a transition function of `W` is the transition function of `zStd` applied to
the real part. -/
theorem cxRePart_W_coordChange (i j : Fin 3) (b : Work.Projective.CP 2)
    (v : EuclideanSpace ℂ (Fin 2)) :
    Work.Thom.cxRePart (W.coordChange i j b v) = zStd.coordChange i j b (Work.Thom.cxRePart v) := by
  rw [show W.coordChange i j b v
      = (Work.Thom.complexificationCore zStd).coordChange i j b v from
    congrFun (Work.Thom.realification_coordChange (Work.Thom.complexificationCore zStd) i j b) v]
  exact Work.Thom.complexificationCore_coordChange_cxRePart zStd i j b v

/-- The real inclusion is a bundle morphism `zStd → W`: it intertwines the transition
functions. -/
theorem cxOfReal_zStd_coordChange (i j : Fin 3) (b : Work.Projective.CP 2)
    (u : EuclideanSpace ℝ (Fin 2)) :
    Work.Thom.cxOfReal (zStd.coordChange i j b u) = W.coordChange i j b (Work.Thom.cxOfReal u) := by
  rw [show W.coordChange i j b (Work.Thom.cxOfReal u)
      = (Work.Thom.complexificationCore zStd).coordChange i j b (Work.Thom.cxOfReal u) from
    congrFun (Work.Thom.realification_coordChange (Work.Thom.complexificationCore zStd) i j b)
      (Work.Thom.cxOfReal u)]
  rw [Work.Thom.complexificationCore_coordChange]
  exact (Work.Thom.cxTrans_cxOfReal (zStd.coordChange i j b) u).symm

/-! ## The real part as a continuous linear map -/

/-- The real part `ℂ² → ℝ²`, as a continuous linear map. -/
noncomputable def cxRePartCLM : EuclideanSpace ℂ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin 2) :=
  LinearMap.toContinuousLinearMap Work.Thom.cxRePart

/-- The real inclusion `ℝ² → ℂ²`, as a continuous linear map. -/
noncomputable def cxOfRealCLM : EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℂ (Fin 2) :=
  LinearMap.toContinuousLinearMap Work.Thom.cxOfReal

@[simp] theorem cxRePartCLM_apply (v : EuclideanSpace ℂ (Fin 2)) :
    cxRePartCLM v = Work.Thom.cxRePart v := rfl

@[simp] theorem cxOfRealCLM_apply (u : EuclideanSpace ℝ (Fin 2)) :
    cxOfRealCLM u = Work.Thom.cxOfReal u := rfl

/-! ## The induced maps of total spaces -/

/-- The real-part projection `W → zStd`, as a map of total spaces. -/
abbrev rhoTotal (p : W.TotalSpace) : zStd.TotalSpace :=
  ⟨p.1, Work.Thom.cxRePart p.2⟩

/-- The inclusion of `zStd` as the real part of `W`, as a map of total spaces. -/
abbrev etaTotal (p : zStd.TotalSpace) : W.TotalSpace :=
  ⟨p.1, Work.Thom.cxOfReal p.2⟩

/-- The fibrewise real-part projection of `W` onto itself. -/
abbrev Ptot (p : W.TotalSpace) : W.TotalSpace :=
  ⟨p.1, Work.Thom.cxOfReal (Work.Thom.cxRePart p.2)⟩

/-- The real-part map `W → zStd` is continuous on total spaces. -/
theorem continuous_rhoTotal : Continuous rhoTotal :=
  continuous_totalSpaceMap_intertwine W zStd cxRePartCLM
    (fun i => zStdUR_W_baseSet i) (fun b => zStdUR_W_indexAt b)
    (fun i j b v _ => cxRePart_W_coordChange i j b v)

/-- The inclusion `zStd → W` is continuous on total spaces. -/
theorem continuous_etaTotal : Continuous etaTotal :=
  continuous_totalSpaceMap_intertwine zStd W cxOfRealCLM
    (fun i => (zStdUR_W_baseSet i).symm) (fun b => (zStdUR_W_indexAt b).symm)
    (fun i j b v _ => cxOfReal_zStd_coordChange i j b v)

/-- The fibrewise real-part projection of `W` onto itself is continuous. -/
theorem continuous_Ptot : Continuous Ptot :=
  continuous_etaTotal.comp continuous_rhoTotal

/-! ## The bundle isomorphism `realification (tautDual 2) ≅ zStd` -/

/-- The realification of the tautological dual line bundle over `ℂP²`. -/
abbrev tautDualTwoR : RealBundle (Work.Projective.CP 2) (EuclideanSpace ℂ (Fin 1)) (Fin 3) :=
  Work.Thom.realification (Work.Gen.tautDual 2)

/-- `equivC1R2` intertwines the transition functions. -/
theorem equivC1R2_mapFibre_coordChange (i j : Fin 3) (b : Work.Projective.CP 2)
    (v : EuclideanSpace ℂ (Fin 1)) :
    equivC1R2 (tautDualTwoR.coordChange i j b v) = zStd.coordChange i j b (equivC1R2 v) := by
  rw [show zStd.coordChange i j b =
      (equivC1R2 : EuclideanSpace ℂ (Fin 1) →L[ℝ] EuclideanSpace ℝ (Fin 2)).comp
        ((tautDualTwoR.coordChange i j b).comp
          (equivC1R2.symm : EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℂ (Fin 1))) from
    RealBundle.mapFibre_coordChange equivC1R2 tautDualTwoR i j b]
  simp

/-- `equivC1R2.symm` intertwines the transition functions the other way. -/
theorem equivC1R2_symm_coordChange (i j : Fin 3) (b : Work.Projective.CP 2)
    (v : EuclideanSpace ℝ (Fin 2)) :
    equivC1R2.symm (zStd.coordChange i j b v) = tautDualTwoR.coordChange i j b (equivC1R2.symm v) := by
  rw [show zStd.coordChange i j b =
      (equivC1R2 : EuclideanSpace ℂ (Fin 1) →L[ℝ] EuclideanSpace ℝ (Fin 2)).comp
        ((tautDualTwoR.coordChange i j b).comp
          (equivC1R2.symm : EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℂ (Fin 1))) from
    RealBundle.mapFibre_coordChange equivC1R2 tautDualTwoR i j b]
  simp

/-- **The bundle isomorphism `realification (tautDual 2) ≅ zStd`** (change of fibre along
`equivC1R2`). -/
noncomputable def bundleIsoTautDualTwoR : Work.Thom.BundleIso tautDualTwoR zStd where
  hom := fun _ => equivC1R2.toLinearMap
  inv := fun _ => equivC1R2.symm.toLinearMap
  left_inv := fun _ x => equivC1R2.symm_apply_apply x
  right_inv := fun _ y => equivC1R2.apply_symm_apply y
  continuous_hom := continuous_totalSpaceMap_intertwine tautDualTwoR zStd
    (equivC1R2 : EuclideanSpace ℂ (Fin 1) →L[ℝ] EuclideanSpace ℝ (Fin 2))
    (fun i => RealBundle.mapFibre_baseSet equivC1R2 tautDualTwoR i)
    (fun b => RealBundle.mapFibre_indexAt equivC1R2 tautDualTwoR b)
    (fun i j b v _ => equivC1R2_mapFibre_coordChange i j b v)
  continuous_inv := continuous_totalSpaceMap_intertwine zStd tautDualTwoR
    (equivC1R2.symm : EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℂ (Fin 1))
    (fun i => (RealBundle.mapFibre_baseSet equivC1R2 tautDualTwoR i).symm)
    (fun b => (RealBundle.mapFibre_indexAt equivC1R2 tautDualTwoR b).symm)
    (fun i j b v _ => equivC1R2_symm_coordChange i j b v)

/-- **The homeomorphism of the punctured total spaces induced by a bundle isomorphism**, for
possibly *different* fibre types.  (The version of the Thom chapter,
`Work.Thom.BundleIso.punctHomeomorph`, is stated for a common fibre type.) -/
noncomputable def punctHomeomorphGen {B : Type} [TopologicalSpace B] {F F' : Type}
    [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup F'] [NormedSpace ℝ F']
    {ι ι' : Type} {Z : VectorBundleCore ℝ B F ι} {Z' : VectorBundleCore ℝ B F' ι'}
    (e : Work.Thom.BundleIso Z Z') :
    ↥(Work.Thom.zeroComplement Z) ≃ₜ ↥(Work.Thom.zeroComplement Z') where
  toFun p := ⟨e.toTotalSpace p.1, e.hom_ne_zero p.2⟩
  invFun p := ⟨e.invTotalSpace p.1, e.symm.hom_ne_zero p.2⟩
  left_inv p := by
    apply Subtype.ext
    show e.invTotalSpace (e.toTotalSpace p.1) = p.1
    exact e.toTotalSpace_left_inv p.1
  right_inv p := by
    apply Subtype.ext
    show e.toTotalSpace (e.invTotalSpace p.1) = p.1
    exact e.toTotalSpace_right_inv p.1
  continuous_toFun := Continuous.subtype_mk
    (e.continuous_hom.comp continuous_subtype_val) _
  continuous_invFun := Continuous.subtype_mk
    (e.continuous_inv.comp continuous_subtype_val) _

/-- The change of fibre `equivC1R2` induces a homeomorphism of the punctured total spaces. -/
noncomputable def punctHomeoTautDualTwoR :
    ↥(Work.Thom.zeroComplement tautDualTwoR) ≃ₜ ↥(Work.Thom.zeroComplement zStd) :=
  punctHomeomorphGen bundleIsoTautDualTwoR

/-- **`H⁴` of the punctured total space of `zStd` vanishes**: it is homeomorphic to the punctured
total space of the realification of the tautological dual line bundle, i.e. to `ℂ³∖0 ≃ S⁵`. -/
theorem isZero_cohomology_four_zStd :
    CategoryTheory.Limits.IsZero (Work.Thom.Coh ℤ 4 ↥(Work.Thom.zeroComplement zStd)) := by
  obtain ⟨iso⟩ := Work.Cohomology.cohomologyIso_of_homotopyEquiv
    punctHomeoTautDualTwoR.toHomotopyEquiv 4
  exact CategoryTheory.Limits.IsZero.of_iso
    (puncturedTautDualTwoHZero 4 (by norm_num) (by norm_num)) iso.symm

end

end Work.ThomBordism.Grassmann
