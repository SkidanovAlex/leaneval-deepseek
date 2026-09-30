import Mathlib
import Submission.Work.Charts.Step3Cover
import Submission.Work.Charts.exists_centre_of_isClosed
import Submission.Work.Charts.exists_V_of_landsIn_Wp
import Submission.Work.Charts.landsIn_Wp_of_linEquiv
import Submission.Work.Charts.addMor_landsIn_Wp_of_landsIn_omega
import Submission.Work.Charts.rep_of_rochData
import Submission.Work.Charts.galCharts_of_orbit_cover

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


set_option autoImplicit false
set_option maxHeartbeats 4000000

universe u

open CategoryTheory Limits

namespace Work.Charts

noncomputable section

theorem exists_orbit_cover {K : Type u} [Field K] {C : Work.CurveBasics.Curve K}
    [Work.SpecLin.DivBase C] (R : Work.Charts.RochData C) (I : Work.Charts.Step3Data R) :
    ∃ (k' : IntermediateField K (SeparableClosure K)) (_ : FiniteDimensional K ↥k')
      (_ : IsGalois K ↥k') (ι₀ : Type u) (_ : Fintype ι₀)
      (E₀ : ι₀ → Work.GCBasics.FPt ((I.symGeom R.g).S) ↥k'),
      ∀ {F : Type u} [Field F] [Algebra K F] (ε : ↥k' →ₐ[K] F) (c : Work.GCBasics.Pic0 C F),
        ∃ i : ι₀, ∀ τ : ↥k' ≃ₐ[K] ↥k',
          @Work.Charts.InChart K _ C _ R (I.symGeom R.g) I.d F _ _
            (Work.GCBasics.RPt.map (ε.comp τ.toAlgHom) (E₀ i)) c := by
  classical
  letI := I.symGeom R.g
  -- `Sym^g C` is compact, so a finite subcover of the `Ω_E` can be extracted
  haveI hQC : AlgebraicGeometry.QuasiCompact ((I.symGeom R.g).S).hom :=
    I.geo.quasiCompact_g
  haveI hCS : CompactSpace ((I.symGeom R.g).S).left :=
    AlgebraicGeometry.QuasiCompact.compactSpace_of_compactSpace ((I.symGeom R.g).S).hom
  let Ω : (Σ k₁ : {k₁ : IntermediateField K (SeparableClosure K) // FiniteDimensional K ↥k₁},
      Work.GCBasics.FPt ((I.symGeom R.g).S) ↥k₁.1) → ((I.symGeom R.g).S).left.Opens :=
    fun E => (haveI := E.1.2; omegaOpen R I.symGeom I.resid I.geo E.2 I.a I.d)
  have hΩtop : (⨆ E, Ω E) = ⊤ := iSup_omega_eq_top R I
  have hcover : (Set.univ : Set ((I.symGeom R.g).S).left) ⊆
      ⋃ E, (Ω E : Set ((I.symGeom R.g).S).left) := by
    intro x _
    have hx : x ∈ (⨆ E, Ω E : ((I.symGeom R.g).S).left.Opens) := by
      rw [hΩtop]; trivial
    exact Set.mem_iUnion.mpr (TopologicalSpace.Opens.mem_iSup.mp hx)
  obtain ⟨T, hT⟩ := isCompact_univ.elim_finite_subcover
    (fun E => (Ω E : Set ((I.symGeom R.g).S).left)) (fun E => (Ω E).2) hcover
  have hT' : ∀ x : ((I.symGeom R.g).S).left,
      ∃ E ∈ T, x ∈ (Ω E : Set ((I.symGeom R.g).S).left) := by
    intro x
    obtain ⟨i, hi, hxi⟩ := Set.mem_iUnion₂.mp (hT (Set.mem_univ x))
    exact ⟨i, hi, hxi⟩
  -- the compositum of the finitely many fields of definition, and its normal closure
  let k'' : IntermediateField K (SeparableClosure K) := ⨆ E ∈ T, E.1.1
  have hfd'' : FiniteDimensional K ↥k'' :=
    IntermediateField.finiteDimensional_iSup_of_finset'
      (t := fun E : (Σ k₁ : {k₁ : IntermediateField K (SeparableClosure K) //
          FiniteDimensional K ↥k₁}, Work.GCBasics.FPt ((I.symGeom R.g).S) ↥k₁.1) => E.1.1)
      (s := T) (fun E _ => E.1.2)
  haveI := hfd''
  let k' : IntermediateField K (SeparableClosure K) :=
    IntermediateField.normalClosure K ↥k'' (SeparableClosure K)
  have hfd' : FiniteDimensional K ↥k' :=
    normalClosure.is_finiteDimensional K ↥k'' (SeparableClosure K)
  have hgal' : IsGalois K ↥k' := IsGalois.normalClosure K ↥k'' (SeparableClosure K)
  -- the centres, pushed from their fields of definition to `k'`
  let ι₀ : Type u := ↥T
  haveI hfint : Fintype ι₀ := inferInstance
  let E₀ : ι₀ → Work.GCBasics.FPt ((I.symGeom R.g).S) ↥k' := fun E =>
    Work.GCBasics.RPt.map (IntermediateField.inclusion
      (le_trans (le_iSup₂ (f := fun E (_ : E ∈ T) => E.1.1) E.1 E.2)
        (IntermediateField.le_normalClosure k''))) E.1.2
  refine ⟨k', hfd', hgal', ι₀, hfint, E₀, ?_⟩
  intro F _ _ ε c
  -- represent `c` as `[divOf D - g · P₀]`
  obtain ⟨D, hDdeg, hDc⟩ := rep_of_rochData (C := C) R I.P0Div I.hP0 (F := F) c
  -- `D` lands in some `Ω_E` of the finite subcover
  obtain ⟨E, hE, hxE⟩ := hT' (D.left (IsLocalRing.closedPoint F))
  haveI hEfin : FiniteDimensional K ↥E.1.1 := E.1.2
  refine ⟨⟨E, hE⟩, ?_⟩
  intro τ
  let incl : ↥E.1.1 →ₐ[K] ↥k' := IntermediateField.inclusion
    (le_trans (le_iSup₂ (f := fun E (_ : E ∈ T) => E.1.1) E hE)
      (IntermediateField.le_normalClosure k''))
  let ε' : ↥E.1.1 →ₐ[K] F := (ε.comp τ.toAlgHom).comp incl
  have hE₀ : E₀ ⟨E, hE⟩ = Work.GCBasics.RPt.map incl E.2 := rfl
  have hE' : Work.GCBasics.RPt.map (ε.comp τ.toAlgHom) (E₀ ⟨E, hE⟩) =
      Work.GCBasics.RPt.map ε' E.2 := by
    rw [hE₀, ← Work.GCBasics.RPt.map_comp]
  have hDΩ : Work.GCBasics.RPt.LandsIn D
      (omegaOpen R I.symGeom I.resid I.geo E.2 I.a I.d) := hxE
  have hWp := addMor_landsIn_Wp_of_landsIn_omega R I.symGeom I.resid I.geo I.a I.d E.2 ε' D hDΩ
  obtain ⟨y, hyV, hylin⟩ := exists_V_of_landsIn_Wp R I.symGeom I.resid I.geo I.a
    (P0Div := I.P0Div) I.ha I.d
    (Work.Domain.Resid.addMor I.symGeom I.resid.addMap D (Work.GCBasics.RPt.map ε' E.2)) hWp
  have hdiv : (I.symGeom (R.g + R.g)).divOf
        (Work.Domain.Resid.addMor I.symGeom I.resid.addMap D (Work.GCBasics.RPt.map ε' E.2))
      = (I.symGeom R.g).divOf D + (I.symGeom R.g).divOf (Work.GCBasics.RPt.map ε' E.2) := by
    have h := Work.Domain.Resid.addMor_divOf (symGeom := I.symGeom) (addMap := I.resid.addMap)
      I.resid.addMap_divOf (X := Work.GCBasics.specOf K F) D
      (Work.GCBasics.RPt.map ε' E.2) (𝟙 (Work.GCBasics.specOf K F))
    simpa using h
  have hbig : Work.GCBasics.LinEquiv C ((I.symGeom R.g).divOf y)
      ((I.symGeom R.g).divOf D + (I.symGeom R.g).divOf (Work.GCBasics.RPt.map ε' E.2)
        - (R.g : ℤ) • pullK C I.P0Div) := by
    rw [← hdiv]; exact hylin
  rw [hE']
  refine ⟨y, hyV, ?_⟩
  show Work.GCBasics.Pic0.mk (divOf y - divOf (Work.GCBasics.RPt.map ε' E.2))
    (Ddeg_divOf_sub y (Work.GCBasics.RPt.map ε' E.2)) = c
  rw [← hDc]
  refine (Work.GCBasics.Pic0.mk_eq_iff (Ddeg_divOf_sub y (Work.GCBasics.RPt.map ε' E.2))
    hDdeg).mpr ?_
  have habel : ((I.symGeom R.g).divOf D + (I.symGeom R.g).divOf (Work.GCBasics.RPt.map ε' E.2)
        - (R.g : ℤ) • pullK C I.P0Div) - (I.symGeom R.g).divOf (Work.GCBasics.RPt.map ε' E.2)
      = (I.symGeom R.g).divOf D - (R.g : ℤ) • pullK C I.P0Div := by abel
  rw [← habel]
  exact (Work.GCBasics.LinEquiv.sub_iff ((I.symGeom R.g).divOf y)
    ((I.symGeom R.g).divOf D + (I.symGeom R.g).divOf (Work.GCBasics.RPt.map ε' E.2)
      - (R.g : ℤ) • pullK C I.P0Div)
    ((I.symGeom R.g).divOf (Work.GCBasics.RPt.map ε' E.2))).mpr hbig

end

end Work.Charts
