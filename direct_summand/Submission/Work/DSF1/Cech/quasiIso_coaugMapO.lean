import Mathlib
import Submission.Work.DSF1.Cech.CechOLocal
import Submission.Work.DSF1.Cech.CechMain
import Submission.Work.DSF1.Cech.cechSpec_quasiIso

/-!
# The coaugmentation of the Čech complex of `Spec R` is a quasi-isomorphism

Let `R` be a commutative ring, `U : ι → (Spec R).Opens` a family of opens and
`cechO R U` the Čech complex of the structure sheaf of `Spec R` along `U`, viewed as a
complex of `R`-modules.  The coaugmentation `coaugO R U : R ⟶ (cechO R U).X 0` is a
morphism of complexes (`coaug0_cech_d`), hence defines a chain map
`coaugMapO R U : R[0] ⟶ cechO R U`.

This file proves that `coaugMapO R U` is a quasi-isomorphism as soon as

* `cechO R U` is exact in positive degrees (`hexact`),
* `coaugO R U` is injective (`h1`),
* `coaugO R U` is surjective onto the degree-zero cycles (`h2`).

The proof is the generic form of `Work.DSF1.Cech.quasiIso_coaugMap`
(`Submission/Work/DSF1/Cech/CechMain.lean`): it never used that `U` was a family of
principal opens, so it applies verbatim to an arbitrary family.  The two ingredients are

* in degree `0`, the map `coaugMapO` factors through the identification of the cycles of
  `R[0]` with `R`, and the hypotheses `h1`, `h2` say that this identification is
  bijective;
* in positive degrees, `R[0]` is exact, so it suffices that `cechO R U` is exact, which is
  `hexact`.
-/

set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 1600000
set_option linter.style.haveILetI false

open CategoryTheory AlgebraicGeometry Opposite Limits

namespace Work.DSF1.Cech

universe u

/-- **Generic quasi-isomorphism criterion for the coaugmentation.**  Let `K` be a cochain
complex of `R`-modules concentrated in nonnegative degrees, let `c : R ⟶ K.X 0` be a
degree-zero map with `c ≫ K.d 0 1 = 0`, and let `cc : R[0] ⟶ K` be the induced chain map.
If `K` is exact in positive degrees and `c` is injective and surjective onto the
degree-zero cycles, then `cc` is a quasi-isomorphism. -/
theorem quasiIso_fromSingle₀ (R : Type u) [CommRing R]
    (K : CochainComplex (ModuleCat.{u} R) ℕ)
    (c : ModuleCat.of R R ⟶ K.X 0) (hc : c ≫ K.d 0 1 = 0)
    (hexact : ∀ n : ℕ, ∀ s : K.X (n + 1), (K.d (n + 1) (n + 2)).hom s = 0 →
      ∃ t : K.X n, (K.d n (n + 1)).hom t = s)
    (h1 : ∀ q : R, c.hom q = 0 → q = 0)
    (h2 : ∀ s : K.X 0, (K.d 0 1).hom s = 0 → ∃ q : R, c.hom q = s) :
    QuasiIso ((CochainComplex.fromSingle₀Equiv K (ModuleCat.of R R)).symm ⟨c, hc⟩) := by
  let cc := (CochainComplex.fromSingle₀Equiv K (ModuleCat.of R R)).symm ⟨c, hc⟩
  change QuasiIso cc
  have hcc0 : cc.f 0 = c := CochainComplex.fromSingle₀Equiv_symm_apply_f_zero c hc
  have hzero : IsIso (HomologicalComplex.homologyMap cc 0) := by
    have hhom : HomologicalComplex.homologyMap cc 0 =
        (CochainComplex.isoHomologyπ₀ ((CochainComplex.single₀ (ModuleCat.{u} R)).obj
            (ModuleCat.of R R))).inv ≫ HomologicalComplex.cyclesMap cc 0 ≫
          (CochainComplex.isoHomologyπ₀ K).hom := by
      rw [← cancel_mono (CochainComplex.isoHomologyπ₀ K).inv]
      rw [CochainComplex.isoHomologyπ₀_inv_naturality]
      simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
    set g : ModuleCat.of R R ⟶ K.cycles 0 :=
      (HomologicalComplex.singleObjCyclesSelfIso (ComplexShape.up ℕ) 0
          (ModuleCat.of R R)).inv ≫ HomologicalComplex.cyclesMap cc 0 with hg
    have hstep : (HomologicalComplex.singleObjCyclesSelfIso (ComplexShape.up ℕ) 0
        (ModuleCat.of R R)).inv ≫
        ((CochainComplex.single₀ (ModuleCat.{u} R)).obj (ModuleCat.of R R)).iCycles 0 =
        𝟙 (ModuleCat.of R R) := by
      rw [HomologicalComplex.singleObjCyclesSelfIso_inv_iCycles,
        CochainComplex.single₀ObjXSelf]
      rfl
    have hgi : g ≫ K.iCycles 0 = c := by
      rw [hg, Category.assoc, HomologicalComplex.cyclesMap_i, ← Category.assoc, hstep,
        Category.id_comp, hcc0]
    have hcyc : HomologicalComplex.cyclesMap cc 0 =
        (HomologicalComplex.singleObjCyclesSelfIso (ComplexShape.up ℕ) 0
          (ModuleCat.of R R)).hom ≫ g := by
      rw [hg, ← Category.assoc, Iso.hom_inv_id, Category.id_comp]
    have hinj : Function.Injective g.hom := by
      intro x y hxy
      have hx : (K.iCycles 0).hom (g.hom x) = c.hom x := by
        have := LinearMap.congr_fun (congrArg ModuleCat.Hom.hom hgi) x
        simpa only [ModuleCat.hom_comp, LinearMap.comp_apply] using this
      have hy : (K.iCycles 0).hom (g.hom y) = c.hom y := by
        have := LinearMap.congr_fun (congrArg ModuleCat.Hom.hom hgi) y
        simpa only [ModuleCat.hom_comp, LinearMap.comp_apply] using this
      have hsub : c.hom (x - y) = 0 := by
        rw [map_sub, ← hx, ← hy, hxy, sub_self]
      exact sub_eq_zero.mp (h1 (x - y) hsub)
    have hsurj : Function.Surjective g.hom := by
      intro y
      have hcyc' : (K.d 0 1).hom ((K.iCycles 0).hom y) = 0 := by
        have h := LinearMap.congr_fun (congrArg ModuleCat.Hom.hom
          (HomologicalComplex.iCycles_d (K := K) (i := 0) (j := 1))) y
        simpa only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_zero,
          LinearMap.zero_apply] using h
      obtain ⟨q, hq⟩ := h2 ((K.iCycles 0).hom y) hcyc'
      refine ⟨q, ?_⟩
      have hmono : Function.Injective ((K.iCycles 0).hom : K.cycles 0 → K.X 0) :=
        (ModuleCat.mono_iff_injective _).mp inferInstance
      apply hmono
      rw [← hq]
      exact LinearMap.congr_fun (congrArg ModuleCat.Hom.hom hgi) q
    haveI : IsIso g := by
      rw [isIso_iff_mono_and_epi, ModuleCat.mono_iff_injective, ModuleCat.epi_iff_surjective]
      exact ⟨hinj, hsurj⟩
    rw [hhom, hcyc]
    infer_instance
  rw [quasiIso_iff]
  intro i
  cases i with
  | zero =>
    rw [quasiIsoAt_iff_isIso_homologyMap]
    exact hzero
  | succ n =>
    rw [quasiIsoAt_iff_exactAt cc (n + 1)
        (CochainComplex.exactAt_succ_single_obj (ModuleCat.of R R) n),
      exactAt_succ_iff K n]
    exact hexact n

theorem quasiIso_coaugMapO (R : Type u) [CommRing R] {ι : Type u} [Finite ι]
    (U : ι → (AlgebraicGeometry.Spec (CommRingCat.of R)).Opens)
    (hexact : ∀ (n : ℕ) (s : (Work.DSF1.Cech.cechO R U).X (n + 1)),
      ((Work.DSF1.Cech.cechO R U).d (n + 1) (n + 2)).hom s = 0 →
        ∃ t : (Work.DSF1.Cech.cechO R U).X n,
          ((Work.DSF1.Cech.cechO R U).d n (n + 1)).hom t = s)
    (h1 : ∀ q : R, (Work.DSF1.Cech.coaugO R U).hom q = 0 → q = 0)
    (h2 : ∀ s : (Work.DSF1.Cech.cechO R U).X 0,
      ((Work.DSF1.Cech.cechO R U).d 0 1).hom s = 0 →
        ∃ q : R, (Work.DSF1.Cech.coaugO R U).hom q = s) :
    HomologicalComplex.quasiIso (ModuleCat.{u} R) (ComplexShape.up ℕ)
      (Work.DSF1.Cech.coaugMapO R U) :=
  quasiIso_fromSingle₀ R (cechO R U) (coaugO R U)
    (coaug0_cech_d R (spec R) (𝟙 (spec R)) U) hexact h1 h2

end Work.DSF1.Cech
