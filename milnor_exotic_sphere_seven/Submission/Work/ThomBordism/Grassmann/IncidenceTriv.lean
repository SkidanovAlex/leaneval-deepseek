import Mathlib
import Submission.Work.ThomBordism.Grassmann.Model
import Submission.Work.Thom.bijective_proj_zeroComplementA

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

/-!
# The cohomology of a product with a punctured Euclidean space

The Gysin descent `Work.Thom.bijective_proj_zeroComplementA` for the *trivial* bundle over `B` of
rank `r` says that the projection `π : B × (ℝʳ∖0) → B` induces an isomorphism on `Hʲ` whenever
`j + 2 ≤ r`.  This module records that statement in the form used by the band computation of the
incidence fibration.  The bridge between the total space of the trivial bundle and the product is
the homeomorphism `Work.Thom.trivProductHomeo`.
-/

open CategoryTheory AlgebraicTopology Simplicial Limits
open scoped Simplicial Topology

namespace Work.ThomBordism.Grassmann

noncomputable section

open Work.Cohomology

/-- An isomorphism of `ℤ`-modules gives a bijection of the underlying modules. -/
theorem bijective_of_isIso_moduleCat {M N : ModuleCat ℤ} (f : M ⟶ N) [IsIso f] :
    Function.Bijective f.hom := by
  have h1 : ∀ x : M, (inv f).hom (f.hom x) = x := by
    intro x
    have h := LinearMap.congr_fun (show ((inv f).hom).comp f.hom = LinearMap.id from by
      rw [← ModuleCat.hom_comp, IsIso.hom_inv_id, ModuleCat.hom_id]) x
    simpa using h
  have h2 : ∀ y : N, f.hom ((inv f).hom y) = y := by
    intro y
    have h := LinearMap.congr_fun (show (f.hom).comp ((inv f).hom) = LinearMap.id from by
      rw [← ModuleCat.hom_comp, IsIso.inv_hom_id, ModuleCat.hom_id]) y
    simpa using h
  exact ⟨fun x y hxy => by rw [← h1 x, hxy, h1 y], fun y => ⟨(inv f).hom y, h2 y⟩⟩

/-- A homeomorphism induces an isomorphism on singular cohomology. -/
theorem isIso_singularCohomologyMap_of_homeomorph {X Y : Type} [TopologicalSpace X]
    [TopologicalSpace Y] (e : X ≃ₜ Y) (n : ℕ) :
    IsIso (Work.Cohomology.singularCohomologyMap ℤ (TopCat.of X) (TopCat.of Y) (TopCat.ofHom e) n) :=
  Work.Cohomology.homotopyEquiv ℤ (TopCat.of X) (TopCat.of Y) (TopCat.ofHom e)
    (TopCat.ofHom e.symm) e.toHomotopyEquiv.left_inv.some e.toHomotopyEquiv.right_inv.some n

/-- The homeomorphism between the zero complement of the trivial bundle and the product of the base
with the punctured fibre, obtained from `Work.Thom.trivProductHomeo`. -/
noncomputable def zeroComplementTrivHomeo (B : Type) [TopologicalSpace B] (F : Type)
    [NormedAddCommGroup F] [NormedSpace ℝ F] (ι : Type) [Inhabited ι] :
    ↥(Work.Thom.zeroComplement (Work.TangentClasses.RealBundle.trivial B F ι)) ≃ₜ
      (B × {v : F // v ≠ 0}) where
  toFun p := ⟨(Work.Thom.trivProductHomeo B F ι p.1).1,
    ⟨(Work.Thom.trivProductHomeo B F ι p.1).2,
      (Work.Thom.trivProductHomeo_zeroComplement B F ι p.1).mp p.2⟩⟩
  invFun q := ⟨(Work.Thom.trivProductHomeo B F ι).symm (q.1, q.2.1), by
    refine (Work.Thom.trivProductHomeo_zeroComplement B F ι _).mpr ?_
    have h : Work.Thom.trivProductHomeo B F ι ((Work.Thom.trivProductHomeo B F ι).symm
        (q.1, q.2.1)) = (q.1, q.2.1) := Homeomorph.apply_symm_apply _ _
    rw [h]
    exact q.2.2⟩
  left_inv p := Subtype.ext (Homeomorph.symm_apply_apply _ p.1)
  right_inv q := by
    have h := Homeomorph.apply_symm_apply (Work.Thom.trivProductHomeo B F ι) (q.1, q.2.1)
    refine Prod.ext ?_ ?_
    · show (Work.Thom.trivProductHomeo B F ι
        ((Work.Thom.trivProductHomeo B F ι).symm (q.1, q.2.1))).1 = q.1
      rw [h]
    · refine Subtype.ext ?_
      show (Work.Thom.trivProductHomeo B F ι
        ((Work.Thom.trivProductHomeo B F ι).symm (q.1, q.2.1))).2 = q.2.1
      rw [h]
  continuous_toFun :=
    ((continuous_fst.comp
        ((Work.Thom.trivProductHomeo B F ι).continuous.comp continuous_subtype_val)).prodMk
      ((continuous_snd.comp
        ((Work.Thom.trivProductHomeo B F ι).continuous.comp continuous_subtype_val)).subtype_mk _))
  continuous_invFun :=
    (((Work.Thom.trivProductHomeo B F ι).symm.continuous.comp
        (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))).subtype_mk _)

/-- **The projection of a product with a punctured Euclidean space is a cohomology isomorphism**:
`π^* : Hʲ(B;ℤ) → Hʲ(B × (ℝʳ∖0);ℤ)` is bijective whenever `j + 2 ≤ r`. -/
theorem trivPuncturedCohomology (r j : ℕ) (hj : j + 2 ≤ r) (B : Type) [TopologicalSpace B] :
    Function.Bijective ((Work.Cohomology.singularCohomologyMap ℤ
      (TopCat.of (B × {v : EuclideanSpace ℝ (Fin r) // v ≠ 0})) (TopCat.of B)
      (TopCat.ofHom ⟨fun p => p.1, continuous_fst⟩) j).hom) := by
  have hr : 1 ≤ r := by omega
  obtain ⟨T⟩ := Work.Thom.thomClassTrivialEuclideanA r B hr
  let Z := Work.TangentClasses.RealBundle.trivial B (EuclideanSpace ℝ (Fin r)) PUnit
  have hF : Module.finrank ℝ (EuclideanSpace ℝ (Fin r)) = r := by simp
  have hb := Work.Thom.bijective_proj_zeroComplementA Z hF T hj
  let e := zeroComplementTrivHomeo B (EuclideanSpace ℝ (Fin r)) PUnit
  let ecm : C(↥(Work.Thom.zeroComplement Z),
      B × {v : EuclideanSpace ℝ (Fin r) // v ≠ 0}) :=
    ⟨(e : ↥(Work.Thom.zeroComplement Z) → B × {v : EuclideanSpace ℝ (Fin r) // v ≠ 0}),
      e.continuous_toFun⟩
  let pcm : C(B × {v : EuclideanSpace ℝ (Fin r) // v ≠ 0}, B) :=
    ⟨fun q => q.1, continuous_fst⟩
  let Estar := Work.Cohomology.singularCohomologyMap ℤ
    (TopCat.of ↥(Work.Thom.zeroComplement Z))
    (TopCat.of (B × {v : EuclideanSpace ℝ (Fin r) // v ≠ 0})) (TopCat.ofHom ecm) j
  let Pstar := Work.Cohomology.singularCohomologyMap ℤ
    (TopCat.of (B × {v : EuclideanSpace ℝ (Fin r) // v ≠ 0})) (TopCat.of B) (TopCat.ofHom pcm) j
  have hcm : (Work.Thom.bundleProj Z).comp (Work.Thom.subtypeMap (Work.Thom.zeroComplement Z))
      = pcm.comp ecm := by
    apply ContinuousMap.ext
    intro x
    show (x.1).proj = (e x).1
    show (x.1).proj
      = (Work.Thom.trivProductHomeo B (EuclideanSpace ℝ (Fin r)) PUnit x.1).1
    rw [Work.Thom.trivProductHomeo_apply]
  rw [hcm] at hb
  rw [Work.Thom.CohMap_comp ecm pcm ℤ j] at hb
  have hb2 : Function.Bijective ((Pstar ≫ Estar).hom) := hb
  rw [ModuleCat.hom_comp] at hb2
  have hb3 : Function.Bijective ((Estar.hom).comp Pstar.hom) := hb2
  haveI : IsIso Estar := isIso_singularCohomologyMap_of_homeomorph e j
  have he : Function.Bijective Estar.hom := bijective_of_isIso_moduleCat Estar
  refine ⟨fun y y' h => ?_, fun z => ?_⟩
  · have h2 : (Estar.hom.comp Pstar.hom) y = (Estar.hom.comp Pstar.hom) y' := by
      rw [LinearMap.comp_apply, LinearMap.comp_apply, h]
    exact hb3.1 h2
  · obtain ⟨y, hy⟩ := hb3.2 (Estar.hom z)
    refine ⟨y, he.1 ?_⟩
    rw [LinearMap.comp_apply] at hy
    exact hy

end

end Work.ThomBordism.Grassmann
