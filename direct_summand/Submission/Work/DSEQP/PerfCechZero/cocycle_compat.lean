import Mathlib
import Submission.Work.DSEQP.perf_K_d_pi
import Submission.Work.DSEQP.PerfAcyclic
import Submission.Work.DSEQP.PerfPresheaf
import Submission.Work.DSEQP.gf_gamma_eq_h0_cech

namespace Work.DSEQP.PerfCechZero

open CategoryTheory AlgebraicGeometry Limits Opposite
open scoped Simplicial BigOperators

universe u

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 800000
set_option linter.style.haveILetI false
set_option linter.unusedVariables false

/-!
# Compatibility of the degree-`0` components of a Čech `0`-cocycle

For an arbitrary presheaf `Q` of `R`-modules on the opens of a scheme `X` and an arbitrary
family of opens `U : ι → X.Opens`, the degree-`0` components of a `0`-cocycle of the Čech
complex `(cechComplexFunctor U).obj Q` agree on the pairwise intersections of the
degree-`0` Čech opens.  This is the compatibility condition consumed by
`Work.DSEQP.PerfCechZero.exists_level_compat` (and, before it, by `Wmap_eq_of_compat`).

The argument is a componentwise computation of the differential (`d 0 1` is the
difference of the two cofaces), together with transport along the equalities of opens
provided by the Čech nerve; it is a direct adaptation of
`Work.DSEQP.cech_isCompatible` to a presheaf which is not the structure sheaf.
-/

section General

variable {R : Type u} [CommRing R] {X : Scheme.{u}} {ι : Type u}

/-- The degree-`0` Čech datum of a cochain, as a family over the cover `Vc U`. -/
noncomputable def sfam (U : ι → X.Opens) (Q : X.Opensᵒᵖ ⥤ ModuleCat.{u} R)
    (y : ↥(((CategoryTheory.cechComplexFunctor U).obj Q).X 0)) (a : Fin 1 → ι) :
    ↥(Q.obj (op (Vc U a))) :=
  (Pi.π (fun x : Fin 1 → ι => Q.obj (op (Work.DSF1.Cech.Eobj U 0 x))) a) y

/-- **Component formula for the degree-`0` differential of the Čech complex.**  The `j`-th
component of `d 0 1 y` is the difference of the two restrictions of the components of `y`
indexed by the functions `fun _ => j 0` and `fun _ => j 1`. -/
theorem d01_apply_general (U : ι → X.Opens) (Q : X.Opensᵒᵖ ⥤ ModuleCat.{u} R)
    (y : ↥(((CategoryTheory.cechComplexFunctor U).obj Q).X 0)) (j : Fin 2 → ι) :
    (Pi.π (fun x => Q.obj (op (Work.DSF1.Cech.Eobj U 1 x))) j)
        ((((CategoryTheory.cechComplexFunctor U).obj Q).d 0 1).hom y)
      = (ConcreteCategory.hom (Q.map (((Work.DSF1.Cech.E U).map (SimplexCategory.δ 0).op).φ j).op))
          ((Pi.π (fun x => Q.obj (op (Work.DSF1.Cech.Eobj U 0 x)))
            (((Work.DSF1.Cech.E U).map (SimplexCategory.δ 0).op).f j)) y)
        - (ConcreteCategory.hom (Q.map (((Work.DSF1.Cech.E U).map (SimplexCategory.δ 1).op).φ j).op))
          ((Pi.π (fun x => Q.obj (op (Work.DSF1.Cech.Eobj U 0 x)))
            (((Work.DSF1.Cech.E U).map (SimplexCategory.δ 1).op).f j)) y) := by
  have hsum : (∑ a : Fin 2, (-1 : ℤ) ^ (a : ℕ) •
      (Pi.π (fun y => Q.obj (op (Work.DSF1.Cech.Eobj U 0 y)))
          (((Work.DSF1.Cech.E U).map (SimplexCategory.δ a).op).f j) ≫
        Q.map (((Work.DSF1.Cech.E U).map (SimplexCategory.δ a).op).φ j).op))
      = (Pi.π (fun y => Q.obj (op (Work.DSF1.Cech.Eobj U 0 y)))
            (((Work.DSF1.Cech.E U).map (SimplexCategory.δ 0).op).f j) ≫
          Q.map (((Work.DSF1.Cech.E U).map (SimplexCategory.δ 0).op).φ j).op)
        - (Pi.π (fun y => Q.obj (op (Work.DSF1.Cech.Eobj U 0 y)))
            (((Work.DSF1.Cech.E U).map (SimplexCategory.δ 1).op).f j) ≫
          Q.map (((Work.DSF1.Cech.E U).map (SimplexCategory.δ 1).op).φ j).op) := by
    rw [Fin.sum_univ_two, sub_eq_add_neg]
    simp
  have h := congrArg (fun (m : ((CategoryTheory.cechComplexFunctor U).obj Q).X 0 ⟶
      Q.obj (op (Work.DSF1.Cech.Eobj U 1 j))) =>
        (ConcreteCategory.hom m) y)
    (Work.DSF1.Cech.cech_d_comp_π U Q 0 j)
  rw [hsum] at h
  simp only [ConcreteCategory.comp_apply, ModuleCat.hom_sub, LinearMap.sub_apply] at h
  exact h

/-- **The kernel of `d 0 1`, componentwise.**  If `y` is a degree-`0` cocycle, then for every
degree-`1` index `j` the two restrictions of the corresponding components of `y` agree. -/
theorem d01_ker_general (U : ι → X.Opens) (Q : X.Opensᵒᵖ ⥤ ModuleCat.{u} R)
    (y : ↥(((CategoryTheory.cechComplexFunctor U).obj Q).X 0))
    (hy : ((((CategoryTheory.cechComplexFunctor U).obj Q).d 0 1).hom y) = 0) (j : Fin 2 → ι) :
    (ConcreteCategory.hom (Q.map (((Work.DSF1.Cech.E U).map (SimplexCategory.δ 0).op).φ j).op))
        ((Pi.π (fun x => Q.obj (op (Work.DSF1.Cech.Eobj U 0 x)))
          (((Work.DSF1.Cech.E U).map (SimplexCategory.δ 0).op).f j)) y)
      = (ConcreteCategory.hom (Q.map (((Work.DSF1.Cech.E U).map (SimplexCategory.δ 1).op).φ j).op))
        ((Pi.π (fun x => Q.obj (op (Work.DSF1.Cech.Eobj U 0 x)))
          (((Work.DSF1.Cech.E U).map (SimplexCategory.δ 1).op).f j)) y) := by
  have h2 : (Pi.π (fun x => Q.obj (op (Work.DSF1.Cech.Eobj U 1 x))) j)
      ((((CategoryTheory.cechComplexFunctor U).obj Q).d 0 1).hom y) = 0 := by
    rw [hy]
    simp
  rw [d01_apply_general, sub_eq_zero] at h2
  exact h2

/-- Transport of a degree-`0` component along an equality of indices. -/
lemma trv_index_general (U : ι → X.Opens) (Q : X.Opensᵒᵖ ⥤ ModuleCat.{u} R)
    (y : ↥(((CategoryTheory.cechComplexFunctor U).obj Q).X 0)) {a b : Fin 1 → ι} (h : a = b) :
    (ConcreteCategory.hom (trv Q (congrArg (fun t => Work.DSF1.Cech.Eobj U 0 t) h)))
        (sfam U Q y a) = sfam U Q y b := by
  have htrv : trv Q (congrArg (fun t => Work.DSF1.Cech.Eobj U 0 t) h)
      = eqToHom (congrArg (fun t : Fin 1 → ι => Q.obj (op (Work.DSF1.Cech.Eobj U 0 t))) h) := by
    rw [trv, eqToHom_map]
  have hπ := Pi.π_comp_eqToHom (fun x : Fin 1 → ι =>
      Q.obj (op (Work.DSF1.Cech.Eobj U 0 x))) h
  have h2 := congrArg (fun (m : ((CategoryTheory.cechComplexFunctor U).obj Q).X 0 ⟶
      Q.obj (op (Work.DSF1.Cech.Eobj U 0 b))) =>
        (ConcreteCategory.hom m) y) hπ
  rw [ConcreteCategory.comp_apply] at h2
  rw [← htrv] at h2
  exact h2

/-- **The matching condition.**  A cocycle in degree `0` of the Čech complex of a presheaf of
`R`-modules gives a compatible family over the cover by the degree-`0` opens. -/
theorem isCompatible_general (U : ι → X.Opens) (Q : X.Opensᵒᵖ ⥤ ModuleCat.{u} R)
    (y : ↥(((CategoryTheory.cechComplexFunctor U).obj Q).X 0))
    (hy : ((((CategoryTheory.cechComplexFunctor U).obj Q).d 0 1).hom y) = 0) :
    TopCat.Presheaf.IsCompatible Q (Vc U) (sfam U Q y) := by
  intro a a'
  have h0 : ((Work.DSF1.Cech.E U).map (SimplexCategory.δ 0).op).f (pair (a 0) (a' 0)) = a' := by
    rw [map_delta_zero_f]
    funext b
    rw [Subsingleton.elim b 0]
    rfl
  have h1 : ((Work.DSF1.Cech.E U).map (SimplexCategory.δ 1).op).f (pair (a 0) (a' 0)) = a := by
    rw [map_delta_one_f]
    funext b
    rw [Subsingleton.elim b 0]
    rfl
  have hWt : Work.DSF1.Cech.Eobj U 1 (pair (a 0) (a' 0)) = Vc U a ⊓ Vc U a' := by
    rw [Eobj_one_eq, pair_zero, pair_one]
    exact congrArg₂ (· ⊓ ·) (Eobj_zero_eq (U := U) a).symm (Eobj_zero_eq (U := U) a').symm
  have hV0 : Work.DSF1.Cech.Eobj U 0 (((Work.DSF1.Cech.E U).map (SimplexCategory.δ 0).op).f
      (pair (a 0) (a' 0))) = Vc U a' := congrArg (fun t => Work.DSF1.Cech.Eobj U 0 t) h0
  have hV1 : Work.DSF1.Cech.Eobj U 0 (((Work.DSF1.Cech.E U).map (SimplexCategory.δ 1).op).f
      (pair (a 0) (a' 0))) = Vc U a := congrArg (fun t => Work.DSF1.Cech.Eobj U 0 t) h1
  have T0 := trv_map_op Q hWt hV0
    (((Work.DSF1.Cech.E U).map (SimplexCategory.δ 0).op).φ (pair (a 0) (a' 0)))
    (TopologicalSpace.Opens.infLERight (Vc U a) (Vc U a'))
  have T1 := trv_map_op Q hWt hV1
    (((Work.DSF1.Cech.E U).map (SimplexCategory.δ 1).op).φ (pair (a 0) (a' 0)))
    (TopologicalSpace.Opens.infLELeft (Vc U a) (Vc U a'))
  have hj := d01_ker_general U Q y hy (pair (a 0) (a' 0))
  have key := congrArg (ConcreteCategory.hom (trv Q hWt)) hj
  have e0 : (ConcreteCategory.hom (trv Q hWt))
        ((ConcreteCategory.hom (Q.map
          (((Work.DSF1.Cech.E U).map (SimplexCategory.δ 0).op).φ (pair (a 0) (a' 0))).op))
          ((Pi.π (fun x : Fin 1 → ι => Q.obj (op (Work.DSF1.Cech.Eobj U 0 x)))
            (((Work.DSF1.Cech.E U).map (SimplexCategory.δ 0).op).f (pair (a 0) (a' 0)))) y))
      = (ConcreteCategory.hom (Q.map
          (TopologicalSpace.Opens.infLERight (Vc U a) (Vc U a')).op))
          (sfam U Q y a') := by
    rw [← ConcreteCategory.comp_apply, T0, ConcreteCategory.comp_apply]
    congr 1
    exact trv_index_general U Q y h0
  have e1 : (ConcreteCategory.hom (trv Q hWt))
        ((ConcreteCategory.hom (Q.map
          (((Work.DSF1.Cech.E U).map (SimplexCategory.δ 1).op).φ (pair (a 0) (a' 0))).op))
          ((Pi.π (fun x : Fin 1 → ι => Q.obj (op (Work.DSF1.Cech.Eobj U 0 x)))
            (((Work.DSF1.Cech.E U).map (SimplexCategory.δ 1).op).f (pair (a 0) (a' 0)))) y))
      = (ConcreteCategory.hom (Q.map
          (TopologicalSpace.Opens.infLELeft (Vc U a) (Vc U a')).op))
          (sfam U Q y a) := by
    rw [← ConcreteCategory.comp_apply, T1, ConcreteCategory.comp_apply]
    congr 1
    exact trv_index_general U Q y h1
  exact e1.symm.trans (key.symm.trans e0)

/-- The matching condition, in the form used by `exists_level_compat`: the two restrictions of
the degree-`0` components of a cocycle to the intersection of the corresponding Čech opens
agree. -/
theorem compat_CechOp (U : ι → X.Opens) (Q : X.Opensᵒᵖ ⥤ ModuleCat.{u} R)
    (y : ↥(((CategoryTheory.cechComplexFunctor U).obj Q).X 0))
    (hy : ((((CategoryTheory.cechComplexFunctor U).obj Q).d 0 1).hom y) = 0)
    (a b : (PerfSetup.CechIdx U 0).I) :
    (Q.map (homOfLE (inf_le_left : PerfSetup.CechOp U 0 a ⊓ PerfSetup.CechOp U 0 b ≤
        PerfSetup.CechOp U 0 a)).op).hom
      ((Pi.π (fun i : (PerfSetup.CechIdx U 0).I => Q.obj (op (PerfSetup.CechOp U 0 i))) a).hom y)
    = (Q.map (homOfLE (inf_le_right : PerfSetup.CechOp U 0 a ⊓ PerfSetup.CechOp U 0 b ≤
        PerfSetup.CechOp U 0 b)).op).hom
      ((Pi.π (fun i : (PerfSetup.CechIdx U 0).I => Q.obj (op (PerfSetup.CechOp U 0 i))) b).hom y) :=
  isCompatible_general U Q y hy a b

end General

theorem cocycle_compat (A : Type u) [CommRing A] (p : ℕ) [Fact p.Prime]
    (X : AlgebraicGeometry.Scheme.{u}) [AlgebraicGeometry.IsIntegral X]
    (f : X ⟶ AlgebraicGeometry.Spec (CommRingCat.of A))
    (S : Work.DSEQP.PerfSetup A p X f) {ι : Type u} (U : ι → X.Opens)
    (z : (S.K U).X 0) (hz : ((S.K U).d 0 1).hom z = 0)
    (a b : (PerfSetup.CechIdx U 0).I) :
    Work.DSEQP.Perf.map (S.hpU (PerfSetup.CechOp U 0 a))
        (S.hpU (PerfSetup.CechOp U 0 a ⊓ PerfSetup.CechOp U 0 b))
        ((X.presheaf.map (CategoryTheory.homOfLE
          (inf_le_left : PerfSetup.CechOp U 0 a ⊓ PerfSetup.CechOp U 0 b ≤
            PerfSetup.CechOp U 0 a)).op).hom)
        ((CategoryTheory.Limits.Pi.π (S.Kobj U 0) a).hom z)
      = Work.DSEQP.Perf.map (S.hpU (PerfSetup.CechOp U 0 b))
        (S.hpU (PerfSetup.CechOp U 0 a ⊓ PerfSetup.CechOp U 0 b))
        ((X.presheaf.map (CategoryTheory.homOfLE
          (inf_le_right : PerfSetup.CechOp U 0 a ⊓ PerfSetup.CechOp U 0 b ≤
            PerfSetup.CechOp U 0 b)).op).hom)
        ((CategoryTheory.Limits.Pi.π (S.Kobj U 0) b).hom z) := by
  change (S.perfPresheaf.map (CategoryTheory.homOfLE
          (inf_le_left : PerfSetup.CechOp U 0 a ⊓ PerfSetup.CechOp U 0 b ≤
            PerfSetup.CechOp U 0 a)).op).hom
        ((CategoryTheory.Limits.Pi.π (S.Kobj U 0) a).hom z)
      = (S.perfPresheaf.map (CategoryTheory.homOfLE
          (inf_le_right : PerfSetup.CechOp U 0 a ⊓ PerfSetup.CechOp U 0 b ≤
            PerfSetup.CechOp U 0 b)).op).hom
        ((CategoryTheory.Limits.Pi.π (S.Kobj U 0) b).hom z)
  exact compat_CechOp U S.perfPresheaf z hz a b

end Work.DSEQP.PerfCechZero
