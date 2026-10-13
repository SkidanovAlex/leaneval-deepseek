import Mathlib
import Submission.Work.DSMX0bU.CechHomotopyDefs

/-!
# The simplicial identity `δ (i.succ) ≫ K = K ≫ δ i` for the contracting homotopy `cechK`

Let `U : ι → X.Opens`, `i₀ : ι`, `V : X.Opens` with `V ≤ U i₀` and `P` a presheaf of
abelian groups on `X`.  The Čech complex of the family `i ↦ V ⊓ U i` is contractible: the
index `i₀` can be inserted at position `0` (`Work.DSF1.Cech.insIdx`), and since every
intersection of members of the family is contained in `V = V ⊓ U i₀`, the coface maps
that insert `i₀` are isomorphisms of presheaf values
(`Work.DSMX0bU.isIso_cof0`).  The contracting homotopy `cechK` is the composite of the
projection onto the `i₀`-inserted index with the inverse of this coface
(`Work.DSMX0bU.cechK`).

This file proves the *second* family of simplicial identities satisfied by `cechK`, namely

`δ (i.succ) ≫ cechK (n+1) = cechK n ≫ δ i`   for every `i : Fin (n+2)`,

the first one (`δ 0 ≫ cechK n = 𝟙`) being `Work.DSMX0bU.delta0_comp_cechK`
(placed, like the definitions just cited, in `Submission/Work/DSMX0bU/CechHomotopyDefs.lean`).
Together they say that the alternating sum of the cofaces is killed by `cechK`, i.e. that
`cechK` is a contracting homotopy; this is what
`Submission/Work/DSMX0bU/cechTrivAll_of_le_mem.lean` consumes.

The proof is a formal computation at the level of components:
`Work.DSMX0bU.cech_delta_comp_π` and `Work.DSMX0bU.cechK_comp_π` express the composites
with the projections of the product in degree `n+1`, `Work.DSF1.Cech.InsIdxDelta` is the
purely combinatorial statement that the coface `δ (i.succ)` commutes with the insertion
of `i₀`, and `Work.DSF1.Cech.deltaSucc_inv_nat` is the naturality of inverse isomorphisms
along the resulting commutative square of cofaces.  This mirrors
`Work.DSF1.Cech.DeltaSuccK`, where the same computation is done for a general family `U`
whose `i₀`-inserting cofaces are inverted by the coefficients.
-/

namespace Work.DSMX0bU

open CategoryTheory AlgebraicGeometry Opposite Limits
open scoped Simplicial BigOperators

set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 800000
set_option linter.style.haveILetI false

universe u

theorem DeltaSuccCechK {X : AlgebraicGeometry.Scheme.{u}} {ι : Type u}
    (U : ι → X.Opens) (i₀ : ι) (V : X.Opens) (hV : V ≤ U i₀)
    (P : CategoryTheory.Functor (Opposite (X.Opens)) (AddCommGrpCat.{u})) (n : ℕ) (i : Fin (n+2)) :
    CategoryTheory.CategoryStruct.comp (cechDelta U V P (n+1) i.succ) (cechK U i₀ V hV P (n+1))
      = CategoryTheory.CategoryStruct.comp (cechK U i₀ V hV P n) (cechDelta U V P n i) := by
  let W : ι → X.Opens := fun i => V ⊓ U i
  apply Pi.hom_ext
  intro y
  change CategoryStruct.comp
        (CategoryStruct.comp ((Cosi U V P).δ i.succ) (cechK U i₀ V hV P (n+1)))
        (Pi.π (fun z => P.obj (op (Work.DSF1.Cech.Eobj W (n+1) z))) y)
      = CategoryStruct.comp
        (CategoryStruct.comp (cechK U i₀ V hV P n) ((Cosi U V P).δ i))
        (Pi.π (fun z => P.obj (op (Work.DSF1.Cech.Eobj W (n+1) z))) y)
  conv_lhs =>
    rw [Category.assoc, cechK_comp_π U i₀ V hV P (n+1) y, ← Category.assoc,
        cech_delta_comp_π U V P (n+1) i.succ (Work.DSF1.Cech.insIdx W i₀ (n+1) y),
        Category.assoc]
  conv_rhs =>
    rw [Category.assoc, cech_delta_comp_π U V P n i y, ← Category.assoc,
        cechK_comp_π U i₀ V hV P n (((Work.DSF1.Cech.E W).map (SimplexCategory.δ i).op).f y),
        Category.assoc]
  have hZ : ((Work.DSF1.Cech.E W).map (SimplexCategory.δ i.succ).op).f
        (Work.DSF1.Cech.insIdx W i₀ (n+1) y) =
      Work.DSF1.Cech.insIdx W i₀ n
        (((Work.DSF1.Cech.E W).map (SimplexCategory.δ i).op).f y) :=
    Work.DSF1.Cech.InsIdxDelta W i₀ n i y
  have hpi : Pi.π (fun z => P.obj (op (Work.DSF1.Cech.Eobj W (n+1) z)))
        (((Work.DSF1.Cech.E W).map (SimplexCategory.δ i.succ).op).f
          (Work.DSF1.Cech.insIdx W i₀ (n+1) y)) ≫
      eqToHom (congrArg (fun z => P.obj (op (Work.DSF1.Cech.Eobj W (n+1) z))) hZ) =
      Pi.π (fun z => P.obj (op (Work.DSF1.Cech.Eobj W (n+1) z)))
        (Work.DSF1.Cech.insIdx W i₀ n
          (((Work.DSF1.Cech.E W).map (SimplexCategory.δ i).op).f y)) :=
    Work.DSF1.Cech.deltaSucc_pi_π_eqToHom
      (fun z => P.obj (op (Work.DSF1.Cech.Eobj W (n+1) z))) hZ
  let f1 : Work.DSF1.Cech.Eobj W (n+2) (Work.DSF1.Cech.insIdx W i₀ (n+1) y) ⟶
      Work.DSF1.Cech.Eobj W (n+1) y :=
    ((Work.DSF1.Cech.E W).map (SimplexCategory.δ (0 : Fin (n+3))).op).φ
      (Work.DSF1.Cech.insIdx W i₀ (n+1) y)
  let f2 : Work.DSF1.Cech.Eobj W (n+2) (Work.DSF1.Cech.insIdx W i₀ (n+1) y) ⟶
      Work.DSF1.Cech.Eobj W (n+1)
        (((Work.DSF1.Cech.E W).map (SimplexCategory.δ i.succ).op).f
          (Work.DSF1.Cech.insIdx W i₀ (n+1) y)) :=
    ((Work.DSF1.Cech.E W).map (SimplexCategory.δ i.succ).op).φ
      (Work.DSF1.Cech.insIdx W i₀ (n+1) y)
  let fi : Work.DSF1.Cech.Eobj W (n+1) y ⟶
      Work.DSF1.Cech.Eobj W n (((Work.DSF1.Cech.E W).map (SimplexCategory.δ i).op).f y) :=
    ((Work.DSF1.Cech.E W).map (SimplexCategory.δ i).op).φ y
  let g0 : Work.DSF1.Cech.Eobj W (n+1)
        (Work.DSF1.Cech.insIdx W i₀ n
          (((Work.DSF1.Cech.E W).map (SimplexCategory.δ i).op).f y)) ⟶
      Work.DSF1.Cech.Eobj W n (((Work.DSF1.Cech.E W).map (SimplexCategory.δ i).op).f y) :=
    ((Work.DSF1.Cech.E W).map (SimplexCategory.δ (0 : Fin (n+2))).op).φ
      (Work.DSF1.Cech.insIdx W i₀ n (((Work.DSF1.Cech.E W).map (SimplexCategory.δ i).op).f y))
  have hsq : f1 ≫ fi =
      f2 ≫ (eqToHom (congrArg (Work.DSF1.Cech.Eobj W (n+1)) hZ) ≫ g0) :=
    Subsingleton.elim _ _
  haveI i1 : IsIso (P.map f1.op) := isIso_cof0 U i₀ V hV P (n+1) y
  haveI i0 : IsIso (P.map g0.op) :=
    isIso_cof0 U i₀ V hV P n (((Work.DSF1.Cech.E W).map (SimplexCategory.δ i).op).f y)
  haveI : IsIso (P.map (eqToHom (congrArg (Work.DSF1.Cech.Eobj W (n+1)) hZ) ≫ g0).op) := by
    rw [op_comp, P.map_comp]; infer_instance
  have hkey := Work.DSF1.Cech.deltaSucc_inv_nat P f1 f2 fi
    (eqToHom (congrArg (Work.DSF1.Cech.Eobj W (n+1)) hZ) ≫ g0) hsq
  have hkm : P.map (eqToHom (congrArg (Work.DSF1.Cech.Eobj W (n+1)) hZ) ≫ g0).op
      = P.map g0.op ≫ P.map (eqToHom (congrArg (Work.DSF1.Cech.Eobj W (n+1)) hZ)).op := by
    rw [op_comp, P.map_comp]
  have hEB : inv (P.map (eqToHom (congrArg (Work.DSF1.Cech.Eobj W (n+1)) hZ)).op)
      = eqToHom (congrArg (fun z => P.obj (op (Work.DSF1.Cech.Eobj W (n+1) z))) hZ) := by
    rw [Work.DSF1.Cech.deltaSucc_inv_map_eqToHom_op]
  have core : P.map f2.op ≫ inv (P.map f1.op)
      = eqToHom (congrArg (fun z => P.obj (op (Work.DSF1.Cech.Eobj W (n+1) z))) hZ)
          ≫ inv (P.map g0.op) ≫ P.map fi.op := by
    simp only [hkey, hkm, IsIso.inv_comp, Category.assoc, hEB]
  change Pi.π (fun z => P.obj (op (Work.DSF1.Cech.Eobj W (n+1) z)))
        (((Work.DSF1.Cech.E W).map (SimplexCategory.δ i.succ).op).f
          (Work.DSF1.Cech.insIdx W i₀ (n+1) y)) ≫
      (P.map f2.op ≫ inv (P.map f1.op)) =
    Pi.π (fun z => P.obj (op (Work.DSF1.Cech.Eobj W (n+1) z)))
        (Work.DSF1.Cech.insIdx W i₀ n
          (((Work.DSF1.Cech.E W).map (SimplexCategory.δ i).op).f y)) ≫
      (inv (P.map g0.op) ≫ P.map fi.op)
  rw [← hpi, core, Category.assoc]

end Work.DSMX0bU
