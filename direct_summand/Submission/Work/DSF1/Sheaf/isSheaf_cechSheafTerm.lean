import Mathlib
import Submission.Work.DSF1.Sheaf.AcycDefs
import Submission.Work.DSF1.Sheaf.CechSheafTerm
import Submission.Work.DSF1.Sheaf.isSheaf_pi
import Submission.Work.DSF1.Sheaf.SSEBasic

/-!
# The sheaf-level Čech terms of a sheaf are sheaves

For a scheme `X`, a family `U : ι → X.Opens` and a sheaf `P` of abelian groups on `X.Opens`,
every degree-`n` term `cechSheafTerm U P n` of the sheaf-level Čech complex (the presheaf
`W ↦ ∏ x, P (⋂ a, U (x a) ⊓ W)`) is again a sheaf.

The proof is coordinatewise: `(cechSheafTerm U P n).obj (op W)` is the product, over the
`n`-simplices `x` of the Čech nerve of `U`, of `P (E.obj x ⊓ W)`, i.e. of the values of the
sheaf `restrL P (E.obj x)` (`W ↦ P (E.obj x ⊓ W)`) at `W`.  A compatible family for the
Čech term gives, by projection onto each coordinate, a compatible family for `restrL P (E.obj x)`;
gluing these coordinates gives a unique gluing.

The main ingredients are `restrL_isSheafUniqueGluing` (the sheaves `restrL P V` are sheaves)
and the component formula `cechComplexFunctor_map_pi` for the maps of Mathlib's Čech complex.
-/

namespace Work.DSF1.Sheaf

open CategoryTheory AlgebraicGeometry Opposite Limits TopologicalSpace
open TopologicalSpace.Opens
open scoped Simplicial

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

universe u

variable {X : AlgebraicGeometry.Scheme.{u}} {ι : Type u}

/-- The `n`-th object of the Čech nerve of the family of opens `U`. -/
noncomputable abbrev cechSimplex (U : ι → X.Opens) (n : ℕ) : FormalCoproduct X.Opens :=
  (FormalCoproduct.mk ι U).cech.obj (op ⦋n⦌)

/-- **Component formula for the restriction maps of the sheaf-level Čech term.**  The `x`-th
component of the restriction `(cechSheafTerm U P n).map f.op` along `f : A' ⟶ A` is the
restriction of `P` along `E.obj x ⊓ A' ≤ E.obj x ⊓ A`. -/
lemma cechSheafTerm_map_π (U : ι → X.Opens) (P : X.Opensᵒᵖ ⥤ AddCommGrpCat.{u}) (n : ℕ)
    {A A' : X.Opens} (f : A' ⟶ A) (x : (cechSimplex U n).I)
    (s : ToType ((cechSheafTerm U P n).obj (op A))) :
    Pi.π (fun y : (cechSimplex U n).I =>
        (restrP P A').obj (op ((cechSimplex U n).obj y))) x
        ((cechSheafTerm U P n).map f.op s) =
      P.map (homOfLE (inf_le_inf_left ((cechSimplex U n).obj x) (leOfHom f))).op
        (Pi.π (fun y : (cechSimplex U n).I =>
          (restrP P A).obj (op ((cechSimplex U n).obj y))) x s) := by
  have key := Work.DSF1.Cech.cechComplexFunctor_map_pi (C := X.Opens)
    (A := AddCommGrpCat.{u}) (U := U) (P := restrP P A) (P' := restrP P A')
    ((restrPFunctor P).map f.op) n x
  have h2 := congrArg (fun m => (ConcreteCategory.hom m) s) key
  rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply] at h2
  exact h2

theorem isSheaf_cechSheafTerm {X : AlgebraicGeometry.Scheme.{u}} {ι : Type u} (U : ι → X.Opens)
    (P : CategoryTheory.Functor (Opposite (X.Opens)) (AddCommGrpCat.{u}))
    (hP : TopCat.Presheaf.IsSheaf P) (n : ℕ) :
    TopCat.Presheaf.IsSheaf (Work.DSF1.Sheaf.cechSheafTerm U P n) := by
  have hPu : TopCat.Presheaf.IsSheafUniqueGluing P :=
    (TopCat.Presheaf.isSheaf_iff_isSheafUniqueGluing P).mp hP
  rw [TopCat.Presheaf.isSheaf_iff_isSheafUniqueGluing]
  intro κ V sf hsf
  classical
  -- Projection of the family onto the `x`-th coordinate is a compatible family for
  -- the sheaf `restrL P (E.obj x)`, hence has a unique gluing.
  have hx : ∀ x : (cechSimplex U n).I,
      ∃! t : ToType ((restrL P ((cechSimplex U n).obj x)).obj (op (iSup V))),
        TopCat.Presheaf.IsGluing (restrL P ((cechSimplex U n).obj x)) V
          (fun i => Pi.π (fun y : (cechSimplex U n).I =>
            (restrP P (V i)).obj (op ((cechSimplex U n).obj y))) x (sf i)) t := by
    intro x
    refine restrL_isSheafUniqueGluing P hPu ((cechSimplex U n).obj x) V _ ?_
    intro i j
    have h := congrArg (fun t => Pi.π (fun y : (cechSimplex U n).I =>
      (restrP P (V i ⊓ V j)).obj (op ((cechSimplex U n).obj y))) x t) (hsf i j)
    rw [cechSheafTerm_map_π (U := U) (P := P) (n := n) (f := infLELeft (V i) (V j)) (x := x)
        (s := sf i),
      cechSheafTerm_map_π (U := U) (P := P) (n := n) (f := infLERight (V i) (V j)) (x := x)
        (s := sf j)] at h
    exact h
  let sx : (x : (cechSimplex U n).I) →
      ToType ((restrL P ((cechSimplex U n).obj x)).obj (op (iSup V))) :=
    fun x => Classical.choose (hx x)
  have hsx : ∀ x, TopCat.Presheaf.IsGluing (restrL P ((cechSimplex U n).obj x)) V
      (fun i => Pi.π (fun y : (cechSimplex U n).I =>
        (restrP P (V i)).obj (op ((cechSimplex U n).obj y))) x (sf i)) (sx x) :=
    fun x => (Classical.choose_spec (hx x)).1
  have huniqx : ∀ x (t : ToType ((restrL P ((cechSimplex U n).obj x)).obj (op (iSup V)))),
      TopCat.Presheaf.IsGluing (restrL P ((cechSimplex U n).obj x)) V
        (fun i => Pi.π (fun y : (cechSimplex U n).I =>
          (restrP P (V i)).obj (op ((cechSimplex U n).obj y))) x (sf i)) t → t = sx x :=
    fun x => (Classical.choose_spec (hx x)).2
  -- Assemble the coordinates into a section of the Čech term over `iSup V`.
  refine ⟨(Limits.Concrete.productEquiv (fun y : (cechSimplex U n).I =>
    (restrP P (iSup V)).obj (op ((cechSimplex U n).obj y)))).symm (fun x => sx x), ?_, ?_⟩
  · intro i
    apply (Limits.Concrete.productEquiv (fun y : (cechSimplex U n).I =>
      (restrP P (V i)).obj (op ((cechSimplex U n).obj y)))).injective
    funext x
    rw [Limits.Concrete.productEquiv_apply_apply, Limits.Concrete.productEquiv_apply_apply]
    rw [cechSheafTerm_map_π (U := U) (P := P) (n := n) (f := Opens.leSupr V i) (x := x)]
    rw [Limits.Concrete.productEquiv_symm_apply_π]
    exact hsx x i
  · intro t ht
    apply (Limits.Concrete.productEquiv (fun y : (cechSimplex U n).I =>
      (restrP P (iSup V)).obj (op ((cechSimplex U n).obj y)))).injective
    funext x
    rw [Limits.Concrete.productEquiv_apply_apply, Limits.Concrete.productEquiv_apply_apply]
    rw [Limits.Concrete.productEquiv_symm_apply_π]
    apply huniqx x
    intro i
    have h := congrArg (fun u => Pi.π (fun y : (cechSimplex U n).I =>
      (restrP P (V i)).obj (op ((cechSimplex U n).obj y))) x u) (ht i)
    rw [cechSheafTerm_map_π (U := U) (P := P) (n := n) (f := Opens.leSupr V i) (x := x)] at h
    exact h

end Work.DSF1.Sheaf
