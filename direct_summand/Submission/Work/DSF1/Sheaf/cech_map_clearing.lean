import Mathlib
import Submission.Work.DSF1.Sheaf.CechStruct
import Submission.Work.DSF1.Cech.CechSetup
import Submission.Work.DSF1.Cech.CechQo
import Submission.Work.DSF1.Sheaf.pi_map_clearing_surj
import Submission.Work.DSF1.Sheaf.pi_map_clearing_ker

/-!
# Clearing denominators for the map `Č(P) ⟶ Č(W ↦ P (W ⊓ V))`

Let `X` be a scheme, `U : ι → X.Opens` a finite family of opens, `V` an open and
`h : Γ(X, ⊤)` a global section.  Writing `P = structPresheaf X` for the structure sheaf
viewed as a presheaf of `Γ(X, ⊤)`-modules and `Q = Qo P V` for the presheaf
`W ↦ P (W ⊓ V)`, the comparison map `ηO : P ⟶ Q` induces a map of Čech complexes

`Č(ηO) : Č(P) ⟶ Č(Q)`.

The main result of this file, `cech_map_clearing`, says that this map clears denominators
at the level of the complexes: if *componentwise* (that is, on each open `Eobj U n x`
of the Čech nerve) `ηO` exhibits `P (Eobj U n x ⊓ V)` as the localization of
`P (Eobj U n x)` away from `h`, then every element of a term of `Č(Q)` is, up to a power
of `h`, in the image of `Č(ηO)`, and every element of a term of `Č(P)` killed by `Č(ηO)`
is killed by a power of `h`.

The Čech complex is a product over the simplices `x` of the nerve, so both statements
are obtained by assembling the componentwise hypotheses over a finite product, using a
single (finite) power of `h` for all components at once.
-/

set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 1600000
set_option linter.style.haveILetI false

open CategoryTheory AlgebraicGeometry Opposite Limits
open scoped Simplicial BigOperators

namespace Work.DSF1.Sheaf

/-- **Component formula for the map of Čech complexes induced by `ηO`.**  In degree `n`
the `x`-component of the map `Č(ηO)` is the map induced by `ηO` on the section module
over `Eobj U n x`. -/
lemma cechMap_component {X : AlgebraicGeometry.Scheme.{0}} {ι : Type} [Fintype ι]
    (U : ι → X.Opens) (V : X.Opens) (n : ℕ)
    (x : ((Work.DSF1.Cech.E U).obj (Opposite.op (SimplexCategory.mk n)) |>.I)) :
    ((CategoryTheory.cechComplexFunctor U).map
        (Work.DSF1.Cech.etaO (Work.DSF1.Sheaf.structPresheaf X) V)).f n ≫
        CategoryTheory.Limits.Pi.π
          (fun y => (Work.DSF1.Cech.Qo (Work.DSF1.Sheaf.structPresheaf X) V).obj
            (Opposite.op (Work.DSF1.Cech.Eobj U n y))) x
      = CategoryTheory.Limits.Pi.π
          (fun y => (Work.DSF1.Sheaf.structPresheaf X).obj
            (Opposite.op (Work.DSF1.Cech.Eobj U n y))) x ≫
        (Work.DSF1.Cech.etaO (Work.DSF1.Sheaf.structPresheaf X) V).app
          (Opposite.op (Work.DSF1.Cech.Eobj U n x)) := by
  simp only [CategoryTheory.cechComplexFunctor,
    CategoryTheory.Limits.FormalCoproduct.cochainComplexFunctor, Functor.comp_map,
    AlgebraicTopology.alternatingCofaceMapComplex_map,
    AlgebraicTopology.AlternatingCofaceMapComplex.map]
  rw [CategoryTheory.Limits.FormalCoproduct.cosimplicialObjectFunctor_map_app]
  exact CategoryTheory.Limits.Pi.map_π _ x

/-- The target lemma `Work.DSF1.Sheaf.cech_map_clearing`. -/
theorem cech_map_clearing {X : AlgebraicGeometry.Scheme} {ι : Type} [Fintype ι]
    (U : ι → X.Opens) (V : X.Opens) (h : ↥(X.presheaf.obj (Opposite.op ⊤)))
    (hsurj : ∀ (n : ℕ) (x : (Work.DSF1.Cech.E U).obj (Opposite.op (SimplexCategory.mk n)) |>.I),
      ∀ z : (Work.DSF1.Sheaf.structPresheaf X).obj
          (Opposite.op (Work.DSF1.Cech.Eobj U n x ⊓ V)),
        ∃ (k : ℕ) (t : (Work.DSF1.Sheaf.structPresheaf X).obj
            (Opposite.op (Work.DSF1.Cech.Eobj U n x))),
          ((Work.DSF1.Sheaf.structPresheaf X).map (CategoryTheory.homOfLE (inf_le_left :
            Work.DSF1.Cech.Eobj U n x ⊓ V ≤ Work.DSF1.Cech.Eobj U n x)).op).hom t = h ^ k • z)
    (hker : ∀ (n : ℕ) (x : (Work.DSF1.Cech.E U).obj (Opposite.op (SimplexCategory.mk n)) |>.I)
        (t : (Work.DSF1.Sheaf.structPresheaf X).obj (Opposite.op (Work.DSF1.Cech.Eobj U n x))),
      ((Work.DSF1.Sheaf.structPresheaf X).map (CategoryTheory.homOfLE (inf_le_left :
        Work.DSF1.Cech.Eobj U n x ⊓ V ≤ Work.DSF1.Cech.Eobj U n x)).op).hom t = 0 →
        ∃ k : ℕ, h ^ k • t = 0) :
    (∀ (n : ℕ) (z : ((CategoryTheory.cechComplexFunctor U).obj
        (Work.DSF1.Cech.Qo (Work.DSF1.Sheaf.structPresheaf X) V)).X n),
      ∃ (k : ℕ) (t : ((CategoryTheory.cechComplexFunctor U).obj
          (Work.DSF1.Sheaf.structPresheaf X)).X n),
        (((CategoryTheory.cechComplexFunctor U).map
          (Work.DSF1.Cech.etaO (Work.DSF1.Sheaf.structPresheaf X) V)).f n).hom t = h ^ k • z) ∧
    (∀ (n : ℕ) (t : ((CategoryTheory.cechComplexFunctor U).obj
        (Work.DSF1.Sheaf.structPresheaf X)).X n),
      (((CategoryTheory.cechComplexFunctor U).map
        (Work.DSF1.Cech.etaO (Work.DSF1.Sheaf.structPresheaf X) V)).f n).hom t = 0 →
        ∃ k : ℕ, h ^ k • t = 0) := by
  classical
  -- In each degree the comparison map is the product of its components.
  have key : ∀ (n : ℕ),
      ((CategoryTheory.cechComplexFunctor U).map
        (Work.DSF1.Cech.etaO (Work.DSF1.Sheaf.structPresheaf X) V)).f n =
      CategoryTheory.Limits.Pi.map
        (fun x : ((Work.DSF1.Cech.E U).obj (Opposite.op (SimplexCategory.mk n)) |>.I) =>
          (Work.DSF1.Cech.etaO (Work.DSF1.Sheaf.structPresheaf X) V).app
            (Opposite.op (Work.DSF1.Cech.Eobj U n x))) := by
    intro n
    apply CategoryTheory.Limits.Pi.hom_ext
    intro x
    have h2 : CategoryTheory.Limits.Pi.map
        (fun x : ((Work.DSF1.Cech.E U).obj (Opposite.op (SimplexCategory.mk n)) |>.I) =>
          (Work.DSF1.Cech.etaO (Work.DSF1.Sheaf.structPresheaf X) V).app
            (Opposite.op (Work.DSF1.Cech.Eobj U n x))) ≫
        CategoryTheory.Limits.Pi.π
          (fun y => (Work.DSF1.Cech.Qo (Work.DSF1.Sheaf.structPresheaf X) V).obj
            (Opposite.op (Work.DSF1.Cech.Eobj U n y))) x
        = CategoryTheory.Limits.Pi.π
            (fun y => (Work.DSF1.Sheaf.structPresheaf X).obj
              (Opposite.op (Work.DSF1.Cech.Eobj U n y))) x ≫
          (Work.DSF1.Cech.etaO (Work.DSF1.Sheaf.structPresheaf X) V).app
            (Opposite.op (Work.DSF1.Cech.Eobj U n x)) := by
      exact CategoryTheory.Limits.Pi.map_π _ x
    exact (cechMap_component U V n x).trans h2.symm
  constructor
  · intro n z
    haveI : Fintype ((Work.DSF1.Cech.E U).obj (Opposite.op (SimplexCategory.mk n)) |>.I) :=
      inferInstanceAs (Fintype (Fin (n + 1) → ι))
    obtain ⟨k, t, ht⟩ := pi_map_clearing_surj
      (fun x => (Work.DSF1.Sheaf.structPresheaf X).obj (Opposite.op (Work.DSF1.Cech.Eobj U n x)))
      (fun x => (Work.DSF1.Cech.Qo (Work.DSF1.Sheaf.structPresheaf X) V).obj
        (Opposite.op (Work.DSF1.Cech.Eobj U n x)))
      (fun x => (Work.DSF1.Cech.etaO (Work.DSF1.Sheaf.structPresheaf X) V).app
        (Opposite.op (Work.DSF1.Cech.Eobj U n x)))
      h (fun x zx => hsurj n x zx) z
    refine ⟨k, t, ?_⟩
    exact (congrArg (fun (m : ((CategoryTheory.cechComplexFunctor U).obj
      (Work.DSF1.Sheaf.structPresheaf X)).X n ⟶ ((CategoryTheory.cechComplexFunctor U).obj
      (Work.DSF1.Cech.Qo (Work.DSF1.Sheaf.structPresheaf X) V)).X n) => m.hom t) (key n)).trans ht
  · intro n t ht
    haveI : Fintype ((Work.DSF1.Cech.E U).obj (Opposite.op (SimplexCategory.mk n)) |>.I) :=
      inferInstanceAs (Fintype (Fin (n + 1) → ι))
    exact pi_map_clearing_ker
      (fun x => (Work.DSF1.Sheaf.structPresheaf X).obj (Opposite.op (Work.DSF1.Cech.Eobj U n x)))
      (fun x => (Work.DSF1.Cech.Qo (Work.DSF1.Sheaf.structPresheaf X) V).obj
        (Opposite.op (Work.DSF1.Cech.Eobj U n x)))
      (fun x => (Work.DSF1.Cech.etaO (Work.DSF1.Sheaf.structPresheaf X) V).app
        (Opposite.op (Work.DSF1.Cech.Eobj U n x)))
      h (fun x tx => hker n x tx) t
      ((congrArg (fun (m : ((CategoryTheory.cechComplexFunctor U).obj
        (Work.DSF1.Sheaf.structPresheaf X)).X n ⟶ ((CategoryTheory.cechComplexFunctor U).obj
        (Work.DSF1.Cech.Qo (Work.DSF1.Sheaf.structPresheaf X) V)).X n) => m.hom t) (key n)).symm.trans ht)

end Work.DSF1.Sheaf
