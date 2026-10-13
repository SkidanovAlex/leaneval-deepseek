import Mathlib
import Submission.Work.DSCOH.ChartULift

namespace Work.DSCOH

open MvPolynomial CategoryTheory Limits
open Work.DSCOH

-- `chartCech` and `chartCechOf` are plain `def`s; unfolding them at `.reducible` transparency is
-- needed whenever the *types* of their components are identified with `ModuleCat.of A _`.
set_option allowUnsafeReducibility true
attribute [local reducible] chartCech chartCechOf

universe uA w U

/-- The differential of the chart Čech complex, explicitly as `cechDiff`. -/
lemma chartCech_d_aux {A : Type uA} [CommRing A] {n : ℕ}
    {M : Type w} [AddCommGroup M] [Module A M] [Module (Poly A n) M]
    [IsScalarTower A (Poly A n) M]
    (ℳ : ℕ → Submodule A M) [SetLike.GradedSMul (homSub A n) ℳ] (i : ℕ) :
    (chartCech (A := A) (n := n) (M := M) ℳ).d i (i + 1) =
      ModuleCat.ofHom (cechDiff (A := A) (n := n) (M := M) ℳ i) := by
  simp only [chartCech, chartCechOf, CochainComplex.of_d]

/-- In every bi-degree, the differential of `chartCechULift` is the differential of the image of
the chart Čech complex under `ModuleCat.uliftFunctor`.  (Away from the neighbouring diagonal both
sides vanish, which is why the statement is not restricted to `j = i + 1`.) -/
lemma chartCechULift_d_eq_uliftFunctor {A : Type uA} [CommRing A] {n : ℕ}
    {M : Type w} [AddCommGroup M] [Module A M] [Module (Poly A n) M]
    [IsScalarTower A (Poly A n) M]
    {ℳ : ℕ → Submodule A M} [SetLike.GradedSMul (homSub A n) ℳ] (i j : ℕ) :
    (chartCechULift.{uA, w, U} (A := A) (n := n) ℳ).d i j =
      (((ModuleCat.uliftFunctor.{U, max uA w, uA} A).mapHomologicalComplex
        (ComplexShape.up ℕ)).obj (chartCech (A := A) (n := n) (M := M) ℳ)).d i j := by
  by_cases h : (ComplexShape.up ℕ).Rel i j
  · rw [ComplexShape.up_Rel] at h
    rw [← h, chartCechULift_d, Functor.mapHomologicalComplex_obj_d, chartCech_d_aux,
      uliftFunctor_map_ofHom]
  · rw [HomologicalComplex.shape _ i j h, Functor.mapHomologicalComplex_obj_d,
      HomologicalComplex.shape _ i j h]
    simp

/-- **`chartCechULift` really is the `ULift` of the chart Čech complex**: it is isomorphic, as a
complex of `A`-modules in the large universe `max uA (max w U)`, to the image of `chartCech` under
`ModuleCat.uliftFunctor`.  Both complexes have the same objects (by definition) and the same
differentials (by `chartCechULift_d_eq_uliftFunctor`), so the isomorphism is the identity
degreewise. -/
noncomputable def chartCechULiftIsoUliftFunctor {A : Type uA} [CommRing A] {n : ℕ}
    {M : Type w} [AddCommGroup M] [Module A M] [Module (Poly A n) M]
    [IsScalarTower A (Poly A n) M]
    {ℳ : ℕ → Submodule A M} [SetLike.GradedSMul (homSub A n) ℳ] :
    chartCechULift.{uA, w, U} (A := A) (n := n) ℳ ≅
      ((ModuleCat.uliftFunctor.{U, max uA w, uA} A).mapHomologicalComplex
        (ComplexShape.up ℕ)).obj (chartCech (A := A) (n := n) (M := M) ℳ) :=
  HomologicalComplex.Hom.isoOfComponents (fun _ => Iso.refl _) (by
    intro i j _
    simp only [Iso.refl_hom]
    exact (chartCechULift_d_eq_uliftFunctor (A := A) (n := n) (ℳ := ℳ) i j).symm)

theorem chartCechULift_homology_finite {A : Type uA} [CommRing A] {n : ℕ}
    {M : Type w} [AddCommGroup M] [Module A M] [Module (Poly A n) M]
    [IsScalarTower A (Poly A n) M]
    {ℳ : ℕ → Submodule A M} [SetLike.GradedSMul (homSub A n) ℳ] (q : ℕ) :
    Module.Finite A ((chartCechULift.{uA, w, U} (A := A) (n := n) ℳ).homology q) ↔
      Module.Finite A ((chartCech (A := A) (n := n) (M := M) ℳ).homology q) := by
  have hhom : (chartCechULift.{uA, w, U} (A := A) (n := n) ℳ).homology q ≅
      (((ModuleCat.uliftFunctor.{U, max uA w, uA} A).mapHomologicalComplex
        (ComplexShape.up ℕ)).obj (chartCech (A := A) (n := n) (M := M) ℳ)).homology q :=
    (HomologicalComplex.homologyFunctor
      (ModuleCat.{max uA (max w U)} A) (ComplexShape.up ℕ) q).mapIso
        (chartCechULiftIsoUliftFunctor (A := A) (n := n) (ℳ := ℳ))
  have h2 : (((ModuleCat.uliftFunctor.{U, max uA w, uA} A).mapHomologicalComplex
        (ComplexShape.up ℕ)).obj (chartCech (A := A) (n := n) (M := M) ℳ)).homology q ≅
      (ModuleCat.uliftFunctor.{U, max uA w, uA} A).obj
        ((chartCech (A := A) (n := n) (M := M) ℳ).homology q) :=
    uliftFunctor_homologyIso (R := A) (C := chartCech (A := A) (n := n) (M := M) ℳ) q
  rw [Module.Finite.equiv_iff (hhom ≪≫ h2).toLinearEquiv]
  exact moduleFinite_uliftFunctor_obj

end Work.DSCOH
