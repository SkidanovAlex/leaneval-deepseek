import Mathlib
import Submission.Work.Serre.mvLadder
import Submission.Work.Serre.bijAssembly
import Submission.Work.StemsB.AToolsR
import Submission.Work.Thom.CapGlue.isIso_relComplexMap_homeomorph
import Submission.Work.RatHurewicz.discPairFibreRestriction_of_fibreVisible

open CategoryTheory

namespace Work.RatHurewicz

/-- **Bijectivity of the mixed cup product is invariant under a homeomorphism of pairs.**

If, for a fixed relative class `z ∈ H^n(Y,B;ℚ)`, the multiplication map
`y ↦ y ⌣ z : H^m(Y;ℚ) → H^{m+n}(Y,B;ℚ)` (the mixed cup product of an absolute with a relative
class) is a bijection, then so is the corresponding multiplication map on `X` by the pullback of `z`
along a homeomorphism of pairs `e : (X,A) ≅ (Y,B)`.

The proof is naturality of the mixed cup product (`Work.StemsB.mixedCupC_pairNaturalR`): the map for
`(X,A)` is the conjugate of the map for `(Y,B)` by the pullback isomorphisms `H^*(X) ≅ H^*(Y)`
(comparison with `CohMap` of `e.symm`) and `H^*(Y,B) ≅ H^*(X,A)`
(`Work.Thom.bijective_relCohMap_of_homeomorphA`). -/
theorem bijective_mixedCup_of_homeo {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (e : X ≃ₜ Y) (A : Set X) (B : Set Y) (he : ∀ x, x ∈ A ↔ e x ∈ B)
    (m n : ℕ) (z : Work.Thom.RelCoh ℚ n Y B)
    (hb : Function.Bijective (fun y : Work.Thom.Coh ℚ m Y =>
      (Work.Thom.mixedCupC ℚ B m n) y z)) :
    Function.Bijective (fun x : Work.Thom.Coh ℚ m X =>
      (Work.Thom.mixedCupC ℚ A m n) x
        ((Work.Thom.relCohMap (e : C(X, Y)) A B (fun x hx => (he x).mp hx) ℚ n).hom z)) := by
  -- `e` carries `A` into `B`.
  have hf : ∀ x ∈ A, (e : C(X, Y)) x ∈ B := fun x hx => (he x).mp hx
  -- The two composites of `e` with its inverse are the identities.
  have hcX : (e.symm : C(Y, X)).comp (e : C(X, Y)) = ContinuousMap.id X :=
    ContinuousMap.ext fun x => e.symm_apply_apply x
  have hcY : (e : C(X, Y)).comp (e.symm : C(Y, X)) = ContinuousMap.id Y :=
    ContinuousMap.ext fun y => e.apply_symm_apply y
  -- Hence the pullbacks on absolute cohomology are mutually inverse.
  have hcomp1 : Work.Thom.CohMap (e.symm : C(Y, X)) ℚ m ≫ Work.Thom.CohMap (e : C(X, Y)) ℚ m
      = 𝟙 (Work.Thom.Coh ℚ m X) := by
    rw [← Work.Thom.CohMap_comp (e : C(X, Y)) (e.symm : C(Y, X)) ℚ m, hcX, Work.Thom.CohMap_id]
  have hcomp2 : Work.Thom.CohMap (e : C(X, Y)) ℚ m ≫ Work.Thom.CohMap (e.symm : C(Y, X)) ℚ m
      = 𝟙 (Work.Thom.Coh ℚ m Y) := by
    rw [← Work.Thom.CohMap_comp (e.symm : C(Y, X)) (e : C(X, Y)) ℚ m, hcY, Work.Thom.CohMap_id]
  have hl1 : (ModuleCat.Hom.hom (Work.Thom.CohMap (e : C(X, Y)) ℚ m)).comp
      (ModuleCat.Hom.hom (Work.Thom.CohMap (e.symm : C(Y, X)) ℚ m)) = LinearMap.id := by
    have := congrArg ModuleCat.Hom.hom hcomp1
    simpa [ModuleCat.hom_comp, ModuleCat.hom_id] using this
  have hl2 : (ModuleCat.Hom.hom (Work.Thom.CohMap (e.symm : C(Y, X)) ℚ m)).comp
      (ModuleCat.Hom.hom (Work.Thom.CohMap (e : C(X, Y)) ℚ m)) = LinearMap.id := by
    have := congrArg ModuleCat.Hom.hom hcomp2
    simpa [ModuleCat.hom_comp, ModuleCat.hom_id] using this
  -- The pullback along `e.symm` is a bijection on `H^m(X;ℚ)`.
  have hΨbij : Function.Bijective
      (ModuleCat.Hom.hom (Work.Thom.CohMap (e.symm : C(Y, X)) ℚ m)) := by
    constructor
    · intro a b hab
      have ha := LinearMap.congr_fun hl1 a
      have hbb := LinearMap.congr_fun hl1 b
      simp only [LinearMap.comp_apply, LinearMap.id_apply] at ha hbb
      rw [hab] at ha
      exact ha.symm.trans hbb
    · intro b
      exact ⟨(ModuleCat.Hom.hom (Work.Thom.CohMap (e : C(X, Y)) ℚ m)) b,
        LinearMap.congr_fun hl2 b⟩
  -- The pullback along `e` is a bijection on `H^{m+n}(X,A;ℚ)`.
  have hφbij : Function.Bijective
      (ModuleCat.Hom.hom (Work.Thom.relCohMap (e : C(X, Y)) A B hf ℚ (m + n))) :=
    Work.Thom.bijective_relCohMap_of_homeomorphA A B e he ℚ (m + n)
  -- Naturality of the mixed cup product identifies the two multiplication maps.
  have hkey : ∀ x : Work.Thom.Coh ℚ m X,
      (Work.Thom.mixedCupC ℚ A m n) x
          ((Work.Thom.relCohMap (e : C(X, Y)) A B hf ℚ n).hom z)
        = (Work.Thom.relCohMap (e : C(X, Y)) A B hf ℚ (m + n)).hom
            ((Work.Thom.mixedCupC ℚ B m n)
              ((Work.Thom.CohMap (e.symm : C(Y, X)) ℚ m).hom x) z) := by
    intro x
    rw [Work.StemsB.mixedCupC_pairNaturalR (R := ℚ) (e : C(X, Y)) A B hf m n
      ((Work.Thom.CohMap (e.symm : C(Y, X)) ℚ m).hom x) z]
    have hx : (Work.Thom.CohMap (e : C(X, Y)) ℚ m).hom
        ((Work.Thom.CohMap (e.symm : C(Y, X)) ℚ m).hom x) = x := LinearMap.congr_fun hl1 x
    rw [hx]
  -- The map for `(X,A)` is thus a composite of bijections.
  rw [show (fun x : Work.Thom.Coh ℚ m X =>
        (Work.Thom.mixedCupC ℚ A m n) x
          ((Work.Thom.relCohMap (e : C(X, Y)) A B (fun x hx => (he x).mp hx) ℚ n).hom z))
      = (fun x : Work.Thom.Coh ℚ m X =>
          (Work.Thom.relCohMap (e : C(X, Y)) A B hf ℚ (m + n)).hom
            ((Work.Thom.mixedCupC ℚ B m n)
              ((Work.Thom.CohMap (e.symm : C(Y, X)) ℚ m).hom x) z))
      from funext hkey]
  exact Function.Bijective.comp hφbij (Function.Bijective.comp hb hΨbij)

end Work.RatHurewicz
