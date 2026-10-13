import Mathlib
import Submission.Work.DSG4a.Present
import Submission.Work.DSG4a.Split

/-!
# DSG4a: finitely presented modules via a free presentation

The local-to-global theorem of this area (`isUnimodular_of_forall_maximal`, in
`Submission.Work.DSG4a.PresentLocalGlobal`) applies to a finitely presented `A`-module `M`
presented as `A^m ⧸ im D` for a matrix `D`.  This file packages that data as a structure
`FreePres A M`, together with the lift of an element of `M` to a vector (a choice, since the
presentation is only a quotient).

The intended source of `FreePres A M` in the application is a finite free model `P` of
`RΓ(X, 𝒪)` over a Noetherian ring `A` (the output of the areas `F1` and `COH`): then
`M = coker (d⁻¹ : P.X (-1) → P.X 0)` and one chooses bases of the finite free modules
`P.X 0`, `P.X (-1)` to write `d⁻¹` as a matrix `D` — see
`Submission.Work.DSG4a.Criterion` for the corresponding `modelModule`/`modelElem`.
-/

namespace Work.DSG4a

universe u v

/-- A **finite free presentation** of an `A`-module `M`: `M` is `A`-linearly isomorphic to
`A^m ⧸ im D` for a matrix `D : Fin m → Fin n → A`.  Equivalently, `M` is finitely
presented, with the presentation made explicit. -/
structure FreePres (A : Type u) [CommRing A] (M : Type v) [AddCommGroup M] [Module A M] where
  /-- number of generators -/
  m : ℕ
  /-- number of relations -/
  n : ℕ
  /-- the matrix of relations -/
  D : Fin m → Fin n → A
  /-- the identification of the module with the quotient presented by `D` -/
  φ : present D ≃ₗ[A] M

namespace FreePres

variable {A : Type u} [CommRing A] {M : Type v} [AddCommGroup M] [Module A M]

/-- A lift of an element of `M` to a vector in `A^m`, through the chosen presentation.  This
is a (noncomputable) choice, since `presentMk` is only surjective. -/
noncomputable def lift (P : FreePres A M) (e : M) : Fin P.m → A :=
  Classical.choose (Submodule.mkQ_surjective (LinearMap.range (matMap P.D))
    (P.φ.symm e))

lemma presentMk_lift (P : FreePres A M) (e : M) :
    presentMk P.D (lift P e) = P.φ.symm e :=
  Classical.choose_spec (Submodule.mkQ_surjective (LinearMap.range (matMap P.D))
    (P.φ.symm e))

lemma φ_presentMk_lift (P : FreePres A M) (e : M) :
    P.φ (presentMk P.D (lift P e)) = e := by
  rw [presentMk_lift, LinearEquiv.apply_symm_apply]

end FreePres

end Work.DSG4a
