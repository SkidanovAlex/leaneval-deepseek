import Mathlib
import Submission.Work.DSMap.Map

/-!
# DSG2: Chow's lemma over a Noetherian base — vocabulary

Definitions used by the Chow construction and shared with the delta lemmas delegated
for this area (`Submission/Work/DSG2/`).

* `Work.DSG2.sectionAlgebra f U : A →+* Γ(X, U)` — the `A`-algebra structure on the sections
  of an open of a scheme over `Spec A`, induced by `f`.
* `Work.DSG2.chartOpen A n i` — the `i`-th standard affine chart `D_+(xᵢ)` of `ℙ^n_A`,
  where `ℙ^n_A = DSMap.PSpace A n = Proj A[x₀,…,xₙ]`.
* `Work.DSG2.chartRing A n i` — its coordinate ring.
* `Work.DSG2.segreN a b` — the target dimension of the Segre embedding
  `ℙ^a_A ×_A ℙ^b_A ↪ ℙ^{segreN a b}_A`.

The conventions match the frozen file `Submission/Work/DSMap/Map.lean`: `ℙ^n_A` is
`PSpace A n = Proj (MvPolynomial.homogeneousSubmodule (Fin (n+1)) A)`, and `IsProjOver A f`
means that `f` is the composite of a closed immersion into some `ℙ^n_A` with the
structure morphism.

-/

open CategoryTheory AlgebraicGeometry Limits

universe u v

namespace Work.DSG2

open LeanEval.AlgebraicGeometry.DirectSummand

section SectionAlgebra

variable {A : Type u} [CommRing A] {X : Scheme.{u}}

/-- The `A`-algebra map `A → Γ(X, U)` induced by a morphism `f : X ⟶ Spec A`, obtained by
composing the inverse of the canonical isomorphism `Γ(Spec A) ≅ A` with the restriction map
`Γ(Spec A) → Γ(U)`. -/
noncomputable def sectionAlgebra (f : X ⟶ Spec (.of A)) (U : X.Opens) : A →+* Γ(X, U) :=
  (f.appLE ⊤ U le_top).hom.comp (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom

end SectionAlgebra

section Chart

attribute [local instance] MvPolynomial.gradedAlgebra

/-- The `i`-th standard affine chart `D_+(xᵢ) ⊆ ℙ^n_A`. -/
noncomputable def chartOpen (A : Type u) [CommRing A] (n : ℕ) (i : Fin (n + 1)) :
    (DSMap.PSpace A n).Opens :=
  ProjectiveSpectrum.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) A)
    (MvPolynomial.X i)

/-- The coordinate ring of the `i`-th affine chart of `ℙ^n_A`, i.e. the degree-zero part of the
localization of `A[x₀,…,xₙ]` at the powers of `xᵢ`. -/
noncomputable def chartRing (A : Type u) [CommRing A] (n : ℕ) (i : Fin (n + 1)) : Type u :=
  HomogeneousLocalization.Away (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) A)
    (MvPolynomial.X i)

/-- `chartRing A n i` is a commutative ring (the instance is recorded here so that the definitions
above can be used without re-synthesizing the grading of `MvPolynomial.homogeneousSubmodule`). -/
noncomputable instance (A : Type u) [CommRing A] (n : ℕ) (i : Fin (n + 1)) :
    CommRing (chartRing A n i) :=
  inferInstanceAs (CommRing (HomogeneousLocalization.Away
    (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) A) (MvPolynomial.X i)))

end Chart

/-- The target index of the Segre embedding `ℙ^a_A ×_A ℙ^b_A ↪ ℙ^N_A`. -/
def segreN (a b : ℕ) : ℕ := (a + 1) * (b + 1) - 1

end Work.DSG2
