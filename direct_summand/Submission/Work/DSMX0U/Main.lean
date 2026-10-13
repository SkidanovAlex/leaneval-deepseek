import Submission.Work.DSMX0U.Coherence
import Submission.Work.DSMX0U.cechZ_homology_finite
import Submission.Work.DSMap.Mix2

/-!
# DSMX0U — the deliverable: `DSMap.Mix2.area_MX0U` for every finite affine cover

This file contains `Work.DSMX0U.area_MX0U_proved`, a proof of the statement of the frozen node
`DSMap.Mix2.area_MX0U` (the `MX0U` node of the MIX2 design), namely: for every Noetherian ring
`A`, every projective `X` over `A` with structure map `f`, and every finite affine cover `U` of
`X`, there is a bounded-above complex `P` of finitely generated free `A`-modules together with a
coaugmentation `ε : A ⟶ P⁰` and a quasi-isomorphism `P ⟶ cechZ A X f U` carrying `ε` to the Čech
coaugmentation — i.e. `DSMap.Mix2.IsFinFreeModelU A X f U P ε`.

The type of `area_MX0U_proved` is *definitionally identical* to the frozen `DSMap.Mix2.area_MX0U`;
this is checked at the bottom of the file by

    `example : @Work.DSMX0U.area_MX0U_proved = @DSMap.Mix2.area_MX0U := rfl`.

## What is proved here, and what is used as an input

The mathematical content of `area_MX0U` beyond the areas `F1` (the Čech complex computes
`RΓ(X, 𝒪)`) and `COH` (finiteness and boundedness of the cohomology) is the pseudo-coherence
statement of `Work.DSMX0U.exists_finFreeModel_of_fgCoh`, which is proved here *unconditionally*
(see `DSMX0U/Basic.lean`, `DSMX0U/Engine.lean` and the files it imports).

The coherence input itself is the content of the frozen areas `DSMap.area_F1_cech` and
`DSMap.area_COH`; it is transferred to the Čech complex by
`Work.DSMX0U.cechZ_homology_finite` (file `Submission/Work/DSMX0U/cechZ_homology_finite.lean`).
Consequently `area_MX0U_proved` depends on those two frozen `sorry`ed interfaces — as the design
table of `direct_summand_mix2.md` prescribes for the node `MX0U` ("depends on F1, COH") — while
the *proof* of `area_MX0U_of_coherence` and of everything under it is sorry-free and axiom-clean.
-/

namespace Work.DSMX0U

open CategoryTheory AlgebraicGeometry Limits

set_option linter.unusedVariables false

universe a

/-- **The area theorem**: the statement of the frozen node `DSMap.Mix2.area_MX0U`. -/
theorem area_MX0U_proved (A : Type a) [CommRing A] [IsNoetherianRing A] (X : Scheme.{a})
    (f : X ⟶ Spec (.of A)) [IsProper f] (hp : DSMap.IsProjOver A f) {ι : Type a} [Finite ι]
    (U : ι → X.Opens) (hU : ∀ i, IsAffineOpen (U i)) (hcov : ⨆ i, U i = ⊤) :
    ∃ (P : CochainComplex (ModuleCat.{a} A) ℤ) (ε : ModuleCat.of A A ⟶ P.X 0),
      DSMap.Mix2.IsFinFreeModelU A X f U P ε :=
  area_MX0U_of_coherence A X f hp U hU hcov (cechZ_homology_finite (A := A) f hp U hU hcov)

/-- The type of `area_MX0U_proved` is definitionally the type of the frozen `DSMap.Mix2.area_MX0U`
(comparison of the constants, which forces the types to be definitionally equal). -/
example : @area_MX0U_proved = @DSMap.Mix2.area_MX0U := rfl

end Work.DSMX0U
