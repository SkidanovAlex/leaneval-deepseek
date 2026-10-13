import Submission.Work.DSCHART.Basic

/-!
# DSCHART — deliverable: the chart cover of `ℙᴺ_A` (area `CHA` of MIX2)

This module contains the deliverable of the subproject `DSCHART`:

* `DSMap.Mix2.chartCover_affine_proved`, whose type is *definitionally identical* to the type
  of the frozen `DSMap.Mix2.chartCover_affine` of `Submission/Work/DSMap/Mix2.lean`;
* `DSMap.Mix2.chartCover_iSup_proved`, likewise for the frozen `DSMap.Mix2.chartCover_iSup`.

Both identities are machine-checked by the `example`s at the end of this file (with the
universe level made explicit — without it `type_of%` introduces two distinct level
metavariables and `rfl` is not even applicable).

The mathematics (node `CHA` of the MIX2 dispatch list,
`sources/dsmap/direct_summand_mix2.md` §Task 3) is:

* for `k : ULift (Fin (N+1))`, `chartCover i k = i ⁻¹ᵁ D₊(x_k) ⊆ X` is affine, because
  `i` is a closed immersion — hence an affine morphism — and `D₊(x_k) ⊆ ℙᴺ_A` is an affine
  open (`Work.DSCHART.basicOpen_X_affine`);
* `⨆ k, chartCover i k = ⊤`, because the standard charts cover `ℙᴺ_A`
  (`Work.DSCHART.iSup_basicOpen_X_eq_top`) and preimages commute with `iSup`.

These two are exactly the `hU`/`hcov` inputs of the frozen nodes `area_MX0U`, `area_MX0bU`
and `area_M6G`.  The mathematical content of the present file is a one-line copy of
`Work.DSCHART.chartCover_affine_of_isAffineHom` and `Work.DSCHART.iSup_chartCover_eq_top`,
whose proofs live in `Submission/Work/DSCHART/Basic.lean`; they are spelled out here so that a
reader can see the whole argument without leaving the file.

`Submission.Work.DSMap.Mix2` is imported only for the type-identity checks: the two proofs
below use nothing from the frozen file except the definitions `PSpace`, `PGr`, `chartCover`
and the proved lemma `DSMap.Mix2.X_mem_PGr`.
-/

open CategoryTheory AlgebraicGeometry

-- the standard grading of the polynomial ring, as in `DSMap`/`Mix2`.
attribute [local instance] MvPolynomial.gradedAlgebra

-- `haveI` below registers a typeclass instance (`IsClosedImmersion`); the style linter's
-- suggestion to use `have` does not apply.
set_option linter.style.haveILetI false

namespace DSMap.Mix2
open DSMap DSMap.Mix

universe a

/-- **CHA** (first half, DSCHART deliverable): each chart `X ∩ D₊(x_k)` of a closed
subscheme `X ⊆ ℙᴺ_A` is affine.  Same type as the frozen `DSMap.Mix2.chartCover_affine`. -/
theorem chartCover_affine_proved {A : Type a} [CommRing A] {X : Scheme.{a}} {N : ℕ}
    (i : X ⟶ PSpace A N) (hi : IsClosedImmersion i) (k) : IsAffineOpen (chartCover i k) := by
  haveI : IsClosedImmersion i := hi
  exact (Proj.isAffineOpen_basicOpen (PGr A N) (MvPolynomial.X k.down)
    (X_mem_PGr k.down) (by norm_num)).preimage i

/-- **CHA** (second half, DSCHART deliverable): the charts `X ∩ D₊(x_k)`, `k : Fin (N+1)`,
cover `X`.  Same type as the frozen `DSMap.Mix2.chartCover_iSup`. -/
theorem chartCover_iSup_proved {A : Type a} [CommRing A] {X : Scheme.{a}} {N : ℕ}
    (i : X ⟶ PSpace A N) : ⨆ k, chartCover i k = ⊤ := by
  apply Scheme.Hom.iSup_preimage_eq_top i
  rw [iSup_ulift]
  refine Proj.iSup_basicOpen_eq_top' (PGr A N) (fun k : Fin (N + 1) => MvPolynomial.X k)
    (fun k => ⟨1, X_mem_PGr k⟩) ?_
  simpa using Work.DSCHART.adjoin_range_X_gradeZero A N

/-- The type of `chartCover_affine_proved` is definitionally identical to the type of the
frozen `chartCover_affine`. -/
example : type_of% (@chartCover_affine_proved.{a}) = type_of% (@chartCover_affine.{a}) := rfl

/-- The type of `chartCover_iSup_proved` is definitionally identical to the type of the
frozen `chartCover_iSup`. -/
example : type_of% (@chartCover_iSup_proved.{a}) = type_of% (@chartCover_iSup.{a}) := rfl

end DSMap.Mix2

namespace Work.DSCHART

universe a

/-- Area-namespace alias of the first deliverable. -/
theorem chartCover_affine_proved {A : Type a} [CommRing A] {X : Scheme.{a}} {N : ℕ}
    (i : X ⟶ DSMap.PSpace A N) (hi : IsClosedImmersion i) (k) :
    IsAffineOpen (DSMap.Mix2.chartCover i k) :=
  DSMap.Mix2.chartCover_affine_proved i hi k

/-- Area-namespace alias of the second deliverable. -/
theorem chartCover_iSup_proved {A : Type a} [CommRing A] {X : Scheme.{a}} {N : ℕ}
    (i : X ⟶ DSMap.PSpace A N) : ⨆ k, DSMap.Mix2.chartCover i k = ⊤ :=
  DSMap.Mix2.chartCover_iSup_proved i

end Work.DSCHART
