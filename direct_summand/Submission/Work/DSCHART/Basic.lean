import Mathlib
import ChallengeDeps
import Submission.Work.DSMap.Mix2

/-!
# DSCHART — the chart cover of `ℙᴺ_A`, basic API

Subproject `DSCHART` (area `CHA` of the MIX2 node set,
`sources/dsmap/direct_summand_mix2.md`, Task 3) supplies the two frozen facts about the
standard affine charts of `ℙᴺ_A = DSMap.PSpace A N`, i.e. the open subsets

  `DSMap.Mix2.chartCover i k = i ⁻¹ᵁ D₊(x_k)`,   `k : ULift (Fin (N+1))`,

for any morphism `i : X ⟶ ℙᴺ_A`:

* `DSMap.Mix2.chartCover_affine_proved` — each chart is affine (when `i` is a closed
  immersion);
* `DSMap.Mix2.chartCover_iSup_proved` — the charts cover `X`.

Both live in `Submission/Work/DSCHART/Main.lean`.  The present file collects the reusable
ingredients, stated for the *unlifted* index `Fin (N+1)` where possible so that they can be
reused by any other consumer of `ℙᴺ_A`.

## The mathematics

`D₊(x_k) ⊆ Proj 𝒜` for `𝒜 = A[x₀,…,x_N]` the standard graded polynomial ring.  Two facts
about it, both from Mathlib:

* the variables generate `A[x₀,…,x_N]` as an algebra over the degree-zero part `𝒜 0`
  (`adjoin_range_X_gradeZero`), so by `Proj.iSup_basicOpen_eq_top'` the sets `D₊(x_k)`
  cover `Proj 𝒜` (`iSup_basicOpen_X_eq_top`);
* `D₊(x_k)` is affine because `x_k` is homogeneous of positive degree
  (`Proj.isAffineOpen_basicOpen`), giving `basicOpen_X_affine`.

Affineness and covering pass to `X` along any *affine* morphism `i` (a closed immersion is
affine, `IsClosedImmersion.instIsAffineHom`), which is exactly the form in which the MIX2
assembly consumes them (`area_M8m`, `area_MX0U`, `area_SEC`).

## What to import

`Submission.Work.DSCHART.Main` (which imports this file) for the deliverables; the umbrella
`Submission.Work.DSCHART.All` for the whole area.
-/

open CategoryTheory AlgebraicGeometry

-- The grading of `MvPolynomial σ A` by total degree is deliberately not a global Mathlib
-- instance; `DSMap`, `DSCOH`, `DSG2` and this area all enable it locally.
-- (`Work.DSCHART.Grading` exports it globally, for files that only need to *state* lemmas.)
attribute [local instance] MvPolynomial.gradedAlgebra

-- The `haveI`s below do register typeclass instances (`IsScalarTower`, `IsClosedImmersion`),
-- so the style linter's suggestion to use `have` does not apply.
set_option linter.style.haveILetI false

namespace Work.DSCHART

universe a

section GradeZero

variable (A : Type a) [CommRing A] (N : ℕ)

/-- `A[x₀,…,x_N]` is generated, as an algebra over the degree-zero part `𝒜 0 = (PGr A N) 0`
of its standard grading, by the variables `x_k`.

This is `MvPolynomial.adjoin_range_X` transported along the scalar tower
`A → 𝒜 0 → A[x₀,…,x_N]` (the constants of `A[x₀,…,x_N]` are exactly `𝒜 0`). -/
theorem adjoin_range_X_gradeZero :
    Algebra.adjoin (↥(DSMap.PGr A N 0))
      (Set.range (MvPolynomial.X : Fin (N + 1) → MvPolynomial (Fin (N + 1)) A)) = ⊤ := by
  haveI : IsScalarTower A (↥(DSMap.PGr A N 0)) (MvPolynomial (Fin (N + 1)) A) :=
    IsScalarTower.of_algebraMap_eq (R := A) (S := DSMap.PGr A N 0)
      (A := MvPolynomial (Fin (N + 1)) A) fun _ => rfl
  refine le_antisymm le_top ?_
  intro p hp
  clear hp
  induction p using MvPolynomial.induction_on with
  | C r =>
    have h2 : MvPolynomial.C r = algebraMap (↥(DSMap.PGr A N 0))
        (MvPolynomial (Fin (N + 1)) A) (algebraMap A (↥(DSMap.PGr A N 0)) r) := by
      rw [← IsScalarTower.algebraMap_apply A (↥(DSMap.PGr A N 0))
        (MvPolynomial (Fin (N + 1)) A) r, MvPolynomial.algebraMap_eq]
    rw [h2]
    exact Subalgebra.algebraMap_mem _ _
  | add p q hp hq => exact add_mem hp hq
  | mul_X p n hp => exact mul_mem hp (Algebra.subset_adjoin (Set.mem_range_self n))

/-- The standard charts `D₊(x_k)`, `k : Fin (N+1)`, of `ℙᴺ_A = Proj A[x₀,…,x_N]` are
affine (`Proj.isAffineOpen_basicOpen`; `x_k` is homogeneous of degree one). -/
theorem basicOpen_X_affine (k : Fin (N + 1)) :
    IsAffineOpen (Proj.basicOpen (DSMap.PGr A N) (MvPolynomial.X k)) :=
  Proj.isAffineOpen_basicOpen (DSMap.PGr A N) (MvPolynomial.X k) (DSMap.Mix2.X_mem_PGr k)
    (by norm_num)

/-- **The standard affine charts cover `ℙᴺ_A`.**  Since the variables generate the whole
polynomial ring over the degree-zero part (`adjoin_range_X_gradeZero`), their basic opens
cover `Proj` (`Proj.iSup_basicOpen_eq_top'`). -/
theorem iSup_basicOpen_X_eq_top :
    ⨆ k : Fin (N + 1), Proj.basicOpen (DSMap.PGr A N) (MvPolynomial.X k) = ⊤ := by
  refine Proj.iSup_basicOpen_eq_top' (DSMap.PGr A N)
    (fun k : Fin (N + 1) => MvPolynomial.X k) (fun k => ⟨1, DSMap.Mix2.X_mem_PGr k⟩) ?_
  simpa using adjoin_range_X_gradeZero A N

/-- Indexed by `ULift (Fin (N+1))` instead of `Fin (N+1)` — the index family used by
`DSMap.Mix2.chartCover`. -/
theorem iSup_basicOpen_X_eq_top_ulift :
    ⨆ k : ULift.{a} (Fin (N + 1)),
      Proj.basicOpen (DSMap.PGr A N) (MvPolynomial.X k.down) = ⊤ := by
  rw [iSup_ulift]
  exact iSup_basicOpen_X_eq_top A N

section Scheme

variable {X : Scheme.{a}}

/-- `DSMap.Mix2.chartCover` is by definition the preimage of the standard chart `D₊(x_k)`:
this `rfl`-lemma lets a caller work with the explicit form without unfolding. -/
theorem chartCover_eq (i : X ⟶ DSMap.PSpace A N) (k : ULift.{a} (Fin (N + 1))) :
    DSMap.Mix2.chartCover i k =
      i ⁻¹ᵁ Proj.basicOpen (DSMap.PGr A N) (MvPolynomial.X k.down) := rfl

/-- A chart of `X ⊆ ℙᴺ_A` is affine as soon as `i : X ⟶ ℙᴺ_A` is an affine morphism: the
preimage of the affine open `D₊(x_k)` under an affine morphism is affine.  In particular this
holds for every closed immersion (`DSMap.Mix2.chartCover_affine_proved`). -/
theorem chartCover_affine_of_isAffineHom (i : X ⟶ DSMap.PSpace A N) [IsAffineHom i]
    (k : ULift.{a} (Fin (N + 1))) : IsAffineOpen (DSMap.Mix2.chartCover i k) :=
  (basicOpen_X_affine A N k.down).preimage i

/-- The chart cover of `X` is the preimage of the standard cover of `ℙᴺ_A`; the `iSup` is
`⊤` for **every** morphism `i : X ⟶ ℙᴺ_A` (no hypothesis is needed, since
`i ⁻¹ᵁ ⊤ = ⊤`). -/
theorem iSup_chartCover_eq_top (i : X ⟶ DSMap.PSpace A N) :
    ⨆ k, DSMap.Mix2.chartCover i k = ⊤ :=
  Scheme.Hom.iSup_preimage_eq_top i (iSup_basicOpen_X_eq_top_ulift A N)

/-- **The packaging used by the MIX2 assembly**: for a closed subscheme `i : X ↪ ℙᴺ_A`, the
charts `X ∩ D₊(x_k)` are a *finite affine open cover* of `X` — i.e. exactly the pair of
hypotheses `hU : ∀ k, IsAffineOpen (chartCover i k)` and
`hcov : ⨆ k, chartCover i k = ⊤` consumed by the frozen nodes `area_MX0U`, `area_MX0bU` and
`area_F1_cech`. -/
theorem chartCover_isAffineCover (i : X ⟶ DSMap.PSpace A N) [IsAffineHom i] :
    (∀ k, IsAffineOpen (DSMap.Mix2.chartCover i k)) ∧
      ⨆ k, DSMap.Mix2.chartCover i k = ⊤ :=
  ⟨fun k => chartCover_affine_of_isAffineHom A N i k, iSup_chartCover_eq_top A N i⟩

end Scheme

end GradeZero

end Work.DSCHART
