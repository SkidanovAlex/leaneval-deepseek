import Mathlib
import Submission.Subspace.Stage2
import Submission.Subspace.RankDescent
import Submission.Subspace.NumberField
import Submission.Subspace.HeightLink
import Submission.Commons.LinearAlgebra.GeneralPosition.exists_infinite_generalPosition_subset
import Submission.Commons.NumberTheory.Height.NumberField.exponent_vector_extraction_uniform

/-!
# Stage 2 assembly

Discharges the single implication `Stage2Output`: if the affine subspace theorem fails for
some `ε > 0`, then there is an exponent vector `c` with `∑ cᵢ < 0` and an infinite
general-position family of small integer points on which every linear form is bounded by
`‖x‖^{cᵢ}`.

Ingredients:
* `smallNonzeroRat_infinite` + `not_coverable_smallNonzeroRat` (Stage 2),
* `Commons.LinearAlgebra.GeneralPosition.exists_infinite_generalPosition_subset`,
* `genPosInt_transfer` (Stage 2),
* `Commons.NumberTheory.Height.NumberField.exponent_vector_extraction_uniform`
  (with the place identity `place_val_eq`).

Together with `subspaces_of_rankDescent` this reduces the challenge to the single statement
`RankDescent`.
-/

open scoped BigOperators

namespace Submission.Subspace

variable {σ : Type*} [Fintype σ]

/-- **Stage 2.**  Failure of the affine subspace theorem for `ε` yields an infinite
general-position family of small points with a common exponent vector of negative sum. -/
theorem stage2Output (hσ : 2 ≤ Fintype.card σ) (L : σ → σ → ℂ)
    (alg : ∀ i j, IsAlgebraic ℚ (L i j)) (ind : LinearIndependent ℂ L) :
    Stage2Output (σ := σ) L := by
  classical
  intro ε hε hnc
  have hcover : ¬ ∃ T : Set (Submodule ℚ (σ → ℚ)), T.Finite ∧ (∀ W ∈ T, W ≠ ⊤) ∧
      ∀ v ∈ SmallNonzeroRat L ε, ∃ W ∈ T, v ∈ W :=
    not_coverable_smallNonzeroRat L ε ind hnc
  have hinf : (SmallNonzeroRat L ε).Infinite := smallNonzeroRat_infinite hσ L ε ind hnc
  obtain ⟨Y, hYsub, hYinf, hYgp⟩ :=
    Commons.LinearAlgebra.GeneralPosition.exists_infinite_generalPosition_subset
      (SmallNonzeroRat L ε) hinf hcover
  have hfr : Module.finrank ℚ (σ → ℚ) = Fintype.card σ :=
    Module.finrank_fintype_fun_eq_card (R := ℚ) (η := σ)
  have hYgp' : ∀ T : Finset (σ → ℚ), (↑T : Set (σ → ℚ)) ⊆ Y → T.card ≤ Fintype.card σ →
      LinearIndepOn ℚ id (↑T : Set (σ → ℚ)) := by
    intro T hT hc
    exact hYgp T hT (by rw [hfr]; exact hc)
  obtain ⟨Z, hZsub, hZinf, hZgp⟩ := genPosInt_transfer L ε Y hYsub hYinf hYgp'
  obtain ⟨K, hKfin, hLK⟩ := exists_numberField_of_algebraic_coefficients L alg
  haveI : NumberField K := { to_charZero := inferInstance, to_finiteDimensional := hKfin }
  let w : NumberField.InfinitePlace K := NumberField.InfinitePlace.mk (IntermediateField.val K)
  let a : σ → σ → K := fun i j => ⟨L i j, hLK i j⟩
  have hne : ∀ x ∈ Z, x ≠ 0 := fun x hx => (hZsub hx).1
  have hnz : ∀ x ∈ Z, ∀ i : σ, (∑ j : σ, a i j * (x j : K)) ≠ 0 := by
    intro x hx i hzero
    have h2 : (IntermediateField.val K) (∑ j : σ, a i j * (x j : K)) = 0 := by
      rw [hzero, map_zero]
    simp only [map_sum, map_mul] at h2
    exact (hZsub hx).2.2 i (by simpa using h2)
  have hsum : ∀ x ∈ Z,
      ∑ i : σ, Real.log (w.val (∑ j : σ, a i j * (x j : K))) < -ε * Real.log ‖x‖ := by
    intro x hx
    have h := small_imp_log_sum L ε (hZsub hx).1 (hZsub hx).2.2 (hZsub hx).2.1
    have hcongr : (∑ i : σ, Real.log (w.val (∑ j : σ, a i j * (x j : K)))) =
        ∑ i : σ, Real.log ‖(∑ j : σ, L i j * (x j : ℂ) : ℂ)‖ := by
      apply Finset.sum_congr rfl
      intro i _
      rw [show w.val (∑ j : σ, (a i) j * (x j : K)) = _ from
        place_val_eq K L hLK x i]
    rw [hcongr]
    exact h
  obtain ⟨c, Z', hc, hZ'sub, hZ'inf, hZ'b⟩ :=
    Commons.NumberTheory.Height.NumberField.exponent_vector_extraction_uniform
      hσ a w ε hε Z hZinf hne hnz hsum
  refine ⟨c, hc, Z', fun x hx => hZsub (hZ'sub hx), hZ'inf, ?_, ?_⟩
  · intro T hTsub hTcard
    exact hZgp T (fun x hx => hZ'sub (hTsub hx)) hTcard
  · intro x hx i
    have h := hZ'b x hx i
    rwa [show w.val (∑ j : σ, (a i) j * (x j : K)) =
      ‖(∑ j : σ, L i j * (x j : ℂ) : ℂ)‖ from place_val_eq K L hLK x i] at h

/-- **The affine subspace theorem from the rank-descent input.** -/
theorem subspaceTheoremSubspaces_of_rankDescent (hσ : 2 ≤ Fintype.card σ)
    (L : σ → σ → ℂ) (alg : ∀ i j, IsAlgebraic ℚ (L i j)) (ind : LinearIndependent ℂ L)
    (hRD : RankDescent (σ := σ) L) :
    SubspaceTheoremSubspaces σ L :=
  subspaces_of_rankDescent L hRD (stage2Output hσ L alg ind)

end Submission.Subspace
