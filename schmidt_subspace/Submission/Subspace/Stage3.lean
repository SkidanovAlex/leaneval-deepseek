import Mathlib
import Submission.Commons.GeometryOfNumbers.Box.rank_bound_small_body_complex

/-!
# Stage 3 glue: the ℂ-linear map given by the system of linear forms

For `L : σ → σ → ℂ`, the map `x ↦ (i ↦ ∑ⱼ Lᵢⱼ xⱼ)` is `ℂ`-linear; it is
injective exactly when the rows of `L` are `ℂ`-linearly independent (matrix
row-independence ↔ unit ↔ injective `mulVec`).  This map is the linear map whose
inverse image of a polydisc is the approximation domain `Π(Q)`, and injectivity
is what makes `Π(Q)` bounded.

We also record the base-change fact that `ℚ`-independent integer vectors remain
`ℂ`-independent when viewed in `ℂ^σ`.
-/

open scoped BigOperators Matrix

namespace Submission.Subspace

section Stage3

variable {σ : Type*} [Fintype σ]

/-- The `ℂ`-linear map `x ↦ (i ↦ ∑ⱼ Lᵢⱼ xⱼ)` attached to the system of forms. -/
noncomputable def formsLinearMap (L : σ → σ → ℂ) :
    (σ → ℂ) →ₗ[ℂ] (σ → ℂ) :=
  (Matrix.of L).mulVecLin

lemma formsLinearMap_apply (L : σ → σ → ℂ) (x : σ → ℂ) :
    formsLinearMap L x = fun i : σ => ∑ j : σ, L i j * x j := by
  funext i
  simp only [formsLinearMap, Matrix.mulVecLin_apply, Matrix.mulVec, Matrix.of_apply]
  rfl

/-- Row-independence makes the form map injective. -/
theorem formsLinearMap_injective (L : σ → σ → ℂ) (ind : LinearIndependent ℂ L) :
    Function.Injective (formsLinearMap L) := by
  classical
  change Function.Injective (Matrix.of L).mulVec
  rw [Matrix.mulVec_injective_iff_isUnit, ← Matrix.linearIndependent_rows_iff_isUnit]
  have hrow : (Matrix.of L).row = L := by
    funext i j
    rfl
  rw [hrow]
  exact ind

/-- `ℚ`-independent integer vectors stay `ℂ`-independent in `ℂ^σ` (base change
along `ℚ → ℂ`). -/
theorem linearIndependent_int_cast_complex {ι : Type*} [Finite ι]
    (y : ι → σ → ℤ) (h : LinearIndependent ℚ (fun i => fun j => (y i j : ℚ))) :
    LinearIndependent ℂ (fun i => fun j => (y i j : ℂ)) := by
  have h' : LinearIndependent ℂ
      (fun i => algebraMap ℚ ℂ ∘ (fun j => (y i j : ℚ))) :=
    (linearIndependent_algebraMap_comp_iff (R := ℚ) (S := ℂ)).mpr h
  simpa [Function.comp_def, Rat.cast_intCast] using h'

/-- **Step 3 (rank bound).** For a system of forms `L` with `ℂ`-independent rows and
exponents `c` with negative total sum, there is `Q₀` such that for `Q ≥ Q₀` the
approximation domain `{x : |∑ⱼ Lᵢⱼ xⱼ| ≤ Q^{cᵢ}}` contains no `σ` linearly
independent integer points: hence its rank is `< |σ|`. -/
theorem no_independent_int_points_of_small_domain (hσ : 2 ≤ Fintype.card σ)
    (L : σ → σ → ℂ) (ind : LinearIndependent ℂ L) (c : σ → ℝ)
    (hc : ∑ i, c i < 0) :
    ∃ Q₀ : ℝ, 1 ≤ Q₀ ∧ ∀ Q : ℝ, Q₀ ≤ Q →
      ¬ ∃ y : σ → (σ → ℤ),
        LinearIndependent ℚ (fun i => fun j => (y i j : ℚ)) ∧
        ∀ i k, ‖(∑ j : σ, L k j * (y i j : ℂ))‖ ≤ Q ^ (c k) := by
  classical
  haveI : Nonempty σ := Fintype.card_pos_iff.mp (by omega)
  obtain ⟨Q₀, hQ₀1, hQ₀⟩ :=
    Commons.GeometryOfNumbers.Box.rank_bound_small_body_complex
      (formsLinearMap L) (formsLinearMap_injective L ind) c hc
  refine ⟨Q₀, hQ₀1, ?_⟩
  intro Q hQ
  rintro ⟨y, hyind, hyb⟩
  refine hQ₀ Q hQ ⟨y, linearIndependent_int_cast_complex y hyind, ?_⟩
  intro i k
  have hik := hyb i k
  simpa only [formsLinearMap_apply] using hik

end Stage3

end Submission.Subspace
