import Mathlib
import Submission.Work.SG.Defs

/-! Guidance from the project lead (the requester):

FULL ROUTE: read Submission/Work/SG/DESIGN.md first (orchestrator design; your lemma is one node of its DAG). Shared definitions + generated data: Submission/Work/SG/Defs.lean (namespace Work.SG) — do NOT edit it. native_decide is NOT permitted (only kernel decide / rfl); keep certificate checks kernel-cheap. Siblings run in parallel; import them when they land.

# intEquiv_transport — push a datum along `U` (easy–medium, ~200–400 lines)

**Claim.** For `U` unimodular, `P' := U P U⁻¹` is an integral point group carrying the cocycle
`τ'(A) := U τ(U⁻¹ A U)`, and `IntEquiv P τ P' τ' U 0`.

**Sketch.** Point group: image of a finite set; `U A U⁻¹ U B U⁻¹ = U(AB)U⁻¹`;
`det(UAU⁻¹) = det A`. Cocycle: `τ'(A'B') = U τ(AB) = U τ A + U A τ B + U n
= τ' A' + A' τ' B' + U n`, with `U n ∈ ℤ³`. `IntEquiv` clause 2 with `s = 0` is definitional
(`U⁻¹(U B U⁻¹)U = B`).
-/

set_option linter.style.haveILetI false

namespace Work.SG

/-- Transported cocycle: `τ'(A) = U · τ(U⁻¹ A U)`. -/
noncomputable def transportTau (U : IMat) (τ : IMat → Fin 3 → ℝ) : IMat → Fin 3 → ℝ :=
  fun A => (U.map (Int.cast : ℤ → ℝ)).mulVec (τ (U⁻¹ * A * U))

/-- `U⁻¹ (U X U⁻¹) U = X` for `U` unimodular. -/
lemma inv_mul_conj_mul (U X : IMat) (hU : IsUnit U.det) : U⁻¹ * (U * X * U⁻¹) * U = X := by
  haveI := Matrix.invertibleOfIsUnitDet U hU
  simp only [Matrix.mul_assoc, Matrix.mul_one, Matrix.inv_mul_of_invertible,
    Matrix.inv_mul_cancel_left_of_invertible]

/-- `(U X U⁻¹) U = U X` for `U` unimodular. -/
lemma conj_mul' (U X : IMat) (hU : IsUnit U.det) : (U * X * U⁻¹) * U = U * X := by
  haveI := Matrix.invertibleOfIsUnitDet U hU
  simp only [Matrix.mul_assoc, Matrix.mul_one, Matrix.inv_mul_of_invertible]

/-- Conjugation is multiplicative: `(UAU⁻¹)(UBU⁻¹) = U(AB)U⁻¹`. -/
lemma conj_mul_conj (U A B : IMat) (hU : IsUnit U.det) :
    (U * A * U⁻¹) * (U * B * U⁻¹) = U * (A * B) * U⁻¹ := by
  haveI := Matrix.invertibleOfIsUnitDet U hU
  simp only [Matrix.mul_assoc, Matrix.inv_mul_cancel_left_of_invertible]

/-- The integer matrix cast acts on integer vectors by `intVec (U.mulVec n)`. -/
lemma map_cast_mulVec_intVec (U : IMat) (n : Fin 3 → ℤ) :
    (U.map (Int.cast : ℤ → ℝ)).mulVec (intVec n) = intVec (U.mulVec n) := by
  ext i
  simp [Matrix.mulVec, dotProduct, intVec, Int.cast_sum]

/-- Casting commutes with matrix multiplication on vectors. -/
lemma map_cast_mulVec_mulVec (U A : IMat) (v : Fin 3 → ℝ) :
    ((U * A).map (Int.cast : ℤ → ℝ)).mulVec v
      = (U.map (Int.cast : ℤ → ℝ)).mulVec ((A.map (Int.cast : ℤ → ℝ)).mulVec v) := by
  change ((U * A).map (⇑(Int.castRingHom ℝ))).mulVec v
      = (U.map (⇑(Int.castRingHom ℝ))).mulVec ((A.map (⇑(Int.castRingHom ℝ))).mulVec v)
  rw [Matrix.map_mul, ← Matrix.mulVec_mulVec]

/-- `τ'` on a conjugate `U X U⁻¹` is `U` applied to `τ X`. -/
lemma transportTau_conj (U : IMat) (τ : IMat → Fin 3 → ℝ) (hU : IsUnit U.det) (X : IMat) :
    transportTau U τ (U * X * U⁻¹) = (U.map (Int.cast : ℤ → ℝ)).mulVec (τ X) := by
  rw [transportTau, inv_mul_conj_mul U X hU]

/-- Naturality of conjugation: `U (A w) = (UAU⁻¹) (U w)` on vectors. -/
lemma mulVec_comp_conj (U A : IMat) (hU : IsUnit U.det) (w : Fin 3 → ℝ) :
    (U.map (Int.cast : ℤ → ℝ)).mulVec ((A.map (Int.cast : ℤ → ℝ)).mulVec w)
      = ((U * A * U⁻¹).map (Int.cast : ℤ → ℝ)).mulVec
          ((U.map (Int.cast : ℤ → ℝ)).mulVec w) :=
  calc (U.map (Int.cast : ℤ → ℝ)).mulVec ((A.map (Int.cast : ℤ → ℝ)).mulVec w)
      = ((U * A).map (Int.cast : ℤ → ℝ)).mulVec w :=
        (map_cast_mulVec_mulVec U A w).symm
    _ = (((U * A * U⁻¹) * U).map (Int.cast : ℤ → ℝ)).mulVec w := by rw [conj_mul' U A hU]
    _ = ((U * A * U⁻¹).map (Int.cast : ℤ → ℝ)).mulVec
          ((U.map (Int.cast : ℤ → ℝ)).mulVec w) := map_cast_mulVec_mulVec (U * A * U⁻¹) U w

/-- Transport of a datum along a unimodular `U`: the conjugate point group carries a cocycle
`τ'` with `IntEquiv P τ (U P U⁻¹) τ' U 0`. -/
theorem intEquiv_transport {P : Set IMat} {τ : IMat → Fin 3 → ℝ} (hP : IsIntPointGroup P)
    (hτ : IsIntCocycle P τ) {U : IMat} (hU : IsUnit U.det) :
    ∃ τ' : IMat → Fin 3 → ℝ,
      IsIntPointGroup {A | ∃ B ∈ P, A = U * B * U⁻¹} ∧
      IsIntCocycle {A | ∃ B ∈ P, A = U * B * U⁻¹} τ' ∧
      IntEquiv P τ {A | ∃ B ∈ P, A = U * B * U⁻¹} τ' U 0 := by
  refine ⟨transportTau U τ, ?_, ?_, ?_⟩
  · obtain ⟨hfin, hone, hmul, hunit⟩ := hP
    refine ⟨?_, ?_, ?_, ?_⟩
    · have h : {A | ∃ B ∈ P, A = U * B * U⁻¹} = (fun B => U * B * U⁻¹) '' P := by
        ext A; simp [Set.mem_image, eq_comm]
      rw [h]
      exact hfin.image _
    · exact ⟨1, hone, by rw [Matrix.mul_one, Matrix.mul_nonsing_inv U hU]⟩
    · rintro A ⟨X, hX, rfl⟩ B ⟨Y, hY, rfl⟩
      exact ⟨X * Y, hmul X hX Y hY, conj_mul_conj U X Y hU⟩
    · rintro A ⟨X, hX, rfl⟩
      rw [Matrix.det_mul, Matrix.det_mul]
      exact IsUnit.mul (IsUnit.mul hU (hunit X hX)) (Matrix.isUnit_nonsing_inv_det U hU)
  · rintro A' ⟨A, hA, rfl⟩ B' ⟨B, hB, rfl⟩
    obtain ⟨m, hm⟩ := hτ A hA B hB
    refine ⟨U.mulVec m, ?_⟩
    rw [conj_mul_conj U A B hU, transportTau_conj U τ hU (A * B), hm,
        transportTau_conj U τ hU A, transportTau_conj U τ hU B,
        ← mulVec_comp_conj U A hU (τ B), ← map_cast_mulVec_intVec U m]
    simp only [Matrix.mulVec_add, add_assoc]
  · refine ⟨?_, ?_⟩
    · intro A; rfl
    · intro B hB
      refine ⟨0, ?_⟩
      rw [transportTau_conj U τ hU B]
      ext i
      simp [Matrix.mulVec_zero, intVec]

end Work.SG
