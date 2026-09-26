import Mathlib
import Submission.Work.SG.AffCoord

/-! Basic facts about lattice-normalised space groups.

These are the elementary facts needed by the main classification route:
* the cocycle value at the identity is an integer vector;
* every integer translation is an element of `sgSet P τ`;
* conjugation of sets of affine maps is an involution. -/

namespace Work.SG

open LeanEval.Geometry.SpaceGroupsProblem

open scoped Matrix

/-- The cocycle value at the identity is an integer vector.  Indeed the cocycle identity at
`(1, 1)` reads `τ 1 = τ 1 + 1·τ 1 + n = τ 1 + τ 1 + n` with `n ∈ ℤ³`, so `τ 1 = -n`. -/
private lemma isIntVec_tau_one {P : Set IMat} {τ : IMat → Fin 3 → ℝ}
    (hτ : IsIntCocycle P τ) (h1 : (1 : IMat) ∈ P) : IsIntVec (τ 1) := by
  obtain ⟨n, hn⟩ := hτ 1 h1 1 h1
  refine ⟨-n, ?_⟩
  have hn' : τ 1 = τ 1 + τ 1 + intVec n := by
    simpa [matR_one, Matrix.one_mulVec, mul_one] using hn
  rw [intVec_neg]
  ext i
  have hi := congrFun hn' i
  simp only [Pi.add_apply, Pi.neg_apply, intVec] at hi ⊢
  linarith

/-- Every integer translation occurs in `sgSet P τ`.  It is the element attached to the identity
`1 ∈ P`, with the integral correction coming from `isIntVec_tau_one`. -/
private lemma exists_translation_mem_sgSet {P : Set IMat} {τ : IMat → Fin 3 → ℝ}
    (hP : IsIntPointGroup P) (hτ : IsIntCocycle P τ) (n : Fin 3 → ℤ) :
    ∃ g ∈ sgSet P τ, ∀ x : E 3, g x = x + WithLp.toLp 2 (intVec n) := by
  obtain ⟨m, hm⟩ := isIntVec_tau_one hτ hP.2.1
  refine ⟨affOfInt 1 (hP.2.2.2 1 hP.2.1) (τ 1 + intVec (n - m)),
    affOfInt_mem_sgSet hP hP.2.1 (n - m), ?_⟩
  intro x
  rw [affOfInt_apply, matR_one, Matrix.one_mulVec, hm]
  have hnm : intVec m + intVec (n - m) = intVec n := by
    rw [← intVec_add]; congr 1; abel
  rw [hnm, WithLp.toLp_add, WithLp.toLp_ofLp]

/-- `conjSet φ⁻¹` inverts `conjSet φ`. -/
private lemma conjSet_inv (φ : AffineGroup 3) (S : Set (AffineGroup 3)) :
    conjSet φ⁻¹ (conjSet φ S) = S := by
  ext h
  simp only [conjSet, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨g, ⟨g', hg', rfl⟩, rfl⟩
    have : φ⁻¹ * (φ * g' * φ⁻¹) * (φ⁻¹)⁻¹ = g' := by group
    rw [this]; exact hg'
  · intro hh
    exact ⟨φ * h * φ⁻¹, ⟨h, hh, rfl⟩, by group⟩

/-- `conjSet φ` inverts `conjSet φ⁻¹` (the other order of `conjSet_inv`). -/
private lemma conjSet_inv' (φ : AffineGroup 3) (S : Set (AffineGroup 3)) :
    conjSet φ (conjSet φ⁻¹ S) = S := by
  have := conjSet_inv φ⁻¹ S
  rwa [inv_inv] at this

/-- Basic facts about lattice-normalised space groups and affine conjugation: the cocycle value
`τ 1` is integral; every integer translation occurs in `sgSet P τ`; and `conjSet` is an
involution (`conjSet φ⁻¹` inverts `conjSet φ` in both orders). -/
theorem sgSet_basic :
    (∀ (P : Set Work.SG.IMat) (τ : Work.SG.IMat → Fin 3 → ℝ),
      Work.SG.IsIntCocycle P τ → (1 : Work.SG.IMat) ∈ P →
      Work.SG.IsIntVec (τ 1)) ∧
    (∀ (P : Set Work.SG.IMat) (τ : Work.SG.IMat → Fin 3 → ℝ),
      Work.SG.IsIntPointGroup P →
      Work.SG.IsIntCocycle P τ → ∀ n : Fin 3 → ℤ,
      ∃ g ∈ Work.SG.sgSet P τ, ∀ x : LeanEval.Geometry.SpaceGroupsProblem.E 3,
        g x = x + WithLp.toLp 2 (Work.SG.intVec n)) ∧
    (∀ (φ : LeanEval.Geometry.SpaceGroupsProblem.AffineGroup 3)
      (S : Set (LeanEval.Geometry.SpaceGroupsProblem.AffineGroup 3)),
      Work.SG.conjSet φ⁻¹ (Work.SG.conjSet φ S) = S) ∧
    (∀ (φ : LeanEval.Geometry.SpaceGroupsProblem.AffineGroup 3)
      (S : Set (LeanEval.Geometry.SpaceGroupsProblem.AffineGroup 3)),
      Work.SG.conjSet φ (Work.SG.conjSet φ⁻¹ S) = S) :=
  ⟨fun _ _ hτ h1 => isIntVec_tau_one hτ h1,
   fun _ _ hP hτ n => exists_translation_mem_sgSet hP hτ n,
   fun φ S => conjSet_inv φ S,
   fun φ S => conjSet_inv' φ S⟩

end Work.SG
