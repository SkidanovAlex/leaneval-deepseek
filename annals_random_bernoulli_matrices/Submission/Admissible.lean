import Mathlib
import Submission.Commons.Nat.Card.big_coords_prefix_count

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 800000
set_option linter.dupNamespace false

noncomputable section

/-!
# Section 3: admissible coordinate families (Step 8B(a))

A coordinate family `A : Fin ℓ → Finset ℤ` is `(N, n, δ)`-admissible (for the
counting layer of Proposition `p: rough decay`) when, writing `i+1` for the
1-based index of coordinate `i`:

- for the small indices (`(i:ℝ)+1 ≤ δ·(n:ℝ)`): `A i` is the disjoint union of
  two integer intervals of cardinality at least `N` each, and every element
  has magnitude `> N` (so any realization `x i` of that coordinate is
  "big");
- for the large indices (`δ·(n:ℝ) < (i:ℝ)+1`): `A i` is a single integer
  interval of cardinality at least `N`.

The interval data is existentially quantified (the assembly later constructs
it from incompressible vectors); the counting layer consumes it through the
`perGoodStep_*` lemmas of `Submission.RoughProduct`.  Origin symmetry of the
small-index arms is NOT needed by the counting (the per-step bounds count
`¬decaysAt` over the actual interval arms); it will be imposed separately in
Section 5d where the families are constructed.
-/

open scoped BigOperators

namespace Submission.Admissible

attribute [local instance] Classical.propDecidable

/-- The 1-based index of coordinate `i` is at most `δ·(n:ℝ)`. -/
def smallIndex (n : ℕ) (δ : ℝ) (i : ℕ) : Prop :=
  (i : ℝ) + 1 ≤ δ * (n : ℝ)

/-- `A` is an admissible coordinate family (counting-layer form). -/
def Admissible (N n ℓ : ℕ) (δ : ℝ) (A : Fin ℓ → Finset ℤ) : Prop :=
  (∀ i : Fin ℓ, smallIndex n δ (i.val) →
      ∃ c₁ d₁ c₂ d₂ : ℤ,
        A i = Finset.Icc c₁ d₁ ∪ Finset.Icc c₂ d₂ ∧
        (N : ℤ) ≤ d₁ - c₁ + 1 ∧
        (N : ℤ) ≤ d₂ - c₂ + 1 ∧
        Disjoint (Finset.Icc c₁ d₁) (Finset.Icc c₂ d₂) ∧
        ∀ a : ℤ, a ∈ A i → (N : ℝ) < |(a : ℝ)|) ∧
    (∀ i : Fin ℓ, ¬ smallIndex n δ (i.val) →
      ∃ c d : ℤ,
        A i = Finset.Icc c d ∧
        (N : ℤ) ≤ d - c + 1)

/-- Small-index coordinates avoid `[−N, N]`: every element has magnitude
`> N`. -/
lemma big_of_small {N n ℓ : ℕ} {δ : ℝ} {A : Fin ℓ → Finset ℤ}
    (hA : Admissible N n ℓ δ A) {i : Fin ℓ} (hi : smallIndex n δ (i.val))
    {a : ℤ} (ha : a ∈ A i) :
    (N : ℝ) < |(a : ℝ)| := by
  classical
  rcases hA.1 i hi with ⟨c₁, d₁, c₂, d₂, hcov, _, _, _, hbig⟩
  exact hbig a ha

/-- Large-index coordinates carry single-interval data of cardinality ≥ N. -/
lemma single_interval_of_large {N n ℓ : ℕ} {δ : ℝ} {A : Fin ℓ → Finset ℤ}
    (hA : Admissible N n ℓ δ A) {i : Fin ℓ} (hi : ¬ smallIndex n δ (i.val)) :
    ∃ c d : ℤ,
      A i = Finset.Icc c d ∧ (N : ℤ) ≤ d - c + 1 := by
  classical
  exact hA.2 i hi

/-- The count of the prefix coordinates that are small is at least `δ₀·(n:ℝ)`
once the prefix is at least `δ₀·n` long (fleet lemma). -/
lemma bigCoordSet_card {n k : ℕ} {δ₀ δ : ℝ} (hδ₀ : 0 < δ₀) (hδle : δ₀ ≤ δ)
    (hk : δ₀ * (n : ℝ) ≤ k) (hslack : (1 : ℝ) ≤ (δ - δ₀) * (n : ℝ)) :
    δ₀ * (n : ℝ) ≤ (((Finset.univ : Finset (Fin k)).filter
        (fun j : Fin k => smallIndex n δ (j.val))).card : ℝ) := by
  have h := Commons.Nat.Card.big_coords_prefix_count hδ₀ hδle hk hslack
  have heq : ((Finset.univ : Finset (Fin k)).filter (fun j : Fin k => smallIndex n δ (j.val))) =
      (Finset.univ : Finset (Fin k)).filter (fun j : Fin k => (j.val : ℝ) + 1 ≤ δ * (n : ℝ)) := by
    apply Finset.filter_congr
    intro j hj
    simp [smallIndex]
  rw [heq]
  exact h

end Submission.Admissible
