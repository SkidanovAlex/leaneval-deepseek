import Mathlib
import Submission.Work.Peluse.Basic

/-!
# The expansion bookkeeping of `Work.Peluse.Holds.ExpansionPETShort`

This module fixes the vocabulary of the "expansion + Peluse's Lemma 4.10" step of Peluse's
Theorem 3.5 (the short-scale first half, `Work.Peluse.Holds.ExpansionPETShort`).

For index vectors `n n' : Fin s → ℤ` (the multipliers of the arithmetic progressions
`(c·a + bᵢ)[M₁]`) and a sign pattern `ω : Fin s → Bool` we write

* `lam n n' ω = ∑ᵢ (ω i ? n i : n' i)` — the coefficient of `a` in the `ω`-corner,
* `mu b n n' ω = ∑ᵢ (ω i ? n i : n' i) * bᵢ` — the constant part of the `ω`-corner,
* `cubeShift κ n n' ω = ∑ᵢ (ω i ? n i : n' i) * κᵢ` — the corner shift `x + (that)`,
* `expCube κ n n' f x = ∏_ω C^{|ω|} f (x + cubeShift κ n n' ω)` — the cube term.

The set of `2^s` corners of the cube is enumerated by an equiv `ε : Fin (2^s) ≃ (Fin s → Bool)`
whose last element is the all-ones pattern; the difference
`c · (lam n n' (ε j) - lam n n' (ε 0))` is then the phase of the `j`-th slot of Peluse's
multilinear average (Lemma 4.10), and `mu b n n' (ε j) - mu b n n' (ε 0)` is the shift of the
corresponding `1`-bounded slot function.
-/

set_option autoImplicit false

open scoped BigOperators

namespace Work.Peluse.Holds.ExpPET

noncomputable section

open Work.Peluse

/-- The coefficient `λ_ω = ∑ᵢ (ω i ? n i : n' i)` of `a` in the `ω`-corner. -/
def lam {s : ℕ} (n n' : Fin s → ℤ) (ω : Fin s → Bool) : ℤ :=
  ∑ i : Fin s, if ω i then n i else n' i

/-- The constant part `μ_ω = ∑ᵢ (ω i ? n i : n' i) · bᵢ` of the `ω`-corner. -/
def mu {s : ℕ} (b n n' : Fin s → ℤ) (ω : Fin s → Bool) : ℤ :=
  ∑ i : Fin s, (if ω i then n i else n' i) * b i

/-- The corner shift `∑ᵢ (ω i ? n i : n' i) · κᵢ`. -/
def cubeShift {s : ℕ} (κ n n' : Fin s → ℤ) (ω : Fin s → Bool) : ℤ :=
  ∑ i : Fin s, (if ω i then n i else n' i) * κ i

/-- The cube term `∏_ω C^{|ω|} f (x + cubeShift κ n n' ω)`. -/
def expCube {s : ℕ} (κ n n' : Fin s → ℤ) (f : ℤ → ℂ) : ℤ → ℂ :=
  fun x => ∏ ω : Fin s → Bool, (star^[Work.Peluse.weight ω]) (f (x + cubeShift κ n n' ω))

/-- The all-ones pattern. -/
def ones (s : ℕ) : Fin s → Bool := fun _ => true

/-- The all-zeros pattern. -/
def zeros (s : ℕ) : Fin s → Bool := fun _ => false

/-- The complement of a sign pattern. -/
def comp {s : ℕ} (ω : Fin s → Bool) : Fin s → Bool := fun i => !ω i

lemma comp_involutive {s : ℕ} (ω : Fin s → Bool) : comp (comp ω) = ω := by
  funext i; simp [comp]

lemma comp_injective {s : ℕ} : Function.Injective (@comp s) := by
  intro ω ω' h
  have := congrArg comp h
  simpa [comp_involutive] using this

lemma comp_ne_ones_iff {s : ℕ} (ω : Fin s → Bool) : comp ω ≠ ones s ↔ ω ≠ zeros s := by
  constructor
  · intro h hz
    exact h (by rw [hz]; funext i; simp [comp, ones, zeros])
  · intro h hc
    exact h (by rw [← comp_involutive ω, hc]; funext i; simp [comp, ones, zeros])

/-- The slot identity of the expansion: for `κ i = c·a + bᵢ` the `a`-dependence of the `ω`-corner
is `c·λ_ω·a` plus the constant `μ_ω`. -/
lemma cubeShift_eq {s : ℕ} (κ b : Fin s → ℤ) (n n' : Fin s → ℤ) (ω : Fin s → Bool) (c a : ℤ)
    (hκ : ∀ i : Fin s, κ i = c * a + b i) :
    cubeShift κ n n' ω = (c * a) * lam n n' ω + mu b n n' ω := by
  rw [cubeShift, lam, mu, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hκ i]; ring

/-- The all-ones pattern is the complement of the all-zeros pattern. -/
lemma comp_zeros {s : ℕ} : comp (zeros s) = ones s := by
  funext i; simp [comp, ones, zeros]

/-- The corner at the all-ones pattern is the sum of the corner at the all-zeros pattern and the
difference vector, in the `λ`- and `μ`-bookkeeping. -/
lemma lam_ones_sub {s : ℕ} (n n' : Fin s → ℤ) :
    lam n n' (ones s) - lam n n' (zeros s) = ∑ i : Fin s, (n i - n' i) := by
  simp only [lam, ones, zeros]
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => by simp

/-- The direction `c·(λ_{ε m} - λ_{ε j})` with `ε m` the all-ones pattern is the `ωOf`-direction
`c · ∑_{i : ωOf i} (nᵢ - n'ᵢ)`. -/
lemma dir_eq {s : ℕ} {n n' : Fin s → ℤ} (ω : Fin s → Bool) :
    lam n n' (ones s) - lam n n' ω
      = ∑ i : Fin s, (if comp ω i then (n i - n' i) else 0) := by
  rw [lam, lam, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  cases h : ω i <;> simp [ones, comp, h]

end

end Work.Peluse.Holds.ExpPET
