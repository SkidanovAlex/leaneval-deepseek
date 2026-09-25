/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# `ψ(v) ≤ i ↔ v ≤ φ(i)`: the inverse Herbrand function as an adjoint

`NK.Ramification.herbrandInv A v` is defined as the least `i` with `v ≤ φ(i)`, where `φ` is the
Herbrand function.  The key point — recorded here — is that this "least index" really computes the
*greatest lower bound* of the set `{i | v ≤ φ(i)}`: since `φ` is nondecreasing and unbounded, that
set is nonempty and upward closed, hence of the form `Ici (ψ v)`.  Consequently

  `ψ(v) ≤ i ↔ v ≤ φ(i)`,

i.e. `ψ` is the *upper adjoint* of `φ` in the sense of Galois connections.

This is the formal input needed to pass between the lower and the upper numbering of the
ramification filtration: the upper subgroup `G^v = G_{ψ(v)}` consists of those `σ` whose lower
index is at least `ψ(v)`, and the present equivalence turns that into the classical criterion
`σ ∈ G^v ↔ v ≤ φ(i)` whenever `σ ∈ G_i` (compare Neukirch–Schmidt–Wingberg, Chapter IV §3).

## Main results

* `NK.Ramification.lowerIndex_pos`: the lower indices are positive.
* `NK.Ramification.herbrand_monotone`: `φ` is nondecreasing.
* `NK.Ramification.herbrand_exists_ge`: `φ` is unbounded, i.e. its values exhaust `ℚ_{≥0}`.
* `NK.Ramification.herbrandInv_le_iff`: `ψ(v) ≤ i ↔ v ≤ φ(i)`.
-/
import Mathlib
import Submission.NK.Ramification.Defs
import Submission.NK.Ramification.Herbrand

namespace NK.Ramification

universe u

noncomputable section

variable {K : Type*} {L : Type*} [Field K] [Field L] [Algebra K L]

/-! ## The lower indices are positive -/

/-- Every lower index `g_i = #G_i` is positive: the ramification subgroup `G_i` always contains
the identity. -/
theorem lowerIndex_pos (A : ValuationSubring L) [Finite (A.decompositionSubgroup K)] (i : ℕ) :
    0 < lowerIndex (K := K) A i := by
  have hne : Nonempty ↥(ramificationSubgroup (K := K) A i) :=
    ⟨⟨1, (ramificationSubgroup A i).one_mem⟩⟩
  unfold lowerIndex
  exact Nat.card_pos

/-! ## Monotonicity of the Herbrand function -/

/-- **The Herbrand function is nondecreasing**: the difference
`φ(n+1) - φ(n) = g_n/g_0` is a quotient of positive numbers. -/
theorem herbrand_monotone (A : ValuationSubring L) [Finite (A.decompositionSubgroup K)] :
    Monotone (herbrand (K := K) A) := by
  intro n m hnm
  have hg0 : (0 : ℚ) < (lowerIndex (K := K) A 0 : ℚ) := by
    exact_mod_cast lowerIndex_pos (K := K) A 0
  have hsum : (∑ i ∈ Finset.range n, (lowerIndex (K := K) A i : ℚ)) ≤
      ∑ i ∈ Finset.range m, (lowerIndex (K := K) A i : ℚ) := by
    apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hnm)
    intro i _ _
    exact_mod_cast Nat.zero_le _
  rw [herbrand, herbrand]
  exact div_le_div_of_nonneg_right hsum hg0.le

/-! ## Unboundedness of the Herbrand function -/

/-- **The Herbrand function is unbounded**: `φ(v * g_0) ≥ v`, because `g_i ≥ 1` for all `i`. -/
theorem herbrand_exists_ge (A : ValuationSubring L) [Finite (A.decompositionSubgroup K)]
    (v : ℕ) : ∃ i : ℕ, (v : ℚ) ≤ herbrand (K := K) A i := by
  refine ⟨v * lowerIndex (K := K) A 0, ?_⟩
  have hg0 : (0 : ℚ) < (lowerIndex (K := K) A 0 : ℚ) := by
    exact_mod_cast lowerIndex_pos (K := K) A 0
  have hterm : ∀ i ∈ Finset.range (v * lowerIndex (K := K) A 0),
      (1 : ℚ) ≤ (lowerIndex (K := K) A i : ℚ) := by
    intro i _
    exact_mod_cast lowerIndex_pos (K := K) A i
  have hsum : ((v * lowerIndex (K := K) A 0 : ℕ) : ℚ) ≤
      ∑ i ∈ Finset.range (v * lowerIndex (K := K) A 0),
        (lowerIndex (K := K) A i : ℚ) := by
    have h := Finset.sum_le_sum hterm
    simpa using h
  rw [herbrand]
  rw [show (v : ℚ) = ((v * lowerIndex (K := K) A 0 : ℕ) : ℚ) /
      (lowerIndex (K := K) A 0 : ℚ) from ?_]
  · exact div_le_div_of_nonneg_right hsum hg0.le
  · push_cast
    field_simp

/-! ## The inverse Herbrand function as an upper adjoint -/

/-- `ψ(v)` is the *least* index with `v ≤ φ(i)`; equivalently (here) `ψ` and `φ` are adjoint:

  `ψ(v) ≤ i ↔ v ≤ φ(i)`.

Indeed, `φ` is nondecreasing and unbounded, so `S = {i | v ≤ φ(i)}` is a nonempty upward closed
set of naturals, i.e. `S = Ici (sInf S)`; and `sInf S` is exactly `herbrandInv A v`. -/
theorem herbrandInv_le_iff {K L : Type*} [Field K] [Field L] [Algebra K L]
    (A : ValuationSubring L) [Finite (A.decompositionSubgroup K)] (v i : ℕ) :
    NK.Ramification.herbrandInv (K := K) A v ≤ i ↔
      (v : ℚ) ≤ NK.Ramification.herbrand (K := K) A i := by
  have hne : ({i : ℕ | (v : ℚ) ≤ herbrand (K := K) A i} : Set ℕ).Nonempty :=
    herbrand_exists_ge (K := K) A v
  have hup : ∀ k₁ k₂ : ℕ, k₁ ≤ k₂ →
      k₁ ∈ ({i : ℕ | (v : ℚ) ≤ herbrand (K := K) A i} : Set ℕ) →
      k₂ ∈ ({i : ℕ | (v : ℚ) ≤ herbrand (K := K) A i} : Set ℕ) :=
    fun k₁ k₂ h hk => hk.trans (herbrand_monotone (K := K) A h)
  have h := Nat.eq_Ici_of_nonempty_of_upward_closed hne hup
  change sInf {i : ℕ | (v : ℚ) ≤ herbrand (K := K) A i} ≤ i ↔
      (v : ℚ) ≤ herbrand (K := K) A i
  exact (Set.ext_iff.mp h i).symm

end

end NK.Ramification
