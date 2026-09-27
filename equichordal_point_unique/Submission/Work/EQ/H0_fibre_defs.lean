import Mathlib
import Submission.Work.EQ.DefsCore
import Submission.Work.EQ.H0_invParam_ge

/-!
# Branch words of a chain in `H0`

This file sets up the combinatorial skeleton for `Work.EQ.H0_countable_fibre`: the branch word
of a chain (the sequence of choices of backward branch along the chain) and the finite word lists
that index the fan.

* `brSign a P Q` is the sign with which `P` is a backward local branch of `Q`;
  `brSign_spec` shows that for a `RegPair` it is the correct sign.
* `chainWord a p : ℤ → Bool` records at every index which of the two backward branches of `p.1 (n+1)`
  the point `p.1 n` is.
* `fanWord σ m k = [σ m, σ (m+1), …, σ (m+k-1)]`.
* `isChain_tail_fwd_z`, `isChain_tail_bwd_z`: the two tail clauses of `IsChain` in `ℤ`-indexed form.
-/

namespace Work.EQ

open Complex Filter _root_.Topology

noncomputable section

/-- The branch sign of an ordered pair of points of the equichordal relation: `true` if the first
point is the *principal* backward branch at `O₁ = (-a/2, 0)` of the second point. -/
def brSign (a : ℝ) (P Q : ℂ × ℂ) : Bool :=
  if P = invBranch a true Q then true else false

/-- For a regular pair, `brSign` is the (a) correct sign: `P` is *that* backward branch of `Q`. -/
theorem brSign_spec {a : ℝ} {P Q : ℂ × ℂ} (h : RegPair a P Q) :
    P = invBranch a (brSign a P Q) Q := by
  rcases H0_invParam_ge_exists_invBranch h.1 h.2.2 with h1 | h0
  · unfold brSign; rw [if_pos h1]; exact h1
  · by_cases hh : P = invBranch a true Q
    · unfold brSign; rw [if_pos hh]; exact hh
    · unfold brSign; rw [if_neg hh]; exact h0

/-- **The branch word of a chain.**  At index `n` it records which of the two backward local
branches of `p.1 (n+1)` the point `p.1 n` is. -/
def chainWord (a : ℝ) (p : ChainData) : ℤ → Bool :=
  fun n => brSign a (p.1 n) (p.1 (n + 1))

/-- Along a chain, the point at index `n` is the backward branch of the point at index `n+1`
selected by the branch word. -/
theorem chainWord_spec {a : ℝ} {h : ℂ → ℂ} {p : ChainData} (hp : IsChain a h p) (n : ℤ) :
    p.1 n = invBranch a (chainWord a p n) (p.1 (n + 1)) :=
  brSign_spec (hp.1 n)

/-- The list of branch signs on the interval `[m, m+k)`, in increasing order. -/
def fanWord (σ : ℤ → Bool) : ℤ → ℕ → List Bool
  | _, 0 => []
  | m, (k + 1) => σ m :: fanWord σ (m + 1) k

@[simp] theorem fanWord_zero (σ : ℤ → Bool) (m : ℤ) : fanWord σ m 0 = [] := rfl

@[simp] theorem fanWord_succ (σ : ℤ → Bool) (m : ℤ) (k : ℕ) :
    fanWord σ m (k + 1) = σ m :: fanWord σ (m + 1) k := rfl

theorem fanWord_length (σ : ℤ → Bool) (m : ℤ) (k : ℕ) : (fanWord σ m k).length = k := by
  induction k generalizing m with
  | zero => rfl
  | succ k ih => rw [fanWord_succ, List.length_cons, ih]

/-- The forward tail clause of `IsChain`, in `ℤ`-indexed form. -/
theorem isChain_tail_fwd_z {a : ℝ} {h : ℂ → ℂ} {p : ChainData} (hp : IsChain a h p) :
    ∃ N : ℕ, ∀ n : ℤ, (N : ℤ) ≤ n →
      p.1 n = germC a h ((eqLam a : ℂ) ^ n * p.2.1) := by
  obtain ⟨N, hN⟩ := eventually_atTop.1 hp.2.2.2.1
  refine ⟨N, fun n hn => ?_⟩
  obtain ⟨k, hk⟩ : ∃ k : ℕ, n = (k : ℤ) :=
    ⟨n.toNat, (Int.toNat_of_nonneg (le_trans (by positivity) hn)).symm⟩
  have hNk : N ≤ k := by omega
  rw [hk, zpow_natCast]
  exact hN k hNk

/-- The backward tail clause of `IsChain`, in `ℤ`-indexed form. -/
theorem isChain_tail_bwd_z {a : ℝ} {h : ℂ → ℂ} {p : ChainData} (hp : IsChain a h p) :
    ∃ M : ℕ, ∀ n : ℤ, n ≤ -((M : ℤ)) →
      p.1 n = ugermC a h ((eqLam a : ℂ) ^ (-n) * p.2.2) := by
  obtain ⟨M, hM⟩ := eventually_atTop.1 hp.2.2.2.2
  refine ⟨M, fun n hn => ?_⟩
  obtain ⟨k, hk⟩ : ∃ k : ℕ, -n = (k : ℤ) :=
    ⟨(-n).toNat, (Int.toNat_of_nonneg (by omega)).symm⟩
  have hnk : n = -((k : ℤ)) := by omega
  have hMk : M ≤ k := by omega
  rw [hnk, show -(-(k : ℤ)) = (k : ℤ) by ring, zpow_natCast]
  exact hM k hMk

end

end Work.EQ
