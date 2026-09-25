import Mathlib.Analysis.Normed.Group.Defs

namespace Commons.Analysis.Fourier

open Finset

section
variable {E : Type*} [NormedAddCommGroup E] [DecidableEq E]

/-- The dyadic "chain map" associated with a family of net maps `σ`: `q 0 = id` and
`q (k+1) = σ (S - k - 1) ∘ q k`.  The point of defining `q` recursively (rather than choosing each
`q k i` independently inside `range (σ (S-k))`) is that `q (k+1) i` depends on `i` only through
`q k i`, which is what makes the `k`-th difference range over a set of size `#(range (σ (S-k)))`
rather than a product of two range sizes. -/
def dyadicChain (N : ℕ) (S : ℕ) (σ : ℕ → Fin N → Fin N) : ℕ → Fin N → Fin N :=
  Nat.rec (motive := fun _ => Fin N → Fin N) (fun i => i)
    (fun k f => fun i => σ (S - k - 1) (f i))

@[simp] lemma dyadicChain_zero_apply (N S : ℕ) (σ : ℕ → Fin N → Fin N) (i : Fin N) :
    dyadicChain N S σ 0 i = i := rfl

@[simp] lemma dyadicChain_succ_apply (N S : ℕ) (σ : ℕ → Fin N → Fin N) (k : ℕ) (i : Fin N) :
    dyadicChain N S σ (k+1) i = σ (S - k - 1) (dyadicChain N S σ k i) := rfl

/-- For `k ≥ 1` the `k`-th element of the chain lies in the range of the `k`-th net map `σ (S-k)`. -/
lemma dyadicChain_mem_image (N S : ℕ) (σ : ℕ → Fin N → Fin N) {k : ℕ} (hk : 1 ≤ k) (i : Fin N) :
    dyadicChain N S σ k i ∈ Finset.univ.image (σ (S - k)) := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
  rw [dyadicChain_succ_apply]
  rw [show S - (j + 1) = S - j - 1 from (Nat.sub_sub S j 1).symm]
  exact Finset.mem_image_of_mem _ (Finset.mem_univ _)

/-- The finite set `B k` of possible `k`-th differences
`a (q k i) - a (q (k+1) i) = a v - a (σ (S-k-1) v)`.
For `k = 0` the indexing set is all of `Fin N` (giving at most `N` elements), while for `k ≥ 1` it is
the range of `σ (S-k)` (giving at most `#(range (σ (S-k)))` elements). -/
def dyadicDiff (N S : ℕ) (a : Fin N → E) (σ : ℕ → Fin N → Fin N) (k : ℕ) : Finset E :=
  (if k = 0 then (Finset.univ : Finset (Fin N)) else Finset.univ.image (σ (S - k))).image
    (fun v => a v - a (σ (S - k - 1) v))

lemma dyadicDiff_def (N S : ℕ) (a : Fin N → E) (σ : ℕ → Fin N → Fin N) (k : ℕ) :
    dyadicDiff N S a σ k =
      (if k = 0 then (Finset.univ : Finset (Fin N)) else Finset.univ.image (σ (S - k))).image
        (fun v => a v - a (σ (S - k - 1) v)) := rfl

/-- **Dyadic chain decomposition of a bounded family with prescribed nets** (the combinatorial
content of the entropy decomposition, (4.21)–(4.23) of Bourgain's *Pointwise ergodic theorems for
arithmetic sets*).

Let `a : Fin N → E` be a finite family in a normed group `E`, and for every scale `s ≤ S` let
`σ s : Fin N → Fin N` be a "net map": `a (σ s i)` is within `2 · 2^{-s}` of `a i`, so that the
range of `σ s` is a `2 · 2^{-s}`-net for the family, of cardinality at most `#(range (σ s))`.

Then there is a *chain* `q : ℕ → Fin N → Fin N` with `q k i ∈ range (σ (S - k))` for `k ≥ 1`,
such that every family value decomposes as
`a i = a (q S i) + ∑_{k < S} (a (q k i) - a (q (k+1) i))`,
where each difference lies in a finite set `B k` with `#(B k) ≤ #(range (σ (S - k)))` (for `k ≥ 1`;
`#(B 0) ≤ N`) and `‖b‖ ≤ 2 · 2^{-(S-k-1)}` for `b ∈ B k`.

The point of the *chain* (each `q (k+1) i` depends only on `q k i`, rather than the two nets being
chosen independently) is that `B k` has at most `#(range (σ (S-k)))` elements rather than the
product of the two cardinalities — this is what makes the resulting entropy sum match Bourgain's
`∫_0^∞ min(K, M_λ)^{1/2} dλ`. -/
theorem exists_dyadic_chain_decomposition
    {E : Type*} [NormedAddCommGroup E] [DecidableEq E]
    (N S : ℕ) (a : Fin N → E) (σ : ℕ → Fin N → Fin N)
    (hnet : ∀ s, s ≤ S → ∀ i : Fin N, ‖a i - a (σ s i)‖ ≤ 2 * (1 / 2 : ℝ) ^ s) :
    ∃ (q : ℕ → Fin N → Fin N) (B : ℕ → Finset E),
      (∀ k, 1 ≤ k → k ≤ S → ∀ i, q k i ∈ Finset.univ.image (σ (S - k))) ∧
      (∀ k, k < S → ∀ i, a (q k i) - a (q (k+1) i) ∈ B k) ∧
      (∀ k, 1 ≤ k → k < S → (B k).card ≤ (Finset.univ.image (σ (S - k))).card) ∧
      (B 0).card ≤ N ∧
      (∀ k, k < S → ∀ b ∈ B k, ‖b‖ ≤ 2 * (1 / 2 : ℝ) ^ (S - k - 1)) ∧
      (∀ i, a i = a (q S i) + ∑ k ∈ Finset.range S, (a (q k i) - a (q (k+1) i))) := by
  refine ⟨dyadicChain N S σ, dyadicDiff N S a σ, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- the chain `q k` lands in `range (σ (S-k))` for `k ≥ 1`
    intro k hk _ i
    exact dyadicChain_mem_image N S σ hk i
  · -- each difference lies in `B k`
    intro k _ i
    rw [dyadicChain_succ_apply]
    refine Finset.mem_image.mpr ⟨dyadicChain N S σ k i, ?_, rfl⟩
    by_cases hk0 : k = 0
    · subst hk0; simp
    · rw [if_neg hk0]
      exact dyadicChain_mem_image N S σ (by omega) i
  · -- cardinality of `B k` for `k ≥ 1`
    intro k hk1 _
    have hk0 : k ≠ 0 := by omega
    simp only [dyadicDiff_def, if_neg hk0]
    exact Finset.card_image_le
  · -- cardinality of `B 0`
    rw [dyadicDiff_def, if_pos rfl]
    calc (Finset.univ.image (fun v => a v - a (σ (S - 0 - 1) v))).card
        ≤ (Finset.univ : Finset (Fin N)).card := Finset.card_image_le
      _ = N := by simp [Fintype.card_fin]
  · -- the norm bound on elements of `B k`
    intro k _ b hb
    rw [dyadicDiff_def] at hb
    rw [Finset.mem_image] at hb
    obtain ⟨v, _, hv⟩ := hb
    rw [← hv]
    exact hnet (S - k - 1) (by omega) v
  · -- the telescoping decomposition
    intro i
    have hsum := Finset.sum_range_sub' (fun k => a (dyadicChain N S σ k i)) S
    rw [hsum]
    rw [dyadicChain_zero_apply]
    exact (add_sub_cancel (a (dyadicChain N S σ S i)) (a i)).symm

end

end Commons.Analysis.Fourier