import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.BigOperators.Group.Finset

namespace Commons.Combinatorics.QPowerRec

open Finset

/-- For `q ≥ 2` and any `j`, we have `j ≤ q^j`. -/
lemma le_pow_self_of_two_le {q : ℕ} (hq : 2 ≤ q) (j : ℕ) : j ≤ q ^ j :=
  (Nat.lt_two_pow_self (n := j)).le.trans (Nat.pow_le_pow_left hq j)

variable {R : Type*} [CommRing R]

/-- The summand of the expansion: over tuples `a : Fin m → Fin B`, take `∏ u (a i)` when
`∑ q ^ (a i) = N`, else `0`. -/
private noncomputable def qFm (q : ℕ) (u : ℕ → R) (B m N : ℕ) : R :=
  ∑ a : Fin m → Fin B,
    (if (∑ i, q ^ ((a i : ℕ))) = N then ∏ i, u ((a i : ℕ)) else 0)

/-- The full expansion sum over tuples of all lengths `0..N`. -/
private noncomputable def qSeq (q : ℕ) (u : ℕ → R) (B N : ℕ) : R :=
  ∑ m ∈ Finset.range (N + 1), qFm q u B m N

/-- A tuple contributes a length at most its total weight. -/
private lemma card_le_weight {q : ℕ} (hq : 2 ≤ q) {m : ℕ} (a : Fin m → ℕ) :
    m ≤ ∑ i, q ^ a i := by
  calc m = ∑ _i : Fin m, (1 : ℕ) := by simp
    _ ≤ ∑ i : Fin m, q ^ a i := by
        apply Finset.sum_le_sum
        intro i _
        exact Nat.one_le_pow (a i) q (by omega)

/-- Tuples whose weight already exceeds the target contribute nothing. -/
private lemma qFm_eq_zero_of_lt {q : ℕ} (hq : 2 ≤ q) {u : ℕ → R} {B m N : ℕ} (h : N < m) :
    qFm q u B m N = 0 := by
  unfold qFm
  apply Finset.sum_eq_zero
  intro a _
  rw [if_neg]
  intro hc
  have := card_le_weight hq (fun i => (a i : ℕ))
  omega

/-- The empty-tuple term. -/
private lemma qFm_zero {q : ℕ} {u : ℕ → R} {B N : ℕ} :
    qFm q u B 0 N = if N = 0 then 1 else 0 := by
  unfold qFm
  rw [Fintype.sum_unique]
  simp only [Fin.sum_univ_zero, Fin.prod_univ_zero]
  rcases eq_or_ne N 0 with hN | hN
  · subst hN; simp
  · rw [if_neg hN]; exact if_neg (Ne.symm hN)


/-- The recursion step: pull the first entry off a tuple. -/
private lemma qFm_succ {q : ℕ} {u : ℕ → R} {B n N : ℕ} :
    qFm q u B (n + 1) N =
      ∑ j : Fin B,
        (if q ^ (j : ℕ) ≤ N then u (j : ℕ) * qFm q u B n (N - q ^ (j : ℕ)) else 0) := by
  have hsum : ∀ (j : Fin B) (b : Fin n → Fin B),
      (∑ i : Fin (n + 1), q ^ (((Fin.cons (α := fun _ => Fin B) j b i : Fin B) : ℕ)))
        = q ^ (j : ℕ) + ∑ i : Fin n, q ^ ((b i : ℕ)) := by
    intro j b
    rw [Fin.sum_univ_succ]
    simp
  have hprod : ∀ (j : Fin B) (b : Fin n → Fin B),
      (∏ i : Fin (n + 1), u (((Fin.cons (α := fun _ => Fin B) j b i : Fin B) : ℕ)))
        = u (j : ℕ) * ∏ i : Fin n, u ((b i : ℕ)) := by
    intro j b
    rw [Fin.prod_univ_succ]
    simp
  have step1 : qFm q u B (n + 1) N
      = ∑ p : Fin B × (Fin n → Fin B),
          (if (∑ i : Fin (n + 1), q ^ (((Fin.cons (α := fun _ => Fin B) p.1 p.2 i : Fin B) : ℕ))) = N
            then ∏ i : Fin (n + 1), u (((Fin.cons (α := fun _ => Fin B) p.1 p.2 i : Fin B) : ℕ)) else 0) := by
    unfold qFm
    rw [← Equiv.sum_comp (Fin.consEquiv (fun _ : Fin (n + 1) => Fin B))]
    simp only [Fin.consEquiv_apply]
  rw [step1, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro j _
  simp only [hsum j, hprod j]
  unfold qFm
  by_cases h : q ^ (j : ℕ) ≤ N
  · rw [if_pos h, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro b _
    by_cases hb : (∑ i : Fin n, q ^ ((b i : ℕ))) = N - q ^ (j : ℕ)
    · simp [hb, Nat.add_sub_of_le h]
    · rw [if_neg hb, mul_zero, if_neg (by omega)]
  · rw [if_neg h]
    apply Finset.sum_eq_zero
    intro b _
    rw [if_neg (by omega)]

/-- Reindexing a sum over `Fin B` with a bound depending only on `N < B`. -/
private lemma sum_FinB_ite_eq_sum_filter {q : ℕ} (hq : 2 ≤ q) {B N : ℕ} (hB : N + 1 ≤ B)
    (w : ℕ → R) :
    (∑ j : Fin B, (if q ^ (j : ℕ) ≤ N then w (j : ℕ) else 0))
      = ∑ j ∈ (Finset.range (N + 1)).filter (fun j => q ^ j ≤ N), w j := by
  rw [← Finset.sum_filter]
  rw [← Finset.sum_image (f := w) (g := Fin.val)
        (s := Finset.univ.filter (fun j : Fin B => q ^ (j : ℕ) ≤ N))
        (fun a _ b _ h => Fin.val_injective h)]
  congr 1
  ext k
  simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_range]
  constructor
  · rintro ⟨j, hj, rfl⟩
    refine ⟨?_, hj⟩
    have := le_pow_self_of_two_le hq j
    omega
  · rintro ⟨hk, hkq⟩
    refine ⟨⟨k, by omega⟩, ?_, rfl⟩
    simpa using hkq

/-- The range-`N` partial sum agrees with the full sequence sum when the weight exceeds the length
of every contributing tuple. -/
private lemma qSum_range_sub {q : ℕ} (hq : 2 ≤ q) {u : ℕ → R} {B N j : ℕ} (hj : q ^ j ≤ N) :
    ∑ m ∈ Finset.range N, qFm q u B m (N - q ^ j) = qSeq q u B (N - q ^ j) := by
  unfold qSeq
  symm
  apply Finset.sum_subset
  · intro x hx
    simp only [Finset.mem_range] at hx ⊢
    have h1 : 1 ≤ q ^ j := Nat.one_le_pow j q (by omega)
    have hN : 1 ≤ N := le_trans h1 hj
    omega
  · intro x hx hnx
    simp only [Finset.mem_range] at hx hnx
    exact qFm_eq_zero_of_lt hq (by omega)

/-- The recursion satisfied by the expansion sum. -/
private lemma qSeq_rec {q : ℕ} (hq : 2 ≤ q) {u : ℕ → R} {B n : ℕ} (hB : n + 1 ≤ B)
    (hn : 1 ≤ n) :
    qSeq q u B n =
      ∑ j ∈ (Finset.range (n + 1)).filter (fun j => q ^ j ≤ n),
        u j * qSeq q u B (n - q ^ j) := by
  have key : qSeq q u B n
      = ∑ j : Fin B,
          (if q ^ (j : ℕ) ≤ n then u (j : ℕ) * qSeq q u B (n - q ^ (j : ℕ)) else 0) := by
    rw [show qSeq q u B n = ∑ m ∈ Finset.range (n + 1), qFm q u B m n from rfl]
    rw [Finset.sum_range_succ', qFm_zero]
    rw [if_neg (by omega : ¬ (n = 0)), add_zero]
    simp only [qFm_succ]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    by_cases h : q ^ (j : ℕ) ≤ n
    · rw [if_pos h, ← qSum_range_sub hq h, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro m _
      rw [if_pos h]
    · rw [if_neg h]
      apply Finset.sum_eq_zero
      intro m _
      rw [if_neg h]
  rw [key]
  exact sum_FinB_ite_eq_sum_filter hq hB (fun j => u j * qSeq q u B (n - q ^ j))

/-- Expansion of a `q`-power recursion as a sum over ordered tuples.

If `q ≥ 2`, `c 0 = 1` and `c n = ∑_{j : q^j ≤ n} u j * c (n - q^j)` for all `n ≥ 1`, then `c N` is the
sum, over all finite sequences `(a_0, ..., a_{m-1})` of natural numbers with `∑_i q ^ (a_i) = N`, of
`∏_i u (a_i)`.  The bound `B` on the entries is irrelevant as long as `B ≥ N + 1` (any entry of such a
sequence is `≤ N`). -/
theorem seq_rec_expand {R : Type*} [CommRing R] (q : ℕ) (hq : 2 ≤ q) (u c : ℕ → R)
    (h0 : c 0 = 1)
    (hrec : ∀ n, 1 ≤ n →
      c n = ∑ j ∈ (Finset.range (n + 1)).filter (fun j => q ^ j ≤ n), u j * c (n - q ^ j))
    (N B : ℕ) (hB : N + 1 ≤ B) :
    c N = ∑ m ∈ Finset.range (N + 1), ∑ a : Fin m → Fin B,
      (if (∑ i, q ^ ((a i : ℕ))) = N then ∏ i, u ((a i : ℕ)) else 0) := by
  have main : ∀ K, K + 1 ≤ B → c K = qSeq q u B K := by
    intro K
    induction K using Nat.strong_induction_on with
    | _ K IH =>
      intro hK
      rcases Nat.eq_zero_or_pos K with hK0 | hKpos
      · subst hK0
        rw [h0]
        rw [show qSeq q u B 0 = ∑ m ∈ Finset.range 1, qFm q u B m 0 from rfl]
        rw [Finset.sum_range_one, qFm_zero]
        simp
      · have hK1 : 1 ≤ K := by omega
        rw [hrec K hK1, qSeq_rec (q := q) (u := u) (B := B) (n := K) hq hK hK1]
        apply Finset.sum_congr rfl
        intro j hj
        have hlt : K - q ^ j < K := Nat.sub_lt hKpos (Nat.pow_pos (show 0 < q by omega))
        rw [IH (K - q ^ j) hlt (by have h1 : 1 ≤ q ^ j := Nat.one_le_pow j q (by omega); omega)]
  simpa only [qSeq, qFm] using main N hB

end Commons.Combinatorics.QPowerRec