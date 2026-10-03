import Mathlib
import Submission.Work.OROneRel.exists_common_power

/-!
# The doubled word being a power

Let `L` be a list of letters (elements of `α × Bool`).  Write `dbl L` for the word obtained
from `L` by doubling every letter, i.e. `dbl L = (L.map (fun p => [p, p])).flatten`.

The main result of this file, `doubledWord_rotate_or_replicate`, says that if `dbl L` is a
`k`-th power (`k ≥ 2`) of some word `B`, then either `L` admits a nontrivial rotation
fixing it, or `L` is a constant word.

The combinatorial content is the following.  If `W = dbl L = B^k` with `m = |B|`, then
`W[i] = B[i % m]` and `W[2j] = W[2j+1] = L[j]`, so that for every `j < |L|`

`L[j] = B[(2j) % m] = B[(2j+1) % m]`.

Viewing `L[j]` as `B[2j mod m]`, a cyclic shift of `L` by `s` does not change `L` as soon as
`2s ≡ 0 (mod m)`: indeed `2(j + s) ≡ 2j` and the "wrap-around" `2|L| t` is a multiple of `m`
because `2|L| = k m`.  Hence `s := m / gcd(m,2)` (i.e. `m/2` for even `m`, `m` for odd `m`) is a
period as long as `s < |L|`.  The two exceptional cases are `m = 1` (covered by the odd case,
`s = 1`) and `m` odd with `k = 2` (then `m = |L|` and, since `2` is invertible modulo the odd
number `m`, the relations `B[2j] = B[2j+1]` link all entries of `B`, so `B` and `L` are
constant).
-/

namespace Work.OROneRel

universe u

variable {α : Type u}

/-! ## Access lemmas for the doubled word -/

/-- The length of the doubled word is twice the length. -/
theorem length_flatten_map_pair {β : Type*} (L : List β) :
    ((L.map (fun p => [p, p])).flatten).length = 2 * L.length := by
  induction L with
  | nil => simp
  | cons p L ih => simp [List.map_cons, List.flatten_cons, ih]; ring

/-- The `i`-th entry of the doubled word is the `(i/2)`-th entry of the original word. -/
theorem getElem?_flatten_map_pair {β : Type*} (L : List β) (i : ℕ) :
    ((L.map (fun p => [p, p])).flatten)[i]? = L[i / 2]? := by
  induction L generalizing i with
  | nil => simp
  | cons p L ih =>
    rw [List.map_cons, List.flatten_cons]
    rcases i with _ | _ | k
    · simp
    · simp
    · rw [List.getElem?_append_right (by simp : [p, p].length ≤ k + 2)]
      simp only [List.length_cons, List.length_nil]
      rw [show k + 2 - (0 + 1 + 1) = k from by omega,
          show (k + 1 + 1) / 2 = (k + 2) / 2 from by omega,
          show (k + 2) / 2 = k / 2 + 1 from by omega,
          ih k, List.getElem?_cons_succ]

/-! ## Two arithmetic helpers -/

/-- If `2n = k·m` and `2s ≡ 0 (mod m)`, then shifting the index `i` by `s` modulo `n` does not
change `2i` modulo `m`. -/
theorem two_mul_mod_eq {n k m i s : ℕ} (hnm : 2 * n = k * m) (hs : 2 * s % m = 0) :
    (2 * ((i + s) % n)) % m = (2 * i) % m := by
  have hmain : (2 * (i + s)) % m = (2 * ((i + s) % n)) % m := by
    have h1 : 2 * (i + s) = 2 * ((i + s) % n) + m * (k * ((i + s) / n)) := by
      conv_lhs => rw [← Nat.div_add_mod (i + s) n]
      calc 2 * (n * ((i + s) / n) + (i + s) % n)
          = 2 * (n * ((i + s) / n)) + 2 * ((i + s) % n) := by ring
        _ = (2 * n) * ((i + s) / n) + 2 * ((i + s) % n) := by ring
        _ = (k * m) * ((i + s) / n) + 2 * ((i + s) % n) := by rw [hnm]
        _ = 2 * ((i + s) % n) + m * (k * ((i + s) / n)) := by ring
    rw [h1, Nat.add_mul_mod_self_left]
  have h2 : (2 * (i + s)) % m = (2 * i) % m := by
    have : 2 * (i + s) = 2 * i + 2 * s := by ring
    rw [this, Nat.add_mod, hs, Nat.add_zero, Nat.mod_mod]
  exact hmain.symm.trans h2

/-- If `m` is odd and `u < m`, there is a `j < m` with `2j ≡ u (mod m)`. -/
theorem exists_mul_two_mod_eq_of_odd {m u : ℕ} (hm : m % 2 = 1) (hu : u < m) :
    ∃ j : ℕ, j < m ∧ (2 * j) % m = u := by
  have hmpos : 0 < m := by omega
  refine ⟨(u * ((m + 1) / 2)) % m, Nat.mod_lt _ hmpos, ?_⟩
  have hinv : 2 * ((m + 1) / 2) = m + 1 := by
    have := Nat.div_add_mod m 2
    omega
  rw [Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod]
  rw [show 2 * (u * ((m + 1) / 2)) = u * (2 * ((m + 1) / 2)) from by ring, hinv,
      Nat.mul_add, Nat.mul_one, Nat.mul_comm u m, Nat.mul_add_mod_self_left,
      Nat.mod_eq_of_lt hu]

/-! ## The main theorem -/

theorem doubledWord_rotate_or_replicate {α : Type u} (L : List (α × Bool)) (hL : 2 ≤ L.length)
    {k : ℕ} (hk : 2 ≤ k) {B : List (α × Bool)}
    (h : (L.map (fun p : α × Bool => [p, p])).flatten = (List.replicate k B).flatten) :
    (∃ s : ℕ, 0 < s ∧ s < L.length ∧ L.rotate s = L) ∨
      (∃ p : α × Bool, L = List.replicate L.length p) := by
  -- Length relation `2 |L| = k |B|`.
  have hlen : 2 * L.length = k * B.length := by
    have h1 := congrArg List.length h
    rwa [length_flatten_map_pair, length_flatten_replicate] at h1
  have hmpos : 0 < B.length := by
    rcases Nat.eq_zero_or_pos B.length with h0 | h0
    · rw [h0, mul_zero] at hlen; omega
    · exact h0
  -- Entry relations of `L` with the blocks of `B`.
  have hLK : ∀ j, j < L.length → L[j]? = B[(2 * j) % B.length]? := by
    intro j hj
    have h1 : ((L.map (fun p => [p, p])).flatten)[2 * j]? = L[j]? := by
      rw [getElem?_flatten_map_pair]
      congr 1
      omega
    have h2 : ((L.map (fun p => [p, p])).flatten)[2 * j]? = B[(2 * j) % B.length]? := by
      rw [h]
      apply getElem?_flatten_replicate
      rw [length_flatten_replicate]
      omega
    rw [← h1, h2]
  have hLK1 : ∀ j, j < L.length → L[j]? = B[(2 * j + 1) % B.length]? := by
    intro j hj
    have h1 : ((L.map (fun p => [p, p])).flatten)[2 * j + 1]? = L[j]? := by
      rw [getElem?_flatten_map_pair]
      congr 1
      omega
    have h2 : ((L.map (fun p => [p, p])).flatten)[2 * j + 1]? = B[(2 * j + 1) % B.length]? := by
      rw [h]
      apply getElem?_flatten_replicate
      rw [length_flatten_replicate]
      omega
    rw [← h1, h2]
  -- A shift `s` with `2s ≡ 0 (mod |B|)` and `s < |L|` is a period of `L`.
  have rotate_of : ∀ s, 0 < s → (2 * s) % B.length = 0 → s < L.length → L.rotate s = L := by
    intro s _ hs2 hsn
    apply List.ext_getElem?
    intro i
    by_cases hi : i < L.length
    · rw [List.getElem?_rotate (l := L) (n := s) (m := i) hi,
          hLK ((i + s) % L.length) (Nat.mod_lt _ (by omega)), hLK i hi]
      congr 1
      exact two_mul_mod_eq hlen hs2
    · have h1 : (L.rotate s)[i]? = none :=
        List.getElem?_eq_none (by rw [List.length_rotate]; omega)
      have h2 : L[i]? = none := List.getElem?_eq_none (le_of_not_gt hi)
      rw [h1, h2]
  -- Case analysis on the parity of `|B|`.
  by_cases hpar : B.length % 2 = 0
  · -- `|B|` even: `s = |B| / 2` is a nontrivial period.
    have h2s : 2 * (B.length / 2) = B.length := by
      have := Nat.div_add_mod B.length 2
      omega
    have hs0 : 0 < B.length / 2 := by omega
    have hsn : B.length / 2 < L.length := by
      have h3 : 2 * L.length = 2 * (k * (B.length / 2)) := by
        rw [hlen]
        conv_lhs => rw [← h2s]
        ring
      have h4 : L.length = k * (B.length / 2) := Nat.mul_left_cancel (by norm_num) h3
      rw [h4]
      simpa using Nat.mul_lt_mul_of_pos_right (by omega : 1 < k) hs0
    exact Or.inl ⟨B.length / 2, hs0, hsn, rotate_of _ hs0 (by rw [h2s, Nat.mod_self]) hsn⟩
  · have hod : B.length % 2 = 1 := by omega
    by_cases hk2 : k = 2
    · -- `|B| = |L|` odd and `k = 2`: `L` is constant.
      have hmn : L.length = B.length := by
        have : 2 * L.length = 2 * B.length := by rw [hlen, hk2]
        exact Nat.mul_left_cancel (by norm_num) this
      -- `B` moves by one along its entries.
      have hstep : ∀ u, u < B.length → B[u]? = B[(u + 1) % B.length]? := by
        intro u hu
        obtain ⟨j, hjlt, hj⟩ := exists_mul_two_mod_eq_of_odd hod hu
        have hjn : j < L.length := by omega
        have h1 : L[j]? = B[u]? := by rw [hLK j hjn, hj]
        have h2 : L[j]? = B[(u + 1) % B.length]? := by
          rw [hLK1 j hjn]
          congr 1
          rw [Nat.add_mod, hj, Nat.mod_eq_of_lt (by omega : 1 < B.length)]
        rw [← h1, h2]
      have hconstB : ∀ u, u < B.length → B[u]? = B[0]? := by
        intro u
        induction u with
        | zero => intro _; rfl
        | succ u ih =>
          intro hu
          have hu' : u < B.length := by omega
          have hs := hstep u hu'
          rw [Nat.mod_eq_of_lt hu] at hs
          rw [← hs]
          exact ih hu'
      have hL0 : L[0]? = B[0]? := by
        rw [hLK 0 (by omega)]
        norm_num
      have hconstL : ∀ j, j < L.length → L[j]? = L[0]? := by
        intro j hj
        rw [hLK j hj, hL0]
        exact hconstB ((2 * j) % B.length) (Nat.mod_lt _ hmpos)
      have h0 : 0 < L.length := by omega
      refine Or.inr ⟨L[0]'(h0), ?_⟩
      apply List.ext_getElem?
      intro i
      by_cases hi : i < L.length
      · rw [hconstL i hi, List.getElem?_replicate, if_pos hi]
        exact List.getElem?_eq_getElem h0
      · rw [List.getElem?_eq_none (le_of_not_gt hi), List.getElem?_replicate, if_neg hi]
    · -- `|B|` odd and `k ≥ 3`: `s = |B|` is a nontrivial period.
      have hk3 : 3 ≤ k := by omega
      have hsg : B.length < L.length := by
        have h3 : 3 * B.length ≤ 2 * L.length := by
          rw [hlen]
          exact Nat.mul_le_mul_right B.length hk3
        omega
      refine Or.inl ⟨B.length, hmpos, hsg, rotate_of B.length hmpos ?_ hsg⟩
      rw [show 2 * B.length = B.length * 2 from by ring, Nat.mul_mod_right]

end Work.OROneRel
