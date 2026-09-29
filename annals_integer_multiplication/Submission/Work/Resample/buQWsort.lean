import Mathlib

/-!
# `Work.Resample.buQWsort`

If `ys` is a permutation of `xs`, sorted by the key `key : α → ℕ` (strictly increasing along `ys`),
with pairwise distinct keys on `xs`, and the keys of `xs` cover every `ℓ < s`, then the `ℓ`-th entry
of `ys` (for `ℓ < s`) is an element of `xs` whose key is exactly `ℓ`.

The mathematical content is the combinatorial fact about strictly increasing lists of naturals: a
strictly increasing list of naturals whose range contains `{0, …, s-1}` starts with `0, 1, …, s-1`.
This is used by the `B̃`-resampling word, where `ys` is the (sorted) index list of the window
entries and `key` records the destination slot.
-/

namespace Work.Resample

/-- A strictly increasing list of naturals containing every `k < s` has `k`-th entry `k`, as long
as it is long enough (here: at least `s`). -/
lemma getD_eq_of_cov {l : List ℕ} {s : ℕ}
    (hs : l.Pairwise (· < ·)) (hcov : ∀ k < s, k ∈ l) (hlen : s ≤ l.length) :
    ∀ k < s, l.getD k 0 = k := by
  have hle : ∀ k (hk : k < l.length), k ≤ l[k] := by
    intro k
    induction k with
    | zero => intro _; exact Nat.zero_le _
    | succ k ih =>
        intro hk
        have hk' : k < l.length := Nat.lt_of_succ_lt hk
        have hmono := List.pairwise_iff_getElem.mp hs
        have hlt : l[k] < l[k+1] := hmono k (k+1) hk' hk (Nat.lt_succ_self k)
        have := ih hk'
        omega
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hk
    have hkltlen : k < l.length := lt_of_lt_of_le hk hlen
    rw [List.getD_eq_getElem l 0 hkltlen]
    have hkle : k ≤ l[k] := hle k hkltlen
    rcases lt_or_eq_of_le hkle with hlt | heq
    · obtain ⟨j, hj, hjeq⟩ := List.mem_iff_getElem.mp (hcov k hk)
      have hjlt : j < k := by
        by_contra hge
        push Not at hge
        rcases lt_or_eq_of_le hge with hkgt | hkeq
        · have hh := (List.pairwise_iff_getElem.mp hs) k j hkltlen hj hkgt
          rw [hjeq] at hh
          omega
        · have hkk : l[k] = k := hkeq.symm ▸ hjeq
          omega
      have hjs : j < s := lt_trans hjlt hk
      have hih : l.getD j 0 = j := ih j hjlt hjs
      rw [List.getD_eq_getElem l 0 hj] at hih
      omega
    · exact heq.symm

/-- A nodup list of naturals containing every `k < s` has length at least `s`. -/
lemma le_length_of_cov {l : List ℕ} {s : ℕ} (hnd : l.Nodup)
    (hcov : ∀ k < s, k ∈ l) : s ≤ l.length := by
  have hsub : Finset.range s ⊆ l.toFinset := by
    intro k hk
    rw [Finset.mem_range] at hk
    rw [List.mem_toFinset]
    exact hcov k hk
  have := Finset.card_le_card hsub
  rwa [Finset.card_range, List.toFinset_card_of_nodup hnd] at this

theorem buQWsort {α : Type} [Inhabited α] (key : α → ℕ) (xs ys : List α) (s : ℕ)
    (hperm : ys.Perm xs) (hsort : ys.Pairwise fun a b => key a < key b)
    (hnd : (xs.map key).Nodup)
    (hcov : ∀ ℓ < s, ∃ x ∈ xs, key x = ℓ) :
    ∀ ℓ < s, ys.getD ℓ default ∈ xs ∧ key (ys.getD ℓ default) = ℓ := by
  have hperm_map : (ys.map key).Perm (xs.map key) := hperm.map key
  have hnd_ys : (ys.map key).Nodup := (hperm_map.nodup_iff).mpr hnd
  have hsorted : (ys.map key).Pairwise (· < ·) := by
    rw [List.pairwise_map]
    exact hsort
  have hcov_ys : ∀ k < s, k ∈ ys.map key := by
    intro k hk
    obtain ⟨x, hx, hkx⟩ := hcov k hk
    exact List.mem_map.mpr ⟨x, (hperm.mem_iff).mpr hx, hkx⟩
  have hlen : s ≤ (ys.map key).length := le_length_of_cov hnd_ys hcov_ys
  intro ℓ hℓ
  have hℓlen : ℓ < ys.length := by
    have h1 : ℓ < (ys.map key).length := lt_of_lt_of_le hℓ hlen
    simpa using h1
  have hget : (ys.map key).getD ℓ 0 = ℓ := getD_eq_of_cov hsorted hcov_ys hlen ℓ hℓ
  have hmapeq : (ys.map key).getD ℓ 0 = key (ys.getD ℓ default) := by
    rw [List.getD_eq_getElem (ys.map key) 0 (by simpa using hℓlen)]
    rw [List.getD_eq_getElem ys default hℓlen]
    exact List.getElem_map key
  constructor
  · have : ys.getD ℓ default ∈ ys := by
      rw [List.getD_eq_getElem ys default hℓlen]
      exact List.getElem_mem hℓlen
    exact (hperm.mem_iff).mp this
  · rw [← hmapeq]; exact hget

end Work.Resample
