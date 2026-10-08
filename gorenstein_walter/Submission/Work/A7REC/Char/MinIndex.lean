/-
Area `A7REC`, file `Char/MinIndex.lean`: the minimal-index vocabulary used by the decomposition of
`Work.A7REC.Char.indexSevenOfSimple2520` (a simple group of order `2520` has a subgroup of
index `7`, i.e. is `A₇`).

## The reduction (all elementary)

Let `G` be simple of order `2520` and suppose, for contradiction, that `G` has no subgroup of
index `7`.  Write `m` for the minimal index of a proper subgroup of `G`.

* `6 < m`: a proper subgroup of index `≤ 6` would give a faithful (simplicity) permutation
  representation of degree `≤ 6`, hence `|G| ≤ 6! = 720 < 2520`
  (`Work.A7REC.Char.no_small_index`).
* `m ∣ 2520`: `|G| = m · |H|` for a subgroup of index `m`
  (`Subgroup.card_mul_index`).
* `m ≤ 70`: the number `n₃` of Sylow `3`-subgroups satisfies `m ≤ n₃` (minimality), and
  `n₃ ∈ {10, 28, 40, 70}`:  `n₃ ≠ 4` (a faithful action of degree `4` is too small),
  `n₃ ≠ 7` (then the normalizer of a Sylow `3`-subgroup is a subgroup of index `7`), and
  `n₃ ≠ 280` (a self-normalizing Sylow `3`-subgroup gives a normal `3`-complement by Burnside's
  transfer theorem, contradicting simplicity).  Hence `m ∈ {7,…,70}`.

So the remaining cases are `m ∈ {7,8,9,10,12,14,15,18,20,21,24,28,30,35,36,40,42,45,56,60,63,70}`,
and the theorem follows as soon as `m ≠ 7` is excluded.  This file only contains the vocabulary
(`MinIndex`) and the two elementary lemmas; the case exclusions live in the sibling files
`Case8.lean`, …, `Case70.lean`.
-/
import Mathlib

namespace Work.A7REC.Char

open Subgroup

/-- **`m` is the minimal index of a proper subgroup of `G`.**  The conjunction of
"some proper subgroup has index `m`" (existence) and "every proper subgroup has index `≥ m`"
(minimality). -/
def MinIndex (G : Type*) [Group G] [Finite G] (m : ℕ) : Prop :=
  (∃ H : Subgroup G, H.index = m) ∧ ∀ K : Subgroup G, K ≠ ⊤ → m ≤ K.index

/-- **A finite simple group of order `2520` has no proper subgroup of index `≤ 6`.**

Indeed, if `H` is proper of index `d ≤ 6`, the action of `G` on the `d` cosets of `H` has kernel
`⊴ G` contained in `H`; simplicity forces the kernel to be trivial, so `G` embeds in the symmetric
group on `d ≤ 6` letters, of order `d! ≤ 720 < 2520`. -/
theorem no_small_index {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
    (hcard : Nat.card G = 2520) (H : Subgroup G) (hH : H ≠ ⊤) : 6 < H.index := by
  rcases Nat.lt_or_ge 6 H.index with h | h
  · exact h
  exfalso
  have hker_le : (MulAction.toPermHom G (G ⧸ H)).ker ≤ H := by
    rw [← Subgroup.normalCore_eq_ker]
    exact Subgroup.normalCore_le H
  have hker : (MulAction.toPermHom G (G ⧸ H)).ker = ⊥ := by
    rcases Subgroup.Normal.eq_bot_or_eq_top (MulAction.toPermHom G (G ⧸ H)).ker with h' | h'
    · exact h'
    · exact absurd (top_le_iff.mp (h' ▸ hker_le)) hH
  have hinj : Function.Injective (MulAction.toPermHom G (G ⧸ H)) :=
    (MonoidHom.ker_eq_bot_iff _).mp hker
  haveI : Finite (G ⧸ H) := Quotient.finite _
  have h1 : Nat.card G ≤ Nat.card (Equiv.Perm (G ⧸ H)) :=
    Nat.card_le_card_of_injective _ hinj
  rw [hcard, Nat.card_perm, ← Subgroup.index_eq_card H] at h1
  have h2 : (H.index).factorial ≤ 720 := (Nat.factorial_le h).trans (by norm_num)
  omega

/-- The index of a proper subgroup divides `|G|`. -/
theorem dvd_card_of_minIndex {G : Type*} [Group G] [Finite G] {m : ℕ}
    (h : MinIndex G m) (hcard : Nat.card G = 2520) : m ∣ 2520 := by
  obtain ⟨H, hH⟩ := h.1
  rw [← hH, ← hcard]
  exact Subgroup.index_dvd_card H

end Work.A7REC.Char
