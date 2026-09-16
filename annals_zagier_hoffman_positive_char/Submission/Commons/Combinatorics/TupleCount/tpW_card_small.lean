import Mathlib
import Submission.Commons.Combinatorics.TupleCount.card_eq_composition
import Submission.Commons.Combinatorics.TupleCount.tpW_rec_large
import Submission.Commons.Combinatorics.TupleCount.tpW_rec_small

open scoped BigOperators
set_option autoImplicit false
set_option linter.unusedVariables false

namespace Commons.Combinatorics.TupleCount

/-- Characterization of the compositions of `w ≤ q` with a block divisible by `q`: this happens
exactly for the single-block composition `[q]`, which can only exist when `w = q`. -/
theorem comp_bad_iff (q w : ℕ) (hq : 2 ≤ q) (hw0 : 0 < w) (hwq : w ≤ q)
    (c : Composition w) :
    (∃ b ∈ c.blocks, q ∣ b) ↔ w = q ∧ c = Composition.single w hw0 := by
  constructor
  · rintro ⟨b, hb, hdvd⟩
    have hbpos : 0 < b := c.blocks_pos hb
    have hble : b ≤ w := c.blocks_le hb
    have hqb : q ≤ b := Nat.le_of_dvd hbpos hdvd
    have hwq' : w = q := by omega
    have hbw : b = w := by omega
    refine ⟨hwq', ?_⟩
    by_contra hne
    have hlt : ∀ i : Fin c.length, c.blocksFun i < w :=
      (Composition.ne_single_iff hw0).mp hne
    have hmem : b ∈ List.ofFn c.blocksFun := by
      rw [Composition.ofFn_blocksFun]; exact hb
    obtain ⟨i, hi⟩ := List.mem_ofFn.mp hmem
    have := hlt i
    omega
  · rintro ⟨hwq', hsingle⟩
    refine ⟨q, ?_, dvd_refl q⟩
    subst hsingle
    rw [Composition.single_blocks, List.mem_singleton]
    exact hwq'.symm

/-- A composition of `w ≤ q` has all its blocks coprime to `q` (i.e. none divisible by `q`)
unless it is the single-block composition `[q]` (possible only for `w = q`). -/
theorem comp_good_iff (q w : ℕ) (hq : 2 ≤ q) (hw0 : 0 < w) (hwq : w ≤ q)
    (c : Composition w) :
    (∀ b ∈ c.blocks, ¬ q ∣ b) ↔ ¬ (w = q ∧ c = Composition.single w hw0) := by
  have key := comp_bad_iff q w hq hw0 hwq c
  constructor
  · intro hg hR
    obtain ⟨b, hb, hdvd⟩ := key.mpr hR
    exact hg b hb hdvd
  · intro hR b hb hdvd
    exact hR (key.mp ⟨b, hb, hdvd⟩)

/-- **Counting `q`-avoiding compositions of small weight.**  For `1 ≤ w ≤ q`, the number of
compositions of `w` none of whose blocks is divisible by `q` equals `2 ^ (w - 1)`, except that
the single-block composition `[q]` has to be removed in the boundary case `w = q`. -/
theorem comp_card_small (q w : ℕ) (hq : 2 ≤ q) (hw : 1 ≤ w) (hwq : w ≤ q) :
    Nat.card {c : Composition w // ∀ b ∈ c.blocks, ¬ q ∣ b}
      = 2 ^ (w - 1) - (if w = q then 1 else 0) := by
  have hw0 : 0 < w := by omega
  by_cases hwq' : w = q
  · -- boundary case `w = q`: the only bad composition is `[q]`
    have hiff : ∀ c : Composition w,
        ((∀ b ∈ c.blocks, ¬ q ∣ b) ↔ c ≠ Composition.single w hw0) := by
      intro c
      have key := comp_bad_iff q w hq hw0 hwq c
      constructor
      · intro hc heq
        have hmem : q ∈ c.blocks := by
          rw [heq, Composition.single_blocks, List.mem_singleton]
          exact hwq'.symm
        exact hc q hmem (dvd_refl q)
      · intro hc b hb hdvd
        exact hc (key.mp ⟨b, hb, hdvd⟩).2
    have hcard : Nat.card {c : Composition w // c ≠ Composition.single w hw0}
        = 2 ^ (w - 1) - 1 := by
      rw [Nat.card_eq_fintype_card,
        Fintype.card_subtype_compl (fun c : Composition w => c = Composition.single w hw0),
        Fintype.card_subtype_eq, composition_card]
    rw [Nat.card_congr (Equiv.subtypeEquivRight hiff), hcard, if_pos hwq']
  · -- case `w ≠ q`, hence `w < q`: every composition is good
    have hiff : ∀ c : Composition w, (∀ b ∈ c.blocks, ¬ q ∣ b) := by
      intro c
      rw [comp_good_iff q w hq hw0 hwq c]
      rintro ⟨h, _⟩
      exact absurd h hwq'
    have hcard : Nat.card {c : Composition w // ∀ b ∈ c.blocks, ¬ q ∣ b} = 2 ^ (w - 1) := by
      rw [Nat.card_congr (Equiv.subtypeUnivEquiv hiff), Nat.card_eq_fintype_card, composition_card]
    rw [hcard, if_neg hwq', Nat.sub_zero]

theorem tpW_card_small (q w : ℕ) (hq : 2 ≤ q) (hw : 1 ≤ w) (hwq : w ≤ q) :
    Nat.card {x : Σ r : Fin (2 * q), Fin r → Fin (2 * q) //
        (∀ j, 1 ≤ ((x.2 j : Fin (2 * q)) : ℕ)) ∧
        (∀ j, ¬ (q ∣ ((x.2 j : Fin (2 * q)) : ℕ))) ∧
        (∑ j, ((x.2 j : Fin (2 * q)) : ℕ)) = w}
      = 2 ^ (w - 1) - (if w = q then 1 else 0) := by
  have hlt : w < 2 * q := by omega
  rw [card_eq_composition q w hlt]
  exact comp_card_small q w hq hw hwq

end Commons.Combinatorics.TupleCount
