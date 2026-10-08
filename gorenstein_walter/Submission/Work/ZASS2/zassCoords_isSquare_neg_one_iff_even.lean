import Mathlib
import Submission.Work.ZASS.Leaf9

/-!
# `IsSquare (-1)` in the coordinate field of a Zassenhaus group

Let `C : Work.GW2.ZassCoords G X inf zero U` be the field coordinates attached to a
Zassenhaus action (`Work.GW2.ZassHyps2 G X q`, so `Nat.card X = q + 1`).  Since
`C.Θ : X ≃ Option C.E` is an equivalence and `Nat.card (Option E) = Nat.card E + 1`, the
finite field `C.E` has exactly `q` elements.  The hypothesis `(2 : C.E) ≠ 0` says that the
characteristic of `C.E` is odd, so `q = #C.E` is odd, and

`IsSquare (-1 : C.E) ↔ Fintype.card C.E % 4 ≠ 3 ↔ Even ((q - 1) / 2)`:

the first equivalence is `FiniteField.isSquare_neg_one_iff`, the second is the elementary
fact that for odd `q` the number `(q - 1)/2` is even exactly when `q ≡ 1 (mod 4)`.
-/

namespace Work.ZASS2

/-- For odd `n`, the number `(n - 1) / 2` is even exactly when `n % 4 ≠ 3`
(i.e. `n ≡ 1 (mod 4)`). -/
lemma even_half_pred_iff_mod_four {n : ℕ} (hn : n % 2 = 1) :
    Even ((n - 1) / 2) ↔ n % 4 ≠ 3 := by
  obtain ⟨m, rfl⟩ : ∃ m, n = 2 * m + 1 := ⟨n / 2, by omega⟩
  have hd : (2 * m + 1 - 1) / 2 = m := by omega
  rw [hd]
  rcases Nat.mod_two_eq_zero_or_one m with h | h
  · have h4 : (2 * m + 1) % 4 = 1 := by omega
    rw [h4]
    simp [Nat.even_iff, h]
  · have h4 : (2 * m + 1) % 4 = 3 := by omega
    rw [h4]
    simp [Nat.even_iff, h]

theorem zassCoords_isSquare_neg_one_iff_even {G X : Type} [Group G] [Finite G]
    [MulAction G X] [Finite X] {q : ℕ} (hZ : Work.GW2.ZassHyps2 G X q) (hq : 2 ≤ q)
    {inf zero : X} (hne : inf ≠ zero) {U : Subgroup G} (C : Work.GW2.ZassCoords G X inf zero U)
    (h2 : (2 : C.E) ≠ 0) :
    (IsSquare (-1 : C.E) ↔ Even ((q - 1) / 2)) := by
  -- `C.E` has `q` elements, because `X ≃ Option C.E` and `Nat.card X = q + 1`.
  have hcardE : Nat.card C.E = q := by
    have h1 : Nat.card X = Nat.card (Option C.E) := Nat.card_congr C.Θ
    have h2' : Nat.card (Option C.E) = Nat.card C.E + 1 := Finite.card_option
    have h3 : Nat.card X = q + 1 := hZ.2.1
    omega
  -- `2 ≠ 0` means `ringChar C.E ≠ 2`, i.e. odd characteristic.
  have hchar : ringChar C.E ≠ 2 := by
    intro h
    exact h2 ((ringChar.spec C.E 2).2 (by simp [h]))
  have hcf : Fintype.card C.E = q := by
    have := Nat.card_eq_fintype_card (α := C.E)
    omega
  have hodd : q % 2 = 1 := by
    have h := FiniteField.odd_card_of_char_ne_two hchar
    omega
  rw [FiniteField.isSquare_neg_one_iff, hcf]
  exact (even_half_pred_iff_mod_four hodd).symm

end Work.ZASS2
