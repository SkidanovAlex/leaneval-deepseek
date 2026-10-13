import Mathlib
import Submission.Work.WilC4.Defs

namespace Work.WilC4

theorem mem_prod_zpow {M : Type} [Field M] {S : Set M} (hS : Work.WilC4.IsValBase S) {m : ℕ}
    (d : Fin m → M) (a : Fin m → ℤ) (hd : ∀ j, d j ∈ S) (hd0 : ∀ j, d j ≠ 0) :
    (∏ j, d j ^ a j) ∈ S ∧ (∏ j, d j ^ a j) ≠ 0 := by
  obtain ⟨h1, hinv, hmul⟩ := hS
  have hnat : ∀ {x : M}, x ∈ S → ∀ n : ℕ, x ^ n ∈ S := by
    intro x hx n
    induction n with
    | zero => simpa using h1
    | succ n ih => rw [pow_succ]; exact hmul _ ih _ hx
  have hpow : ∀ (x : M), x ∈ S → x ≠ 0 → ∀ z : ℤ, x ^ z ∈ S ∧ x ^ z ≠ 0 := by
    intro x hx hx0 z
    rcases Int.eq_nat_or_neg z with ⟨n, hz | hz⟩
    · rw [hz, zpow_natCast]
      exact ⟨hnat hx n, pow_ne_zero n hx0⟩
    · rw [hz, zpow_neg, zpow_natCast]
      exact ⟨hinv _ (hnat hx n) (pow_ne_zero n hx0), inv_ne_zero (pow_ne_zero n hx0)⟩
  have hmem : ∀ j : Fin m, d j ^ a j ∈ S := fun j => (hpow (d j) (hd j) (hd0 j) (a j)).1
  have hne : ∀ j : Fin m, d j ^ a j ≠ 0 := fun j => (hpow (d j) (hd j) (hd0 j) (a j)).2
  exact ⟨Finset.prod_induction (fun j => d j ^ a j) (fun x => x ∈ S)
      (fun x y hx hy => hmul x hx y hy) h1 (fun j _ => hmem j),
    Finset.prod_ne_zero_iff.mpr (fun j _ => hne j)⟩

end Work.WilC4
