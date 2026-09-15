import Mathlib
import Submission.Commons.NumberTheory.Sieve.card_omega_pair_gen

namespace Commons.NumberTheory.Sieve

/-- If `X` has at least two indices, the number of solutions `x : Fin t → ZMod p` to the
system of affine equations `W * ((∑ j, L i j * x j) + c i) + 1 = 0` for all `i ∈ X`
(with the `L i` pairwise non-proportional and nonzero) is at most `p ^ (t - 2)`. -/
theorem card_omega_ge_two_le {p : ℕ} [Fact p.Prime] {t m : ℕ} (ht : 2 ≤ t) {W : ZMod p} (L : Fin m → Fin t → ZMod p) (c : Fin m → ZMod p) (X : Finset (Fin m)) (hX : 2 ≤ X.card) (hne0 : ∀ i ∈ X, L i ≠ 0) (hprop : ∀ i ∈ X, ∀ j ∈ X, i ≠ j → ∀ lam : ZMod p, L j ≠ lam • L i) : ((Finset.univ : Finset (Fin t → ZMod p)).filter (fun x => ∀ i ∈ X, W * ((∑ j, L i j * x j) + c i) + 1 = 0)).card ≤ if W = 0 then 0 else p ^ (t - 2) := by
  classical
  obtain ⟨i0, hi0, j0, hj0, hij⟩ := Finset.one_lt_card.mp (by omega : 1 < X.card)
  have hsub : ((Finset.univ : Finset (Fin t → ZMod p)).filter
        (fun x => ∀ i ∈ X, W * ((∑ j, L i j * x j) + c i) + 1 = 0)) ⊆
      ((Finset.univ : Finset (Fin t → ZMod p)).filter
        (fun x => W * ((∑ j, L i0 j * x j) + c i0) + 1 = 0 ∧
                  W * ((∑ j, L j0 j * x j) + c j0) + 1 = 0)) := by
    intro x hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
    exact ⟨hx i0 hi0, hx j0 hj0⟩
  exact le_trans (Finset.card_le_card hsub)
    (card_omega_pair_gen ht (L i0) (L j0) (hne0 i0 hi0)
      (hprop i0 hi0 j0 hj0 hij) (c i0) (c j0))

end Commons.NumberTheory.Sieve
