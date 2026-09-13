import Mathlib
import Submission.Commons.LinearAlgebra.Submodule.card_hyperplanes_between

namespace Commons.LinearAlgebra.Submodule

open Module

theorem card_neighbors_containing_of_inf_eq {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    [Finite V] (W L : Submodule (ZMod 2) V) (i ℓ : ℕ) (hW : Module.finrank (ZMod 2) W = i)
    (hL : Module.finrank (ZMod 2) L = ℓ) (hnle : ¬ W ≤ L)
    (hinf : Module.finrank (ZMod 2) ↥(W ⊓ L) = i - 1) :
    Nat.card {L' : Submodule (ZMod 2) V // Module.finrank (ZMod 2) L' = ℓ ∧
        Module.finrank (ZMod 2) ↥(L ⊓ L') = ℓ - 1 ∧ W ≤ L'} = 2 ^ (ℓ + 1 - i) - 1 := by
  classical
  have hi : 1 ≤ i := by
    rcases Nat.eq_zero_or_pos i with h | h
    · exfalso
      have hWbot : W = ⊥ := Submodule.finrank_eq_zero.mp (by rw [hW, h])
      exact hnle (by rw [hWbot]; exact bot_le)
    · exact h
  rcases Nat.eq_zero_or_pos ℓ with hℓ0 | hℓ
  · subst hℓ0
    have hempty : IsEmpty {L' : Submodule (ZMod 2) V // Module.finrank (ZMod 2) L' = 0 ∧
        Module.finrank (ZMod 2) ↥(L ⊓ L') = 0 - 1 ∧ W ≤ L'} :=
      ⟨fun L' => by
        have hbot : L'.1 = ⊥ := Submodule.finrank_eq_zero.mp L'.2.1
        have h1 : W ≤ ⊥ := hbot ▸ L'.2.2.2
        exact hnle (le_trans h1 bot_le)⟩
    rw [Nat.card_eq_zero.mpr (Or.inl hempty)]
    have hexp : (0 : ℕ) + 1 - i = 0 := by omega
    rw [hexp]
    norm_num
  · have hℓ1 : 1 ≤ ℓ := hℓ
    have hsupW : ∀ H : Submodule (ZMod 2) V, W ⊓ L ≤ H → H ≤ L →
        Module.finrank (ZMod 2) H = ℓ - 1 → Module.finrank (ZMod 2) ↥(H ⊔ W) = ℓ := by
      intro H hAH hHL hfin
      have hHW : H ⊓ W = W ⊓ L := by
        apply le_antisymm
        · calc H ⊓ W ≤ L ⊓ W := le_inf (le_trans inf_le_left hHL) inf_le_right
            _ = W ⊓ L := inf_comm L W
        · exact le_inf hAH inf_le_left
      have hdim := Submodule.finrank_sup_add_finrank_inf_eq H W
      rw [hHW, hinf, hfin, hW] at hdim
      omega
    have hinfLsup : ∀ H : Submodule (ZMod 2) V, W ⊓ L ≤ H → H ≤ L → L ⊓ (H ⊔ W) = H := by
      intro H hAH hHL
      rw [inf_comm, sup_inf_assoc_of_le W hHL]
      exact sup_eq_left.mpr hAH
    let f : {L' : Submodule (ZMod 2) V // Module.finrank (ZMod 2) L' = ℓ ∧
          Module.finrank (ZMod 2) ↥(L ⊓ L') = ℓ - 1 ∧ W ≤ L'} →
        {H : Submodule (ZMod 2) V // W ⊓ L ≤ H ∧ H ≤ L ∧
          Module.finrank (ZMod 2) H = ℓ - 1} :=
      fun L' => ⟨L ⊓ L'.1, le_inf inf_le_right (le_trans inf_le_left L'.2.2.2),
        inf_le_left, L'.2.2.1⟩
    let g : {H : Submodule (ZMod 2) V // W ⊓ L ≤ H ∧ H ≤ L ∧
          Module.finrank (ZMod 2) H = ℓ - 1} →
        {L' : Submodule (ZMod 2) V // Module.finrank (ZMod 2) L' = ℓ ∧
          Module.finrank (ZMod 2) ↥(L ⊓ L') = ℓ - 1 ∧ W ≤ L'} :=
      fun H => ⟨H.1 ⊔ W, ⟨hsupW H.1 H.2.1 H.2.2.1 H.2.2.2,
        by rw [hinfLsup H.1 H.2.1 H.2.2.1, H.2.2.2], le_sup_right⟩⟩
    have hleft : Function.LeftInverse g f := by
      intro L'
      apply Subtype.ext
      show (L ⊓ L'.1) ⊔ W = L'.1
      apply Submodule.eq_of_le_of_finrank_eq (sup_le inf_le_right L'.2.2.2)
      rw [hsupW (L ⊓ L'.1) (le_inf inf_le_right (le_trans inf_le_left L'.2.2.2)) inf_le_left
        L'.2.2.1]
      exact L'.2.1.symm
    have hright : Function.RightInverse g f := by
      intro H
      apply Subtype.ext
      show L ⊓ (H.1 ⊔ W) = H.1
      exact hinfLsup H.1 H.2.1 H.2.2.1
    have hcard : Nat.card {L' : Submodule (ZMod 2) V // Module.finrank (ZMod 2) L' = ℓ ∧
          Module.finrank (ZMod 2) ↥(L ⊓ L') = ℓ - 1 ∧ W ≤ L'} =
        Nat.card {H : Submodule (ZMod 2) V // W ⊓ L ≤ H ∧ H ≤ L ∧
          Module.finrank (ZMod 2) H = ℓ - 1} :=
      Nat.card_congr { toFun := f, invFun := g, left_inv := hleft, right_inv := hright }
    rw [hcard, card_hyperplanes_between (W ⊓ L) L ℓ hℓ1 inf_le_right hL]
    have he : ℓ - Module.finrank (ZMod 2) ↥(W ⊓ L) = ℓ + 1 - i := by rw [hinf]; omega
    rw [he]

end Commons.LinearAlgebra.Submodule
