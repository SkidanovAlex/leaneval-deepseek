import Mathlib

namespace Work.EKLC7

/-- If two monotone sequences `A B : ℕ → ENNReal` agree pointwise except possibly at
places where `A` is `⊤` and `B` is `0`, and `B` is never `⊤`, then the (real) values of
their suprema coincide.  Indeed, as soon as `A` takes the value `⊤` at some index `n`,
monotonicity forces `B` to vanish everywhere and every value of `A` to lie in `{0, ⊤}`,
so both `toReal`-suprema are `0`; otherwise `A = B` exactly. -/
theorem toReal_iSup_eq_of_approx {A B : ℕ → ENNReal} (hBtop : ∀ n, B n ≠ ⊤) (hAm : Monotone A) (hBm : Monotone B) (h : ∀ n, A n = B n ∨ (A n = ⊤ ∧ B n = 0)) : (⨆ n, A n).toReal = (⨆ n, B n).toReal := by
  by_cases hcase : ∃ n, A n = ⊤
  · obtain ⟨n, hn⟩ := hcase
    have hsupA : (⨆ m, A m) = ⊤ := le_antisymm le_top (by rw [← hn]; exact le_iSup A n)
    have hnB : B n = 0 := by
      rcases h n with h' | ⟨_, h'⟩
      · exact absurd (hn ▸ h').symm (hBtop n)
      · exact h'
    have hB0 : ∀ m, B m = 0 := by
      intro m
      rcases le_total m n with hmn | hnm
      · exact le_antisymm (hnB ▸ hBm hmn) bot_le
      · have hAm_top : A m = ⊤ := le_antisymm le_top (hn ▸ hAm hnm)
        rcases h m with h' | ⟨_, h'⟩
        · exact absurd (hAm_top ▸ h').symm (hBtop m)
        · exact h'
    have hsupB : (⨆ m, B m) = 0 := by simp [hB0]
    rw [hsupA, hsupB]
    simp
  · have hnot : ∀ n, A n ≠ ⊤ := fun n hAn => hcase ⟨n, hAn⟩
    have hAB : A = B := funext fun n => by
      rcases h n with h' | ⟨h', _⟩
      · exact h'
      · exact absurd h' (hnot n)
    rw [hAB]

end Work.EKLC7
