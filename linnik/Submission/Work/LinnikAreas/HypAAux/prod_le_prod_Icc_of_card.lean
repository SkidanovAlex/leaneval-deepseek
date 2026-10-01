import Mathlib

namespace Work.LinnikAreas.HypAAux

/-- Given a finite set `S` of natural numbers all `≥ 2`, and a nonnegative,
non-increasing (on the range `[2, ∞)`) real-valued function `f`, the product of
`f` over `S` is at most the product of `f` over the initial segment
`{2, 3, …, S.card + 1}`. -/
theorem prod_le_prod_Icc_of_card {S : Finset ℕ} (hS : ∀ s ∈ S, 2 ≤ s)
    (f : ℕ → ℝ) (hf0 : ∀ s, 0 ≤ f s) (hf : ∀ a b, 2 ≤ a → a ≤ b → f b ≤ f a) :
    ∏ s ∈ S, f s ≤ ∏ j ∈ Finset.Icc 2 (S.card + 1), f j := by
  suffices H : ∀ n : ℕ, ∀ S : Finset ℕ, S.card = n → (∀ s ∈ S, 2 ≤ s) →
      ∏ s ∈ S, f s ≤ ∏ j ∈ Finset.Icc 2 (n + 1), f j by
    exact H S.card S rfl hS
  intro n
  refine Nat.strong_induction_on n ?_
  intro n ih S hcard hS
  rcases S.eq_empty_or_nonempty with h | hne
  · have hn : n = 0 := by rw [← hcard, h]; simp
    subst hn
    rw [h]
    simp
  · -- `m` is the largest element of `S`.
    set m := S.max' hne with hm
    have hmem : m ∈ S := by rw [hm]; exact Finset.max'_mem S hne
    have hm2 : 2 ≤ m := hS m hmem
    have hnpos : 0 < n := by rw [← hcard]; exact Finset.card_pos.mpr hne
    have herase_card : (S.erase m).card = n - 1 := by
      rw [Finset.card_erase_of_mem hmem, hcard]
    -- `S` has `n` elements all `≥ 2`, so its largest element is at least `n + 1`.
    have hsub : S ⊆ Finset.Icc 2 m := by
      intro s hs
      exact Finset.mem_Icc.mpr ⟨hS s hs, by rw [hm]; exact Finset.le_max' S s hs⟩
    have hnm : n < m := by
      have hle : n ≤ (Finset.Icc 2 m).card := by
        rw [← hcard]; exact Finset.card_le_card hsub
      rw [Nat.card_Icc] at hle
      omega
    have hIH := ih (n - 1) (by omega) (S.erase m) herase_card
      (fun s hs => hS s (Finset.mem_of_mem_erase hs))
    rw [Nat.sub_add_cancel (by omega : 1 ≤ n)] at hIH
    have hfm : f m ≤ f (n + 1) := hf (n + 1) m (by omega) (by omega)
    have hA0 : 0 ≤ ∏ s ∈ S.erase m, f s := Finset.prod_nonneg (fun s _ => hf0 s)
    have hfn1 : 0 ≤ f (n + 1) := hf0 (n + 1)
    calc
      ∏ s ∈ S, f s = f m * ∏ s ∈ S.erase m, f s := (Finset.mul_prod_erase S f hmem).symm
      _ ≤ f (n + 1) * ∏ s ∈ S.erase m, f s := mul_le_mul_of_nonneg_right hfm hA0
      _ ≤ f (n + 1) * ∏ j ∈ Finset.Icc 2 n, f j := mul_le_mul_of_nonneg_left hIH hfn1
      _ = ∏ j ∈ Finset.Icc 2 (n + 1), f j := by
            rw [Finset.prod_Icc_succ_top (by omega : 2 ≤ n + 1) f]; ring

end Work.LinnikAreas.HypAAux
