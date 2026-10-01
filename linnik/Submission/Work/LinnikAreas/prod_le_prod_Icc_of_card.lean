import Mathlib

namespace Work.LinnikAreas

/-- Auxiliary: for a finset `S` of naturals all of whose elements are `≥ 2` and a
non-increasing nonnegative function `f`, the product `∏ s ∈ S, f s` is bounded by the
product of `f` over the initial segment `{2, 3, …, S.card + 1}`.

This is the "matching" fact that the `i`-th smallest element of `S` is at least `i + 2`. -/
theorem prod_le_prod_Icc_of_card {S : Finset ℕ} (hS : ∀ s ∈ S, 2 ≤ s)
    (f : ℕ → ℝ) (hf0 : ∀ s, 0 ≤ f s) (hf : ∀ a b, 2 ≤ a → a ≤ b → f b ≤ f a) :
    ∏ s ∈ S, f s ≤ ∏ j ∈ Finset.Icc 2 (S.card + 1), f j := by
  classical
  suffices H : ∀ n (S : Finset ℕ), S.card = n → (∀ s ∈ S, 2 ≤ s) →
      ∏ s ∈ S, f s ≤ ∏ j ∈ Finset.Icc 2 (n + 1), f j by
    exact H S.card S rfl hS
  intro n
  induction n with
  | zero =>
      intro S hScard _
      rw [Finset.card_eq_zero.mp hScard]
      simp
  | succ n ih =>
      intro S hScard hS2
      have hne : S.Nonempty := Finset.card_pos.mp (by omega)
      set M := S.max' hne with hM
      have hMin : M ∈ S := by rw [hM]; exact Finset.max'_mem S hne
      have hMbound : ∀ s ∈ S, s ≤ M := by
        intro s hs
        rw [hM]
        exact (Finset.isGreatest_max' S hne).2 hs
      have hMge : S.card + 1 ≤ M := by
        have hsub : S ⊆ Finset.Icc 2 M :=
          fun s hs => Finset.mem_Icc.mpr ⟨hS2 s hs, hMbound s hs⟩
        have h1 : S.card ≤ (Finset.Icc 2 M).card := Finset.card_le_card hsub
        rw [Nat.card_Icc] at h1
        omega
      have hsplit : S = insert M (S.erase M) := (Finset.insert_erase hMin).symm
      have hnotmem : M ∉ S.erase M := S.notMem_erase M
      have hTcard : (S.erase M).card = n := by
        rw [Finset.card_erase_of_mem hMin, hScard]
        omega
      have hT2 : ∀ s ∈ S.erase M, 2 ≤ s := fun s hs => hS2 s (Finset.mem_of_mem_erase hs)
      have ihT : ∏ s ∈ S.erase M, f s ≤ ∏ j ∈ Finset.Icc 2 (n + 1), f j :=
        ih (S.erase M) hTcard hT2
      rw [hsplit, Finset.prod_insert hnotmem]
      rw [Finset.prod_Icc_succ_top (a := 2) (b := n + 1) (by omega : 2 ≤ n + 1 + 1) f]
      have hQ0 : 0 ≤ ∏ j ∈ Finset.Icc 2 (n + 1), f j := Finset.prod_nonneg (fun j _ => hf0 j)
      have hMle : f M ≤ f ((n + 1) + 1) :=
        hf ((n + 1) + 1) M (by omega) (by omega)
      calc f M * ∏ s ∈ S.erase M, f s
          ≤ f M * ∏ j ∈ Finset.Icc 2 (n + 1), f j :=
              mul_le_mul_of_nonneg_left ihT (hf0 M)
        _ ≤ f ((n + 1) + 1) * ∏ j ∈ Finset.Icc 2 (n + 1), f j :=
              mul_le_mul_of_nonneg_right hMle hQ0
        _ = (∏ j ∈ Finset.Icc 2 (n + 1), f j) * f ((n + 1) + 1) := mul_comm _ _

end Work.LinnikAreas
