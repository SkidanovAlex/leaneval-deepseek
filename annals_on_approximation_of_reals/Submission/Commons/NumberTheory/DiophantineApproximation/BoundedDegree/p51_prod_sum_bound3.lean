import Mathlib
open scoped BigOperators

namespace Commons.NumberTheory.DiophantineApproximation.BoundedDegree

theorem p51_prod_sum_bound3 (n k : ℕ) (hn : 1 ≤ n) (hk2 : 2 ≤ k) (hkn : k ≤ n + 1)
    (H : Fin k → ℝ) (hmono : Monotone H) (hHge : ∀ i : Fin k, 1 ≤ H i)
    (C : ℝ) (hCge1 : 1 ≤ C)
    (L : Fin (2 * n - k + 2) → Fin k)
    (hLab0 : ∀ ℓ : Fin (2 * n - k + 2), ℓ.val < n + 2 - k → L ℓ = ⟨0, by omega⟩)
    (hLab1 : ∀ ℓ : Fin (2 * n - k + 2), n + 2 - k ≤ ℓ.val → ℓ.val < 2 * (n + 2 - k) →
      L ℓ = ⟨1, by omega⟩)
    (hLab2 : ∀ ℓ : Fin (2 * n - k + 2), 2 * (n + 2 - k) ≤ ℓ.val →
      2 ≤ (L ℓ).val ∧ (L ℓ).val ≤ ℓ.val - 2 * (n + 2 - k) + 2) :
    ∃ Cbig : ℝ, 0 < Cbig ∧
    ∀ (A : Fin (2 * n - k + 2) → ℝ),
      (∀ ℓ : Fin (2 * n - k + 2), A ℓ ≤ C * H (L ℓ)) →
      (∀ ℓ : Fin (2 * n - k + 2), H (L ℓ) ≤ C * A ℓ) →
      ∀ a : Fin (2 * n - k + 2),
        (Finset.prod (Finset.univ.erase a) A) ≤ Cbig *
          ((H ⟨0, by omega⟩) ^ (n + 1 - k) * (H ⟨1, by omega⟩) ^ (n + 2 - k) *
            Finset.prod (Finset.univ.filter (fun j : Fin k => 2 ≤ j.val)) H) := by
  classical
  let m : ℕ := 2 * n - k + 2
  let top : Fin k := ⟨k - 1, by omega⟩
  let B : ℝ := C * H top
  refine ⟨B ^ (m - 1), ?_, ?_⟩
  · have hBpos : 0 < B := by
      dsimp [B]
      have hCpos : (0 : ℝ) < C := by linarith
      have hHpos : (0 : ℝ) < H top := by
        have : (1 : ℝ) ≤ H top := hHge top
        linarith
      exact mul_pos hCpos hHpos
    exact pow_pos hBpos (m - 1)
  · intro A hAub hAlb a
    have hCpos : (0 : ℝ) < C := by linarith
    have hApos : ∀ ℓ : Fin (2 * n - k + 2), 0 ≤ A ℓ := by
      intro ℓ
      have hAlb1 : (1 : ℝ) ≤ C * A ℓ := le_trans (hHge (L ℓ)) (hAlb ℓ)
      by_contra h
      have hA0 : A ℓ ≤ 0 := le_of_not_ge h
      have hle0 : C * A ℓ ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (le_of_lt hCpos) hA0
      linarith
    have hAleB : ∀ ℓ : Fin (2 * n - k + 2), A ℓ ≤ B := by
      intro ℓ
      dsimp [B]
      calc
        A ℓ ≤ C * H (L ℓ) := hAub ℓ
        _ ≤ C * H top := by
          apply mul_le_mul_of_nonneg_left _ (le_of_lt hCpos)
          apply hmono
          rw [Fin.le_def]
          dsimp [top]
          have hlt : (L ℓ).val < k := (L ℓ).isLt
          omega
    have hprod : (∏ ℓ ∈ (Finset.univ.erase a), A ℓ) ≤ B ^ (Finset.univ.erase a).card := by
      calc
        (∏ ℓ ∈ (Finset.univ.erase a), A ℓ) ≤ (∏ ℓ ∈ (Finset.univ.erase a), B) := by
          exact Finset.prod_le_prod (by intro ℓ hℓ; exact hApos ℓ) (by intro ℓ hℓ; exact hAleB ℓ)
        _ = B ^ (Finset.univ.erase a).card := by simp
    have hcard : (Finset.univ.erase a).card = m - 1 := by
      rw [Finset.card_erase_of_mem (Finset.mem_univ a)]
      simp [m]
    have hprod' : (∏ ℓ ∈ (Finset.univ.erase a), A ℓ) ≤ B ^ (m - 1) := by
      simpa [hcard] using hprod
    have hRHS1 : (1 : ℝ) ≤
        (H ⟨0, by omega⟩) ^ (n + 1 - k) * (H ⟨1, by omega⟩) ^ (n + 2 - k) *
          (∏ j ∈ (Finset.univ.filter (fun j : Fin k => 2 ≤ j.val)), H j) := by
      have ha : (1 : ℝ) ≤ (H ⟨0, by omega⟩) ^ (n + 1 - k) := one_le_pow₀ (hHge ⟨0, by omega⟩)
      have hb : (1 : ℝ) ≤ (H ⟨1, by omega⟩) ^ (n + 2 - k) := one_le_pow₀ (hHge ⟨1, by omega⟩)
      have hab : (1 : ℝ) ≤ (H ⟨0, by omega⟩) ^ (n + 1 - k) * (H ⟨1, by omega⟩) ^ (n + 2 - k) := one_le_mul_of_one_le_of_one_le ha hb
      have hc : (1 : ℝ) ≤ ∏ j ∈ (Finset.univ.filter (fun j : Fin k => 2 ≤ j.val)), H j := by
        exact Finset.one_le_prod (by intro j hj; exact hHge j)
      exact one_le_mul_of_one_le_of_one_le hab hc
    have hBnonneg : 0 ≤ B ^ (m - 1) := by
      have hBpos : 0 < B := by
        dsimp [B]
        exact mul_pos (by linarith) (by have : (1 : ℝ) ≤ H top := hHge top; linarith)
      exact pow_nonneg (le_of_lt hBpos) (m - 1)
    have hBle : B ^ (m - 1) ≤ B ^ (m - 1) *
        ((H ⟨0, by omega⟩) ^ (n + 1 - k) * (H ⟨1, by omega⟩) ^ (n + 2 - k) *
          (∏ j ∈ (Finset.univ.filter (fun j : Fin k => 2 ≤ j.val)), H j)) := by
      simpa [mul_assoc] using (mul_le_mul_of_nonneg_left hRHS1 hBnonneg)
    exact le_trans hprod' hBle

end Commons.NumberTheory.DiophantineApproximation.BoundedDegree
