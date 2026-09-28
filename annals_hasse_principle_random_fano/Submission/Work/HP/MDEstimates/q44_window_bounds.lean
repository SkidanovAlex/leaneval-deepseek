import Mathlib
import Submission.Work.HP.Defs
import Submission.Work.HP.PairsAux
import Submission.Work.HP.kwin_spec

namespace Work.HP.MDEstimates

/-- Dyadic window bounds for a rank-`3` sublattice `L ⊆ ℤ^5` of covolume `≤ Δ+1`.

Writing `k_j = kwin 3 L j = ⌈log₂ λ_{j+1}(L)⌉`, the windows are monotone in `j`, and the
product `∏_{j=1}^{3} 2^{k_j}` is at most `8 λ₁λ₂λ₃` (`kwin_spec`), which is at most
`8 · Kmink · detL L ≤ 8 · Kmink · (Δ+1)` by the Minkowski product bound `hmink`.  Hence
the exponents satisfy `Σ_j k_j ≤ ⌈log₂ (8 · Kmink · (Δ+1))⌉` (`sum_le_ceil_logb_of_prod`),
and each `k_j` is bounded by the same quantity. -/
theorem q44_window_bounds (Kmink : ℝ) (hKmink : 1 ≤ Kmink)
    (hmink : ∀ L : Submodule ℤ (Fin 5 → ℤ),
      (∏ j ∈ Finset.range (Work.HP.rk L), Work.HP.lam L (j + 1)) ≤ Kmink * Work.HP.detL L) :
    ∀ (Δ : ℝ), 1 ≤ Δ → ∀ L : Submodule ℤ (Fin 5 → ℤ),
      Work.HP.rk L = 3 → Work.HP.detL L ≤ Δ + 1 →
      Monotone (Work.HP.kwin 3 L) ∧
      (∑ j : Fin 3, Work.HP.kwin 3 L j) ≤ ⌈Real.logb 2 (8 * Kmink * (Δ + 1))⌉₊ ∧
      (∀ j : Fin 3, Work.HP.kwin 3 L j ≤ ⌈Real.logb 2 (8 * Kmink * (Δ + 1))⌉₊) := by
  intro Δ hΔ L hrk hdet
  set M : ℝ := 8 * Kmink * (Δ + 1) with hMdef
  have hKmink0 : 0 ≤ Kmink := le_trans zero_le_one hKmink
  have hΔ1 : (1 : ℝ) ≤ Δ + 1 := by linarith
  have hM1 : 1 ≤ M := by
    have hprod : 1 ≤ Kmink * (Δ + 1) := by
      simpa using mul_le_mul hKmink hΔ1 (by norm_num : (0:ℝ) ≤ 1) hKmink0
    rw [hMdef]; nlinarith
  obtain ⟨_, hhi, hmono, hsum⟩ := Work.HP.kwin_spec (Fin 5) 3 L (by norm_num) hrk
  -- The Minkowski product bound, transported from `Finset.range` to `Fin 3`.
  have hlamprod : (∏ j : Fin 3, Work.HP.lam L (j.1 + 1)) ≤ Kmink * Work.HP.detL L := by
    have h := hmink L
    rw [hrk, ← Fin.prod_univ_eq_prod_range (fun i => Work.HP.lam L (i + 1)) 3] at h
    exact h
  -- The window product `∏ 2^{k_j}` is at most `M`.
  have hprod_le : (∏ j : Fin 3, (2 : ℝ) ^ (Work.HP.kwin 3 L j)) ≤ M := by
    calc (∏ j : Fin 3, (2 : ℝ) ^ (Work.HP.kwin 3 L j))
        ≤ ∏ j : Fin 3, 2 * Work.HP.lam L (j.1 + 1) :=
          Finset.prod_le_prod₀ (fun j _ => by positivity) (fun j _ => hhi j)
      _ = 8 * ∏ j : Fin 3, Work.HP.lam L (j.1 + 1) := by
          rw [Finset.prod_mul_distrib, Finset.prod_const]; norm_num
      _ ≤ 8 * (Kmink * Work.HP.detL L) :=
          mul_le_mul_of_nonneg_left hlamprod (by norm_num)
      _ ≤ 8 * (Kmink * (Δ + 1)) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left hdet hKmink0) (by norm_num)
      _ = M := by rw [hMdef]; ring
  have hsum' := hsum M hM1 hprod_le
  refine ⟨hmono, hsum', fun j => ?_⟩
  exact (Finset.single_le_sum (fun i _ => Nat.zero_le _) (Finset.mem_univ j)).trans hsum'

end Work.HP.MDEstimates
