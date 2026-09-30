import Mathlib
import Submission.Work.BMF.MSD.basic

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF.MSD

/-- Kernel majorant vs counting function: for any real `θ` and natural `N`, `kern N θ` is at
most the number of integers `k ∈ {0, …, N-1}` with `2 · circDist θ · k < 1`. -/
theorem kern_le_filter_card (N : ℕ) (θ : ℝ) :
    kern N θ
      ≤ (((Finset.range N).filter (fun k : ℕ => 2 * circDist θ * (k : ℝ) < 1)).card : ℝ) := by
  rw [kern]
  split_ifs with h0
  · -- `circDist θ = 0`: the filter keeps everything
    have hfilter : (Finset.range N).filter (fun k : ℕ => 2 * circDist θ * (k : ℝ) < 1)
        = Finset.range N := by
      apply Finset.filter_true_of_mem
      intro k _
      rw [h0]; norm_num
    rw [hfilter, Finset.card_range]
  · -- `circDist θ ≠ 0`: count the initial segment `k < 1/(2·circDist θ)`
    have hpos : 0 < circDist θ := lt_of_le_of_ne (circDist_nonneg θ) (Ne.symm h0)
    set S : Finset ℕ := (Finset.range N).filter (fun k : ℕ => 2 * circDist θ * (k : ℝ) < 1)
      with hS
    have hmem : ∀ k : ℕ, k ∈ S ↔ k < N ∧ 2 * circDist θ * (k : ℝ) < 1 := by
      intro k
      rw [hS]
      simp [Finset.mem_filter]
    -- `S` is downward closed
    have hdown : ∀ {x y : ℕ}, x ∈ S → y ≤ x → y ∈ S := by
      intro x y hx hyx
      rw [hmem] at hx ⊢
      obtain ⟨hxN, hxP⟩ := hx
      refine ⟨lt_of_le_of_lt hyx hxN, ?_⟩
      have hyx' : (y : ℝ) ≤ (x : ℝ) := by exact_mod_cast hyx
      have hmono : 2 * circDist θ * (y : ℝ) ≤ 2 * circDist θ * (x : ℝ) :=
        mul_le_mul_of_nonneg_left hyx' (by linarith)
      linarith
    by_contra hcon
    rw [not_le] at hcon
    have hcN : (S.card : ℝ) < (N : ℝ) := lt_of_lt_of_le hcon (min_le_left _ _)
    have hcL : (S.card : ℝ) < 1 / (2 * circDist θ) :=
      lt_of_lt_of_le hcon (min_le_right _ _)
    have hcP : 2 * circDist θ * (S.card : ℝ) < 1 := by
      have h2 : (0 : ℝ) < 2 * circDist θ := by linarith
      have h := (lt_div_iff₀ h2).mp hcL
      linarith [h, mul_comm ((S.card : ℝ)) (2 * circDist θ)]
    have hcS : S.card ∈ S := by
      rw [hmem]
      exact ⟨Nat.cast_lt.mp hcN, hcP⟩
    have hrange : (Finset.range (S.card + 1)) ⊆ S := by
      intro x hx
      rw [Finset.mem_range] at hx
      exact hdown hcS (Nat.lt_succ_iff.mp hx)
    have hle := Finset.card_le_card hrange
    rw [Finset.card_range] at hle
    omega

end Work.BMF.MSD
