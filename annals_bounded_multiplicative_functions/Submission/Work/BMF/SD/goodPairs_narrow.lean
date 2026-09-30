import Mathlib
import Submission.Work.BMF.Defs
import Submission.Work.BMF.SD.sd3_defs
import Submission.Work.BMF.SD.primeWindow_cover
import Submission.Work.BMF.SD.rho_window_arith
import Submission.Work.BMF.SD.pi0_subwindow_le

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-! Guidance from the project lead (the requester):

LEAD 09-30: new scale_down decomposition (read _NOTE_BMF_SD_0930_VERDICT.md at the workspace root; your node's route and constants are in its docstring). Narrow the prime window AFTER counting (pigeonhole into sub-windows of ratio 1+ρ), then split on T = X/H at a threshold T₁ depending only on c₀. No new analytic number theory is needed.
Pigeonhole leaf (no analytic input). No extra imports.
-/

namespace Work.BMF.SD

/-- Narrowing a prime window by pigeonhole (no analytic input).  Let `0 < ρ ≤ 2/5`.  If the good
pairs of a window `[a,b]` (`2 ≤ a ≤ b ≤ 7a/5`) number at least `κ π₀(a)`, then some sub-window
`[a', b'] ⊆ [a, b]` of ratio `b' ≤ (1+ρ) a'` carries at least `c κ π₀(a')` of them, with `c > 0`
depending on `ρ` only.

Route.  Put `M := ⌈1/ρ⌉₊`, `a_j := a (1+ρ)^j`, `b_j := min b a_{j+1}` for `j < M`.  Bernoulli gives
`(1+ρ)^M ≥ 1 + Mρ ≥ 2 ≥ 7/5`, so every prime `p ∈ [a,b]` lies in some `[a_j, b_j]` (take the
largest `j` with `a_j ≤ p`); hence `Σ_{j<M} #goodPairs(.., a_j, b_j, S) ≥ #goodPairs(.., a, b, S)`
(`goodPairs f pol η H u v S` only depends on `[u,v]` through `primesIn u v`).  Pigeonhole: some
`j` has `#goodPairs(.., a_j, b_j, S) ≥ κ π₀(a) / M`; it is non-empty when `κ > 0`, so
`a_j ≤ b_j` and `a_j ≤ b`.  Finally `π₀(a_j) = a_j / log a_j ≤ (7a/5) / log a = (7/5) π₀(a)`
(`a ≤ a_j ≤ 7a/5`, `log a ≥ log 2 > 0`), so `c := 5 / (7 (M + 1))` works (any `c ≤ 5/(7M)`).
The case `κ = 0` is `a' = b' = a`. -/
theorem goodPairs_narrow (ρ : ℝ) (hρ : 0 < ρ) (hρ' : ρ ≤ 2 / 5) :
    ∃ c : ℝ, 0 < c ∧
      ∀ (f : ℕ → ℂ) (pol : ℝ → Polynomial ℝ) (η H a b κ : ℝ) (S : Finset ℝ),
        2 ≤ a → a ≤ b → 5 * b ≤ 7 * a → 0 ≤ κ →
        κ * Work.BMF.pi0 a ≤ ((Work.BMF.goodPairs f pol η H a b S).card : ℝ) →
        ∃ a' b' : ℝ, a ≤ a' ∧ a' ≤ b' ∧ b' ≤ b ∧ b' ≤ (1 + ρ) * a' ∧
          c * κ * Work.BMF.pi0 a' ≤ ((Work.BMF.goodPairs f pol η H a' b' S).card : ℝ) := by
  -- the number of sub-windows and the pigeonhole constant
  set M : ℕ := Nat.ceil (1 / ρ) with hMdef
  refine ⟨5 / (7 * ((M : ℝ) + 1)), ?_, ?_⟩
  · exact div_pos (by norm_num) (by positivity)
  · intro f pol η H a b κ S ha2 hab hb75 hκ hcard
    have hapos : 0 < a := by linarith
    -- `M ≥ 1` and `b ≤ a (1+ρ)^M` (Bernoulli, via `rho_window_arith`)
    obtain ⟨hM1', hbig'⟩ := rho_window_arith ρ a b hρ hapos hb75
    have hM1 : 1 ≤ M := by rw [hMdef]; exact hM1'
    have hbig : b ≤ a * (1 + ρ) ^ M := by rw [hMdef]; exact hbig'
    by_cases hκ0 : κ = 0
    · -- degenerate case: `a' = b' = a`
      refine ⟨a, a, le_rfl, le_rfl, hab, ?_, ?_⟩
      · nlinarith [hρ, hapos]
      · rw [hκ0]; simp
    have hκpos : 0 < κ := lt_of_le_of_ne hκ (Ne.symm hκ0)
    have hpi0a : 0 < Work.BMF.pi0 a := by
      rw [Work.BMF.pi0]
      exact div_pos (by linarith) (Real.log_pos (by linarith))
    -- every prime of `[a,b]` lies in one of the geometric sub-windows
    have hcover := primeWindow_cover ρ a b M hρ hapos hM1 hbig
    -- hence the good pairs of `[a,b]` are covered by the good pairs of the sub-windows
    have hgpcov : Work.BMF.goodPairs f pol η H a b S ⊆
        (Finset.range M).biUnion (fun j => Work.BMF.goodPairs f pol η H
          (a * (1 + ρ) ^ j) (min b (a * (1 + ρ) ^ (j + 1))) S) := by
      intro q hq
      rw [Work.BMF.mem_goodPairs] at hq
      obtain ⟨hy, hp, hcond⟩ := hq
      have hp' := hcover hp
      rw [Finset.mem_biUnion] at hp'
      obtain ⟨j, hj, hpj⟩ := hp'
      rw [Finset.mem_biUnion]
      exact ⟨j, hj, by rw [Work.BMF.mem_goodPairs]; exact ⟨hy, hpj, hcond⟩⟩
    -- the counting inequality `#goodPairs a b ≤ Σ_j #goodPairs a_j b_j`
    have hsum : ((Work.BMF.goodPairs f pol η H a b S).card : ℝ) ≤
        ∑ j ∈ Finset.range M, ((Work.BMF.goodPairs f pol η H
          (a * (1 + ρ) ^ j) (min b (a * (1 + ρ) ^ (j + 1))) S).card : ℝ) := by
      have h1 : (Work.BMF.goodPairs f pol η H a b S).card ≤
          ((Finset.range M).biUnion (fun j => Work.BMF.goodPairs f pol η H
            (a * (1 + ρ) ^ j) (min b (a * (1 + ρ) ^ (j + 1))) S)).card :=
        Finset.card_le_card hgpcov
      have h2 := Finset.card_biUnion_le (s := Finset.range M)
        (t := fun j => Work.BMF.goodPairs f pol η H
            (a * (1 + ρ) ^ j) (min b (a * (1 + ρ) ^ (j + 1))) S)
      exact_mod_cast le_trans h1 h2
    -- pigeonhole: some sub-window carries at least `κ π₀(a) / M` good pairs
    have hpige : ∃ j ∈ Finset.range M,
        κ * Work.BMF.pi0 a / (M : ℝ) ≤
          ((Work.BMF.goodPairs f pol η H (a * (1 + ρ) ^ j)
            (min b (a * (1 + ρ) ^ (j + 1))) S).card : ℝ) := by
      by_contra hcon
      push_neg at hcon
      have hlt : (∑ j ∈ Finset.range M, ((Work.BMF.goodPairs f pol η H (a * (1 + ρ) ^ j)
            (min b (a * (1 + ρ) ^ (j + 1))) S).card : ℝ)) <
          ∑ _j ∈ Finset.range M, (κ * Work.BMF.pi0 a / (M : ℝ)) := by
        apply Finset.sum_lt_sum_of_nonempty
        · exact ⟨0, Finset.mem_range.mpr hM1⟩
        · intro j hj
          exact hcon j hj
      have hMne : (M : ℝ) ≠ 0 := by
        have : (0:ℝ) < (M : ℝ) := by exact_mod_cast hM1
        exact ne_of_gt this
      have hsum2 : ∑ _j ∈ Finset.range M, (κ * Work.BMF.pi0 a / (M : ℝ)) =
          κ * Work.BMF.pi0 a := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        field_simp
      rw [hsum2] at hlt
      have hle : κ * Work.BMF.pi0 a ≤ ∑ j ∈ Finset.range M, ((Work.BMF.goodPairs f pol η H
            (a * (1 + ρ) ^ j) (min b (a * (1 + ρ) ^ (j + 1))) S).card : ℝ) :=
        le_trans hcard hsum
      linarith
    obtain ⟨j, hj, hjbound⟩ := hpige
    -- the selected sub-window carries a pair, so it is non-degenerate
    have hNjpos : 0 < ((Work.BMF.goodPairs f pol η H (a * (1 + ρ) ^ j)
        (min b (a * (1 + ρ) ^ (j + 1))) S).card : ℝ) := by
      have hMpos : (0:ℝ) < (M : ℝ) := by exact_mod_cast hM1
      have h1 : 0 < κ * Work.BMF.pi0 a / (M : ℝ) := div_pos (mul_pos hκpos hpi0a) hMpos
      linarith
    have hne : (Work.BMF.goodPairs f pol η H (a * (1 + ρ) ^ j)
        (min b (a * (1 + ρ) ^ (j + 1))) S).Nonempty := by
      rw [← Finset.card_pos]
      exact_mod_cast hNjpos
    obtain ⟨q, hq⟩ := hne
    rw [Work.BMF.mem_goodPairs] at hq
    obtain ⟨hy, hp, hcond⟩ := hq
    have hpIcc := (Finset.mem_filter.mp hp).1
    have hp1 : a * (1 + ρ) ^ j ≤ (q.2 : ℝ) :=
      le_trans (Nat.le_ceil _) (by exact_mod_cast (Finset.mem_Icc.mp hpIcc).1)
    have hbnonneg : 0 ≤ min b (a * (1 + ρ) ^ (j + 1)) :=
      le_min (by linarith) (by positivity)
    have hp2 : (q.2 : ℝ) ≤ min b (a * (1 + ρ) ^ (j + 1)) :=
      le_trans (by exact_mod_cast (Finset.mem_Icc.mp hpIcc).2) (Nat.floor_le hbnonneg)
    have hle_a' : a ≤ a * (1 + ρ) ^ j := by
      calc a = a * 1 := by ring
        _ ≤ a * (1 + ρ) ^ j :=
            mul_le_mul_of_nonneg_left (one_le_pow₀ (by linarith)) hapos.le
    have hle_a'b' : a * (1 + ρ) ^ j ≤ min b (a * (1 + ρ) ^ (j + 1)) := le_trans hp1 hp2
    have hb'le75 : min b (a * (1 + ρ) ^ (j + 1)) ≤ 7 * a / 5 :=
      le_trans (min_le_left _ _) (by linarith)
    have ha'75 : a * (1 + ρ) ^ j ≤ 7 * a / 5 := le_trans hle_a'b' hb'le75
    -- `π₀(a_j) ≤ (7/5) π₀(a)`, and the constant `5/(7(M+1))` absorbs the factor `7/5`
    have hpi := pi0_subwindow_le a (a * (1 + ρ) ^ j) ha2 hle_a' ha'75
    have hconst : 5 / (7 * ((M : ℝ) + 1)) * κ * Work.BMF.pi0 (a * (1 + ρ) ^ j)
        ≤ κ * Work.BMF.pi0 a / (M : ℝ) := by
      have hMpos : (0:ℝ) < (M : ℝ) := by exact_mod_cast hM1
      have hfrac : 5 / (7 * ((M : ℝ) + 1)) * (7 / 5) = 1 / ((M : ℝ) + 1) := by
        field_simp
      calc 5 / (7 * ((M : ℝ) + 1)) * κ * Work.BMF.pi0 (a * (1 + ρ) ^ j)
          = (5 / (7 * ((M : ℝ) + 1))) * (κ * Work.BMF.pi0 (a * (1 + ρ) ^ j)) := by ring
        _ ≤ (5 / (7 * ((M : ℝ) + 1))) * (κ * ((7 / 5) * Work.BMF.pi0 a)) := by
            apply mul_le_mul_of_nonneg_left _ (by positivity)
            exact mul_le_mul_of_nonneg_left hpi hκ
        _ = (1 / ((M : ℝ) + 1)) * (κ * Work.BMF.pi0 a) := by
            rw [← hfrac]; ring
        _ ≤ (1 / (M : ℝ)) * (κ * Work.BMF.pi0 a) := by
            apply mul_le_mul_of_nonneg_right _ (by positivity)
            exact one_div_le_one_div_of_le hMpos (by linarith)
        _ = κ * Work.BMF.pi0 a / (M : ℝ) := by ring
    exact ⟨a * (1 + ρ) ^ j, min b (a * (1 + ρ) ^ (j + 1)), hle_a', hle_a'b', min_le_left _ _,
      (by calc min b (a * (1 + ρ) ^ (j + 1)) ≤ a * (1 + ρ) ^ (j + 1) := min_le_right _ _
            _ = (1 + ρ) * (a * (1 + ρ) ^ j) := by rw [pow_succ]; ring),
      le_trans hconst hjbound⟩

end Work.BMF.SD
