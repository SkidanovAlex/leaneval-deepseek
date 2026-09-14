import Mathlib
import Submission.Commons.Analysis.Sum.sum_rpow_neg_le_of_card_le
import Submission.Commons.Analysis.Sum.sum_antitone_rank_le

open Finset

set_option linter.style.haveILetI false

namespace Commons.Analysis.Sum

/-- Cardinality bound: under the counting hypothesis `#{i : g i ≤ Y} ≤ c Y^β` for all `Y`,
the total number of indices is at most `c X^β` (when all `g i ≤ X` and `X ≥ 1`). -/
private theorem card_le_of_card_filter_le_fintype {ι : Type*} [Fintype ι] (g : ι → ℕ)
    {c X β : ℝ} (hc : 0 ≤ c) (hX : 1 ≤ X) (hnX : ∀ i, (g i : ℝ) ≤ X)
    (hcard : ∀ Y : ℕ, ((Finset.univ.filter (fun i => g i ≤ Y)).card : ℝ) ≤ c * (Y:ℝ)^β) :
    (Fintype.card ι : ℝ) ≤ c * X^β := by
  have hXpos : (0:ℝ) < X := lt_of_lt_of_le zero_lt_one hX
  rcases le_or_gt 0 β with hβ | hβ
  · have hY : ((Nat.floor X : ℕ) : ℝ) ≤ X := Nat.floor_le (le_of_lt hXpos)
    have hs_eq : Finset.univ.filter (fun i => g i ≤ Nat.floor X) = Finset.univ := by
      apply Finset.filter_true_of_mem
      intro i _
      exact Nat.le_floor (hnX i)
    have hm : (Fintype.card ι : ℝ) = ((Finset.univ.filter (fun i => g i ≤ Nat.floor X)).card : ℝ) := by
      rw [hs_eq, Finset.card_univ]
    rw [hm]
    calc ((Finset.univ.filter (fun i => g i ≤ Nat.floor X)).card : ℝ)
        ≤ c * ((Nat.floor X : ℕ) : ℝ)^β := hcard (Nat.floor X)
      _ ≤ c * X^β := mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow (by positivity) hY hβ) hc
  · have hY : X ≤ ((Nat.ceil X : ℕ) : ℝ) := Nat.le_ceil X
    have hs_eq : Finset.univ.filter (fun i => g i ≤ Nat.ceil X) = Finset.univ := by
      apply Finset.filter_true_of_mem
      intro i _
      have h1 : (g i : ℝ) ≤ ((Nat.ceil X : ℕ) : ℝ) := le_trans (hnX i) hY
      exact_mod_cast h1
    have hm : (Fintype.card ι : ℝ) = ((Finset.univ.filter (fun i => g i ≤ Nat.ceil X)).card : ℝ) := by
      rw [hs_eq, Finset.card_univ]
    rw [hm]
    calc ((Finset.univ.filter (fun i => g i ≤ Nat.ceil X)).card : ℝ)
        ≤ c * ((Nat.ceil X : ℕ) : ℝ)^β := hcard (Nat.ceil X)
      _ ≤ c * X^β := mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow_of_nonpos hXpos hY (le_of_lt hβ)) hc

/-- **van der Waerden counting-to-sum bound (finite type form, uniform constant).**

There is a constant `C ≥ 0`, depending only on `α < β`, such that for *every* finite type
`ι`, every `g : ι → ℕ` with values in `[1, X]` whose counting function satisfies
`#{i : g i ≤ Y} ≤ c · Y^β` for every `Y : ℕ`, one has
`∑ i, (g i)^{-α} ≤ C · c · X^{β-α}`. -/
theorem exists_sum_rpow_neg_le_of_card_le_fintype (α β : ℝ) (hαβ : α < β) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {ι : Type*} [Fintype ι] (g : ι → ℕ) (c X : ℝ), 0 ≤ c → 1 ≤ X →
      (∀ i, 1 ≤ g i) → (∀ i, (g i : ℝ) ≤ X) →
      (∀ Y : ℕ, ((Finset.univ.filter (fun i => g i ≤ Y)).card : ℝ) ≤ c * (Y : ℝ) ^ β) →
      ∑ i, ((g i : ℝ) ^ (-α)) ≤ C * c * X ^ (β - α) := by
  refine ⟨max 1 (1 / (1 - α/β)), le_trans zero_le_one (le_max_left _ _), ?_⟩
  intro ι inst g c X hc hX hge hle hcard
  letI := inst
  by_cases hc0 : c = 0
  · have hcardX := card_le_of_card_filter_le_fintype g hc hX hle hcard
    rw [hc0, zero_mul] at hcardX
    have hcard0 : Fintype.card ι = 0 := by
      have : (Fintype.card ι : ℝ) = 0 := le_antisymm hcardX (by positivity)
      exact_mod_cast this
    haveI : IsEmpty ι := Fintype.card_eq_zero_iff.mp hcard0
    rw [Finset.sum_eq_zero (fun i _ => isEmptyElim i), hc0]
    simp
  · have hcpos : 0 < c := lt_of_le_of_ne hc (Ne.symm hc0)
    have hXpos : (0:ℝ) < X := lt_of_lt_of_le zero_lt_one hX
    by_cases hα : α ≤ 0
    · have hcardX : (Fintype.card ι : ℝ) ≤ c * X^β := card_le_of_card_filter_le_fintype g hc hX hle hcard
      have hterm : ∀ i, (g i : ℝ)^(-α) ≤ X^(-α) := by
        intro i
        have hgi0 : (0:ℝ) ≤ (g i : ℝ) := by positivity
        exact Real.rpow_le_rpow hgi0 (hle i) (by linarith)
      have hsum : ∑ i, (g i : ℝ)^(-α) ≤ (Fintype.card ι : ℝ) * X^(-α) := by
        calc ∑ i, (g i : ℝ)^(-α) ≤ ∑ i, X^(-α) := Finset.sum_le_sum (fun i _ => hterm i)
          _ = (Fintype.card ι : ℝ) * X^(-α) := by
                rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      have hXneg : 0 ≤ X^(-α) := Real.rpow_nonneg (le_of_lt hXpos) _
      calc ∑ i, (g i : ℝ)^(-α)
          ≤ (Fintype.card ι : ℝ) * X^(-α) := hsum
        _ ≤ (c * X^β) * X^(-α) := mul_le_mul_of_nonneg_right hcardX hXneg
        _ = c * X^(β - α) := by rw [mul_assoc, ← Real.rpow_add hXpos]; congr 1
        _ ≤ max 1 (1/(1-α/β)) * c * X^(β-α) := by
            have hle1 : (1:ℝ) ≤ max 1 (1/(1-α/β)) := le_max_left _ _
            have hnn : 0 ≤ c * X^(β-α) := by
              have := Real.rpow_nonneg (le_of_lt hXpos) (β-α); positivity
            calc c * X^(β-α) = 1 * (c*X^(β-α)) := by ring
              _ ≤ max 1 (1/(1-α/β)) * (c*X^(β-α)) := mul_le_mul_of_nonneg_right hle1 hnn
              _ = max 1 (1/(1-α/β)) * c * X^(β-α) := by ring
    · rw [not_le] at hα
      have hαpos : 0 < α := hα
      have hβpos : 0 < β := lt_trans hαpos hαβ
      have hγpos : 0 < α/β := div_pos hαpos hβpos
      have hγlt1 : α/β < 1 := by rw [div_lt_one hβpos]; exact hαβ
      have hcardX : (Fintype.card ι : ℝ) ≤ c * X^β := card_le_of_card_filter_le_fintype g hc hX hle hcard
      have hterm : ∀ i, (g i : ℝ)^(-α) ≤
          c^(α/β) * (((Finset.univ.filter (fun j => g j ≤ g i)).card : ℕ) : ℝ)^(-(α/β)) := by
        intro i
        have hgi : (0:ℝ) < (g i : ℝ) := by
          have : 1 ≤ g i := hge i
          exact_mod_cast (lt_of_lt_of_le zero_lt_one this)
        have hApos : (0:ℝ) < (((Finset.univ.filter (fun j => g j ≤ g i)).card : ℕ) : ℝ) := by
          have : 0 < (Finset.univ.filter (fun j => g j ≤ g i)).card :=
            Finset.card_pos.mpr ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ i, le_refl (g i)⟩⟩
          exact_mod_cast this
        exact rpow_neg_le_of_le_mul_rpow (g i : ℝ) c α β _ hgi hcpos hαpos hβpos hApos (hcard (g i))
      have hstep1 : ∑ i, (g i : ℝ)^(-α)
          ≤ c^(α/β) * ∑ i, (((Finset.univ.filter (fun j => g j ≤ g i)).card : ℕ) : ℝ)^(-(α/β)) := by
        rw [Finset.mul_sum]
        exact Finset.sum_le_sum (fun i _ => hterm i)
      have hψ : ∀ a b : ℕ, 1 ≤ a → a ≤ b → (b:ℝ)^(-(α/β)) ≤ (a:ℝ)^(-(α/β)) := by
        intro a b ha hab
        have hapos : (0:ℝ) < (a:ℝ) := by exact_mod_cast (lt_of_lt_of_le zero_lt_one ha)
        have hab' : (a:ℝ) ≤ (b:ℝ) := by exact_mod_cast hab
        exact Real.rpow_le_rpow_of_nonpos hapos hab' (by linarith)
      have hrank := sum_antitone_rank_le g (fun j => (j:ℝ)^(-(α/β))) hψ
      have hharm := sum_Icc_rpow_neg_le (α/β) hγpos hγlt1 (Fintype.card ι)
      have hcard_rpow : ((Fintype.card ι : ℕ):ℝ)^(1-α/β) ≤ (c*X^β)^(1-α/β) :=
        Real.rpow_le_rpow (by positivity) hcardX (by linarith)
      have hcard_rpow2 : (c*X^β)^(1-α/β) = c^(1-α/β) * X^(β-α) := by
        rw [Real.mul_rpow (le_of_lt hcpos) (Real.rpow_nonneg (le_of_lt hXpos) β)]
        congr 1
        rw [← Real.rpow_mul (le_of_lt hXpos)]
        congr 1
        field_simp
      have hcard_rpow' : ((Fintype.card ι : ℕ):ℝ)^(1-α/β) ≤ c^(1-α/β) * X^(β-α) := by
        rw [hcard_rpow2] at hcard_rpow; exact hcard_rpow
      have hcc : c^(α/β) * c^(1-α/β) = c := by
        rw [← Real.rpow_add hcpos]
        have : α/β + (1 - α/β) = 1 := by ring
        rw [this, Real.rpow_one]
      have hγsub : 0 < 1 - α/β := by linarith
      have hns : 0 ≤ 1/(1-α/β) := div_nonneg zero_le_one (le_of_lt hγsub)
      have hcpos' : 0 ≤ c^(α/β) := Real.rpow_nonneg (le_of_lt hcpos) _
      calc ∑ i, (g i : ℝ)^(-α)
          ≤ c^(α/β) * ∑ i, (((Finset.univ.filter (fun j => g j ≤ g i)).card : ℕ) : ℝ)^(-(α/β)) := hstep1
        _ ≤ c^(α/β) * ∑ j ∈ Finset.Icc 1 (Fintype.card ι), (j:ℝ)^(-(α/β)) :=
              mul_le_mul_of_nonneg_left hrank hcpos'
        _ ≤ c^(α/β) * ((1/(1-α/β)) * ((Fintype.card ι : ℕ):ℝ)^(1-α/β)) :=
              mul_le_mul_of_nonneg_left hharm hcpos'
        _ ≤ c^(α/β) * ((1/(1-α/β)) * (c^(1-α/β) * X^(β-α))) := by
              apply mul_le_mul_of_nonneg_left _ hcpos'
              apply mul_le_mul_of_nonneg_left hcard_rpow' hns
        _ = (1/(1-α/β)) * c * X^(β-α) := by
              rw [show c^(α/β) * ((1/(1-α/β)) * (c^(1-α/β) * X^(β-α)))
                    = (1/(1-α/β)) * (c^(α/β) * c^(1-α/β)) * X^(β-α) by ring]
              rw [hcc]
        _ ≤ max 1 (1/(1-α/β)) * c * X^(β-α) := by
              have hle1 : (1/(1-α/β)) ≤ max 1 (1/(1-α/β)) := le_max_right _ _
              have hnn : 0 ≤ c * X^(β-α) := by
                have := Real.rpow_nonneg (le_of_lt hXpos) (β-α); positivity
              calc (1/(1-α/β)) * c * X^(β-α) = (1/(1-α/β)) * (c * X^(β-α)) := by ring
                _ ≤ max 1 (1/(1-α/β)) * (c * X^(β-α)) := mul_le_mul_of_nonneg_right hle1 hnn
                _ = max 1 (1/(1-α/β)) * c * X^(β-α) := by ring

end Commons.Analysis.Sum
