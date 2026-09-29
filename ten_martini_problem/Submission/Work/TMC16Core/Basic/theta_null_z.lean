import Mathlib
import Submission.Work.TMC16Core.Defs
import Submission.Work.TMC16Core.Basic.freq_int_atTop
import Submission.Work.TMC16Core.Basic.freq_int_atBot
import Submission.Work.TMC16Core.Basic.volume_nearColl_inter_le
import Submission.Work.TMC16Core.Basic.tsum_ofReal_inv_sq_tail

open MeasureTheory Filter Topology Set
open Work.TMC16Core

namespace Work.TMC16Core.Basic


private def nearColl (β : ℝ) : Set ℝ :=
  {θ : ℝ | ∃ᶠ n : ℕ in atTop, Work.TMC16Core.fracDist (2 * θ + (n : ℝ) * β) < ((n : ℝ))⁻¹ ^ 2}

private lemma volume_nearColl_inter (β a : ℝ) :
    volume (nearColl β ∩ Ico a (a + 1 / 2)) = 0 := by
  have key : ∀ N : ℕ, 2 ≤ N →
      volume (nearColl β ∩ Ico a (a + 1 / 2))
        ≤ ∑' m : ℕ, ENNReal.ofReal (3 * (((N + m : ℕ) : ℝ))⁻¹ ^ 2) := by
    intro N hN
    have hsub : nearColl β ∩ Ico a (a + 1 / 2) ⊆
        ⋃ m : ℕ, ({θ : ℝ | Work.TMC16Core.fracDist (2 * θ + ((N + m : ℕ) : ℝ) * β) <
            (((N + m : ℕ) : ℝ))⁻¹ ^ 2} ∩ Ico a (a + 1 / 2)) := by
      rintro θ ⟨hf, hI⟩
      simp only [nearColl, Set.mem_setOf_eq] at hf
      rw [Filter.frequently_atTop] at hf
      obtain ⟨n, hn, hlt⟩ := hf N
      obtain ⟨m, rfl⟩ : ∃ m : ℕ, n = N + m := ⟨n - N, (Nat.add_sub_cancel' hn).symm⟩
      exact Set.mem_iUnion.mpr ⟨m, hlt, hI⟩
    calc volume (nearColl β ∩ Ico a (a + 1 / 2))
        ≤ volume (⋃ m : ℕ, ({θ : ℝ |
              Work.TMC16Core.fracDist (2 * θ + ((N + m : ℕ) : ℝ) * β) <
                (((N + m : ℕ) : ℝ))⁻¹ ^ 2} ∩ Ico a (a + 1 / 2))) :=
          measure_mono hsub
      _ ≤ ∑' m : ℕ, volume ({θ : ℝ |
              Work.TMC16Core.fracDist (2 * θ + ((N + m : ℕ) : ℝ) * β) <
                (((N + m : ℕ) : ℝ))⁻¹ ^ 2} ∩ Ico a (a + 1 / 2)) :=
          measure_iUnion_le _
      _ ≤ ∑' m : ℕ, ENNReal.ofReal (3 * (((N + m : ℕ) : ℝ))⁻¹ ^ 2) := by
          refine ENNReal.tsum_le_tsum (fun m => ?_)
          refine volume_nearColl_inter_le _ _ a (by positivity) ?_
          have h2 : (2 : ℝ) ≤ ((N + m : ℕ) : ℝ) := by
            have h : (2 : ℕ) ≤ N + m := le_trans hN (Nat.le_add_right N m)
            exact_mod_cast h
          have hpos : (0 : ℝ) < ((N + m : ℕ) : ℝ) := lt_of_lt_of_le (by norm_num) h2
          have hinv : (((N + m : ℕ) : ℝ))⁻¹ ≤ 1 / 2 := by
            have h2' : 1 / ((N + m : ℕ) : ℝ) ≤ 1 / 2 :=
              one_div_le_one_div_of_le (show (0 : ℝ) < 2 by norm_num) h2
            simpa [one_div] using h2'
          calc (((N + m : ℕ) : ℝ))⁻¹ ^ 2 ≤ (1 / 2 : ℝ) ^ 2 :=
                pow_le_pow_left₀ (by positivity) hinv 2
            _ = 1 / 4 := by norm_num
            _ ≤ 1 / 2 := by norm_num
  have hev : ∀ᶠ N : ℕ in atTop,
      volume (nearColl β ∩ Ico a (a + 1 / 2))
        ≤ ∑' m : ℕ, ENNReal.ofReal (3 * (((N + m : ℕ) : ℝ))⁻¹ ^ 2) :=
    Filter.eventually_atTop.mpr ⟨2, fun N hN => key N hN⟩
  exact le_antisymm
    (le_of_tendsto_of_tendsto tendsto_const_nhds tsum_ofReal_inv_sq_tail hev)
    bot_le

private lemma countable_exactColl (α : ℝ) :
    ({θ : ℝ | ∃ m z : ℤ, 2 * θ + (m : ℝ) * α = (z : ℝ)} : Set ℝ).Countable := by
  refine Set.Countable.mono ?_ (Set.countable_range
    (fun p : ℤ × ℤ => (((p.2 : ℝ) - (p.1 : ℝ) * α) / 2)))
  rintro θ ⟨m, z, hz⟩
  refine ⟨(m, z), ?_⟩
  simp only [Set.mem_range]
  linarith

private lemma nearColl_eq_atTop (α : ℝ) :
    ({θ : ℝ | ∃ᶠ k : ℤ in atTop,
        Work.TMC16Core.fracDist (2 * θ + (k : ℝ) * α) < (((k.natAbs : ℕ) : ℝ))⁻¹ ^ 2}
      : Set ℝ) = nearColl α := by
  ext θ
  simp only [nearColl, Set.mem_setOf_eq]
  rw [freq_int_atTop]
  refine Filter.frequently_congr (Filter.Eventually.of_forall (fun n => ?_))
  simp

private lemma nearColl_eq_atBot (α : ℝ) :
    ({θ : ℝ | ∃ᶠ k : ℤ in atBot,
        Work.TMC16Core.fracDist (2 * θ + (k : ℝ) * α) < (((k.natAbs : ℕ) : ℝ))⁻¹ ^ 2}
      : Set ℝ) = nearColl (-α) := by
  ext θ
  simp only [nearColl, Set.mem_setOf_eq]
  rw [freq_int_atBot]
  refine Filter.frequently_congr (Filter.Eventually.of_forall (fun n => ?_))
  simp only [Int.natAbs_neg, Int.natAbs_natCast, Int.cast_neg, Int.cast_natCast]
  ring_nf

private lemma volume_Theta_inter (α a : ℝ) :
    volume (Work.TMC16Core.Theta α ∩ Ico a (a + 1 / 2)) = 0 := by
  have hS1z : volume (({θ : ℝ | ∃ᶠ k : ℤ in atTop,
        Work.TMC16Core.fracDist (2 * θ + (k : ℝ) * α) <
          (((k.natAbs : ℕ) : ℝ))⁻¹ ^ 2} : Set ℝ) ∩ Ico a (a + 1 / 2)) = 0 := by
    rw [nearColl_eq_atTop α]
    exact volume_nearColl_inter α a
  have hS2z : volume (({θ : ℝ | ∃ᶠ k : ℤ in atBot,
        Work.TMC16Core.fracDist (2 * θ + (k : ℝ) * α) <
          (((k.natAbs : ℕ) : ℝ))⁻¹ ^ 2} : Set ℝ) ∩ Ico a (a + 1 / 2)) = 0 := by
    rw [nearColl_eq_atBot α]
    exact volume_nearColl_inter (-α) a
  have hEz : volume (({θ : ℝ | ∃ m z : ℤ,
        2 * θ + (m : ℝ) * α = (z : ℝ)} : Set ℝ) ∩ Ico a (a + 1 / 2)) = 0 :=
    ((countable_exactColl α).mono Set.inter_subset_left).measure_zero volume
  have hEq : Work.TMC16Core.Theta α ∩ Ico a (a + 1 / 2)
      = (({θ : ℝ | ∃ᶠ k : ℤ in atTop,
            Work.TMC16Core.fracDist (2 * θ + (k : ℝ) * α) <
              (((k.natAbs : ℕ) : ℝ))⁻¹ ^ 2} : Set ℝ) ∩ Ico a (a + 1 / 2))
        ∪ ((({θ : ℝ | ∃ᶠ k : ℤ in atBot,
              Work.TMC16Core.fracDist (2 * θ + (k : ℝ) * α) <
                (((k.natAbs : ℕ) : ℝ))⁻¹ ^ 2} : Set ℝ) ∩ Ico a (a + 1 / 2))
          ∪ (({θ : ℝ | ∃ m z : ℤ,
                2 * θ + (m : ℝ) * α = (z : ℝ)} : Set ℝ) ∩ Ico a (a + 1 / 2))) := by
    ext θ
    simp only [Work.TMC16Core.Theta, Set.mem_inter_iff, Set.mem_union, Set.mem_setOf_eq]
    tauto
  rw [hEq]
  exact measure_union_null hS1z (measure_union_null hS2z hEz)

theorem theta_null_z (α : ℝ) (hα : Irrational α) :
    MeasureTheory.volume (Work.TMC16Core.Theta α) = 0 := by
  have hcover : Work.TMC16Core.Theta α ⊆
      ⋃ j : ℤ, Ico ((j : ℝ) / 2) ((j : ℝ) / 2 + 1 / 2) := by
    intro θ hθ
    refine Set.mem_iUnion.mpr ⟨⌊2 * θ⌋, ?_⟩
    rw [Set.mem_Ico]
    constructor
    · have := Int.floor_le (2 * θ)
      linarith
    · have := Int.lt_floor_add_one (2 * θ)
      linarith
  have hsubset : Work.TMC16Core.Theta α ⊆
      ⋃ j : ℤ, (Work.TMC16Core.Theta α ∩ Ico ((j : ℝ) / 2) ((j : ℝ) / 2 + 1 / 2)) := by
    intro θ hθ
    obtain ⟨j, hj⟩ := Set.mem_iUnion.mp (hcover hθ)
    exact Set.mem_iUnion.mpr ⟨j, hθ, hj⟩
  have hle : volume (Work.TMC16Core.Theta α) ≤ 0 := by
    calc volume (Work.TMC16Core.Theta α)
        ≤ volume (⋃ j : ℤ,
            (Work.TMC16Core.Theta α ∩ Ico ((j : ℝ) / 2) ((j : ℝ) / 2 + 1 / 2))) :=
          measure_mono hsubset
      _ ≤ ∑' j : ℤ,
            volume (Work.TMC16Core.Theta α ∩ Ico ((j : ℝ) / 2) ((j : ℝ) / 2 + 1 / 2)) :=
          measure_iUnion_le _
      _ = 0 := by
          have hz : (fun j : ℤ =>
              volume (Work.TMC16Core.Theta α ∩ Ico ((j : ℝ) / 2) ((j : ℝ) / 2 + 1 / 2)))
              = fun _ => 0 := by
            funext j
            exact volume_Theta_inter α ((j : ℝ) / 2)
          rw [hz, tsum_zero]
  exact le_antisymm hle bot_le

end Work.TMC16Core.Basic
