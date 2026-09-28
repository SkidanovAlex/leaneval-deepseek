import Mathlib
import Submission.Work.HP.Defs
import Submission.Work.HP.MinkDefs
import Submission.Work.HP.lam_basic
import Submission.Work.HP.FM.minkowski_lower
import Submission.Work.HP.Lat.detL_ge_one
import Submission.Work.HP.MDEstimates.detL_le_prod_lam

namespace Work.HP.MM2

theorem pow_div_lamprod_le {ι : Type*} [Fintype ι] [DecidableEq ι] (L : Submodule ℤ (ι → ℤ)) {T μ : ℝ} {m : ℕ}
    (hT : 1 ≤ T) (hμ : 1 ≤ μ) (hν : Work.HP.lam L (Work.HP.rk L) ≤ μ) (hm1 : 1 ≤ m) (hmR : m ≤ Work.HP.rk L) :
    T ^ (m - 1) / (∏ i ∈ Finset.range m, Work.HP.lam L (i + 1)) ≤
      (T ^ (Work.HP.rk L - 1) + μ ^ (Work.HP.rk L - 1)) / Work.HP.detL L := by
  classical
  set A := ∏ i ∈ Finset.range m, Work.HP.lam L (i + 1) with hAdef
  have hApos : 0 < A := by
    rw [hAdef]
    exact Finset.prod_pos (fun i hi => Work.HP.lam_pos L (by omega) (by have := Finset.mem_range.mp hi; omega))
  have hdetpos : 0 < Work.HP.detL L := lt_of_lt_of_le one_pos (Work.HP.Lat.detL_ge_one L)
  rw [div_le_div_iff₀ hApos hdetpos]
  have hsub : Finset.range m ⊆ Finset.range (Work.HP.rk L) := Finset.range_subset_range.mpr hmR
  have hsplit : (∏ i ∈ Finset.range (Work.HP.rk L), Work.HP.lam L (i + 1))
      = A * (∏ i ∈ Finset.range (Work.HP.rk L) \ Finset.range m, Work.HP.lam L (i + 1)) := by
    have h := Finset.prod_sdiff (f := fun i => Work.HP.lam L (i + 1)) hsub
    rw [hAdef, ← h, mul_comm]
  have hcard : (Finset.range (Work.HP.rk L) \ Finset.range m).card = Work.HP.rk L - m := by
    rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hsub, Finset.card_range, Finset.card_range]
  have htail : (∏ i ∈ Finset.range (Work.HP.rk L) \ Finset.range m, Work.HP.lam L (i + 1))
      ≤ μ ^ (Work.HP.rk L - m) := by
    calc (∏ i ∈ Finset.range (Work.HP.rk L) \ Finset.range m, Work.HP.lam L (i + 1))
        ≤ ∏ _i ∈ Finset.range (Work.HP.rk L) \ Finset.range m, μ := by
          apply Finset.prod_le_prod₀
          · intro i hi
            have hiR : i < Work.HP.rk L := Finset.mem_range.mp (Finset.mem_sdiff.mp hi).1
            exact le_of_lt (Work.HP.lam_pos L (by omega) (by omega))
          · intro i hi
            have hiR : i < Work.HP.rk L := Finset.mem_range.mp (Finset.mem_sdiff.mp hi).1
            have him : m ≤ i := by
              have h2 := (Finset.mem_sdiff.mp hi).2
              simp only [Finset.mem_range] at h2
              omega
            calc Work.HP.lam L (i + 1) ≤ Work.HP.lam L (Work.HP.rk L) :=
                  Work.HP.lam_mono L (by omega) le_rfl
              _ ≤ μ := hν
      _ = μ ^ (Finset.range (Work.HP.rk L) \ Finset.range m).card := Finset.prod_const μ
      _ = μ ^ (Work.HP.rk L - m) := by rw [hcard]
  have hstep1 : Work.HP.detL L ≤ A * μ ^ (Work.HP.rk L - m) := by
    calc Work.HP.detL L
        ≤ ∏ i ∈ Finset.range (Work.HP.rk L), Work.HP.lam L (i + 1) :=
          Work.HP.MDEstimates.detL_le_prod_lam L
      _ = A * (∏ i ∈ Finset.range (Work.HP.rk L) \ Finset.range m, Work.HP.lam L (i + 1)) := hsplit
      _ ≤ A * μ ^ (Work.HP.rk L - m) := mul_le_mul_of_nonneg_left htail (le_of_lt hApos)
  have hexp : m - 1 + (Work.HP.rk L - m) = Work.HP.rk L - 1 := by omega
  have hstep2 : T ^ (m - 1) * μ ^ (Work.HP.rk L - m)
      ≤ T ^ (Work.HP.rk L - 1) + μ ^ (Work.HP.rk L - 1) := by
    rcases le_total T μ with h | h
    · calc T ^ (m - 1) * μ ^ (Work.HP.rk L - m)
          ≤ μ ^ (m - 1) * μ ^ (Work.HP.rk L - m) :=
            mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by linarith) h _) (pow_nonneg (by linarith) _)
        _ = μ ^ (Work.HP.rk L - 1) := by rw [← pow_add, hexp]
        _ ≤ T ^ (Work.HP.rk L - 1) + μ ^ (Work.HP.rk L - 1) :=
            le_add_of_nonneg_left (pow_nonneg (by linarith) _)
    · calc T ^ (m - 1) * μ ^ (Work.HP.rk L - m)
          ≤ T ^ (m - 1) * T ^ (Work.HP.rk L - m) :=
            mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by linarith) h _) (pow_nonneg (by linarith) _)
        _ = T ^ (Work.HP.rk L - 1) := by rw [← pow_add, hexp]
        _ ≤ T ^ (Work.HP.rk L - 1) + μ ^ (Work.HP.rk L - 1) :=
            le_add_of_nonneg_right (pow_nonneg (by linarith) _)
  calc T ^ (m - 1) * Work.HP.detL L ≤ T ^ (m - 1) * (A * μ ^ (Work.HP.rk L - m)) :=
        mul_le_mul_of_nonneg_left hstep1 (pow_nonneg (by linarith) _)
    _ = (T ^ (m - 1) * μ ^ (Work.HP.rk L - m)) * A := by ring
    _ ≤ (T ^ (Work.HP.rk L - 1) + μ ^ (Work.HP.rk L - 1)) * A :=
        mul_le_mul_of_nonneg_right hstep2 (le_of_lt hApos)

end Work.HP.MM2
