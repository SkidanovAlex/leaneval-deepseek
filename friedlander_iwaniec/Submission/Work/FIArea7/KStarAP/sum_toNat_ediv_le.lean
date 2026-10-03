import Mathlib

namespace Work.FIArea7.KStarAP

lemma sum_toNat_ediv_le (κ tlo thi : ℤ) (hκ : 0 < κ) (h : tlo ≤ thi) :
    ∑ e ∈ Finset.Ico (0:ℤ) κ, ((thi - e) / κ + (e - tlo) / κ).toNat
      ≤ (thi + 1 - tlo).toNat - 1 := by
  have hs : 0 ≤ thi - tlo := by omega
  -- Each summand is at most `((thi - tlo)/κ).toNat`, since floor division is
  -- subadditive and `(thi - e) + (e - tlo) = thi - tlo`.
  have hterm : ∀ e ∈ Finset.Ico (0:ℤ) κ,
      ((thi - e) / κ + (e - tlo) / κ).toNat ≤ ((thi - tlo) / κ).toNat := by
    intro e _
    apply Int.toNat_le_toNat
    have h2 := Int.ediv_add_ediv_le_add_ediv (x := thi - e) (y := e - tlo) (z := κ) hκ
    have h3 : (thi - e) + (e - tlo) = thi - tlo := by ring
    rwa [h3] at h2
  have hQ : 0 ≤ (thi - tlo) / κ := Int.ediv_nonneg hs hκ.le
  -- The sum of a constant over `Ico 0 κ` equals `κ.toNat` times that constant.
  have hcard : (∑ e ∈ Finset.Ico (0:ℤ) κ, ((thi - tlo) / κ).toNat)
      = κ.toNat * ((thi - tlo) / κ).toNat := by
    rw [Finset.sum_const, Int.card_Ico, sub_zero, nsmul_eq_mul]
    simp
  -- `κ.toNat * ((thi - tlo)/κ).toNat ≤ (thi - tlo).toNat`.
  have hmulle : κ.toNat * ((thi - tlo) / κ).toNat ≤ (thi - tlo).toNat := by
    rw [← Int.toNat_mul hκ.le hQ]
    apply Int.toNat_le_toNat
    have := Int.ediv_mul_le (thi - tlo) (ne_of_gt hκ)
    rwa [mul_comm] at this
  -- `(thi - tlo).toNat = (thi + 1 - tlo).toNat - 1`.
  have heq : (thi - tlo).toNat = (thi + 1 - tlo).toNat - 1 := by
    have h1 : (thi + 1 - tlo : ℤ) = (thi - tlo) + 1 := by ring
    have h2 : (thi + 1 - tlo).toNat = (thi - tlo).toNat + 1 := by
      rw [h1, Int.toNat_add hs (by norm_num : (0:ℤ) ≤ 1)]
      norm_num
    rw [h2]; omega
  calc
    ∑ e ∈ Finset.Ico (0:ℤ) κ, ((thi - e) / κ + (e - tlo) / κ).toNat
        ≤ ∑ e ∈ Finset.Ico (0:ℤ) κ, ((thi - tlo) / κ).toNat := Finset.sum_le_sum hterm
    _ = κ.toNat * ((thi - tlo) / κ).toNat := hcard
    _ ≤ (thi - tlo).toNat := hmulle
    _ = (thi + 1 - tlo).toNat - 1 := heq

end Work.FIArea7.KStarAP
