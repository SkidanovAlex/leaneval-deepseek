import Mathlib

namespace Work.ZeroFreeTables.Rep9

theorem shiftAbsorb {a M e C C' : ℝ} (ha : 0 < a) (hM : 0 ≤ M) (he : 0 < e)
    (hC : 0 < C) (hC' : 0 < C') :
    ∃ L₀ : ℝ, 1 ≤ L₀ ∧ ∀ {L : ℝ}, L₀ ≤ L → ∀ {x : ℝ}, 0 ≤ x → x ≤ a + M →
      (x / L) * C * (1 + x / L + (x / L) ^ 2)
        + (x / L) * C' * (1 + Real.sqrt L) * (1 + x / L + (x / L) ^ 2)
        ≤ x * e := by
  set K : ℝ := 1 + (a + M) with hKdef
  have hKpos : 0 < K := by rw [hKdef]; linarith
  have haM : 0 ≤ a + M := by linarith
  set q : ℝ := 2 * (C + C') * K^2 / e with hqdef
  have hqpos : 0 < q := by
    rw [hqdef]
    positivity
  refine ⟨max 1 (q^2), le_max_left _ _, ?_⟩
  intro L hL x hx hxM
  have hL1 : 1 ≤ L := le_trans (le_max_left _ _) hL
  have hLpos : 0 < L := lt_of_lt_of_le one_pos hL1
  have hq2L : q^2 ≤ L := le_trans (le_max_right _ _) hL
  set s : ℝ := Real.sqrt L with hsdef
  have hspos : 0 < s := by rw [hsdef]; exact Real.sqrt_pos.mpr hLpos
  have hs_nonneg : 0 ≤ s := le_of_lt hspos
  have hs_sq : s^2 = L := by rw [hsdef]; exact Real.sq_sqrt (le_of_lt hLpos)
  have hs1 : 1 ≤ s := by
    rw [hsdef]
    calc (1:ℝ) = Real.sqrt 1 := by simp
     _ ≤ Real.sqrt L := Real.sqrt_le_sqrt hL1
  have hqs : q ≤ s := by
    rw [hsdef]
    calc q = Real.sqrt (q^2) := (Real.sqrt_sq (le_of_lt hqpos)).symm
     _ ≤ Real.sqrt L := Real.sqrt_le_sqrt hq2L
  have hratio : (C + C' * (1 + s)) / L ≤ 2 * (C + C') / s := by
    have hA : C + C' * (1 + s) ≤ (C + C') * (1 + s) := by
      have hcs : 0 ≤ C * s := mul_nonneg (le_of_lt hC) hs_nonneg
      nlinarith
    have hB : (1 + s) / L ≤ 2 / s := by
      rw [div_le_iff₀ hLpos]
      have h2 : (2 / s) * L = 2 * s := by
        rw [show L = s^2 from hs_sq.symm]
        field_simp
      rw [h2]
      linarith
    calc (C + C' * (1 + s)) / L ≤ ((C + C') * (1 + s)) / L := div_le_div_of_nonneg_right hA (le_of_lt hLpos)
      _ = (C + C') * ((1 + s) / L) := by ring
      _ ≤ (C + C') * (2 / s) := mul_le_mul_of_nonneg_left hB (by linarith)
      _ = 2 * (C + C') / s := by ring
  have hy_nonneg : 0 ≤ x / L := div_nonneg hx (le_of_lt hLpos)
  have hy_le : x / L ≤ a + M := by
    have h1 : x / L ≤ (a + M) / L := div_le_div_of_nonneg_right hxM (le_of_lt hLpos)
    have h2 : (a + M) / L ≤ a + M := div_le_self haM hL1
    linarith
  have hpoly : 1 + x / L + (x / L)^2 ≤ K^2 := by
    have h1 : 1 + x / L + (x / L)^2 ≤ (1 + x/L)^2 := by nlinarith [hy_nonneg]
    have h2 : (1 + x/L)^2 ≤ K^2 := by
      rw [hKdef]
      nlinarith [hy_nonneg, hy_le]
    linarith
  have hratio_nonneg : 0 ≤ (C + C' * (1 + s)) / L :=
    div_nonneg (by nlinarith [hC, hC', hs_nonneg]) (le_of_lt hLpos)
  have hpoly_nonneg : 0 ≤ 1 + x / L + (x / L)^2 := by nlinarith [hy_nonneg]
  have hup : 0 ≤ 2 * (C + C') / s :=
    div_nonneg (mul_nonneg (by norm_num) (by linarith)) (le_of_lt hspos)
  have hbracket : (C + C' * (1 + s)) / L * (1 + x / L + (x / L)^2) ≤ (2 * (C + C') / s) * K^2 :=
    mul_le_mul hratio hpoly hpoly_nonneg hup
  have hs_ge : 2 * (C + C') * K^2 / s ≤ 2 * (C + C') * K^2 / q :=
    div_le_div_of_nonneg_left (by nlinarith [hC, hC', hKpos]) hqpos hqs
  have hqe : q * e = 2 * (C + C') * K^2 := by
    rw [hqdef]; field_simp
  have heq : 2 * (C + C') * K^2 / q = e := by
    rw [← hqe]; field_simp
  have h2 : 2 * (C + C') / s * K^2 ≤ e := by
    have h3 : 2 * (C + C') / s * K^2 = 2 * (C + C') * K^2 / s := by ring
    rw [h3]
    linarith
  have hfin : (C + C' * (1 + s)) / L * (1 + x / L + (x / L)^2) ≤ e := le_trans hbracket h2
  calc (x / L) * C * (1 + x / L + (x / L)^2) + (x / L) * C' * (1 + s) * (1 + x / L + (x / L)^2)
      = x * ((C + C' * (1 + s)) / L * (1 + x / L + (x / L)^2)) := by
          field_simp [hLpos.ne']
    _ ≤ x * e := mul_le_mul_of_nonneg_left hfin hx

end Work.ZeroFreeTables.Rep9
