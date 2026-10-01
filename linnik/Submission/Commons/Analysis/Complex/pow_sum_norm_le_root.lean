import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.LinearAlgebra.Complex.FiniteDimensional

namespace Commons.Analysis.Complex

theorem pow_sum_norm_le_root {ι : Type*} [Fintype ι] (z : ι → ℂ) {a b : ℝ}
    (ha : 0 < a) (hb : 0 < b)
    (h : ∀ n : ℕ, 0 < n → ‖∑ i, (z i) ^ n‖ ≤ a * b ^ n) :
    ∀ i, ‖z i‖ ≤ b := by
  classical
  by_cases hne : Nonempty ι
  · haveI : Nonempty ι := hne
    obtain ⟨i0, -, hi0⟩ :=
      Finset.exists_max_image (Finset.univ : Finset ι) (fun i => ‖z i‖) Finset.univ_nonempty
    by_cases hble : ‖z i0‖ ≤ b
    · intro i
      exact le_trans (hi0 i (Finset.mem_univ i)) hble
    · push_neg at hble
      exfalso
      set W : ℝ := ‖z i0‖ with hW
      have hWpos : 0 < W := by rw [hW]; exact lt_trans hb hble
      have hWb : 0 < W - b := by linarith
      have hzi0 : z i0 ≠ 0 := by
        intro hz
        have h1 : ‖z i0‖ = 0 := by rw [hz, norm_zero]
        rw [← hW] at h1
        linarith
      set u : ι → ℂ := fun i => z i / z i0 with hu
      have hu_norm : ∀ i, ‖u i‖ ≤ 1 := by
        intro i
        simp only [hu]
        rw [norm_div]
        exact div_le_one_of_le₀ (hi0 i (Finset.mem_univ i)) (le_of_lt (by rw [← hW]; exact hWpos))
      have hu_i0 : u i0 = 1 := by
        simp only [hu]
        exact div_self hzi0
      -- choose the parameter s
      set C : ℝ := (Fintype.card ι : ℝ) + a * b / (W - b) with hC
      have hCnn : 0 ≤ C := by
        rw [hC]
        have h1 : (0 : ℝ) ≤ (Fintype.card ι : ℝ) := by positivity
        have h2 : 0 ≤ a * b / (W - b) := div_nonneg (mul_nonneg ha.le hb.le) hWb.le
        linarith
      set δ : ℝ := 1 / (2 * (C + 1)) with hδ
      have hCp1 : 0 < C + 1 := by linarith
      have hδpos : 0 < δ := by rw [hδ]; positivity
      have hδlt1 : δ < 1 := by
        rw [hδ, div_lt_one (by linarith : (0 : ℝ) < 2 * (C + 1))]
        linarith
      set s : ℝ := 1 - δ with hs
      have hs_pos : 0 < s := by rw [hs]; linarith
      have hs_lt_one : s < 1 := by rw [hs]; linarith
      have hs1 : 1 - s = δ := by rw [hs]; ring
      have hrec : 1 / (1 - s) = 2 * (C + 1) := by
        rw [hs1, hδ, one_div, one_div, inv_inv]
      -- the power series
      set F : ℕ → ℂ := fun n => (s : ℂ) ^ n * (∑ i, z i ^ n) / (z i0) ^ n with hF
      set L : ℂ := ∑ i, (1 - (s : ℂ) * u i)⁻¹ with hL
      have hs_norm_lt : ∀ i, ‖(s : ℂ) * u i‖ < 1 := by
        intro i
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hs_pos]
        calc s * ‖u i‖ ≤ s * 1 := mul_le_mul_of_nonneg_left (hu_norm i) hs_pos.le
          _ = s := by ring
          _ < 1 := hs_lt_one
      have hgeom : ∀ i, HasSum (fun n : ℕ => ((s : ℂ) * u i) ^ n) ((1 - (s : ℂ) * u i)⁻¹) :=
        fun i => hasSum_geometric_of_norm_lt_one (hs_norm_lt i)
      have hfin : HasSum (fun n : ℕ => ∑ i, ((s : ℂ) * u i) ^ n) (∑ i, (1 - (s : ℂ) * u i)⁻¹) :=
        hasSum_sum (fun i _ => hgeom i)
      have hF_eq : (fun n : ℕ => ∑ i, ((s : ℂ) * u i) ^ n) = F := by
        funext n
        change ∑ i, ((s : ℂ) * u i) ^ n = (s : ℂ) ^ n * (∑ i, z i ^ n) / (z i0) ^ n
        rw [Finset.mul_sum, Finset.sum_div]
        apply Finset.sum_congr rfl
        intro i _
        simp only [hu]
        rw [mul_pow, div_pow]
        ring
      have hkey : HasSum F L := by
        rw [← hF_eq, hL]
        exact hfin
      have hsumm : Summable (fun n => ‖F n‖) := hkey.summable.norm
      have hnorm : ‖L‖ ≤ ∑' n, ‖F n‖ := by
        rw [← hkey.tsum_eq]
        exact norm_tsum_le_tsum_norm hsumm
      have hF0 : ‖F 0‖ = (Fintype.card ι : ℝ) := by
        have h0 : F 0 = (Fintype.card ι : ℂ) := by simp [hF]
        rw [h0, Complex.norm_natCast]
      have htail : ∑' n, ‖F (n + 1)‖ ≤ a * b / (W - b) := by
        set r : ℝ := b / W with hr
        have hrnn : 0 ≤ r := by rw [hr]; exact div_nonneg hb.le hWpos.le
        have hr1 : r < 1 := by rw [hr, div_lt_one hWpos, hW]; exact hble
        have hsumm_tail : Summable (fun n => ‖F (n + 1)‖) := (summable_nat_add_iff 1).mpr hsumm
        have hsumm_g : Summable (fun n => a * r * r ^ n) :=
          (summable_geometric_of_lt_one hrnn hr1).mul_left (a * r)
        have hcmp : ∀ n, ‖F (n + 1)‖ ≤ a * r * r ^ n := by
          intro n
          have hpow : s ^ (n + 1) ≤ 1 := pow_le_one₀ hs_pos.le hs_lt_one.le
          have hrn : 0 ≤ r ^ (n + 1) := pow_nonneg hrnn _
          calc ‖F (n + 1)‖
              = s ^ (n + 1) * ‖∑ i, z i ^ (n + 1)‖ / W ^ (n + 1) := by
                  simp only [hF, norm_div, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs,
                    abs_of_pos hs_pos, ← hW]
            _ ≤ s ^ (n + 1) * (a * b ^ (n + 1)) / W ^ (n + 1) := by
                  gcongr
                  exact h (n + 1) (Nat.succ_pos n)
            _ = a * s ^ (n + 1) * r ^ (n + 1) := by
                  rw [hr, div_pow]; ring
            _ ≤ a * r ^ (n + 1) := by
                  have h1 : a * s ^ (n + 1) ≤ a * 1 := mul_le_mul_of_nonneg_left hpow ha.le
                  calc a * s ^ (n + 1) * r ^ (n + 1) ≤ a * 1 * r ^ (n + 1) :=
                        mul_le_mul_of_nonneg_right h1 hrn
                    _ = a * r ^ (n + 1) := by ring
            _ = a * r * r ^ n := by ring
        calc ∑' n, ‖F (n + 1)‖ ≤ ∑' n, a * r * r ^ n :=
              Summable.tsum_le_tsum hcmp hsumm_tail hsumm_g
          _ = a * r * (1 - r)⁻¹ := by
              rw [Summable.tsum_mul_left (a * r) (summable_geometric_of_lt_one hrnn hr1),
                tsum_geometric_of_lt_one hrnn hr1]
          _ = a * b / (W - b) := by
              rw [hr]
              have hWne : W ≠ 0 := ne_of_gt hWpos
              have hWbne : W - b ≠ 0 := ne_of_gt hWb
              field_simp
      have hupper : ‖L‖ ≤ C := le_trans hnorm (by
        rw [Summable.tsum_eq_zero_add hsumm, hF0, hC]
        linarith [htail])
      -- lower bound via real part
      have hre_nonneg : ∀ i, 0 ≤ ((1 - (s : ℂ) * u i)⁻¹).re := by
        intro i
        rw [Complex.inv_re]
        have h1 : (u i).re ≤ 1 := le_trans (Complex.re_le_norm (u i)) (hu_norm i)
        have h2 : 0 ≤ (1 - (s : ℂ) * u i).re := by
          rw [Complex.sub_re, Complex.one_re, Complex.re_ofReal_mul]
          nlinarith [mul_le_mul_of_nonneg_left h1 hs_pos.le]
        exact div_nonneg h2 (Complex.normSq_nonneg _)
      have hre_i0 : ((1 - (s : ℂ) * u i0)⁻¹).re = 1 / (1 - s) := by
        rw [Complex.inv_re, hu_i0]
        have hsub : (1 - (s : ℂ) * 1) = ((1 - s : ℝ) : ℂ) := by push_cast; ring
        rw [hsub, Complex.ofReal_re, Complex.normSq_ofReal]
        have hne : (1 - s) ≠ 0 := by linarith
        field_simp
      have hlower : 1 / (1 - s) ≤ ‖L‖ := by
        have h1 : 1 / (1 - s) ≤ L.re := by
          rw [hL, Complex.re_sum]
          calc 1 / (1 - s) = ((1 - (s : ℂ) * u i0)⁻¹).re := hre_i0.symm
            _ ≤ ∑ i, ((1 - (s : ℂ) * u i)⁻¹).re :=
                Finset.single_le_sum (fun i _ => hre_nonneg i) (Finset.mem_univ i0)
        exact le_trans h1 (Complex.re_le_norm L)
      have hcontra : 2 * (C + 1) ≤ C := by
        rw [← hrec]
        exact le_trans hlower hupper
      linarith [hCnn, hcontra]
  · intro i
    exact (hne ⟨i⟩).elim

end Commons.Analysis.Complex