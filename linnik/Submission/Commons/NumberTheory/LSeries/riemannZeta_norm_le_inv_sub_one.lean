import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.NumberTheory.LSeries.RiemannZeta

open Complex MeasureTheory
open scoped BigOperators Topology

set_option autoImplicit false

namespace Commons.NumberTheory.LSeries

/-- Integral-test bound for the `p`-series: for real `σ > 1`,
`∑' n : ℕ, n ^ (-σ) ≤ 1 + 1 / (σ - 1)`.  (The `n = 0` term vanishes.) -/
lemma tsum_nat_rpow_neg_le_inv (σ : ℝ) (hσ : 1 < σ) :
    ∑' n : ℕ, (n : ℝ) ^ (-σ) ≤ 1 + 1 / (σ - 1) := by
  have hσ0 : 0 < σ := lt_trans zero_lt_one hσ
  have hlt : -σ < -1 := by linarith
  have hnonpos : -σ ≤ 0 := by linarith
  have hanti : AntitoneOn (fun x : ℝ => x ^ (-σ)) (Set.Ici ((1 : ℕ) : ℝ)) :=
    (Real.antitoneOn_rpow_Ioi_of_exponent_nonpos hnonpos).mono (by
      intro x hx
      simp only [Set.mem_Ici] at hx
      simp only [Set.mem_Ioi]
      exact lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) (by simpa using hx))
  have hint : IntegrableOn (fun x : ℝ => x ^ (-σ)) (Set.Ioi ((1 : ℕ) : ℝ)) :=
    integrableOn_Ioi_rpow_of_lt hlt (by norm_num : (0 : ℝ) < ((1 : ℕ) : ℝ))
  have hnonneg : ∀ t ∈ Set.Ioi ((1 : ℕ) : ℝ), 0 ≤ t ^ (-σ) := by
    intro t ht
    exact Real.rpow_nonneg (le_of_lt (lt_of_lt_of_le (by norm_num : (0 : ℝ) < ((1 : ℕ) : ℝ))
      (le_of_lt ht))) _
  have hkey := AntitoneOn.tsum_comp_add_le_integral
    (f := fun x : ℝ => x ^ (-σ)) 1 hanti hint hnonneg
  have hintval : ∫ x in Set.Ioi ((1 : ℕ) : ℝ), x ^ (-σ) = 1 / (σ - 1) := by
    rw [integral_Ioi_rpow_of_lt hlt (by norm_num : (0 : ℝ) < ((1 : ℕ) : ℝ)),
      show (-σ) + 1 = 1 - σ by ring, Nat.cast_one, Real.one_rpow]
    rw [show (1 : ℝ) - σ = -(σ - 1) by ring, div_neg, neg_div, neg_neg]
  have htail : ∑' n : ℕ, ((n + 1 + 1 : ℕ) : ℝ) ^ (-σ) ≤ 1 / (σ - 1) :=
    hkey.trans hintval.le
  have hsumm : Summable (fun n : ℕ => (n : ℝ) ^ (-σ)) := Real.summable_nat_rpow.mpr hlt
  have hdecomp : ∑' n : ℕ, (n : ℝ) ^ (-σ)
      = 1 + ∑' n : ℕ, ((n + 1 + 1 : ℕ) : ℝ) ^ (-σ) := by
    have h := hsumm.sum_add_tsum_nat_add 2
    have hsum2 : ∑ i ∈ Finset.range 2, (i : ℝ) ^ (-σ) = 1 := by
      rw [Finset.sum_range_succ, Finset.sum_range_one]
      simp [Real.zero_rpow (ne_of_lt (by linarith : -σ < 0))]
    have hcong : (∑' i : ℕ, ((i + 2 : ℕ) : ℝ) ^ (-σ))
        = ∑' n : ℕ, ((n + 1 + 1 : ℕ) : ℝ) ^ (-σ) :=
      tsum_congr fun _ => rfl
    calc ∑' n : ℕ, (n : ℝ) ^ (-σ)
        = (∑ i ∈ Finset.range 2, (i : ℝ) ^ (-σ))
            + ∑' i : ℕ, ((i + 2 : ℕ) : ℝ) ^ (-σ) := h.symm
      _ = 1 + ∑' n : ℕ, ((n + 1 + 1 : ℕ) : ℝ) ^ (-σ) := by rw [hsum2, hcong]
  rw [hdecomp]
  linarith

/-- For real `σ > 1`: `‖ζ(σ)‖ ≤ 1 + 1 / (σ - 1)`. -/
lemma riemannZeta_norm_le_one_add_inv_sub_one (σ : ℝ) (hσ : 1 < σ) :
    ‖riemannZeta ((σ : ℝ) : ℂ)‖ ≤ 1 + 1 / (σ - 1) := by
  have hσ0 : 0 < σ := lt_trans zero_lt_one hσ
  have hlt : -σ < -1 := by linarith
  have hsC : 1 < (((σ : ℝ) : ℂ)).re := by simpa using hσ
  have hsummNat : Summable (fun n : ℕ => (((n + 1 : ℕ) : ℝ) ^ (-σ))) :=
    (summable_nat_add_iff 1).mpr (Real.summable_nat_rpow.mpr hlt)
  have hterm : ∀ n : ℕ,
      ‖(1 : ℂ) / ((n : ℂ) + 1) ^ (σ : ℂ)‖ = (((n + 1 : ℕ) : ℝ) ^ (-σ)) := by
    intro n
    have hcast : ((n : ℂ) + 1) = ((n + 1 : ℕ) : ℂ) := by push_cast; ring
    rw [hcast, norm_div, norm_one,
      Complex.norm_natCast_cpow_of_pos (by omega : 0 < n + 1)]
    simp only [Complex.ofReal_re]
    rw [one_div, Real.rpow_neg (by positivity : (0 : ℝ) ≤ ((n + 1 : ℕ) : ℝ))]
  have hsummNorm : Summable (fun n : ℕ => ‖(1 : ℂ) / ((n : ℂ) + 1) ^ (σ : ℂ)‖) :=
    hsummNat.congr (fun n => (hterm n).symm)
  have hnorm : ‖riemannZeta (σ : ℂ)‖ ≤ ∑' n : ℕ, (((n + 1 : ℕ) : ℝ) ^ (-σ)) := by
    rw [zeta_eq_tsum_one_div_nat_add_one_cpow (s := (σ : ℂ)) hsC]
    calc ‖∑' n : ℕ, (1 : ℂ) / ((n : ℂ) + 1) ^ (σ : ℂ)‖
        ≤ ∑' n : ℕ, ‖(1 : ℂ) / ((n : ℂ) + 1) ^ (σ : ℂ)‖ :=
          norm_tsum_le_tsum_norm hsummNorm
      _ = ∑' n : ℕ, (((n + 1 : ℕ) : ℝ) ^ (-σ)) := tsum_congr hterm
  have hshift : ∑' n : ℕ, (((n + 1 : ℕ) : ℝ) ^ (-σ)) = ∑' n : ℕ, (n : ℝ) ^ (-σ) := by
    have h0 : ((0 : ℕ) : ℝ) ^ (-σ) = 0 := by
      simpa using Real.zero_rpow (ne_of_lt (by linarith : -σ < 0))
    have h := (Real.summable_nat_rpow.mpr hlt).tsum_eq_zero_add
    rw [h0, zero_add] at h
    exact h.symm
  calc ‖riemannZeta (σ : ℂ)‖ ≤ ∑' n : ℕ, (((n + 1 : ℕ) : ℝ) ^ (-σ)) := hnorm
    _ = ∑' n : ℕ, (n : ℝ) ^ (-σ) := hshift
    _ ≤ 1 + 1 / (σ - 1) := tsum_nat_rpow_neg_le_inv σ hσ

theorem riemannZeta_norm_le_inv_sub_one {σ : ℝ} (h1 : 1 < σ) (h2 : σ ≤ 2) :
    ‖riemannZeta (σ : ℂ)‖ ≤ 2 / (σ - 1) := by
  have hsub : 0 < σ - 1 := by linarith
  refine le_trans (riemannZeta_norm_le_one_add_inv_sub_one σ h1) ?_
  have hkey : 1 + 1 / (σ - 1) = σ / (σ - 1) := by
    field_simp
    ring
  rw [hkey]
  exact div_le_div_of_nonneg_right h2 (le_of_lt hsub)

end Commons.NumberTheory.LSeries