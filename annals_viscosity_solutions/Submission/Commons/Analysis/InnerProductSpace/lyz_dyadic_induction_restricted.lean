import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Normed.Order.Lattice

namespace Commons.Analysis.InnerProductSpace

open scoped BigOperators

set_option maxHeartbeats 4000000

/-- If `u`, `v` are unit vectors and a point of the ray `ℝ≥0 • v` is within `δ` of `r • u`,
where `δ ≤ 3/4 * r`, then the directions `u` and `v` differ by at most `(7/6) * (δ / r)`. -/
private lemma unit_sub_le_aux {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    {u v : F} (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) {r s δ : ℝ} (hr : 0 < r) (hs : 0 ≤ s)
    (hδ : 0 ≤ δ) (hz : δ ≤ 3 / 4 * r) (h : ‖r • u - s • v‖ ≤ δ) :
    ‖u - v‖ ≤ (7 / 6) * (δ / r) := by
  set c : ℝ := inner ℝ u v with hc
  have hnormu : ‖u‖ ^ 2 = 1 := by rw [hu]; norm_num
  have hnormv : ‖v‖ ^ 2 = 1 := by rw [hv]; norm_num
  have h1 : ‖r • u‖ ^ 2 = r ^ 2 := by
    rw [norm_smul, hu, mul_one, Real.norm_eq_abs, sq_abs]
  have h2 : ‖s • v‖ ^ 2 = s ^ 2 := by
    rw [norm_smul, hv, mul_one, Real.norm_eq_abs, sq_abs]
  have hexp : ‖r • u - s • v‖ ^ 2 = r ^ 2 - 2 * r * s * c + s ^ 2 := by
    rw [norm_sub_sq_real, h1, h2, real_inner_smul_left, real_inner_smul_right]
    ring
  have hexp_bound : r ^ 2 - 2 * r * s * c + s ^ 2 ≤ δ ^ 2 := by
    rw [← hexp]; exact pow_le_pow_left₀ (norm_nonneg _) h 2
  have hδr : δ < r := by nlinarith [hz, hr]
  have hc_nonneg : 0 ≤ c := by
    by_contra hneg
    push Not at hneg
    have hcneg' : 0 ≤ -c := by linarith
    have hprod : 0 ≤ 2 * r * s * (-c) :=
      mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hr.le) hs) hcneg'
    have hquad : r ^ 2 ≤ r ^ 2 - 2 * r * s * c + s ^ 2 := by nlinarith [hprod, sq_nonneg s]
    have hδ2 : δ ^ 2 < r ^ 2 := by nlinarith [hδr, hδ, hr]
    nlinarith [hquad, hexp_bound, hδ2]
  have hquad2 : r ^ 2 * (1 - c ^ 2) ≤ δ ^ 2 := by
    nlinarith [sq_nonneg (r * c - s), hexp_bound]
  have hz0 : 0 ≤ δ / r := div_nonneg hδ hr.le
  have hz34 : δ / r ≤ 3 / 4 := by rw [div_le_iff₀ hr]; linarith
  have hc2 : 1 - c ^ 2 ≤ (δ / r) ^ 2 := by
    rw [div_pow, le_div_iff₀ (pow_pos hr 2)]; linarith [hquad2]
  have hc_ge : Real.sqrt (1 - (δ / r) ^ 2) ≤ c := by
    rw [Real.sqrt_le_iff]
    refine ⟨hc_nonneg, ?_⟩
    linarith [hc2]
  have hz2le : (δ / r) ^ 2 ≤ 9 / 16 := by nlinarith [hz34, hz0]
  have h7 : Real.sqrt (7 / 16) ≤ Real.sqrt (1 - (δ / r) ^ 2) := by
    apply Real.sqrt_le_sqrt; linarith [hz2le]
  have h7v : (1 : ℝ) / 2 < Real.sqrt (7 / 16) := by
    rw [Real.lt_sqrt (by norm_num : (0:ℝ) ≤ 1/2)]
    norm_num
  have hc_half : 1 / 2 < c := lt_of_lt_of_le (lt_of_lt_of_le h7v h7) hc_ge
  have hBsq : ‖u - v‖ ^ 2 = 2 - 2 * c := by
    rw [norm_sub_sq_real, hnormu, hnormv, hc]; ring
  have hBle1 : ‖u - v‖ ^ 2 ≤ 1 := by rw [hBsq]; linarith
  have hBnn : 0 ≤ ‖u - v‖ ^ 2 := sq_nonneg _
  have h4eq : ‖u - v‖ ^ 4 = (‖u - v‖ ^ 2) ^ 2 := by ring
  have hkey : ‖u - v‖ ^ 2 - ‖u - v‖ ^ 4 / 4 = 1 - c ^ 2 := by
    rw [h4eq, hBsq]; ring
  have h4 : ‖u - v‖ ^ 4 / 4 ≤ ‖u - v‖ ^ 2 / 4 := by nlinarith [hBle1, hBnn]
  have hmain : (3 / 4) * ‖u - v‖ ^ 2 ≤ (δ / r) ^ 2 := by nlinarith [hkey, hc2, h4]
  have hBsq2 : ‖u - v‖ ^ 2 ≤ 4 / 3 * (δ / r) ^ 2 := by linarith
  have hBsq3 : ‖u - v‖ ^ 2 ≤ (Real.sqrt (4 / 3) * (δ / r)) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 4/3)]
    exact hBsq2
  have hB_le : ‖u - v‖ ≤ Real.sqrt (4 / 3) * (δ / r) := by
    have := Real.sqrt_le_sqrt hBsq3
    rwa [Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq (mul_nonneg (Real.sqrt_nonneg _) hz0)] at this
  have h73 : Real.sqrt (4 / 3) ≤ 7 / 6 := by
    rw [Real.sqrt_le_iff]
    exact ⟨by norm_num, by norm_num⟩
  calc ‖u - v‖ ≤ Real.sqrt (4 / 3) * (δ / r) := hB_le
    _ ≤ (7 / 6) * (δ / r) := mul_le_mul_of_nonneg_right h73 hz0

/-- `√(a * X) = a * √(X / a)` for `a > 0`, `X ≥ 0`. -/
private lemma sqrt_mul_eq_mul_sqrt_div (a X : ℝ) (ha : 0 < a) (hX : 0 ≤ X) :
    Real.sqrt (a * X) = a * Real.sqrt (X / a) := by
  have h1 : 0 ≤ a * Real.sqrt (X / a) := mul_nonneg ha.le (Real.sqrt_nonneg _)
  rw [show a * X = (a * Real.sqrt (X / a)) ^ 2 by
    rw [mul_pow, Real.sq_sqrt (div_nonneg hX ha.le)]
    field_simp]
  exact Real.sqrt_sq h1

/-- The dyadic induction of Liu--Yan--Zhou. -/
theorem lyz_dyadic_induction_restricted {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] {Γ : ℝ → F} {len : ℝ → ℝ → ℝ} {xS aF : F} {Ψ Ψb : ℝ → ℝ} {σ : ℕ → ℝ} {n₀ n : ℕ} {τ : ℝ} (hΨnn : ∀ T, 0 ≤ T → 0 ≤ Ψ T) (hΨmono : ∀ T T', 0 ≤ T → T ≤ T' → Ψ T ≤ Ψ T') (hΨbnn : ∀ t, 0 ≤ Ψb t) (hrel : ∀ t, 0 < t → Real.sqrt (Ψ t / t) ≤ Ψb t) (hslow : ∀ s t, 0 < s → s ≤ t → t ≤ 2 * s → Ψb t ≤ 2 * Ψb s) (hsumm : Summable fun k : ℕ => Real.sqrt (Ψ ((2:ℝ) ^ k) / (2:ℝ) ^ k)) (htail : ∀ i : ℕ, (∑' k : ℕ, Real.sqrt (Ψ ((2:ℝ) ^ (i + k)) / (2:ℝ) ^ (i + k))) ≤ Ψb ((2:ℝ) ^ i)) (hn : n₀ ≤ n) (hτ : 0 ≤ τ) (hσn : σ n = τ) (hΓτ : Γ τ = xS + (2:ℝ) ^ n • aF) (hσmem : ∀ i, n₀ ≤ i → i ≤ n → σ i ∈ Set.Icc 0 τ) (hσval : ∀ i, n₀ ≤ i → i ≤ n → ‖Γ (σ i) - xS‖ = (2:ℝ) ^ i) (hσle : ∀ i, n₀ ≤ i → i ≤ n → ∀ t ∈ Set.Icc (σ i) τ, (2:ℝ) ^ i ≤ ‖Γ t - xS‖) (hσmono : ∀ i, n₀ ≤ i → i < n → σ i ≤ σ (i + 1)) (hlen_add : ∀ a b c, 0 ≤ a → a ≤ b → b ≤ c → c ≤ τ → len a c = len a b + len b c) (hlen_chord : ∀ a b, 0 ≤ a → a ≤ b → b ≤ τ → ‖Γ b - Γ a‖ ≤ len a b) (hlen_bound : ∀ t ∈ Set.Icc (σ n₀) τ, len 0 t ≤ ‖Γ t - xS‖ + Ψ (‖Γ t - xS‖)) (hmid : ∀ i, n₀ ≤ i → i < n → ‖Γ (σ i) - (xS + ((1:ℝ) / 2) • (Γ (σ (i + 1)) - xS))‖ ≤ 4 * Real.sqrt ((2:ℝ) ^ (i + 1) * Ψ ((2:ℝ) ^ (i + 1)))) (hray : ∀ i, n₀ ≤ i → i < n → ∀ t ∈ Set.Icc (σ i) (σ (i + 1)), ∃ c : ℝ, 0 ≤ c ∧ ‖Γ t - (xS + c • (Γ (σ (i + 1)) - xS))‖ ≤ 6 * Real.sqrt ((2:ℝ) ^ (i + 1) * Ψ ((2:ℝ) ^ (i + 1)))) : (∀ t ∈ Set.Icc (σ n₀) τ, len 0 t ≤ ‖Γ t - xS‖ * (1 + Ψb (‖Γ t - xS‖) ^ 2)) ∧ (∀ t ∈ Set.Icc (σ n₀) τ, ‖(‖Γ t - xS‖)⁻¹ • (Γ t - xS) - aF‖ ≤ 64 * Ψb (‖Γ t - xS‖))  := by
  have hΓτ_sub : Γ τ - xS = (2:ℝ)^n • aF := by rw [hΓτ]; abel
  have hτ_val : ‖Γ τ - xS‖ = (2:ℝ)^n := by rw [← hσn]; exact hσval n hn le_rfl
  have haF_norm : ‖aF‖ = 1 := by
    have h2 : ‖(2:ℝ)^n • aF‖ = (2:ℝ)^n := by rw [← hΓτ_sub, hτ_val]
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)] at h2
    exact mul_left_cancel₀ (by positivity : ((2:ℝ)^n) ≠ 0) (by rw [mul_one]; exact h2)
  constructor
  · intro t ht
    have ht0 : 0 ≤ t := le_trans (hσmem n₀ le_rfl hn).1 ht.1
    have hrt_ge : (2:ℝ)^n₀ ≤ ‖Γ t - xS‖ := hσle n₀ le_rfl hn t ⟨ht.1, ht.2⟩
    have hrt_pos : 0 < ‖Γ t - xS‖ := lt_of_lt_of_le (by positivity) hrt_ge
    have hlenb := hlen_bound t ht
    have hrelt := hrel (‖Γ t - xS‖) hrt_pos
    have hPsi_nn : 0 ≤ Ψ (‖Γ t - xS‖) := hΨnn _ hrt_pos.le
    have hsq : Ψ (‖Γ t - xS‖) / ‖Γ t - xS‖ ≤ Ψb (‖Γ t - xS‖) ^ 2 := by
      have h1 := pow_le_pow_left₀ (Real.sqrt_nonneg _) hrelt 2
      rwa [Real.sq_sqrt (div_nonneg hPsi_nn hrt_pos.le)] at h1
    have hPsi_le : Ψ (‖Γ t - xS‖) ≤ ‖Γ t - xS‖ * Ψb (‖Γ t - xS‖) ^ 2 := by
      have h2 := mul_le_mul_of_nonneg_right hsq hrt_pos.le
      rw [div_mul_cancel₀ _ hrt_pos.ne'] at h2
      simpa [mul_comm] using h2
    have hgoal : ‖Γ t - xS‖ * (1 + Ψb (‖Γ t - xS‖) ^ 2)
        = ‖Γ t - xS‖ + ‖Γ t - xS‖ * Ψb (‖Γ t - xS‖) ^ 2 := by ring
    rw [hgoal]; linarith
  · intro t ht
    by_cases htτ : t = τ
    · have hrt : ‖Γ t - xS‖ = (2:ℝ)^n := by rw [htτ, ← hσn]; exact hσval n hn le_rfl
      have hsub : Γ t - xS = (2:ℝ)^n • aF := by rw [htτ]; exact hΓτ_sub
      have hone : (‖Γ t - xS‖)⁻¹ • (Γ t - xS) = aF := by
        rw [hrt, hsub, smul_smul, inv_mul_cancel₀ (by positivity), one_smul]
      rw [hone, sub_self, norm_zero]
      exact mul_nonneg (by norm_num) (hΨbnn _)
    · have ht_lt : t < τ := lt_of_le_of_ne ht.2 htτ
      let S : Finset ℕ := (Finset.Icc n₀ n).filter (fun k => σ k ≤ t)
      have hn₀S : n₀ ∈ S := by
        simp only [S, Finset.mem_filter, Finset.mem_Icc]
        exact ⟨⟨le_rfl, hn⟩, ht.1⟩
      have hSne : S.Nonempty := ⟨n₀, hn₀S⟩
      set i : ℕ := S.max' hSne with hi_def
      have hiS : i ∈ S := by rw [hi_def]; exact Finset.max'_mem S hSne
      have hi_data := Finset.mem_filter.mp hiS
      have hi_n₀ : n₀ ≤ i := (Finset.mem_Icc.mp hi_data.1).1
      have hi_n : i ≤ n := (Finset.mem_Icc.mp hi_data.1).2
      have hσi : σ i ≤ t := hi_data.2
      have hi_lt_n : i < n := by
        rcases lt_or_eq_of_le hi_n with h | h
        · exact h
        · exfalso
          rw [h] at hσi
          rw [hσn] at hσi
          exact absurd hσi (not_le.mpr ht_lt)
      have hi1 : t < σ (i+1) := by
        by_contra hcon
        rw [not_lt] at hcon
        have hmem : i + 1 ∈ S := by
          simp only [S, Finset.mem_filter, Finset.mem_Icc]
          exact ⟨⟨by omega, by omega⟩, hcon⟩
        have := Finset.le_max' S (i+1) hmem
        rw [← hi_def] at this
        omega
      have ht0 : 0 ≤ t := le_trans (hσmem n₀ le_rfl hn).1 ht.1
      have hσi1_mem : σ (i+1) ∈ Set.Icc 0 τ := hσmem (i+1) (by omega) (by omega)
      have hσi1_val : ‖Γ (σ (i+1)) - xS‖ = (2:ℝ)^(i+1) := hσval (i+1) (by omega) (by omega)
      set r : ℝ := ‖Γ t - xS‖ with hr_def
      have hr_ge_i : (2:ℝ)^i ≤ r := by
        rw [hr_def]; exact hσle i hi_n₀ (le_of_lt hi_lt_n) t ⟨hσi, ht.2⟩
      have hr_pos : 0 < r := lt_of_lt_of_le (by positivity) hr_ge_i
      set u : F := r⁻¹ • (Γ t - xS) with hu_def
      have hu_norm : ‖u‖ = 1 := by
        rw [hu_def, norm_smul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr hr_pos.le),
          ← hr_def, inv_mul_cancel₀ hr_pos.ne']
      set v : F := ((2:ℝ)^(i+1))⁻¹ • (Γ (σ (i+1)) - xS) with hv_def
      have hv_norm : ‖v‖ = 1 := by
        rw [hv_def, norm_smul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (by positivity)),
          hσi1_val, inv_mul_cancel₀ (by positivity)]
      obtain ⟨c, hc_nn, hc_bound⟩ := hray i hi_n₀ hi_lt_n t ⟨hσi, le_of_lt hi1⟩
      set s : ℝ := c * (2:ℝ)^(i+1) with hs_def
      set δ : ℝ := 6 * Real.sqrt ((2:ℝ)^(i+1) * Ψ ((2:ℝ)^(i+1))) with hδ_def
      have hs_nn : 0 ≤ s := by rw [hs_def]; positivity
      have hδ_nn : 0 ≤ δ := by rw [hδ_def]; positivity
      have hru : r • u = Γ t - xS := by
        rw [hu_def, smul_smul, mul_inv_cancel₀ hr_pos.ne', one_smul]
      have hsv : s • v = c • (Γ (σ (i+1)) - xS) := by
        rw [hv_def, smul_smul]
        congr 1
        rw [hs_def, mul_assoc, mul_inv_cancel₀ (by positivity), mul_one]
      have hray_bound : ‖r • u - s • v‖ ≤ δ := by
        rw [hru, hsv, hδ_def]
        rw [show Γ t - xS - c • (Γ (σ (i+1)) - xS)
            = Γ t - (xS + c • (Γ (σ (i+1)) - xS)) by abel]
        exact hc_bound
      let g : ℕ → ℝ := fun k => Real.sqrt (Ψ ((2:ℝ)^k) / (2:ℝ)^k)
      have hg_nn : ∀ k, 0 ≤ g k := fun k => Real.sqrt_nonneg _
      have hg_sum : Summable g := by simpa only [g] using hsumm
      have htail' : ∀ j : ℕ, (∑' k : ℕ, g (j + k)) ≤ Ψb ((2:ℝ)^j) := by
        intro j; simpa only [g] using htail j
      let Et : ℕ → F := fun j => ((2:ℝ)^j)⁻¹ • (Γ (σ j) - xS)
      have hEt_smul : ∀ j, ((2:ℝ)^j) • Et j = Γ (σ j) - xS := by
        intro j; simp only [Et]; rw [smul_smul, mul_inv_cancel₀ (by positivity), one_smul]
      have hEt_sub_smul : ∀ j, ((2:ℝ)^j) • Et (j+1) = (1/2:ℝ) • (Γ (σ (j+1)) - xS) := by
        intro j; simp only [Et]; rw [smul_smul]
        congr 1
        rw [show ((2:ℝ)^j * ((2:ℝ)^(j+1))⁻¹) = 1/2 by rw [pow_succ]; field_simp]
      have hmid_step : ∀ j, n₀ ≤ j → j < n → ‖Et j - Et (j+1)‖ ≤ 8 * g (j+1) := by
        intro j hj₀ hjlt
        have hm := hmid j hj₀ hjlt
        have heq : ((2:ℝ)^j) • (Et j - Et (j+1))
            = Γ (σ j) - (xS + (1/2:ℝ) • (Γ (σ (j+1)) - xS)) := by
          rw [smul_sub, hEt_smul j, hEt_sub_smul j]; abel
        have hm' : ((2:ℝ)^j) * ‖Et j - Et (j+1)‖
            ≤ 4 * Real.sqrt ((2:ℝ)^(j+1) * Ψ ((2:ℝ)^(j+1))) := by
          rw [← heq] at hm
          rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)] at hm
          exact hm
        have hbd : ‖Et j - Et (j+1)‖
            ≤ (4 * Real.sqrt ((2:ℝ)^(j+1) * Ψ ((2:ℝ)^(j+1)))) / ((2:ℝ)^j) :=
          (le_div_iff₀ (by positivity : (0:ℝ) < (2:ℝ)^j)).mpr (by rw [mul_comm]; exact hm')
        calc ‖Et j - Et (j+1)‖
            ≤ (4 * Real.sqrt ((2:ℝ)^(j+1) * Ψ ((2:ℝ)^(j+1)))) / ((2:ℝ)^j) := hbd
          _ = 8 * g (j+1) := by
              rw [show g (j+1) = Real.sqrt (Ψ ((2:ℝ)^(j+1)) / (2:ℝ)^(j+1)) from rfl]
              rw [sqrt_mul_eq_mul_sqrt_div ((2:ℝ)^(j+1)) (Ψ ((2:ℝ)^(j+1)))
                    (by positivity) (hΨnn _ (by positivity))]
              have hA : (2:ℝ)^(j+1) = 2 * (2:ℝ)^j := by rw [pow_succ]; ring
              rw [hA]
              have hp2 : ((2:ℝ)^j) ≠ 0 := by positivity
              field_simp
              ring
      have htel : ∑ j ∈ Finset.Ico (i+1) n, (Et j - Et (j+1)) = Et (i+1) - Et n := by
        have h := Finset.sum_Ico_sub Et (show i+1 ≤ n by omega)
        have h2 : Et (i+1) - Et n = - ∑ j ∈ Finset.Ico (i+1) n, (Et (j+1) - Et j) := by
          rw [h]; abel
        rw [h2, ← Finset.sum_neg_distrib]
        apply Finset.sum_congr rfl
        intro j hj; abel
      have hchain : ‖Et (i+1) - Et n‖ ≤ 8 * (∑' k, g (i+2+k)) := by
        calc ‖Et (i+1) - Et n‖
            = ‖∑ j ∈ Finset.Ico (i+1) n, (Et j - Et (j+1))‖ := by rw [htel]
          _ ≤ ∑ j ∈ Finset.Ico (i+1) n, ‖Et j - Et (j+1)‖ := norm_sum_le _ _
          _ ≤ ∑ j ∈ Finset.Ico (i+1) n, 8 * g (j+1) := by
              apply Finset.sum_le_sum
              intro j hj
              obtain ⟨hj1, hj2⟩ := Finset.mem_Ico.mp hj
              exact hmid_step j (by omega) hj2
          _ = 8 * ∑ j ∈ Finset.Ico (i+1) n, g (j+1) := by rw [Finset.mul_sum]
          _ ≤ 8 * (∑' k, g (i+2+k)) := by
              apply mul_le_mul_of_nonneg_left _ (by norm_num)
              rw [Finset.sum_Ico_eq_sum_range]
              have hcong : ∑ k ∈ Finset.range (n - (i+1)), g ((i+1)+k+1)
                  = ∑ k ∈ Finset.range (n - (i+1)), g (i+2+k) := by
                apply Finset.sum_congr rfl
                intro k hk
                congr 1
                omega
              rw [hcong]
              exact Summable.sum_le_tsum _ (fun k _ => hg_nn _)
                (hg_sum.comp_injective (by intro a b hab; omega))
      have hv_final : ‖v - aF‖ ≤ 8 * (∑' k, g (i+2+k)) := by
        have h1 : Et (i+1) = v := by simp only [Et, hv_def]
        have h2 : Et n = aF := by
          simp only [Et]
          rw [hσn, hΓτ_sub, smul_smul, inv_mul_cancel₀ (by positivity), one_smul]
        rwa [h1, h2] at hchain
      have hp_rel : Real.sqrt (Ψ r / r) ≤ Ψb r := hrel r hr_pos
      have hp_div : Ψ r / r ≤ Ψb r ^ 2 := by
        have h1 := pow_le_pow_left₀ (Real.sqrt_nonneg _) hp_rel 2
        rwa [Real.sq_sqrt (div_nonneg (hΨnn r hr_pos.le) hr_pos.le)] at h1
      have hp_le : Ψ r ≤ r * Ψb r ^ 2 := by
        have h1 := mul_le_mul_of_nonneg_right hp_div hr_pos.le
        rw [div_mul_cancel₀ _ hr_pos.ne'] at h1
        simpa [mul_comm] using h1
      have hlen_t : len 0 t ≤ (2:ℝ)^(i+1) + Ψ ((2:ℝ)^(i+1)) := by
        have hmono' : len 0 t ≤ len 0 (σ (i+1)) := by
          have h := hlen_add 0 t (σ (i+1)) (le_refl 0) ht0 (le_of_lt hi1) hσi1_mem.2
          have hnn : 0 ≤ len t (σ (i+1)) :=
            le_trans (norm_nonneg _) (hlen_chord t (σ (i+1)) ht0 (le_of_lt hi1) hσi1_mem.2)
          linarith
        refine hmono'.trans ?_
        have h := hlen_bound (σ (i+1)) ⟨le_of_lt (lt_of_le_of_lt ht.1 hi1), hσi1_mem.2⟩
        rwa [hσi1_val] at h
      have hr0_bound : ‖Γ 0 - xS‖ ≤ (2:ℝ)^(n₀+1) + Ψ ((2:ℝ)^n₀) := by
        have hσn₀_mem : σ n₀ ∈ Set.Icc 0 τ := hσmem n₀ le_rfl hn
        have hchord : ‖Γ 0 - Γ (σ n₀)‖ ≤ len 0 (σ n₀) := by
          rw [norm_sub_rev]; exact hlen_chord 0 (σ n₀) (le_refl 0) hσn₀_mem.1 hσn₀_mem.2
        have hb : len 0 (σ n₀) ≤ (2:ℝ)^n₀ + Ψ ((2:ℝ)^n₀) := by
          have h := hlen_bound (σ n₀) ⟨le_rfl, hσn₀_mem.2⟩
          rwa [hσval n₀ le_rfl hn] at h
        have h1 : ‖Γ 0 - xS‖ ≤ ‖Γ 0 - Γ (σ n₀)‖ + ‖Γ (σ n₀) - xS‖ := by
          calc ‖Γ 0 - xS‖ = ‖(Γ 0 - Γ (σ n₀)) + (Γ (σ n₀) - xS)‖ := by rw [sub_add_sub_cancel]
            _ ≤ _ := norm_add_le _ _
        have h2 : ‖Γ (σ n₀) - xS‖ = (2:ℝ)^n₀ := hσval n₀ le_rfl hn
        rw [h2] at h1
        rw [show (2:ℝ)^(n₀+1) = 2 * (2:ℝ)^n₀ by rw [pow_succ]; ring]
        linarith
      have hr_bound : r ≤ (2:ℝ)^(i+2) + 2 * Ψ ((2:ℝ)^(i+1)) := by
        have ht_len : ‖Γ t - Γ 0‖ ≤ len 0 t := hlen_chord 0 t (le_refl 0) ht0 ht.2
        have h1 : r ≤ len 0 t + ‖Γ 0 - xS‖ := by
          rw [hr_def]
          calc ‖Γ t - xS‖ = ‖(Γ t - Γ 0) + (Γ 0 - xS)‖ := by rw [sub_add_sub_cancel]
            _ ≤ ‖Γ t - Γ 0‖ + ‖Γ 0 - xS‖ := norm_add_le _ _
            _ ≤ len 0 t + ‖Γ 0 - xS‖ := by linarith
        have hmonoΨ : Ψ ((2:ℝ)^n₀) ≤ Ψ ((2:ℝ)^(i+1)) :=
          hΨmono _ _ (by positivity) (pow_le_pow_right₀ (by norm_num) (by omega))
        have hpow : (2:ℝ)^(n₀+1) ≤ (2:ℝ)^(i+1) := pow_le_pow_right₀ (by norm_num) (by omega)
        have h2i2 : (2:ℝ)^(i+2) = 2 * (2:ℝ)^(i+1) := by rw [pow_succ]; ring
        linarith [h1, hlen_t, hr0_bound, hmonoΨ, hpow, h2i2]
      by_cases he : (1:ℝ)/32 ≤ Ψb r
      · have hdev : ‖u - aF‖ ≤ 2 := by
          have h := norm_sub_le u aF
          rw [hu_norm, haF_norm] at h
          linarith
        calc ‖u - aF‖ ≤ 2 := hdev
          _ ≤ 64 * Ψb r := by linarith
      · rw [not_le] at he
        have hPsi_le1024 : Ψ r ≤ r / 1024 := by
          have h0 : 0 ≤ Ψb r := hΨbnn r
          have hpb : Ψb r ^ 2 ≤ (1/32:ℝ)^2 := by nlinarith [he, h0]
          have h2 : r * Ψb r ^ 2 ≤ r * (1/32:ℝ)^2 := mul_le_mul_of_nonneg_left hpb hr_pos.le
          nlinarith [hp_le, h2]
        have h2i1 : (0:ℝ) < (2:ℝ)^(i+1) := by positivity
        have hmem2 : (2:ℝ)^(i+1) ≤ 2 * r := by
          rw [show (2:ℝ)^(i+1) = 2 * (2:ℝ)^i by rw [pow_succ]; ring]
          linarith [hr_ge_i]
        have hcases : δ ≤ 12 * (2:ℝ)^(i+1) * Ψb r ∧ (∑' k, g (i+2+k)) ≤ 4 * Ψb r := by
          have h2i2 : (2:ℝ)^(i+2) = 2 * (2:ℝ)^(i+1) := by rw [pow_succ]; ring
          have h2i3 : (2:ℝ)^(i+3) = 4 * (2:ℝ)^(i+1) := by
            rw [show i+3 = (i+1)+2 by omega, pow_add]; ring
          have hdeq : Real.sqrt ((2:ℝ)^(i+1) * Ψ ((2:ℝ)^(i+1))) = (2:ℝ)^(i+1) * g (i+1) := by
            rw [sqrt_mul_eq_mul_sqrt_div ((2:ℝ)^(i+1)) (Ψ ((2:ℝ)^(i+1))) h2i1 (hΨnn _ h2i1.le)]
          have hdelta_of : g (i+1) ≤ 2 * Ψb r → δ ≤ 12 * (2:ℝ)^(i+1) * Ψb r := by
            intro hterm
            rw [hδ_def, hdeq]
            have h6 : (0:ℝ) ≤ 6 * (2:ℝ)^(i+1) := by positivity
            have hmm := mul_le_mul_of_nonneg_left hterm h6
            calc 6 * ((2:ℝ)^(i+1) * g (i+1)) = (6 * (2:ℝ)^(i+1)) * g (i+1) := by ring
              _ ≤ (6 * (2:ℝ)^(i+1)) * (2 * Ψb r) := hmm
              _ = 12 * (2:ℝ)^(i+1) * Ψb r := by ring
          by_cases hC : r < (2:ℝ)^(i+1)
          · have hslow1 : Ψb ((2:ℝ)^(i+1)) ≤ 2 * Ψb r := hslow r _ hr_pos (le_of_lt hC) hmem2
            have hterm : g (i+1) ≤ 2 * Ψb r := by
              have h1 : g (i+1) ≤ Ψb ((2:ℝ)^(i+1)) := by
                rw [show g (i+1) = Real.sqrt (Ψ ((2:ℝ)^(i+1)) / (2:ℝ)^(i+1)) from rfl]
                exact hrel _ h2i1
              linarith
            have hslow2 : Ψb ((2:ℝ)^(i+2)) ≤ 2 * Ψb ((2:ℝ)^(i+1)) :=
              hslow _ _ h2i1 (by rw [h2i2]; linarith [h2i1]) (by rw [h2i2])
            refine ⟨hdelta_of hterm, ?_⟩
            calc (∑' k, g (i+2+k)) ≤ Ψb ((2:ℝ)^(i+2)) := htail' (i+2)
              _ ≤ 2 * Ψb ((2:ℝ)^(i+1)) := hslow2
              _ ≤ 2 * (2 * Ψb r) := by linarith
              _ = 4 * Ψb r := by ring
          · rw [not_lt] at hC
            by_cases hB : r < (2:ℝ)^(i+2)
            · have hterm : g (i+1) ≤ 2 * Ψb r := by
                have hstep1 : Real.sqrt (Ψ ((2:ℝ)^(i+1)) / (2:ℝ)^(i+1))
                    ≤ Real.sqrt (Ψ r / (2:ℝ)^(i+1)) :=
                  Real.sqrt_le_sqrt (div_le_div_of_nonneg_right (hΨmono _ _ (by positivity) hC) h2i1.le)
                have hsplit : Real.sqrt (Ψ r / (2:ℝ)^(i+1))
                    = Real.sqrt (Ψ r / r) * Real.sqrt (r / (2:ℝ)^(i+1)) := by
                  rw [← Real.sqrt_mul (div_nonneg (hΨnn r hr_pos.le) hr_pos.le)]
                  congr 1; field_simp
                have hrdiv : r / (2:ℝ)^(i+1) < 2 := by rw [div_lt_iff₀ h2i1, ← h2i2]; exact hB
                have hs2 : Real.sqrt (r / (2:ℝ)^(i+1)) ≤ 2 := by
                  rw [Real.sqrt_le_iff]
                  exact ⟨by norm_num, by nlinarith [hrdiv, (by positivity : (0:ℝ) < r / (2:ℝ)^(i+1))]⟩
                calc g (i+1) = Real.sqrt (Ψ ((2:ℝ)^(i+1)) / (2:ℝ)^(i+1)) := rfl
                  _ ≤ Real.sqrt (Ψ r / (2:ℝ)^(i+1)) := hstep1
                  _ = Real.sqrt (Ψ r / r) * Real.sqrt (r / (2:ℝ)^(i+1)) := hsplit
                  _ ≤ Ψb r * 2 := mul_le_mul (hrel r hr_pos) hs2 (Real.sqrt_nonneg _) (hΨbnn r)
                  _ = 2 * Ψb r := by ring
              have hslowB : Ψb ((2:ℝ)^(i+2)) ≤ 2 * Ψb r :=
                hslow r _ hr_pos (le_of_lt hB) (by rw [h2i2]; linarith)
              refine ⟨hdelta_of hterm, ?_⟩
              calc (∑' k, g (i+2+k)) ≤ Ψb ((2:ℝ)^(i+2)) := htail' (i+2)
                _ ≤ 2 * Ψb r := hslowB
                _ ≤ 4 * Ψb r := by linarith [hΨbnn r]
            · rw [not_lt] at hB
              have hΨmono1 : Ψ ((2:ℝ)^(i+1)) ≤ Ψ r :=
                hΨmono _ _ (by positivity) (by nlinarith [hB, h2i2, h2i1])
              have hrA : r ≤ (512/511) * (2:ℝ)^(i+2) := by
                nlinarith [hr_bound, hΨmono1, hPsi_le1024, h2i2, h2i1]
              have hterm : g (i+1) ≤ 2 * Ψb r := by
                have hstep1 : Real.sqrt (Ψ ((2:ℝ)^(i+1)) / (2:ℝ)^(i+1))
                    ≤ Real.sqrt (Ψ r / (2:ℝ)^(i+1)) :=
                  Real.sqrt_le_sqrt (div_le_div_of_nonneg_right hΨmono1 h2i1.le)
                have hsplit : Real.sqrt (Ψ r / (2:ℝ)^(i+1))
                    = Real.sqrt (Ψ r / r) * Real.sqrt (r / (2:ℝ)^(i+1)) := by
                  rw [← Real.sqrt_mul (div_nonneg (hΨnn r hr_pos.le) hr_pos.le)]
                  congr 1; field_simp
                have hrdiv4 : r / (2:ℝ)^(i+1) ≤ 4 := by
                  rw [div_le_iff₀ h2i1]; nlinarith [hrA, h2i2, h2i1]
                have hs2 : Real.sqrt (r / (2:ℝ)^(i+1)) ≤ 2 := by
                  rw [Real.sqrt_le_iff]
                  exact ⟨by norm_num, by nlinarith [hrdiv4, (by positivity : (0:ℝ) ≤ r / (2:ℝ)^(i+1))]⟩
                calc g (i+1) = Real.sqrt (Ψ ((2:ℝ)^(i+1)) / (2:ℝ)^(i+1)) := rfl
                  _ ≤ Real.sqrt (Ψ r / (2:ℝ)^(i+1)) := hstep1
                  _ = Real.sqrt (Ψ r / r) * Real.sqrt (r / (2:ℝ)^(i+1)) := hsplit
                  _ ≤ Ψb r * 2 := mul_le_mul (hrel r hr_pos) hs2 (Real.sqrt_nonneg _) (hΨbnn r)
                  _ = 2 * Ψb r := by ring
              have hslowA : Ψb ((2:ℝ)^(i+3)) ≤ 2 * Ψb r :=
                hslow r _ hr_pos (by nlinarith [hrA, h2i2, h2i1]) (by nlinarith [hB, h2i3, h2i1])
              have hgi2 : g (i+2) ≤ 2 * Ψb r := by
                have hmono2 : Ψ ((2:ℝ)^(i+2)) ≤ Ψ r := hΨmono _ _ (by positivity) hB
                have hstep1 : Real.sqrt (Ψ ((2:ℝ)^(i+2)) / r) ≤ Real.sqrt (Ψ r / r) :=
                  Real.sqrt_le_sqrt (div_le_div_of_nonneg_right hmono2 hr_pos.le)
                have hsplit : Real.sqrt (Ψ ((2:ℝ)^(i+2)) / (2:ℝ)^(i+2))
                    = Real.sqrt (Ψ ((2:ℝ)^(i+2)) / r) * Real.sqrt (r / (2:ℝ)^(i+2)) := by
                  rw [← Real.sqrt_mul (div_nonneg (hΨnn _ (by positivity)) hr_pos.le)]
                  congr 1; field_simp
                have hrdiv : r / (2:ℝ)^(i+2) ≤ 4 := by
                  rw [div_le_iff₀ (by positivity : (0:ℝ) < (2:ℝ)^(i+2))]
                  nlinarith [hrA]
                have hs2 : Real.sqrt (r / (2:ℝ)^(i+2)) ≤ 2 := by
                  rw [Real.sqrt_le_iff]
                  exact ⟨by norm_num, by nlinarith [hrdiv, (by positivity : (0:ℝ) ≤ r / (2:ℝ)^(i+2))]⟩
                calc g (i+2) = Real.sqrt (Ψ ((2:ℝ)^(i+2)) / (2:ℝ)^(i+2)) := rfl
                  _ = Real.sqrt (Ψ ((2:ℝ)^(i+2)) / r) * Real.sqrt (r / (2:ℝ)^(i+2)) := hsplit
                  _ ≤ Ψb r * 2 := by
                      refine mul_le_mul ?_ hs2 (Real.sqrt_nonneg _) (hΨbnn r)
                      exact hstep1.trans (hrel r hr_pos)
                  _ = 2 * Ψb r := by ring
              have hsplit2 : (∑' k, g (i+2+k)) = g (i+2) + (∑' k, g (i+3+k)) := by
                have hsum2 : Summable (fun k => g (i+2+k)) :=
                  hg_sum.comp_injective (by intro a b hab; omega)
                have h := hsum2.tsum_eq_zero_add
                simp only [add_zero] at h
                rw [h]
                congr 1
                apply tsum_congr
                intro k
                congr 1
                omega
              refine ⟨hdelta_of hterm, ?_⟩
              rw [hsplit2]
              have h3 := htail' (i+3)
              linarith [hgi2, hslowA, h3]
        obtain ⟨hδ_le, hsum_le⟩ := hcases
        have hδr : δ ≤ 3 / 4 * r := by
          have hcoef : 12 * (2:ℝ)^(i+1) ≤ 24 * r := by linarith [hmem2]
          have h1 : 12 * (2:ℝ)^(i+1) * Ψb r ≤ 24 * r * Ψb r := by
            nlinarith [hcoef, hΨbnn r]
          have h2 : 24 * r * Ψb r < 3 / 4 * r := by nlinarith [he, hr_pos]
          linarith
        have huv : ‖u - v‖ ≤ (7/6) * (δ/r) :=
          unit_sub_le_aux hu_norm hv_norm hr_pos hs_nn hδ_nn hδr hray_bound
        have hδr_le : δ / r ≤ 24 * Ψb r := by
          rw [div_le_iff₀ hr_pos]
          nlinarith [hδ_le, hmem2, hΨbnn r]
        have hud : ‖u - aF‖ ≤ ‖u - v‖ + ‖v - aF‖ := by
          have h : u - aF = (u - v) + (v - aF) := by abel
          rw [h]; exact norm_add_le _ _
        calc ‖u - aF‖ ≤ ‖u - v‖ + ‖v - aF‖ := hud
          _ ≤ (7/6) * (δ/r) + 8 * (∑' k, g (i+2+k)) := add_le_add huv hv_final
          _ ≤ (7/6) * (24 * Ψb r) + 8 * (4 * Ψb r) := by
              have h1 := mul_le_mul_of_nonneg_left hδr_le (by norm_num : (0:ℝ) ≤ 7/6)
              have h2 := mul_le_mul_of_nonneg_left hsum_le (by norm_num : (0:ℝ) ≤ 8)
              linarith
          _ ≤ 64 * Ψb r := by linarith [hΨbnn r]


end Commons.Analysis.InnerProductSpace