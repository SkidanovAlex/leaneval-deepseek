import Mathlib
import Submission.Commons.NumberTheory.LSeries.exists_bound_deriv_riemannZeta_log_sq
import Submission.Commons.NumberTheory.LSeries.exists_bound_norm_riemannZeta_fractional
import Submission.Commons.NumberTheory.LSeries.norm_riemannZeta_le_five_mul_log
import Submission.Commons.NumberTheory.LSeries.one_le_norm_riemannZeta_three_four_one
import Submission.Commons.NumberTheory.LSeries.riemannZeta_norm_le_inv_sub_one

set_option maxHeartbeats 800000

open Complex Metric

namespace Commons.NumberTheory.LSeries

/-- Mean-value inequality for `ζ` along a horizontal segment at height `γ ≠ 0`: if the
derivative of `ζ` is bounded by `C` on the segment from `β` to `σ`, then
`‖ζ(σ+iγ) - ζ(β+iγ)‖ ≤ C (σ-β)`. -/
lemma norm_riemannZeta_sub_le_of_deriv_bound (β σ γ C : ℝ) (hβσ : β ≤ σ) (hγ : γ ≠ 0)
    (hC : ∀ u ∈ Set.Icc β σ, ‖deriv riemannZeta ((u:ℂ) + (γ:ℂ)*I)‖ ≤ C) :
    ‖riemannZeta ((σ:ℂ) + (γ:ℂ)*I) - riemannZeta ((β:ℂ) + (γ:ℂ)*I)‖ ≤ C * (σ - β) := by
  have hne : ∀ u : ℝ, (u:ℂ) + (γ:ℂ)*I ≠ 1 := by
    intro u h
    have : ((u:ℂ) + (γ:ℂ)*I).im = 0 := by rw [h]; simp
    simp at this
    exact hγ this
  have hf' : ∀ x ∈ Set.Icc β σ,
      HasDerivWithinAt (fun u : ℝ => riemannZeta ((u:ℂ) + (γ:ℂ)*I))
        (deriv riemannZeta ((x:ℂ) + (γ:ℂ)*I)) (Set.Icc β σ) x := by
    intro x hx
    have h1 : HasDerivAt (fun u : ℝ => ((u:ℂ) + (γ:ℂ)*I)) 1 x := by
      have : HasDerivAt (fun u : ℝ => (u:ℂ)) 1 x := Complex.ofRealCLM.hasDerivAt
      simpa using this.add_const ((γ:ℂ)*I)
    have h2 : HasDerivAt riemannZeta (deriv riemannZeta ((x:ℂ) + (γ:ℂ)*I)) ((x:ℂ) + (γ:ℂ)*I) :=
      (differentiableAt_riemannZeta (hne x)).hasDerivAt
    simpa [Function.comp_def] using (h2.comp x h1).hasDerivWithinAt
  have hb : ∀ x ∈ Set.Ico β σ, ‖deriv riemannZeta ((x:ℂ) + (γ:ℂ)*I)‖ ≤ C := fun x hx =>
    hC x (Set.Ico_subset_Icc_self hx)
  have h := norm_image_sub_le_of_norm_deriv_le_segment' hf' hb σ ⟨hβσ, le_rfl⟩
  rw [mul_comm] at h
  simpa only [mul_comm (γ:ℂ) I] using h

/-- **Quantitative zero-free region for `ζ`** (de la Vallée Poussin, explicit form).

If `C ≥ 1` bounds `‖ζ'(σ+it)‖ ≤ C (log(|t|+2))²` on the strip
`|1 - σ| ≤ 1/(2 log(|t|+2))`, `|t| ≥ 2`, then `ζ(σ+it) ≠ 0` for `|t| ≥ 2` and
`σ ≥ 1 - (1/(20 C⁴)) / (log(|t|+2))⁹`. -/
theorem zero_free_region_riemannZeta (C : ℝ) (hC1 : 1 ≤ C)
    (hderiv : ∀ σ t : ℝ, 2 ≤ |t| →
      1 - 1 / (2 * Real.log (|t| + 2)) ≤ σ →
      σ ≤ 1 + 1 / (2 * Real.log (|t| + 2)) →
      ‖deriv riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I)‖
        ≤ C * (Real.log (|t| + 2)) ^ 2) :
    ∀ σ t : ℝ, 2 ≤ |t| →
      1 - (1 / (2560 * C ^ 4)) / (Real.log (|t| + 2)) ^ 9 ≤ σ →
      riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I) ≠ 0 := by
  intro σ t ht hσ hz
  have htne : t ≠ 0 := by
    intro h
    rw [h] at ht
    simp at ht
    linarith
  set L : ℝ := Real.log (|t| + 2) with hLdef
  have hLpos : 0 < L := by
    rw [hLdef]; exact Real.log_pos (by linarith [abs_nonneg t])
  have hL1 : 1 ≤ L := by
    rw [hLdef, Real.le_log_iff_exp_le (by linarith [abs_nonneg t] :
      (0:ℝ) < |t| + 2)]
    exact le_trans (le_of_lt Real.exp_one_lt_d9) (by linarith [abs_nonneg t])
  have hL2 : Real.log 2 ≤ L := by
    rw [hLdef]; exact Real.log_le_log (by norm_num) (by linarith [abs_nonneg t])
  set D : ℝ := 80 * C ^ 4 with hDdef
  have hC4 : 1 ≤ C ^ 4 := one_le_pow₀ hC1
  have hD80 : 80 ≤ D := by rw [hDdef]; nlinarith
  have hDpos : 0 < D := by linarith
  have hL9pos : 0 < L ^ 9 := pow_pos hLpos 9
  set δ : ℝ := 1 / (16 * (D * L ^ 9)) with hδdef
  have hδpos : 0 < δ := by rw [hδdef]; positivity
  have hL8 : 1 ≤ L ^ 8 := one_le_pow₀ hL1
  have hLL9 : L ≤ L ^ 9 := by
    have : L ^ 9 = L ^ 8 * L := by ring
    nlinarith [hLpos, hL8, this]
  have hδle : δ ≤ 1 / (2 * L) := by
    rw [hδdef]
    rw [div_le_iff₀ (by positivity), div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
    have h1 : 2 * L ≤ D * L ^ 9 := by
      have hb : 2 * L ≤ D * L := by
        have h2 : (2:ℝ) ≤ D := by linarith
        exact mul_le_mul_of_nonneg_right h2 (le_of_lt hLpos)
      have hc : D * L ≤ D * L ^ 9 := mul_le_mul_of_nonneg_left hLL9 (le_of_lt hDpos)
      linarith
    linarith
  set σ₁ : ℝ := 1 + δ with hσ₁def
  have hσ₁1 : 1 < σ₁ := by rw [hσ₁def]; linarith
  have hσ₁2 : σ₁ ≤ 1 + 1 / (2 * L) := by rw [hσ₁def]; linarith
  have hσ₁2' : σ₁ ≤ 2 := by
    have : 1 / (2 * L) ≤ 1 := by
      rw [div_le_one (by positivity)]; linarith
    linarith
  by_cases hσge1 : 1 ≤ σ
  · have hre : (1:ℝ) ≤ ((σ : ℂ) + (t : ℂ) * Complex.I).re := by
      simp [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
        Complex.I_re, Complex.I_im]
      linarith
    exact riemannZeta_ne_zero_of_one_le_re hre hz
  · push Not at hσge1
    have hσσ₁ : σ ≤ σ₁ := by linarith
    -- derivative bound on the segment
    have hderiv' : ∀ u ∈ Set.Icc σ σ₁, ‖deriv riemannZeta ((u:ℂ) + (t:ℂ)*I)‖ ≤ C * L ^ 2 := by
      intro u hu
      have hu1 : 1 - 1 / (2 * L) ≤ u := by
        have h2 : (1 / (2560 * C ^ 4)) / L ^ 9 ≤ 1 / (2 * L) := by
          rw [div_div]
          apply one_div_le_one_div_of_le (by positivity)
          have h1 : 2 ≤ 2560 * C ^ 4 * L ^ 8 := by nlinarith [hC4, hL8]
          have h2' : 2 * L ≤ (2560 * C ^ 4 * L ^ 8) * L :=
            mul_le_mul_of_nonneg_right h1 (le_of_lt hLpos)
          calc 2 * L ≤ (2560 * C ^ 4 * L ^ 8) * L := h2'
            _ = 2560 * C ^ 4 * L ^ 9 := by ring
        linarith [hu.1]
      have hu2 : u ≤ 1 + 1 / (2 * L) := le_trans hu.2 hσ₁2
      simpa [hLdef] using hderiv u t ht hu1 hu2
    -- mean value inequality ⇒ upper bound for ‖ζ(σ₁+it)‖
    have hmv : ‖riemannZeta ((σ₁:ℂ) + (t:ℂ)*I)‖ ≤ (C * L ^ 2) * (σ₁ - σ) := by
      have h := norm_riemannZeta_sub_le_of_deriv_bound σ σ₁ t (C * L ^ 2) hσσ₁ htne hderiv'
      rw [hz, sub_zero] at h
      simpa using h
    -- the 3-4-1 inequality and the upper bounds
    have h341 := one_le_norm_riemannZeta_three_four_one (σ := σ₁) (t := t) hσ₁1
    have hA : ‖riemannZeta (σ₁ : ℂ)‖ ≤ 2 / δ := by
      have h := riemannZeta_norm_le_inv_sub_one hσ₁1 hσ₁2'
      have : σ₁ - 1 = δ := by rw [hσ₁def]; ring
      rwa [this] at h
    have hB : ‖riemannZeta ((σ₁:ℂ) + 2*(t:ℂ)*I)‖ ≤ 10 * L := by
      have h2t : (1:ℝ) ≤ |2*t| := by rw [abs_mul]; norm_num; linarith
      have h := norm_riemannZeta_le_five_mul_log (σ := σ₁) (t := 2*t) (le_of_lt hσ₁1) h2t
      have hlog : Real.log (|2*t| + 2) ≤ 2 * L := by
        have h1 : |2*t| + 2 ≤ 2 * (|t| + 2) := by
          rw [abs_mul]; norm_num
          nlinarith [abs_nonneg t]
        calc Real.log (|2*t| + 2) ≤ Real.log (2 * (|t| + 2)) :=
              Real.log_le_log (by positivity) h1
          _ = Real.log 2 + Real.log (|t| + 2) := Real.log_mul (by norm_num) (by linarith [abs_nonneg t])
          _ ≤ L + L := by rw [← hLdef]; linarith
          _ = 2 * L := by ring
      calc ‖riemannZeta ((σ₁:ℂ) + 2*(t:ℂ)*I)‖
            = ‖riemannZeta ((σ₁:ℂ) + ((2*t:ℝ):ℂ)*I)‖ := by congr 1; push_cast; ring
        _ ≤ 5 * Real.log (|2*t| + 2) := h
        _ ≤ 5 * (2 * L) := by linarith
        _ = 10 * L := by ring
    -- lower bound ‖ζ(σ₁+it)‖⁴ ≥ δ³/(80 L)
    have hB4 : δ ^ 3 / (80 * L) ≤ ‖riemannZeta ((σ₁:ℂ) + (t:ℂ)*I)‖ ^ 4 := by
      have hA3 : ‖riemannZeta (σ₁:ℂ)‖ ^ 3 ≤ (2 / δ) ^ 3 :=
        pow_le_pow_left₀ (norm_nonneg _) hA 3
      have hprod : ‖riemannZeta (σ₁:ℂ)‖ ^ 3 * ‖riemannZeta ((σ₁:ℂ) + (t:ℂ)*I)‖ ^ 4
          * ‖riemannZeta ((σ₁:ℂ) + 2*(t:ℂ)*I)‖
          ≤ (2 / δ) ^ 3 * ‖riemannZeta ((σ₁:ℂ) + (t:ℂ)*I)‖ ^ 4 * (10 * L) := by
        apply mul_le_mul
        · exact mul_le_mul hA3 le_rfl (pow_nonneg (norm_nonneg _) 4)
            (by positivity)
        · exact hB
        · positivity
        · positivity
      have h1 : (1:ℝ) ≤ (2 / δ) ^ 3 * ‖riemannZeta ((σ₁:ℂ) + (t:ℂ)*I)‖ ^ 4 * (10 * L) :=
        le_trans h341 hprod
      have h2 : (2 / δ) ^ 3 * ‖riemannZeta ((σ₁:ℂ) + (t:ℂ)*I)‖ ^ 4 * (10 * L)
          = 80 * L * ‖riemannZeta ((σ₁:ℂ) + (t:ℂ)*I)‖ ^ 4 / δ ^ 3 := by
        field_simp
        ring
      rw [h2] at h1
      rw [le_div_iff₀ (by positivity)] at h1
      rw [div_le_iff₀ (by positivity), mul_comm]
      nlinarith [h1, hδpos]
    -- combine with the mean-value bound
    have hσ₁σ4 : δ ^ 3 / (D * L ^ 9) ≤ (σ₁ - σ) ^ 4 := by
      have hB4' : ‖riemannZeta ((σ₁:ℂ) + (t:ℂ)*I)‖ ^ 4 ≤ (C * L ^ 2) ^ 4 * (σ₁ - σ) ^ 4 := by
        calc ‖riemannZeta ((σ₁:ℂ) + (t:ℂ)*I)‖ ^ 4 ≤ ((C * L ^ 2) * (σ₁ - σ)) ^ 4 :=
              pow_le_pow_left₀ (norm_nonneg _) hmv 4
          _ = (C * L ^ 2) ^ 4 * (σ₁ - σ) ^ 4 := by ring
      have hpow : (C * L ^ 2) ^ 4 = C ^ 4 * L ^ 8 := by ring
      rw [hpow] at hB4'
      have h1 : δ ^ 3 / (80 * L) ≤ C ^ 4 * L ^ 8 * (σ₁ - σ) ^ 4 := le_trans hB4 hB4'
      rw [div_le_iff₀ (by positivity)] at h1
      rw [div_le_iff₀ (by positivity)]
      have hD : D * L ^ 9 = 80 * (C ^ 4 * L ^ 8) * L := by
        rw [hDdef]; ring
      rw [hD]
      nlinarith [h1, hLpos]
    -- hence σ₁ - σ ≥ 8/(D L⁹)
    have hkey : (1/8:ℝ) ^ 4 ≤ ((σ₁ - σ) * (D * L ^ 9)) ^ 4 := by
      have hDL : 0 < D * L ^ 9 := by positivity
      have hδ3 : δ ^ 3 = 4096⁻¹ / (D * L ^ 9) ^ 3 := by
        rw [hδdef]
        field_simp
        ring
      rw [hδ3, div_div] at hσ₁σ4
      rw [← pow_succ] at hσ₁σ4
      have := (div_le_iff₀ (by positivity : (0:ℝ) < (D * L ^ 9) ^ 4)).mp hσ₁σ4
      rw [mul_pow] at this
      norm_num at this ⊢
      linarith [this]
    have hx8 : 1/8 ≤ (σ₁ - σ) * (D * L ^ 9) := by
      have hx0 : 0 ≤ (σ₁ - σ) * (D * L ^ 9) := by
        apply mul_nonneg _ (by positivity)
        linarith
      have := (pow_le_pow_iff_left₀ (by norm_num : (0:ℝ) ≤ 1/8) hx0 (n := 4) (by norm_num)).mp hkey
      simpa using this
    have hsub : 1 / (8 * (D * L ^ 9)) ≤ σ₁ - σ := by
      rw [div_le_iff₀ (by positivity)]
      linarith [hx8]
    -- conclusion
    have hfinal : σ ≤ 1 - (1 / (1280 * C ^ 4)) / L ^ 9 := by
      have hD' : D = 80 * C ^ 4 := hDdef
      have : σ = (1 + 1 / (16 * (D * L ^ 9))) - (σ₁ - σ) := by rw [hσ₁def, hδdef]; ring
      rw [this]
      have heq : 1 / (16 * (D * L ^ 9)) - 1 / (8 * (D * L ^ 9))
          = - ((1 / (1280 * C ^ 4)) / L ^ 9) := by
        rw [hD']
        field_simp
        ring
      linarith [hsub, heq]
    have hstrict : 1 - (1 / (1280 * C ^ 4)) / L ^ 9 < 1 - (1 / (2560 * C ^ 4)) / L ^ 9 := by
      have hlt : 1 / (2560 * C ^ 4) < 1 / (1280 * C ^ 4) :=
        one_div_lt_one_div_of_lt (by positivity) (by nlinarith [hC4])
      have := div_lt_div_of_pos_right hlt (by positivity : (0:ℝ) < L ^ 9)
      linarith
    linarith [hσ, hfinal, hstrict]

/-- **Unconditional quantitative zero-free region for `ζ`**: there is `c > 0` such that
`ζ(σ + i t) ≠ 0` whenever `|t| ≥ 2` and `σ ≥ 1 - c/(log(|t|+2))⁹`. -/
theorem exists_zero_free_region_riemannZeta_log_pow :
    ∃ c : ℝ, 0 < c ∧ ∀ σ t : ℝ, 2 ≤ |t| →
      1 - c / (Real.log (|t| + 2)) ^ 9 ≤ σ →
      riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I) ≠ 0 := by
  obtain ⟨C, hCpos, hC⟩ := exists_bound_deriv_riemannZeta_log_sq
  set C' : ℝ := max C 1 with hC'def
  have hC'1 : 1 ≤ C' := le_max_right _ _
  have hC'pos : 0 < C' := lt_of_lt_of_le zero_lt_one hC'1
  refine ⟨1 / (2560 * C' ^ 4), by positivity, ?_⟩
  intro σ t ht hσ
  apply zero_free_region_riemannZeta C' hC'1 _ σ t ht
  · rw [hC'def]; exact hσ
  · intro a b hb h1 h2
    have := hC a b hb h1 h2
    have hCL : C * Real.log (|b| + 2) ^ 2 ≤ C' * Real.log (|b| + 2) ^ 2 :=
      mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
    exact le_trans this hCL

end Commons.NumberTheory.LSeries
