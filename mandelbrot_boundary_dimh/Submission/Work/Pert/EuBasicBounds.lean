import Mathlib
import Submission.Work.Pert.EuDefs
import Submission.Work.Pert.exp_inv_64_le
import Submission.Work.Pert.norm_psi_sub_one_le

namespace Work.Pert

open Complex

noncomputable section

set_option maxHeartbeats 1000000

/-- **Elementary bounds for the datum `(σ, α, u₀)` with a small exponent.**

With `s = euS α = 2πiα`, `t = euT α η = 2παη`, `ψ = euPsi α = (e^s - 1)/s`, assuming
`1 - σ u₀ = e^s`, `‖u₀ - 1‖ ≤ 1/1024` and `2π‖α‖ η ≤ 1/64` (so `‖s‖ ≤ 1/6400`), all the
elementary quantities attached to the two centres `±iη` are `1 + O(1/64)`:

* `‖s‖ η ≤ 1/64` and `‖t‖ ≤ 1/64`;
* `1 - 10⁻⁴ ≤ ‖ψ‖`, hence `ψ ≠ 0`;
* `‖u₀‖ ≤ 1025/1024`;
* `‖e^{±t}‖ ≤ 1.02`;
* `‖u₀ e^{±t}/ψ - 1‖ ≤ 171/10000`;
* `‖u₀ e^{±t}/(1 - e^s)‖ · ‖s‖ ≤ 1.03`.

These are the "numerical hygiene" estimates of Shishikura's §4.2 / Lemma A.1 used to bound the
deviation `E_u = τ₀ ∘ τ_f - id` (see `EuDevBounds`, `Eu_exists_center`). -/
theorem EuBasicBounds {σ α u₀ : ℂ} {η : ℝ}
    (hη : 0 < η) (hη100 : 100 ≤ η) (hσ : σ ≠ 0) (hα : α ≠ 0)
    (hu₀ : ‖u₀ - 1‖ ≤ 1 / 1024)
    (hαη : 2 * Real.pi * ‖α‖ * η ≤ 1 / 64)
    (heq : 1 - σ * u₀ = Complex.exp (euS α)) :
    ‖euS α‖ * η ≤ 1 / 64
    ∧ ‖euT α η‖ ≤ 1 / 64
    ∧ 9999 / 10000 ≤ ‖euPsi α‖
    ∧ ‖u₀‖ ≤ 1025 / 1024
    ∧ ‖Complex.exp (euT α η)‖ ≤ 102 / 100
    ∧ ‖u₀ * Complex.exp (euT α η) / euPsi α - 1‖ ≤ 171 / 10000
    ∧ ‖u₀ * Complex.exp (-(euT α η)) / euPsi α - 1‖ ≤ 171 / 10000
    ∧ ‖u₀ * Complex.exp (euT α η) / (1 - Complex.exp (euS α))‖ * ‖euS α‖ ≤ 103 / 100
    ∧ ‖u₀ * Complex.exp (-(euT α η)) / (1 - Complex.exp (euS α))‖ * ‖euS α‖ ≤ 103 / 100 := by
  -- ## the two exponents `s = euS α`, `t = euT α η`
  have hsnorm : ‖euS α‖ = 2 * Real.pi * ‖α‖ := norm_euS α
  have htnorm : ‖euT α η‖ = 2 * Real.pi * ‖α‖ * |η| := norm_euT α η
  have hηabs : |η| = η := abs_of_pos hη
  have hsnz : euS α ≠ 0 := euS_ne_zero hα
  have hsle : ‖euS α‖ ≤ 1 / 6400 := by
    rw [hsnorm]; nlinarith [hαη, hη100, Real.pi_pos]
  have hshalf : ‖euS α‖ ≤ 1 / 2 := by linarith
  have hs_eta : ‖euS α‖ * η ≤ 1 / 64 := by rw [hsnorm]; exact hαη
  have htle : ‖euT α η‖ ≤ 1 / 64 := by rw [htnorm, hηabs]; exact hαη
  -- ## the cube root of unity `u₀` is close to `1` and non-zero
  have hu0nz : u₀ ≠ 0 := by
    intro h; rw [h] at hu₀; norm_num at hu₀
  have hu0le : ‖u₀‖ ≤ 1025 / 1024 := by
    have h3 : (u₀ - 1) + 1 = u₀ := by ring
    have h2 : ‖(u₀ - 1) + 1‖ ≤ ‖u₀ - 1‖ + ‖(1 : ℂ)‖ := norm_add_le _ _
    rw [h3, norm_one] at h2
    linarith
  -- ## the normalisation `σ u₀ = 1 - e^s`
  have hσu0 : σ * u₀ = 1 - Complex.exp (euS α) := by linear_combination -heq
  have h1expnz : 1 - Complex.exp (euS α) ≠ 0 := by
    rw [← hσu0]; exact mul_ne_zero hσ hu0nz
  -- ## `ψ = (e^s - 1)/s` is within `10⁻⁴` of `1`
  have hψ1 : ‖euPsi α - 1‖ ≤ 29 / 48 * ‖euS α‖ := by
    have h := norm_psi_sub_one_le (x := euS α) hsnz hshalf
    simpa only [euPsi] using h
  have hψ1b : ‖euPsi α - 1‖ ≤ 1 / 10000 := by
    have h : (29 / 48 : ℝ) * ‖euS α‖ ≤ 1 / 10000 := by nlinarith [hsle]
    linarith
  have hψge : 9999 / 10000 ≤ ‖euPsi α‖ := by
    have h : (1 : ℂ) = euPsi α - (euPsi α - 1) := by ring
    have h2 : ‖(1 : ℂ)‖ ≤ ‖euPsi α - (euPsi α - 1)‖ := by rw [← h]
    rw [norm_one] at h2
    have h3 := norm_sub_le (euPsi α) (euPsi α - 1)
    linarith [hψ1b]
  have hψnz : euPsi α ≠ 0 := by
    intro h; rw [h, norm_zero] at hψge; norm_num at hψge
  have hψpos : 0 < ‖euPsi α‖ := norm_pos_iff.mpr hψnz
  have hψeq : euS α * euPsi α = Complex.exp (euS α) - 1 := by
    rw [euPsi]
    exact mul_div_cancel₀ (Complex.exp (euS α) - 1) hsnz
  -- ## `‖e^{±t}‖ ≤ 1.02`
  have hexpnorm : ∀ w : ℂ, ‖w‖ ≤ 1 / 64 → ‖Complex.exp w‖ ≤ 102 / 100 := by
    intro w hw
    rw [Complex.norm_exp]
    calc Real.exp w.re ≤ Real.exp ‖w‖ := Real.exp_le_exp.mpr (Complex.re_le_norm w)
      _ ≤ Real.exp (1 / 64) := Real.exp_le_exp.mpr hw
      _ ≤ 102 / 100 := by linarith [exp_inv_64_le]
  -- ## `‖u₀ e^{w}/ψ - 1‖ ≤ 171/10000` for `‖w‖ ≤ 1/64`
  have key : ∀ w : ℂ, ‖w‖ ≤ 1 / 64 →
      ‖u₀ * Complex.exp w / euPsi α - 1‖ ≤ 171 / 10000 := by
    intro w hw
    have hwexpnorm : ‖Complex.exp w‖ ≤ 51 / 50 := by
      rw [Complex.norm_exp]
      calc Real.exp w.re ≤ Real.exp ‖w‖ := Real.exp_le_exp.mpr (Complex.re_le_norm w)
        _ ≤ Real.exp (1 / 64) := Real.exp_le_exp.mpr hw
        _ ≤ 51 / 50 := by linarith [exp_inv_64_le]
    have hnum : ‖u₀ * Complex.exp w - euPsi α‖ ≤ 17 / 1000 := by
      have hsplit : u₀ * Complex.exp w - euPsi α
          = (u₀ - 1) * Complex.exp w + (Complex.exp w - 1) + (1 - euPsi α) := by ring
      rw [hsplit]
      have ha : ‖(u₀ - 1) * Complex.exp w‖ ≤ (1 / 1024) * (51 / 50) := by
        rw [norm_mul]
        exact mul_le_mul hu₀ hwexpnorm (norm_nonneg _) (by norm_num)
      have hb : ‖Complex.exp w - 1‖ ≤ ‖w‖ + ‖w‖ ^ 2 := by
        have ht := Complex.norm_exp_sub_one_sub_id_le (x := w) (by linarith : ‖w‖ ≤ 1)
        have he : Complex.exp w - 1 = (Complex.exp w - 1 - w) + w := by ring
        rw [he]
        calc ‖(Complex.exp w - 1 - w) + w‖ ≤ ‖Complex.exp w - 1 - w‖ + ‖w‖ :=
              norm_add_le _ _
          _ ≤ ‖w‖ ^ 2 + ‖w‖ := by linarith [ht]
          _ = ‖w‖ + ‖w‖ ^ 2 := by ring
      have hc : ‖1 - euPsi α‖ ≤ 1 / 10000 := by rw [norm_sub_rev]; exact hψ1b
      calc ‖(u₀ - 1) * Complex.exp w + (Complex.exp w - 1) + (1 - euPsi α)‖
          ≤ ‖(u₀ - 1) * Complex.exp w + (Complex.exp w - 1)‖ + ‖1 - euPsi α‖ :=
            norm_add_le _ _
        _ ≤ (‖(u₀ - 1) * Complex.exp w‖ + ‖Complex.exp w - 1‖) + ‖1 - euPsi α‖ := by
            gcongr
            exact norm_add_le _ _
        _ ≤ 17 / 1000 := by
            have hwnn : (0 : ℝ) ≤ ‖w‖ := norm_nonneg w
            nlinarith [ha, hb, hc, hw, hwnn]
    have hform : u₀ * Complex.exp w / euPsi α - 1
        = (u₀ * Complex.exp w - euPsi α) / euPsi α := by
      rw [div_sub_one (a := u₀ * Complex.exp w) hψnz]
    rw [hform, norm_div]
    calc ‖u₀ * Complex.exp w - euPsi α‖ / ‖euPsi α‖ ≤ (17 / 1000) / ‖euPsi α‖ :=
          div_le_div_of_nonneg_right hnum (norm_nonneg _)
      _ ≤ (17 / 1000) / (9999 / 10000) :=
          div_le_div_of_nonneg_left (by norm_num) (by norm_num) hψge
      _ ≤ 171 / 10000 := by norm_num
  -- ## `‖s‖/‖σ‖ = ‖u₀‖/‖ψ‖`
  have hnorm_eq : ‖euS α‖ * ‖euPsi α‖ = ‖σ‖ * ‖u₀‖ := by
    have h : euS α * euPsi α = -(σ * u₀) := by
      rw [hψeq, hσu0]; ring
    simp only [← norm_mul, h, norm_neg]
  have hratio : ‖euS α‖ / ‖σ‖ = ‖u₀‖ / ‖euPsi α‖ := by
    rw [div_eq_div_iff (norm_ne_zero_iff.mpr hσ) (norm_ne_zero_iff.mpr hψnz)]
    rw [mul_comm ‖u₀‖ ‖σ‖]
    exact hnorm_eq
  -- ## `u₀/(1 - e^s) = 1/σ`
  have hσun : u₀ / (1 - Complex.exp (euS α)) = 1 / σ := by
    rw [← hσu0]
    field_simp
  -- ## `‖u₀ e^{w}/(1 - e^s)‖ · ‖s‖ ≤ 103/100` for `w = ±t`
  have hbound89 : ∀ w : ℂ, w = euT α η ∨ w = -(euT α η) →
      ‖u₀ * Complex.exp w / (1 - Complex.exp (euS α))‖ * ‖euS α‖ ≤ 103 / 100 := by
    intro w hw
    have hwle : ‖w‖ ≤ 1 / 64 := by
      rcases hw with h | h
      · rw [h]; exact htle
      · rw [h, norm_neg]; exact htle
    have hwexp : ‖Complex.exp w‖ ≤ 102 / 100 := hexpnorm w hwle
    have hφ : u₀ * Complex.exp w / (1 - Complex.exp (euS α)) = Complex.exp w / σ := by
      rw [show u₀ * Complex.exp w / (1 - Complex.exp (euS α))
            = Complex.exp w * (u₀ / (1 - Complex.exp (euS α))) by ring]
      rw [hσun]
      ring
    rw [hφ, norm_div]
    have hstep : ‖Complex.exp w‖ / ‖σ‖ * ‖euS α‖ = ‖Complex.exp w‖ * (‖u₀‖ / ‖euPsi α‖) := by
      rw [← hratio]
      ring
    rw [hstep]
    have hratio_le : ‖u₀‖ / ‖euPsi α‖ ≤ (1025 / 1024) / (9999 / 10000) := by
      rw [div_le_iff₀ hψpos]
      have h1 : ((1025 : ℝ) / 1024) / (9999 / 10000) * (9999 / 10000) = 1025 / 1024 := by
        norm_num
      calc ‖u₀‖ ≤ 1025 / 1024 := hu0le
        _ = (1025 / 1024) / (9999 / 10000) * (9999 / 10000) := h1.symm
        _ ≤ (1025 / 1024) / (9999 / 10000) * ‖euPsi α‖ := by
            exact mul_le_mul_of_nonneg_left hψge (by norm_num)
    calc ‖Complex.exp w‖ * (‖u₀‖ / ‖euPsi α‖)
        ≤ (102 / 100) * ((1025 / 1024) / (9999 / 10000)) := by
          exact mul_le_mul hwexp hratio_le (by positivity) (by norm_num)
      _ ≤ 103 / 100 := by norm_num
  exact ⟨hs_eta, htle, hψge, hu0le, hexpnorm (euT α η) htle,
    key (euT α η) htle, key (-(euT α η)) (by rw [norm_neg]; exact htle),
    hbound89 (euT α η) (Or.inl rfl), hbound89 (-(euT α η)) (Or.inr rfl)⟩

end

end Work.Pert
