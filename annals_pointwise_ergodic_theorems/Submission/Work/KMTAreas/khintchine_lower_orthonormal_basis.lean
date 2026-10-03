import Mathlib
import Submission.Commons.Analysis.Walsh.exists_khintchine_hilbert

namespace Work.KMTAreas

open scoped InnerProductSpace

/-- Expanding the inner product of a signed sum of vectors against a fixed vector:
`⟪∑ᵢ εᵢ • bᵢ, x⟫ = ∑ᵢ εᵢ • ⟪bᵢ, x⟫` for signs `εᵢ = ±1`. -/
private lemma inner_sum_sign_smul {n : ℕ} {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H]
    (b : Fin n → H) (x : H) (ε : Fin n → Bool) :
    inner ℂ (∑ i, (if ε i then (1 : ℂ) else -1) • b i) x
      = ∑ i, (if ε i then (1 : ℂ) else -1) • inner ℂ (b i) x := by
  rw [sum_inner]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [inner_smul_left]
  by_cases h : ε i <;> simp [h]

/-- `enorm` commutes with a finite `p`-sum: `∑ᵢ ‖fᵢ‖ₑ ^ p = ofReal (∑ᵢ ‖fᵢ‖ ^ p)` for `p > 0`. -/
private lemma sum_enorm_rpow {ι : Type*} [Fintype ι] {E : Type*} [SeminormedAddCommGroup E]
    (f : ι → E) {p : ℝ} (hp : 0 < p) :
    (∑ i, ‖f i‖ₑ ^ p) = ENNReal.ofReal (∑ i, ‖f i‖ ^ p) := by
  have h : ∀ i, ‖f i‖ₑ ^ p = ENNReal.ofReal (‖f i‖ ^ p) := fun i => by
    rw [← ENNReal.ofReal_rpow_of_nonneg (norm_nonneg (f i)) hp.le, ← ofReal_norm]
  calc (∑ i, ‖f i‖ₑ ^ p) = ∑ i, ENNReal.ofReal (‖f i‖ ^ p) :=
        Finset.sum_congr rfl (fun i _ => h i)
    _ = ENNReal.ofReal (∑ i, ‖f i‖ ^ p) :=
        (ENNReal.ofReal_sum_of_nonneg (fun i _ => Real.rpow_nonneg (norm_nonneg (f i)) p)).symm

/-- Packaging of a real `ℓᵖ`-type lower bound into the corresponding `ℝ≥0∞` inequality:
if `c * A ≤ (S / 2ⁿ)^{1/p}` then `ofReal (A^p) ≤ (ofReal (c^p))⁻¹ * (ofReal (2ⁿ))⁻¹ * ofReal S`. -/
private lemma ofReal_rpow_le_inv_mul_inv_mul {p c A S : ℝ} {n : ℕ}
    (hc : 0 < c) (hp : 0 < p) (hA : 0 ≤ A) (hS : 0 ≤ S)
    (h : c * A ≤ (S / (2 : ℝ) ^ n) ^ (1 / p)) :
    ENNReal.ofReal (A ^ p) ≤
      (ENNReal.ofReal (c ^ p))⁻¹ * (ENNReal.ofReal ((2 : ℝ) ^ n))⁻¹ * ENNReal.ofReal S := by
  have hcp : 0 < c ^ p := Real.rpow_pos_of_pos hc p
  have h2n : 0 < (2 : ℝ) ^ n := pow_pos (by norm_num) n
  have hcA : 0 ≤ c * A := mul_nonneg hc.le hA
  have hSd : 0 ≤ S / (2 : ℝ) ^ n := div_nonneg hS h2n.le
  have h1 : (c * A) ^ p ≤ S / (2 : ℝ) ^ n := by
    have hlt := Real.rpow_le_rpow hcA h hp.le
    rw [one_div, Real.rpow_inv_rpow hSd (ne_of_gt hp)] at hlt
    exact hlt
  have h2 : c ^ p * A ^ p ≤ S / (2 : ℝ) ^ n := by
    rwa [Real.mul_rpow hc.le hA] at h1
  have h3 : A ^ p ≤ (c ^ p)⁻¹ * (S / (2 : ℝ) ^ n) := by
    calc A ^ p = (c ^ p)⁻¹ * (c ^ p * A ^ p) := by
            rw [← mul_assoc, inv_mul_cancel₀ (ne_of_gt hcp), one_mul]
      _ ≤ (c ^ p)⁻¹ * (S / (2 : ℝ) ^ n) :=
            mul_le_mul_of_nonneg_left h2 (inv_nonneg.mpr hcp.le)
  have h4 : A ^ p ≤ (c ^ p)⁻¹ * ((2 : ℝ) ^ n)⁻¹ * S := by
    rw [div_eq_mul_inv] at h3
    calc A ^ p ≤ (c ^ p)⁻¹ * (S * ((2 : ℝ) ^ n)⁻¹) := h3
      _ = (c ^ p)⁻¹ * ((2 : ℝ) ^ n)⁻¹ * S := by ring
  have hrhs : (ENNReal.ofReal (c ^ p))⁻¹ * (ENNReal.ofReal ((2 : ℝ) ^ n))⁻¹ * ENNReal.ofReal S
      = ENNReal.ofReal ((c ^ p)⁻¹ * ((2 : ℝ) ^ n)⁻¹ * S) := by
    rw [← ENNReal.ofReal_inv_of_pos hcp, ← ENNReal.ofReal_inv_of_pos h2n]
    rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
  rw [hrhs]
  exact ENNReal.ofReal_le_ofReal h4

/-- **Lower Khintchine inequality in an orthonormal basis.**

For every `p ≥ 1` there is `c > 0` such that for every finite-dimensional complex inner product
space `H` and every `x : H`, the average of `‖⟪∑ᵢ εᵢ bᵢ, x⟫‖^p` over all `2^{dim H}` sign
choices `ε` for the standard orthonormal basis `(bᵢ)` of `H` is at least `c^p ‖x‖^p`.

Equivalently `‖x‖^p ≤ (c^p)^{-1} (2^{dim H})^{-1} ∑_ε ‖⟪∑ᵢ εᵢ bᵢ, x⟫‖^p`. -/
theorem khintchine_lower_orthonormal_basis (p : ℝ) (hp : 1 ≤ p) :
    ∃ c : ℝ, 0 < c ∧ ∀ {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
      [FiniteDimensional ℂ H] (x : H),
      enorm x ^ p ≤ (ENNReal.ofReal (c ^ p))⁻¹ * (ENNReal.ofReal ((2 : ℝ) ^ Module.finrank ℂ H))⁻¹ *
        ∑ ε : Fin (Module.finrank ℂ H) → Bool,
          enorm (inner ℂ (∑ i, (if ε i then (1 : ℂ) else -1) • (stdOrthonormalBasis ℂ H) i) x) ^ p := by
  classical
  obtain ⟨c, C, hc, hC, hmain⟩ := Commons.Analysis.Walsh.exists_khintchine_hilbert p hp
  refine ⟨c, hc, ?_⟩
  intro H _ _ _ x
  set n : ℕ := Module.finrank ℂ H with hn
  set b : OrthonormalBasis (Fin n) ℂ H := stdOrthonormalBasis ℂ H with hb
  have hp0 : (0 : ℝ) < p := lt_of_lt_of_le zero_lt_one hp
  -- Khintchine's inequality applied in the Hilbert space `ℂ` to the coefficients `⟪bᵢ, x⟫`
  have hk := (hmain (H := ℂ) n (fun i => inner ℂ (b i) x)).1
  have hpars : (∑ i : Fin n, ‖inner ℂ (b i) x‖ ^ 2) = ‖x‖ ^ 2 := b.sum_sq_norm_inner_right x
  have hsummand : ∀ e : Fin n → Bool,
      ‖∑ i : Fin n, (if e i then (1 : ℂ) else -1) • inner ℂ (b i) x‖
        = ‖inner ℂ (∑ i, (if e i then (1 : ℂ) else -1) • b i) x‖ := by
    intro e
    rw [inner_sum_sign_smul b x e]
  set S : ℝ := ∑ e : Fin n → Bool,
      ‖inner ℂ (∑ i, (if e i then (1 : ℂ) else -1) • b i) x‖ ^ p with hSdef
  have hSnn : 0 ≤ S := by
    rw [hSdef]
    exact Finset.sum_nonneg fun e _ => Real.rpow_nonneg (norm_nonneg _) p
  have hsumR : (∑ e : Fin n → Bool,
      ‖∑ i : Fin n, (if e i then (1 : ℂ) else -1) • inner ℂ (b i) x‖ ^ p) = S := by
    rw [hSdef]
    exact Finset.sum_congr rfl fun e _ => by rw [hsummand e]
  have hk' : c * ‖x‖ ≤ (S / (2 : ℝ) ^ n) ^ (1 / p) := by
    rw [hsumR, hpars] at hk
    rw [show (‖x‖ ^ 2) ^ ((1 : ℝ) / 2) = ‖x‖ by
          rw [← Real.sqrt_eq_rpow, Real.sqrt_sq (norm_nonneg x)]] at hk
    exact hk
  have hconv := ofReal_rpow_le_inv_mul_inv_mul hc hp0 (norm_nonneg x) hSnn hk'
  have hL : enorm x ^ p = ENNReal.ofReal (‖x‖ ^ p) := by
    rw [← ENNReal.ofReal_rpow_of_nonneg (norm_nonneg x) hp0.le, ← ofReal_norm]
  have hSr : (∑ ε : Fin n → Bool,
      enorm (inner ℂ (∑ i, (if ε i then (1 : ℂ) else -1) • b i) x) ^ p) = ENNReal.ofReal S := by
    rw [hSdef]
    exact sum_enorm_rpow _ hp0
  rw [hL, hSr]
  exact hconv

end Work.KMTAreas
