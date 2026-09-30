import Mathlib
import Submission.Work.BW.wsb_helpers
import Submission.Work.BW.logHeight_one_le_of_finite
import Submission.Work.BW.isIntegral_of_forall_finitePlace_le_one
import Submission.Work.BW.finitePlace_eq_one_of_abs_log_lt_log_two
import Submission.Work.BW.logHeight_prod_zpow_le
import Submission.Work.BW.es2.isOfFinOrder_of_forall_abs_log_le
import Submission.Work.BW.logHeight_prod_zpow_deviation_le

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
namespace Work.BW.es2

open NumberField

/-!
# The "deviation" step of Waldschmidt's Lemma 4.1

`Work.BW.wsb_isOfFinOrder_prod_of_deviation`: given a non-trivial integer relation
`∑ᵢ tᵢ ℓᵢ = 0` between determinations `ℓᵢ` of the logarithms of `φ (αᵢ)`, together with a vector
`s` whose "deviation" from a multiple of `t` is bounded by `|t_k| · cⱼ` and an archimedean
bound `∑_{j ≠ k} cⱼ h(αⱼ) ≤ 1/(9 d²)`, the product `∏ᵢ αᵢ^{sᵢ}` is a root of unity.

The proof has three steps.

* **The relation `∏ᵢ αᵢ^{tᵢ} = 1`.**  Since `exp (∑ᵢ tᵢ ℓᵢ) = ∏ᵢ φ(αᵢ)^{tᵢ} = φ (∏ᵢ αᵢ^{tᵢ})`
  and `∑ᵢ tᵢ ℓᵢ = 0`, the ring hom `φ` (injective, `K` being a field) forces the relation.

* **The perturbed product.**  Writing `uⱼ := t_k sⱼ - s_k tⱼ`, the relation gives
  `β^{t_k} = ∏ⱼ αⱼ^{uⱼ}` for `β := ∏ᵢ αᵢ^{sᵢ}`, and `u_k = 0`, so `β^{t_k}` is a product over
  the `αⱼ`, `j ≠ k`, with exponents `|uⱼ| ≤ |t_k| cⱼ`.
  By subadditivity of the height and the (finite, resp. archimedean) bounds
  `|log |x|_w| ≤ h(x)` this gives, at *every* place `w` of `K`,
  `|t_k| · |log |β|_w| ≤ h(β^{t_k}) ≤ |t_k| · ∑_{j ≠ k} cⱼ h(αⱼ) ≤ |t_k| · 1/(9 d²)`,
  hence `|log |β|_w| ≤ 1/(9 d²)`.

* **Root of unity.**  In particular every finite place value of `β` is `1` (as `1/9 < log 2`),
  so `β ∈ 𝓞_K` is an algebraic integer, and every embedding of `K` gives a conjugate of `β` of
  modulus within `e^{1/(9d²)}` of `1`.  The Frobenius/power-sum criterion for the house of a
  monic integer polynomial (`Work.BW.isOfFinOrder_of_forall_abs_log_le`) then shows that `β` is
  a root of unity.
-/

section Aux

/-- If `ℓ i` is a determination of `log (φ (α i))` and the integer relation `∑ i, t i * ℓ i = 0`
holds, then `∏ i, α i ^ (t i) = 1`.  (Injectivity of `φ`, applied to
`exp (∑ i, t i * ℓ i) = φ (∏ i, α i ^ (t i))`.) -/
lemma wsb_prod_zpow_eq_one_of_exp_sum_eq_zero {K : Type*} [Field K] [NumberField K] {m : ℕ}
    (φ : K →+* ℂ) (α : Fin m → K) (ℓ : Fin m → ℂ) (t : Fin m → ℤ)
    (hℓ : ∀ i, Complex.exp (ℓ i) = φ (α i)) (ht : ∑ i, (t i : ℂ) * ℓ i = 0) :
    ∏ i, α i ^ (t i : ℤ) = 1 := by
  apply φ.injective
  rw [map_one, ← Complex.exp_zero, ← ht, Complex.exp_sum, map_prod]
  exact Finset.prod_congr rfl fun i _ => by rw [Complex.exp_int_mul, hℓ i, map_zpow₀]

/-- The perturbed product identity: if `∏ i, α i ^ (t i) = 1`, then for every `k`
`(∏ i, α i ^ (s i)) ^ (t k) = ∏ i, α i ^ (t k * s i - s k * t i)`. -/
lemma wsb_pow_prod_zpow_eq {K : Type*} [Field K] {m : ℕ} (α : Fin m → K)
    (hα : ∀ i, α i ≠ 0) (t s : Fin m → ℤ) (k : Fin m)
    (h1 : ∏ i, α i ^ (t i : ℤ) = 1) :
    (∏ i, α i ^ (s i : ℤ)) ^ (t k : ℤ) = ∏ i, α i ^ (t k * s i - s k * t i : ℤ) := by
  have hL : (∏ i, α i ^ (s i : ℤ)) ^ (t k : ℤ) = ∏ i, α i ^ (s i * t k : ℤ) := by
    rw [← Finset.prod_zpow]
    exact Finset.prod_congr rfl fun i _ => (zpow_mul (α i) (s i) (t k)).symm
  have hR : ∏ i, α i ^ (t k * s i - s k * t i : ℤ) = ∏ i, α i ^ (s i * t k : ℤ) := by
    have hpoint : ∀ i : Fin m, α i ^ (t k * s i - s k * t i : ℤ)
        = α i ^ (s i * t k : ℤ) * (α i ^ (t i * s k : ℤ))⁻¹ := by
      intro i
      rw [show (t k * s i - s k * t i : ℤ) = s i * t k + -(t i * s k) by ring,
        zpow_add₀ (hα i), zpow_neg]
    rw [Finset.prod_congr rfl (fun i _ => hpoint i), Finset.prod_mul_distrib,
      Finset.prod_inv_distrib]
    have h2 : ∏ i, α i ^ (t i * s k : ℤ) = 1 := by
      rw [Finset.prod_congr rfl (fun i _ => zpow_mul (α i) (t i) (s k)),
        Finset.prod_zpow, h1]
      simp
    rw [h2, inv_one, mul_one]
  rw [hL, hR]

/-- `1/9 < log 2` (the threshold of Kronecker's theorem used below). -/
lemma one_div_nine_lt_log_two : (1 : ℝ) / 9 < Real.log 2 := by
  have h := Real.log_two_gt_d9
  norm_num at h ⊢
  linarith

end Aux


theorem wsb_isOfFinOrder_prod_of_deviation {K : Type*} [Field K] [NumberField K] {m : ℕ} (φ : K →+* ℂ) (α : Fin m → K) (hα : ∀ i, α i ≠ 0) (ℓ : Fin m → ℂ) (hℓ : ∀ i, Complex.exp (ℓ i) = φ (α i)) (t : Fin m → ℤ) (k : Fin m) (htk : t k ≠ 0) (ht : ∑ i, (t i : ℂ) * ℓ i = 0) (s : Fin m → ℤ) (c : Fin m → ℝ) (hdev : ∀ j : Fin m, j ≠ k → |((t k : ℤ) : ℝ) * (s j : ℝ) - (s k : ℝ) * ((t j : ℤ) : ℝ)| ≤ |((t k : ℤ) : ℝ)| * c j) (harch : (∑ j ∈ Finset.univ.erase k, c j * Height.logHeight₁ (α j)) ≤ 1 / (9 * (Module.finrank ℚ K : ℝ) ^ 2)) : IsOfFinOrder (∏ i, α i ^ (s i : ℤ)) := by
  classical
  have hd1 : (1 : ℝ) ≤ (Module.finrank ℚ K : ℝ) := by
    have h := Module.finrank_pos (R := ℚ) (M := K)
    exact_mod_cast h
  have htkabs : 0 < |((t k : ℤ) : ℝ)| := by
    rw [abs_pos, Int.cast_ne_zero]; exact htk
  set β : K := ∏ i, α i ^ (s i : ℤ) with hβdef
  have hβne : β ≠ 0 := by
    rw [hβdef]
    exact Finset.prod_ne_zero_iff.mpr fun i _ => zpow_ne_zero _ (hα i)
  have ht_one : ∏ i, α i ^ (t i : ℤ) = 1 :=
    wsb_prod_zpow_eq_one_of_exp_sum_eq_zero φ α ℓ t hℓ ht
  set γ : K := ∏ i, α i ^ (t k * s i - s k * t i : ℤ) with hγdef
  have hγeq : β ^ (t k : ℤ) = γ := by
    rw [hβdef, hγdef]
    exact wsb_pow_prod_zpow_eq α hα t s k ht_one
  set R : ℝ := ∑ j ∈ Finset.univ.erase k, c j * Height.logHeight₁ (α j) with hRdef
  have hRle : R ≤ 1 / (9 * (Module.finrank ℚ K : ℝ) ^ 2) := by
    rw [hRdef]; exact harch
  have hheight : Height.logHeight₁ γ ≤ |((t k : ℤ) : ℝ)| * R := by
    rw [hγdef, hRdef]
    exact logHeight_prod_zpow_deviation_le α t s k c hdev
  have hinf : ∀ σ : K →+* ℂ,
      |Real.log ‖σ β‖| ≤ 1 / (9 * (Module.finrank ℚ K : ℝ) ^ 2) := by
    intro σ
    have hγlog : Real.log ‖σ γ‖ = (t k : ℝ) * Real.log ‖σ β‖ := by
      rw [← hγeq, map_zpow₀, norm_zpow, Real.log_zpow]
    have hb : |Real.log ‖σ γ‖| ≤ Height.logHeight₁ γ := by
      have h := abs_log_le_of_infinite γ (NumberField.InfinitePlace.mk σ)
      simpa using h
    rw [hγlog, abs_mul] at hb
    have h2 : |((t k : ℤ) : ℝ)| * |Real.log ‖σ β‖|
        ≤ |((t k : ℤ) : ℝ)| * R := le_trans hb hheight
    have h3 : |Real.log ‖σ β‖| ≤ R := (mul_le_mul_iff_of_pos_left htkabs).mp h2
    linarith [h3, hRle]
  have hfin : ∀ v : NumberField.FinitePlace K,
      |Real.log (v β)| ≤ 1 / (9 * (Module.finrank ℚ K : ℝ) ^ 2) := by
    intro v
    have hγlog : Real.log (v γ) = (t k : ℝ) * Real.log (v β) := by
      rw [← hγeq, map_zpow₀, Real.log_zpow]
    have hb : |Real.log (v γ)| ≤ Height.logHeight₁ γ := abs_log_le_of_finite γ v
    rw [hγlog, abs_mul] at hb
    have h2 : |((t k : ℤ) : ℝ)| * |Real.log (v β)| ≤ |((t k : ℤ) : ℝ)| * R :=
      le_trans hb hheight
    have h3 : |Real.log (v β)| ≤ R := (mul_le_mul_iff_of_pos_left htkabs).mp h2
    linarith [h3, hRle]
  have hv_one : ∀ v : NumberField.FinitePlace K, v β = 1 := by
    intro v
    refine finitePlace_eq_one_of_abs_log_lt_log_two v hβne ?_
    have h1 : 1 / (9 * (Module.finrank ℚ K : ℝ) ^ 2) ≤ (1 : ℝ) / 9 := by
      have h9 : (9 : ℝ) ≤ 9 * (Module.finrank ℚ K : ℝ) ^ 2 := by nlinarith
      exact one_div_le_one_div_of_le (by norm_num) h9
    linarith [hfin v, h1, one_div_nine_lt_log_two]
  have hint : IsIntegral ℤ β :=
    isIntegral_of_forall_finitePlace_le_one β fun v => by simp [hv_one v]
  have hmain := isOfFinOrder_of_forall_abs_log_le β hβne hint hinf
  rwa [hβdef] at hmain

end Work.BW.es2
