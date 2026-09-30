import Mathlib
import Submission.Work.BW.bm_base
import Submission.Work.BW.mahlerDefs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW

open scoped BigOperators

/-! ## Private auxiliary lemmas

These are self-contained copies of the elementary lemmas the Blanksby–Montgomery Step 3
argument uses (`prod_lt_prod_of_sum_log_lt`, the per-pair geometric comparison and the
`ε⁻²` reformulation).  They are kept `private` so that they cannot clash with the copies in
the companion files `pair_key_ineq`/`pair_product_le`/... , which live above this module in
the import order.
-/

/-- For nonnegative `a`, the product is bounded by `exp` of the sum of the logarithms;
the convention `log 0 = 0` only helps here. -/
private lemma bm_prod_le_exp_sum_log {N : ℕ} (a : Fin N → ℝ) (ha : ∀ j, 0 ≤ a j) :
    ∏ j, a j ≤ Real.exp (∑ j, Real.log (a j)) := by
  by_cases h : ∏ j, a j = 0
  · rw [h]; exact le_of_lt (Real.exp_pos _)
  · have hpos : 0 < ∏ j, a j :=
      lt_of_le_of_ne (Finset.prod_nonneg (fun j _ => ha j)) (Ne.symm h)
    have hall : ∀ j, a j ≠ 0 := fun j hj => h (Finset.prod_eq_zero (Finset.mem_univ j) hj)
    have hl : ∑ j, Real.log (a j) = Real.log (∏ j, a j) := by
      rw [Real.log_prod (fun j _ => hall j)]
    rw [hl, Real.exp_log hpos]

/-- `exp` of the sum of the logarithms of positive numbers is their product. -/
private lemma bm_exp_sum_log {N : ℕ} (e : Fin N → ℝ) (he : ∀ j, 0 < e j) :
    Real.exp (∑ j, Real.log (e j)) = ∏ j, e j := by
  rw [Real.exp_sum]
  exact Finset.prod_congr rfl (fun j _ => Real.exp_log (he j))

/-- If `∑ log a_j < ∑ log e_j` with `a_j ≥ 0` and `e_j > 0`, then `∏ a_j < ∏ e_j`. -/
private lemma bm_prod_lt_prod_of_sum_log_lt {N : ℕ} (a e : Fin N → ℝ)
    (ha : ∀ j, 0 ≤ a j) (he : ∀ j, 0 < e j)
    (h : ∑ j, Real.log (a j) < ∑ j, Real.log (e j)) :
    ∏ j, a j < ∏ j, e j := by
  calc ∏ j, a j ≤ Real.exp (∑ j, Real.log (a j)) := bm_prod_le_exp_sum_log a ha
    _ < Real.exp (∑ j, Real.log (e j)) := Real.exp_lt_exp.mpr h
    _ = ∏ j, e j := bm_exp_sum_log e he

/-- `ρ' = 1 - 1/(12N)` is positive for `N ≥ 1`. -/
private lemma bm_rhoP_pos {N : ℕ} (hN : 1 ≤ N) : 0 < rhoP N := by
  have hNR : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hden : (0 : ℝ) < 12 * (N : ℝ) := by linarith
  rw [rhoP, sub_pos, div_lt_one hden]
  nlinarith

/-- `ρ' = 1 - 1/(12N) ≤ 1`. -/
private lemma bm_rhoP_le_one (N : ℕ) : rhoP N ≤ 1 := by
  rw [rhoP]
  have : 0 ≤ 1 / (12 * (N : ℝ)) := by positivity
  linarith

/-- For `u` on the unit circle, `‖s·u - 1‖²` depends on `u` only through `Re u`. -/
private lemma bm_normSq_smul_sub_one (s : ℝ) (u : ℂ) (hu : ‖u‖ = 1) :
    Complex.normSq ((s : ℂ) * u - 1) = s ^ 2 - 2 * s * u.re + 1 := by
  rw [Complex.normSq_sub, Complex.normSq_mul, Complex.normSq_ofReal, Complex.normSq_one,
      Complex.normSq_eq_norm_sq, hu]
  simp [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]
  ring

/-- Elementary real inequality underlying the per-pair comparison of the
Blanksby–Montgomery argument: the two quadratic forms differ by `(s - e)(e·s - 1)`. -/
private lemma bm_smul_ineq_arith {e s a : ℝ} (he : 0 < e) (hes : e ≤ s) (hs : s ≤ 1) :
    e * (s ^ 2 - 2 * s * a + 1) ≤ s * (e ^ 2 - 2 * e * a + 1) := by
  have hse : 0 ≤ s - e := by linarith
  have hes1 : e ≤ 1 := le_trans hes hs
  have hpos : 0 ≤ s := le_trans (le_of_lt he) hes
  have hes_le : e * s ≤ 1 := by nlinarith [hes1, hpos, he, hs]
  have hle : e * s - 1 ≤ 0 := by linarith
  nlinarith [mul_nonpos_of_nonneg_of_nonpos hse hle]

private lemma bm_pair_key_ineq {e s : ℝ} (he : 0 < e) (hes : e ≤ s) (hs : s ≤ 1) {u : ℂ}
    (hu : ‖u‖ = 1) : e * ‖(s : ℂ) * u - 1‖ ^ 2 ≤ s * ‖(e : ℂ) * u - 1‖ ^ 2 := by
  rw [Complex.sq_norm, Complex.sq_norm]
  rw [bm_normSq_smul_sub_one s u hu, bm_normSq_smul_sub_one e u hu]
  exact bm_smul_ineq_arith he hes hs

/-- `‖α^k - 1‖·‖α^{-k} - 1‖ = ‖α‖^{-k}·‖α^k - 1‖²` for `α ≠ 0`. -/
private lemma bm_pair_norm_eq {α : ℂ} (hα0 : α ≠ 0) (k : ℕ) :
    ‖α ^ k - 1‖ * ‖α ^ (-(k : ℤ)) - 1‖ = (‖α‖ ^ k)⁻¹ * ‖α ^ k - 1‖ ^ 2 := by
  have hz : α ^ (-(k : ℤ)) = (α ^ k)⁻¹ := by rw [zpow_neg, zpow_natCast]
  rw [hz]
  have hz0 : (α ^ k : ℂ) ≠ 0 := pow_ne_zero _ hα0
  have hsecond : ‖(α ^ k)⁻¹ - 1‖ = ‖α ^ k - 1‖ * (‖α‖ ^ k)⁻¹ := by
    have heq : (α ^ k)⁻¹ - 1 = (1 - α ^ k) * (α ^ k)⁻¹ := by
      rw [sub_mul, one_mul, mul_inv_cancel₀ hz0]
    rw [heq, norm_mul, norm_inv, norm_pow, norm_sub_rev]
  rw [hsecond]
  ring

/-- `‖α‖^k · (α/‖α‖)^k = α^k` for `α ≠ 0`. -/
private lemma bm_norm_pow_mul_div_pow_eq {α : ℂ} (hα0 : α ≠ 0) (k : ℕ) :
    ((‖α‖ ^ k : ℝ) : ℂ) * (α / (‖α‖ : ℂ)) ^ k = α ^ k := by
  have hnorm : (‖α‖ : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hα0)
  have hmul : (‖α‖ : ℂ) * (α / (‖α‖ : ℂ)) = α := by
    rw [← mul_div_assoc, mul_div_cancel_left₀ _ hnorm]
  calc ((‖α‖ ^ k : ℝ) : ℂ) * (α / (‖α‖ : ℂ)) ^ k
      = (‖α‖ : ℂ) ^ k * (α / (‖α‖ : ℂ)) ^ k := by rw [Complex.ofReal_pow]
    _ = ((‖α‖ : ℂ) * (α / (‖α‖ : ℂ))) ^ k := by rw [mul_pow]
    _ = α ^ k := by rw [hmul]

/-- **Per-pair bound (Blanksby–Montgomery, Step 3).** If `0 < ‖α‖ ≤ 1` and `0 < ρ ≤ 1`, then for
`1 ≤ k ≤ K` the product `‖α^k-1‖·‖α^{-k}-1‖` is bounded by `ε^{-2}·‖ε·(α/‖α‖)^k - 1‖²` with
`ε := min ρ (‖α‖^K)`. -/
private theorem bm_pair_product_le {α : ℂ} (hα0 : α ≠ 0) (hα1 : ‖α‖ ≤ 1) {ρ : ℝ} (hρ0 : 0 < ρ)
    (hρ1 : ρ ≤ 1) {K k : ℕ} (hk : 1 ≤ k) (hkK : k ≤ K) :
    ‖α ^ k - 1‖ * ‖α ^ (-(k : ℤ)) - 1‖
      ≤ ((min ρ (‖α‖ ^ K))⁻¹) ^ 2
          * ‖((min ρ (‖α‖ ^ K) : ℝ) : ℂ) * (α / (‖α‖ : ℂ)) ^ k - 1‖ ^ 2 := by
  have ha0 : 0 < ‖α‖ := norm_pos_iff.mpr hα0
  set u : ℂ := (α / (‖α‖ : ℂ)) ^ k with hu_def
  set s : ℝ := ‖α‖ ^ k with hs_def
  set e : ℝ := min ρ (‖α‖ ^ K) with he_def
  have hs_pos : 0 < s := by rw [hs_def]; positivity
  have hs_le_one : s ≤ 1 := by rw [hs_def]; exact pow_le_one₀ ha0.le hα1
  have he_pos : 0 < e := by rw [he_def]; exact lt_min hρ0 (pow_pos ha0 K)
  have he_le_one : e ≤ 1 := by rw [he_def]; exact le_trans (min_le_left _ _) hρ1
  have he_le_s : e ≤ s := by
    rw [he_def, hs_def]
    exact le_trans (min_le_right _ _) (pow_le_pow_of_le_one ha0.le hα1 hkK)
  have hu_one : ‖u‖ = 1 := by
    rw [hu_def, norm_pow]
    have hd : ‖α / (‖α‖ : ℂ)‖ = 1 := by
      rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ha0,
        div_self (ne_of_gt ha0)]
    rw [hd, one_pow]
  have hsv : (s : ℂ) * u = α ^ k := by
    rw [hs_def, hu_def]
    exact bm_norm_pow_mul_div_pow_eq hα0 k
  have hkey : e * ‖(s : ℂ) * u - 1‖ ^ 2 ≤ s * ‖(e : ℂ) * u - 1‖ ^ 2 :=
    bm_pair_key_ineq he_pos he_le_s hs_le_one hu_one
  have hmain : s⁻¹ * ‖(s : ℂ) * u - 1‖ ^ 2 ≤ (e⁻¹) ^ 2 * ‖(e : ℂ) * u - 1‖ ^ 2 := by
    have h1 : s⁻¹ * ‖(s : ℂ) * u - 1‖ ^ 2 ≤ e⁻¹ * ‖(e : ℂ) * u - 1‖ ^ 2 := by
      rw [← div_eq_inv_mul, ← div_eq_inv_mul]
      rw [div_le_div_iff₀ hs_pos he_pos]
      nlinarith [hkey]
    have h2 : e⁻¹ * ‖(e : ℂ) * u - 1‖ ^ 2 ≤ (e⁻¹) ^ 2 * ‖(e : ℂ) * u - 1‖ ^ 2 := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      have hone : 1 ≤ e⁻¹ := (one_le_inv₀ he_pos).mpr he_le_one
      calc e⁻¹ = 1 * e⁻¹ := by ring
        _ ≤ e⁻¹ * e⁻¹ := mul_le_mul_of_nonneg_right hone (by positivity)
        _ = (e⁻¹) ^ 2 := by ring
    exact le_trans h1 h2
  have hLHS : ‖α ^ k - 1‖ * ‖α ^ (-(k : ℤ)) - 1‖ = s⁻¹ * ‖α ^ k - 1‖ ^ 2 := by
    rw [bm_pair_norm_eq hα0 k, ← hs_def]
  have hnorm : ‖α ^ k - 1‖ = ‖(s : ℂ) * u - 1‖ := by rw [hsv]
  rw [hLHS, hnorm]
  exact hmain

/-- **Product bound (Blanksby–Montgomery, Acta Arith. 18 (1971), Step 3).**

Let `P ∈ ℤ[X]` be monic of degree `> 1` whose roots are the `N ≥ 1` inverse pairs
`{w_j, w_j⁻¹}` with `0 < ‖w_j‖ ≤ 1`, written in the additive multiset form
`roots P = (univ.val.map w) + (univ.val.map (·⁻¹))`.  Suppose moreover that
`w_j = ‖w_j‖ · exp (2π i θ_j)` (hypothesis `hwθ`, i.e. `θ_j` is the argument of `w_j` divided by
`2π`), that `1 ≤ k ≤ K`, and that with `ε_j := min (rhoP N) (‖w_j‖^K)` one has
`σ_k := ∑_j log ‖1 - ε_j·exp(2π i k θ_j)‖ < ∑_j log ε_j`.  Then
`∏_{u ∈ roots P} ‖u^k - 1‖ < 1`.

Maths: for each `j`, put `α := w_j`, `t := ‖α^k‖ ∈ (0,1]`, `u := (α/‖α‖)^k` (so `‖u‖ = 1` and
`t·u = α^k`).  Then `‖α^k - 1‖² = t² - 2t·Re u + 1` and `‖(α⁻¹)^k - 1‖ = t⁻¹‖α^k - 1‖`, so
`‖α^k-1‖·‖(α⁻¹)^k-1‖ = t + 1/t - 2·Re u`, while
`ε⁻²‖ε·u - 1‖² = 1 + 1/ε² - 2·Re u/ε`.  Since `Re u ≤ 1`, `t ≤ 1`, `t + 1/t ≤ ε + 1/ε` for
`ε ≤ t ≤ 1`, and `(ε-1)³ ≤ 0`, the first is at most the second, i.e.
`‖α^k-1‖·‖(α⁻¹)^k-1‖ ≤ ε_j⁻²‖ε_j·(α/‖α‖)^k - 1‖²`.  Multiplying over `j` turns the left-hand
side into `∏_{u ∈ roots P} ‖u^k - 1‖`, and the right-hand side into
`(∏_j ε_j)⁻² · (∏_j ‖1 - ε_j e(kθ_j)‖)²`, which is `< 1` because
`∏_j ‖1 - ε_j e(kθ_j)‖ < ∏_j ε_j` is exactly the hypothesis `hσ` (sum of logs is strictly
increasing, then exponentiate). -/
theorem bm_prod_norm_lt_one (P : Polynomial ℤ) (hP : P.Monic) {N : ℕ} (hN : 1 ≤ N)
    (w : Fin N → ℂ) (θ : Fin N → ℝ)
    (hw0 : ∀ j, w j ≠ 0) (hw1 : ∀ j, ‖w j‖ ≤ 1)
    (hwθ : ∀ j, w j = (‖w j‖ : ℂ) * Complex.exp (2 * Real.pi * Complex.I * (θ j)))
    (hpair : (P.map (Int.castRingHom ℂ)).roots
        = (Finset.univ : Finset (Fin N)).val.map w
          + (Finset.univ : Finset (Fin N)).val.map (fun j => (w j)⁻¹))
    {K k : ℕ} (hk : 1 ≤ k) (hkK : k ≤ K)
    (hσ : (∑ j, Real.log ‖(1:ℂ) - ((min (rhoP N) (‖w j‖ ^ K) : ℝ) : ℂ)
              * Complex.exp (2 * Real.pi * Complex.I * (k:ℂ) * (θ j : ℂ))‖)
          < ∑ j, Real.log (min (rhoP N) (‖w j‖ ^ K))) :
    ((P.map (Int.castRingHom ℂ)).roots.map (fun u => ‖u ^ k - 1‖)).prod < 1 := by
  classical
  -- The multiset product over the roots is the product of the `N` per-pair products.
  have hLHS : (Multiset.map (fun u : ℂ => ‖u ^ k - 1‖)
        (P.map (Int.castRingHom ℂ)).roots).prod
      = ∏ j, (‖(w j) ^ k - 1‖ * ‖((w j)⁻¹) ^ k - 1‖) := by
    rw [hpair, Multiset.map_add, Multiset.prod_add, Multiset.map_map, Multiset.map_map]
    repeat rw [← Finset.prod_eq_multiset_prod]
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl (fun j _ => ?_)
    simp [Function.comp_apply]
  rw [hLHS]
  -- The geometric per-pair bound, in exactly the form of the hypothesis `hσ`.
  have hpairle : ∀ j : Fin N,
      ‖(w j) ^ k - 1‖ * ‖((w j)⁻¹) ^ k - 1‖
        ≤ ((min (rhoP N) (‖w j‖ ^ K))⁻¹) ^ 2
          * ‖(1 : ℂ) - ((min (rhoP N) (‖w j‖ ^ K) : ℝ) : ℂ)
              * Complex.exp (2 * Real.pi * Complex.I * (k:ℂ) * (θ j : ℂ))‖ ^ 2 := by
    intro j
    have hpos : 0 < ‖w j‖ := norm_pos_iff.mpr (hw0 j)
    have hne : ((‖w j‖ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt hpos)
    have hdiv : w j / ((‖w j‖ : ℝ) : ℂ) = Complex.exp (2 * Real.pi * Complex.I * (θ j)) := by
      nth_rewrite 1 [hwθ j]
      rw [mul_div_cancel_left₀ _ hne]
    have hexp_k : Complex.exp (2 * Real.pi * Complex.I * (θ j)) ^ k
        = Complex.exp (2 * Real.pi * Complex.I * (k:ℂ) * (θ j : ℂ)) := by
      rw [← Complex.exp_nat_mul]
      congr 1
      ring
    have key := bm_pair_product_le (hw0 j) (hw1 j) (bm_rhoP_pos hN) (bm_rhoP_le_one N) hk hkK
    have hinv : (w j) ^ (-(k : ℤ)) = ((w j)⁻¹) ^ k := by rw [zpow_neg, zpow_natCast, inv_pow]
    rw [hinv, hdiv, hexp_k] at key
    have hns : ‖((min (rhoP N) (‖w j‖ ^ K) : ℝ) : ℂ)
          * Complex.exp (2 * Real.pi * Complex.I * (k:ℂ) * (θ j:ℂ)) - 1‖
        = ‖(1 : ℂ) - ((min (rhoP N) (‖w j‖ ^ K) : ℝ) : ℂ)
            * Complex.exp (2 * Real.pi * Complex.I * (k:ℂ) * (θ j:ℂ))‖ := norm_sub_rev _ _
    rw [hns] at key
    exact key
  have hεpos : ∀ j : Fin N, 0 < min (rhoP N) (‖w j‖ ^ K) :=
    fun j => lt_min (bm_rhoP_pos hN) (pow_pos (norm_pos_iff.mpr (hw0 j)) K)
  -- `∏_j ‖1 - ε_j e(k θ_j)‖ < ∏_j ε_j` from the hypothesis on the logarithms.
  have hprod_lt : ∏ j, ‖(1:ℂ) - ((min (rhoP N) (‖w j‖ ^ K) : ℝ) : ℂ)
        * Complex.exp (2 * Real.pi * Complex.I * (k:ℂ) * (θ j:ℂ))‖
      < ∏ j, min (rhoP N) (‖w j‖ ^ K) :=
    bm_prod_lt_prod_of_sum_log_lt _ _ (fun j => norm_nonneg _) hεpos hσ
  -- Multiplying the per-pair bounds.
  have hprod_le : ∏ j, (‖(w j) ^ k - 1‖ * ‖((w j)⁻¹) ^ k - 1‖)
      ≤ ((∏ j, min (rhoP N) (‖w j‖ ^ K))⁻¹) ^ 2
        * (∏ j, ‖(1:ℂ) - ((min (rhoP N) (‖w j‖ ^ K) : ℝ) : ℂ)
            * Complex.exp (2 * Real.pi * Complex.I * (k:ℂ) * (θ j:ℂ))‖) ^ 2 := by
    calc ∏ j, (‖(w j) ^ k - 1‖ * ‖((w j)⁻¹) ^ k - 1‖)
        ≤ ∏ j, (((min (rhoP N) (‖w j‖ ^ K))⁻¹) ^ 2
            * ‖(1:ℂ) - ((min (rhoP N) (‖w j‖ ^ K) : ℝ) : ℂ)
                * Complex.exp (2 * Real.pi * Complex.I * (k:ℂ) * (θ j:ℂ))‖ ^ 2) := by
          apply Finset.prod_le_prod₀
          · intro j _; exact mul_nonneg (norm_nonneg _) (norm_nonneg _)
          · intro j _; exact hpairle j
      _ = ((∏ j, min (rhoP N) (‖w j‖ ^ K))⁻¹) ^ 2
            * (∏ j, ‖(1:ℂ) - ((min (rhoP N) (‖w j‖ ^ K) : ℝ) : ℂ)
                * Complex.exp (2 * Real.pi * Complex.I * (k:ℂ) * (θ j:ℂ))‖) ^ 2 := by
          rw [Finset.prod_mul_distrib, Finset.prod_pow, Finset.prod_pow,
              Finset.prod_inv_distrib]
  have hEpos : 0 < ∏ j, min (rhoP N) (‖w j‖ ^ K) := Finset.prod_pos (fun j _ => hεpos j)
  have hApos : 0 ≤ ∏ j, ‖(1:ℂ) - ((min (rhoP N) (‖w j‖ ^ K) : ℝ) : ℂ)
        * Complex.exp (2 * Real.pi * Complex.I * (k:ℂ) * (θ j:ℂ))‖ :=
    Finset.prod_nonneg (fun j _ => norm_nonneg _)
  calc ∏ j, (‖(w j) ^ k - 1‖ * ‖((w j)⁻¹) ^ k - 1‖)
      ≤ ((∏ j, min (rhoP N) (‖w j‖ ^ K))⁻¹) ^ 2
          * (∏ j, ‖(1:ℂ) - ((min (rhoP N) (‖w j‖ ^ K) : ℝ) : ℂ)
              * Complex.exp (2 * Real.pi * Complex.I * (k:ℂ) * (θ j:ℂ))‖) ^ 2 := hprod_le
    _ = (((∏ j, min (rhoP N) (‖w j‖ ^ K)) ^ 2)⁻¹)
          * (∏ j, ‖(1:ℂ) - ((min (rhoP N) (‖w j‖ ^ K) : ℝ) : ℂ)
              * Complex.exp (2 * Real.pi * Complex.I * (k:ℂ) * (θ j:ℂ))‖) ^ 2 := by
        rw [inv_pow]
    _ < (((∏ j, min (rhoP N) (‖w j‖ ^ K)) ^ 2)⁻¹)
          * ((∏ j, min (rhoP N) (‖w j‖ ^ K)) ^ 2) := by
        exact mul_lt_mul_of_pos_left
          (pow_lt_pow_left₀ hprod_lt hApos (by norm_num)) (inv_pos.mpr (pow_pos hEpos 2))
    _ = 1 := inv_mul_cancel₀ (ne_of_gt (pow_pos hEpos 2))

end Work.BW
