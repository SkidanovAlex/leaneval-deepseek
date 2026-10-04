import Mathlib
import Submission.Work.Diff.STE.Torus

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.STE.Comp

/-- **Generalised Hölder for `tsum`.**  For `r ∈ [0,1]` and nonnegative summable families
`f, g : α → ℝ` one has `∑' i, f i ^ r * g i ^ (1 - r) ≤ (∑' i, f i) ^ r * (∑' i, g i) ^ (1 - r)`,
together with the summability of the left-hand family.

This is Hölder's inequality with the conjugate exponents `r⁻¹` and `(1-r)⁻¹`, i.e.
`Real.summable_and_inner_le_Lp_mul_Lq_tsum_of_nonneg` applied to `f^r` and `g^(1-r)`; the two
endpoints `r = 0` and `r = 1` are the trivial cases. -/
theorem tsum_rpow_mul_rpow_le {α : Type*} (r : ℝ) (hr0 : 0 ≤ r) (hr1 : r ≤ 1)
    (f g : α → ℝ) (hf : ∀ i, 0 ≤ f i) (hg : ∀ i, 0 ≤ g i)
    (hfs : Summable f) (hgs : Summable g) :
    Summable (fun i => f i ^ r * g i ^ (1 - r)) ∧
      ∑' i, f i ^ r * g i ^ (1 - r) ≤ (∑' i, f i) ^ r * (∑' i, g i) ^ (1 - r) := by
  rcases eq_or_lt_of_le hr0 with h0 | hr
  · subst h0
    simp only [Real.rpow_zero, sub_zero, Real.rpow_one, one_mul]
    exact ⟨hgs, le_rfl⟩
  rcases eq_or_lt_of_le (sub_nonneg.mpr hr1) with h1 | hr'
  · have hr1' : r = 1 := by linarith
    subst hr1'
    simp only [Real.rpow_one, sub_self, Real.rpow_zero, mul_one]
    exact ⟨hfs, le_rfl⟩
  have hfr : (fun i => (f i ^ r) ^ r⁻¹) = f := by
    funext i
    rw [← Real.rpow_mul (hf i), mul_inv_cancel₀ (ne_of_gt hr), Real.rpow_one]
  have hgr : (fun i => (g i ^ (1 - r)) ^ (1 - r)⁻¹) = g := by
    funext i
    rw [← Real.rpow_mul (hg i), mul_inv_cancel₀ (ne_of_gt hr'), Real.rpow_one]
  obtain ⟨hsum, hle⟩ := Real.summable_and_inner_le_Lp_mul_Lq_tsum_of_nonneg
    (Real.HolderConjugate.inv_one_sub_inv hr (by linarith : r < 1))
    (fun i => Real.rpow_nonneg (hf i) r) (fun i => Real.rpow_nonneg (hg i) (1 - r))
    (hfr.symm ▸ hfs) (hgr.symm ▸ hgs)
  have e1 : (∑' i, (f i ^ r) ^ r⁻¹) ^ (1 / r⁻¹) = (∑' i, f i) ^ r := by
    rw [hfr]; simp only [one_div, inv_inv]
  have e2 : (∑' i, (g i ^ (1 - r)) ^ (1 - r)⁻¹) ^ (1 / (1 - r)⁻¹) = (∑' i, g i) ^ (1 - r) := by
    rw [hgr]; simp only [one_div, inv_inv]
  rw [e1, e2] at hle
  exact ⟨hsum, hle⟩

/-- **Exponent bookkeeping (pointwise form).**  For `0 ≤ β ≤ s`, `s > 0` and `x, y ≥ 0`:
`(x y^β)^p = x^r · (y^{2s} x²)^{1-r}` with `p = 2s/(2s-β)` and `r = 2(s-β)/(2s-β)`.  The two
exponents match because `r + 2(1-r) = p` and `2s(1-r) = β p`. -/
theorem weighted_pointwise (s β : ℕ) (hβ : β ≤ s) (hs : 0 < s) (x y : ℝ) (hx : 0 ≤ x)
    (hy : 0 ≤ y) :
    (x * y ^ β) ^ ((2 * s : ℝ) / (2 * s - β))
      = x ^ (2 * ((s : ℝ) - (β : ℝ)) / (2 * (s : ℝ) - (β : ℝ)))
        * (y ^ (2 * s) * x ^ 2) ^ (1 - 2 * ((s : ℝ) - (β : ℝ)) / (2 * (s : ℝ) - (β : ℝ))) := by
  have hs' : (0 : ℝ) < (s : ℝ) := by exact_mod_cast hs
  have hβ' : (β : ℝ) ≤ (s : ℝ) := by exact_mod_cast hβ
  have hden : 2 * (s : ℝ) - (β : ℝ) ≠ 0 := by
    have : (0:ℝ) < 2 * (s:ℝ) - (β:ℝ) := by linarith
    linarith
  set R : ℝ := 2 * ((s : ℝ) - (β : ℝ)) / (2 * (s : ℝ) - (β : ℝ)) with hRdef
  set P : ℝ := (2 * s : ℝ) / (2 * s - β) with hPdef
  have hPeq : P = R + 2 * (1 - R) := by
    rw [hPdef, hRdef]; field_simp; ring
  have hBeq : (β : ℝ) * P = 2 * (s : ℝ) * (1 - R) := by
    rw [hPdef, hRdef]; field_simp; ring
  have hPne : R + 2 * (1 - R) ≠ 0 := by
    rw [← hPeq]
    exact div_ne_zero (by positivity) hden
  have hL : (x * y ^ β) ^ P = x ^ P * y ^ ((β : ℝ) * P) := by
    rw [Real.mul_rpow hx (pow_nonneg hy β), ← Real.rpow_natCast y β, ← Real.rpow_mul hy]
  have hR : x ^ R * (y ^ (2 * s) * x ^ 2) ^ (1 - R) = x ^ P * y ^ ((β : ℝ) * P) := by
    have hA : (y ^ (2 * s)) ^ (1 - R) = y ^ (2 * (s : ℝ) * (1 - R)) := by
      rw [← Real.rpow_natCast y (2 * s), ← Real.rpow_mul hy]
      congr 1
      push_cast
      ring
    have hB : (x ^ 2) ^ (1 - R) = x ^ (2 * (1 - R)) := by
      rw [← Real.rpow_natCast x 2, ← Real.rpow_mul hx]
      congr 1
    calc x ^ R * (y ^ (2 * s) * x ^ 2) ^ (1 - R)
        = x ^ R * ((y ^ (2 * s)) ^ (1 - R) * (x ^ 2) ^ (1 - R)) := by
          rw [Real.mul_rpow (pow_nonneg hy (2 * s)) (pow_nonneg hx 2)]
      _ = x ^ R * (y ^ (2 * (s : ℝ) * (1 - R)) * x ^ (2 * (1 - R))) := by rw [hA, hB]
      _ = x ^ R * x ^ (2 * (1 - R)) * y ^ (2 * (s : ℝ) * (1 - R)) := by ring
      _ = x ^ (R + 2 * (1 - R)) * y ^ (2 * (s : ℝ) * (1 - R)) := by
          rw [← Real.rpow_add' hx hPne]
      _ = x ^ P * y ^ (2 * (s : ℝ) * (1 - R)) := by rw [← hPeq]
      _ = x ^ P * y ^ ((β : ℝ) * P) := by rw [← hBeq]
  rw [hL, hR]

/-- **Exponent bookkeeping (final step).**  With `r = 2(s-β)/(2s-β)` and `t = (2s-β)/(2s)` and
`A, Q ≥ 0`: `(A^r Q^{1-r})^t ≤ (1+A)^{1-β/s} (1+Q)^{β/(2s)}`.  Indeed `r t = 1 - β/s` and
`(1-r) t = β/(2s)`, so the left-hand side is `A^{1-β/s} Q^{β/(2s)}`, and the right-hand side only
enlarges the two bases. -/
theorem weighted_final_le (s β : ℕ) (hβ : β ≤ s) (hs : 0 < s) (A Q : ℝ) (hA : 0 ≤ A)
    (hQ : 0 ≤ Q) :
    (A ^ (2 * ((s : ℝ) - (β : ℝ)) / (2 * (s : ℝ) - (β : ℝ)))
        * Q ^ (1 - 2 * ((s : ℝ) - (β : ℝ)) / (2 * (s : ℝ) - (β : ℝ))))
      ^ ((2 * s - β) / (2 * s : ℝ))
    ≤ (1 + A) ^ (1 - (β : ℝ) / s) * (1 + Q) ^ ((β : ℝ) / (2 * s)) := by
  have hs' : (0 : ℝ) < (s : ℝ) := by exact_mod_cast hs
  have hβ' : (β : ℝ) ≤ (s : ℝ) := by exact_mod_cast hβ
  have hden : 2 * (s : ℝ) - (β : ℝ) ≠ 0 := by
    have : (0:ℝ) < 2 * (s:ℝ) - (β:ℝ) := by linarith
    linarith
  set R : ℝ := 2 * ((s : ℝ) - (β : ℝ)) / (2 * (s : ℝ) - (β : ℝ)) with hRdef
  set T : ℝ := (2 * s - β) / (2 * s : ℝ) with hTdef
  have hRT : R * T = 1 - (β : ℝ) / (s : ℝ) := by
    rw [hRdef, hTdef]; field_simp
  have hCT : (1 - R) * T = (β : ℝ) / (2 * (s : ℝ)) := by
    rw [hRdef, hTdef]; field_simp; ring
  have h1 : 0 ≤ 1 - (β : ℝ) / (s : ℝ) := by
    rw [sub_nonneg, div_le_one hs']
    exact hβ'
  have h2 : 0 ≤ (β : ℝ) / (2 * (s : ℝ)) := by positivity
  have key : (A ^ R * Q ^ (1 - R)) ^ T
      = A ^ (1 - (β : ℝ) / (s : ℝ)) * Q ^ ((β : ℝ) / (2 * (s : ℝ))) := by
    rw [Real.mul_rpow (Real.rpow_nonneg hA R) (Real.rpow_nonneg hQ (1 - R)),
        ← Real.rpow_mul hA R T, ← Real.rpow_mul hQ (1 - R) T, hRT, hCT]
  rw [key]
  exact mul_le_mul (Real.rpow_le_rpow hA (by linarith) h1) (Real.rpow_le_rpow hQ (by linarith) h2)
    (Real.rpow_nonneg hQ _) (by positivity)

/-- Interpolation bound for weighted `ℓ^p`-norms of a coefficient family (pure Hölder — no
functional analysis).  With `Λ = ∑ ‖γ k‖`, `Q = ∑ ‖k‖^{2s} ‖γ k‖²`, `0 ≤ β ≤ s` and
`p = 2s/(2s-β)`, one has `(∑_k (‖γ k‖ ‖k‖^β)^p)^{1/p} ≤ Λ^{1-β/s} Q^{β/(2s)}`; the statement
below is this with `Λ, Q` replaced by `1+Λ, 1+Q` (to keep the `Real.rpow` bases positive) and the
root written as the power `(2s-β)/(2s) = 1/p`.

Proof: set `r = 2(s-β)/(2s-β) ∈ [0,1]` and write
`(‖γ k‖ ‖k‖^β)^p = ‖γ k‖^r · ((‖k‖^s ‖γ k‖)²)^{1-r}` (the exponents match because
`r + 2(1-r) = p` and `2s(1-r) = βp`); then Hölder
`∑ f^r g^{1-r} ≤ (∑f)^r (∑g)^{1-r}` with `f k = ‖γ k‖`, `g k = (‖k‖^s ‖γ k‖)²` gives
`(∑ d^p)^{1/p} ≤ Λ^{r/p} Q^{(1-r)/p} = Λ^{1-β/s} Q^{β/(2s)}` since `r/p = 1-β/s` and
`(1-r)/p = β/(2s)`.  Both sums are finite by the two summability hypotheses; the
`ℓ^p`-sum is summable by comparison. -/
theorem weighted_lp_le {ι : Type*} [Fintype ι] [DecidableEq ι] (s β : ℕ) (hβ : β ≤ s) (hs : 0 < s)
    (γ : (ι → ℤ) → ℂ)
    (hΛ : Summable fun k : ι → ℤ => ‖γ k‖)
    (hQ : Summable fun k : ι → ℤ => (‖k‖ : ℝ) ^ (2 * s) * ‖γ k‖ ^ 2) :
    (∑' k : ι → ℤ, (‖γ k‖ * (‖k‖ : ℝ) ^ β) ^ ((2 * s : ℝ) / (2 * s - β)))
        ^ ((2 * s - β) / (2 * s : ℝ))
      ≤ (1 + ∑' k : ι → ℤ, ‖γ k‖) ^ (1 - (β : ℝ) / s)
        * (1 + ∑' k : ι → ℤ, (‖k‖ : ℝ) ^ (2 * s) * ‖γ k‖ ^ 2) ^ ((β : ℝ) / (2 * s)) := by
  let a : (ι → ℤ) → ℝ := fun k => ‖γ k‖
  let q : (ι → ℤ) → ℝ := fun k => (‖k‖ : ℝ) ^ (2 * s) * ‖γ k‖ ^ 2
  have ha : ∀ k, 0 ≤ a k := fun k => norm_nonneg _
  have hq : ∀ k, 0 ≤ q k := fun k => mul_nonneg (pow_nonneg (norm_nonneg _) _) (sq_nonneg _)
  have haS : Summable a := hΛ
  have hqS : Summable q := hQ
  have hs' : (0 : ℝ) < (s : ℝ) := by exact_mod_cast hs
  have hβ' : (β : ℝ) ≤ (s : ℝ) := by exact_mod_cast hβ
  set R : ℝ := 2 * ((s : ℝ) - (β : ℝ)) / (2 * (s : ℝ) - (β : ℝ)) with hRdef
  have hden : (0 : ℝ) < 2 * (s : ℝ) - (β : ℝ) := by linarith
  have hR0 : 0 ≤ R := by
    rw [hRdef]
    exact div_nonneg (by linarith) (le_of_lt hden)
  have hR1 : R ≤ 1 := by
    rw [hRdef]
    rw [div_le_one (by linarith : (0:ℝ) < 2 * (s:ℝ) - (β:ℝ))]
    linarith
  have ht0 : 0 ≤ (2 * s - β) / (2 * s : ℝ) := by
    apply div_nonneg _ (by positivity)
    linarith
  have hpt : ∀ k : ι → ℤ, (a k * (‖k‖ : ℝ) ^ β) ^ ((2 * s : ℝ) / (2 * s - β))
      = (a k) ^ R * (q k) ^ (1 - R) :=
    fun k => weighted_pointwise s β hβ hs (a k) (‖k‖) (ha k) (norm_nonneg _)
  have hsum_eq : (∑' k : ι → ℤ, (a k * (‖k‖ : ℝ) ^ β) ^ ((2 * s : ℝ) / (2 * s - β)))
      = ∑' k : ι → ℤ, (a k) ^ R * (q k) ^ (1 - R) := tsum_congr hpt
  have hH := tsum_rpow_mul_rpow_le R hR0 hR1 a q ha hq haS hqS
  have hfin := weighted_final_le s β hβ hs (∑' k : ι → ℤ, a k) (∑' k : ι → ℤ, q k)
      (tsum_nonneg ha) (tsum_nonneg hq)
  calc (∑' k : ι → ℤ, (a k * (‖k‖ : ℝ) ^ β) ^ ((2 * s : ℝ) / (2 * s - β)))
        ^ ((2 * s - β) / (2 * s : ℝ))
      = (∑' k : ι → ℤ, (a k) ^ R * (q k) ^ (1 - R)) ^ ((2 * s - β) / (2 * s : ℝ)) := by
        rw [hsum_eq]
    _ ≤ ((∑' k : ι → ℤ, a k) ^ R * (∑' k : ι → ℤ, q k) ^ (1 - R))
          ^ ((2 * s - β) / (2 * s : ℝ)) :=
        Real.rpow_le_rpow
          (tsum_nonneg fun k =>
            mul_nonneg (Real.rpow_nonneg (ha k) R) (Real.rpow_nonneg (hq k) (1 - R)))
          hH.2 ht0
    _ ≤ (1 + ∑' k : ι → ℤ, a k) ^ (1 - (β : ℝ) / s)
          * (1 + ∑' k : ι → ℤ, q k) ^ ((β : ℝ) / (2 * s)) := hfin

end Work.Diff.STE.Comp
