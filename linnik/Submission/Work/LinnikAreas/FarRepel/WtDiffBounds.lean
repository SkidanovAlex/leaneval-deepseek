import Mathlib

namespace Work.LinnikAreas.FarRepel

/-- Norm of a real number embedded in `ℂ`: `‖(r : ℂ)‖ = |r|`. -/
lemma cnorm_ofReal (r : ℝ) : ‖(r : ℂ)‖ = |r| := RCLike.norm_ofReal r

/-- The elementary power-difference estimate
`‖x^n - y^n‖ ≤ n ‖x - y‖ (max ‖x‖ ‖y‖)^{n-1}`, from the geometric identity
`(x - y) * ∑_{i<n} x^i y^{n-1-i} = x^n - y^n` and the termwise bound
`‖x^i y^{n-1-i}‖ ≤ (max ‖x‖ ‖y‖)^{n-1}`. -/
lemma norm_pow_sub_pow_le (x y : ℂ) (n : ℕ) :
    ‖x ^ n - y ^ n‖ ≤ (n : ℝ) * ‖x - y‖ * (max ‖x‖ ‖y‖) ^ (n - 1) := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn; simp
  · have hgeom : (x - y) * (∑ i ∈ Finset.range n, x ^ i * y ^ (n - 1 - i)) = x ^ n - y ^ n :=
      (Commute.all x y).mul_geom_sum₂ n
    rw [← hgeom, norm_mul]
    have hsum : ‖∑ i ∈ Finset.range n, x ^ i * y ^ (n - 1 - i)‖
        ≤ (n : ℝ) * (max ‖x‖ ‖y‖) ^ (n - 1) := by
      have h1 : ‖∑ i ∈ Finset.range n, x ^ i * y ^ (n - 1 - i)‖
          ≤ ∑ i ∈ Finset.range n, ‖x ^ i * y ^ (n - 1 - i)‖ := norm_sum_le _ _
      have h2 : ∑ i ∈ Finset.range n, ‖x ^ i * y ^ (n - 1 - i)‖
          ≤ ∑ i ∈ Finset.range n, (max ‖x‖ ‖y‖) ^ (n - 1) := by
        apply Finset.sum_le_sum
        intro i hi
        have hi' : i ≤ n - 1 := by have := Finset.mem_range.mp hi; omega
        rw [norm_mul, norm_pow, norm_pow]
        calc ‖x‖ ^ i * ‖y‖ ^ (n - 1 - i)
            ≤ (max ‖x‖ ‖y‖) ^ i * (max ‖x‖ ‖y‖) ^ (n - 1 - i) := by
              apply mul_le_mul
              · exact pow_le_pow_left₀ (norm_nonneg _) (le_max_left _ _) i
              · exact pow_le_pow_left₀ (norm_nonneg _) (le_max_right _ _) _
              · positivity
              · positivity
          _ = (max ‖x‖ ‖y‖) ^ (n - 1) := by
              rw [← pow_add]; congr 1; omega
      rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at h2
      exact h1.trans h2
    calc ‖x - y‖ * ‖∑ i ∈ Finset.range n, x ^ i * y ^ (n - 1 - i)‖
        ≤ ‖x - y‖ * ((n : ℝ) * (max ‖x‖ ‖y‖) ^ (n - 1)) :=
          mul_le_mul_of_nonneg_left hsum (norm_nonneg _)
      _ = (n : ℝ) * ‖x - y‖ * (max ‖x‖ ‖y‖) ^ (n - 1) := by ring

/-- Inverse-power difference bound: for complex `z₁, z₂` and `0 < r ≤ ‖z₁‖, ‖z₂‖`,
`‖(z₁⁻¹)^n - (z₂⁻¹)^n‖ ≤ n ‖z₁ - z₂‖ / r^{n+1}`. -/
lemma norm_inv_pow_sub_le {z₁ z₂ : ℂ} {r : ℝ} (hr : 0 < r)
    (h₁ : r ≤ ‖z₁‖) (h₂ : r ≤ ‖z₂‖) (n : ℕ) :
    ‖(z₁⁻¹) ^ n - (z₂⁻¹) ^ n‖ ≤ (n : ℝ) * ‖z₁ - z₂‖ / r ^ (n + 1) := by
  rcases n with _ | m
  · simp
  · have hz1 : 0 < ‖z₁‖ := lt_of_lt_of_le hr h₁
    have hz2 : 0 < ‖z₂‖ := lt_of_lt_of_le hr h₂
    have hz1ne : z₁ ≠ 0 := norm_pos_iff.mp hz1
    have hz2ne : z₂ ≠ 0 := norm_pos_iff.mp hz2
    have hA := norm_pow_sub_pow_le z₁⁻¹ z₂⁻¹ (m+1)
    have hA' : ‖(z₁⁻¹) ^ (m+1) - (z₂⁻¹) ^ (m+1)‖
        ≤ ((m+1 : ℕ) : ℝ) * ‖z₁⁻¹ - z₂⁻¹‖ * (max ‖z₁⁻¹‖ ‖z₂⁻¹‖) ^ m := by
      simpa using hA
    have hiz1 : ‖z₁⁻¹‖ ≤ r⁻¹ := by rw [norm_inv]; exact (inv_le_inv₀ hz1 hr).mpr h₁
    have hiz2 : ‖z₂⁻¹‖ ≤ r⁻¹ := by rw [norm_inv]; exact (inv_le_inv₀ hz2 hr).mpr h₂
    have hMle : max ‖z₁⁻¹‖ ‖z₂⁻¹‖ ≤ r⁻¹ := max_le hiz1 hiz2
    have hMnn : (0:ℝ) ≤ max ‖z₁⁻¹‖ ‖z₂⁻¹‖ := le_trans (norm_nonneg _) (le_max_left _ _)
    have hp : (max ‖z₁⁻¹‖ ‖z₂⁻¹‖) ^ m ≤ (r⁻¹) ^ m := pow_le_pow_left₀ hMnn hMle m
    have hprod_le : r^2 ≤ ‖z₁‖ * ‖z₂‖ := by
      have h := mul_le_mul h₁ h₂ (le_of_lt hr) (le_of_lt hz1)
      rwa [← pow_two] at h
    have hprod_pos : 0 < ‖z₁‖ * ‖z₂‖ := mul_pos hz1 hz2
    have hinv : (‖z₁‖ * ‖z₂‖)⁻¹ ≤ (r^2)⁻¹ :=
      (inv_le_inv₀ hprod_pos (pow_pos hr 2)).mpr hprod_le
    have hInvDiff : ‖z₁⁻¹ - z₂⁻¹‖ ≤ ‖z₁ - z₂‖ / r^2 := by
      rw [inv_sub_inv hz1ne hz2ne, norm_div, norm_mul, norm_sub_rev]
      rw [div_eq_mul_inv, div_eq_mul_inv]
      exact mul_le_mul_of_nonneg_left hinv (norm_nonneg _)
    have hstep : ((m+1 : ℕ) : ℝ) * ‖z₁⁻¹ - z₂⁻¹‖ * (max ‖z₁⁻¹‖ ‖z₂⁻¹‖) ^ m
        ≤ ((m+1 : ℕ) : ℝ) * (‖z₁ - z₂‖ / r^2) * (r⁻¹) ^ m := by
      apply mul_le_mul
      · exact mul_le_mul_of_nonneg_left hInvDiff (by positivity)
      · exact hp
      · positivity
      · positivity
    have hfin : ((m+1 : ℕ) : ℝ) * (‖z₁ - z₂‖ / r^2) * (r⁻¹)^m
        = ((m+1 : ℕ) : ℝ) * ‖z₁ - z₂‖ / r ^ ((m+1) + 1) := by
      have hkey : (r^2)⁻¹ * (r⁻¹) ^ m = (r ^ ((m+1)+1))⁻¹ := by
        rw [inv_pow, ← mul_inv_rev, ← pow_add]
      calc ((m+1 : ℕ) : ℝ) * (‖z₁ - z₂‖ / r^2) * (r⁻¹)^m
          = ((m+1 : ℕ) : ℝ) * ‖z₁ - z₂‖ * ((r^2)⁻¹ * (r⁻¹)^m) := by
            rw [div_eq_mul_inv]; ring
        _ = ((m+1 : ℕ) : ℝ) * ‖z₁ - z₂‖ * (r ^ ((m+1)+1))⁻¹ := by rw [hkey]
        _ = ((m+1 : ℕ) : ℝ) * ‖z₁ - z₂‖ / r ^ ((m+1) + 1) := by rw [div_eq_mul_inv]
    exact hA'.trans (hstep.trans (le_of_eq hfin))

/-- Difference of real parts bound, obtained from `norm_inv_pow_sub_le` via
`|Re z| ≤ ‖z‖`. -/
lemma re_inv_pow_diff_le {z₁ z₂ : ℂ} {r δ : ℝ} (hr : 0 < r)
    (h₁ : r ≤ ‖z₁‖) (h₂ : r ≤ ‖z₂‖) (hd : ‖z₁ - z₂‖ = δ) (n : ℕ) :
    |((z₁⁻¹)^n).re - ((z₂⁻¹)^n).re| ≤ (n : ℝ) * δ / r^(n+1) := by
  calc |((z₁⁻¹)^n).re - ((z₂⁻¹)^n).re| = |(((z₁⁻¹)^n) - ((z₂⁻¹)^n)).re| := by rw [Complex.sub_re]
    _ ≤ ‖(z₁⁻¹)^n - (z₂⁻¹)^n‖ := Complex.abs_re_le_norm _
    _ ≤ (n : ℝ) * ‖z₁ - z₂‖ / r^(n+1) := norm_inv_pow_sub_le hr h₁ h₂ n
    _ = (n : ℝ) * δ / r^(n+1) := by rw [hd]

/-- **The two elementary difference bounds of the Deuring–Heilbronn argument.** (module `Submission.Work.LinnikAreas.FarRepel.WtDiffBounds`; declare in `namespace Work.LinnikAreas.FarRepel`; import `Mathlib`.)

For `β < 1 < c`, `γ' ∈ ℝ` and `j : ℕ`:

* (real case) `|1/(c-1)^{2j} - 1/(c-β)^{2j}| ≤ 2j(1-β)/(c-1)^{2j+1}`;
* (complex case) `|Re (1/((c+iγ'-1))^{2j}) - Re (1/((c+iγ'-(β:ℂ)))^{2j})| ≤ 2j(1-β)/(c-1)^{2j+1}`.

These are exactly the estimates `|1/(c+it'-1)^{2j} - 1/(c+it'-β₁)^{2j}| ≤ 2j(1-β₁)/(c-1)^{2j+1}`
(`t' = 0`, `γ'`) used in Kadiri–Ng–Wong arXiv:1902.08640 §2.

PROOF ROUTE: for `z₁ = c+iγ'-1`, `z₂ = c+iγ'-β` one has `|z₁|, |z₂| ≥ c-1` and `|z₁ - z₂| = 1-β < 1`;
prove first the elementary estimate `‖x^n - y^n‖ ≤ n‖x-y‖(max ‖x‖ ‖y‖)^{n-1}` (induction on `n`),
apply it to `x = z₁`, `y = z₂`, and rewrite
`(1/z₂)^n - (1/z₁)^n = (z₁^n - z₂^n)/(z₁^n z₂^n)` to get
`≤ n‖z₁-z₂‖/(min ‖z₁‖ ‖z₂‖)^n/max ‖z₁‖ ‖z₂‖ ≤ n(1-β)/(c-1)^{n+1}`.  Finish with `|Re z| ≤ ‖z‖`.
The real case is the same with `z₁ = (c-1 : ℂ)`, `z₂ = (c-β : ℂ)` (use `Complex.norm_ofReal`). -/
theorem WtDiffBounds {c γ' β : ℝ} (hβ : β < 1) (hc : 1 < c) (j : ℕ) :
    |1 / (c - 1) ^ (2 * j) - 1 / (c - β) ^ (2 * j)| ≤ 2 * j * (1 - β) / (c - 1) ^ (2 * j + 1) ∧
    |((1 / ((c : ℂ) + Complex.I * (γ' : ℂ) - 1)) ^ (2 * j)).re
      - ((1 / ((c : ℂ) + Complex.I * (γ' : ℂ) - (β : ℂ))) ^ (2 * j)).re|
      ≤ 2 * j * (1 - β) / (c - 1) ^ (2 * j + 1) := by
  have hc1 : 0 < c - 1 := by linarith
  have hcβ : 0 < c - β := by linarith
  constructor
  · -- real case
    have h₁ : c - 1 ≤ ‖((c - 1 : ℝ) : ℂ)‖ := by
      rw [cnorm_ofReal, abs_of_nonneg hc1.le]
    have h₂ : c - 1 ≤ ‖((c - β : ℝ) : ℂ)‖ := by
      rw [cnorm_ofReal, abs_of_pos hcβ]; linarith
    have hd : ‖((c - 1 : ℝ) : ℂ) - ((c - β : ℝ) : ℂ)‖ = 1 - β := by
      rw [← Complex.ofReal_sub, cnorm_ofReal, abs_of_neg (by linarith)]; ring
    have hb := re_inv_pow_diff_le hc1 h₁ h₂ hd (2 * j)
    have hL1 : ((((c - 1 : ℝ)) : ℂ)⁻¹ ^ (2 * j)).re = 1 / (c - 1) ^ (2 * j) := by
      rw [← Complex.ofReal_inv, ← Complex.ofReal_pow, Complex.ofReal_re, inv_pow, one_div]
    have hL2 : ((((c - β : ℝ)) : ℂ)⁻¹ ^ (2 * j)).re = 1 / (c - β) ^ (2 * j) := by
      rw [← Complex.ofReal_inv, ← Complex.ofReal_pow, Complex.ofReal_re, inv_pow, one_div]
    rw [hL1, hL2] at hb
    refine hb.trans (le_of_eq ?_)
    push_cast; ring
  · -- complex case
    have h₁ : c - 1 ≤ ‖(c : ℂ) + Complex.I * (γ' : ℂ) - 1‖ := by
      have hre : ((c : ℂ) + Complex.I * (γ' : ℂ) - 1).re = c - 1 := by
        simp only [Complex.sub_re, Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im,
          Complex.ofReal_re, Complex.ofReal_im, Complex.one_re]
        ring
      calc c - 1 = |((c : ℂ) + Complex.I * (γ' : ℂ) - 1).re| := by rw [hre, abs_of_pos hc1]
        _ ≤ ‖(c : ℂ) + Complex.I * (γ' : ℂ) - 1‖ := Complex.abs_re_le_norm _
    have h₂ : c - 1 ≤ ‖(c : ℂ) + Complex.I * (γ' : ℂ) - (β : ℂ)‖ := by
      have hre : ((c : ℂ) + Complex.I * (γ' : ℂ) - (β : ℂ)).re = c - β := by
        simp only [Complex.sub_re, Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im,
          Complex.ofReal_re, Complex.ofReal_im]
        ring
      calc c - 1 ≤ c - β := by linarith
        _ = |((c : ℂ) + Complex.I * (γ' : ℂ) - (β : ℂ)).re| := by rw [hre, abs_of_pos hcβ]
        _ ≤ ‖(c : ℂ) + Complex.I * (γ' : ℂ) - (β : ℂ)‖ := Complex.abs_re_le_norm _
    have hd : ‖((c : ℂ) + Complex.I * (γ' : ℂ) - 1) - ((c : ℂ) + Complex.I * (γ' : ℂ) - (β : ℂ))‖ = 1 - β := by
      have hsub : ((c : ℂ) + Complex.I * (γ' : ℂ) - 1) - ((c : ℂ) + Complex.I * (γ' : ℂ) - (β : ℂ))
          = ((β - 1 : ℝ) : ℂ) := by push_cast; ring
      rw [hsub, cnorm_ofReal, abs_of_neg (by linarith)]; ring
    have hb := re_inv_pow_diff_le hc1 h₁ h₂ hd (2 * j)
    rw [one_div, one_div]
    refine hb.trans (le_of_eq ?_)
    push_cast; ring

end Work.LinnikAreas.FarRepel
