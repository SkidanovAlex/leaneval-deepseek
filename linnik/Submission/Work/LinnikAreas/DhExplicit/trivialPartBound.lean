import Mathlib

namespace Work.LinnikAreas.DhExplicit

/-- Elementary lower bound for the real part of an inverse power:
for any complex `z` and `k : ℕ`, `Re (z ^ k)⁻¹ ≥ -‖z‖^{-k}`.
This is just `|Re w| ≤ ‖w‖` applied to `w = (z ^ k)⁻¹`. -/
lemma re_inv_pow_ge_neg (z : ℂ) (k : ℕ) : -((‖z‖ ^ k)⁻¹) ≤ ((z ^ k)⁻¹).re := by
  have h1 : -‖(z ^ k)⁻¹‖ ≤ ((z ^ k)⁻¹).re := by
    have h := Complex.abs_re_le_norm ((z ^ k)⁻¹)
    have h2 := neg_abs_le ((z ^ k)⁻¹).re
    linarith
  rwa [norm_inv, norm_pow] at h1

/-- **Elementary sign of the "trivial-zero" (Γ) part of the explicit formula, even character.**

For `j ≥ 1`, `c > 0`, `γ' ∈ ℝ`, with `w = c + iγ'` and the two Γ-series summable,

`Re (1/c^{2j}) + Re (1/w^{2j}) ≤ 2 Σ'_n Re (1/(c+2n))^{2j} + 2 Σ'_n Re (1/(w+2n))^{2j}`.

PROOF ROUTE (elementary): write `RHS − LHS = Re(1/c^{2j}) + Re(1/w^{2j}) +
2Σ_{n≥1}Re(1/(c+2n))^{2j} + 2Σ_{n≥1}Re(1/(w+2n))^{2j}` (the `n = 0` terms of the two series
are the two LHS terms, with the factor `2`), then use the termwise bound
`Re (1/(z+2n))^{2j} ≥ -|z+2n|^{-2j} ≥ -(c+2n)^{-2j}` for `n ≥ 1` (valid because
`Re z = c > 0`), and `Re (1/z^{2j}) ≥ -|z|^{-2j} ≥ -(Re z)^{-2j}`, i.e.
`Re(1/c^{2j}) + Re(1/w^{2j}) ≥ 0`.  All `Σ'` manipulations are by
`Summable.tsum_sub`/`tsum_add`/`tsum_le_tsum` on the `.re` families (summable by dominance:
`|1/(z+2n)^{2j}| ≤ (c+2n)^{-2j}` and `Σ (c+2n)^{-2j} < ∞` for `2j ≥ 2`). -/
theorem trivialPartBound (j : ℕ) (hj : 1 ≤ j) {c γ' : ℝ} (hc : 0 < c)
    (h1 : Summable (fun n : ℕ => (1 / ((c : ℂ) + ((2 * n : ℕ) : ℂ))) ^ (2 * j)))
    (h2 : Summable (fun n : ℕ => (1 / (((c : ℂ) + Complex.I * (γ' : ℂ)) + ((2 * n : ℕ) : ℂ))) ^ (2 * j))) :
    (1 / ((c : ℂ) ^ (2 * j))).re + (1 / (((c : ℂ) + Complex.I * (γ' : ℂ))) ^ (2 * j)).re
      ≤ 2 * (∑' n : ℕ, ((1 / ((c : ℂ) + ((2 * n : ℕ) : ℂ))) ^ (2 * j)).re)
        + 2 * (∑' n : ℕ, ((1 / (((c : ℂ) + Complex.I * (γ' : ℂ)) + ((2 * n : ℕ) : ℂ))) ^ (2 * j)).re) := by
  -- summability of the real parts, transported through `Complex.reCLM`
  have h1re : Summable (fun n : ℕ => ((1 / ((c : ℂ) + ((2 * n : ℕ) : ℂ))) ^ (2 * j)).re) :=
    h1.map Complex.reCLM Complex.reCLM.continuous
  have h2re : Summable (fun n : ℕ => ((1 / (((c : ℂ) + Complex.I * (γ' : ℂ)) + ((2 * n : ℕ) : ℂ))) ^ (2 * j)).re) :=
    h2.map Complex.reCLM Complex.reCLM.continuous
  -- termwise nonnegativity of the summand `F n + G n`
  have hnn : ∀ n : ℕ, 0 ≤ ((1 / ((c : ℂ) + ((2 * n : ℕ) : ℂ))) ^ (2 * j)).re
      + ((1 / (((c : ℂ) + Complex.I * (γ' : ℂ)) + ((2 * n : ℕ) : ℂ))) ^ (2 * j)).re := by
    intro n
    -- the "real" term is the inverse power of a positive real
    have hF : ((1 / ((c : ℂ) + ((2 * n : ℕ) : ℂ))) ^ (2 * j)).re = ((c + 2*n : ℝ) ^ (2*j))⁻¹ := by
      have h : (c : ℂ) + ((2 * n : ℕ) : ℂ) = ((c + 2*n : ℝ) : ℂ) := by push_cast; ring
      rw [h, one_div, ← Complex.ofReal_inv, ← Complex.ofReal_pow, Complex.ofReal_re, inv_pow]
    -- the real part of `w + 2n`
    have hyre : (((c : ℂ) + Complex.I * (γ' : ℂ)) + ((2 * n : ℕ) : ℂ)).re = c + 2*n := by
      simp [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.I_re, Complex.ofReal_im]
    -- and it is bounded by the modulus of `w + 2n`
    have hnormle : c + 2*n ≤ ‖((c : ℂ) + Complex.I * (γ' : ℂ)) + ((2 * n : ℕ) : ℂ)‖ := by
      have h := Complex.abs_re_le_norm (((c : ℂ) + Complex.I * (γ' : ℂ)) + ((2 * n : ℕ) : ℂ))
      rw [hyre] at h
      rwa [abs_of_nonneg (by positivity : (0:ℝ) ≤ c + 2*n)] at h
    have hG := re_inv_pow_ge_neg (((c : ℂ) + Complex.I * (γ' : ℂ)) + ((2 * n : ℕ) : ℂ)) (2*j)
    have hGex : ((1 / (((c : ℂ) + Complex.I * (γ' : ℂ)) + ((2 * n : ℕ) : ℂ))) ^ (2 * j)).re
        = (((((c : ℂ) + Complex.I * (γ' : ℂ)) + ((2 * n : ℕ) : ℂ)) ^ (2*j))⁻¹).re := by
      rw [one_div, inv_pow]
    have hpos : (0:ℝ) < c + 2*n := by positivity
    have hba : (c + 2*n : ℝ)^(2*j) ≤ ‖((c : ℂ) + Complex.I * (γ' : ℂ)) + ((2 * n : ℕ) : ℂ)‖^(2*j) :=
      pow_le_pow_left₀ (le_of_lt hpos) hnormle (2*j)
    have hinv : (‖((c : ℂ) + Complex.I * (γ' : ℂ)) + ((2 * n : ℕ) : ℂ)‖^(2*j))⁻¹ ≤ ((c + 2*n : ℝ)^(2*j))⁻¹ :=
      inv_anti₀ (pow_pos hpos _) hba
    linarith [hF, hG, hGex, hG, hinv]
  have hsum : Summable (fun n : ℕ => ((1 / ((c : ℂ) + ((2 * n : ℕ) : ℂ))) ^ (2 * j)).re
      + ((1 / (((c : ℂ) + Complex.I * (γ' : ℂ)) + ((2 * n : ℕ) : ℂ))) ^ (2 * j)).re) := h1re.add h2re
  -- the `n = 0` term is bounded by the whole sum
  have hle : ((1 / ((c : ℂ) + ((2 * 0 : ℕ) : ℂ))) ^ (2 * j)).re
      + ((1 / (((c : ℂ) + Complex.I * (γ' : ℂ)) + ((2 * 0 : ℕ) : ℂ))) ^ (2 * j)).re
      ≤ ∑' n : ℕ, (((1 / ((c : ℂ) + ((2 * n : ℕ) : ℂ))) ^ (2 * j)).re
      + ((1 / (((c : ℂ) + Complex.I * (γ' : ℂ)) + ((2 * n : ℕ) : ℂ))) ^ (2 * j)).re) :=
    hsum.le_tsum 0 (fun n _ => hnn n)
  have hS : 0 ≤ ∑' n : ℕ, (((1 / ((c : ℂ) + ((2 * n : ℕ) : ℂ))) ^ (2 * j)).re
      + ((1 / (((c : ℂ) + Complex.I * (γ' : ℂ)) + ((2 * n : ℕ) : ℂ))) ^ (2 * j)).re) :=
    tsum_nonneg hnn
  have hsum_eq : (∑' n : ℕ, (((1 / ((c : ℂ) + ((2 * n : ℕ) : ℂ))) ^ (2 * j)).re
      + ((1 / (((c : ℂ) + Complex.I * (γ' : ℂ)) + ((2 * n : ℕ) : ℂ))) ^ (2 * j)).re))
      = (∑' n : ℕ, ((1 / ((c : ℂ) + ((2 * n : ℕ) : ℂ))) ^ (2 * j)).re)
        + (∑' n : ℕ, ((1 / (((c : ℂ) + Complex.I * (γ' : ℂ)) + ((2 * n : ℕ) : ℂ))) ^ (2 * j)).re) :=
    h1re.tsum_add h2re
  -- the LHS is exactly the `n = 0` term of the two series
  have hp : (1 / ((c : ℂ) ^ (2 * j))).re + (1 / (((c : ℂ) + Complex.I * (γ' : ℂ))) ^ (2 * j)).re
      = ((1 / ((c : ℂ) + ((2 * 0 : ℕ) : ℂ))) ^ (2 * j)).re
        + ((1 / (((c : ℂ) + Complex.I * (γ' : ℂ)) + ((2 * 0 : ℕ) : ℂ))) ^ (2 * j)).re := by
    simp only [Nat.mul_zero, Nat.cast_zero, add_zero, one_div, inv_pow]
  rw [hp]
  linarith [hle, hS, hsum_eq]

end Work.LinnikAreas.DhExplicit
