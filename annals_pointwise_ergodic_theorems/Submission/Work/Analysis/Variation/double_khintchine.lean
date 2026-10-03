import Mathlib
import Submission.Work.Analysis.Variation.bilinear_basic

namespace Work.Analysis.Variation

/-! ## Auxiliary lemmas for the two-step Khintchine inequality -/

/-- `(x ^ (1/q)) ^ q = x` for `x ≥ 0`, `q ≠ 0`. -/
private lemma rpow_one_div_mul {x q : ℝ} (hx : 0 ≤ x) (hq : q ≠ 0) : (x ^ (1 / q)) ^ q = x := by
  rw [← Real.rpow_mul hx (1 / q) q, one_div_mul_cancel hq, Real.rpow_one]

/-- `(x ^ q) ^ (1/q) = x` for `x ≥ 0`, `q ≠ 0`. -/
private lemma rpow_mul_one_div {x q : ℝ} (hx : 0 ≤ x) (hq : q ≠ 0) : (x ^ q) ^ (1/q) = x := by
  rw [one_div, Real.rpow_rpow_inv hx hq]

/-- The sign `±1` attached to a `Bool`, in the form produced by `khintchine_lower_all_q`. -/
private lemma ite_eq_sgn (b : Bool) : (if b = true then (1 : ℂ) else -1) = sgn b := rfl

/-- **Combination step of the two-step Khintchine inequality.** Given the two lower Khintchine
bounds with common constant `c` -- one for the outer sign average and one for each inner sign
average -- the double average satisfies the expected bound with constant `c ^ 2`. -/
private lemma khintchine_combine {n₁ n₂ : ℕ} {q c S : ℝ}
    {W : (Fin n₁ → Bool) → ℝ} {T : (Fin n₁ → Bool) → (Fin n₂ → Bool) → ℂ}
    (hq : 0 < q) (hc : 0 < c) (hS : 0 ≤ S) (hW : ∀ e₁, 0 ≤ W e₁)
    (hK2 : c * S ^ ((1:ℝ)/2) ≤ ((∑ e₁, W e₁ ^ q) / (2:ℝ) ^ n₁) ^ ((1:ℝ)/q))
    (hK1 : ∀ e₁, c * W e₁ ≤ ((∑ e₂, ‖T e₁ e₂‖ ^ q) / (2:ℝ) ^ n₂) ^ ((1:ℝ)/q)) :
    c * c * S ^ ((1:ℝ)/2)
      ≤ ((∑ e₁, ∑ e₂, ‖T e₁ e₂‖ ^ q) / ((2:ℝ)^n₁ * (2:ℝ)^n₂)) ^ ((1:ℝ)/q) := by
  have h2n₁ : (0:ℝ) < (2:ℝ)^n₁ := by positivity
  have h2n₂ : (0:ℝ) < (2:ℝ)^n₂ := by positivity
  have hcq : 0 ≤ c ^ q := Real.rpow_nonneg (le_of_lt hc) q
  have hstep1 : ∀ e₁, c ^ q * W e₁ ^ q ≤ (∑ e₂, ‖T e₁ e₂‖ ^ q) / (2:ℝ)^n₂ := by
    intro e₁
    have hsum_nn : 0 ≤ ∑ e₂ : Fin n₂ → Bool, ‖T e₁ e₂‖ ^ q :=
      Finset.sum_nonneg fun e₂ _ => Real.rpow_nonneg (norm_nonneg _) q
    have h := Real.rpow_le_rpow (mul_nonneg (le_of_lt hc) (hW e₁)) (hK1 e₁) (le_of_lt hq)
    rw [Real.mul_rpow (le_of_lt hc) (hW e₁),
        rpow_one_div_mul (div_nonneg hsum_nn (le_of_lt h2n₂)) (ne_of_gt hq)] at h
    exact h
  have hsum1 : c ^ q * (∑ e₁, W e₁ ^ q) ≤ (∑ e₁, ∑ e₂, ‖T e₁ e₂‖ ^ q) / (2:ℝ)^n₂ := by
    calc c ^ q * (∑ e₁, W e₁ ^ q)
        = ∑ e₁, c ^ q * W e₁ ^ q :=
          Finset.mul_sum Finset.univ (fun e₁ => W e₁ ^ q) (c ^ q)
      _ ≤ ∑ e₁, (∑ e₂, ‖T e₁ e₂‖ ^ q) / (2:ℝ)^n₂ := Finset.sum_le_sum fun e₁ _ => hstep1 e₁
      _ = (∑ e₁, ∑ e₂, ‖T e₁ e₂‖ ^ q) / (2:ℝ)^n₂ :=
          (Finset.sum_div Finset.univ (fun e₁ => ∑ e₂, ‖T e₁ e₂‖ ^ q) ((2:ℝ)^n₂)).symm
  have hstep2 : c ^ q * ((∑ e₁, W e₁ ^ q) / (2:ℝ)^n₁)
      ≤ (∑ e₁, ∑ e₂, ‖T e₁ e₂‖ ^ q) / ((2:ℝ)^n₁ * (2:ℝ)^n₂) := by
    calc c ^ q * ((∑ e₁, W e₁ ^ q) / (2:ℝ)^n₁)
        = c ^ q * (∑ e₁, W e₁ ^ q) / (2:ℝ)^n₁ := by rw [mul_div_assoc]
      _ ≤ ((∑ e₁, ∑ e₂, ‖T e₁ e₂‖ ^ q) / (2:ℝ)^n₂) / (2:ℝ)^n₁ :=
          div_le_div_of_nonneg_right hsum1 (le_of_lt h2n₁)
      _ = (∑ e₁, ∑ e₂, ‖T e₁ e₂‖ ^ q) / ((2:ℝ)^n₁ * (2:ℝ)^n₂) := by rw [div_div, mul_comm]
  have hstep3 : (c * S ^ ((1:ℝ)/2)) ^ q ≤ (∑ e₁, W e₁ ^ q) / (2:ℝ)^n₁ := by
    have hsumW : 0 ≤ ∑ e₁ : Fin n₁ → Bool, W e₁ ^ q :=
      Finset.sum_nonneg fun e₁ _ => Real.rpow_nonneg (hW e₁) q
    have h := Real.rpow_le_rpow (mul_nonneg (le_of_lt hc) (Real.rpow_nonneg hS (1/2))) hK2 (le_of_lt hq)
    rwa [rpow_one_div_mul (div_nonneg hsumW (le_of_lt h2n₁)) (ne_of_gt hq)] at h
  have hkey : (c * c * S ^ ((1:ℝ)/2)) ^ q
      ≤ (∑ e₁, ∑ e₂, ‖T e₁ e₂‖ ^ q) / ((2:ℝ)^n₁ * (2:ℝ)^n₂) := by
    have hA : c * c * S ^ ((1:ℝ)/2) = c * (c * S ^ ((1:ℝ)/2)) := by ring
    rw [hA, Real.mul_rpow (le_of_lt hc) (mul_nonneg (le_of_lt hc) (Real.rpow_nonneg hS (1/2)))]
    exact le_trans (mul_le_mul_of_nonneg_left hstep3 hcq) hstep2
  have hLnn : 0 ≤ c * c * S ^ ((1:ℝ)/2) :=
    mul_nonneg (mul_nonneg (le_of_lt hc) (le_of_lt hc)) (Real.rpow_nonneg hS (1/2))
  calc c * c * S ^ ((1:ℝ)/2)
      = ((c * c * S ^ ((1:ℝ)/2)) ^ q) ^ ((1:ℝ)/q) :=
        (rpow_mul_one_div hLnn (ne_of_gt hq)).symm
    _ ≤ ((∑ e₁, ∑ e₂, ‖T e₁ e₂‖ ^ q) / ((2:ℝ)^n₁ * (2:ℝ)^n₂)) ^ ((1:ℝ)/q) :=
        Real.rpow_le_rpow (Real.rpow_nonneg hLnn q) hkey (div_nonneg zero_le_one (le_of_lt hq))

/-- **Two-step Khintchine for a bilinear family** (the Khintchine step of the paper's Corollary
`rm-bil`).  For every `q > 0` there is `c > 0` such that for all `n₁, n₂` and every matrix
`y : Fin n₁ → Fin n₂ → ℂ`,

`c (∑_{i,j} ‖y i j‖²)^{1/2} ≤ ( (∑_{ε,ε'} ‖∑_{i,j} ε_i ε'_j y i j‖^q) / (2^{n₁} 2^{n₂}) )^{1/q}`.

The proof is two applications of the uniform lower Khintchine bound
`Work.Analysis.Variation.khintchine_lower_all_q` (available in
`Submission.Work.Analysis.Variation.bilinear_basic`; its constant is uniform in the Hilbert space
and in `n`):

* with `H := ℂ` applied to `z : Fin n₂ → ℂ` it gives `c (∑_j ‖z j‖²)^{1/2} ≤ (E_{ε'} ‖∑_j ε'_j z_j‖^q)^{1/q}`;
* with `H := EuclideanSpace ℂ (Fin n₂)` applied to the vectors `x i := y i ·` it gives
  `c (∑_i ‖x i‖²)^{1/2} ≤ (E_ε ‖∑_i ε_i x_i‖^q)^{1/q}`; here `‖x i‖² = ∑_j ‖y i j‖²` by
  `EuclideanSpace.norm_sq_eq`, and the `j`-th coordinate of `∑_i ε_i x_i` is `∑_i ε_i y i j`
  (`PiLp.smul_apply`, `PiLp.add_apply`, `Finset.sum_apply`), so `‖∑_i ε_i x_i‖ = (∑_j ‖z_j(ε)‖²)^{1/2}`
  with `z_j(ε) = ∑_i ε_i y i j`.

Applying the first bound to `z(ε)` and inserting it into the second yields the claim with constant
`c²`; the sign vector is `ε_i := sgn (e i) = if e i then 1 else -1` and the normalisation is
handled with `Real.mul_rpow`, `Real.rpow_mul`, `mul_one_div_cancel`, `Finset.sum_div`,
`Finset.sum_const_mul`. -/
theorem double_khintchine {q : ℝ} (hq : 0 < q) :
    ∃ c : ℝ, 0 < c ∧ ∀ (n₁ n₂ : ℕ) (y : Fin n₁ → Fin n₂ → ℂ),
      c * (∑ i : Fin n₁, ∑ j : Fin n₂, ‖y i j‖ ^ 2) ^ ((1 : ℝ) / 2)
        ≤ ((∑ e₁ : Fin n₁ → Bool, ∑ e₂ : Fin n₂ → Bool,
              ‖∑ i : Fin n₁, ∑ j : Fin n₂,
                  (Work.Analysis.Variation.sgn (e₁ i) * Work.Analysis.Variation.sgn (e₂ j))
                    * y i j‖ ^ q)
            / ((2 : ℝ) ^ n₁ * (2 : ℝ) ^ n₂)) ^ ((1 : ℝ) / q) := by
  classical
  obtain ⟨c, hc, hkh⟩ := khintchine_lower_all_q.{0} q hq
  refine ⟨c * c, mul_pos hc hc, ?_⟩
  intro n₁ n₂ y
  set x : Fin n₁ → EuclideanSpace ℂ (Fin n₂) := fun i => WithLp.toLp 2 (y i) with hxdef
  have hval : ∀ (i : Fin n₁) (j : Fin n₂), (x i).ofLp j = y i j := by
    intro i j
    simp only [hxdef, WithLp.ofLp_toLp]
  have hCoord : ∀ (e₁ : Fin n₁ → Bool) (j : Fin n₂),
      (∑ i : Fin n₁, sgn (e₁ i) • x i).ofLp j = ∑ i : Fin n₁, sgn (e₁ i) * y i j := by
    intro e₁ j
    rw [WithLp.ofLp_sum, Finset.sum_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [hxdef, PiLp.smul_apply, smul_eq_mul]
  have hrow : ∑ i : Fin n₁, ‖x i‖ ^ 2 = ∑ i : Fin n₁, ∑ j : Fin n₂, ‖y i j‖ ^ 2 := by
    simp only [EuclideanSpace.norm_sq_eq, hval]
  have hWnorm : ∀ e₁ : Fin n₁ → Bool,
      ‖∑ i : Fin n₁, sgn (e₁ i) • x i‖
        = (∑ j : Fin n₂, ‖∑ i : Fin n₁, sgn (e₁ i) * y i j‖ ^ 2) ^ ((1:ℝ)/2) := by
    intro e₁
    rw [EuclideanSpace.norm_eq, Real.sqrt_eq_rpow]
    simp only [hCoord e₁]
  have hK2 : c * (∑ i : Fin n₁, ∑ j : Fin n₂, ‖y i j‖ ^ 2) ^ ((1:ℝ)/2)
      ≤ ((∑ e₁ : Fin n₁ → Bool,
            ((∑ j : Fin n₂, ‖∑ i : Fin n₁, sgn (e₁ i) * y i j‖ ^ 2) ^ ((1:ℝ)/2)) ^ q)
          / (2:ℝ) ^ n₁) ^ ((1:ℝ)/q) := by
    have h := hkh (H := EuclideanSpace ℂ (Fin n₂)) n₁ x
    rw [hrow] at h
    simp only [ite_eq_sgn, hWnorm] at h
    exact h
  have hT : ∀ (e₁ : Fin n₁ → Bool) (e₂ : Fin n₂ → Bool),
      (∑ j : Fin n₂, (if e₂ j = true then (1:ℂ) else -1) • (∑ i : Fin n₁, sgn (e₁ i) * y i j))
        = ∑ i : Fin n₁, ∑ j : Fin n₂, (sgn (e₁ i) * sgn (e₂ j)) * y i j := by
    intro e₁ e₂
    have h1 : (∑ j : Fin n₂, (if e₂ j = true then (1:ℂ) else -1) • (∑ i : Fin n₁, sgn (e₁ i) * y i j))
        = ∑ j : Fin n₂, ∑ i : Fin n₁, (if e₂ j = true then (1:ℂ) else -1) * (sgn (e₁ i) * y i j) := by
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [smul_eq_mul, Finset.mul_sum]
    rw [h1, Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    simp only [sgn]
    ring
  have hK1 : ∀ e₁ : Fin n₁ → Bool,
      c * (∑ j : Fin n₂, ‖∑ i : Fin n₁, sgn (e₁ i) * y i j‖ ^ 2) ^ ((1:ℝ)/2)
        ≤ ((∑ e₂ : Fin n₂ → Bool,
              ‖∑ i : Fin n₁, ∑ j : Fin n₂, (sgn (e₁ i) * sgn (e₂ j)) * y i j‖ ^ q)
            / (2:ℝ) ^ n₂) ^ ((1:ℝ)/q) := by
    intro e₁
    have h := hkh (H := ℂ) n₂ (fun j => ∑ i : Fin n₁, sgn (e₁ i) * y i j)
    simp only [hT e₁] at h
    exact h
  have hWnn : ∀ e₁ : Fin n₁ → Bool,
      0 ≤ (∑ j : Fin n₂, ‖∑ i : Fin n₁, sgn (e₁ i) * y i j‖ ^ 2) ^ ((1:ℝ)/2) :=
    fun e₁ => Real.rpow_nonneg (Finset.sum_nonneg fun j _ => sq_nonneg _) _
  have hS : 0 ≤ ∑ i : Fin n₁, ∑ j : Fin n₂, ‖y i j‖ ^ 2 :=
    Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg _
  exact khintchine_combine (S := ∑ i : Fin n₁, ∑ j : Fin n₂, ‖y i j‖ ^ 2)
    (W := fun e₁ => (∑ j : Fin n₂, ‖∑ i : Fin n₁, sgn (e₁ i) * y i j‖ ^ 2) ^ ((1:ℝ)/2))
    (T := fun e₁ e₂ => ∑ i : Fin n₁, ∑ j : Fin n₂, (sgn (e₁ i) * sgn (e₂ j)) * y i j)
    hq hc hS hWnn hK2 hK1

end Work.Analysis.Variation
