import Mathlib

open Filter

namespace Work.Fatou.Analysis

/-- Auxiliary limit: for natural numbers `m < n`, the ratio `(1+R)^m / R^n` tends to `0`
as `R → +∞`. -/
lemma tendsto_one_add_pow_div_pow_atTop {m n : ℕ} (hmn : m < n) :
    Tendsto (fun R : ℝ => (1 + R) ^ m / R ^ n) atTop (nhds 0) := by
  have hk : n - m ≠ 0 := Nat.sub_ne_zero_of_lt hmn
  have hnm : n = m + (n - m) := (Nat.add_sub_of_le hmn.le).symm
  have haux : Tendsto (fun R : ℝ => (1 + R⁻¹) ^ m * R⁻¹ ^ (n - m)) atTop (nhds 0) := by
    have h1 : Tendsto (fun R : ℝ => 1 + R⁻¹) atTop (nhds (1 + 0)) :=
      tendsto_const_nhds.add tendsto_inv_atTop_zero
    have h2 : Tendsto (fun R : ℝ => (1 + R⁻¹) ^ m) atTop (nhds ((1 + 0) ^ m)) := h1.pow m
    have h3 : Tendsto (fun R : ℝ => R⁻¹ ^ (n - m)) atTop (nhds (0 ^ (n - m))) :=
      tendsto_inv_atTop_zero.pow (n - m)
    simpa [hk] using h2.mul h3
  have heq : (fun R : ℝ => (1 + R) ^ m / R ^ n)
      =ᶠ[atTop] (fun R : ℝ => (1 + R⁻¹) ^ m * R⁻¹ ^ (n - m)) := by
    filter_upwards [Filter.eventually_ne_atTop (0 : ℝ)] with R hR
    have hRp : (1 + R⁻¹) = (1 + R) / R := by field_simp; ring
    have hpow : R ^ n = R ^ m * R ^ (n - m) := by
      conv_lhs => rw [hnm]
      rw [pow_add]
    rw [hpow, hRp, div_pow, inv_pow, div_eq_mul_inv, div_eq_mul_inv, mul_inv, mul_assoc]
  exact haux.congr' heq.symm

/-- An entire function of at most polynomial growth is a polynomial, of degree bounded by the
growth exponent.  This is the "generalized Liouville theorem" behind the classical proof that
`IteratedDeriv` of an entire function with growth `(1 + ‖z‖)^m` vanishes above order `m`.

We prove it via the Taylor series at the origin together with Cauchy's estimate for the
`n`-th derivative on circles of arbitrarily large radius. -/
lemma entireEqPolynomialOfGrowth (f : ℂ → ℂ) (hf : Differentiable ℂ f) (m : ℕ) (C : ℝ) (hC : 0 ≤ C)
    (hbd : ∀ z : ℂ, ‖f z‖ ≤ C * (1 + ‖z‖) ^ m) :
    ∃ p : Polynomial ℂ, (∀ z : ℂ, p.eval z = f z) ∧ p.natDegree ≤ m := by
  -- Step 1: all derivatives of order `> m` at the origin vanish, via Cauchy estimates on
  -- circles of radius `R → ∞`.
  have hderiv : ∀ n, m < n → iteratedDeriv n f 0 = 0 := by
    intro n hn
    have hnorm : ‖iteratedDeriv n f 0‖ ≤ 0 := by
      refine le_of_forall_pos_le_add ?_
      intro ε hε
      have hlimK : Tendsto (fun R : ℝ => ((n.factorial : ℝ) * C) * ((1 + R) ^ m / R ^ n))
          atTop (nhds 0) := by
        simpa using (tendsto_const_nhds.mul (tendsto_one_add_pow_div_pow_atTop hn))
      have hev : ∀ᶠ R : ℝ in atTop,
          ((n.factorial : ℝ) * C) * ((1 + R) ^ m / R ^ n) < ε :=
        hlimK.eventually_lt_const hε
      obtain ⟨R, hRlt, hRpos⟩ := (hev.and (eventually_gt_atTop (0 : ℝ))).exists
      have hCauchy : ‖iteratedDeriv n f 0‖ ≤
          (n.factorial : ℝ) * (C * (1 + R) ^ m) / R ^ n := by
        refine Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le n hRpos
          hf.diffContOnCl ?_
        intro z hz
        have hz' : ‖z‖ = R := by
          rw [mem_sphere_iff_norm] at hz
          simpa using hz
        calc ‖f z‖ ≤ C * (1 + ‖z‖) ^ m := hbd z
          _ = C * (1 + R) ^ m := by rw [hz']
      have hle : ‖iteratedDeriv n f 0‖ ≤ ε := by
        calc ‖iteratedDeriv n f 0‖
            ≤ (n.factorial : ℝ) * (C * (1 + R) ^ m) / R ^ n := hCauchy
          _ = ((n.factorial : ℝ) * C) * ((1 + R) ^ m / R ^ n) := by ring_nf
          _ ≤ ε := le_of_lt hRlt
      simpa using hle
    exact norm_eq_zero.mp (le_antisymm hnorm (norm_nonneg _))
  -- Step 2: build the Taylor polynomial of degree `m`.
  let p : Polynomial ℂ := ∑ n ∈ Finset.range (m + 1),
      Polynomial.C ((n.factorial : ℂ)⁻¹ * iteratedDeriv n f 0) * Polynomial.X ^ n
  refine ⟨p, ?_, ?_⟩
  · intro z
    -- The Taylor series of `f` at `0` equals the finite Taylor polynomial, since all higher
    -- Taylor coefficients vanish.
    have htsum : ∑' n : ℕ, (n.factorial : ℂ)⁻¹ * iteratedDeriv n f 0 * z ^ n
        = ∑ n ∈ Finset.range (m + 1),
            (n.factorial : ℂ)⁻¹ * iteratedDeriv n f 0 * z ^ n := by
      refine tsum_eq_sum (s := Finset.range (m + 1)) (fun b hb => ?_)
      rw [Finset.mem_range, not_lt] at hb
      have : m < b := Nat.lt_of_succ_le hb
      rw [hderiv b this]
      simp
    have hpz : p.eval z = ∑ n ∈ Finset.range (m + 1),
        (n.factorial : ℂ)⁻¹ * iteratedDeriv n f 0 * z ^ n := by
      simp only [p]
      rw [Polynomial.eval_finsetSum]
      refine Finset.sum_congr rfl (fun n hn => ?_)
      simp only [Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C]
    rw [hpz]
    rw [← Complex.taylorSeries_eq_of_entire' (0 : ℂ) z hf]
    simp only [sub_zero]
    exact htsum.symm
  · -- Degree bound: each summand `C a * X ^ n` with `n ≤ m` has degree at most `m`.
    simp only [p]
    refine (Polynomial.natDegree_sum_le (Finset.range (m + 1)) _).trans ?_
    rw [Finset.fold_max_le]
    refine ⟨Nat.zero_le m, fun n hn => ?_⟩
    exact (Polynomial.natDegree_C_mul_X_pow_le _ n).trans (by
      rw [Finset.mem_range] at hn; omega)

end Work.Fatou.Analysis
