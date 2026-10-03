import Mathlib
import Submission.Commons.Analysis.Polynomial.abs_eval_sub_eval_le

/-!
# `Work.A3.exp_phase_variation_bound`

For an integer polynomial `Q` of degree `d ≥ 2` and a real `β` in the major-arc range
`|β| ≤ 1/(2 N^d)`, the total variation of the exponential phase `n ↦ e(-2π i β Q(n))` along the
`N - 1` consecutive integer steps of `[1, N]` is bounded by a constant depending only on `Q`.

The proof is the elementary "telescoping derivative" argument.  Over a unit step, the phase
difference is the finite difference `Q(v) - Q(u)`, and since `Q` has degree `d` it is
`C_Q * N^{d - 1}`-Lipschitz on `[0, N]`
(`Commons.Analysis.Polynomial.abs_eval_sub_eval_le`, obtained from a factorisation of
`x^i - y^i`).  Together with `|e^{ix} - e^{iy}| ≤ |x - y|` this gives the pointwise bound

`|e(-βQ(v)) - e(-βQ(u))| ≤ 2π |β| C_Q N^{d-1} ≤ π C_Q / N`,

and there are only `N - 1` steps, so the total is `≤ π C_Q`.
-/

namespace Work.A3

/-- `‖e^{ix} - e^{iy}‖ ≤ |x - y|` for real `x`, `y`. -/
lemma norm_exp_I_mul_sub_le (x y : ℝ) :
    ‖Complex.exp (Complex.I * (x : ℂ)) - Complex.exp (Complex.I * (y : ℂ))‖ ≤ |x - y| := by
  have h : Complex.exp (Complex.I * (x : ℂ)) - Complex.exp (Complex.I * (y : ℂ))
      = Complex.exp (Complex.I * (y : ℂ))
          * (Complex.exp (Complex.I * ((x - y : ℝ) : ℂ)) - 1) := by
    rw [mul_sub, ← Complex.exp_add, mul_one]
    congr 1
    push_cast
    ring_nf
  rw [h, norm_mul, Complex.norm_exp_I_mul_ofReal, one_mul]
  exact Real.norm_exp_I_mul_ofReal_sub_one_le

/-- `‖e^{-2πiβa} - e^{-2πiβb}‖ ≤ 2π|β||a - b|` for real `a`, `b`. -/
lemma norm_exp_neg_two_pi_I_mul_sub_le (β a b : ℝ) :
    ‖Complex.exp (-(2 * Real.pi * Complex.I * (β * a)))
      - Complex.exp (-(2 * Real.pi * Complex.I * (β * b)))‖
      ≤ 2 * Real.pi * |β| * |a - b| := by
  have ha : -(2 * Real.pi * Complex.I * (β * a))
      = Complex.I * ((-(2 * Real.pi * (β * a))) : ℝ) := by push_cast; ring
  have hb : -(2 * Real.pi * Complex.I * (β * b))
      = Complex.I * ((-(2 * Real.pi * (β * b))) : ℝ) := by push_cast; ring
  rw [ha, hb]
  refine le_trans (norm_exp_I_mul_sub_le _ _) ?_
  have hkey : -(2 * Real.pi * (β * a)) - (-(2 * Real.pi * (β * b)))
      = 2 * Real.pi * β * (b - a) := by ring
  have hEq : |-(2 * Real.pi * (β * a)) - (-(2 * Real.pi * (β * b)))|
      = 2 * Real.pi * |β| * |a - b| := by
    rw [hkey, abs_mul, abs_mul, abs_of_nonneg (show (0 : ℝ) ≤ 2 * Real.pi by positivity),
      abs_sub_comm]
  exact le_of_eq hEq

/-- **Phase variation bound.**  For an integer polynomial `Q` of degree `d ≥ 2` there is a
constant `A ≥ 0` such that for every `N ≥ 1` and every real `β` with `|β| ≤ 1/(2 N^d)`, the sum of
the `N - 1` one-step increments of the phase `n ↦ e(-2π i β Q(n))` over `n ∈ [1, N]` is at most
`A`. -/
theorem exp_phase_variation_bound (Q : Polynomial ℤ) (hd : 2 ≤ Polynomial.natDegree Q) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ (N : ℕ) (β : ℝ), 1 ≤ N →
      |β| ≤ (1 / 2) / ((N : ℝ) ^ Polynomial.natDegree Q) →
      ∑ n ∈ Finset.range (N - 1),
        ‖Complex.exp (-(2 * Real.pi * Complex.I * (β * (((Q.eval ((n + 2 : ℕ) : ℤ)) : ℤ) : ℝ))))
          - Complex.exp (-(2 * Real.pi * Complex.I * (β * (((Q.eval ((n + 1 : ℕ) : ℤ)) : ℤ) : ℝ))))‖ ≤ A := by
  set d : ℕ := Polynomial.natDegree Q with hddef
  set W : Polynomial ℝ := Q.map (Int.castRingHom ℝ) with hW
  set C : ℝ := ∑ i ∈ Finset.range (d + 1), |W.coeff i| with hC
  set K : ℝ := C * (d : ℝ) with hK
  have hd1 : 1 ≤ d := by omega
  have hCnn : 0 ≤ C := by
    rw [hC]; exact Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hKnn : 0 ≤ K := by
    rw [hK]; exact mul_nonneg hCnn (Nat.cast_nonneg d)
  refine ⟨Real.pi * K, mul_nonneg Real.pi_pos.le hKnn, ?_⟩
  intro N β hN hβ
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hNpos : (0 : ℝ) < (N : ℝ) := lt_of_lt_of_le one_pos hN1
  have hWdeg : W.natDegree ≤ d := by
    rw [hW, hddef]; exact Polynomial.natDegree_map_le
  have hev : ∀ m : ℕ, Polynomial.eval ((m : ℤ) : ℝ) W = ((Q.eval (m : ℤ) : ℤ) : ℝ) := by
    intro m
    rw [hW, Polynomial.eval_map]
    exact Polynomial.eval₂_at_apply (Int.castRingHom ℝ) (m : ℤ)
  -- the polynomial finite-difference bound
  have hpoly : ∀ n ∈ Finset.range (N - 1),
      |(((Q.eval ((n + 2 : ℕ) : ℤ)) : ℤ) : ℝ) - (((Q.eval ((n + 1 : ℕ) : ℤ)) : ℤ) : ℝ)|
        ≤ K * (N : ℝ) ^ (d - 1) := by
    intro n hn
    have hn2 : n + 2 ≤ N := by
      have := Finset.mem_range.mp hn; omega
    have hn1 : n + 1 ≤ N := by
      have := Finset.mem_range.mp hn; omega
    have hcom : |Polynomial.eval ((n + 2 : ℕ) : ℝ) W - Polynomial.eval ((n + 1 : ℕ) : ℝ) W|
        ≤ C * (d : ℝ) * (N : ℝ) ^ (d - 1) := by
      have hraw := Commons.Analysis.Polynomial.abs_eval_sub_eval_le W d hd1 hWdeg
        (X := (N : ℝ)) (x := ((n + 2 : ℕ) : ℝ)) (y := ((n + 1 : ℕ) : ℝ))
        (by positivity) (by positivity) (by exact_mod_cast hn2) (by exact_mod_cast hn1) hN1
      rw [← hC] at hraw
      have h12 : |((n + 2 : ℕ) : ℝ) - ((n + 1 : ℕ) : ℝ)| = 1 := by
        rw [show ((n + 2 : ℕ) : ℝ) - ((n + 1 : ℕ) : ℝ) = 1 by push_cast; ring, abs_one]
      rwa [h12, mul_one] at hraw
    rw [← hev (n + 2), ← hev (n + 1)]
    calc |Polynomial.eval ((n + 2 : ℕ) : ℝ) W - Polynomial.eval ((n + 1 : ℕ) : ℝ) W|
        ≤ C * (d : ℝ) * (N : ℝ) ^ (d - 1) := hcom
      _ = K * (N : ℝ) ^ (d - 1) := by rw [hK]
  -- the arithmetic input from the hypothesis on `β`
  have hstep1 : 2 * |β| ≤ ((N : ℝ) ^ d)⁻¹ := by
    have h2 := mul_le_mul_of_nonneg_left hβ (show (0 : ℝ) ≤ 2 by norm_num)
    calc 2 * |β| ≤ 2 * ((1 / 2) / (N : ℝ) ^ d) := h2
      _ = ((N : ℝ) ^ d)⁻¹ := by rw [div_eq_mul_inv]; ring
  have hstep2 : 2 * |β| * (N : ℝ) ^ d ≤ 1 := by
    calc 2 * |β| * (N : ℝ) ^ d ≤ ((N : ℝ) ^ d)⁻¹ * (N : ℝ) ^ d :=
          mul_le_mul_of_nonneg_right hstep1 (pow_nonneg hNpos.le d)
      _ = 1 := inv_mul_cancel₀ (ne_of_gt (pow_pos hNpos d))
  have hKpi : 0 ≤ Real.pi * K := mul_nonneg Real.pi_pos.le hKnn
  have hkey3 : 2 * |β| * (N : ℝ) ^ d * Real.pi * K ≤ Real.pi * K := by
    have h1 := mul_le_mul_of_nonneg_right hstep2 hKpi
    calc 2 * |β| * (N : ℝ) ^ d * Real.pi * K
        = (2 * |β| * (N : ℝ) ^ d) * (Real.pi * K) := by ring
      _ ≤ 1 * (Real.pi * K) := h1
      _ = Real.pi * K := one_mul _
  have hpow : (N : ℝ) ^ d = (N : ℝ) ^ (d - 1) * (N : ℝ) := by
    conv_lhs => rw [show d = (d - 1) + 1 from (Nat.sub_add_cancel hd1).symm]
    rw [pow_succ]
  have hfacnn : 0 ≤ 2 * Real.pi * |β| * (K * (N : ℝ) ^ (d - 1)) :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) Real.pi_pos.le) (abs_nonneg β))
      (mul_nonneg hKnn (pow_nonneg hNpos.le _))
  -- pointwise bound for each increment
  have hpt : ∀ n ∈ Finset.range (N - 1),
      ‖Complex.exp (-(2 * Real.pi * Complex.I * (β * (((Q.eval ((n + 2 : ℕ) : ℤ)) : ℤ) : ℝ))))
        - Complex.exp (-(2 * Real.pi * Complex.I * (β * (((Q.eval ((n + 1 : ℕ) : ℤ)) : ℤ) : ℝ))))‖
      ≤ 2 * Real.pi * |β| * (K * (N : ℝ) ^ (d - 1)) := by
    intro n hn
    refine le_trans (norm_exp_neg_two_pi_I_mul_sub_le β
      (((Q.eval ((n + 2 : ℕ) : ℤ)) : ℤ) : ℝ) (((Q.eval ((n + 1 : ℕ) : ℤ)) : ℤ) : ℝ)) ?_
    exact mul_le_mul_of_nonneg_left (hpoly n hn) (by positivity)
  calc ∑ n ∈ Finset.range (N - 1),
        ‖Complex.exp (-(2 * Real.pi * Complex.I * (β * (((Q.eval ((n + 2 : ℕ) : ℤ)) : ℤ) : ℝ))))
          - Complex.exp (-(2 * Real.pi * Complex.I * (β * (((Q.eval ((n + 1 : ℕ) : ℤ)) : ℤ) : ℝ))))‖
      ≤ ∑ _n ∈ Finset.range (N - 1), 2 * Real.pi * |β| * (K * (N : ℝ) ^ (d - 1)) :=
        Finset.sum_le_sum hpt
    _ = ((N - 1 : ℕ) : ℝ) * (2 * Real.pi * |β| * (K * (N : ℝ) ^ (d - 1))) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    _ ≤ ((N : ℕ) : ℝ) * (2 * Real.pi * |β| * (K * (N : ℝ) ^ (d - 1))) := by
        refine mul_le_mul_of_nonneg_right ?_ hfacnn
        exact_mod_cast Nat.sub_le N 1
    _ = 2 * |β| * (N : ℝ) ^ d * Real.pi * K := by rw [hpow]; ring
    _ ≤ Real.pi * K := hkey3

end Work.A3
