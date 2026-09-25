import Mathlib

open Polynomial

namespace Work.NN.Core

/-- Lagrange basis polynomial for the nodes `0, 1, ..., k - 1`: the polynomial taking
the value `1` at the node `i` and `0` at every other node `l < k`. -/
noncomputable def lag (k : ℕ) (i : ℕ) : ℂ[X] :=
  ∏ l ∈ (Finset.range k).erase i,
    Polynomial.C (((i : ℂ) - (l : ℂ))⁻¹) * (Polynomial.X - Polynomial.C (l : ℂ))

/-- The Lagrange basis polynomial evaluates to the Kronecker delta on the nodes. -/
lemma lag_eval {k i j : ℕ} (hj : j ∈ Finset.range k) :
    (lag k i).eval (j : ℂ) = if j = i then 1 else 0 := by
  rw [lag, Polynomial.eval_prod]
  simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_sub, Polynomial.eval_X]
  by_cases h : j = i
  · rw [h, ite_eq_left rfl]
    apply Finset.prod_eq_one
    intro x hx
    rw [Finset.mem_erase] at hx
    have hne : ((i : ℂ) - (x : ℂ)) ≠ 0 := by
      intro hc
      exact hx.1 (Nat.cast_injective (sub_eq_zero.mp hc)).symm
    rw [inv_mul_cancel₀ hne]
  · rw [ite_eq_right h]
    exact Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨h, hj⟩) (by simp)

/-- The Lagrange basis polynomial for `i ∈ range k` has degree at most `k - 1`. -/
lemma natDegree_lag_le {k i : ℕ} (hi : i ∈ Finset.range k) : (lag k i).natDegree ≤ k - 1 := by
  rw [lag]
  have h2 : ∀ l ∈ (Finset.range k).erase i,
      (Polynomial.C (((i : ℂ) - (l : ℂ))⁻¹) *
        (Polynomial.X - Polynomial.C (l : ℂ))).natDegree ≤ 1 := by
    intro l hl
    calc (Polynomial.C (((i : ℂ) - (l : ℂ))⁻¹) *
            (Polynomial.X - Polynomial.C (l : ℂ))).natDegree
        ≤ (Polynomial.X - Polynomial.C (l : ℂ)).natDegree := Polynomial.natDegree_C_mul_le _ _
      _ ≤ 1 := Polynomial.natDegree_X_sub_C_le _
  have h3 : ∑ l ∈ (Finset.range k).erase i,
        (Polynomial.C (((i : ℂ) - (l : ℂ))⁻¹) *
          (Polynomial.X - Polynomial.C (l : ℂ))).natDegree
      ≤ ∑ l ∈ (Finset.range k).erase i, (1:ℕ) := Finset.sum_le_sum h2
  have h4 : ∑ l ∈ (Finset.range k).erase i, (1:ℕ) = k - 1 := by
    rw [Finset.sum_const, Finset.card_erase_of_mem hi, Finset.card_range]
    simp
  calc (∏ l ∈ (Finset.range k).erase i,
        Polynomial.C (((i : ℂ) - (l : ℂ))⁻¹) * (Polynomial.X - Polynomial.C (l : ℂ))).natDegree
      ≤ ∑ l ∈ (Finset.range k).erase i,
          (Polynomial.C (((i : ℂ) - (l : ℂ))⁻¹) *
            (Polynomial.X - Polynomial.C (l : ℂ))).natDegree := Polynomial.natDegree_prod_le _ _
    _ ≤ k - 1 := by rw [← h4]; exact h3

/-- Lagrange interpolation: a polynomial of degree `< k` is determined by its values on
the nodes `0, 1, ..., k - 1`, through the Lagrange basis. -/
lemma lag_interp {k : ℕ} (Q : ℂ[X]) (hQ : Q.natDegree < k) :
    Q = ∑ i ∈ Finset.range k, Polynomial.C (Q.eval (i : ℂ)) * lag k i := by
  refine Polynomial.eq_of_natDegree_lt_card_of_eval_eq _ _
    (f := fun i : Fin k => ((i:ℕ):ℂ)) ?_ ?_ ?_
  · intro a b hab
    exact Fin.ext (Nat.cast_injective hab)
  · intro i
    rw [Polynomial.eval_finsetSum]
    simp only [Polynomial.eval_mul, Polynomial.eval_C]
    rw [Finset.sum_eq_single (i : ℕ)]
    · rw [lag_eval (Finset.mem_range.mpr i.isLt)]; simp
    · intro b hb hbi
      rw [lag_eval (Finset.mem_range.mpr i.isLt)]
      simp [Ne.symm hbi]
    · intro hi; exact absurd (Finset.mem_range.mpr i.isLt) hi
  · rw [Fintype.card_fin]
    refine max_lt hQ ?_
    have hnn : (∑ x ∈ Finset.range k, Polynomial.C (Q.eval (x : ℂ)) * lag k x).natDegree ≤ k - 1 :=
      Polynomial.natDegree_sum_le_of_forall_le (Finset.range k)
        (fun i => Polynomial.C (Q.eval (i : ℂ)) * lag k i)
        (fun i hi => le_trans (Polynomial.natDegree_C_mul_le _ _) (natDegree_lag_le hi))
    omega

/-- The `j`-th derivative at `0` is an explicit linear combination of the values on the
nodes: the coefficients are the derivatives of the Lagrange basis. -/
lemma interp_iterate_derivative {k j : ℕ} (Q : ℂ[X]) (hQ : Q.natDegree < k) :
    (derivative^[j] Q).eval 0 =
      ∑ i ∈ Finset.range k, Q.eval (i : ℂ) * ((derivative^[j] (lag k i)).eval 0) := by
  conv_lhs => rw [lag_interp Q hQ]
  rw [Polynomial.iterate_derivative_sum]
  simp only [Polynomial.iterate_derivative_C_mul]
  rw [Polynomial.eval_finsetSum]
  simp only [Polynomial.eval_mul, Polynomial.eval_C]

/-- The `h = 1` version of the interpolation bound. -/
theorem interp_bound_aux {k j : ℕ} (_hjk : j < k) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ Q : ℂ[X], Q.degree < k →
      ‖(derivative^[j] Q).eval 0‖ ≤ C * ∑ i ∈ Finset.range k, ‖Q.eval (i:ℂ)‖ := by
  classical
  refine ⟨∑ i ∈ Finset.range k, ‖(derivative^[j] (lag k i)).eval 0‖,
    Finset.sum_nonneg (fun _ _ => norm_nonneg _), ?_⟩
  intro Q hQ
  by_cases hQ0 : Q = 0
  · rw [hQ0]; simp
  · have hQn : Q.natDegree < k := (Polynomial.natDegree_lt_iff_degree_lt hQ0).mpr hQ
    have hloc : ∀ i ∈ Finset.range k,
        ‖Q.eval ((i:ℕ):ℂ)‖ ≤ ∑ l ∈ Finset.range k, ‖Q.eval ((l:ℕ):ℂ)‖ := by
      intro i hi
      exact Finset.single_le_sum (s := Finset.range k)
        (f := fun l : ℕ => ‖Q.eval ((l:ℂ))‖) (fun l _ => norm_nonneg _) hi
    rw [interp_iterate_derivative Q hQn]
    calc ‖∑ i ∈ Finset.range k, Q.eval (i:ℂ) * (derivative^[j] (lag k i)).eval 0‖
        ≤ ∑ i ∈ Finset.range k, ‖Q.eval (i:ℂ) * (derivative^[j] (lag k i)).eval 0‖ :=
          norm_sum_le _ _
      _ = ∑ i ∈ Finset.range k, ‖Q.eval (i:ℂ)‖ * ‖(derivative^[j] (lag k i)).eval 0‖ := by simp
      _ ≤ ∑ i ∈ Finset.range k,
            (∑ l ∈ Finset.range k, ‖Q.eval (l:ℂ)‖) * ‖(derivative^[j] (lag k i)).eval 0‖ := by
        apply Finset.sum_le_sum
        intro i hi
        exact mul_le_mul_of_nonneg_right (hloc i hi) (norm_nonneg _)
      _ = (∑ l ∈ Finset.range k, ‖Q.eval (l:ℂ)‖) *
            ∑ i ∈ Finset.range k, ‖(derivative^[j] (lag k i)).eval 0‖ := by
        rw [Finset.mul_sum]
      _ = (∑ i ∈ Finset.range k, ‖(derivative^[j] (lag k i)).eval 0‖) *
            ∑ l ∈ Finset.range k, ‖Q.eval (l:ℂ)‖ := by
        rw [mul_comm]

/-- Substituting `X ↦ a * X` commutes with differentiation and scales the `j`-th
derivative by `a ^ j`. -/
lemma iterate_derivative_comp_C_mul_X (p : ℂ[X]) (a : ℂ) (j : ℕ) :
    derivative^[j] (p.comp (Polynomial.C a * Polynomial.X)) =
      (derivative^[j] p).comp (Polynomial.C a * Polynomial.X) * Polynomial.C (a ^ j) := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [Function.iterate_succ_apply', ih]
    rw [Polynomial.derivative_mul, Polynomial.derivative_C, mul_zero, add_zero]
    rw [Polynomial.derivative_comp, Polynomial.derivative_C_mul_X]
    conv_rhs => rw [Function.iterate_succ_apply']
    rw [pow_succ, Polynomial.C_mul]
    ring

/-- The evaluation at `0` of the preceding identity. -/
lemma eval_zero_iterate_derivative_comp_C_mul_X (p : ℂ[X]) (a : ℂ) (j : ℕ) :
    (derivative^[j] (p.comp (Polynomial.C a * Polynomial.X))).eval 0 =
      (derivative^[j] p).eval 0 * a ^ j := by
  rw [iterate_derivative_comp_C_mul_X]
  simp [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_comp, Polynomial.eval_X]

/--
**Polynomial interpolation bound.**  For polynomials of degree `< k`, the absolute value
of the `j`-th derivative at the origin (`j < k`) is controlled by the values at the
equally spaced points `0, h, 2h, ..., (k-1)h`, with a constant depending only on `k`
and `j`.  This is a finite dimensional (Lagrange interpolation) estimate, at the heart
of the Newlander–Nirenberg iteration.
-/
theorem poly_interp_bound {k j : ℕ} (hjk : j < k) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (P : Polynomial ℂ) (h : ℝ), 0 < h → P.degree < k →
        ‖(Polynomial.derivative^[j] P).eval 0‖ ≤
          C * (∑ i ∈ Finset.range k, ‖P.eval (((i : ℝ) * h : ℝ) : ℂ)‖) / h ^ j := by
  obtain ⟨C, hC0, hC⟩ := interp_bound_aux hjk
  refine ⟨C, hC0, ?_⟩
  intro P h hpos hPdeg
  set a : ℂ := (h : ℂ) with ha
  set Q : ℂ[X] := P.comp (Polynomial.C a * Polynomial.X) with hQ
  have ha0 : a ≠ 0 := by rw [ha]; exact Complex.ofReal_ne_zero.mpr (ne_of_gt hpos)
  have hqa : (Polynomial.C a * Polynomial.X).degree = (1 : WithBot ℕ) := by
    rw [Polynomial.degree_C_mul ha0, Polynomial.degree_X]
  have hQdeg : Q.degree < (k : WithBot ℕ) := by
    rw [hQ, Polynomial.degree_comp (by rw [hqa]; decide), hqa, mul_one]
    exact hPdeg
  have hbd := hC Q hQdeg
  have heval : ∀ i : ℕ, Q.eval ((i:ℂ)) = P.eval ((((i:ℝ)*h : ℝ) : ℂ)) := by
    intro i
    rw [hQ, Polynomial.eval_comp]
    simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X, ha]
    congr 1
    push_cast
    ring
  have hderiv : (derivative^[j] Q).eval 0 = (derivative^[j] P).eval 0 * (h:ℂ)^j := by
    rw [hQ, eval_zero_iterate_derivative_comp_C_mul_X, ha]
  have hnorm : ‖(derivative^[j] Q).eval 0‖ = ‖(derivative^[j] P).eval 0‖ * h^j := by
    have hh : ‖(h:ℂ)‖ = h := by rw [show ‖(h:ℂ)‖ = |h| from by simp, abs_of_pos hpos]
    rw [hderiv, norm_mul, norm_pow, hh]
  have hS : (∑ i ∈ Finset.range k, ‖Q.eval (i:ℂ)‖) =
      ∑ i ∈ Finset.range k, ‖P.eval (((i:ℝ)*h:ℝ):ℂ)‖ := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [heval i]
  rw [hS] at hbd
  have hd : 0 < h ^ j := pow_pos hpos j
  have hstep : ‖(derivative^[j] P).eval 0‖ * h^j ≤
      C * (∑ i ∈ Finset.range k, ‖P.eval (((i:ℝ)*h:ℝ):ℂ)‖) := by
    rw [← hnorm]; exact hbd
  calc ‖(derivative^[j] P).eval 0‖
      = ‖(derivative^[j] P).eval 0‖ * h^j * (h^j)⁻¹ := by
        rw [mul_assoc, mul_inv_cancel₀ (ne_of_gt hd), mul_one]
    _ ≤ (C * (∑ i ∈ Finset.range k, ‖P.eval (((i:ℝ)*h:ℝ):ℂ)‖)) * (h^j)⁻¹ :=
          mul_le_mul_of_nonneg_right hstep (inv_nonneg.mpr hd.le)
    _ = C * (∑ i ∈ Finset.range k, ‖P.eval (((i:ℝ)*h:ℝ):ℂ)‖) / h^j := by rw [div_eq_mul_inv]

end Work.NN.Core
