import Mathlib
import Submission.Work.BourgainPlan.Maximal.poly_block_core_defs
import Submission.Work.BourgainPlan.Maximal.poly_commons_import

/-!
# Sharp van der Corput decay of the polynomial oscillatory profile

The oscillatory profile of the integer polynomial `P` at scale `N` is
`polyProfile P N β = ∫_0^1 e(β P(N s)) ds`.  For `d = P.natDegree ≥ 2` it decays like
`(|β| N^d)^{-1/d}` once `|β| N^d ≥ 1`.

This is the classical van der Corput estimate for the oscillatory integral
`∫_0^1 e^{2πi β P(N s)} ds`, whose phase `s ↦ 2π β P(N s)` has constant `d`-th derivative
`2π β d! (lead P) N^d`: `|∫| ≤ C (2π |β| d! |lead P| N^d)^{-1/d}`.  We rewrite this as the stated
bound in terms of `polyDil P k = (2^k)^d`.

The main analytic input is `Commons.Analysis.Oscillatory.van_der_corput_bound`; the algebraic part
is the computation of the `d`-th derivative of `s ↦ Q.eval (N * s)` for `Q = toRealPoly P`
(`iteratedDeriv_comp_eval`).
-/

open MeasureTheory
open scoped BigOperators
open Commons.Analysis.ExponentialSums

set_option autoImplicit false

namespace Work.BourgainPlan.Maximal

/-! ## The `n`-th derivative of a polynomial function -/

/-- The `n`-th iterated derivative of the polynomial function `t ↦ Q.eval t` is the evaluation of
the `n`-th *algebraic* iterated derivative. -/
lemma iteratedDeriv_eval (Q : Polynomial ℝ) (n : ℕ) :
    iteratedDeriv n (fun t : ℝ => Q.eval t) = fun t => ((Polynomial.derivative^[n]) Q).eval t := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [iteratedDeriv_succ, ih]
    funext t
    rw [Polynomial.deriv]
    rw [Function.iterate_succ_apply']

/-- The `natDegree`-th algebraic derivative of a polynomial is the constant `d! · lead`. -/
lemma iterate_derivative_natDegree_eq_C (Q : Polynomial ℝ) :
    (Polynomial.derivative^[Q.natDegree]) Q
      = Polynomial.C ((Q.natDegree.factorial : ℝ) * Q.leadingCoeff) := by
  have hdeg : ((Polynomial.derivative^[Q.natDegree]) Q).natDegree ≤ 0 := by
    have := Polynomial.natDegree_iterate_derivative Q Q.natDegree
    simpa using this
  rw [Polynomial.eq_C_of_natDegree_le_zero hdeg]
  congr 1
  rw [Polynomial.coeff_iterate_derivative]
  simp only [zero_add, Nat.descFactorial_self]
  rw [Polynomial.coeff_natDegree]
  simp

/-- The degree of `Q.comp (C N * X)` (the dilation of `Q` by `N ≠ 0`). -/
lemma comp_C_mul_X_natDegree (Q : Polynomial ℝ) {N : ℝ} (hN : N ≠ 0) :
    (Q.comp (Polynomial.C N * Polynomial.X)).natDegree = Q.natDegree := by
  rw [Polynomial.natDegree_comp, Polynomial.natDegree_C_mul_X N hN, mul_one]

/-- The leading coefficient of `Q.comp (C N * X)` is `lead Q · N^{natDegree Q}`. -/
lemma comp_C_mul_X_leadingCoeff (Q : Polynomial ℝ) {N : ℝ} (hN : N ≠ 0) :
    (Q.comp (Polynomial.C N * Polynomial.X)).leadingCoeff
      = Q.leadingCoeff * N ^ Q.natDegree := by
  rw [Polynomial.leadingCoeff_comp (q := Polynomial.C N * Polynomial.X)
      (by rw [Polynomial.natDegree_C_mul_X N hN]; norm_num), Polynomial.leadingCoeff_C_mul_X]

/-- **The `d`-th derivative of the dilated polynomial.**  For `Q : ℝ[X]` with `d = Q.natDegree`
and `N ≠ 0`, the `d`-th iterated derivative of `s ↦ Q.eval (N * s)` is the constant
`d! · lead Q · N^d`. -/
lemma iteratedDeriv_comp_eval (Q : Polynomial ℝ) {N : ℝ} (hN : N ≠ 0) (t : ℝ) :
    iteratedDeriv Q.natDegree (fun s : ℝ => Q.eval (N * s)) t
      = (Q.natDegree.factorial : ℝ) * Q.leadingCoeff * N ^ Q.natDegree := by
  have hdeg : (Q.comp (Polynomial.C N * Polynomial.X)).natDegree = Q.natDegree :=
    comp_C_mul_X_natDegree Q hN
  have hfun : (fun s : ℝ => Q.eval (N * s))
      = fun s => (Q.comp (Polynomial.C N * Polynomial.X)).eval s := by
    funext s
    rw [Polynomial.eval_comp, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]
  have key : iteratedDeriv (Q.comp (Polynomial.C N * Polynomial.X)).natDegree
        (fun s : ℝ => (Q.comp (Polynomial.C N * Polynomial.X)).eval s) t
      = ((Q.comp (Polynomial.C N * Polynomial.X)).natDegree.factorial : ℝ)
          * (Q.comp (Polynomial.C N * Polynomial.X)).leadingCoeff := by
    rw [iteratedDeriv_eval, iterate_derivative_natDegree_eq_C]
    simp only [Polynomial.eval_C]
  rw [hfun]
  conv_lhs => rw [← hdeg]
  rw [key, hdeg, comp_C_mul_X_leadingCoeff Q hN]
  ring

/-- Distribution of the real `rpow` over a product: `C / (A x)^e = (C / A^e) · x^{-e}`. -/
lemma div_rpow_mul_eq (C₁ A x e : ℝ) (hA : 0 < A) (hx : 0 ≤ x) :
    C₁ / (A * x) ^ e = (C₁ / A ^ e) * x ^ (-e) := by
  rw [Real.mul_rpow hA.le hx, Real.rpow_neg hx, div_eq_mul_inv, div_eq_mul_inv, mul_inv]
  ring

/-! ## The decay of the profile -/

theorem polyProfile_decay_sharp (P : Polynomial ℤ) (hd : 2 ≤ P.natDegree) :
    ∃ C : ℝ, 0 < C ∧ ∀ β : ℝ, β ≠ 0 → ∀ k : ℕ, 1 ≤ |β| * polyDil P k →
      ‖polyProfile P (2 ^ k) β‖
        ≤ C * (|β| * polyDil P k) ^ (-(1 / (P.natDegree : ℝ))) := by
  obtain ⟨C₁, hC₁pos, hC₁⟩ := Commons.Analysis.Oscillatory.van_der_corput_bound P.natDegree hd
  set Q : Polynomial ℝ := toRealPoly P with hQdef
  have hQdeg : Q.natDegree = P.natDegree := by
    rw [hQdef, toRealPoly]
    exact Polynomial.natDegree_map_eq_of_injective Int.cast_injective P
  have hQlc : Q.leadingCoeff = (P.leadingCoeff : ℝ) := by
    rw [hQdef, toRealPoly]
    exact Polynomial.leadingCoeff_map_of_injective Int.cast_injective P
  have hPne : P ≠ 0 := by intro h; rw [h] at hd; simp at hd
  have hlc_ne : Q.leadingCoeff ≠ 0 := by
    rw [hQlc]
    exact_mod_cast (Polynomial.leadingCoeff_ne_zero.mpr hPne)
  set A : ℝ := 2 * Real.pi * (P.natDegree.factorial : ℝ) * |Q.leadingCoeff| with hAdef
  have hApos : 0 < A := by
    rw [hAdef]
    have := abs_pos.mpr hlc_ne
    positivity
  refine ⟨C₁ / A ^ ((1 : ℝ) / (P.natDegree : ℝ)), ?_, ?_⟩
  · exact div_pos hC₁pos (Real.rpow_pos_of_pos hApos _)
  · intro β hβ k hk
    set N : ℝ := (2 : ℝ) ^ k with hNdef
    have hNpos : 0 < N := by rw [hNdef]; positivity
    have hNne : N ≠ 0 := ne_of_gt hNpos
    have hpDil : polyDil P k = N ^ P.natDegree := by
      rw [polyDil, powDil, hNdef]
    have hβpos : 0 < |β| := abs_pos.mpr hβ
    have hXpos : 0 < |β| * polyDil P k := by
      rw [hpDil]
      exact mul_pos hβpos (pow_pos hNpos _)
    set φ : ℝ → ℝ := fun s => 2 * Real.pi * (β * Q.eval (N * s)) with hφdef
    have hφcd : ContDiffOn ℝ P.natDegree φ (Set.Icc 0 1) := by
      apply ContDiff.contDiffOn
      rw [hφdef]
      exact contDiff_const.mul (contDiff_const.mul
        ((Polynomial.contDiff_aeval (R := ℝ) (𝕜 := ℝ) Q (P.natDegree : WithTop ℕ∞)).comp
          (contDiff_const.mul contDiff_id)))
    have hderiv : ∀ t ∈ Set.Icc (0 : ℝ) 1,
        A * (|β| * polyDil P k) ≤ |iteratedDeriv P.natDegree φ t| := by
      intro t _ht
      have hcomp := iteratedDeriv_comp_eval Q hNne t
      rw [hQdeg] at hcomp
      have hval : iteratedDeriv P.natDegree φ t
          = 2 * Real.pi * β
              * ((P.natDegree.factorial : ℝ) * Q.leadingCoeff * N ^ P.natDegree) := by
        rw [hφdef, iteratedDeriv_const_mul_field, iteratedDeriv_const_mul_field, hcomp]
        ring
      rw [hval, hpDil]
      have hfac : (0 : ℝ) < (P.natDegree.factorial : ℝ) := by
        exact_mod_cast Nat.factorial_pos _
      have hNpow : (0 : ℝ) < N ^ P.natDegree := pow_pos hNpos _
      simp only [abs_mul]
      rw [abs_of_pos (by norm_num : (0 : ℝ) < 2), abs_of_pos Real.pi_pos, abs_of_pos hfac,
        abs_of_pos hNpow]
      rw [hAdef]
      exact le_of_eq (by ring)
    have hvc := hC₁ (a := 0) (b := 1) zero_le_one (φ := φ)
      (lam := A * (|β| * polyDil P k)) (by positivity) hφcd hderiv
    have hprof : polyProfile P (2 ^ k) β
        = ∫ s in (0 : ℝ)..1, Complex.exp (Complex.I * (φ s : ℂ)) := by
      unfold polyProfile
      apply intervalIntegral.integral_congr
      intro s _
      rw [hφdef]
      rw [← hQdef, hNdef]
      push_cast
      ring_nf
    rw [hprof]
    refine le_trans hvc (le_of_eq ?_)
    rw [div_rpow_mul_eq C₁ A (|β| * polyDil P k) ((1 : ℝ) / (P.natDegree : ℝ)) hApos hXpos.le]

end Work.BourgainPlan.Maximal
