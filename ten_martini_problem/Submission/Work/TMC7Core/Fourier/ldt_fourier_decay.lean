import Mathlib
import Submission.Work.TMC7Core.Fourier.poly_of_frobSq
import Submission.Work.TMC7Core.Fourier.log_root_aux
import Submission.Work.TMC7Core.Fourier.log_root_fourier
import Submission.Work.TMC7Core.Cocycle
import Submission.Work.TMC7Core.Cocycle.frob_sqrt_two_le_of_det_one

/-!
# Fourier decay of the finite-scale Lyapunov exponent `u_N`

`uAvg α lam E N x = (1/N) log ‖A_N(x)‖_F`, where `A_N` is the `N`-th iterate of the
almost Mathieu transfer cocycle (a product of `N` matrices of determinant one).
The finite-scale exponent has Fourier coefficients decaying like `1/|k|`
(Bourgain–Goldstein (2.3), used in the proof of the large deviation theorem):

`‖∫₀¹ u_N(x) e^{-2πikx} dx‖ ≤ 1/|k|` for `k ≠ 0`, `N ≥ 1`.

The proof assembles the following pieces.

* `poly_of_frobSq` provides a polynomial `Q ∈ ℂ[X]` of degree `≤ 4N` with
  `‖Q(e^{2πix})‖ = frobSq α lam E N x = ‖A_N(x)‖_F²` for all `x`.
  Hence `u_N(x) = log‖Q(e^{2πix})‖ / (2N)`.
* `log_root_fourier` bounds the `k`-th Fourier coefficient of `log‖e^{2πix} − a‖`
  by `1/(2|k|)` as soon as `‖a‖ ≠ 1` (the classical single-root estimate).
* `poly_log_fourier` (below) sums this over the roots of `Q` (factoring `Q` one
  linear factor at a time), which bounds the `k`-th Fourier coefficient of
  `log‖Q(e^{2πix})‖` by `natDegree Q/(2|k|) ≤ 2N/|k|`.
* Dividing by `2N` yields `1/|k|`.
-/

open MeasureTheory Filter Topology Set Polynomial
open scoped Interval

namespace Work.TMC7Core.Fourier

noncomputable section

/-- `e^{2πix}`. -/
private abbrev ee (x : ℝ) : ℂ := Complex.exp (2 * Real.pi * Complex.I * x)

/-- `e^{-2πikx}`, the Fourier kernel. -/
private abbrev ww (k : ℤ) (x : ℝ) : ℂ := Complex.exp (-(2 * Real.pi * Complex.I * (k : ℝ) * x))

/-- The `k`-th Fourier coefficient of the kernel vanishes for `k ≠ 0`. -/
private lemma integral_ww_zero (k : ℤ) (hk : k ≠ 0) : ∫ x in (0:ℝ)..1, ww k x = 0 := by
  have hfun : ∀ x : ℝ, ww k x
      = Complex.exp (2 * Real.pi * Complex.I * ((-k : ℤ) : ℝ) * x) := by
    intro x; rw [ww]; congr 1; push_cast; ring
  rw [show (∫ x in (0:ℝ)..1, ww k x)
      = ∫ x in (0:ℝ)..1, Complex.exp (2 * Real.pi * Complex.I * ((-k : ℤ) : ℝ) * x) from
        intervalIntegral.integral_congr (fun x _ => hfun x)]
  rw [integral_exp_two_pi_I_int (-k), if_neg]
  intro h
  exact hk (neg_eq_zero.mp h)

/-- **Polynomial Fourier bound.**  For a polynomial `Q` with no zeros on the unit circle, the
`k`-th Fourier coefficient of `log‖Q(e^{2πix})‖` is at most `natDegree Q/(2|k|)`.

Obtained by peeling off one root at a time (`Q = (X − a) Q₁`), where the contribution of the
factor `X − a` is bounded by `log_root_fourier` and that of `Q₁` by the induction
hypothesis; the split of `log` over the product uses that neither factor vanishes on
the unit circle. -/
private theorem poly_log_fourier (Q : Polynomial ℂ)
    (hnz : ∀ x : ℝ, Polynomial.eval (ee x) Q ≠ 0) (k : ℤ) (hk : k ≠ 0) :
    ‖∫ x in (0:ℝ)..1, ((Real.log ‖Polynomial.eval (ee x) Q‖ : ℝ) : ℂ) * ww k x‖
      ≤ (Q.natDegree : ℝ)/(2*|(k:ℝ)|) := by
  have hconst : ∀ (Q : Polynomial ℂ), Q.natDegree = 0 →
      (∀ x : ℝ, Polynomial.eval (ee x) Q ≠ 0) →
      ‖∫ x in (0:ℝ)..1, ((Real.log ‖Polynomial.eval (ee x) Q‖ : ℝ) : ℂ) * ww k x‖
        ≤ (Q.natDegree : ℝ)/(2*|(k:ℝ)|) := by
    intro Q hQ0 _
    rw [hQ0, Nat.cast_zero, zero_div]
    have hC : Q = Polynomial.C (Q.coeff 0) := Polynomial.eq_C_of_natDegree_eq_zero hQ0
    have hfun : (fun x : ℝ => ((Real.log ‖Polynomial.eval (ee x) Q‖ : ℝ) : ℂ) * ww k x)
        = fun x : ℝ => ((Real.log ‖Q.coeff 0‖ : ℝ) : ℂ) * ww k x := by
      funext x; rw [hC]; simp
    rw [hfun, intervalIntegral.integral_const_mul, integral_ww_zero k hk, mul_zero, norm_zero]
  suffices aux : ∀ d : ℕ, ∀ Q : Polynomial ℂ, Q.natDegree ≤ d →
      (∀ x : ℝ, Polynomial.eval (ee x) Q ≠ 0) →
      ‖∫ x in (0:ℝ)..1, ((Real.log ‖Polynomial.eval (ee x) Q‖ : ℝ) : ℂ) * ww k x‖
        ≤ (Q.natDegree : ℝ)/(2*|(k:ℝ)|) by
    exact aux Q.natDegree Q le_rfl hnz
  intro d
  induction d with
  | zero => intro Q hd hnz; exact hconst Q (Nat.le_zero.mp hd) hnz
  | succ d ih =>
    intro Q hd hnz
    by_cases h0 : Q.natDegree = 0
    · exact hconst Q h0 hnz
    · have hQne : Q ≠ 0 := by intro h; exact hnz 0 (by rw [h]; simp)
      have hnatpos : 0 < Q.natDegree := Nat.pos_of_ne_zero h0
      have hdegpos : 0 < Q.degree := by
        rw [Polynomial.degree_eq_natDegree hQne]; exact_mod_cast hnatpos
      obtain ⟨a, ha⟩ := Complex.exists_root hdegpos
      have hdvd : (Polynomial.X - Polynomial.C a) ∣ Q := Polynomial.dvd_iff_isRoot.mpr ha
      obtain ⟨Q1, hQ1⟩ := hdvd
      have hQ1ne : Q1 ≠ 0 := by intro h; exact hQne (by rw [hQ1, h, mul_zero])
      have hmul : Q.natDegree = 1 + Q1.natDegree := by
        have h := (Polynomial.monic_X_sub_C a).natDegree_mul' hQ1ne
        rw [hQ1, h, Polynomial.natDegree_X_sub_C]
      have hnatQ1 : Q1.natDegree ≤ d := by omega
      have hnz1 : ∀ x : ℝ, Polynomial.eval (ee x) Q1 ≠ 0 := by
        intro x h
        have hx := hnz x
        rw [hQ1] at hx
        simp only [Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_X,
          Polynomial.eval_C] at hx
        rw [h, mul_zero] at hx
        exact hx rfl
      have hA_ne : ∀ x : ℝ, ee x - a ≠ 0 := by
        intro x h; exact hnz x (by rw [hQ1]; simp [h])
      have ha_ne : ‖a‖ ≠ 1 := by
        intro hnorm
        obtain ⟨θ, hθ⟩ := (Complex.norm_eq_one_iff a).mp hnorm
        have h3 : 2 * (Real.pi : ℂ) * Complex.I * ((θ/(2*Real.pi) : ℝ) : ℂ)
            = (θ : ℂ) * Complex.I := by
          push_cast; field_simp
        have hee : ee (θ/(2*Real.pi)) = a := by rw [ee, h3, hθ]
        exact hnz (θ/(2*Real.pi)) (by rw [hee]; exact ha)
      have hlogpt : ∀ x : ℝ, Real.log ‖Polynomial.eval (ee x) Q‖
          = Real.log ‖ee x - a‖ + Real.log ‖Polynomial.eval (ee x) Q1‖ := by
        intro x
        rw [hQ1]
        simp only [Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_X,
          Polynomial.eval_C]
        rw [norm_mul, Real.log_mul (norm_ne_zero_iff.mpr (hA_ne x)) (norm_ne_zero_iff.mpr (hnz1 x))]
      have hcont1 : Continuous (fun x : ℝ => ((Real.log ‖ee x - a‖ : ℝ) : ℂ) * ww k x) := by
        have hc : Continuous (fun x : ℝ => Real.log ‖ee x - a‖) :=
          (continuous_norm.comp (by fun_prop : Continuous (fun x : ℝ => ee x - a))).log
            (fun x => norm_ne_zero_iff.mpr (hA_ne x))
        exact (Complex.continuous_ofReal.comp hc).mul (by fun_prop)
      have hcont2 : Continuous (fun x : ℝ => ((Real.log ‖Polynomial.eval (ee x) Q1‖ : ℝ) : ℂ) * ww k x) := by
        have hc : Continuous (fun x : ℝ => Real.log ‖Polynomial.eval (ee x) Q1‖) :=
          (continuous_norm.comp (by fun_prop : Continuous (fun x : ℝ => Polynomial.eval (ee x) Q1))).log
            (fun x => norm_ne_zero_iff.mpr (hnz1 x))
        exact (Complex.continuous_ofReal.comp hc).mul (by fun_prop)
      have hIntEq : (∫ x in (0:ℝ)..1, ((Real.log ‖Polynomial.eval (ee x) Q‖ : ℝ) : ℂ) * ww k x)
          = (∫ x in (0:ℝ)..1, ((Real.log ‖ee x - a‖ : ℝ) : ℂ) * ww k x)
            + (∫ x in (0:ℝ)..1, ((Real.log ‖Polynomial.eval (ee x) Q1‖ : ℝ) : ℂ) * ww k x) := by
        rw [← intervalIntegral.integral_add (hcont1.intervalIntegrable 0 1) (hcont2.intervalIntegrable 0 1)]
        apply intervalIntegral.integral_congr
        intro x _
        dsimp only
        rw [hlogpt x]
        push_cast
        ring
      calc ‖∫ x in (0:ℝ)..1, ((Real.log ‖Polynomial.eval (ee x) Q‖ : ℝ) : ℂ) * ww k x‖
          = ‖(∫ x in (0:ℝ)..1, ((Real.log ‖ee x - a‖ : ℝ) : ℂ) * ww k x)
              + (∫ x in (0:ℝ)..1, ((Real.log ‖Polynomial.eval (ee x) Q1‖ : ℝ) : ℂ) * ww k x)‖ := by
            rw [hIntEq]
        _ ≤ ‖∫ x in (0:ℝ)..1, ((Real.log ‖ee x - a‖ : ℝ) : ℂ) * ww k x‖
              + ‖∫ x in (0:ℝ)..1, ((Real.log ‖Polynomial.eval (ee x) Q1‖ : ℝ) : ℂ) * ww k x‖ :=
            norm_add_le _ _
        _ ≤ 1/(2*|(k:ℝ)|) + (Q1.natDegree : ℝ)/(2*|(k:ℝ)|) :=
            add_le_add (by simpa only [ee, ww] using log_root_fourier a ha_ne k hk)
              (ih Q1 hnatQ1 hnz1)
        _ = (Q.natDegree : ℝ)/(2*|(k:ℝ)|) := by rw [hmul]; push_cast; rw [add_div]

/-- `uAvg` is `log frobSq / (2N)`: the two finite-scale exponents coincide. -/
theorem uAvg_eq_log_frobSq (α lam : ℝ) (E : ℂ) (N : ℕ) (x : ℝ) :
    uAvg α lam E N x = Real.log (Work.TMC7Core.frobSq α lam E N x) / (2 * (N : ℝ)) := by
  rw [uAvg, Work.TMC7Core.frobSq, Real.log_pow]
  ring

/-- **Fourier decay of the finite-scale Lyapunov exponent** (Bourgain–Goldstein (2.3)). -/
theorem ldt_fourier_decay (α lam : ℝ) (E : ℝ) (N : ℕ) (hN : 1 ≤ N) (k : ℤ) (hk : k ≠ 0) :
    ‖∫ x in (0 : ℝ)..1, ((uAvg α lam (E : ℂ) N x : ℝ) : ℂ) *
      Complex.exp (-(2 * Real.pi * Complex.I * (k : ℝ) * x))‖ ≤ 1 / |(k : ℝ)| := by
  obtain ⟨Q, hdeg, hev⟩ := poly_of_frobSq α lam (E : ℂ) N
  have hpos : ∀ x, 0 < frobSq α lam (E:ℂ) N x := by
    intro x
    have h2 : Real.sqrt 2 ≤ frob (iterC α lam (E:ℂ) N x) :=
      Work.TMC7Core.Cocycle.frob_sqrt_two_le_of_det_one (det_iterC α lam (E:ℂ) N x)
    have h2' : (2:ℝ) ≤ frobSq α lam (E:ℂ) N x := by
      have hsq : (Real.sqrt 2)^2 ≤ (frob (iterC α lam (E:ℂ) N x))^2 :=
        pow_le_pow_left₀ (Real.sqrt_nonneg 2) h2 2
      rw [Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num)] at hsq
      simpa [frobSq] using hsq
    linarith
  have hlog : ∀ x, Real.log (frobSq α lam (E:ℂ) N x) = Real.log ‖Polynomial.eval (ee x) Q‖ := by
    intro x; rw [← hev x]
  have hQnz : ∀ x : ℝ, Polynomial.eval (ee x) Q ≠ 0 := by
    intro x h
    have h1 := hev x
    rw [h, norm_zero] at h1
    have := hpos x
    linarith
  have hfun : (fun x : ℝ => ((uAvg α lam (E:ℂ) N x : ℝ) : ℂ) *
        Complex.exp (-(2 * Real.pi * Complex.I * (k:ℝ) * x)))
      = fun x : ℝ => (((2 * (N:ℝ) : ℝ) : ℂ))⁻¹ *
          (((Real.log ‖Polynomial.eval (ee x) Q‖ : ℝ) : ℂ) *
            Complex.exp (-(2 * Real.pi * Complex.I * (k:ℝ) * x))) := by
    funext x
    rw [uAvg_eq_log_frobSq, hlog x]
    push_cast
    ring
  have hI : (∫ x in (0:ℝ)..1, ((uAvg α lam (E:ℂ) N x : ℝ) : ℂ) *
        Complex.exp (-(2 * Real.pi * Complex.I * (k:ℝ) * x)))
      = (((2 * (N:ℝ) : ℝ) : ℂ))⁻¹ *
        (∫ x in (0:ℝ)..1, ((Real.log ‖Polynomial.eval (ee x) Q‖ : ℝ) : ℂ) *
          Complex.exp (-(2 * Real.pi * Complex.I * (k:ℝ) * x))) := by
    rw [hfun, intervalIntegral.integral_const_mul]
  rw [hI, norm_mul]
  have h1 : ‖((((2 * (N:ℝ) : ℝ)) : ℂ))⁻¹‖ = 1/(2*(N:ℝ)) := by
    rw [norm_inv, Complex.norm_real, Real.norm_of_nonneg (by positivity : (0:ℝ) ≤ 2*(N:ℝ)), one_div]
  rw [h1]
  have h2 : ‖∫ x in (0:ℝ)..1, ((Real.log ‖Polynomial.eval (ee x) Q‖ : ℝ) : ℂ) *
        Complex.exp (-(2 * Real.pi * Complex.I * (k:ℝ) * x))‖
      ≤ (Q.natDegree : ℝ)/(2*|(k:ℝ)|) := by
    simpa only [ee, ww] using poly_log_fourier Q hQnz k hk
  have h3 : (0:ℝ) ≤ 1/(2*(N:ℝ)) := by positivity
  calc (1/(2*(N:ℝ))) *
          ‖∫ x in (0:ℝ)..1, ((Real.log ‖Polynomial.eval (ee x) Q‖ : ℝ) : ℂ) *
            Complex.exp (-(2 * Real.pi * Complex.I * (k:ℝ) * x))‖
      ≤ (1/(2*(N:ℝ))) * ((Q.natDegree:ℝ)/(2*|(k:ℝ)|)) := mul_le_mul_of_nonneg_left h2 h3
    _ ≤ (1/(2*(N:ℝ))) * ((4*N:ℝ)/(2*|(k:ℝ)|)) := by
        gcongr
        exact_mod_cast hdeg
    _ = 1/|(k:ℝ)| := by
        have hk0 : ((k:ℝ)) ≠ 0 := by exact_mod_cast hk
        have hkabs : |(k:ℝ)| ≠ 0 := abs_ne_zero.mpr hk0
        have hN0 : (N:ℝ) ≠ 0 := by
          have : (1:ℝ) ≤ (N:ℝ) := by exact_mod_cast hN
          linarith
        field_simp
        ring

end

end Work.TMC7Core.Fourier
