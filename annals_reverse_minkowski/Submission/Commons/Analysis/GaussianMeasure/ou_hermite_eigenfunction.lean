import Mathlib
import Submission.Commons.Analysis.GaussianMeasure.hermite_derivative
import Submission.Commons.Analysis.GaussianMeasure.ou_semigroup_contDiff_bounded
import Submission.Commons.Analysis.GaussianMeasure.gaussian_integration_by_parts

open MeasureTheory Polynomial
open scoped Real

namespace Commons.Analysis.GaussianMeasure

noncomputable section

/-! ## Change of variables for a shifted/scaled Gaussian -/

/-- Integrating `F` against the Ornstein–Uhlenbeck kernel
`y ↦ (2π s²)^{-1/2} exp (-(y-a)²/(2s²))` (the density of `a + s·Z`, `Z` standard Gaussian)
equals integrating `u ↦ F (a + s·u)` against the standard Gaussian density. -/
theorem gauss_shift_scale_integral (a s : ℝ) (hs : 0 < s) (F : ℝ → ℝ) :
    (∫ y : ℝ, (1 / Real.sqrt (2 * Real.pi * s ^ 2))
        * Real.exp (-((y - a) ^ 2) / (2 * s ^ 2)) * F y)
      = (1 / Real.sqrt (2 * Real.pi))
        * ∫ u : ℝ, Real.exp (-(u ^ 2 / 2)) * F (a + s * u) := by
  have hnorm : Real.sqrt (2 * Real.pi * s ^ 2) = Real.sqrt (2 * Real.pi) * s := by
    rw [Real.sqrt_mul (by positivity)]
    rw [Real.sqrt_sq hs.le]
  have hcore : (∫ y : ℝ, Real.exp (-((y - a) ^ 2) / (2 * s ^ 2)) * F y)
      = s * ∫ u : ℝ, Real.exp (-(u ^ 2 / 2)) * F (a + s * u) := by
    have htrans : (∫ y : ℝ, Real.exp (-((y - a) ^ 2) / (2 * s ^ 2)) * F y)
        = ∫ w : ℝ, Real.exp (-(w ^ 2) / (2 * s ^ 2)) * F (a + w) := by
      have h := integral_add_left_eq_self (μ := volume)
        (fun y : ℝ => Real.exp (-((y - a) ^ 2) / (2 * s ^ 2)) * F y) a
      rw [← h]
      apply integral_congr_ae
      filter_upwards with w
      show Real.exp (-((a + w - a) ^ 2) / (2 * s ^ 2)) * F (a + w)
          = Real.exp (-(w ^ 2) / (2 * s ^ 2)) * F (a + w)
      rw [show a + w - a = w from by ring]
    rw [htrans]
    have h := Measure.integral_comp_div
      (fun u : ℝ => Real.exp (-(u ^ 2 / 2)) * F (a + s * u)) s
    rw [abs_of_pos hs, smul_eq_mul] at h
    rw [← h]
    apply integral_congr_ae
    filter_upwards with w
    have h1 : -(w ^ 2) / (2 * s ^ 2) = -((w / s) ^ 2 / 2) := by field_simp
    have hsw : s * (w / s) = w := by field_simp
    rw [h1, hsw]
  have hconst : (∫ y : ℝ, (1 / Real.sqrt (2 * Real.pi * s ^ 2))
        * Real.exp (-((y - a) ^ 2) / (2 * s ^ 2)) * F y)
      = (1 / Real.sqrt (2 * Real.pi * s ^ 2))
        * ∫ y : ℝ, Real.exp (-((y - a) ^ 2) / (2 * s ^ 2)) * F y := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards with y
    ring
  rw [hconst, hcore]
  have hcs : (1 / Real.sqrt (2 * Real.pi * s ^ 2)) * s = 1 / Real.sqrt (2 * Real.pi) := by
    rw [hnorm]; field_simp
  rw [← mul_assoc, hcs]

/-! ## The polynomial `u ↦ Heₙ (a + s·u)` -/

private noncomputable def hermiteComp (n : ℕ) (a s : ℝ) : ℝ[X] :=
  ((Polynomial.hermite n).map (algebraMap ℤ ℝ)).comp (Polynomial.C a + Polynomial.C s * Polynomial.X)

private lemma eval_hermiteComp (n : ℕ) (a s u : ℝ) :
    (hermiteComp n a s).eval u = Polynomial.aeval (a + s * u) (Polynomial.hermite n) := by
  rw [hermiteComp, Polynomial.eval_comp, Polynomial.eval_add, Polynomial.eval_C,
    Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]
  exact (aeval_hermite_eq_eval_map n (a + s * u)).symm

private lemma integrable_hermite_gauss (n m : ℕ) (a s : ℝ) :
    Integrable
      (fun u : ℝ => u ^ m * (Real.exp (-(u ^ 2 / 2)) * Polynomial.aeval (a + s * u) (Polynomial.hermite n))) := by
  have h := integrable_polynomial_mul_gaussian (Polynomial.X ^ m * hermiteComp n a s)
  refine h.congr (Filter.Eventually.of_forall fun u => ?_)
  simp only [Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X, eval_hermiteComp]
  ring

/-! ## The Ornstein–Uhlenbeck average of the Hermite polynomials -/

/-- `D n r s x = ∫ u, exp (-u²/2) · Heₙ (r·x + s·u)`. -/
private noncomputable def D (n : ℕ) (r s x : ℝ) : ℝ :=
  ∫ u : ℝ, Real.exp (-(u ^ 2 / 2)) * Polynomial.aeval (r * x + s * u) (Polynomial.hermite n)

private lemma D_zero (r s x : ℝ) : D 0 r s x = Real.sqrt (2 * Real.pi) := by
  simp only [D, Polynomial.hermite_zero, map_one, mul_one]
  have h1 : (∫ u : ℝ, Real.exp (-(u ^ 2 / 2)))
      = ∫ u : ℝ, Real.exp (-(1 / 2 : ℝ) * u ^ 2) := by
    apply integral_congr_ae
    filter_upwards with u
    congr 1
    ring
  rw [h1, integral_gaussian]
  congr 1
  rw [show Real.pi / (1 / 2 : ℝ) = 2 * Real.pi by ring]

private lemma hermite_rec (n : ℕ) (v : ℝ) :
    Polynomial.aeval v (Polynomial.hermite (n + 1))
      = v * Polynomial.aeval v (Polynomial.hermite n)
        - (n : ℝ) * Polynomial.aeval v (Polynomial.hermite (n - 1)) := by
  rw [Polynomial.hermite_succ, Polynomial.aeval_sub, Polynomial.aeval_mul, Polynomial.aeval_X,
    hermite_derivative_poly n, Polynomial.aeval_mul, Polynomial.aeval_C]
  rw [show (algebraMap ℤ ℝ) (n : ℤ) = (n : ℝ) by simp]

/-- Integration by parts (Stein's identity) for Hermite polynomials against a Gaussian. -/
private lemma hermite_stein (n : ℕ) (a s : ℝ) :
    (∫ u : ℝ, u * (Real.exp (-(u ^ 2 / 2)) * Polynomial.aeval (a + s * u) (Polynomial.hermite n)))
      = s * (n : ℝ)
        * ∫ u : ℝ, Real.exp (-(u ^ 2 / 2)) * Polynomial.aeval (a + s * u) (Polynomial.hermite (n - 1)) := by
  set A : ℝ → ℝ := fun u => u * (Real.exp (-(u ^ 2 / 2)) * Polynomial.aeval (a + s * u) (Polynomial.hermite n)) with hA
  set B : ℝ → ℝ := fun u => Real.exp (-(u ^ 2 / 2)) * (s * ((n : ℝ) * Polynomial.aeval (a + s * u) (Polynomial.hermite (n - 1)))) with hB
  have hderiv : ∀ u, HasDerivAt
      (fun v : ℝ => Real.exp (-(v ^ 2 / 2)) * Polynomial.aeval (a + s * v) (Polynomial.hermite n))
      (-(A u) + B u) u := by
    intro u
    have hw : HasDerivAt (fun v : ℝ => Real.exp (-(v ^ 2 / 2))) (-u * Real.exp (-(u ^ 2 / 2))) u := by
      have hdiff : DifferentiableAt ℝ (fun v : ℝ => Real.exp (-(v ^ 2 / 2))) u := by fun_prop
      have h := hdiff.hasDerivAt
      rwa [deriv_gaussianWeight u] at h
    have hlin : HasDerivAt (fun v : ℝ => a + s * v) s u := by
      have h : HasDerivAt (fun v : ℝ => s * v) s u := by
        simpa using (hasDerivAt_id u).const_mul s
      simpa using h.const_add a
    have hcore : HasDerivAt (fun v : ℝ => Polynomial.aeval v (Polynomial.hermite n))
        ((n : ℝ) * Polynomial.aeval (a + s * u) (Polynomial.hermite (n - 1))) (a + s * u) := by
      have h := Polynomial.hasDerivAt_aeval (Polynomial.hermite n) (a + s * u)
      rw [hermite_derivative_poly n, Polynomial.aeval_mul, Polynomial.aeval_C] at h
      simpa using h
    have hH := hcore.comp u hlin
    have hφd := hw.mul hH
    refine hφd.congr_deriv ?_
    rw [hA, hB]
    simp only [Function.comp_apply]
    ring
  have hAint : Integrable A := by
    rw [hA]
    simpa using (integrable_hermite_gauss n 1 a s)
  have hBint : Integrable B := by
    have h := (integrable_hermite_gauss (n - 1) 0 a s).const_mul (s * (n : ℝ))
    rw [hB]
    refine h.congr (Filter.Eventually.of_forall fun u => ?_)
    simp only [pow_zero, one_mul]
    ring
  have hφint : Integrable (fun v : ℝ => Real.exp (-(v ^ 2 / 2)) * Polynomial.aeval (a + s * v) (Polynomial.hermite n)) :=
    (integrable_hermite_gauss n 0 a s).congr (Filter.Eventually.of_forall fun u => by
      simp only [pow_zero, one_mul])
  have hzero := integral_eq_zero_of_hasDerivAt_of_integrable hderiv (hAint.neg.add hBint) hφint
  have hsplit : (∫ u : ℝ, (-(A u) + B u)) = -(∫ u : ℝ, A u) + ∫ u : ℝ, B u := by
    have h1 : (∫ u : ℝ, (-(A u) + B u)) = ∫ u : ℝ, ((-A) u + B u) := by
      apply integral_congr_ae; filter_upwards with u; rfl
    rw [h1, integral_add hAint.neg hBint]
    rw [show (∫ u : ℝ, (-A) u) = -∫ u : ℝ, A u from integral_neg A]
  have hAB : (∫ u : ℝ, A u) = ∫ u : ℝ, B u := by
    rw [hsplit] at hzero; linarith
  rw [show (∫ u : ℝ, u * (Real.exp (-(u ^ 2 / 2)) * Polynomial.aeval (a + s * u) (Polynomial.hermite n)))
        = ∫ u : ℝ, A u from by rw [hA]]
  rw [hAB]
  rw [show (∫ u : ℝ, B u)
        = s * (n : ℝ) * ∫ u : ℝ, Real.exp (-(u ^ 2 / 2)) * Polynomial.aeval (a + s * u) (Polynomial.hermite (n - 1)) from by
      rw [hB, ← integral_const_mul]
      apply integral_congr_ae
      filter_upwards with u
      ring]

/-- Recursion for the Ornstein–Uhlenbeck average. -/
private lemma D_rec (n : ℕ) (r s x : ℝ) (hsq : s ^ 2 = 1 - r ^ 2) :
    D (n + 1) r s x = r * x * D n r s x - r ^ 2 * (n : ℝ) * D (n - 1) r s x := by
  set A : ℝ → ℝ := fun u => Real.exp (-(u ^ 2 / 2)) * ((r * x) * Polynomial.aeval (r * x + s * u) (Polynomial.hermite n)) with hA
  set B : ℝ → ℝ := fun u => Real.exp (-(u ^ 2 / 2)) * (s * (u * Polynomial.aeval (r * x + s * u) (Polynomial.hermite n))) with hB
  set C : ℝ → ℝ := fun u => Real.exp (-(u ^ 2 / 2)) * ((n : ℝ) * Polynomial.aeval (r * x + s * u) (Polynomial.hermite (n - 1))) with hC
  have hAint : Integrable A := by
    have h := (integrable_hermite_gauss n 0 (r * x) s).const_mul (r * x)
    rw [hA]
    refine h.congr (Filter.Eventually.of_forall fun u => ?_)
    simp only [pow_zero, one_mul]
    ring
  have hBint : Integrable B := by
    rw [hB]
    have h := (integrable_hermite_gauss n 1 (r * x) s).const_mul s
    refine h.congr (Filter.Eventually.of_forall fun u => ?_)
    simp only [pow_one]
    ring
  have hCint : Integrable C := by
    have h := (integrable_hermite_gauss (n - 1) 0 (r * x) s).const_mul (n : ℝ)
    rw [hC]
    refine h.congr (Filter.Eventually.of_forall fun u => ?_)
    simp only [pow_zero, one_mul]
    ring
  have hcong : D (n + 1) r s x = ∫ u : ℝ, (A u + B u - C u) := by
    simp only [D]
    apply integral_congr_ae
    filter_upwards with u
    rw [hermite_rec n (r * x + s * u)]
    simp only [hA, hB, hC]
    ring
  have hA_eq : (∫ u : ℝ, A u) = r * x * D n r s x := by
    rw [hA]; simp only [D]; rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards with u
    ring
  have hC_eq : (∫ u : ℝ, C u) = (n : ℝ) * D (n - 1) r s x := by
    rw [hC]; simp only [D]; rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards with u
    ring
  have hB_eq : (∫ u : ℝ, B u) = s * (s * (n : ℝ) * D (n - 1) r s x) := by
    have hstein := hermite_stein n (r * x) s
    have h1 : (∫ u : ℝ, B u)
        = s * (∫ u : ℝ, u * (Real.exp (-(u ^ 2 / 2)) * Polynomial.aeval (r * x + s * u) (Polynomial.hermite n))) := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards with u
      simp only [hB]
      ring
    rw [h1, hstein, show (∫ u : ℝ, Real.exp (-(u ^ 2 / 2)) * Polynomial.aeval (r * x + s * u) (Polynomial.hermite (n - 1))) = D (n - 1) r s x from rfl]
  have hsplit : (∫ u : ℝ, (A u + B u - C u)) = ((∫ u : ℝ, A u) + (∫ u : ℝ, B u)) - ∫ u : ℝ, C u := by
    have hAB : (∫ u : ℝ, (A u + B u)) = (∫ u : ℝ, A u) + (∫ u : ℝ, B u) := by
      simpa only using integral_add hAint hBint
    have hsub : (∫ u : ℝ, (A u + B u - C u)) = (∫ u : ℝ, (A u + B u)) - ∫ u : ℝ, C u :=
      integral_sub (hAint.add hBint) hCint
    linarith
  rw [hcong, hsplit, hA_eq, hB_eq, hC_eq]
  rw [show s * (s * ↑n * D (n - 1) r s x) = s ^ 2 * (↑n * D (n - 1) r s x) by ring]
  rw [hsq]
  ring

private lemma D_eq (n : ℕ) (r s x : ℝ) (hsq : s ^ 2 = 1 - r ^ 2) :
    D n r s x = Real.sqrt (2 * Real.pi) * r ^ n * Polynomial.aeval x (Polynomial.hermite n) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    match n with
    | 0 =>
      rw [D_zero, Polynomial.hermite_zero, Polynomial.aeval_C, map_one, pow_zero, mul_one, mul_one]
    | 1 =>
      have hrec := D_rec 0 r s x hsq
      simp only [Nat.zero_add, Nat.zero_sub, Nat.cast_zero, mul_zero, zero_mul, sub_zero] at hrec
      rw [hrec, D_zero, Polynomial.hermite_one, Polynomial.aeval_X]
      ring
    | (k + 2) =>
      have hrec := D_rec (k + 1) r s x hsq
      rw [show (k + 1) + 1 = k + 2 from by omega] at hrec
      rw [show (k + 1) - 1 = k from by omega] at hrec
      rw [hrec, ih (k + 1) (by omega), ih k (by omega), hermite_rec (k + 1) x]
      rw [show (k + 1) - 1 = k from by omega]
      have e1 : r ^ (k + 1) = r * r ^ k := by rw [Nat.add_comm k 1, pow_add, pow_one]
      have e2 : r ^ (k + 2) = r ^ 2 * r ^ k := by rw [Nat.add_comm k 2, pow_add]
      rw [e1, e2]
      ring

/-- Eigenfunction relation in the `(r,s)` normalisation. -/
theorem ou_hermite_gen (n : ℕ) (r s x : ℝ) (hs : 0 < s) (hsq : s ^ 2 = 1 - r ^ 2) :
    (∫ y : ℝ, (1 / Real.sqrt (2 * Real.pi * s ^ 2))
        * Real.exp (-((y - r * x) ^ 2) / (2 * s ^ 2))
        * (Polynomial.aeval y (Polynomial.hermite n)))
      = r ^ n * Polynomial.aeval x (Polynomial.hermite n) := by
  rw [gauss_shift_scale_integral (r * x) s hs (fun y => Polynomial.aeval y (Polynomial.hermite n))]
  rw [show (∫ u : ℝ, Real.exp (-(u ^ 2 / 2)) * Polynomial.aeval (r * x + s * u) (Polynomial.hermite n))
        = D n r s x from rfl]
  rw [D_eq n r s x hsq]
  have hspi : Real.sqrt (2 * Real.pi) ≠ 0 := by positivity
  field_simp

theorem ou_hermite_eigenfunction (n : ℕ) (t x : ℝ) (ht : 0 < t) :
    (∫ y : ℝ, (1 / Real.sqrt (2 * Real.pi * (1 - Real.exp (-2 * t))))
        * Real.exp (-((y - Real.exp (-t) * x) ^ 2) / (2 * (1 - Real.exp (-2 * t))))
        * (Polynomial.aeval y (Polynomial.hermite n)))
      = Real.exp (-(n : ℝ) * t) * Polynomial.aeval x (Polynomial.hermite n) := by
  have hpos : 0 < 1 - Real.exp (-2 * t) := by
    rw [sub_pos, Real.exp_lt_one_iff]; linarith
  have hs : 0 < Real.sqrt (1 - Real.exp (-2 * t)) := Real.sqrt_pos.mpr hpos
  have hsq : (Real.sqrt (1 - Real.exp (-2 * t))) ^ 2 = 1 - Real.exp (-t) ^ 2 := by
    rw [Real.sq_sqrt hpos.le, sq, ← Real.exp_add]
    congr 1
    ring
  have h := ou_hermite_gen n (Real.exp (-t)) (Real.sqrt (1 - Real.exp (-2 * t))) x hs hsq
  have hL : (∫ y : ℝ, (1 / Real.sqrt (2 * Real.pi * Real.sqrt (1 - Real.exp (-2 * t)) ^ 2))
        * Real.exp (-((y - Real.exp (-t) * x) ^ 2) / (2 * Real.sqrt (1 - Real.exp (-2 * t)) ^ 2))
        * (Polynomial.aeval y (Polynomial.hermite n)))
      = (∫ y : ℝ, (1 / Real.sqrt (2 * Real.pi * (1 - Real.exp (-2 * t))))
        * Real.exp (-((y - Real.exp (-t) * x) ^ 2) / (2 * (1 - Real.exp (-2 * t))))
        * (Polynomial.aeval y (Polynomial.hermite n))) := by
    rw [Real.sq_sqrt hpos.le]
  rw [← hL, h, ← Real.exp_nat_mul]
  congr 1
  ring

end

end Commons.Analysis.GaussianMeasure
