import Mathlib
import Submission.Work.BourgainPlan.Maximal.mst_freeze_defs
import Submission.Work.BourgainPlan.Maximal.mst_deriv_defs

/-!
# Smoothness and two-derivative bounds for the lifted one-arc error symbol `mstTht`

`mstTht P J β r u = star (mstG P β) − star (polyWeylKernel P J (r + u))` is a constant minus the
conjugate Weyl kernel read at the lifted offset `r + u`.  Expanding the kernel as the finite sum
`J⁻¹ Σ_{n<J} e^{−2πi (r+u) P(n)}` (`star_polyWeylKernel_expand`; vocabulary in `mst_deriv_defs`)
turns both derivative bounds into finite-sum estimates:

* `‖(mstTht)'(u)‖ ≤ J⁻¹ Σ_{n<J} 2π |P(n)| ≤ 2π (Σᵢ|cᵢ|) J^d = mstThtL P J`,
* `‖(mstTht)''(u)‖ ≤ J⁻¹ Σ_{n<J} (2π P(n))² ≤ (2π (Σᵢ|cᵢ|) J^d)² = (mstThtL P J)²`

for `n < J`, `J ≥ 1`, using `|P(n)| ≤ (Σᵢ|cᵢ|) J^d`.
-/

set_option autoImplicit false

namespace Work.BourgainPlan.Maximal

open Work.BourgainPlan.IonescuWainger

noncomputable section

/-! ### The lift identity and the expanded symbol -/

/-- The lift of the conjugate Weyl kernel: for real `r, u`,
`star (polyWeylKernel P J (r+u)) = J⁻¹ Σ_{n<J} e^{−2πi (r+u) P(n)}`. -/
theorem star_polyWeylKernel_lift (P : Polynomial ℤ) (J : ℕ) (r u : ℝ) :
    star (polyWeylKernel P J (r + u)) = mstJInv J * mstExpSum P J r u := by
  rw [star_polyWeylKernel_expand]
  simp only [mstJInv, mstExpSum, mstExpTerm, mstPn]

/-- The lifted one-arc error symbol as a constant minus the normalised expanded kernel. -/
theorem mstTht_eq_expSum (P : Polynomial ℤ) (J : ℕ)
    (β : Work.BourgainPlan.IonescuWainger.Circle) (r u : ℝ) :
    mstTht P J β r u = star (mstG P β) - mstJInv J * mstExpSum P J r u := by
  rw [mstTht_apply, star_polyWeylKernel_lift]

/-! ### Derivative facts for the summands and the sums -/

/-- Termwise derivative of `mstExpTerm P r n`: the derivative is the summand times `−2πi P(n)`. -/
theorem hasDerivAt_mstExpTerm (P : Polynomial ℤ) (r : ℝ) (n : ℕ) (u : ℝ) :
    HasDerivAt (mstExpTerm P r n) (mstExpTerm P r n u * mstDConst P n) u := by
  have h1 : HasDerivAt (fun u : ℝ => r + u) (1 : ℝ) u := by
    simpa using (hasDerivAt_id u).const_add r
  have h2 : HasDerivAt (fun u : ℝ => (r + u) * mstPn P n) (mstPn P n) u := by
    simpa using h1.mul_const (mstPn P n)
  have h3 : HasDerivAt (fun u : ℝ => 2 * Real.pi * ((r + u) * mstPn P n))
      (2 * Real.pi * mstPn P n) u := by
    simpa using h2.const_mul (2 * Real.pi)
  have h4 : HasDerivAt (fun u : ℝ => -(2 * Real.pi * ((r + u) * mstPn P n)))
      (-(2 * Real.pi * mstPn P n)) u := h3.neg
  have h5 : HasDerivAt (fun u : ℝ => (((-(2 * Real.pi * ((r + u) * mstPn P n))) : ℝ) : ℂ))
      (((-(2 * Real.pi * mstPn P n)) : ℝ) : ℂ) u := h4.ofReal_comp
  have h6 : HasDerivAt
      (fun u : ℝ => (((-(2 * Real.pi * ((r + u) * mstPn P n))) : ℝ) : ℂ) * Complex.I)
      ((((-(2 * Real.pi * mstPn P n)) : ℝ) : ℂ) * Complex.I) u := h5.mul_const Complex.I
  have h7 := h6.cexp
  have hfun : (fun u : ℝ => Complex.exp
      ((((-(2 * Real.pi * ((r + u) * mstPn P n))) : ℝ) : ℂ) * Complex.I)) = mstExpTerm P r n := by
    ext v
    rfl
  rw [hfun] at h7
  simpa only [mstDConst, mstExpTerm] using h7

/-- Termwise derivative of the expanded sum. -/
theorem hasDerivAt_mstExpSum (P : Polynomial ℤ) (J : ℕ) (r : ℝ) (u : ℝ) :
    HasDerivAt (mstExpSum P J r) (mstExpSumDeriv P J r u) u := by
  have h := HasDerivAt.sum (u := Finset.range J) (A := fun n => mstExpTerm P r n)
    (A' := fun n => mstExpTerm P r n u * mstDConst P n)
    (fun n _ => hasDerivAt_mstExpTerm P r n u)
  have hfun : (∑ i ∈ Finset.range J, mstExpTerm P r i) = mstExpSum P J r := by
    ext v
    rw [Finset.sum_apply]
    rfl
  rw [hfun] at h
  simpa only [mstExpSumDeriv] using h

/-- Termwise second derivative of the expanded sum. -/
theorem hasDerivAt_mstExpSumDeriv (P : Polynomial ℤ) (J : ℕ) (r : ℝ) (u : ℝ) :
    HasDerivAt (mstExpSumDeriv P J r) (mstExpSumDeriv2 P J r u) u := by
  have h := HasDerivAt.sum (u := Finset.range J)
    (A := fun n => fun u : ℝ => mstExpTerm P r n u * mstDConst P n)
    (A' := fun n => (mstExpTerm P r n u * mstDConst P n) * mstDConst P n)
    (fun n _ => (hasDerivAt_mstExpTerm P r n u).mul_const (mstDConst P n))
  have hfun : (∑ i ∈ Finset.range J, fun u : ℝ => mstExpTerm P r i u * mstDConst P i)
      = mstExpSumDeriv P J r := by
    ext v
    rw [Finset.sum_apply]
    rfl
  rw [hfun] at h
  simpa only [mstExpSumDeriv2, pow_two, mul_assoc] using h

/-- The expanded sum is `C²`. -/
theorem contDiff_mstExpSum (P : Polynomial ℤ) (J : ℕ) (r : ℝ) :
    ContDiff ℝ 2 (mstExpSum P J r) := by
  refine ContDiff.sum (fun n _ => ?_)
  have hlin : ContDiff ℝ 2 (fun u : ℝ => -(2 * Real.pi * ((r + u) * mstPn P n))) := by
    fun_prop
  have hcast : ContDiff ℝ 2
      (fun u : ℝ => (((-(2 * Real.pi * ((r + u) * mstPn P n))) : ℝ) : ℂ)) :=
    (Complex.ofRealCLM.contDiff).comp hlin
  have hmul : ContDiff ℝ 2
      (fun u : ℝ => (((-(2 * Real.pi * ((r + u) * mstPn P n))) : ℝ) : ℂ) * Complex.I) :=
    hcast.mul contDiff_const
  simpa only [mstExpTerm] using hmul.cexp

/-! ### The modulus of the summands and the size of `P(n)` -/

/-- The summands have modulus `1`. -/
theorem norm_mstExpTerm (P : Polynomial ℤ) (r : ℝ) (n : ℕ) (u : ℝ) :
    ‖mstExpTerm P r n u‖ = 1 := by
  rw [mstExpTerm, Complex.norm_exp]
  simp

/-- The derivative constant has modulus `2π |P(n)|`. -/
theorem norm_mstDConst (P : Polynomial ℤ) (n : ℕ) :
    ‖mstDConst P n‖ = 2 * Real.pi * |mstPn P n| := by
  rw [mstDConst, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_neg,
    abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2 * Real.pi)]

/-- `|P(n)| ≤ (Σᵢ|cᵢ|) J^d` for `n < J`, `J ≥ 1`. -/
theorem mstPn_abs_le_aux (P : Polynomial ℤ) (J n : ℕ) (hn : n < J) (hJ : 1 ≤ J) :
    |mstPn P n| ≤ mstCoeffB P * (J : ℝ) ^ P.natDegree := by
  have hnr : (n : ℝ) ≤ (J : ℝ) := by
    exact_mod_cast (Nat.le_of_lt hn)
  have hJ1 : (1 : ℝ) ≤ (J : ℝ) := by exact_mod_cast hJ
  have hPn : mstPn P n
      = ∑ i ∈ Finset.range (P.natDegree + 1), ((P.coeff i : ℤ) : ℝ) * (n : ℝ) ^ i := by
    rw [mstPn, Polynomial.eval_eq_sum_range]
    push_cast
    rfl
  rw [hPn]
  calc |∑ i ∈ Finset.range (P.natDegree + 1), ((P.coeff i : ℤ) : ℝ) * (n : ℝ) ^ i|
      ≤ ∑ i ∈ Finset.range (P.natDegree + 1),
          |((P.coeff i : ℤ) : ℝ) * (n : ℝ) ^ i| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ i ∈ Finset.range (P.natDegree + 1),
          |((P.coeff i : ℤ) : ℝ)| * (n : ℝ) ^ i := by
        refine Finset.sum_congr rfl (fun i _ => ?_)
        rw [abs_mul]
        rw [abs_of_nonneg (show (0 : ℝ) ≤ (n : ℝ) ^ i by positivity)]
    _ ≤ ∑ i ∈ Finset.range (P.natDegree + 1),
          |((P.coeff i : ℤ) : ℝ)| * (J : ℝ) ^ P.natDegree := by
        refine Finset.sum_le_sum (fun i hi => ?_)
        refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
        have hid : i ≤ P.natDegree := by
          have := Finset.mem_range.mp hi
          omega
        calc (n : ℝ) ^ i ≤ (J : ℝ) ^ i := pow_le_pow_left₀ (by positivity) hnr i
          _ ≤ (J : ℝ) ^ P.natDegree := pow_le_pow_right₀ hJ1 hid
    _ = mstCoeffB P * (J : ℝ) ^ P.natDegree := by
        rw [mstCoeffB, Finset.sum_mul]

/-! ### The two norm bounds -/

/-- `‖J⁻¹‖ = J⁻¹`. -/
theorem norm_mstJInv (J : ℕ) : ‖mstJInv J‖ = (J : ℝ)⁻¹ := by
  rw [mstJInv, norm_inv, Complex.norm_real, Real.norm_eq_abs]
  rw [abs_of_nonneg (show (0 : ℝ) ≤ (J : ℝ) by positivity)]

/-- `‖Σ_{n<J} (−2πi P(n)) e^{−2πi (r+u) P(n)}‖ ≤ J · (2π (Σᵢ|cᵢ|) J^d)`. -/
theorem norm_mstExpSumDeriv_le (P : Polynomial ℤ) (J : ℕ) (r : ℝ) (hJ : 1 ≤ J) (u : ℝ) :
    ‖mstExpSumDeriv P J r u‖
      ≤ (J : ℝ) * (2 * Real.pi * (mstCoeffB P * (J : ℝ) ^ P.natDegree)) := by
  rw [mstExpSumDeriv]
  calc ‖∑ n ∈ Finset.range J, mstExpTerm P r n u * mstDConst P n‖
      ≤ ∑ n ∈ Finset.range J, ‖mstExpTerm P r n u * mstDConst P n‖ := norm_sum_le _ _
    _ ≤ ∑ _n ∈ Finset.range J,
          (2 * Real.pi * (mstCoeffB P * (J : ℝ) ^ P.natDegree)) := by
        refine Finset.sum_le_sum (fun n hn => ?_)
        rw [norm_mul, norm_mstExpTerm, one_mul, norm_mstDConst]
        exact mul_le_mul_of_nonneg_left
          (mstPn_abs_le_aux P J n (Finset.mem_range.mp hn) hJ) (by positivity)
    _ = (J : ℝ) * (2 * Real.pi * (mstCoeffB P * (J : ℝ) ^ P.natDegree)) := by
        simp [Finset.sum_const, Finset.card_range, nsmul_eq_mul]

/-- `‖Σ_{n<J} (−2πi P(n))² e^{−2πi (r+u) P(n)}‖ ≤ J · (2π (Σᵢ|cᵢ|) J^d)²`. -/
theorem norm_mstExpSumDeriv2_le (P : Polynomial ℤ) (J : ℕ) (r : ℝ) (hJ : 1 ≤ J) (u : ℝ) :
    ‖mstExpSumDeriv2 P J r u‖
      ≤ (J : ℝ) * (2 * Real.pi * (mstCoeffB P * (J : ℝ) ^ P.natDegree)) ^ 2 := by
  rw [mstExpSumDeriv2]
  calc ‖∑ n ∈ Finset.range J, mstExpTerm P r n u * (mstDConst P n) ^ 2‖
      ≤ ∑ n ∈ Finset.range J, ‖mstExpTerm P r n u * (mstDConst P n) ^ 2‖ := norm_sum_le _ _
    _ ≤ ∑ _n ∈ Finset.range J,
          (2 * Real.pi * (mstCoeffB P * (J : ℝ) ^ P.natDegree)) ^ 2 := by
        refine Finset.sum_le_sum (fun n hn => ?_)
        rw [norm_mul, norm_pow, norm_mstExpTerm, one_mul]
        have hb : ‖mstDConst P n‖ ≤ 2 * Real.pi * (mstCoeffB P * (J : ℝ) ^ P.natDegree) := by
          rw [norm_mstDConst]
          exact mul_le_mul_of_nonneg_left
            (mstPn_abs_le_aux P J n (Finset.mem_range.mp hn) hJ) (by positivity)
        exact pow_le_pow_left₀ (norm_nonneg _) hb 2
    _ = (J : ℝ) * (2 * Real.pi * (mstCoeffB P * (J : ℝ) ^ P.natDegree)) ^ 2 := by
        simp [Finset.sum_const, Finset.card_range, nsmul_eq_mul]

/-- The first-derivative bound of the lifted symbol. -/
theorem norm_deriv_mstTht_le (P : Polynomial ℤ) (J : ℕ) (r : ℝ) (hJ : 1 ≤ J) (u : ℝ) :
    ‖-(mstJInv J * mstExpSumDeriv P J r u)‖ ≤ mstThtL P J := by
  rw [norm_neg]
  calc ‖mstJInv J * mstExpSumDeriv P J r u‖
      ≤ ‖mstJInv J‖ * ‖mstExpSumDeriv P J r u‖ := norm_mul_le _ _
    _ ≤ (J : ℝ)⁻¹ * ((J : ℝ) * (2 * Real.pi * (mstCoeffB P * (J : ℝ) ^ P.natDegree))) := by
        rw [norm_mstJInv J]
        exact mul_le_mul_of_nonneg_left (norm_mstExpSumDeriv_le P J r hJ u) (by positivity)
    _ = mstThtL P J := by
        rw [mstThtL]
        field_simp

/-- The second-derivative bound of the lifted symbol. -/
theorem norm_iteratedDeriv_mstTht_le (P : Polynomial ℤ) (J : ℕ) (r : ℝ) (hJ : 1 ≤ J) (u : ℝ) :
    ‖-(mstJInv J * mstExpSumDeriv2 P J r u)‖ ≤ (mstThtL P J) ^ 2 := by
  rw [norm_neg]
  calc ‖mstJInv J * mstExpSumDeriv2 P J r u‖
      ≤ ‖mstJInv J‖ * ‖mstExpSumDeriv2 P J r u‖ := norm_mul_le _ _
    _ ≤ (J : ℝ)⁻¹
          * ((J : ℝ) * (2 * Real.pi * (mstCoeffB P * (J : ℝ) ^ P.natDegree)) ^ 2) := by
        rw [norm_mstJInv J]
        exact mul_le_mul_of_nonneg_left (norm_mstExpSumDeriv2_le P J r hJ u) (by positivity)
    _ = (mstThtL P J) ^ 2 := by
        rw [mstThtL]
        field_simp

/-! ### The main statement -/

/-- Smoothness and `L^∞` bounds for the first two derivatives of the lifted one-arc error
symbol `mstTht P J β r u = star (mstG P β) − star (polyWeylKernel P J (r + u))`.

Route: `star_polyWeylKernel_expand` writes `star (polyWeylKernel P J x)` as
`J⁻¹ Σ_{n<J} exp(−2πi x P(n))` (`P(n) ∈ ℤ`); the summand `u ↦ exp(−2πi (r+u) P(n))` has
derivative `(−2πi P(n)) exp(…)` of modulus `2π|P(n)|` and second derivative of modulus
`(2π P(n))²`.  Termwise differentiation of the finite sum gives
`‖(mstTht)'‖ ≤ 2π J⁻¹ Σ_{n<J} |P(n)| ≤ 2π (Σᵢ|cᵢ|) J^d = mstThtL P J` for `J ≥ 1`
(using `|P(n)| ≤ (Σᵢ|cᵢ|) J^d` from `Polynomial.eval_eq_sum_range` and `n < J`),
and, by Cauchy–Schwarz in the form `(J⁻¹ Σ_{n<J} |P(n)|)² ≤ J⁻¹ Σ_{n<J} P(n)²`,
`‖(mstTht)''‖ ≤ 4π² J⁻¹ Σ_{n<J} P(n)² ≤ (mstThtL P J)²`. -/
theorem mstTht_deriv_bounds (P : Polynomial ℤ) (J : ℕ)
    (β : Work.BourgainPlan.IonescuWainger.Circle) (r : ℝ) (hJ : 1 ≤ J) :
    ContDiff ℝ 2 (fun u : ℝ => Work.BourgainPlan.Maximal.mstTht P J β r u) ∧
    (∀ u : ℝ, ‖deriv (fun x : ℝ => Work.BourgainPlan.Maximal.mstTht P J β r x) u‖
      ≤ Work.BourgainPlan.Maximal.mstThtL P J) ∧
    (∀ u : ℝ, ‖iteratedDeriv 2 (fun x : ℝ => Work.BourgainPlan.Maximal.mstTht P J β r x) u‖
      ≤ (Work.BourgainPlan.Maximal.mstThtL P J) ^ 2) := by
  have hfun : (fun u : ℝ => mstTht P J β r u)
      = fun u : ℝ => star (mstG P β) - mstJInv J * mstExpSum P J r u :=
    funext fun u => mstTht_eq_expSum P J β r u
  rw [hfun]
  set F : ℝ → ℂ := fun u : ℝ => star (mstG P β) - mstJInv J * mstExpSum P J r u with hF
  have hderiv : ∀ u : ℝ, deriv F u = -(mstJInv J * mstExpSumDeriv P J r u) := by
    intro u
    have h : HasDerivAt F (-(mstJInv J * mstExpSumDeriv P J r u)) u := by
      rw [hF]
      exact ((hasDerivAt_mstExpSum P J r u).const_mul (mstJInv J)).const_sub (star (mstG P β))
    exact h.deriv
  have hderiv2 : ∀ u : ℝ, deriv (deriv F) u = -(mstJInv J * mstExpSumDeriv2 P J r u) := by
    intro u
    have heq : deriv F = fun v : ℝ => -(mstJInv J * mstExpSumDeriv P J r v) :=
      funext fun v => hderiv v
    have h : HasDerivAt (deriv F) (-(mstJInv J * mstExpSumDeriv2 P J r u)) u := by
      rw [heq]
      exact ((hasDerivAt_mstExpSumDeriv P J r u).const_mul (mstJInv J)).neg
    exact h.deriv
  refine ⟨?_, ?_, ?_⟩
  · rw [hF]
    exact ContDiff.sub contDiff_const ((contDiff_const).mul (contDiff_mstExpSum P J r))
  · intro u
    rw [hderiv u]
    exact norm_deriv_mstTht_le P J r hJ u
  · intro u
    have hiter : iteratedDeriv 2 F = deriv (deriv F) := by
      rw [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ]
      rw [show (1 : ℕ) = 0 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_zero]
    rw [hiter, hderiv2 u]
    exact norm_iteratedDeriv_mstTht_le P J r hJ u

end

end Work.BourgainPlan.Maximal
