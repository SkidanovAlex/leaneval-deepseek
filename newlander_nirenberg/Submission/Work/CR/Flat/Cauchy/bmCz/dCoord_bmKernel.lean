import Mathlib
import Submission.Work.CR.Flat.Cauchy.bmCz.bmKernelDerivAux

namespace Work.CR.Flat.Cauchy.bmCz

open scoped NNReal ENNReal

open Work.CR.Flat

/-! ### Elementary rewrites used in the final computation -/

lemma conj_eq_re_sub_im_mul_I (z : ℂ) :
    starRingEnd ℂ z = (z.re : ℂ) - (z.im : ℂ) * Complex.I := by
  refine Complex.ext ?_ ?_ <;> simp [Complex.conj_re, Complex.conj_im]

/-- Evaluation of `smDeriv` on the `k`-th unit vector: `2 Re x_k`. -/
lemma smDeriv_single_one {n : ℕ} (x : Fin n → ℂ) (k : Fin n) :
    smDeriv x (Pi.single k (1 : ℂ)) = 2 * (x k).re := by
  have hsum : smDeriv x (Pi.single k (1 : ℂ) : Fin n → ℂ)
      = ∑ l, (2 * (x l).re * ((Pi.single k (1 : ℂ) : Fin n → ℂ) l).re
            + 2 * (x l).im * ((Pi.single k (1 : ℂ) : Fin n → ℂ) l).im) := by
    simp [smDeriv]
  rw [hsum]
  rw [Finset.sum_eq_single k (fun l _ hl => ?_) (fun hk => ?_)]
  · simp
  · rw [Pi.single_eq_of_ne hl]
    simp
  · exact absurd (Finset.mem_univ k) hk

/-- Evaluation of `smDeriv` on the `k`-th vector `i e_k`: `2 Im x_k`. -/
lemma smDeriv_single_I {n : ℕ} (x : Fin n → ℂ) (k : Fin n) :
    smDeriv x (Pi.single k (Complex.I : ℂ)) = 2 * (x k).im := by
  have hsum : smDeriv x (Pi.single k (Complex.I : ℂ) : Fin n → ℂ)
      = ∑ l, (2 * (x l).re * ((Pi.single k (Complex.I : ℂ) : Fin n → ℂ) l).re
            + 2 * (x l).im * ((Pi.single k (Complex.I : ℂ) : Fin n → ℂ) l).im) := by
    simp [smDeriv]
  rw [hsum]
  rw [Finset.sum_eq_single k (fun l _ hl => ?_) (fun hk => ?_)]
  · simp
  · rw [Pi.single_eq_of_ne hl]
    simp
  · exact absurd (Finset.mem_univ k) hk

/-- `i e_k` in terms of `e_k`, componentwise. -/
lemma single_I_eq {n : ℕ} (k : Fin n) :
    (Pi.single k (Complex.I : ℂ) : Fin n → ℂ)
      = fun l => Complex.I * (Pi.single k (1 : ℂ) : Fin n → ℂ) l := by
  funext l
  by_cases hl : l = k
  · subst hl; simp
  · rw [Pi.single_eq_of_ne hl, Pi.single_eq_of_ne hl]; simp

/-- The conjugate of the `j`-th component of `i e_k` in terms of that of `e_k`. -/
lemma star_single_I {n : ℕ} (j k : Fin n) :
    starRingEnd ℂ ((Pi.single k (Complex.I : ℂ) : Fin n → ℂ) j)
      = -Complex.I * starRingEnd ℂ ((Pi.single k (1 : ℂ) : Fin n → ℂ) j) := by
  rw [congrFun (single_I_eq k) j, map_mul]
  simp

/-- `‖x‖^{-2n-2} = (s x)^{-n-1}` where `s x = ‖x‖²`. -/
lemma sm_zpow_eq {n : ℕ} (x : Fin n → ℂ) :
    ((((sm x : ℝ) : ℂ))) ^ (-(n : ℤ) - 1)
      = (((eucNorm x : ℂ) ^ (2 * n + 2))⁻¹) := by
  have hZ : ((((sm x : ℝ) : ℂ))) = ((eucNorm x : ℂ)) ^ 2 := by
    rw [sm_eq_eucNorm_sq, Complex.ofReal_pow]
  have hexp : 2 * (n + 1) = 2 * n + 2 := by ring
  rw [hZ, show (-(n : ℤ) - 1) = -(((n + 1 : ℕ) : ℤ)) by push_cast; ring,
    zpow_neg, zpow_natCast, ← pow_mul, hexp]

/-! ### The derivative of the Bochner–Martinelli kernel -/

/-- The value of the Fréchet derivative of `y ↦ bmKernel j y` at `x ≠ 0` on a vector `v`,
in coordinates. -/
lemma fderiv_bmKernel_apply {n : ℕ} (j : Fin n) {x : Fin n → ℂ} (hx : x ≠ 0)
    (v : Fin n → ℂ) :
    fderiv ℝ (bmKernel j) x v
      = starRingEnd ℂ (x j) *
          ((↑(-(n:ℤ)) : ℂ) * (((sm x : ℝ) : ℂ)) ^ (-(n:ℤ) - 1) * ((smDeriv x v : ℝ) : ℂ))
        + ((((sm x : ℝ) : ℂ)) ^ (-(n:ℤ))) * starRingEnd ℂ (v j) := by
  have hZ : (((sm x : ℝ) : ℂ)) ≠ 0 := by
    simpa using ne_of_gt (sm_pos hx : (0:ℝ) < sm x)
  have hconj : HasFDerivAt (fun y : Fin n → ℂ => starRingEnd ℂ (y j))
      ((Complex.conjCLE : ℂ →L[ℝ] ℂ).comp (projCLM j)) x := by
    have h := ContinuousLinearMap.hasFDerivAt
      ((Complex.conjCLE : ℂ →L[ℝ] ℂ).comp (projCLM j)) (x := x)
    have hfun : (⇑((Complex.conjCLE : ℂ →L[ℝ] ℂ).comp (projCLM j)) : (Fin n → ℂ) → ℂ)
        = fun y => starRingEnd ℂ (y j) := by ext y; simp
    rw [hfun] at h
    exact h
  have hof : HasFDerivAt (fun y : Fin n → ℂ => ((sm y : ℝ) : ℂ))
      (Complex.ofRealCLM.comp (smDeriv x)) x :=
    Complex.ofRealCLM.hasFDerivAt.comp x (hasFDerivAt_sm x)
  have hout : HasFDerivAt (fun z : ℂ => z ^ (-(n:ℤ)))
      ((ContinuousLinearMap.mul ℝ ℂ
        ((↑(-(n:ℤ)) : ℂ) * ((((sm x : ℝ) : ℂ))) ^ (-(n:ℤ) - 1)) : ℂ →L[ℝ] ℂ))
      ((((sm x : ℝ) : ℂ))) := by
    have h1 : HasDerivAt (fun z : ℂ => z ^ (-(n:ℤ)))
        ((↑(-(n:ℤ)) : ℂ) * ((((sm x : ℝ) : ℂ))) ^ (-(n:ℤ) - 1)) (((sm x : ℝ) : ℂ)) :=
      hasDerivAt_zpow (-(n:ℤ)) _ (Or.inl hZ)
    have hL : ContinuousLinearMap.restrictScalars ℝ
        (ContinuousLinearMap.toSpanSingleton ℂ
          ((↑(-(n:ℤ)) : ℂ) * ((((sm x : ℝ) : ℂ))) ^ (-(n:ℤ) - 1)))
        = ContinuousLinearMap.mul ℝ ℂ
          ((↑(-(n:ℤ)) : ℂ) * ((((sm x : ℝ) : ℂ))) ^ (-(n:ℤ) - 1)) := by
      ext w; simp; ring
    have h2 := h1.restrictScalars ℝ
    rw [hL] at h2
    exact h2
  have hprod := hconj.mul (hout.comp x hof)
  have hbm : HasFDerivAt (fun y : Fin n → ℂ => bmKernel j y) (bmKernelFDeriv j x) x := by
    convert hprod using 1
    · funext y
      exact bmKernel_eq j y
    · ext w
      simp [bmKernelFDeriv]
  have hf : fderiv ℝ (bmKernel j) x = bmKernelFDeriv j x := hbm.fderiv
  rw [hf]
  simp [bmKernelFDeriv]

/-! ### The final algebraic computation -/

/-- The algebraic core of the Wirtinger derivative of the kernel: the value of
`∂_{z_k}` obtained from the two directional derivatives, as a function of the auxiliary
quantity `s = \overline{(e_k)_j}`. -/
lemma dCoord_bmKernel_alg {n : ℕ} (j k : Fin n) (x : Fin n → ℂ) (s : ℂ) :
    (1/2 : ℂ) *
        ((starRingEnd ℂ (x j)
              * ((↑(-(n:ℤ)) : ℂ) * (((sm x : ℝ) : ℂ)) ^ (-(n:ℤ) - 1) * ((2 * (x k).re : ℝ) : ℂ))
            + ((((sm x : ℝ) : ℂ)) ^ (-(n:ℤ))) * s)
          - Complex.I *
            (starRingEnd ℂ (x j)
                * ((↑(-(n:ℤ)) : ℂ) * (((sm x : ℝ) : ℂ)) ^ (-(n:ℤ) - 1) * ((2 * (x k).im : ℝ) : ℂ))
              + ((((sm x : ℝ) : ℂ)) ^ (-(n:ℤ))) * (-Complex.I * s)))
      = bmDzKernel k j x := by
  rw [bmDzKernel, div_eq_mul_inv, conj_eq_re_sub_im_mul_I (x k), sm_zpow_eq x]
  push_cast
  ring_nf
  rw [Complex.I_sq]
  ring

/-- The Wirtinger derivative `∂_{z_k}` of the Bochner–Martinelli kernel. -/
theorem dCoord_bmKernel {n : ℕ} {k j : Fin n} {x : Fin n → ℂ} (hx : x ≠ 0) :
    Work.CR.Flat.dCoord k (Work.CR.Flat.Cauchy.bmKernel j) x
      = Work.CR.Flat.Cauchy.bmDzKernel k j x := by
  have h1 := fderiv_bmKernel_apply j hx (Pi.single k (1 : ℂ))
  have h2 := fderiv_bmKernel_apply j hx (Pi.single k (Complex.I : ℂ))
  rw [dCoord, h1, h2, smDeriv_single_one, smDeriv_single_I, star_single_I]
  exact dCoord_bmKernel_alg j k x _

end Work.CR.Flat.Cauchy.bmCz
