import Mathlib
import Submission.Work.KMTAreas.A7.ModelApproxM0Deriv

set_option autoImplicit false
set_option maxHeartbeats 2000000

open MeasureTheory Polynomial Topology Filter
open scoped Convolution BigOperators Interval

namespace Work.KMTPlan.A6

noncomputable section

/-!
## The `C^4` regularity of the differentiated oscillatory integral of §6

The integral `mTildeDeriv P N ξ₁ ξ₂ j₁ j₂` of `Work.KMTAreas.A7.ModelApproxM0Deriv` is the formal
`j`-th `(ξ₁,ξ₂)`-derivative of the halved oscillatory integral `m̃_{N,ℝ}` of §6 of
Krause--Mirek--Tao.  Its integrand is a smooth function of `(t,ξ₁,ξ₂)`, and `t` ranges over the
compact interval `[1/2,1]`; hence the parametric integral is `C^∞` in `(ξ₁,ξ₂)`.

Rather than differentiating under the integral sign directly, we *recognise the integral as a
convolution*: with `f = 1_{(1/2,1]}` (locally integrable) and
`g(ξ,t) = ψ(t) · e(ξ₁N(-t) + ξ₂P(N(-t))) (2πiN(-t))^{j₁} (2πiP(N(-t)))^{j₂}`, where `ψ` is a bump
equal to `1` on `[-1,1]` and supported in `[-2,2]` (so that the auxiliary compact support required
by the convolution theorem is available and `ψ(-t) = 1` on `(1/2,1]`), we have

`mTildeDeriv P N ξ₁ ξ₂ j₁ j₂ = (f ⋆[mul] g(ξ,·))(0)`,

and Mathlib's `contDiffOn_convolution_right_with_param_comp` gives the smoothness of the right-hand
side as a function of the parameter `ξ`, with no domination bookkeeping left to us.
-/

/-- The localising bump: it equals `1` on `[-1,1]` and is supported in `[-2,2]`. -/
def mTildeBump : ContDiffBump (0 : ℝ) := default

/-- The integrand of `mTildeDeriv`, with the parameter `s` standing for `-t`:
`e(ξ₁N(-s) + ξ₂P(N(-s)))(2πiN(-s))^{j₁}(2πiP(N(-s)))^{j₂}`. -/
def mTildeIntg (P : ℤ[X]) (N : ℝ) (j₁ j₂ : ℕ) (p : ℝ × ℝ) (s : ℝ) : ℂ :=
  Work.KMTAreas.A7.ee (p.1 * N * (-s) + p.2 * Work.KMTAreas.A7.PevalR P (N * (-s)))
    * (2 * Real.pi * Complex.I * (((N * (-s) : ℝ)) : ℂ)) ^ j₁
    * (2 * Real.pi * Complex.I * (((Work.KMTAreas.A7.PevalR P (N * (-s)) : ℝ)) : ℂ)) ^ j₂

/-- The bump-localised integrand of `mTildeDeriv`; the bump supplies the compact support in `s`
which the convolution theorem needs, and equals `1` on the relevant interval `[-1,1]`. -/
def mTildeGfun (P : ℤ[X]) (N : ℝ) (j₁ j₂ : ℕ) (p : ℝ × ℝ) (s : ℝ) : ℂ :=
  ((mTildeBump s : ℝ) : ℂ) * mTildeIntg P N j₁ j₂ p s

/-- The indicator of the integration interval, as a function on `ℝ`. -/
def mTildeFfun (a b : ℝ) : ℝ → ℂ := (Set.Ioc a b).indicator (fun _ => 1)

/-- Multiplication, as a continuous bilinear map `ℂ →L[ℝ] ℂ →L[ℝ] ℂ`. -/
def mTildeCL : ℂ →L[ℝ] ℂ →L[ℝ] ℂ := ContinuousLinearMap.mul ℝ ℂ

/-- The coercion `ℝ → ℂ` is `C^∞`. -/
theorem contDiff_ofReal_A6 (n : ℕ∞) : ContDiff ℝ n (fun x : ℝ => (x : ℂ)) := by
  have h : (fun x : ℝ => (x : ℂ)) = ⇑Complex.ofRealCLM := by
    funext x
    rw [Complex.ofRealCLM_apply]
  rw [h]
  exact Complex.ofRealCLM.contDiff

/-- The real evaluation `PevalR P` of an integer polynomial is `C^∞`. -/
theorem contDiff_PevalR_A6 (P : ℤ[X]) :
    ContDiff ℝ ⊤ (fun t : ℝ => Work.KMTAreas.A7.PevalR P t) := by
  have h : (fun t : ℝ => (aeval t) P) = fun t : ℝ => Work.KMTAreas.A7.PevalR P t := by
    funext t
    simp [Work.KMTAreas.A7.PevalR, Polynomial.aeval_def, Polynomial.eval_map]
  rw [← h]
  exact Polynomial.contDiff_aeval P ⊤

/-- The character `e(x) = exp (2πi x)` is `C^∞` on `ℝ`. -/
theorem contDiff_ee_A6 (n : ℕ∞) : ContDiff ℝ n Work.KMTAreas.A7.ee := by
  unfold Work.KMTAreas.A7.ee
  refine (Complex.contDiff_exp (𝕜 := ℝ)).comp ?_
  have h : ContDiff ℝ n (fun x : ℝ => (2 * (Real.pi : ℂ) * Complex.I) * (x : ℂ)) :=
    contDiff_const.mul (contDiff_ofReal_A6 n)
  simpa [Function.comp_apply] using h

/-- The joint integrand `(ξ,s) ↦ ψ(s) · mTildeIntg(ξ,s)` is `C^∞`. -/
theorem contDiff_mTildeGfun (P : ℤ[X]) (N : ℝ) (j₁ j₂ : ℕ) (n : ℕ∞) :
    ContDiff ℝ n (fun q : (ℝ × ℝ) × ℝ => mTildeGfun P N j₁ j₂ q.1 q.2) := by
  have hPcont : ContDiff ℝ ⊤ (fun t : ℝ => Work.KMTAreas.A7.PevalR P t) := contDiff_PevalR_A6 P
  have hee : ContDiff ℝ n Work.KMTAreas.A7.ee := contDiff_ee_A6 n
  have hP : ContDiff ℝ n (fun q : (ℝ × ℝ) × ℝ => Work.KMTAreas.A7.PevalR P (N * (-q.2))) :=
    hPcont.of_le le_top |>.comp (by fun_prop)
  have hbump : ContDiff ℝ n (fun q : (ℝ × ℝ) × ℝ => ((mTildeBump q.2 : ℝ) : ℂ)) := by
    have h0 : ContDiff ℝ n (fun q : (ℝ × ℝ) × ℝ => mTildeBump q.2) :=
      (ContDiffBump.contDiff mTildeBump (n := n)).comp (by fun_prop)
    have h := (contDiff_ofReal_A6 n).comp h0
    have hfun : ((fun x : ℝ => (x : ℂ)) ∘ (fun q : (ℝ × ℝ) × ℝ => mTildeBump q.2))
        = fun q : (ℝ × ℝ) × ℝ => ((mTildeBump q.2 : ℝ) : ℂ) := rfl
    rw [hfun] at h
    exact h
  have hphase : ContDiff ℝ n (fun q : (ℝ × ℝ) × ℝ =>
      q.1.1 * N * (-q.2) + q.1.2 * Work.KMTAreas.A7.PevalR P (N * (-q.2))) := by
    fun_prop
  have h1 : ContDiff ℝ n (fun q : (ℝ × ℝ) × ℝ =>
      (2 * (Real.pi : ℂ) * Complex.I) * ((N * (-q.2) : ℝ) : ℂ)) := by
    have h := (contDiff_const (c := (2 * (Real.pi : ℂ) * Complex.I))).mul
      ((contDiff_ofReal_A6 n).comp
        (by fun_prop : ContDiff ℝ n (fun q : (ℝ × ℝ) × ℝ => N * (-q.2))))
    simpa [Function.comp_apply] using h
  have h2 : ContDiff ℝ n (fun q : (ℝ × ℝ) × ℝ =>
      (2 * (Real.pi : ℂ) * Complex.I) *
        ((Work.KMTAreas.A7.PevalR P (N * (-q.2)) : ℝ) : ℂ)) := by
    have h := (contDiff_const (c := (2 * (Real.pi : ℂ) * Complex.I))).mul
      ((contDiff_ofReal_A6 n).comp hP)
    simpa [Function.comp_apply] using h
  simp only [mTildeGfun, mTildeIntg]
  simpa only [mul_assoc, Function.comp_apply] using
    (hbump.mul ((hee.comp hphase).mul (h1.pow j₁))).mul (h2.pow j₂)

/-- The uncurried version: `(ξ,s) ↦ ψ(s) mTildeIntg(ξ,s)` is `C^∞`. -/
theorem contDiff_mTildeGfun_uncurry (P : ℤ[X]) (N : ℝ) (j₁ j₂ : ℕ) (n : ℕ∞) :
    ContDiff ℝ n (Function.uncurry (mTildeGfun P N j₁ j₂)) := by
  have h : Function.uncurry (mTildeGfun P N j₁ j₂)
      = fun q : (ℝ × ℝ) × ℝ => mTildeGfun P N j₁ j₂ q.1 q.2 := rfl
  rw [h]
  exact contDiff_mTildeGfun P N j₁ j₂ n

/-- The indicator of an interval is locally integrable. -/
theorem locallyIntegrable_mTildeFfun (a b : ℝ) : LocallyIntegrable (mTildeFfun a b) volume := by
  have h : LocallyIntegrable ((Set.Ioc a b).indicator (fun _ : ℝ => (1 : ℂ))) volume :=
    (locallyIntegrable_const (μ := volume) (1 : ℂ)).indicator measurableSet_Ioc
  simpa [mTildeFfun] using h

/-- **The integral `mTildeDeriv` is the convolution of the interval indicator with the integrand**,
evaluated at `0`.  This is the identity which transfers the smoothness of the convolution (a
Mathlib theorem) to `mTildeDeriv`. -/
theorem conv_eq_mTildeDeriv (P : ℤ[X]) (N : ℕ) (j₁ j₂ : ℕ) (p : ℝ × ℝ) :
    (mTildeFfun (1 / 2) 1 ⋆[mTildeCL, volume] (mTildeGfun P (N : ℝ) j₁ j₂ p)) 0
      = Work.KMTAreas.A7.mTildeDeriv P N p.1 p.2 j₁ j₂ := by
  rw [convolution_def]
  have hpt : ∀ t : ℝ, mTildeCL (mTildeFfun (1 / 2) 1 t)
        (mTildeGfun P (N : ℝ) j₁ j₂ p (0 - t))
      = (Set.Ioc (1 / 2 : ℝ) 1).indicator
          (fun t : ℝ => mTildeGfun P (N : ℝ) j₁ j₂ p (0 - t)) t := by
    intro t
    simp only [mTildeFfun, mTildeCL, ContinuousLinearMap.mul_apply']
    by_cases ht : t ∈ Set.Ioc (1 / 2 : ℝ) 1
    · rw [Set.indicator_of_mem ht, Set.indicator_of_mem ht, one_mul]
    · rw [Set.indicator_of_notMem ht, Set.indicator_of_notMem ht, zero_mul]
  rw [integral_congr_ae (Filter.Eventually.of_forall hpt),
    integral_indicator measurableSet_Ioc]
  rw [← intervalIntegral.integral_of_le (μ := volume) (show (1 / 2 : ℝ) ≤ 1 by norm_num)]
  rw [Work.KMTAreas.A7.mTildeDeriv]
  refine intervalIntegral.integral_congr (fun t ht => ?_)
  have ht' : (1 / 2 : ℝ) ≤ t ∧ t ≤ 1 := by
    have h := ht
    rw [Set.uIcc_of_le (by norm_num : (1 / 2 : ℝ) ≤ 1)] at h
    exact h
  have habs : |t| ≤ 1 := abs_le.mpr ⟨by linarith [ht'.1], ht'.2⟩
  have hmem : (-t) ∈ Metric.closedBall (0 : ℝ) mTildeBump.rIn := by
    rw [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs, abs_neg]
    exact habs
  have hpsi : ((mTildeBump (-t) : ℝ) : ℂ) = 1 := by
    rw [ContDiffBump.one_of_mem_closedBall mTildeBump hmem]
    simp
  simp only [mTildeGfun, mTildeIntg, zero_sub, hpsi, one_mul, neg_neg]

/-- **Every `(ξ₁,ξ₂)`-derivative of `m̃_{N,ℝ}` is `C^n` for every `n`** (the form in which the
induction over the order is clean). -/
theorem mTildeDeriv_contDiff_aux (P : Polynomial ℤ) (N : ℕ) (n : ℕ∞) (j₁ j₂ : ℕ) :
    ContDiff ℝ n (fun p : ℝ × ℝ => Work.KMTAreas.A7.mTildeDeriv P N p.1 p.2 j₁ j₂) := by
  have hg : ContDiffOn ℝ n (Function.uncurry (mTildeGfun P (N : ℝ) j₁ j₂))
      (Set.univ ×ˢ Set.univ) :=
    (contDiff_mTildeGfun_uncurry P (N : ℝ) j₁ j₂ n).contDiffOn
  have hgs : ∀ p : ℝ × ℝ, ∀ x : ℝ, p ∈ Set.univ →
      x ∉ Metric.closedBall (0 : ℝ) 2 → mTildeGfun P (N : ℝ) j₁ j₂ p x = 0 := by
    intro p x _ hx
    have hx' : (2 : ℝ) ≤ dist x (0 : ℝ) := by
      rw [Metric.mem_closedBall, not_le] at hx
      exact le_of_lt hx
    have h0 : ((mTildeBump x : ℝ) : ℂ) = 0 := by
      rw [ContDiffBump.zero_of_le_dist mTildeBump (c := (0 : ℝ)) hx']
      simp
    simp only [mTildeGfun, h0, zero_mul]
  have hmain : ContDiffOn ℝ n
      (fun p : ℝ × ℝ =>
        (mTildeFfun (1 / 2) 1 ⋆[mTildeCL, volume] (mTildeGfun P (N : ℝ) j₁ j₂ p)) 0)
      Set.univ := by
    have h := contDiffOn_convolution_right_with_param_comp (𝕜 := ℝ) (μ := volume)
      (mTildeCL) (s := Set.univ) (v := fun _ : ℝ × ℝ => (0 : ℝ))
      (f := mTildeFfun (1 / 2) 1) (g := mTildeGfun P (N : ℝ) j₁ j₂)
      (k := Metric.closedBall (0 : ℝ) 2)
      (by exact contDiff_const.contDiffOn) isOpen_univ (isCompact_closedBall (0 : ℝ) 2) hgs
      (locallyIntegrable_mTildeFfun _ _) hg
    simpa using h
  have hc : ContDiff ℝ n
      (fun p : ℝ × ℝ =>
        (mTildeFfun (1 / 2) 1 ⋆[mTildeCL, volume] (mTildeGfun P (N : ℝ) j₁ j₂ p)) 0) :=
    contDiffOn_univ.mp hmain
  rw [show (fun p : ℝ × ℝ => Work.KMTAreas.A7.mTildeDeriv P N p.1 p.2 j₁ j₂)
      = (fun p : ℝ × ℝ =>
        (mTildeFfun (1 / 2) 1 ⋆[mTildeCL, volume] (mTildeGfun P (N : ℝ) j₁ j₂ p)) 0) from
      funext (fun p => (conv_eq_mTildeDeriv P N j₁ j₂ p).symm)]
  exact hc

/-- **Every `(ξ₁,ξ₂)`-derivative of the oscillatory integral `m̃_{N,ℝ}` of §6 is `C⁴`.**

`Work.KMTAreas.A7.mTildeDeriv P N ξ₁ ξ₂ j₁ j₂` is the integral over `t ∈ [1/2,1]` of
`ee (ξ₁ * N * t + ξ₂ * P(N t)) * (2πi N t)^{j₁} * (2πi P(N t))^{j₂}`, the formal
`j`-th `(ξ₁,ξ₂)`-derivative of `mTilde P N ξ₁ ξ₂ = ∫ t in (1/2)..1, ee (ξ₁*N*t + ξ₂*P(N*t))`.

The integrand is jointly `C^∞` in `(t,ξ₁,ξ₂)` and every derivative is bounded uniformly on the
compact `t`-interval `[1/2,1]` and on a neighbourhood of the point in `(ξ₁,ξ₂)`; hence the
parametric integral is `C^∞` in `(ξ₁,ξ₂)`, in particular `C^4`.  Suggested route: prove
`HasFDerivAt (fun p : ℝ×ℝ => mTildeDeriv P N p.1 p.2 j₁ j₂)
   (u ↦ u.1 • mTildeDeriv P N p.1 p.2 (j₁+1) j₂ + u.2 • mTildeDeriv P N p.1 p.2 j₁ (j₂+1)) p`
for every `p` via `intervalIntegral.hasFDerivAt_integral_of_dominated_of_fderiv_le`, then proceed by
induction on the order using `contDiff_succ_iff_hasFDerivAt`. -/
theorem mTildeDeriv_family_contDiff (P : Polynomial ℤ) (N : ℕ) :
    ∀ j₁ j₂ : ℕ,
      ContDiff ℝ 4 (fun p : ℝ × ℝ => Work.KMTAreas.A7.mTildeDeriv P N p.1 p.2 j₁ j₂) := by
  intro j₁ j₂
  exact mTildeDeriv_contDiff_aux P N 4 j₁ j₂

end

end Work.KMTPlan.A6
