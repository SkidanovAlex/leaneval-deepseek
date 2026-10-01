import Mathlib
import Submission.Work.ZeroDensity.Montgomery.mvtDefs
import Submission.Work.ZeroDensity.Montgomery.mvtThetaFourierFormula

open MeasureTheory
open scoped FourierTransform Convolution ContDiff
open Work.ZeroDensity.Montgomery

/-!
# The spreading bound `mvtSpread`

`mvtSpread` bounds the mean square `∫_{-S}^{S} ‖∑_{n ≤ N} a n · e(-2πi s log n)‖² ds` of a
Dirichlet polynomial by the "spread" quadratic form built from the spreading kernel `Θ_S`
(`mvtTheta`) of `mvtDefs`.

The argument is the classical Fourier/spreading proof:

1. `mvtThetaFourierFormula`: `𝓕 Θ_δ (ξ) = ‖ψ (δ ξ)‖²`, where `ψ = 𝓕 ρ`.  In particular
   `𝓕 Θ_δ ≥ C²` on `[-S, S]` because `δ S = E` and `‖ψ‖ ≥ C` on `[-E, E]`.
2. `mvt_expansion`: expanding `‖∑ a n e(-2πi s log n)‖²` and integrating term by term against
   `𝓕 Θ_δ` (via the Fourier inversion identity `integralFourierMulExp`) turns the integral of
   `𝓕 Θ_δ ‖·‖²` over `ℝ` into the quadratic form `∑_{m,n} a m · conj (a n) · Θ_δ (log (n/m))`.
3. The pointwise bound `mvtC ^ 2 ≤ 𝓕 Θ_δ` on `[-S,S]`, positivity of `𝓕 Θ_δ`, and
   `∫_{-S}^{S} ≤ ∫_{ℝ}` finish the proof.
-/

set_option maxHeartbeats 1000000

namespace Work.ZeroDensity.Montgomery

noncomputable section

/-- `exp(2πi w s)`, the additive character used for the exponential sums. -/
def mvtChar (w s : ℝ) : ℂ := Complex.exp (2 * Real.pi * Complex.I * (s : ℂ) * (w : ℂ))

lemma E_norm (w s : ℝ) : ‖mvtChar w s‖ = 1 := by
  simp only [mvtChar]
  rw [show 2 * Real.pi * Complex.I * (s:ℂ) * (w:ℂ) = ((2 * Real.pi * s * w : ℝ) : ℂ) * Complex.I
      from by push_cast; ring]
  exact Complex.norm_exp_ofReal_mul_I _

lemma mvtChar_cont (w : ℝ) : Continuous (fun s : ℝ => mvtChar w s) := by
  simp only [mvtChar]
  exact Complex.continuous_exp.comp (by fun_prop)

lemma E_norm_neg (l s : ℝ) : ‖Complex.exp (-(2 * Real.pi * Complex.I * (s:ℂ) * (l:ℂ)))‖ = 1 := by
  rw [show -(2 * Real.pi * Complex.I * (s:ℂ) * (l:ℂ)) = ((2 * Real.pi * s * (-l) : ℝ) : ℂ) * Complex.I
      from by push_cast; ring]
  exact Complex.norm_exp_ofReal_mul_I _

lemma norm_ofReal_eq_abs (r : ℝ) : ‖((r : ℝ) : ℂ)‖ = |r| := RCLike.norm_ofReal r

lemma starExpNeg (s l : ℝ) :
    star (Complex.exp (-(2 * Real.pi * Complex.I * (s : ℂ) * (l : ℂ)))) = mvtChar l s := by
  simp only [mvtChar]
  have h1 : star (Complex.exp (-(2 * Real.pi * Complex.I * (s : ℂ) * (l : ℂ))))
      = Complex.exp ((starRingEnd ℂ) (-(2 * Real.pi * Complex.I * (s : ℂ) * (l : ℂ)))) :=
    (Complex.exp_conj _).symm
  rw [h1]
  congr 1
  rw [map_neg]
  have key : (starRingEnd ℂ) (2 * Real.pi * Complex.I * (s : ℂ) * (l : ℂ))
      = -(2 * Real.pi * Complex.I * (s : ℂ) * (l : ℂ)) := by
    rw [show (2 : ℂ) * Real.pi * Complex.I * (s : ℂ) * (l : ℂ)
        = (((2 * Real.pi * s * l : ℝ)) : ℂ) * Complex.I from by push_cast; ring]
    rw [map_mul, Complex.conj_I, Complex.conj_ofReal]
    ring
  rw [key, neg_neg]

lemma expNegMulExp (A B : ℂ) : Complex.exp (-A) * Complex.exp B = Complex.exp (B - A) := by
  rw [← Complex.exp_add]; congr 1; ring

lemma term_eq (a b : ℂ) (x y s : ℝ) :
    (a * Complex.exp (-(2 * Real.pi * Complex.I * (s:ℂ) * (x:ℂ))))
      * star (b * Complex.exp (-(2 * Real.pi * Complex.I * (s:ℂ) * (y:ℂ))))
    = a * star b * mvtChar (y - x) s := by
  rw [star_mul, starExpNeg]
  simp only [mvtChar]
  rw [show (a * Complex.exp (-(2 * Real.pi * Complex.I * (s:ℂ) * (x:ℂ))))
      * (Complex.exp (2 * Real.pi * Complex.I * (s:ℂ) * (y:ℂ)) * star b)
      = a * star b * (Complex.exp (-(2 * Real.pi * Complex.I * (s:ℂ) * (x:ℂ)))
        * Complex.exp (2 * Real.pi * Complex.I * (s:ℂ) * (y:ℂ))) from by ring]
  rw [expNegMulExp]
  congr 1
  rw [Complex.ofReal_sub]
  ring

lemma normSqDoubleSumExp (a : ℕ → ℂ) (N : ℕ) (s : ℝ) :
    (‖∑ n ∈ Finset.Icc 1 N, a n * Complex.exp (-(2 * Real.pi * Complex.I * (s : ℂ) * (Real.log (n : ℝ) : ℂ)))‖ ^ 2 : ℂ)
      = ∑ m ∈ Finset.Icc 1 N, ∑ n ∈ Finset.Icc 1 N,
          a m * star (a n) * mvtChar (Real.log (n : ℝ) - Real.log (m : ℝ)) s := by
  have hsq : (‖(∑ n ∈ Finset.Icc 1 N, a n * Complex.exp (-(2 * Real.pi * Complex.I * (s : ℂ) * (Real.log (n : ℝ) : ℂ))))‖ ^ 2 : ℂ)
      = (∑ n ∈ Finset.Icc 1 N, a n * Complex.exp (-(2 * Real.pi * Complex.I * (s : ℂ) * (Real.log (n : ℝ) : ℂ))))
        * star (∑ n ∈ Finset.Icc 1 N, a n * Complex.exp (-(2 * Real.pi * Complex.I * (s : ℂ) * (Real.log (n : ℝ) : ℂ)))) := by
    rw [← Complex.ofReal_pow,
      show (‖(∑ n ∈ Finset.Icc 1 N, a n * Complex.exp (-(2 * Real.pi * Complex.I * (s : ℂ) * (Real.log (n : ℝ) : ℂ))))‖ ^ 2 : ℝ)
        = Complex.normSq (∑ n ∈ Finset.Icc 1 N, a n * Complex.exp (-(2 * Real.pi * Complex.I * (s : ℂ) * (Real.log (n : ℝ) : ℂ)))) from (Complex.normSq_eq_norm_sq _).symm]
    exact (Complex.mul_conj _).symm
  rw [hsq, star_sum, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl (fun m hm => ?_)
  refine Finset.sum_congr rfl (fun n hn => ?_)
  exact term_eq (a m) (a n) (Real.log (m:ℝ)) (Real.log (n:ℝ)) s

lemma integralFourierMulExp (Θ : ℝ → ℂ) (hΘc : Continuous Θ) (hΘi : Integrable Θ)
    (hhat : Integrable (𝓕 Θ)) (w : ℝ) :
    ∫ s : ℝ, (𝓕 Θ) s * mvtChar w s = Θ w := by
  have h := Continuous.fourierInv_fourier_eq hΘc hΘi hhat
  have hw := congrFun h w
  rw [Real.fourierInv_eq'] at hw
  rw [← hw]
  refine integral_congr_ae (Filter.Eventually.of_forall fun s => ?_)
  show (𝓕 Θ) s * mvtChar w s = Complex.exp (↑(2 * Real.pi * inner ℝ s w) * Complex.I) • (𝓕 Θ) s
  have harg : (↑(2 * Real.pi * inner ℝ s w) * Complex.I : ℂ)
      = 2 * Real.pi * Complex.I * (s:ℂ) * (w:ℂ) := by
    rw [Real.inner_apply]; push_cast; ring
  simp only [mvtChar]
  rw [smul_eq_mul, harg]
  exact mul_comm _ _

lemma cdiff_rho : ContDiff ℝ (∞ : ℕ∞ω) mvtRho := mvtRho_contDiff (⊤ : ℕ∞)

lemma cdiff_rhoC : ContDiff ℝ (∞ : ℕ∞ω) mvtRhoC := by
  have h2 := (Complex.ofRealCLM.contDiff (n := (∞ : ℕ∞ω))).comp cdiff_rho
  convert h2 using 1
  ext x; rfl

lemma cdiff_rhoDelta (S : ℝ) (hS : 0 < S) : ContDiff ℝ (∞ : ℕ∞ω) (mvtRhoDeltaC S) := by
  show ContDiff ℝ (∞ : ℕ∞ω)
    (fun y : ℝ => ((mvtDelta S)⁻¹ : ℝ) * mvtRhoC (y / mvtDelta S))
  have h1 : ContDiff ℝ (∞ : ℕ∞ω) (fun y : ℝ => y / mvtDelta S) := contDiff_id.div_const _
  exact contDiff_const.mul (cdiff_rhoC.comp h1)

lemma hcs_theta (S : ℝ) (hS : 0 < S) : HasCompactSupport (mvtTheta S) := by
  rw [HasCompactSupport, tsupport]
  have hsupp : Function.support (mvtTheta S) ⊆
      Set.Icc (-(2 * mvtBump.rOut * mvtDelta S)) (2 * mvtBump.rOut * mvtDelta S) := by
    intro x hx
    rw [Set.mem_Icc, ← abs_le]
    by_contra h
    rw [not_le] at h
    exact hx (mvtTheta_support S hS h)
  exact IsCompact.of_isClosed_subset isCompact_Icc isClosed_closure
    (closure_minimal hsupp isClosed_Icc)

lemma conv_eq (S : ℝ) :
    mvtTheta S = mvtRhoDeltaC S ⋆[ContinuousLinearMap.mul ℝ ℂ, volume]
      (fun y => star (mvtRhoDeltaC S (-y))) := by
  rw [mvtTheta]
  funext x
  simp only [convolution_def, ContinuousLinearMap.mul_apply']

lemma cdiff_theta (S : ℝ) (hS : 0 < S) : ContDiff ℝ (∞ : ℕ∞ω) (mvtTheta S) := by
  have hrefl_cont : Continuous (fun y : ℝ => star (mvtRhoDeltaC S (-y))) :=
    (mvtRhoDeltaC_continuous S).star.comp continuous_neg
  rw [conv_eq S]
  exact HasCompactSupport.contDiff_convolution_left (ContinuousLinearMap.mul ℝ ℂ) (n := ⊤)
    (mvtRhoDeltaC_hasCompactSupport S hS) (cdiff_rhoDelta S hS) hrefl_cont.locallyIntegrable

lemma cont_theta (S : ℝ) (hS : 0 < S) : Continuous (mvtTheta S) :=
  (cdiff_theta S hS).continuous

lemma intble_theta (S : ℝ) (hS : 0 < S) : Integrable (mvtTheta S) :=
  (cont_theta S hS).integrable_of_hasCompactSupport (hcs_theta S hS)

lemma intble_fourier_theta (S : ℝ) (hS : 0 < S) : Integrable (𝓕 (mvtTheta S)) := by
  have h2 : Integrable (⇑(FourierTransform.fourier
      (HasCompactSupport.toSchwartzMap (hcs_theta S hS) (cdiff_theta S hS))) : ℝ → ℂ) volume :=
    SchwartzMap.integrable (FourierTransform.fourier
      (HasCompactSupport.toSchwartzMap (hcs_theta S hS) (cdiff_theta S hS))) (μ := volume)
  rw [SchwartzMap.fourier_coe] at h2
  exact h2

lemma hInt_w (S : ℝ) (hS : 0 < S) (w : ℝ) :
    Integrable (fun s : ℝ => (𝓕 (mvtTheta S)) s * mvtChar w s) := by
  have hbdd : ∀ᵐ s : ℝ, ‖mvtChar w s‖ ≤ (1:ℝ) := by
    filter_upwards with s; rw [E_norm]
  exact Integrable.mul_bdd (c := 1) (intble_fourier_theta S hS)
    (mvtChar_cont w).aestronglyMeasurable hbdd

lemma mvt_expansion (S : ℝ) (hS : 0 < S) (a : ℕ → ℂ) (N : ℕ) :
    ∫ s : ℝ, (𝓕 (mvtTheta S)) s * (‖∑ n ∈ Finset.Icc 1 N, a n * Complex.exp (-(2 * Real.pi * Complex.I * (s : ℂ) * (Real.log (n : ℝ) : ℂ)))‖ ^ 2 : ℂ)
      = ∑ m ∈ Finset.Icc 1 N, ∑ n ∈ Finset.Icc 1 N,
          a m * star (a n) * mvtTheta S (Real.log ((n : ℝ) / (m : ℝ))) := by
  have hΘc := cont_theta S hS
  have hΘi := intble_theta S hS
  have hhat := intble_fourier_theta S hS
  have hExp : ∀ s : ℝ, (𝓕 (mvtTheta S)) s *
        (‖∑ n ∈ Finset.Icc 1 N, a n * Complex.exp (-(2 * Real.pi * Complex.I * (s : ℂ) * (Real.log (n : ℝ) : ℂ)))‖ ^ 2 : ℂ)
      = ∑ m ∈ Finset.Icc 1 N, ∑ n ∈ Finset.Icc 1 N,
          (a m * star (a n)) * ((𝓕 (mvtTheta S)) s * mvtChar (Real.log (n : ℝ) - Real.log (m : ℝ)) s) := by
    intro s
    rw [normSqDoubleSumExp a N s, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun m hm => ?_)
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun n hn => ?_)
    ring
  simp_rw [hExp]
  have hFint1 : ∀ m ∈ Finset.Icc 1 N, Integrable (fun s : ℝ => ∑ n ∈ Finset.Icc 1 N,
      a m * star (a n) * ((𝓕 (mvtTheta S)) s * mvtChar (Real.log (n : ℝ) - Real.log (m : ℝ)) s)) := by
    intro m hm
    exact integrable_finsetSum (Finset.Icc 1 N) (fun n hn =>
      (hInt_w S hS (Real.log (n:ℝ) - Real.log (m:ℝ))).const_mul (a m * star (a n)))
  rw [integral_finsetSum (Finset.Icc 1 N) hFint1]
  refine Finset.sum_congr rfl (fun m hm => ?_)
  have hFint2 : ∀ n ∈ Finset.Icc 1 N, Integrable (fun s : ℝ =>
      a m * star (a n) * ((𝓕 (mvtTheta S)) s * mvtChar (Real.log (n : ℝ) - Real.log (m : ℝ)) s)) := by
    intro n hn
    exact (hInt_w S hS (Real.log (n:ℝ) - Real.log (m:ℝ))).const_mul (a m * star (a n))
  rw [integral_finsetSum (Finset.Icc 1 N) hFint2]
  refine Finset.sum_congr rfl (fun n hn => ?_)
  rw [integral_const_mul]
  congr 1
  rw [integralFourierMulExp (mvtTheta S) hΘc hΘi hhat (Real.log (n:ℝ) - Real.log (m:ℝ))]
  have hn0 : (n : ℝ) ≠ 0 := by
    have : (1:ℝ) ≤ (n:ℝ) := by exact_mod_cast (Finset.mem_Icc.mp hn).1
    linarith
  have hm0 : (m : ℝ) ≠ 0 := by
    have : (1:ℝ) ≤ (m:ℝ) := by exact_mod_cast (Finset.mem_Icc.mp hm).1
    linarith
  rw [Real.log_div hn0 hm0]

theorem mvtSpread (S : ℝ) (hS : 1 ≤ S) (a : ℕ → ℂ) (N : ℕ) :
    (∫ s in (-S)..S, ‖∑ n ∈ Finset.Icc 1 N,
        a n * Complex.exp (-(2 * Real.pi * Complex.I * (s : ℂ) * (Real.log (n : ℝ) : ℂ)))‖ ^ 2)
      ≤ (mvtC ^ 2)⁻¹ * ‖∑ m ∈ Finset.Icc 1 N, ∑ n ∈ Finset.Icc 1 N,
          a m * star (a n) * mvtTheta S (Real.log ((n : ℝ) / (m : ℝ)))‖ := by
  have hS0 : 0 < S := by linarith
  have hC2pos : 0 < mvtC ^ 2 := pow_pos mvtC_pos 2
  set T : ℂ := ∑ m ∈ Finset.Icc 1 N, ∑ n ∈ Finset.Icc 1 N,
          a m * star (a n) * mvtTheta S (Real.log ((n : ℝ) / (m : ℝ))) with hT
  set G : ℝ → ℝ := fun s => ‖mvtPsi (mvtDelta S * s)‖ ^ 2 with hG
  have hGcont : Continuous G := by
    rw [hG]
    exact (mvtPsi_continuous.comp (continuous_const.mul continuous_id)).norm.pow 2
  have hformula : ∀ ξ : ℝ, (𝓕 (mvtTheta S)) ξ = ((G ξ : ℝ) : ℂ) := by
    intro ξ; rw [hG]; exact mvtThetaFourierFormula S hS0 ξ
  have hident : ∫ s : ℝ, (𝓕 (mvtTheta S)) s *
        (‖∑ n ∈ Finset.Icc 1 N, a n * Complex.exp (-(2 * Real.pi * Complex.I * (s : ℂ) * (Real.log (n : ℝ) : ℂ)))‖ ^ 2 : ℂ) = T := by
    rw [hT]
    exact mvt_expansion S hS0 a N
  have hreal : ∫ s : ℝ, (𝓕 (mvtTheta S)) s *
        (‖∑ n ∈ Finset.Icc 1 N, a n * Complex.exp (-(2 * Real.pi * Complex.I * (s : ℂ) * (Real.log (n : ℝ) : ℂ)))‖ ^ 2 : ℂ)
      = ((∫ s : ℝ, G s * ‖∑ n ∈ Finset.Icc 1 N, a n * Complex.exp (-(2 * Real.pi * Complex.I * (s : ℂ) * (Real.log (n : ℝ) : ℂ)))‖ ^ 2 : ℝ) : ℂ) := by
    have h1 : ∫ s : ℝ, (𝓕 (mvtTheta S)) s *
          (‖∑ n ∈ Finset.Icc 1 N, a n * Complex.exp (-(2 * Real.pi * Complex.I * (s : ℂ) * (Real.log (n : ℝ) : ℂ)))‖ ^ 2 : ℂ)
        = ∫ s : ℝ, ((G s * ‖∑ n ∈ Finset.Icc 1 N, a n * Complex.exp (-(2 * Real.pi * Complex.I * (s : ℂ) * (Real.log (n : ℝ) : ℂ)))‖ ^ 2 : ℝ) : ℂ) := by
      refine integral_congr_ae (Filter.Eventually.of_forall fun s => ?_)
      simp only []
      rw [hformula s]
      push_cast
      ring
    rw [h1]
    exact integral_ofReal
  have hTeq : T = ((∫ s : ℝ, G s * ‖∑ n ∈ Finset.Icc 1 N, a n * Complex.exp (-(2 * Real.pi * Complex.I * (s : ℂ) * (Real.log (n : ℝ) : ℂ)))‖ ^ 2 : ℝ) : ℂ) :=
    hident.symm.trans hreal
  have hTnorm : ‖T‖ = ∫ s : ℝ, G s * ‖∑ n ∈ Finset.Icc 1 N, a n * Complex.exp (-(2 * Real.pi * Complex.I * (s : ℂ) * (Real.log (n : ℝ) : ℂ)))‖ ^ 2 := by
    have hnn : 0 ≤ (∫ s : ℝ, G s * ‖∑ n ∈ Finset.Icc 1 N, a n * Complex.exp (-(2 * Real.pi * Complex.I * (s : ℂ) * (Real.log (n : ℝ) : ℂ)))‖ ^ 2) :=
      integral_nonneg (fun s => by rw [hG]; exact mul_nonneg (sq_nonneg _) (sq_nonneg _))
    rw [hTeq, norm_ofReal_eq_abs]
    exact abs_of_nonneg hnn
  have hFcont : Continuous (fun s : ℝ => ∑ n ∈ Finset.Icc 1 N,
      a n * Complex.exp (-(2 * Real.pi * Complex.I * (s : ℂ) * (Real.log (n : ℝ) : ℂ)))) :=
    continuous_finsetSum _ (fun n hn => continuous_const.mul (Complex.continuous_exp.comp (by fun_prop)))
  have hFbound : ∀ x : ℝ, ‖∑ n ∈ Finset.Icc 1 N, a n * Complex.exp (-(2 * Real.pi * Complex.I * (x : ℂ) * (Real.log (n : ℝ) : ℂ)))‖ ≤ ∑ n ∈ Finset.Icc 1 N, ‖a n‖ := by
    intro x
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum (fun n hn => ?_))
    rw [norm_mul, E_norm_neg, mul_one]
  have hGint : Integrable G := by
    have h1 : Integrable (fun x : ℝ => RCLike.re ((𝓕 (mvtTheta S)) x)) := (intble_fourier_theta S hS0).re
    have h2 : (fun x : ℝ => RCLike.re ((𝓕 (mvtTheta S)) x)) = G := by
      funext x
      rw [hformula x]
      simp
    rwa [h2] at h1
  have hInt : Integrable (fun x : ℝ => G x * ‖∑ n ∈ Finset.Icc 1 N, a n * Complex.exp (-(2 * Real.pi * Complex.I * (x : ℂ) * (Real.log (n : ℝ) : ℂ)))‖ ^ 2) := by
    have hb : ∀ᵐ x : ℝ, ‖‖∑ n ∈ Finset.Icc 1 N, a n * Complex.exp (-(2 * Real.pi * Complex.I * (x : ℂ) * (Real.log (n : ℝ) : ℂ)))‖ ^ 2‖ ≤ (∑ n ∈ Finset.Icc 1 N, ‖a n‖)^2 := by
      filter_upwards with x
      rw [Real.norm_of_nonneg (sq_nonneg _)]
      exact pow_le_pow_left₀ (norm_nonneg _) (hFbound x) 2
    exact Integrable.mul_bdd (c := (∑ n ∈ Finset.Icc 1 N, ‖a n‖)^2) hGint
      ((hFcont.norm.pow 2).aestronglyMeasurable) hb
  have hGL : ∀ x ∈ Set.Icc (-S) S, mvtC ^ 2 ≤ G x := by
    intro x hx
    have hx' : |x| ≤ S := by rw [abs_le]; exact ⟨hx.1, hx.2⟩
    have hδpos : 0 < mvtDelta S := mvtDelta_pos hS0
    have h1 : |mvtDelta S * x| ≤ mvtE := by
      rw [abs_mul, abs_of_pos hδpos]
      calc mvtDelta S * |x| ≤ mvtDelta S * S := mul_le_mul_of_nonneg_left hx' (le_of_lt hδpos)
        _ = mvtE := by rw [mvtDelta, div_mul_cancel₀ _ (ne_of_gt hS0)]
    have h2 : mvtC ≤ ‖mvtPsi (mvtDelta S * x)‖ := mvtE_bound _ h1
    have h3 : mvtC ^ 2 ≤ ‖mvtPsi (mvtDelta S * x)‖ ^ 2 := pow_le_pow_left₀ (le_of_lt mvtC_pos) h2 2
    rw [hG]
    exact h3
  rw [hTnorm]
  calc ∫ x in (-S)..S, ‖∑ n ∈ Finset.Icc 1 N, a n * Complex.exp (-(2 * Real.pi * Complex.I * (x : ℂ) * (Real.log (n : ℝ) : ℂ)))‖ ^ 2
      ≤ ∫ x in (-S)..S, (mvtC ^ 2)⁻¹ * (G x * ‖∑ n ∈ Finset.Icc 1 N, a n * Complex.exp (-(2 * Real.pi * Complex.I * (x : ℂ) * (Real.log (n : ℝ) : ℂ)))‖ ^ 2) := by
        refine intervalIntegral.integral_mono_on (by linarith) ?_ ?_ ?_
        · exact (hFcont.norm.pow 2).intervalIntegrable _ _
        · exact (continuous_const.mul (hGcont.mul (hFcont.norm.pow 2))).intervalIntegrable _ _
        · intro x hx
          have hpos : 0 < mvtC ^ 2 := hC2pos
          have h1 : 1 ≤ (mvtC ^ 2)⁻¹ * G x := by
            rw [← div_eq_inv_mul]
            exact (one_le_div hpos).mpr (hGL x hx)
          calc ‖∑ n ∈ Finset.Icc 1 N, a n * Complex.exp (-(2 * Real.pi * Complex.I * (x : ℂ) * (Real.log (n : ℝ) : ℂ)))‖ ^ 2
              = 1 * ‖∑ n ∈ Finset.Icc 1 N, a n * Complex.exp (-(2 * Real.pi * Complex.I * (x : ℂ) * (Real.log (n : ℝ) : ℂ)))‖ ^ 2 := by ring
            _ ≤ ((mvtC ^ 2)⁻¹ * G x) * ‖∑ n ∈ Finset.Icc 1 N, a n * Complex.exp (-(2 * Real.pi * Complex.I * (x : ℂ) * (Real.log (n : ℝ) : ℂ)))‖ ^ 2 :=
                mul_le_mul_of_nonneg_right h1 (sq_nonneg _)
            _ = (mvtC ^ 2)⁻¹ * (G x * ‖∑ n ∈ Finset.Icc 1 N, a n * Complex.exp (-(2 * Real.pi * Complex.I * (x : ℂ) * (Real.log (n : ℝ) : ℂ)))‖ ^ 2) := by ring
    _ = (mvtC ^ 2)⁻¹ * ∫ x in (-S)..S, G x * ‖∑ n ∈ Finset.Icc 1 N, a n * Complex.exp (-(2 * Real.pi * Complex.I * (x : ℂ) * (Real.log (n : ℝ) : ℂ)))‖ ^ 2 :=
        intervalIntegral.integral_const_mul _ _
    _ ≤ (mvtC ^ 2)⁻¹ * ∫ x : ℝ, G x * ‖∑ n ∈ Finset.Icc 1 N, a n * Complex.exp (-(2 * Real.pi * Complex.I * (x : ℂ) * (Real.log (n : ℝ) : ℂ)))‖ ^ 2 := by
        refine mul_le_mul_of_nonneg_left ?_ (le_of_lt (inv_pos.mpr hC2pos))
        rw [intervalIntegral.integral_of_le (by linarith : -S ≤ S)]
        exact setIntegral_le_integral hInt (Filter.Eventually.of_forall fun x => by
          rw [hG]; exact mul_nonneg (sq_nonneg _) (sq_nonneg _))


end

end Work.ZeroDensity.Montgomery
