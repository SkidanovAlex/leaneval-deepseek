import Mathlib
import Submission.Work.LinnikAreas.A5.Basic

namespace Work.LinnikAreas.A5

open Complex intervalIntegral MeasureTheory

/-- Auxiliary computation: `∫₀ᴷ e^{−zt}(K−t) dt = (Kz − 1 + e^{−Kz})/z²` for `z ≠ 0`. -/
lemma integral_sub_mul_exp (K : ℝ) {z : ℂ} (hz : z ≠ 0) :
    ∫ t in (0:ℝ)..K, Complex.exp (-(z * (t:ℂ))) * ((K - t : ℝ) : ℂ)
      = ((K:ℂ)*z - 1 + Complex.exp (-(K:ℂ)*z)) / z^2 := by
  have hderiv : ∀ x ∈ Set.uIcc (0:ℝ) K,
      HasDerivAt (fun t : ℝ => Complex.exp (-(z * (t:ℂ))) * (1 - z * ((K:ℂ) - (t:ℂ))) / z^2)
        (Complex.exp (-(z * (x:ℂ))) * ((K - x : ℝ):ℂ)) x := by
    intro x _
    have hbase : HasDerivAt (fun t : ℝ => (t:ℂ)) 1 x := by
      have h := Complex.ofRealCLM.hasDerivAt (x := x)
      rw [show (⇑Complex.ofRealCLM : ℝ → ℂ) = fun t : ℝ => (t:ℂ) from
        funext fun t => Complex.ofRealCLM_apply t] at h
      simpa using h
    have hlin : HasDerivAt (fun t : ℝ => z * (t:ℂ)) (z * 1) x := hbase.const_mul z
    have hneg : HasDerivAt (fun t : ℝ => -(z * (t:ℂ))) (-(z * 1)) x := hlin.neg
    have hexp : HasDerivAt (fun t : ℝ => Complex.exp (-(z*(t:ℂ))))
        (Complex.exp (-(z*(x:ℂ))) * (-(z*1))) x :=
      (Complex.hasDerivAt_exp (-(z*(x:ℂ)))).comp x hneg
    have hKsub : HasDerivAt (fun t : ℝ => (K:ℂ) - (t:ℂ)) (-1) x := hbase.const_sub (K:ℂ)
    have hzKsub : HasDerivAt (fun t : ℝ => z * ((K:ℂ) - (t:ℂ))) (z * (-1)) x := hKsub.const_mul z
    have hone : HasDerivAt (fun t : ℝ => 1 - z * ((K:ℂ) - (t:ℂ))) (-(z * (-1))) x :=
      hzKsub.const_sub 1
    have hprod := hexp.mul hone
    have hd := hprod.div_const (z^2)
    refine hd.congr_deriv ?_
    push_cast
    field_simp
    ring
  have hint : IntervalIntegrable (fun t : ℝ => Complex.exp (-(z * (t:ℂ))) * ((K - t : ℝ) : ℂ))
      volume (0:ℝ) K := by
    apply Continuous.intervalIntegrable
    fun_prop
  rw [integral_eq_sub_of_hasDerivAt hderiv hint]
  have hKend : Complex.exp (-(z * (K:ℂ))) * (1 - z * ((K:ℂ) - (K:ℂ))) / z^2
      = Complex.exp (-(z*(K:ℂ))) / z^2 := by ring
  have h0end : Complex.exp (-(z * ((0:ℝ):ℂ))) * (1 - z * ((K:ℂ) - ((0:ℝ):ℂ))) / z^2
      = (1 - (K:ℂ)*z) / z^2 := by
    simp only [Complex.ofReal_zero, mul_zero, neg_zero, Complex.exp_zero]
    ring
  rw [hKend, h0end]
  field_simp
  ring

/-- `G0 K` is the Laplace transform `z ↦ ∫₀ᴷ e^{−zt} (K−t)/K dt` of `g0 K t = (K−t)/K`
(`Work.LinnikAreas.A5.G0`, `Work.LinnikAreas.A5.g0` in `Submission/Work/LinnikAreas/A5/Basic.lean`).
Its closed form is `(Kz − 1 + e^{−Kz})/(K z²)` for `z ≠ 0` (note this expression is the analytic
continuation across `z = 0`, where its limit is `K/2`, but at `z = 0` the Lean expression is `0/0`),
and its value at `z = 0` is `∫₀ᴷ g0 = K/2`. -/
theorem G0_closed (K : ℝ) (hK : 0 < K) :
    (∀ z : ℂ, z ≠ 0 →
      Work.LinnikAreas.A5.G0 K z =
        ((K : ℂ) * z - 1 + Complex.exp (-(K : ℂ) * z)) / ((K : ℂ) * z ^ 2)) ∧
    Work.LinnikAreas.A5.G0 K 0 = (K : ℂ) / 2 := by
  constructor
  · intro z hz
    unfold G0
    have hcongr : (∫ t in (0:ℝ)..K, Complex.exp (-(z * (t:ℂ))) * ((g0 K t : ℝ) : ℂ))
        = ∫ t in (0:ℝ)..K, Complex.exp (-(z * (t:ℂ))) * (((K - t)/K : ℝ) : ℂ) := by
      apply intervalIntegral.integral_congr
      intro t ht
      rw [Set.uIcc_of_le hK.le] at ht
      dsimp only
      rw [g0_of_le ht.2]
    rw [hcongr]
    have h2 : (∫ t in (0:ℝ)..K, Complex.exp (-(z * (t:ℂ))) * (((K - t)/K : ℝ) : ℂ))
        = (1/(K:ℂ)) * ∫ t in (0:ℝ)..K, Complex.exp (-(z * (t:ℂ))) * ((K - t : ℝ) : ℂ) := by
      rw [← intervalIntegral.integral_const_mul]
      apply intervalIntegral.integral_congr
      intro t ht
      push_cast
      ring
    rw [h2, integral_sub_mul_exp K hz]
    field_simp
  · unfold G0
    have hcongr : (∫ t in (0:ℝ)..K, Complex.exp (-((0:ℂ) * (t:ℂ))) * ((g0 K t : ℝ) : ℂ))
        = ∫ t in (0:ℝ)..K, (((K - t)/K : ℝ) : ℂ) := by
      apply intervalIntegral.integral_congr
      intro t ht
      rw [Set.uIcc_of_le hK.le] at ht
      dsimp only
      rw [g0_of_le ht.2]
      simp
    rw [hcongr, intervalIntegral.integral_ofReal]
    have hreal : ∫ t in (0:ℝ)..K, (K - t)/K = K/2 := by
      have hd : ∀ x ∈ Set.uIcc (0:ℝ) K,
          HasDerivAt (fun t : ℝ => (K*t - t^2/2)/K) ((K - x)/K) x := by
        intro x _
        have h1 : HasDerivAt (fun t : ℝ => K * t) (K * 1) x := (hasDerivAt_id x).const_mul K
        have h2 : HasDerivAt (fun t : ℝ => t^2/2) ((2 * x^(2-1) * 1)/2) x :=
          ((hasDerivAt_id x).pow 2).div_const 2
        have h := (h1.sub h2).div_const K
        refine h.congr_deriv ?_
        ring_nf
      have hint : IntervalIntegrable (fun t : ℝ => (K - t)/K) volume (0:ℝ) K := by
        apply Continuous.intervalIntegrable
        fun_prop
      rw [integral_eq_sub_of_hasDerivAt hd hint]
      field_simp
      ring
    rw [hreal]
    push_cast
    ring

end Work.LinnikAreas.A5
