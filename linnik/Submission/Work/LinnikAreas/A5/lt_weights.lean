import Mathlib
import Submission.Work.LinnikAreas.A5.Weights

namespace Work.LinnikAreas.A5

/-
The Laplace transforms of the two test functions, in the form needed to identify the "zero sum"
of HB's smoothing estimate with the box sum of HB Lemma 13.3: the integral over `(0,K)` of
`e^{-zt} f(t)` is `(sinh (K*lam))⁻¹ * F1 K lam z` for the normalised weight `f = wc K lam`, and
`G0 K z` for the endpoint weight `f = gc K`.  (`F1 K lam z = ∫₀^K e^{-zt} sinh((K-t)λ) dt` and
`G0 K z = ∫₀^K e^{-zt}(K-t)/K dt` by definition; on `(0,K)` the cut-off weights agree with the
smooth branches, which both sides of each identity only see through the integral over `(0,K)`.)
-/

/-- The Laplace transform of the normalised weight `wc K lam` over `(0,K)`: both `wc K lam` and
`f1 K lam` agree on `(0,K)` with the smooth branch `sinh((K-t)λ)`, so the integral of `e^{-zt}`
against `wc` is just `(sinh (Kλ))⁻¹` times the integral against `f1`, i.e. `(sinh (Kλ))⁻¹ · F1`. -/
lemma integral_exp_mul_wc (K lam : ℝ) (hK : 0 < K) (z : ℂ) :
    (∫ t in (0:ℝ)..K, Complex.exp (-(z * (t : ℂ))) * ((wc K lam t : ℝ) : ℂ))
      = ((Real.sinh (K * lam))⁻¹ : ℂ) * F1 K lam z := by
  rw [F1]
  rw [show (∫ t in (0:ℝ)..K, Complex.exp (-(z * (t : ℂ))) * ((wc K lam t : ℝ) : ℂ))
      = ∫ t in (0:ℝ)..K, ((Real.sinh (K * lam))⁻¹ : ℂ) *
          (Complex.exp (-(z * (t : ℂ))) * ((f1 K lam t : ℝ) : ℂ)) from ?_]
  · rw [intervalIntegral.integral_const_mul]
  · refine intervalIntegral.integral_congr (fun t ht => ?_)
    have h0 : 0 ≤ t := (Set.uIcc_of_le hK.le ▸ ht).1
    rw [wc_of_nonneg h0, Complex.ofReal_mul, Complex.ofReal_inv]
    ring

/-- The Laplace transform of the endpoint weight `gc K` over `(0,K)`: on `(0,K)` the cut-off
`gc K` and the smooth branch `g0 K = (K-t)/K` agree, so the integral of `e^{-zt}` against `gc`
is by definition `G0 K z`. -/
lemma integral_exp_mul_gc (K : ℝ) (hK : 0 < K) (z : ℂ) :
    (∫ t in (0:ℝ)..K, Complex.exp (-(z * (t : ℂ))) * ((gc K t : ℝ) : ℂ)) = G0 K z := by
  rw [G0]
  refine intervalIntegral.integral_congr (fun t ht => ?_)
  have h0 : 0 ≤ t := (Set.uIcc_of_le hK.le ▸ ht).1
  have hKt : t ≤ K := (Set.uIcc_of_le hK.le ▸ ht).2
  rw [gc_of_mem h0 hKt, g0_of_le hKt]

theorem lt_weights (K lam : ℝ) (hK : 0 < K) (hlam : 0 < lam) :
    (∀ z : ℂ, (∫ t in (0:ℝ)..K, Complex.exp (-(z * (t : ℂ))) *
        ((Work.LinnikAreas.A5.wc K lam t : ℝ) : ℂ))
      = ((Real.sinh (K * lam))⁻¹ : ℂ) * Work.LinnikAreas.A5.F1 K lam z) ∧
    (∀ z : ℂ, (∫ t in (0:ℝ)..K, Complex.exp (-(z * (t : ℂ))) *
        ((Work.LinnikAreas.A5.gc K t : ℝ) : ℂ))
      = Work.LinnikAreas.A5.G0 K z) := by
  have hlam' : (0 : ℝ) < lam := hlam
  exact ⟨fun z => integral_exp_mul_wc K lam hK z, fun z => integral_exp_mul_gc K hK z⟩

end Work.LinnikAreas.A5
