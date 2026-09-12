import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Analysis.Calculus.Deriv.Support

namespace Commons.Analysis.Real

open MeasureTheory Set Filter

theorem integral_Ioi_deriv_mul_pow_boundary
    (m : ℕ) (γ : ℝ → ℝ) (hγ : ContDiff ℝ 1 γ) (hs : HasCompactSupport γ) :
    (∫ r in Set.Ioi (0 : ℝ), deriv γ r * r ^ m)
      = - (γ 0 * (0 : ℝ) ^ m)
        - (m : ℝ) * ∫ r in Set.Ioi (0 : ℝ), γ r * r ^ (m - 1) := by
  -- u = γ · r^m
  set u : ℝ → ℝ := fun r => γ r * r ^ m with hu
  have hu_cd : ContDiff ℝ 1 u := by
    rw [hu]
    fun_prop
  have hu_cs : HasCompactSupport u := by
    rw [hu]
    exact hs.mono' ((subset_tsupport (fun r : ℝ => γ r * r ^ m)).trans
      (tsupport_mul_subset_left (f := γ) (g := fun r : ℝ => r ^ m)))
  -- key: ∫_{Ioi 0} u' = -u(0)
  have hmain0 : (∫ r in Set.Ioi (0:ℝ), deriv u r) = - (γ 0 * (0:ℝ) ^ m) := by
    rw [HasCompactSupport.integral_Ioi_deriv_eq hu_cd hu_cs (0:ℝ)]
  -- pointwise product rule
  have hderiv : ∀ r : ℝ, deriv u r
      = deriv γ r * r ^ m + γ r * ((m : ℝ) * r ^ (m - 1)) := by
    intro r
    simp only [hu]
    have h1 : HasDerivAt γ (deriv γ r) r :=
      (hγ.differentiable one_ne_zero r).hasDerivAt
    have h2 : HasDerivAt (fun r : ℝ => r ^ m) ((m : ℝ) * r ^ (m - 1)) r := by
      simpa using hasDerivAt_pow m r
    exact (h1.mul h2).deriv
  -- integrability of the two pieces
  have hA_cs : HasCompactSupport (fun r : ℝ => deriv γ r * r ^ m) :=
    (hs.deriv).mono' ((subset_tsupport (fun r : ℝ => deriv γ r * r ^ m)).trans
      (tsupport_mul_subset_left (f := deriv γ) (g := fun r : ℝ => r ^ m)))
  have hA_int : IntegrableOn (fun r : ℝ => deriv γ r * r ^ m) (Set.Ioi 0) :=
    (((hγ.continuous_deriv le_rfl).mul (continuous_id.pow m)).integrable_of_hasCompactSupport
      hA_cs).integrableOn
  have hB_cs : HasCompactSupport (fun r : ℝ => γ r * ((m : ℝ) * r ^ (m - 1))) :=
    hs.mono' ((subset_tsupport (fun r : ℝ => γ r * ((m : ℝ) * r ^ (m - 1)))).trans
      (tsupport_mul_subset_left (f := γ) (g := fun r : ℝ => (m : ℝ) * r ^ (m - 1))))
  have hB_int : IntegrableOn (fun r : ℝ => γ r * ((m : ℝ) * r ^ (m - 1))) (Set.Ioi 0) :=
    ((hγ.continuous.mul (continuous_const.mul (continuous_id.pow (m - 1)))).integrable_of_hasCompactSupport
      hB_cs).integrableOn
  -- rewrite the integral of u' as a sum
  have hcongr : (∫ r in Set.Ioi (0:ℝ), deriv u r)
      = ∫ r in Set.Ioi (0:ℝ),
          (deriv γ r * r ^ m + γ r * ((m : ℝ) * r ^ (m - 1))) :=
    integral_congr_ae (Eventually.of_forall hderiv)
  have hsplit : (∫ r in Set.Ioi (0:ℝ),
          (deriv γ r * r ^ m + γ r * ((m : ℝ) * r ^ (m - 1))))
      = (∫ r in Set.Ioi (0:ℝ), deriv γ r * r ^ m)
        + ∫ r in Set.Ioi (0:ℝ), γ r * ((m : ℝ) * r ^ (m - 1)) := by
    rw [integral_add hA_int hB_int]
  have hBcon : (∫ r in Set.Ioi (0:ℝ), γ r * ((m : ℝ) * r ^ (m - 1)))
      = (m : ℝ) * ∫ r in Set.Ioi (0:ℝ), γ r * r ^ (m - 1) := by
    trans ∫ r in Set.Ioi (0:ℝ), (m : ℝ) * (γ r * r ^ (m - 1))
    · exact integral_congr_ae (Eventually.of_forall fun r => by ring)
    · rw [integral_const_mul]
  rw [hcongr, hsplit, hBcon] at hmain0
  linarith

end Commons.Analysis.Real
