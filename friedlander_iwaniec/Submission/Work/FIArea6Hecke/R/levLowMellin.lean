import Mathlib
import Submission.Work.FIArea6Hecke.R.levelHeckeDefs
import Submission.Work.FIArea5.S16Hecke.integral_inv_scale
import Submission.Work.FIArea5.S16Hecke.cpow_inv_scale

set_option maxHeartbeats 1000000

namespace Work.FIArea6Hecke.R

open MeasureTheory Set

/-- **Mellin transform of the low cut.**  For a theta series `f` satisfying the theta law

  `f(u) = A·u^{-(m+1)}·conj f(1/(B u))`

the Mellin transform of the restriction of `f` to the interval `(0, c)`, `c = 1/√B`
(`= thetaCutLo B f`), equals the reflected integral

  `∫_0^c f(u)u^{t-1}du = A·B^{m+1-t}·∫_c^∞ conj f(v)v^{m-t}dv`,

i.e. `mellin (thetaCutLo B f) t = A·B^{m+1-t}·thetaE B f m t`.  This is the reflection half of
Hecke's functional equation.

The proof is the substitution `u = 1/(B v)`, an involution of `(0,∞)` reversing the order and
fixing `c`, with Jacobian `|φ'| = 1/(Bv²)`: it carries the integral over `(0,c)` to the integral
over `(c,∞)` (`integral_inv_scale`), and the theta law turns the pull-back of the integrand into
`A·B^{m+1-t}·conj f(v)·v^{m-t}` (`cpow_inv_scale` on the pointwise level, with the two cuts
matched by `inv_mul_lt_thetaCutPt_iff`). -/
theorem levLowMellin (B : ℝ) (hB : 0 < B) (f : ℝ → ℂ) (m : ℕ) (A : ℂ)
    (hlaw : ∀ u : ℝ, 0 < u → f u = A * ((u : ℂ) ^ (-(m : ℤ) - 1)) * star (f (1 / (B * u))))
    (t : ℂ) :
    mellin (thetaCutLo B f) t = A * ((B : ℂ) ^ ((m : ℂ) + 1 - t)) * thetaE B f m t := by
  -- The substitution `u = 1/(B v)` in the Mellin integral.
  have hsub := Work.FIArea5.S16Hecke.integral_inv_scale (B := B)
    (fun u : ℝ => (u : ℂ) ^ (t - 1) * thetaCutLo B f u) hB
  -- Pointwise rewriting of the substituted integrand, using the theta law.
  have hpoint : ∀ v ∈ Set.Ioi (0 : ℝ),
      ((1 / (B * v) : ℝ) : ℂ) ^ (t - 1) * thetaCutLo B f (1 / (B * v))
          * (((B * v ^ 2)⁻¹ : ℝ) : ℂ)
        = A * ((B : ℂ) ^ ((m : ℂ) + 1 - t))
            * ((v : ℂ) ^ ((m : ℂ) - t) * thetaCutHiStar B f v) := by
    intro v hv
    have hvpos : 0 < v := hv
    by_cases hcv : thetaCutPt B < v
    · have hu : 1 / (B * v) < thetaCutPt B :=
        (inv_mul_lt_thetaCutPt_iff hB hvpos).mpr hcv
      have hu0 : 0 < 1 / (B * v) := by positivity
      have h_low : thetaCutLo B f (1 / (B * v)) = f (1 / (B * v)) := by
        simp only [thetaCutLo]; rw [if_pos hu]
      have h_star : thetaCutHiStar B f v = star (f v) := by
        simp only [thetaCutHiStar]; rw [if_pos hcv]
      have hv1 : 1 / (B * (1 / (B * v))) = v := by field_simp
      have hL := hlaw (1 / (B * v)) hu0
      rw [hv1] at hL
      rw [h_low, hL, h_star]
      rw [show ((1 / (B * v) : ℝ) : ℂ) ^ (t - 1)
            * (A * (((1 / (B * v) : ℝ) : ℂ) ^ (-(m : ℤ) - 1))
                * star (f v)) * (((B * v ^ 2)⁻¹ : ℝ) : ℂ)
          = ((((1 / (B * v) : ℝ) : ℂ) ^ (t - 1)
              * (((1 / (B * v) : ℝ) : ℂ) ^ (-(m : ℤ) - 1))
              * (((B * v ^ 2)⁻¹ : ℝ) : ℂ))) * (A * star (f v))
          by ring]
      rw [Work.FIArea5.S16Hecke.cpow_inv_scale B hB m t v hvpos]
      ring
    · have hu : ¬ (1 / (B * v) < thetaCutPt B) :=
        fun h => hcv ((inv_mul_lt_thetaCutPt_iff hB hvpos).mp h)
      have h_low : thetaCutLo B f (1 / (B * v)) = 0 := by
        simp only [thetaCutLo]; rw [if_neg hu]
      have h_star : thetaCutHiStar B f v = 0 := by
        simp only [thetaCutHiStar]; rw [if_neg hcv]
      rw [h_low, h_star]; ring
  calc mellin (thetaCutLo B f) t
      = ∫ u in Set.Ioi (0 : ℝ), (u : ℂ) ^ (t - 1) * thetaCutLo B f u := by
          rw [mellin]
          refine setIntegral_congr_fun measurableSet_Ioi (fun u _ => ?_)
          rw [smul_eq_mul]
      _ = ∫ v in Set.Ioi (0 : ℝ), ((1 / (B * v) : ℝ) : ℂ) ^ (t - 1)
            * thetaCutLo B f (1 / (B * v)) * (((B * v ^ 2)⁻¹ : ℝ) : ℂ) :=
          hsub.symm
      _ = ∫ v in Set.Ioi (0 : ℝ), A * ((B : ℂ) ^ ((m : ℂ) + 1 - t))
            * ((v : ℂ) ^ ((m : ℂ) - t) * thetaCutHiStar B f v) :=
          setIntegral_congr_fun measurableSet_Ioi hpoint
      _ = A * ((B : ℂ) ^ ((m : ℂ) + 1 - t))
            * ∫ v in Set.Ioi (0 : ℝ), ((v : ℂ) ^ ((m : ℂ) - t) * thetaCutHiStar B f v) := by
          rw [integral_const_mul]
      _ = A * ((B : ℂ) ^ ((m : ℂ) + 1 - t)) * thetaE B f m t := by
          rw [thetaE, mellin]
          have hexp : ((m : ℂ) + 1 - t) - 1 = (m : ℂ) - t := by ring
          rw [hexp]
          refine congrArg
            (fun z => A * ((B : ℂ) ^ ((m : ℂ) + 1 - t)) * z) ?_
          refine setIntegral_congr_fun measurableSet_Ioi (fun v _ => ?_)
          rw [smul_eq_mul]

end Work.FIArea6Hecke.R
