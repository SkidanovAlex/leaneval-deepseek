import Mathlib
import Submission.Work.LinnikAreas.PrincipalZeroCount

namespace Work.LinnikAreas.TuranOther

open Filter
open scoped Topology

-- Route: for `u ≠ 0,1` use `riemannZeta_def_of_ne_zero` to write `ζ =ᶠ Λ · (fun s => (Gammaℝ s)⁻¹)`
-- near `u` (both factors analytic there: `completedRiemannZeta_eq` + `differentiable_Gammaℝ_inv`)
-- and `analyticOrderAt_mul`; at `u = 1` use `analyticOrderNatAt_of_not_analyticAt` for both `ζ`
-- and `Λ` (`PrincipalZeroCount.not_analyticAt_completedZeta_one`; for `ζ` use
-- `riemannZeta_residue_one`, as in that file) and `Complex.Gammaℝ_one`.

/-- An entire function which is not identically zero has finite order of vanishing at every point:
if its order of vanishing were infinite it would vanish in a whole neighbourhood of the point,
hence everywhere by the identity theorem. -/
lemma analyticOrderAt_ne_top_of_entire_ne_zero {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hne : f ≠ 0) (u : ℂ) : analyticOrderAt f u ≠ ⊤ := by
  intro htop
  have h0 : f =ᶠ[𝓝 u] 0 := analyticOrderAt_eq_top.mp htop
  have han : AnalyticOnNhd ℂ f Set.univ := fun z _ => hf.analyticAt z
  have hzero : AnalyticOnNhd ℂ (0 : ℂ → ℂ) Set.univ := fun _ _ => analyticAt_const
  exact hne (AnalyticOnNhd.eq_of_eventuallyEq han hzero h0)

/-- The order of vanishing of a function which is analytic and non-zero at a point is zero. -/
lemma analyticOrderNatAt_eq_zero_of_analyticAt_ne_zero {f : ℂ → ℂ} {z : ℂ}
    (hf : AnalyticAt ℂ f z) (hz : f z ≠ 0) : analyticOrderNatAt f z = 0 := by
  simp [analyticOrderNatAt, hf.analyticOrderAt_eq_zero.mpr hz]

/-- `ζ` is not analytic at `1`: it has a (simple) pole there. -/
lemma not_analyticAt_riemannZeta_one : ¬ AnalyticAt ℂ riemannZeta 1 := by
  intro h
  have hcont : ContinuousAt (fun s : ℂ => (s - 1) * riemannZeta s) 1 :=
    (continuousAt_id.sub continuousAt_const).mul h.continuousAt
  have hlim0 : Filter.Tendsto (fun s : ℂ => (s - 1) * riemannZeta s)
      (𝓝[≠] (1:ℂ)) (𝓝 (0:ℂ)) := by
    have := hcont.mono_left (nhdsWithin_le_nhds (s := ({1}ᶜ : Set ℂ)) (a := 1))
    simpa using this
  have h01 : (0:ℂ) = 1 := tendsto_nhds_unique hlim0 riemannZeta_residue_one
  norm_num at h01

theorem orderZeta_eq_orderLambda_add_invGammaR (u : ℂ) (hu : u ≠ 0) :
    analyticOrderNatAt riemannZeta u
      = analyticOrderNatAt completedRiemannZeta u
        + analyticOrderNatAt (fun s : ℂ => (Complex.Gammaℝ s)⁻¹) u := by
  rcases eq_or_ne u 1 with rfl | hu1
  · -- `u = 1`: `ζ` and `Λ` both have a pole there and `(Gammaℝ ·)⁻¹` is analytic with value `1`.
    have hginv : analyticOrderNatAt (fun s : ℂ => (Complex.Gammaℝ s)⁻¹) (1 : ℂ) = 0 :=
      analyticOrderNatAt_eq_zero_of_analyticAt_ne_zero
        (Complex.differentiable_Gammaℝ_inv.analyticAt 1) (by simp [Complex.Gammaℝ_one])
    rw [analyticOrderNatAt_of_not_analyticAt not_analyticAt_riemannZeta_one,
      analyticOrderNatAt_of_not_analyticAt not_analyticAt_completedZeta_one, hginv, zero_add]
  · -- `u ≠ 0, 1`: `ζ =ᶠ Λ · (Gammaℝ ·)⁻¹` near `u` and both factors are analytic there.
    have hΛan : AnalyticAt ℂ completedRiemannZeta u :=
      analyticAt_completedZeta_of_ne u hu hu1
    have hgan : AnalyticAt ℂ (fun s : ℂ => (Complex.Gammaℝ s)⁻¹) u :=
      Complex.differentiable_Gammaℝ_inv.analyticAt u
    -- finiteness of the order of `Λ` at `u`, via the entire non-zero function `Ξ = (1/2)s(s-1)Λ`
    have hΛfin : analyticOrderAt completedRiemannZeta u ≠ ⊤ := by
      have hxi : analyticOrderAt xiC u ≠ ⊤ :=
        analyticOrderAt_ne_top_of_entire_ne_zero xiC_diff
          (fun h => xiC_zero_ne (by simpa using congr_fun h 0)) u
      have hpoly : AnalyticAt ℂ (fun s : ℂ => (1/2 : ℂ) * s * (s - 1)) u := by fun_prop
      have hpoly0 : analyticOrderAt (fun s : ℂ => (1/2 : ℂ) * s * (s - 1)) u = 0 :=
        hpoly.analyticOrderAt_eq_zero.mpr (by
          have hne : (1/2 : ℂ) * u * (u - 1) ≠ 0 :=
            mul_ne_zero (mul_ne_zero (by norm_num) hu) (sub_ne_zero.mpr hu1)
          simpa using hne)
      have hcongr : analyticOrderAt xiC u
          = analyticOrderAt
              ((fun s : ℂ => (1/2 : ℂ) * s * (s - 1)) * completedRiemannZeta) u :=
        analyticOrderAt_congr (xiC_eventuallyEq u hu hu1)
      rw [hcongr, analyticOrderAt_mul hpoly hΛan, hpoly0, zero_add] at hxi
      exact hxi
    -- finiteness of the order of `(Gammaℝ ·)⁻¹` at `u`
    have hgfin : analyticOrderAt (fun s : ℂ => (Complex.Gammaℝ s)⁻¹) u ≠ ⊤ :=
      analyticOrderAt_ne_top_of_entire_ne_zero Complex.differentiable_Gammaℝ_inv
        (fun h => by
          have h1' : (Complex.Gammaℝ 1)⁻¹ = (0 : ℂ) := by simpa using congr_fun h 1
          rw [Complex.Gammaℝ_one] at h1'
          norm_num at h1') u
    have hζeq : riemannZeta =ᶠ[𝓝 u]
        completedRiemannZeta * (fun s : ℂ => (Complex.Gammaℝ s)⁻¹) := by
      filter_upwards [eventually_ne_nhds hu] with s hs
      rw [Pi.mul_apply, riemannZeta_def_of_ne_zero hs, div_eq_mul_inv]
    calc analyticOrderNatAt riemannZeta u
        = analyticOrderNatAt
            (completedRiemannZeta * (fun s : ℂ => (Complex.Gammaℝ s)⁻¹)) u := by
          simp only [analyticOrderNatAt]
          rw [analyticOrderAt_congr hζeq]
      _ = analyticOrderNatAt completedRiemannZeta u
            + analyticOrderNatAt (fun s : ℂ => (Complex.Gammaℝ s)⁻¹) u :=
          analyticOrderNatAt_mul hΛan hgan hΛfin hgfin

end Work.LinnikAreas.TuranOther
