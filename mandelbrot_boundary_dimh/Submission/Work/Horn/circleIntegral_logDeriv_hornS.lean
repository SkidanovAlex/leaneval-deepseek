import Mathlib
import Submission.Work.Horn.horn_chart

/-!
# The circle integral of `logDeriv (hornS s)` around `0`

`hornS s` is the transfer of a `T`-equivariant section `s` of the horn map to the
inverted chart `u = e^{-2πiw}` (`w = -(log u)/(2πi)`).  On the circle `|u| = r`
the pull-back of `u` to the `w`-plane is the horizontal segment
`w(θ) = t - θ/(2π)` (with `t = log r/(2π)`) running from `t` to `t - 1`, which lies
in `D` as soon as `r < e^{-2πη}`.  Substituting `θ ↦ w(θ)` turns
`∮ logDeriv (hornS s)` into `-2πi ∫ s'(w(θ)) w'(θ) dθ`, which the fundamental
theorem of calculus evaluates with the equivariance `s (w+1) = s w + 1` to `2πi`.
-/

noncomputable section

open MandelDim Filter Topology Metric Set
open scoped Topology Real

namespace Work.Horn

theorem circleIntegral_logDeriv_hornS {s : ℂ → ℂ} {D : Set ℂ} {η : ℝ}
    (hDo : IsOpen D) (hT : MandelDim.IsTInvariant D) (hs : DifferentiableOn ℂ s D)
    (heq : ∀ w ∈ D, s (w + 1) = s w + 1)
    (hlo : {w : ℂ | w.im < -η} ⊆ D) :
    ∀ r : ℝ, 0 < r → r < Real.exp (-(2 * Real.pi) * η) →
      circleIntegral (logDeriv (Work.Horn.hornS s)) 0 r = 2 * Real.pi * Complex.I := by
  intro r hr hrη
  set t : ℝ := Real.log r / (2 * Real.pi) with htdef
  have h2pi : (0:ℝ) < 2 * Real.pi := by positivity
  have htmul : 2 * Real.pi * t = Real.log r := by rw [htdef]; field_simp
  have hlogr : Real.log r < -(2 * Real.pi) * η := by
    have h := Real.log_lt_log hr hrη
    rwa [Real.log_exp] at h
  have htlt : t < -η := by
    rw [htdef, div_lt_iff₀ h2pi]
    nlinarith
  set W : ℝ → ℂ := fun (θ : ℝ) => (t:ℂ) * Complex.I - (θ:ℂ) / (2*(Real.pi:ℂ)) with hWdef
  have hWval : ∀ θ, W θ = (t:ℂ) * Complex.I - (θ:ℂ) / (2*(Real.pi:ℂ)) := fun θ => rfl
  have hWim : ∀ θ, (W θ).im = t := by
    intro θ
    rw [hWval θ]
    have h : ((θ:ℂ) / (2*(Real.pi:ℂ))).im = 0 := by rw [Complex.div_im]; simp
    simp [Complex.sub_im, Complex.mul_im, h]
  have hWmem : ∀ θ, W θ ∈ D := fun θ => hlo (by
    show (W θ).im < -η
    rw [hWim θ]; exact htlt)
  have hWderiv : ∀ θ, HasDerivAt W (-((2*(Real.pi:ℂ))⁻¹)) θ := by
    intro θ
    have h1 : HasDerivAt (fun x : ℝ => (x:ℂ)) 1 θ := (hasDerivAt_id θ).ofReal_comp
    have h2 : HasDerivAt (fun x : ℝ => (x:ℂ) / (2*(Real.pi:ℂ))) ((2*(Real.pi:ℂ))⁻¹) θ := by
      simpa using h1.div_const (2*(Real.pi:ℂ))
    have h3 : HasDerivAt (fun x : ℝ => (t:ℂ)*Complex.I - (x:ℂ)/(2*(Real.pi:ℂ)))
        (0 - (2*(Real.pi:ℂ))⁻¹) θ := (hasDerivAt_const θ ((t:ℂ)*Complex.I)).sub h2
    simpa [hWdef] using h3
  -- the circle `|u| = r` is the image of the horizontal segment `Im = t` under `w ↦ π(-w)`
  have hcirc : ∀ θ : ℝ, circleMap 0 r θ = MandelDim.piExp (-(W θ)) := by
    intro θ
    have hA : 2 * (Real.pi:ℂ) * Complex.I * (-(W θ)) = (Real.log r : ℂ) + (θ:ℂ) * Complex.I := by
      rw [hWval θ]
      rw [show -((t:ℂ) * Complex.I - (θ:ℂ) / (2*(Real.pi:ℂ)))
          = -((t:ℂ) * Complex.I) + ((θ:ℂ) / (2*(Real.pi:ℂ))) by ring]
      rw [mul_add]
      rw [show 2*(Real.pi:ℂ)*Complex.I*(-((t:ℂ)*Complex.I)) = 2*(Real.pi:ℂ)*(t:ℂ) by
        rw [show 2*(Real.pi:ℂ)*Complex.I*(-((t:ℂ)*Complex.I))
            = -(2*(Real.pi:ℂ)*(t:ℂ)*(Complex.I*Complex.I)) by ring, Complex.I_mul_I]; ring]
      rw [show 2*(Real.pi:ℂ)*Complex.I*((θ:ℂ)/(2*(Real.pi:ℂ))) = (θ:ℂ)*Complex.I by field_simp]
      have h2 : 2*(Real.pi:ℂ)*(t:ℂ) = (Real.log r : ℂ) := by rw [← htmul]; push_cast; ring
      rw [h2]
    rw [MandelDim.piExp, hA, Complex.exp_add,
      show Complex.exp (↑(Real.log r)) = (r:ℂ) by rw [← Complex.ofReal_exp, Real.exp_log hr]]
    rw [circleMap]; simp
  have hVeq : ∀ θ : ℝ, hornS s (circleMap 0 r θ) = MandelDim.piExp (-(s (W θ))) := by
    intro θ
    rw [hcirc θ]
    exact hornS_piExp hT heq (hWmem θ)
  have hGfun : ((hornS s) ∘ (circleMap 0 r)) = fun (θ : ℝ) => MandelDim.piExp (-(s (W θ))) :=
    funext hVeq
  have hne2pi : ((2:ℂ)*(Real.pi:ℂ)) ≠ 0 := by
    have h : (2:ℝ)*Real.pi ≠ 0 := by positivity
    exact_mod_cast h
  -- the integrand is the derivative of `θ ↦ -2πi s (W θ)`
  have hkey : ∀ θ : ℝ, deriv (circleMap 0 r) θ • logDeriv (hornS s) (circleMap 0 r θ)
      = deriv s (W θ) * Complex.I := by
    intro θ
    have hcdiff : DifferentiableAt ℝ (circleMap 0 r) θ :=
      (hasDerivAt_circleMap 0 r θ).differentiableAt
    have hcθmem : circleMap 0 r θ ∈ hornDl' D :=
      Set.mem_insert_of_mem _ ⟨-(W θ), by simpa using hWmem θ, (hcirc θ).symm⟩
    have hcθne : circleMap 0 r θ ≠ 0 := by
      rw [hcirc θ]; exact MandelDim.piExp_ne_zero _
    have hVdiff : DifferentiableAt ℂ (hornS s) (circleMap 0 r θ) :=
      hornS_differentiableAt hDo hT heq hs hcθmem hcθne
    have hcomp : deriv ((hornS s) ∘ (circleMap 0 r)) θ
        = deriv (hornS s) (circleMap 0 r θ) * deriv (circleMap 0 r) θ :=
      deriv_comp θ hVdiff hcdiff
    have hVne : hornS s (circleMap 0 r θ) ≠ 0 := by
      rw [hVeq θ]; exact MandelDim.piExp_ne_zero _
    have hg : HasDerivAt (fun x : ℝ => -(s (W x)))
        (-(deriv s (W θ) * (-((2*(Real.pi:ℂ))⁻¹)))) θ := by
      have h1 : HasDerivAt (fun x : ℝ => s (W x)) (deriv s (W θ) * (-((2*(Real.pi:ℂ))⁻¹))) θ := by
        have h := ((hs.differentiableAt (hDo.mem_nhds (hWmem θ))).hasDerivAt).comp θ (hWderiv θ)
        simpa [Function.comp_def] using h
      exact h1.neg
    have hGat : HasDerivAt (fun x : ℝ => MandelDim.piExp (-(s (W x))))
        ((2*(Real.pi:ℂ)*Complex.I*MandelDim.piExp (-(s (W θ)))) *
          (-(deriv s (W θ) * (-((2*(Real.pi:ℂ))⁻¹))))) θ := by
      have h := (differentiableAt_piExp (-(s (W θ)))).hasDerivAt.comp θ hg
      rw [deriv_piExp] at h
      exact h
    have hGderiv := hGat.deriv
    have hpi : MandelDim.piExp (-(s (W θ))) ≠ 0 := MandelDim.piExp_ne_zero _
    calc deriv (circleMap 0 r) θ • logDeriv (hornS s) (circleMap 0 r θ)
        = deriv (circleMap 0 r) θ
            * (deriv (hornS s) (circleMap 0 r θ) / hornS s (circleMap 0 r θ)) := by
          rw [logDeriv_apply, smul_eq_mul]
      _ = (deriv (hornS s) (circleMap 0 r θ) * deriv (circleMap 0 r) θ)
            / hornS s (circleMap 0 r θ) := by ring
      _ = deriv ((hornS s) ∘ (circleMap 0 r)) θ / hornS s (circleMap 0 r θ) := by rw [hcomp]
      _ = deriv (fun x : ℝ => MandelDim.piExp (-(s (W x)))) θ / MandelDim.piExp (-(s (W θ))) := by
          rw [hGfun, hVeq θ]
      _ = deriv s (W θ) * Complex.I := by
          rw [hGderiv]
          field_simp
  have hFderiv : ∀ θ : ℝ, HasDerivAt (fun x : ℝ => -(2 * Real.pi * Complex.I) * s (W x))
      (deriv s (W θ) * Complex.I) θ := by
    intro θ
    have h1 : HasDerivAt (fun x : ℝ => s (W x)) (deriv s (W θ) * (-((2*(Real.pi:ℂ))⁻¹))) θ := by
      have h := ((hs.differentiableAt (hDo.mem_nhds (hWmem θ))).hasDerivAt).comp θ (hWderiv θ)
      simpa [Function.comp_def] using h
    have h2 : HasDerivAt (fun x : ℝ => -(2 * Real.pi * Complex.I) * s (W x))
        (-(2 * Real.pi * Complex.I) * (deriv s (W θ) * (-((2*(Real.pi:ℂ))⁻¹)))) θ := by
      have h := h1.const_mul (-(2 * Real.pi * Complex.I))
      simpa using h
    have hval : -(2 * Real.pi * Complex.I) * (deriv s (W θ) * (-((2*(Real.pi:ℂ))⁻¹)))
        = deriv s (W θ) * Complex.I := by field_simp
    rw [← hval]
    exact h2
  have hcont : Continuous (fun θ : ℝ => deriv s (W θ) * Complex.I) := by
    have hderivcont : ContinuousOn (deriv s) D :=
      ((hs.analyticOnNhd hDo).deriv_of_isOpen hDo).continuousOn
    have hWcont : Continuous W := by
      have h4 : Continuous (fun x : ℝ => (t:ℂ)*Complex.I - (x:ℂ)/(2*(Real.pi:ℂ))) := by
        refine Continuous.sub ?_ ?_
        · exact continuous_const
        · exact Complex.continuous_ofReal.div_const _
      rw [hWdef]; exact h4
    exact ((hderivcont.comp_continuous hWcont hWmem).mul continuous_const)
  rw [circleIntegral]
  rw [intervalIntegral.integral_congr (fun θ _ => hkey θ)]
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun θ _ => hFderiv θ)
        (hcont.continuousOn.intervalIntegrable)]
  have hW0 : W 0 = (t:ℂ) * Complex.I := by rw [hWval]; simp
  have hW2pi : W (2*Real.pi) = (t:ℂ) * Complex.I - 1 := by
    rw [hWval]
    congr 1
    push_cast
    field_simp
  have hsrel : s (W (2*Real.pi)) = s (W 0) - 1 := by
    have h := heq (W (2*Real.pi)) (hWmem _)
    have h1 : W (2*Real.pi) + 1 = W 0 := by rw [hW2pi, hW0]; ring
    rw [h1] at h
    rw [h]; ring
  have : -(2 * Real.pi * Complex.I) * s (W (2*Real.pi)) - (-(2 * Real.pi * Complex.I) * s (W 0))
      = 2 * Real.pi * Complex.I := by
    rw [hsrel]; ring
  exact this

end Work.Horn
