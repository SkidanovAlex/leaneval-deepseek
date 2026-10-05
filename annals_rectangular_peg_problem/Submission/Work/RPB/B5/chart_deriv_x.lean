import Mathlib
import Submission.Work.RPB.B5.chartChain
import Submission.Work.RPB.B5.LagData
import Submission.Work.RPB.B5.chartW_eq_chordSurf_sqrt
import Submission.Work.RPB.B5.deriv_comp_sqrt

/-!
# B5: the `x`-derivative of the chart branch

On the middle region `-√2 < x < 0` the assembled family is `(x,t) ↦ W τ t (rho τ x t)`, the
`ρ`-chart of the chord annulus evaluated at the chord parameter `ρ = rho τ x t`.  Writing
`r = √ρ`, the chart identity `hWchord` of `LagData` says

`W τ t (rho τ x t) = chordSurf CI.c a τ t (√(rho τ x t))`,

(`Work.RPB.B5.chartW_eq_chordSurf_sqrt`: here `0 < rho τ x t ≤ π²/4`, so `√ρ ∈ (0, π/2]` is in the
range on which the chart is the chord surface).  Hence the `x`-derivative is the chain rule

`∂_x (W τ t (rho τ (·) t)) = ∂_x (√(rho τ (·) t)) • ∂_r chordSurf CI.c a τ t (√(rho τ x t))`,

the second factor being a pure `PS`-vector: the Fréchet derivative `fderiv ℝ (chordSurf …) r` of a
map `ℝ → PS` at `r` satisfies `fderiv ℝ (chordSurf …) r c = c • deriv (chordSurf …) r`.

The two ingredients are proved separately: the pointwise chart identity
(`Work.RPB.B5.chartW_eq_chordSurf_sqrt`, promoted to an eventual equality on the open interval
`(-√2, 0)` since the interval is a neighbourhood of `x`) and the abstract chain rule
`Work.RPB.B5.deriv_comp_sqrt`.

The differentiability inputs are: `rho τ · t` is differentiable at `x` (`D.hrhosm` is globally
`C⁸`) and `r ↦ chordSurf CI.c a τ t r` is differentiable at `√(rho τ x t)` (from
`Work.RPB.B5.chordSurf_pair_contDiffAt`, the chord surface being `C⁸` in `(t,r)` for
`τ ∈ [0,1]`, `0 < r < π`; here `0 < √(rho τ x t) ≤ π/2 < π`).
-/

open Filter

open scoped Topology

set_option autoImplicit false

noncomputable section

namespace Work.RPB.B5

theorem chart_deriv_x (CI : Work.RPV.CurveIsotopy) (a : ℝ → ℝ → ℝ → ℝ)
    (ha : Work.RPB.IsChordPhase CI.c a) (D : Work.RPB.B5.LagData CI a) :
    ∀ τ ∈ Set.Icc (0 : ℝ) 1, ∀ t : ℝ, ∀ x ∈ Set.Ioo (-Real.sqrt 2) 0,
      deriv (fun y => D.W τ t (D.rho τ y t)) x
        = deriv (fun y => Real.sqrt (D.rho τ y t)) x •
            deriv (fun r => Work.RPB.chordSurf CI.c a τ t r) (Real.sqrt (D.rho τ x t)) := by
  intro τ hτ t x hx
  -- the chart equals the chord surface on the whole open interval `(-√2, 0)`
  have hloc : (fun y => D.W τ t (D.rho τ y t)) =ᶠ[𝓝 x]
      (fun y => Work.RPB.chordSurf CI.c a τ t (Real.sqrt (D.rho τ y t))) := by
    filter_upwards [isOpen_Ioo.mem_nhds hx] with y hy
    exact chartW_eq_chordSurf_sqrt CI a D τ hτ t y hy
  -- `rho τ x t` is positive and at most `π²/4`, so `√(rho τ x t) ∈ (0, π)`
  have hxIoc : x ∈ Set.Ioc (-Real.sqrt 2) 0 := ⟨hx.1, le_of_lt hx.2⟩
  have hval := D.hrhoval τ hτ x hxIoc t
  have hρpos : 0 < D.rho τ x t := hval.1
  have hr0mem : Real.sqrt (D.rho τ x t) ∈ Set.Ioo (0 : ℝ) Real.pi := by
    refine ⟨Real.sqrt_pos.mpr hρpos, ?_⟩
    have h1 : Real.sqrt (D.rho τ x t) ≤ Real.pi / 2 := by
      calc Real.sqrt (D.rho τ x t) ≤ Real.sqrt (Real.pi ^ 2 / 4) := Real.sqrt_le_sqrt hval.2
        _ = Real.pi / 2 := by
            rw [show Real.pi ^ 2 / 4 = (Real.pi / 2) ^ 2 by ring]
            exact Real.sqrt_sq (by positivity)
    linarith [Real.pi_pos]
  -- differentiability of the two legs of the chain
  have hρdiff : DifferentiableAt ℝ (fun y : ℝ => D.rho τ y t) x := by
    have hglob : Differentiable ℝ (fun z : ℝ × (ℝ × ℝ) => D.rho z.1 z.2.1 z.2.2) :=
      D.hrhosm.differentiable (by norm_num)
    have h2 : DifferentiableAt ℝ (fun y : ℝ => ((τ, (y, t)) : ℝ × (ℝ × ℝ))) x := by fun_prop
    exact (hglob.differentiableAt (x := (τ, (x, t)))).comp x h2
  have hfdiff : DifferentiableAt ℝ (fun r : ℝ => Work.RPB.chordSurf CI.c a τ t r)
      (Real.sqrt (D.rho τ x t)) := by
    have hpair : ContDiffAt ℝ 8
        (fun z : ℝ × ℝ => Work.RPB.chordSurf CI.c a τ z.1 z.2) (t, Real.sqrt (D.rho τ x t)) :=
      chordSurf_pair_contDiffAt CI a ha hτ hr0mem
    have h2 : DifferentiableAt ℝ (fun r : ℝ => ((t, r) : ℝ × ℝ))
        (Real.sqrt (D.rho τ x t)) := by fun_prop
    exact (hpair.differentiableAt (by norm_num)).comp _ h2
  -- the chain rule
  rw [hloc.deriv_eq,
    deriv_comp_sqrt (fun r : ℝ => Work.RPB.chordSurf CI.c a τ t r)
      (fun y : ℝ => D.rho τ y t) x (ne_of_gt hρpos) hfdiff hρdiff]

end Work.RPB.B5
