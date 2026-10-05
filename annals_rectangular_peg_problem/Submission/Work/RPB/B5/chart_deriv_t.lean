import Mathlib
import Submission.Work.RPB.B5.chartChain
import Submission.Work.RPB.B5.LagData

namespace Work.RPB.B5

theorem chart_deriv_t (CI : Work.RPV.CurveIsotopy) (a : ℝ → ℝ → ℝ → ℝ)
    (ha : Work.RPB.IsChordPhase CI.c a) (D : Work.RPB.B5.LagData CI a) :
    ∀ τ ∈ Set.Icc (0 : ℝ) 1, ∀ x ∈ Set.Ioo (-Real.sqrt 2) 0, ∀ t : ℝ,
      deriv (fun s => D.W τ s (D.rho τ x s)) t
        = deriv (fun u => Work.RPB.chordSurf CI.c a τ u (Real.sqrt (D.rho τ x t))) t
          + deriv (fun s => Real.sqrt (D.rho τ x s)) t •
              deriv (fun r => Work.RPB.chordSurf CI.c a τ t r) (Real.sqrt (D.rho τ x t)) := by
  intro τ hτ x hx t
  have hxIoc : x ∈ Set.Ioc (-Real.sqrt 2) 0 := ⟨hx.1, hx.2.le⟩
  -- the level `ρ = rho τ x s` stays in `(0, π²/4]` for every `s`, so `r = √ρ` is in `(0, π/2]`
  have hρpos : ∀ s, 0 < D.rho τ x s := fun s => (D.hrhoval τ hτ x hxIoc s).1
  have hρle : ∀ s, D.rho τ x s ≤ Real.pi ^ 2 / 4 := fun s => (D.hrhoval τ hτ x hxIoc s).2
  have hsqrtpi : Real.sqrt (Real.pi ^ 2 / 4) = Real.pi / 2 := by
    have h : Real.pi ^ 2 / 4 = (Real.pi / 2) ^ 2 := by ring
    rw [h, Real.sqrt_sq (by positivity)]
  have hsqrtle : ∀ s, Real.sqrt (D.rho τ x s) ≤ Real.pi / 2 := by
    intro s
    rw [← hsqrtpi]
    exact Real.sqrt_le_sqrt (hρle s)
  have hlt : Real.sqrt (D.rho τ x t) ∈ Set.Ioo (0 : ℝ) Real.pi :=
    ⟨Real.sqrt_pos_of_pos (hρpos t), by linarith [hsqrtle t, Real.pi_pos]⟩
  -- replace the chart `W` by the chord surface, in the `r = √ρ` variable
  have heq : (fun s => D.W τ s (D.rho τ x s))
      = (fun s => Work.RPB.chordSurf CI.c a τ s (Real.sqrt (D.rho τ x s))) := by
    funext s
    have hγ : Real.sqrt (D.rho τ x s) ∈ Set.Ioc (0 : ℝ) (Real.pi / 2) :=
      ⟨Real.sqrt_pos_of_pos (hρpos s), hsqrtle s⟩
    have h3 := D.hWchord τ hτ s (Real.sqrt (D.rho τ x s)) hγ
    rwa [Real.sq_sqrt (le_of_lt (hρpos s))] at h3
  rw [heq]
  -- both remaining factors are differentiable, so the two-variable chain rule applies
  have hΦ : DifferentiableAt ℝ (fun z : ℝ × ℝ => Work.RPB.chordSurf CI.c a τ z.1 z.2)
      (t, Real.sqrt (D.rho τ x t)) :=
    (Work.RPB.B5.chordSurf_pair_contDiffAt CI a ha hτ hlt).differentiableAt (by norm_num)
  have hρcd : ContDiff ℝ 8 (fun s : ℝ => D.rho τ x s) :=
    D.hrhosm.comp (contDiff_const.prodMk (contDiff_const.prodMk contDiff_id))
  have hρdiff : DifferentiableAt ℝ (fun s : ℝ => D.rho τ x s) t :=
    (hρcd.differentiable (by norm_num)).differentiableAt
  have hψ : DifferentiableAt ℝ (fun s => Real.sqrt (D.rho τ x s)) t :=
    (Real.hasDerivAt_sqrt (ne_of_gt (hρpos t))).differentiableAt.comp t hρdiff
  exact (Work.RPB.B5.hasDerivAt_pair_comp hΦ hψ).deriv

end Work.RPB.B5
