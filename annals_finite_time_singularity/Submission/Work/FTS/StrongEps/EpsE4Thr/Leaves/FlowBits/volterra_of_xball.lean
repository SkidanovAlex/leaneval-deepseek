import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Submission.Work.FTS.StrongEps.EpsE4Thr.XStep
import Submission.Work.FTS.EpsEngine.LocalStepXBall
import Submission.Work.FTS.StrongEps.RhsCont
import Submission.Work.FTS.EpsEngine.EpsClass
import Submission.Work.FTS.StrongEps.PZeroScheme
import Submission.Work.FTS.StrongEps.EpsStructP
import Submission.Work.FTS.StrongEps.IsEpsSolPQ.epsSolP_volterra

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.EpsE4Thr.Leaves.FlowBits

theorem volterra_of_xball {α C₁ Ce Cs R ε δ : ℝ} {ρ : ℝ × ℝ → ℝ} {Φs : Work.FTS.Galerkin.Fn} {E : Work.FTS.Galerkin.Fn → Work.FTS.Galerkin.Fn}
    {h₀ : Work.FTS.Galerkin.Fn} {g : Work.FTS.Galerkin.Fam}
    (hα : α ∈ Set.Ioc (0 : ℝ) 1) (hρ : Work.FTS.StrongEps.IsSmoothKernel ρ) (hε : 0 < ε) (hε1 : ε ≤ 1) (hR : 0 ≤ R)
    (hEll : ∀ u : Work.FTS.Galerkin.Fn, Work.FTS.ClassC.ClassC α u →
      Work.FTS.VocabO.EllPkgGo α Ce u (E u) ∧ Work.FTS.ClassC.EllPkgK α 6 Ce u (E u))
    (hstar : Work.FTS.VocabO2.StarPkgo2 α Cs Φs) (hml : Work.FTS.StrongEps.MuLamOK α C₁ Φs E)
    (hδ : 0 < δ) (hsol : Work.FTS.StrongEps.IsEpsSolP α ρ ε δ Φs E h₀ g)
    (hreg : Work.FTS.StrongEps.EpsRegP α ρ ε δ g)
    (hX : ∀ τ ∈ Set.Icc 0 δ, Work.FTS.EpsEngine.XBall α ρ ε R C₁ (Work.FTS.Galerkin.slice g τ)) :
    ∀ z θ τ : ℝ, (z, θ) ∈ Work.FTS.EllipticEst.Q0 → τ ∈ Set.Icc 0 δ →
      g z θ τ = g z θ 0 + ∫ s in (0 : ℝ)..τ, Work.FTS.EpsEngine.Feps α ρ ε Φs E (Work.FTS.Galerkin.slice g s) z θ := by
  intro z θ τ hQ hτ
  rw [Work.FTS.EllipticEst.mem_Q0] at hQ
  obtain ⟨hz, hθ0, hθ1⟩ := hQ
  have hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) := ⟨hθ0, hθ1⟩
  -- The integrand is the fake-time derivative of the jointly `C¹` family, hence continuous:
  have hcont : ContinuousOn
      (fun s : ℝ =>
        Work.FTS.EpsEngine.Feps α ρ ε Φs E (Work.FTS.Galerkin.slice g s) z θ)
      (Set.Icc 0 δ) :=
    Work.FTS.StrongEps.IsEpsSolPQ.continuousOn_derivWithin_curve
      (f := fun p : ℝ × (ℝ × ℝ) => g p.1 p.2.1 p.2.2)
      (v := fun s : ℝ =>
        Work.FTS.EpsEngine.Feps α ρ ε Φs E (Work.FTS.Galerkin.slice g s) z θ)
      hδ hz hθ hreg.1 (fun s hs => by
        have h := hsol.2 z θ s hz hθ hs
        rwa [Work.FTS.EpsEngine.epsRHSP_eq_Feps_slice α ρ ε Φs E] at h)
  have hmemI : Set.MapsTo (fun s : ℝ => (z, (θ, s))) (Set.Icc 0 τ)
      (Work.FTS.StrongEps.IsEpsSolPQ.Dset δ) := by
    intro s hs
    rw [Work.FTS.StrongEps.IsEpsSolPQ.mem_Dset]
    exact ⟨hz, hθ0, hθ1, hs.1, le_trans hs.2 hτ.2⟩
  have hprim : ContinuousOn (fun s : ℝ => g z θ s) (Set.Icc 0 τ) :=
    hreg.1.continuousOn.comp (by fun_prop) hmemI
  have hint : IntervalIntegrable
      (fun s : ℝ =>
        Work.FTS.EpsEngine.Feps α ρ ε Φs E (Work.FTS.Galerkin.slice g s) z θ)
      MeasureTheory.volume 0 τ :=
    ContinuousOn.intervalIntegrable_of_Icc hτ.1
      (hcont.mono (fun x hx => ⟨hx.1, le_trans hx.2 hτ.2⟩))
  -- The fundamental theorem of calculus in the fake time:
  have hFTC : (∫ s in (0 : ℝ)..τ,
        Work.FTS.EpsEngine.Feps α ρ ε Φs E (Work.FTS.Galerkin.slice g s) z θ)
      = g z θ τ - g z θ 0 := by
    refine intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hτ.1 hprim (fun x hx => ?_) hint
    have hxδ : x < δ := lt_of_lt_of_le hx.2 hτ.2
    have h := hsol.2 z θ x hz hθ ⟨hx.1.le, hxδ.le⟩
    rw [Work.FTS.EpsEngine.epsRHSP_eq_Feps_slice α ρ ε Φs E] at h
    exact h.hasDerivAt (Icc_mem_nhds hx.1 hxδ)
  linarith [hFTC]

end Work.FTS.StrongEps.EpsE4Thr.Leaves.FlowBits
