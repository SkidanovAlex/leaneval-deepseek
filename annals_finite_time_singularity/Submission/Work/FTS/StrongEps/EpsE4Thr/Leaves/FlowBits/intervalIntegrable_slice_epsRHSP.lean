import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Submission.Work.FTS.EpsEngine.aesm_epsRHSP_fam_of_gate
import Submission.Work.FTS.EpsEngine.EpsClass
import Submission.Work.FTS.EpsEngine.LocalStepXBall
import Submission.Work.FTS.EpsEngine.Feps_intervalIntegrable_pt

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.EpsE4Thr.Leaves.FlowBits

theorem intervalIntegrable_slice_epsRHSP {α C₁ Ce Cs R ε δ Lw : ℝ} {ρ : ℝ × ℝ → ℝ}
    {Φs : Work.FTS.Galerkin.Fn} {E : Work.FTS.Galerkin.Fn → Work.FTS.Galerkin.Fn}
    {g : Work.FTS.Galerkin.Fam}
    (hα : α ∈ Set.Ioc 0 1) (hρ : Work.FTS.StrongEps.IsSmoothKernel ρ) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hR : 0 ≤ R)
    (hEll : ∀ u : Work.FTS.Galerkin.Fn, Work.FTS.ClassC.ClassC α u →
      Work.FTS.VocabO.EllPkgGo α Ce u (E u) ∧ Work.FTS.ClassC.EllPkgK α 6 Ce u (E u))
    (hstar : Work.FTS.VocabO2.StarPkgo2 α Cs Φs) (hml : Work.FTS.StrongEps.MuLamOK α C₁ Φs E)
    (hδ : 0 ≤ δ) (hLw : 0 ≤ Lw)
    (hX : ∀ τ ∈ Set.Icc 0 δ, Work.FTS.EpsEngine.XBall α ρ ε R C₁ (Work.FTS.Galerkin.slice g τ))
    (hEq : ∀ s ∈ Set.Icc 0 δ, ∀ t ∈ Set.Icc 0 δ,
      Work.FTS.StrongEps.EpsSq α (fun z θ => Work.FTS.Galerkin.slice g s z θ - Work.FTS.Galerkin.slice g t z θ)
        ≤ Lw * (s - t) ^ 2) :
    ∀ z θ : ℝ, (z, θ) ∈ Work.FTS.EllipticEst.Q0 →
      IntervalIntegrable (fun u : ℝ => Work.FTS.EpsEngine.Feps α ρ ε Φs E
        (Work.FTS.Galerkin.slice g u) z θ) MeasureTheory.volume 0 δ := by
  intro z θ hzθ
  obtain ⟨hz, hθ1, hθ2⟩ := hzθ
  -- the pointwise Lipschitz gate of the scheme's right-hand side on the `X`-ball
  obtain ⟨C, hCpos, hpt⟩ :=
    Work.FTS.EpsEngine.pt_of_XBall (α := α) (C₀ := C₁) (R := R) (Ce := Ce) (Cs := Cs)
      (ρ := ρ) (Φs := Φs) (E := E) (ε := ε) hα hρ hε hε1 hEll hstar hml hR
  -- the curve is `EpsSq`-Lipschitz in the fake time, hence the integrand is Lipschitz in `u`
  have hstep : ∀ s ∈ Set.Icc 0 δ, ∀ t ∈ Set.Icc 0 δ,
      |Work.FTS.EpsEngine.Feps α ρ ε Φs E (Work.FTS.Galerkin.slice g s) z θ
        - Work.FTS.EpsEngine.Feps α ρ ε Φs E (Work.FTS.Galerkin.slice g t) z θ|
        ≤ (C * Real.sqrt Lw) * |s - t| := by
    intro s hs t ht
    have h1 := hpt (Work.FTS.Galerkin.slice g s) (Work.FTS.Galerkin.slice g t)
      (hX s hs) (hX t ht) z θ hz hθ1 hθ2
    have h2 : Real.sqrt (Work.FTS.StrongEps.EpsSq α (fun z θ =>
        Work.FTS.Galerkin.slice g s z θ - Work.FTS.Galerkin.slice g t z θ))
        ≤ Real.sqrt Lw * |s - t| := by
      rw [← Real.sqrt_sq_eq_abs, ← Real.sqrt_mul hLw]
      exact Real.sqrt_le_sqrt (hEq s hs t ht)
    calc |Work.FTS.EpsEngine.Feps α ρ ε Φs E (Work.FTS.Galerkin.slice g s) z θ
          - Work.FTS.EpsEngine.Feps α ρ ε Φs E (Work.FTS.Galerkin.slice g t) z θ|
        ≤ C * Real.sqrt (Work.FTS.StrongEps.EpsSq α (fun z θ =>
            Work.FTS.Galerkin.slice g s z θ - Work.FTS.Galerkin.slice g t z θ)) := h1
      _ ≤ C * (Real.sqrt Lw * |s - t|) := mul_le_mul_of_nonneg_left h2 hCpos.le
      _ = (C * Real.sqrt Lw) * |s - t| := by ring
  have hLipOn : LipschitzOnWith ⟨C * Real.sqrt Lw, mul_nonneg hCpos.le (Real.sqrt_nonneg Lw)⟩
      (fun u : ℝ => Work.FTS.EpsEngine.Feps α ρ ε Φs E (Work.FTS.Galerkin.slice g u) z θ)
      (Set.Icc 0 δ) :=
    LipschitzOnWith.of_dist_le_mul (fun s hs t ht => by
      rw [Real.dist_eq, Real.dist_eq]
      exact hstep s hs t ht)
  exact ContinuousOn.intervalIntegrable_of_Icc hδ hLipOn.continuousOn

end Work.FTS.StrongEps.EpsE4Thr.Leaves.FlowBits
