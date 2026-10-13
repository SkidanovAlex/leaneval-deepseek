import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Submission.Work.FTS.EpsEngine.LimSmoothOpenEngine
import Submission.Work.FTS.EpsEngine.SmoothOpenIter
import Submission.Work.FTS.EpsEngine.LocalStepXBall
import Submission.Work.FTS.StrongEps.EpsLocalPStar.profRHS_sub_sup_le_Sq

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter
open Work.FTS.Galerkin (Fn slice)

namespace Work.FTS.EpsEngine

theorem Feps_intervalIntegrable_pt {α C₀ R Ce Cs Lw δ : ℝ} {ρ : ℝ × ℝ → ℝ} {Φs : Work.FTS.Galerkin.Fn}
    {E : Work.FTS.Galerkin.Fn → Work.FTS.Galerkin.Fn} {ε : ℝ} {h₀ : Work.FTS.Galerkin.Fn}
    (hα : α ∈ Set.Ioc 0 1) (hρ : Work.FTS.StrongEps.IsSmoothKernel ρ) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hEll : ∀ u : Work.FTS.Galerkin.Fn, Work.FTS.ClassC.ClassC α u →
      Work.FTS.VocabO.EllPkgGo α Ce u (E u) ∧ Work.FTS.ClassC.EllPkgK α 6 Ce u (E u))
    (hstar : Work.FTS.VocabO2.StarPkgo2 α Cs Φs)
    (hml : Work.FTS.StrongEps.MuLamOK α C₀ Φs E) (hR : 0 ≤ R) (hLw : 0 ≤ Lw) (n : ℕ)
    (hP : ∀ s ∈ Set.Icc 0 δ, Work.FTS.EpsEngine.XBall α ρ ε R C₀
      (Work.FTS.Galerkin.slice (Work.FTS.StrongEps.EpsLocalPStar.iter
        (Work.FTS.EpsEngine.Feps α ρ ε Φs E) h₀ n) s))
    (hEq : ∀ s ∈ Set.Icc 0 δ, ∀ t ∈ Set.Icc 0 δ,
      Work.FTS.StrongEps.EpsSq α (fun z θ =>
        Work.FTS.Galerkin.slice (Work.FTS.StrongEps.EpsLocalPStar.iter
          (Work.FTS.EpsEngine.Feps α ρ ε Φs E) h₀ n) s z θ
        - Work.FTS.Galerkin.slice (Work.FTS.StrongEps.EpsLocalPStar.iter
          (Work.FTS.EpsEngine.Feps α ρ ε Φs E) h₀ n) t z θ) ≤ Lw * (s - t) ^ 2)
    {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (π / 2)) {τ : ℝ} (hτ : τ ∈ Set.Icc 0 δ) :
    IntervalIntegrable (fun s => Work.FTS.EpsEngine.Feps α ρ ε Φs E
      (Work.FTS.Galerkin.slice (Work.FTS.StrongEps.EpsLocalPStar.iter
        (Work.FTS.EpsEngine.Feps α ρ ε Φs E) h₀ n) s) z θ)
      MeasureTheory.volume 0 τ := by
  -- the pointwise Lipschitz bound of the scheme's right-hand side in the profile
  obtain ⟨C, hCpos, hC⟩ :=
    Work.FTS.StrongEps.EpsLocalPStar.profRHS_sub_sup_le_Sq (α := α) (C₀ := C₀) (Ce := Ce)
      (Cs := Cs) (R := R) (ρ := ρ) (Φs := Φs) (E := E) (ε := ε)
      hα hρ hε hε1 hEll hstar hml hR
  have hpt : ∀ {u v : Fn}, XBall α ρ ε R C₀ u → XBall α ρ ε R C₀ v →
      ∀ z θ : ℝ, 0 < z → θ ∈ Set.Ioo 0 (π / 2) →
      |Feps α ρ ε Φs E u z θ - Feps α ρ ε Φs E v z θ|
        ≤ C * Real.sqrt (Work.FTS.StrongEps.EpsSq α (fun z θ => u z θ - v z θ)) := by
    intro u v hu hv z θ hz hθ
    have h1 := hC hu.smoothOpen hv.smoothOpen hu.mem hu.sq_le hv.mem hv.sq_le
      hu.classC hv.classC hu.ball hv.ball z θ hz hθ.1 hθ.2
    rw [← Feps_eq_epsRHPSlice α ρ ε Φs E 0 u,
      ← Feps_eq_epsRHPSlice α ρ ε Φs E 0 v] at h1
    exact h1
  set w : ℝ → Fn := fun s =>
    slice (Work.FTS.StrongEps.EpsLocalPStar.iter (Feps α ρ ε Φs E) h₀ n) s with hw
  -- the curve is `EpsSq`-Lipschitz in the fake time, hence the integrand is Lipschitz in `s`
  have hstep : ∀ s ∈ Set.Icc 0 δ, ∀ t ∈ Set.Icc 0 δ,
      |Feps α ρ ε Φs E (w s) z θ - Feps α ρ ε Φs E (w t) z θ|
        ≤ (C * Real.sqrt Lw) * |s - t| := by
    intro s hs t ht
    have h1 := hpt (hP s hs) (hP t ht) z θ hz hθ
    have h2 : Real.sqrt (Work.FTS.StrongEps.EpsSq α (fun z θ => w s z θ - w t z θ))
        ≤ Real.sqrt Lw * |s - t| := by
      rw [← Real.sqrt_sq_eq_abs, ← Real.sqrt_mul hLw]
      exact Real.sqrt_le_sqrt (hEq s hs t ht)
    calc |Feps α ρ ε Φs E (w s) z θ - Feps α ρ ε Φs E (w t) z θ|
        ≤ C * Real.sqrt (Work.FTS.StrongEps.EpsSq α (fun z θ => w s z θ - w t z θ)) := h1
      _ ≤ C * (Real.sqrt Lw * |s - t|) := mul_le_mul_of_nonneg_left h2 hCpos.le
      _ = (C * Real.sqrt Lw) * |s - t| := by ring
  have hLipOn : LipschitzOnWith ⟨C * Real.sqrt Lw, mul_nonneg hCpos.le (Real.sqrt_nonneg Lw)⟩
      (fun s : ℝ => Feps α ρ ε Φs E (w s) z θ) (Set.Icc 0 δ) :=
    LipschitzOnWith.of_dist_le_mul (fun s hs t ht => by
      rw [Real.dist_eq, Real.dist_eq]
      exact hstep s hs t ht)
  have hcont : ContinuousOn (fun s : ℝ => Feps α ρ ε Φs E (w s) z θ) (Set.Icc 0 δ) :=
    hLipOn.continuousOn
  have heq : (fun s : ℝ => Feps α ρ ε Φs E (w s) z θ)
      = fun s : ℝ => Feps α ρ ε Φs E
          (slice (Work.FTS.StrongEps.EpsLocalPStar.iter (Feps α ρ ε Φs E) h₀ n) s) z θ := by
    funext s
    simp only [hw]
  rw [heq] at hcont
  exact ContinuousOn.intervalIntegrable_of_Icc hτ.1 (hcont.mono (Set.Icc_subset_Icc_right hτ.2))

end Work.FTS.EpsEngine

end
