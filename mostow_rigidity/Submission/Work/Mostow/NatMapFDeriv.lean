import Mathlib
import Submission.Work.Mostow.BCGDefs


set_option linter.unusedVariables false
namespace Work.Mostow

open Submission.Mostow LeanEval.Geometry.MostowRigidity MeasureTheory Filter

open scoped Topology

theorem NatMapFDeriv (n : ℕ) (hV : Submission.Mostow.VisualProp n) (hB : Submission.Mostow.BaryProp n)
    (φ : Submission.Mostow.E n → Submission.Mostow.E n)
    (hbij : Set.BijOn φ (Submission.Mostow.Sph n) (Submission.Mostow.Sph n))
    (hcont : ContinuousOn φ (Submission.Mostow.Sph n))
    (hzero : ∀ x y : Submission.Mostow.E n, Work.Mostow.Gv n φ x y = 0 ↔ y = Submission.Mostow.natMap φ x)
    (hC1 : ContDiff ℝ 1 (fun p : Submission.Mostow.E n × Submission.Mostow.E n =>
        Work.Mostow.Gv n φ p.1 p.2))
    (hder : ∀ p : Submission.Mostow.E n × Submission.Mostow.E n,
      fderiv ℝ (fun q : Submission.Mostow.E n × Submission.Mostow.E n => Work.Mostow.Gv n φ q.1 q.2) p
        = Work.Mostow.DGv n φ p.1 p.2)
    (hinv : (Work.Mostow.DGv n φ 0 0 ∘L ContinuousLinearMap.inr ℝ (Submission.Mostow.E n)
        (Submission.Mostow.E n)).IsInvertible)
    (h0 : Submission.Mostow.natMap φ 0 = 0) :
    ContDiffAt ℝ 1 (Submission.Mostow.natMap φ) 0 ∧
    HasFDerivAt (Submission.Mostow.natMap φ)
      (-(((Work.Mostow.DGv n φ 0 0 ∘L ContinuousLinearMap.inr ℝ (Submission.Mostow.E n)
            (Submission.Mostow.E n)).inverse) ∘L
        (Work.Mostow.DGv n φ 0 0 ∘L ContinuousLinearMap.inl ℝ (Submission.Mostow.E n)
          (Submission.Mostow.E n)))) 0 := by
  classical
  -- `f` is the joint `(x,y) ↦ Gv n φ x y` map whose zero set defines `natMap φ`.
  set f : Submission.Mostow.E n × Submission.Mostow.E n → Submission.Mostow.E n :=
    fun q => Work.Mostow.Gv n φ q.1 q.2 with hf
  have hcdf : ContDiffAt ℝ 1 f ((0, 0) : Submission.Mostow.E n × Submission.Mostow.E n) := by
    rw [hf]; exact hC1.contDiffAt
  have hfu : f ((0, 0) : Submission.Mostow.E n × Submission.Mostow.E n) = 0 := by
    rw [hf]; exact (hzero 0 0).mpr h0.symm
  have hfder : fderiv ℝ f ((0, 0) : Submission.Mostow.E n × Submission.Mostow.E n) = Work.Mostow.DGv n φ 0 0 := by
    rw [hf]; exact hder (0, 0)
  have hinv' : (fderiv ℝ f ((0, 0) : Submission.Mostow.E n × Submission.Mostow.E n) ∘L
      ContinuousLinearMap.inr ℝ (Submission.Mostow.E n) (Submission.Mostow.E n)).IsInvertible := by
    rw [hfder]; exact hinv
  -- the implicit function produced by the implicit function theorem
  set ψ : Submission.Mostow.E n → Submission.Mostow.E n :=
    hcdf.implicitFunction one_ne_zero hinv' with hψ
  -- it satisfies the same equation as `natMap φ`, hence agrees with it near `0`
  have hψ_ev : ψ =ᶠ[𝓝 (0 : Submission.Mostow.E n)] Submission.Mostow.natMap φ := by
    rw [hψ]
    filter_upwards [hcdf.eventually_apply_implicitFunction one_ne_zero hinv'] with x hx
    have hx0 : Work.Mostow.Gv n φ x (hcdf.implicitFunction one_ne_zero hinv' x) = 0 := by
      have h1 : f (x, hcdf.implicitFunction one_ne_zero hinv' x) = 0 := by rw [hx, hfu]
      simpa only [hf] using h1
    exact (hzero x _).mp hx0
  have hcont' : ContDiffAt ℝ 1 (Submission.Mostow.natMap φ) 0 := by
    have h : ContDiffAt ℝ 1 ψ ((0, 0) : Submission.Mostow.E n × Submission.Mostow.E n).1 := hcdf.contDiffAt_implicitFunction one_ne_zero hinv'
    exact h.congr_of_eventuallyEq hψ_ev.symm
  refine ⟨hcont', ?_⟩
  have hss : HasFDerivAt ψ
      (-(fderiv ℝ f ((0, 0) : Submission.Mostow.E n × Submission.Mostow.E n) ∘L ContinuousLinearMap.inr ℝ (Submission.Mostow.E n)
          (Submission.Mostow.E n)).inverse ∘L
        (fderiv ℝ f ((0, 0) : Submission.Mostow.E n × Submission.Mostow.E n) ∘L ContinuousLinearMap.inl ℝ (Submission.Mostow.E n)
          (Submission.Mostow.E n))) 0 :=
    (hcdf.hasStrictFDerivAt_implicitFunction one_ne_zero hinv').hasFDerivAt
  have hss2 := hss.congr_of_eventuallyEq hψ_ev.symm
  rw [hfder] at hss2
  exact hss2

end Work.Mostow
