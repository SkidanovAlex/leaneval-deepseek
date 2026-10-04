import Mathlib
import Submission.Work.Diff.STE.B3.Comp
import Submission.Work.Diff.STE.B3.mat_jet_bound_global

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.STE.Lead

theorem psiComp_contDiffAt
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ((⊤ : ENat) : WithTop ENat) M] [T2Space M] [I.Boundaryless]
    {ι₀ : Type*} [Fintype ι₀] {g₀ : Submission.Diff.SMet I M}
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀)
    (h : Work.Diff.STE.Bil (I := I) (M := M))
    (hsm : Work.Diff.STE.D.ChartData (I := I) (M := M) h)
    (i : ι₀) (a b : Fin (Module.finrank ℝ E))
    (Psi : ((Fin (Module.finrank ℝ E) → ℝ) ×
        (Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → ℝ) ×
        (Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → ℝ)) →
      Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → ℝ)
    (hPsi : ContDiff ℝ ((⊤ : ENat) : WithTop ENat) Psi)
    (z : Fin (Module.finrank ℝ E) → ℝ) (hz : ‖z‖ ≤ 2 * D.σ i) :
    ContDiffAt ℝ ((⊤ : ENat) : WithTop ENat)
      (fun y : Fin (Module.finrank ℝ E) → ℝ =>
        ((Psi (y, (fun c d => D.mat i h c d y),
            (fun c d r => Work.Diff.STE.pdR r (D.mat i h c d) y)) a b : ℝ) : ℂ)) z := by
  -- The chart matrix `D.mat i h c d` is smooth at `z`: `hz` puts `flatToE z` in the chart target,
  -- so `Work.Diff.STE.B3.mat_contDiffAt_of_chartData` applies.
  have hmat : ∀ c d : Fin (Module.finrank ℝ E),
      ContDiffAt ℝ ((⊤ : ENat) : WithTop ENat) (D.mat i h c d) z := fun c d =>
    Work.Diff.STE.B3.mat_contDiffAt_of_chartData D h hsm i c d z (D.htarget i z hz)
  -- Hence so is the first derivative `Work.Diff.STE.pdR r (D.mat i h c d)`.
  have hpdR : ∀ c d r : Fin (Module.finrank ℝ E),
      ContDiffAt ℝ ((⊤ : ENat) : WithTop ENat)
        (fun y => Work.Diff.STE.pdR r (D.mat i h c d) y) z := by
    intro c d r
    have hfd : ContDiffAt ℝ ((⊤ : ENat) : WithTop ENat) (fderiv ℝ (D.mat i h c d)) z :=
      (hmat c d).fderiv_right (by simp)
    have := hfd.clm_apply (contDiffAt_const (c := Pi.single r (1 : ℝ)))
    simpa [Work.Diff.STE.pdR] using this
  -- The triple of data fed into `Psi` is therefore smooth at `z`.
  have hG : ContDiffAt ℝ ((⊤ : ENat) : WithTop ENat)
      (fun y : Fin (Module.finrank ℝ E) → ℝ =>
        (y, (fun c d => D.mat i h c d y),
          (fun c d r => Work.Diff.STE.pdR r (D.mat i h c d) y))) z := by
    refine ContDiffAt.prodMk contDiffAt_id ?_
    refine ContDiffAt.prodMk ?_ ?_
    · exact contDiffAt_pi.2 (fun c => contDiffAt_pi.2 (fun d => hmat c d))
    · exact contDiffAt_pi.2 (fun c => contDiffAt_pi.2 (fun d =>
        contDiffAt_pi.2 (fun r => hpdR c d r)))
  -- `Psi p a b` is the composition of `Psi` with two continuous linear projections.
  have hF : ContDiff ℝ ((⊤ : ENat) : WithTop ENat) (fun p => Psi p a b) := by
    have hlin : ContDiff ℝ ((⊤ : ENat) : WithTop ENat)
        (fun q : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → ℝ => q a b) := by
      fun_prop
    exact hlin.comp hPsi
  have hcomp := hF.contDiffAt.comp z hG
  have hcast := (Complex.ofRealCLM.contDiff.contDiffAt).comp z hcomp
  simpa [Function.comp_def] using hcast

end Work.Diff.STE.Lead
