import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS_EllLimOK.Pinning.hpin_of_hasPkgD

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS_EllLimOK.Pinning

set_option autoImplicit false

theorem hpin_of_pkgCos {α Ce : ℝ} (hα : 0 < α) (hα1 : α ≤ 1)
    {E : Work.FTS.Galerkin.Fn →ₗ[ℝ] Work.FTS.Galerkin.Fn}
    (h : Work.FTS_EllLimOK.HasPkg α Ce E) (hcos : Work.FTS_EllLimOK.PkgCos α E) :
    ∀ g : Work.FTS.Galerkin.Fn, Work.FTS.ClassC.ClassC α g → ∀ z ∈ Set.Ioi (0 : ℝ),
      Filter.Tendsto (fun s => Real.cos s
        * Work.Construction.PhiTil α g (E g) z s)
        (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0) := by
  intro g hg z hz
  obtain ⟨hGo, _hK6⟩ := h g hg
  set Ψ : ℝ → ℝ → ℝ := Work.Construction.PhiTil α g (E g) with hΨ
  have hsm : Work.FTS.EllipticEst.SmoothOpen Ψ :=
    Work.FTS.GalFields.RHS.Sharp.smoothOpen_PhiTil hα hGo
  have hVsm : Work.FTS.EllipticEst.SmoothOpen (Work.Construction.Vop Ψ) := hGo.V.1.1
  have hV4 : Work.Spaces.HkMem α 4 (Work.Construction.Vop Ψ) := hGo.V.1.2
  have hV0 : Work.Spaces.HkMem α 0 (Work.Construction.Vop Ψ) :=
    Work.FTS.OpenPkg.HkMem_mono_open hVsm 0 (by norm_num) hV4
  have hmemCos : Work.Spaces.HkMem α 0 (fun z θ => Ψ z θ / Real.cos θ) := hcos g hg
  have hVint : MeasureTheory.IntegrableOn
      (fun θ => (Work.Construction.Vop Ψ z θ) ^ 2
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) Work.Spaces.Iθ :=
    integrableOn_sq_rpow_of_HkMem hVsm hV0 z hz
  have hcint : MeasureTheory.IntegrableOn
      (fun θ => (Ψ z θ / Real.cos θ) ^ 2
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) Work.Spaces.Iθ :=
    integrableOn_sq_rpow_of_HkMem (smoothOpen_div_cos hsm) hmemCos z hz
  have h1 : MeasureTheory.IntegrableOn
      (fun θ => (Real.cos θ * Ψ z θ) ^ 2
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta + 4)))
      (Set.Ioo (Real.pi / 6) (Real.pi / 2)) :=
    integrableOn_cos_sq_rpow_tail hsm hz hcint
  have h2 : MeasureTheory.IntegrableOn
      (fun θ => (deriv (fun s => Real.cos s * Ψ z s) θ) ^ 2
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) (Set.Ioo 0 (Real.pi / 2)) :=
    integrableOn_deriv_cos_mul_sq_rpow hsm hz hVint
  have ht : (Real.pi / 6) ∈ Set.Ioo 0 (Real.pi / 2) :=
    ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
  have hmain := Work.FTS_EllLimOK.SliceTrace.tendsto_zero_of_deriv_sq_integrable
    (η := Work.Spaces.eta) (γ := Work.Spaces.eta + 4)
    (by norm_num [Work.Spaces.eta]) (by norm_num [Work.Spaces.eta]) ht
    (contDiffOn_one_cos_mul_slice hsm hz) h1 h2
  exact hmain

end Work.FTS_EllLimOK.Pinning
