import Mathlib
import Submission.Work.Asymptotics.DomainD
import Submission.Work.Asymptotics.F2LayerDefs
import Submission.Work.Asymptotics.GcuspDefs
import Submission.Work.Asymptotics.Kaxis_local_coincidence
import Submission.Work.Asymptotics.continuousOn_Kfun_clean
import Submission.Work.LayerCont.GcuspHolomorphic
import Submission.Work.CKFinal.AxisCont.Basic
import Submission.Work.Asymptotics.eq_one_or_neg_one_or_S_of_smul_imagAxis
import Submission.Work.Asymptotics.measurable_Kaxis_Kfun
import Submission.Work.Asymptotics.differentiableAt_Kfun_tau
import Submission.Work.Asymptotics.HalfFunnel.tangTailExpansion

/-!
# The trunc integrand is measurable in `t` and a.e. continuous in `τ`

The truncated contour integrand of CKMRV is

  `Φ(τ,t) = (K^{(d)}(τ,it) - 𝒢(τ,it)) · e^{-πr²t}`,   `t ≥ 1`,

i.e. `Kaxis (Kfun ℓ d) · t` minus its non-decaying part `Aexp (Gcusp ℓ d) · t`, times the
Gaussian weight.  The dominated-convergence argument for the continuity of `τ ↦ layerTrunc`
needs exactly two pieces of data, provided by this file:

* **`AEStronglyMeasurable` in `t`, eventually near `τ₁`** — in fact for *every* `τ`:
  `t ↦ Kaxis (Kfun ℓ d) τ t` is measurable without any hypothesis
  (`Work.Asymptotics.measurable_Kaxis_Kfun`), `t ↦ Aexp (Gcusp ℓ d) τ t` is continuous
  (`continuous_Aexp_tang`) and the Gaussian weight is continuous.

* **`ContinuousAt` in `τ` at `τ₁`, for a.e. `t`** — for `t ∉ S`, `S` the (at most two-element)
  coincidence set of `τ₁` with the contour (`Work.CKFinal.finite_coincidenceSet_imagAxis`), the
  kernel `τ ↦ K^{(d)}(τ,it)` is complex differentiable at `τ₁`
  (`Work.Asymptotics.differentiableAt_Kfun_tau`, `UpperHalfPlane.mdifferentiableAt_iff`), `Aexp`
  is continuous in `τ` (`continuous_Aexp_tang`), and the Gaussian weight does not depend on `τ`.
  Since `S` is finite its measure is zero, so the bad `t`'s form a null set.
-/

namespace Work.CKFinal.AxisCont

open MeasureTheory Filter Topology
open UpperHalfPlane Work.Kernels

theorem trunc_integrand_ae_data (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    (r : ℝ) {τ₁ : UpperHalfPlane} (hτ₁ : τ₁ ∈ Work.Asymptotics.DomainD) :
    (Filter.Eventually (fun τ : UpperHalfPlane => MeasureTheory.AEStronglyMeasurable (fun t : ℝ =>
        (Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t
          - Work.Asymptotics.Aexp (Work.Asymptotics.Gcusp ℓ d) τ t)
        * Complex.exp (-(Real.pi * (r : ℂ) ^ 2 * (t : ℂ))))
        (MeasureTheory.volume.restrict (Set.Ici (1 : ℝ)))) (nhds τ₁)) ∧
    (Filter.Eventually (fun t : ℝ => ContinuousAt (fun τ : UpperHalfPlane =>
        (Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t
          - Work.Asymptotics.Aexp (Work.Asymptotics.Gcusp ℓ d) τ t)
        * Complex.exp (-(Real.pi * (r : ℂ) ^ 2 * (t : ℂ)))) τ₁)
      (MeasureTheory.ae (MeasureTheory.volume.restrict (Set.Ici (1 : ℝ))))) := by
  -- The Gaussian weight `e^{-πr²t}` is measurable and continuous in `t`.
  have hgauss : Measurable (fun t : ℝ => Complex.exp (-(Real.pi * (r : ℂ) ^ 2 * (t : ℂ)))) := by
    fun_prop
  -- `t ↦ Aexp (Gcusp ℓ d) τ t` is continuous (hence measurable) in `t`, for every `τ`.
  have hAmeas : ∀ τ : UpperHalfPlane,
      Measurable (fun t : ℝ => Work.Asymptotics.Aexp (Work.Asymptotics.Gcusp ℓ d) τ t) :=
    fun τ => ((Work.Asymptotics.HalfFunnel.continuous_Aexp_tang ℓ d hd).comp
      (continuous_const.prodMk continuous_id)).measurable
  refine ⟨Filter.Eventually.of_forall fun τ => ?_, ?_⟩
  · -- ### Measurability in `t`, for every fixed `τ`
    exact (((Work.Asymptotics.measurable_Kaxis_Kfun ℓ d hd τ).sub (hAmeas τ)).mul
      hgauss).aestronglyMeasurable
  · -- ### A.e. continuity in `τ` at `τ₁`
    -- The coincidence set of `τ₁` with the contour is finite, hence null.
    obtain ⟨S, hSfin, hS⟩ := Work.CKFinal.finite_coincidenceSet_imagAxis hτ₁
    have hSae : ∀ᵐ t ∂(volume.restrict (Set.Ici (1 : ℝ))), t ∉ S := by
      rw [MeasureTheory.ae_iff]
      have hzero : (volume.restrict (Set.Ici (1 : ℝ))) S = 0 := by
        rw [Measure.restrict_apply hSfin.measurableSet]
        exact measure_mono_null Set.inter_subset_left (hSfin.measure_zero volume)
      simpa using hzero
    filter_upwards [hSae] with t htS
    -- `Aexp` is continuous in `τ` at `τ₁`, for every `t`.
    have hA : ContinuousAt (fun τ : UpperHalfPlane =>
        Work.Asymptotics.Aexp (Work.Asymptotics.Gcusp ℓ d) τ t) τ₁ :=
      ((Work.Asymptotics.HalfFunnel.continuous_Aexp_tang ℓ d hd).comp
        (continuous_id.prodMk continuous_const)).continuousAt
    by_cases ht : 0 < t
    · -- Clean `t`: the kernel itself is complex differentiable in `τ` at `τ₁`.
      have hJ : Work.Kernels.jInvariantFun τ₁
          ≠ Work.Kernels.jInvariantFun (Work.Kernels.imagAxis t ht) := fun h => htS (hS t ht h)
      have hmd : MDifferentiableAt (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ)
          (fun τ : UpperHalfPlane => Work.Kernels.Kfun ℓ d τ (Work.Kernels.imagAxis t ht)) τ₁ :=
        UpperHalfPlane.mdifferentiableAt_iff.mpr
          (Work.Asymptotics.differentiableAt_Kfun_tau (d := d) hd (τ := τ₁)
            (z := Work.Kernels.imagAxis t ht) hJ)
      have hfun : (fun τ : UpperHalfPlane =>
            (Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t
              - Work.Asymptotics.Aexp (Work.Asymptotics.Gcusp ℓ d) τ t)
            * Complex.exp (-(Real.pi * (r : ℂ) ^ 2 * (t : ℂ))))
          = fun τ : UpperHalfPlane =>
            (Work.Kernels.Kfun ℓ d τ (Work.Kernels.imagAxis t ht)
              - Work.Asymptotics.Aexp (Work.Asymptotics.Gcusp ℓ d) τ t)
            * Complex.exp (-(Real.pi * (r : ℂ) ^ 2 * (t : ℂ))) := by
        funext τ
        simp only [Work.Kernels.Kaxis, dif_pos ht]
      rw [hfun]
      exact (hmd.continuousAt.sub hA).mul continuousAt_const
    · -- `t ≤ 0`: `Kaxis` vanishes, and only `Aexp` varies with `τ`.
      have hfun : (fun τ : UpperHalfPlane =>
            (Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t
              - Work.Asymptotics.Aexp (Work.Asymptotics.Gcusp ℓ d) τ t)
            * Complex.exp (-(Real.pi * (r : ℂ) ^ 2 * (t : ℂ))))
          = fun τ : UpperHalfPlane =>
            ((0 : ℂ) - Work.Asymptotics.Aexp (Work.Asymptotics.Gcusp ℓ d) τ t)
            * Complex.exp (-(Real.pi * (r : ℂ) ^ 2 * (t : ℂ))) := by
        funext τ
        simp only [Work.Kernels.Kaxis, dif_neg ht]
      rw [hfun]
      exact (continuousAt_const.sub hA).mul continuousAt_const

end Work.CKFinal.AxisCont
