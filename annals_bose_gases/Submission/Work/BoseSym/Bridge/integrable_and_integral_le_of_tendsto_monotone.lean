import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Submission.Work.BoseSym.Interface
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Monotone convergence inside the Bosonic reduction (integration bridge)

`Work.BoseSym.Bridge.integrable_and_integral_le_of_tendsto_monotone`: a pointwise
monotone sequence of almost-everywhere nonnegative, integrable functions whose
integrals are uniformly bounded by `c` converges (pointwise, everywhere) to an
almost-everywhere measurable `g`, which is then integrable with integral `≤ c`.

This is the "pass to the limit in an energy estimate" bridge: the proof is the
monotone convergence theorem for the `ℝ≥0∞`-valued functions
`x ↦ ENNReal.ofReal (f k x)` together with the identification of `∫⁻` and `∫`
for nonnegative integrable functions.
-/

namespace Work.BoseSym.Bridge

open MeasureTheory Filter
open scoped ENNReal

theorem integrable_and_integral_le_of_tendsto_monotone {N : ℕ} {f : ℕ → Work.BoseSym.Conf N → ℝ}
    {g : Work.BoseSym.Conf N → ℝ} {c : ℝ}
    (hf0 : ∀ k, Work.BoseSym.AENonneg N (f k)) (hmono : ∀ k x, f k x ≤ f (k + 1) x)
    (hgm : Work.BoseSym.AEMeas N g)
    (htend : ∀ x, Filter.Tendsto (fun k => f k x) Filter.atTop (nhds (g x)))
    (hfint : ∀ k, MeasureTheory.Integrable (f k) (Work.BoseSym.volC N))
    (hb : ∀ k, ∫ x, f k x ∂(Work.BoseSym.volC N) ≤ c) :
    MeasureTheory.Integrable g (Work.BoseSym.volC N) ∧
      ∫ x, g x ∂(Work.BoseSym.volC N) ≤ c := by
  have hfmeas : ∀ k, AEMeasurable (f k) (Work.BoseSym.volC N) := fun k => (hfint k).aemeasurable
  -- the (countably many) almost-everywhere nonnegativity statements hold simultaneously
  have hf0' : ∀ᵐ x ∂(Work.BoseSym.volC N), ∀ k, 0 ≤ f k x := ae_all_iff.2 hf0
  have hgnn : 0 ≤ᵐ[Work.BoseSym.volC N] g := by
    filter_upwards [hf0'] with x hx
    exact ge_of_tendsto' (htend x) hx
  -- monotone convergence for the `ℝ≥0∞`-valued functions `ENNReal.ofReal (f k ·)`
  have hmono_ae : ∀ᵐ x ∂(Work.BoseSym.volC N), Monotone fun k => ENNReal.ofReal (f k x) :=
    Eventually.of_forall fun x k m hkm =>
      ENNReal.ofReal_le_ofReal ((monotone_nat_of_le_succ fun j => hmono j x) hkm)
  have htend_ae : ∀ᵐ x ∂(Work.BoseSym.volC N),
      Tendsto (fun k => ENNReal.ofReal (f k x)) Filter.atTop (nhds (ENNReal.ofReal (g x))) :=
    Eventually.of_forall fun x =>
      (ENNReal.continuous_ofReal.tendsto (g x)).comp (htend x)
  have hlim := lintegral_tendsto_of_tendsto_of_monotone
    (fun k => (hfmeas k).ennreal_ofReal) hmono_ae htend_ae
  -- identify the `ℝ≥0∞`-integrals with the real integrals
  have hk : ∀ k, ∫⁻ x, ENNReal.ofReal (f k x) ∂(Work.BoseSym.volC N)
      = ENNReal.ofReal (∫ x, f k x ∂(Work.BoseSym.volC N)) :=
    fun k => (ofReal_integral_eq_lintegral_ofReal (hfint k) (hf0 k)).symm
  have hc0 : 0 ≤ c := le_trans (integral_nonneg_of_ae (hf0 0)) (hb 0)
  have hgle : ∫⁻ x, ENNReal.ofReal (g x) ∂(Work.BoseSym.volC N) ≤ ENNReal.ofReal c := by
    refine le_of_tendsto' hlim fun k => ?_
    rw [hk k]
    exact ENNReal.ofReal_le_ofReal (hb k)
  -- `g` is nonnegative a.e., so `‖g‖ = g` a.e. and the `ℝ≥0∞`-bound bounds `‖g‖ₑ`
  have hnorm : ∫⁻ x, ENNReal.ofReal ‖g x‖ ∂(Work.BoseSym.volC N)
      = ∫⁻ x, ENNReal.ofReal (g x) ∂(Work.BoseSym.volC N) := by
    refine lintegral_congr_ae ?_
    filter_upwards [hgnn] with x hx
    rw [Real.norm_of_nonneg hx]
  refine ⟨⟨hgm.aestronglyMeasurable, ?_⟩, ?_⟩
  · rw [hasFiniteIntegral_iff_norm, hnorm]
    exact lt_of_le_of_lt hgle ENNReal.ofReal_lt_top
  · rw [integral_eq_lintegral_of_nonneg_ae hgnn hgm.aestronglyMeasurable]
    calc (∫⁻ x, ENNReal.ofReal (g x) ∂(Work.BoseSym.volC N)).toReal
        ≤ (ENNReal.ofReal c).toReal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hgle
      _ = c := ENNReal.toReal_ofReal hc0

end Work.BoseSym.Bridge
