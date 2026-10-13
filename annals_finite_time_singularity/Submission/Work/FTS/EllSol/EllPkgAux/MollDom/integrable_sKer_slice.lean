import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.EllSol.EllPkgAux.KernelDefs
import Submission.Work.FTS.EllSol.EllPkgAux.MollDom.mmDefs
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.Spaces.Defs
import Submission.Work.Spaces.aesm_slice_of_continuousOn_Qd
import Submission.Work.FTS.EllSol.EllPkgAux.MollDom.integrableOn_exp_comp

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllSol.EllPkgAux.MollDom

set_option linter.unusedVariables false

open MeasureTheory Set Filter
open scoped Real Topology

/-!
# Integrability of the logarithmic slice of the mollification kernel

The mollification `zmoll` of the datum `X` in the logarithmic radial variable convolves the
`σ_η`-weighted angular slice functional against the kernel `sKer δ (log z - t)`.  This file
proves that this is legitimate, i.e. that the slice is integrable as soon as the weighted
slice functional is integrable on `Iz`:

`Integrable (fun t => sKer δ (log z - t) * ∫_{Iθ} X (e^t) s² σ_η(s) ds)`.

The proof is a three-line reduction.

* `sKer δ` is supported in `[-δ, δ]`, so the `t`-integrand lives on the compact interval
  `[log z - δ, log z + δ]`; it therefore suffices to prove integrability there and to glue
  with `MeasureTheory.integrableOn_iff_integrable_of_support_subset`.
* on a compact subinterval `[a, b]` of `(0, ∞)` the weight `w` is bounded below, so the
  hypothesis `IntegrableOn (w z ² ∫_{Iθ} X z s² σ_η s) Iz` gives integrability of the raw
  slice functional `F u = ∫_{Iθ} X u s² σ_η s` there (multiply by the continuous factor
  `(w · ²)⁻¹`);
* the change of variables `u = e^t` (`integrableOn_exp_comp`) converts that into integrability
  of `t ↦ F (e^t)`, and `sKer δ (log z - ·)` is continuous, so
  `IntegrableOn.mul_continuousOn` finishes.
-/

theorem integrable_sKer_slice {X : ℝ → ℝ → ℝ}
    (hX : ContinuousOn (Function.uncurry X) Work.FTS.EllipticEst.Q0)
    {δ z : ℝ} (hδ : 0 < δ) (hz : 0 < z)
    (hdd : MeasureTheory.IntegrableOn (fun u : ℝ => (Work.Spaces.w u) ^ 2 *
      (∫ s in Work.Spaces.Iθ, X u s ^ 2 * Work.FTS.EllipticEst.thEta s)) Work.Spaces.Iz) :
    MeasureTheory.Integrable (fun t : ℝ =>
      Work.FTS.EllSol.PkgK5.K5c.sKer δ (Real.log z - t) *
        (∫ s in Work.Spaces.Iθ, X (Real.exp t) s ^ 2 * Work.FTS.EllipticEst.thEta s))
      MeasureTheory.volume := by
  -- ### Step 1: the raw slice functional is integrable on compact subintervals of `(0,∞)`
  have hFint : ∀ a b : ℝ, 0 < a → a ≤ b →
      MeasureTheory.IntegrableOn (fun u : ℝ =>
        ∫ s in Work.Spaces.Iθ, X u s ^ 2 * Work.FTS.EllipticEst.thEta s) (Set.Icc a b) := by
    intro a b ha _hab
    -- restrict the hypothesis to the compact subinterval
    have hsub : Set.Icc a b ⊆ Work.Spaces.Iz := by
      intro u hu
      exact le_of_lt (lt_of_lt_of_le ha hu.1)
    have h1 := hdd.mono_set hsub
    -- the weight `w²` does not vanish on `[a,b]` (`a > 0`)
    have hw2 : ∀ u ∈ Set.Icc a b, (Work.Spaces.w u) ^ 2 ≠ 0 := by
      intro u hu
      have hu0 : 0 < u := lt_of_lt_of_le ha hu.1
      have hw : Work.Spaces.w u ≠ 0 := by
        rw [Work.Spaces.w]
        exact div_ne_zero (pow_ne_zero 2 (by linarith)) (pow_ne_zero 2 (ne_of_gt hu0))
      exact pow_ne_zero 2 hw
    -- hence `(w · ²)⁻¹` is continuous there and we may divide
    have hwcont : ContinuousOn (fun u : ℝ => ((Work.Spaces.w u) ^ 2)⁻¹) (Set.Icc a b) := by
      refine ContinuousOn.inv₀ ?_ hw2
      refine ContinuousOn.pow ?_ 2
      have hw : Work.Spaces.w = fun u : ℝ => (1 + u) ^ 2 / u ^ 2 := rfl
      rw [hw]
      refine ContinuousOn.div ((continuousOn_const.add continuousOn_id).pow 2)
        (continuousOn_id.pow 2) ?_
      intro u hu
      exact pow_ne_zero 2 (ne_of_gt (lt_of_lt_of_le ha hu.1))
    have h2 := h1.mul_continuousOn hwcont isCompact_Icc
    refine h2.congr_fun (fun u hu => ?_) measurableSet_Icc
    have h0 := hw2 u hu
    show (Work.Spaces.w u ^ 2 *
          (∫ s in Work.Spaces.Iθ, X u s ^ 2 * Work.FTS.EllipticEst.thEta s))
        * (Work.Spaces.w u ^ 2)⁻¹
      = ∫ s in Work.Spaces.Iθ, X u s ^ 2 * Work.FTS.EllipticEst.thEta s
    rw [show (Work.Spaces.w u ^ 2 *
            (∫ s in Work.Spaces.Iθ, X u s ^ 2 * Work.FTS.EllipticEst.thEta s))
          * (Work.Spaces.w u ^ 2)⁻¹
        = (∫ s in Work.Spaces.Iθ, X u s ^ 2 * Work.FTS.EllipticEst.thEta s)
          * ((Work.Spaces.w u ^ 2) * (Work.Spaces.w u ^ 2)⁻¹) from by ring,
      mul_inv_cancel₀ h0, mul_one]
  -- ### Step 2: change variables `u = exp t`
  have hexp := integrableOn_exp_comp hFint (Real.log z - δ) (Real.log z + δ)
  -- ### Step 3: multiply by the (continuous) compactly supported kernel
  have hKcont : ContinuousOn (fun t : ℝ => Work.FTS.EllSol.PkgK5.K5c.sKer δ (Real.log z - t))
      (Set.Icc (Real.log z - δ) (Real.log z + δ)) :=
    ((Work.FTS.EllSol.K5cAux.continuous_sKer δ).comp
      (continuous_const.sub continuous_id)).continuousOn
  have hInt := hexp.mul_continuousOn hKcont isCompact_Icc
  have hInt' : MeasureTheory.IntegrableOn (fun t : ℝ =>
      Work.FTS.EllSol.PkgK5.K5c.sKer δ (Real.log z - t) *
        (∫ s in Work.Spaces.Iθ, X (Real.exp t) s ^ 2 * Work.FTS.EllipticEst.thEta s))
      (Set.Icc (Real.log z - δ) (Real.log z + δ)) :=
    hInt.congr_fun (fun t _ => mul_comm _ _) measurableSet_Icc
  -- ### Step 4: the integrand vanishes off the support of the kernel
  have hsup : Function.support (fun t : ℝ =>
      Work.FTS.EllSol.PkgK5.K5c.sKer δ (Real.log z - t) *
        (∫ s in Work.Spaces.Iθ, X (Real.exp t) s ^ 2 * Work.FTS.EllipticEst.thEta s))
      ⊆ Set.Icc (Real.log z - δ) (Real.log z + δ) := by
    intro t ht
    have hmul := Function.mem_support.mp ht
    have hK0 : Work.FTS.EllSol.PkgK5.K5c.sKer δ (Real.log z - t) ≠ 0 :=
      fun h0 => hmul (by rw [h0, zero_mul])
    have habs : |Real.log z - t| < δ := by
      by_contra hle
      exact hK0 (Work.FTS.EllSol.PkgK5.K5c.sKer_eq_zero_of_le_abs hδ (not_lt.mp hle))
    rw [Set.mem_Icc]
    rw [abs_lt] at habs
    exact ⟨by linarith [habs.2], by linarith [habs.1]⟩
  exact (integrableOn_iff_integrable_of_support_subset hsup).mp hInt'

end Work.FTS.EllSol.EllPkgAux.MollDom
