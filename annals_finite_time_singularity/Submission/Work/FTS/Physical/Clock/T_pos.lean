/-
# `Work.FTS.Physical.Clock.T_pos` — positivity of the blow-up time

The blow-up time of the dynamic rescaling is `T = ∫₀^∞ A`, where the amplitude `A > 0` solves the
modulation ODE `A' = -(1 + μ) A` with `1/2 ≤ 1 + μ ≤ 2`.  Since `A` decays at least like
`e^{-τ/2}`, `A` is integrable on `[0, ∞)`, and since `A` is continuous and strictly positive there,
the integral is positive: the blow-up happens at a *positive* physical time.

The two ingredients, both proved here from the structure fields of `PhysClock`:

* `antitoneOn_A_mul_exp`: `τ ↦ A τ · e^{τ/2}` is antitone on `[0,∞)` (its derivative is
  `e^{τ/2} A τ (-(1+μ τ) + 1/2) ≤ 0`), whence `A s ≤ A 0 · e^{-s/2}`;
* `integrableOn_A_Tpos`: domination by the integrable function `A 0 · e^{-s/2}` on `[0,∞)`.

The final step uses the measurable-set criterion `0 < ∫_s f ↔ 0 < volume (support f ∩ s)` for
nonnegative integrable `f` together with `[0,1] ⊆ support A ∩ [0,∞)`.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Topology.Separation.CompletelyRegular
import Submission.Work.FTS.Physical.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open MeasureTheory

set_option autoImplicit false

namespace Work.FTS.Physical.Clock

/-- **Grönwall-type monotonicity of `τ ↦ A τ · e^{τ/2}`.**  This is the only place where the
modulation lower bound `1/2 ≤ 1 + μ` is used. -/
private theorem antitoneOn_A_mul_exp (C : Work.FTS.Physical.PhysClock) :
    AntitoneOn (fun t : ℝ => C.A t * Real.exp (t / 2)) (Set.Ici 0) := by
  refine antitoneOn_of_deriv_nonpos (convex_Ici 0) ?_ ?_ ?_
  · exact C.hAcont.mul ((Real.continuous_exp.comp (continuous_id.div_const 2)).continuousOn)
  · -- differentiability on the interior
    intro t ht
    have ht0 : 0 ≤ t := by
      have h := interior_subset ht
      simpa using h
    have h1 : HasDerivAt (fun s : ℝ => Real.exp (s / 2)) (Real.exp (t / 2) * (1 / 2)) t := by
      have h2 : HasDerivAt (fun s : ℝ => s / 2) (1 / 2) t := (hasDerivAt_id t).div_const 2
      simpa using h2.exp
    exact ((C.hAderiv t ht0).mul h1).differentiableAt.differentiableWithinAt
  · -- the derivative is nonpositive
    intro t ht
    have ht0 : 0 ≤ t := by
      have h := interior_subset ht
      simpa using h
    have h1 : HasDerivAt (fun s : ℝ => Real.exp (s / 2)) (Real.exp (t / 2) * (1 / 2)) t := by
      have h2 : HasDerivAt (fun s : ℝ => s / 2) (1 / 2) t := (hasDerivAt_id t).div_const 2
      simpa using h2.exp
    have hd : HasDerivAt (fun s : ℝ => C.A s * Real.exp (s / 2))
        (Real.exp (t / 2) * C.A t * (-(1 + C.mu t) + 1 / 2)) t := by
      have h3 := (C.hAderiv t ht0).mul h1
      convert h3 using 1
      ring
    rw [hd.deriv]
    exact mul_nonpos_of_nonneg_of_nonpos (mul_nonneg (Real.exp_pos _).le (C.hApos t ht0).le)
      (by linarith [C.hmu_lo t ht0])

/-- **Exponential decay of the amplitude**: `A s ≤ A 0 · e^{-s/2}` for `s ≥ 0`. -/
private theorem A_le_exp_half (C : Work.FTS.Physical.PhysClock) {s : ℝ} (hs : 0 ≤ s) :
    C.A s ≤ C.A 0 * Real.exp ((-(1 / 2)) * s) := by
  have h0mem : (0 : ℝ) ∈ Set.Ici 0 := le_refl (0 : ℝ)
  have hs' : s ∈ Set.Ici (0 : ℝ) := hs
  have hle : C.A s * Real.exp (s / 2) ≤ C.A 0 := by
    have h := antitoneOn_A_mul_exp C (a := 0) (b := s) h0mem hs' hs
    simpa using h
  have h1 : -(s / 2) = (-(1 / 2)) * s := by ring
  calc C.A s = C.A s * Real.exp (s / 2) * Real.exp (-(s / 2)) := by
        rw [mul_assoc, ← Real.exp_add, add_neg_cancel, Real.exp_zero, mul_one]
    _ ≤ C.A 0 * Real.exp (-(s / 2)) := mul_le_mul_of_nonneg_right hle (Real.exp_pos _).le
    _ = C.A 0 * Real.exp ((-(1 / 2)) * s) := by rw [h1]

/-- **Integrability of the amplitude on `[0,∞)`**: the blow-up happens in finite time. -/
private theorem integrableOn_A_Tpos (C : Work.FTS.Physical.PhysClock) :
    MeasureTheory.IntegrableOn C.A (Set.Ici 0) := by
  have hg : MeasureTheory.IntegrableOn (fun s : ℝ => Real.exp ((-(1 / 2)) * s)) (Set.Ici 0) :=
    (integrableOn_Ici_iff_integrableOn_Ioi).mpr (integrableOn_exp_mul_Ioi (by norm_num) 0)
  have hg2 : MeasureTheory.IntegrableOn (fun s : ℝ => C.A 0 * Real.exp ((-(1 / 2)) * s))
      (Set.Ici 0) := by
    show MeasureTheory.Integrable (fun s : ℝ => C.A 0 * Real.exp ((-(1 / 2)) * s))
      (volume.restrict (Set.Ici 0))
    exact (show MeasureTheory.Integrable (fun s : ℝ => Real.exp ((-(1 / 2)) * s))
      (volume.restrict (Set.Ici 0)) from hg).const_mul _
  have hmeas : MeasureTheory.AEStronglyMeasurable C.A (volume.restrict (Set.Ici 0)) :=
    C.hAcont.aestronglyMeasurable measurableSet_Ici
  have hbound : ∀ᵐ s ∂(volume.restrict (Set.Ici 0)),
      ‖C.A s‖ ≤ C.A 0 * Real.exp ((-(1 / 2)) * s) := by
    rw [MeasureTheory.ae_restrict_iff' measurableSet_Ici]
    exact Filter.Eventually.of_forall (fun s hs => by
      rw [Real.norm_of_nonneg (C.hApos s hs).le]
      exact A_le_exp_half C hs)
  exact hg2.mono' hmeas hbound

/-- **The blow-up time is positive.** -/
theorem T_pos (C : Work.FTS.Physical.PhysClock) : 0 < C.T := by
  change 0 < ∫ s in Set.Ici (0 : ℝ), C.A s
  have hint : MeasureTheory.IntegrableOn C.A (Set.Ici 0) := integrableOn_A_Tpos C
  have hnn : 0 ≤ᵐ[volume.restrict (Set.Ici 0)] C.A := by
    have h : ∀ᵐ s ∂(volume.restrict (Set.Ici 0)), 0 ≤ C.A s := by
      rw [MeasureTheory.ae_restrict_iff' measurableSet_Ici]
      exact Filter.Eventually.of_forall (fun s hs => (C.hApos s hs).le)
    exact h
  rw [MeasureTheory.setIntegral_pos_iff_support_of_nonneg_ae hnn hint]
  have hpos : (0 : ENNReal) < volume (Set.Icc (0 : ℝ) 1) := by
    rw [Real.volume_Icc]
    exact ENNReal.ofReal_pos.mpr (by norm_num)
  have hsub : Set.Icc (0 : ℝ) 1 ⊆ Function.support C.A ∩ Set.Ici 0 := by
    intro x hx
    exact ⟨(C.hApos x hx.1).ne', hx.1⟩
  exact lt_of_lt_of_le hpos (MeasureTheory.measure_mono hsub)

end Work.FTS.Physical.Clock
