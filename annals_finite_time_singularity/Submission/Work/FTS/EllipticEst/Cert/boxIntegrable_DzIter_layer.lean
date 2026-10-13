/-
Copyright: work module for the Elgindi finite-time singularity project.

# Box integrability of the squared `∂_z D_z^j`-term (certificate layer)

For `F` smooth on the open quadrant `(0,∞) × (0,π/2)` (`Work.FTS.EllipticEst.SmoothOpen`)
and `F ∈ ℋ^k` (`Work.Spaces.HkMem α k F`), the uncurried function

  `(s,θ) ↦ (∂_z D_z^j F (s,θ))² · sin(2θ)^{-η}`

is integrable on the box `[a,b] ×ˢ Iθ` for every `0 < a < b` and every `j` with `j + 1 ≤ k`.

## Route

Write `G s θ` for the target integrand and recall `D_z^{j+1} F = z · ∂_z D_z^j F`
(definitional: `Dz f z θ = z * pz f z θ`).

* **Domination.**  On the box (`s > 0`, `θ ∈ Iθ`) the pointwise estimate

    `G s θ ≤ (D_z^{j+1} F (s,θ) · w(s)/sin(2θ)^{η/2})²`

  is exactly `Work.FTS.EllipticEst.pz_DzIter_sq_mul_sin_le_term`; the right-hand side is the
  `i = j + 1` slot of the `ℋ^k`-integrand, and `j + 1 ≤ k` bounds it by
  `Work.Spaces.HkIntegrand α k F s θ` (`Work.Spaces.sq_le_HkIntegrand_z`).

* **The majorant is integrable on the box.**  `HkIntegrand α k F` is nonnegative everywhere
  (it is a sum of squares, `Work.Spaces.HkIntegrand_nonneg`), continuous on the open
  quadrant (`Work.FTS.EllipticEst.SmoothOpen.continuousOn_HkIntegrand`), has integrable
  angular slices for every `s ∈ Iz` (`hmem.1`) and an integrable iterated `θ`-integral on
  `Iz ⊇ [a,b]` (`hmem.2`); so `Work.FTS.EllipticEst.integrableOn_box_of_slice` gives its box
  integrability.

* **A.e. strong measurability of `G` on the box.**  `G` is continuous on the open quadrant,
  hence a.e. strongly measurable for `(dz)|_{Iz} × (dθ)|_{Iθ}`
  (`Work.Spaces.aesm_of_continuousOn_Qd`); the box measure `(dz)|_{[a,b]} × (dθ)|_{Iθ}` is
  dominated by it, so `AEStronglyMeasurable.mono_measure` descends (the two product measures
  are rewritten as restrictions of the planar Lebesgue measure by `Measure.prod_restrict`).

* **Conclusion.**  `Integrable.mono'` combines the three.

Everything here is `sorry`-free and rests on `[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.EllipticEst.integrableOn_slice_l2
import Submission.Work.FTS.EllipticEst.integrableOn_box_of_slice
import Submission.Work.FTS.EllipticEst.pz_DzIter_sq_mul_sin_le_term

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.Cert

open MeasureTheory Set Filter
open scoped Real Topology

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 800000

theorem boxIntegrable_DzIter_layer (α : ℝ) (k : ℕ) {F : ℝ → ℝ → ℝ}
    (hF : Work.FTS.EllipticEst.SmoothOpen F)
    (hmem : Work.Spaces.HkMem α k F) (j : ℕ) (hj : j + 1 ≤ k) :
    ∀ a b : ℝ, 0 < a → a < b →
      MeasureTheory.IntegrableOn (Function.uncurry (fun s θ : ℝ =>
        (Work.Spaces.pz (Work.Spaces.DzIter j F) s θ) ^ 2
          * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))) (Set.Icc a b ×ˢ Work.Spaces.Iθ) := by
  intro a b ha hab
  -- `[a,b] ⊆ Iz = [0,∞)` because `0 < a`.
  have hsub : Set.Icc a b ⊆ Work.Spaces.Iz :=
    fun x hx => Set.mem_Ici.mpr (le_trans (le_of_lt ha) hx.1)
  -- **The majorant**: the `ℋ^k`-integrand, integrable on the box.
  have hM : MeasureTheory.IntegrableOn
      (Function.uncurry (fun s θ : ℝ => Work.Spaces.HkIntegrand α k F s θ))
      (Set.Icc a b ×ˢ Work.Spaces.Iθ) :=
    Work.FTS.EllipticEst.integrableOn_box_of_slice
      (g := fun s θ : ℝ => Work.Spaces.HkIntegrand α k F s θ)
      (hF.continuousOn_HkIntegrand α k)
      (fun z θ => Work.Spaces.HkIntegrand_nonneg α k F z θ)
      ha hab
      (fun s hs => hmem.1 s (hsub hs))
      (hmem.2.mono_set hsub)
  -- **Continuity of the target integrand on the open quadrant.**
  have hsinpos : ∀ p ∈ Work.FTS.EllipticEst.Q0, 0 < Real.sin (2 * p.2) := by
    intro p hp
    obtain ⟨-, hθ0, hθ1⟩ := Work.FTS.EllipticEst.mem_Q0.mp hp
    exact Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos])
  have hcont : ContinuousOn (fun p : ℝ × ℝ =>
      (Work.Spaces.pz (Work.Spaces.DzIter j F) p.1 p.2) ^ 2
        * (Real.sin (2 * p.2)) ^ (-(Work.Spaces.eta))) Work.FTS.EllipticEst.Q0 := by
    refine ContinuousOn.mul ?_ ?_
    · exact (((hF.DzIter j).pz).continuousOn).pow 2
    · exact ((Real.continuous_sin.comp
          (continuous_const.mul continuous_snd)).continuousOn).rpow_const
        (fun p hp => Or.inl (by
          intro h0
          have h0' : Real.sin (2 * p.2) = 0 := h0
          have h := hsinpos p hp
          rw [h0'] at h
          exact absurd h (lt_irrefl (0 : ℝ))))
  -- **A.e. strong measurability** of the target on the box.
  have hle : (volume.restrict (Set.Icc a b)).prod (volume.restrict Work.Spaces.Iθ)
      ≤ (volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ) := by
    rw [MeasureTheory.Measure.prod_restrict, MeasureTheory.Measure.prod_restrict]
    exact MeasureTheory.Measure.restrict_mono (Set.prod_mono hsub subset_rfl) le_rfl
  have hAE : AEStronglyMeasurable (Function.uncurry (fun s θ : ℝ =>
      (Work.Spaces.pz (Work.Spaces.DzIter j F) s θ) ^ 2
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))))
      (volume.restrict (Set.Icc a b ×ˢ Work.Spaces.Iθ)) := by
    have h := (Work.Spaces.aesm_of_continuousOn_Qd (fun p : ℝ × ℝ =>
      (Work.Spaces.pz (Work.Spaces.DzIter j F) p.1 p.2) ^ 2
        * (Real.sin (2 * p.2)) ^ (-(Work.Spaces.eta))) hcont).mono_measure hle
    rwa [MeasureTheory.Measure.prod_restrict] at h
  refine hM.mono' hAE ?_
  -- **Pointwise bound on the box** by the `(j+1)`-slot of the `ℋ^k`-integrand.
  refine MeasureTheory.ae_restrict_of_forall_mem
    (measurableSet_Icc.prod (show MeasurableSet Work.Spaces.Iθ from measurableSet_Icc)) ?_
  intro p hp
  obtain ⟨hp1, hp2⟩ := hp
  have hspos : 0 < p.1 := lt_of_lt_of_le ha hp1.1
  have hS : 0 ≤ Real.sin (2 * p.2) :=
    Real.sin_nonneg_of_mem_Icc ⟨by linarith [hp2.1], by linarith [hp2.2, Real.pi_pos]⟩
  have hGnn : 0 ≤ (Work.Spaces.pz (Work.Spaces.DzIter j F) p.1 p.2) ^ 2
      * (Real.sin (2 * p.2)) ^ (-(Work.Spaces.eta)) :=
    mul_nonneg (sq_nonneg _) (Real.rpow_nonneg hS _)
  simp only [Function.uncurry_def]
  rw [Real.norm_of_nonneg hGnn]
  exact le_trans
    (Work.FTS.EllipticEst.pz_DzIter_sq_mul_sin_le_term j hspos hp2)
    (Work.Spaces.sq_le_HkIntegrand_z α k F p.1 p.2 (j + 1) hj)

end Work.FTS.EllipticEst.Cert
