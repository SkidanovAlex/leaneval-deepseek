/-
# `Work.FTS.Top.Rescale.Blowup` — moving the blow-up time to `1` (proved)

This is the replacement of the *vacuous* hypothesis `Work.StabilityFar.EulerScalingToUnit` by a
proved result: every blow-up of the class of the paper's Theorem 1 at a time `T > 0` is rescaled
to one at time `1`.

The rescaling used is the time-only Euler symmetry

  `u₁(x,t) = T · u(x, T·t)`,   `p₁(x,t) = T² · p(x, T·t)`,

which acts on the values and on the time variable but leaves `ℝ³` alone.  Its properties:

* the equation: all three terms are multiplied by `T²` (`Rescale/euler_eq_timeScale`);
* divergence-freeness: `div u₁(·,t) = T · div u(·,T t)` (`Rescale/div_timeScale`);
* oddness and the `C^{1,α}` class of the datum, and the `α`-power decay of its vorticity: value
  scalings (`Rescale/isOdd_const_smul`, `Rescale/isContDiffHolder_const_smul`,
  `Rescale/vorticity_const_smul`);
* the joint `C^{1,α}` strip regularity: the reparametrisation result
  `Rescale/isContDiffHolderOn_uncurry_timeScale`;
* the blow-up rate: `vortLInf u₁ t = T · vortLInf u (T t)` (`Rescale/vortLInf_timeScale`), so
  `c/(T - T·t) = c/(T(1-t))` becomes `c/(1-t)`
  (the same constant `c` works).

Nothing here uses regularity at or past the blow-up time.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.PiL2
import Submission.Work.FTS.Top.Defs
import Submission.Work.FTS.Top.Rescale.Basic
import Submission.Work.FTS.Top.Rescale.isContDiffHolderOn_uncurry_timeScale
import Submission.Work.FTS.Top.Rescale.vortLInf_timeScale

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open FiniteTimeSingularity Set Gradient Matrix Filter Topology MeasureTheory
open scoped Topology Matrix NNReal ENNReal

set_option autoImplicit false

namespace Work.FTS.Top

/-- The strip `ℝ³ × [0,S]` is carried into `ℝ³ × [0,T·S]` by `timeCLM T`, for `0 ≤ T`. -/
private theorem mapsTo_Icc_T (T : ℝ) (hT : 0 < T) (S : ℝ) :
    Set.MapsTo (timeCLM T) (Set.univ ×ˢ Set.Icc (0 : ℝ) S)
      (Set.univ ×ˢ Set.Icc (0 : ℝ) (T * S)) :=
  mapsTo_timeCLM_Icc hT.le S

/-- The half-open strip `ℝ³ × [0,1)` is carried into `ℝ³ × [0,T)` by `timeCLM T`, for `T > 0`. -/
private theorem mapsTo_Ico_one_T (T : ℝ) (hT : 0 < T) :
    Set.MapsTo (timeCLM T) (Set.univ ×ˢ Set.Ico (0 : ℝ) 1)
      (Set.univ ×ˢ Set.Ico (0 : ℝ) T) := by
  intro z hz
  simp only [Set.mem_prod, Set.mem_univ, true_and, timeCLM_apply, Set.mem_Ico] at hz ⊢
  exact ⟨mul_nonneg hT.le hz.1, by nlinarith [hz.2, hT]⟩

/-- **The blow-up time can be moved to `1`.**  A blow-up of the class of the paper's Theorem 1 at
time `T > 0` is carried, by the time-only Euler rescaling `u₁(x,t) = T·u(x,T·t)`,
`p₁(x,t) = T²·p(x,T·t)`, to a blow-up at time `1`.

This replaces the hypothesis `Work.StabilityFar.EulerScalingToUnit` (which the audit, §2.2/§3,
showed to be vacuous) by a proved result. -/
noncomputable def blowupAt_one_of_blowupAt {α : ℝ≥0} {T : ℝ} (B : BlowupAt α T) :
    BlowupAt α 1 := by
  have hT : 0 < T := B.hT
  have hu_zero : (timeScale T B.u · 0) = fun x => T • (B.u · 0) x := by
    funext x
    rw [timeScale_apply, mul_zero]
  refine
    { u := timeScale T B.u
      p := timeScaleP T B.p
      hT := one_pos
      sol := ?_
      div0 := ?_
      odd := ?_
      cdh0 := ?_
      decay0 := ?_
      strip := ?_
      lower := ?_ }
  · -- the rescaled pair solves the Euler equation on `[0,1)`
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · -- joint `C¹` of the velocity
      exact contDiffOn_uncurry_timeScale (mapsTo_Ico_one_T T hT) B.sol.solContDiff
    · -- joint `C¹` of the pressure
      exact contDiffOn_uncurry_timeScaleP (mapsTo_Ico_one_T T hT) B.sol.pressureContDiff
    · -- the equation
      refine euler_eq_timeScale (c := T) (T := T) hT le_rfl ?_ B.sol.eq
      exact B.sol.solContDiff.mono (fun z hz => ⟨trivial, ⟨hz.2.1.le, hz.2.2⟩⟩)
    · -- divergence-freeness of the slices
      intro t ht
      have hmem : T * t ∈ Set.Ioo 0 T :=
        ⟨mul_pos hT ht.1, by nlinarith [ht.2, hT]⟩
      have h0 := B.sol.div_free (T * t) hmem
      rw [div_timeScale T B.u t, h0]
      funext x
      simp
    · -- the initial datum
      rfl
  · -- the datum is divergence-free
    have h0 := B.div0
    rw [div_timeScale T B.u 0, mul_zero, h0]
    funext x
    simp
  · -- oddness at every time
    intro t ht
    have hmem : T * t ∈ Set.Ico 0 T :=
      ⟨mul_nonneg hT.le ht.1, by nlinarith [ht.2, hT]⟩
    exact isOdd_const_smul (B.odd (T * t) hmem)
  · -- the datum is `C^{1,α}`
    rw [hu_zero]
    exact isContDiffHolder_const_smul B.cdh0
  · -- the vorticity of the datum decays
    obtain ⟨C₀, hC₀, hC₀b⟩ := B.decay0
    refine ⟨T * C₀, mul_pos hT hC₀, fun x => ?_⟩
    rw [hu_zero, vorticity_const_smul, norm_smul, Real.norm_of_nonneg hT.le]
    calc T * ‖vorticity (B.u · 0) x‖ ≤ T * (C₀ / (‖x‖ ^ (α : ℝ) + 1)) :=
          mul_le_mul_of_nonneg_left (hC₀b x) hT.le
      _ = T * C₀ / (‖x‖ ^ (α : ℝ) + 1) := by ring
  · -- the joint `C^{1,α}` strip regularity
    intro S hS
    have hTS : T * S ∈ Set.Ioo 0 T :=
      ⟨mul_pos hT hS.1, by nlinarith [hS.2, hT]⟩
    exact Work.FTS.Top.Rescale.isContDiffHolderOn_uncurry_timeScale (mapsTo_Icc_T T hT S)
      (uniqueDiffWithinAt_prod_Icc hS.1) (B.strip (T * S) hTS)
  · -- the blow-up rate
    obtain ⟨c₀, hc₀, hlow⟩ := B.lower
    refine ⟨c₀, hc₀, fun t ht => ?_⟩
    have hmem : T * t ∈ Set.Ico 0 T :=
      ⟨mul_nonneg hT.le ht.1, by nlinarith [ht.2, hT]⟩
    have h1 : c₀ / (T - T * t) ≤ Work.LWP.vortLInf B.u (T * t) := hlow (T * t) hmem
    rw [Work.FTS.Top.Rescale.vortLInf_timeScale T hT.le B.u t]
    have h2 : T * (c₀ / (T - T * t)) = c₀ / (1 - t) := by
      have h3 : T - T * t = T * (1 - t) := by ring
      rw [h3]
      have ht1 : (1 : ℝ) - t ≠ 0 := by linarith [ht.2]
      field_simp
    rw [← h2]
    exact mul_le_mul_of_nonneg_left h1 hT.le

end Work.FTS.Top
