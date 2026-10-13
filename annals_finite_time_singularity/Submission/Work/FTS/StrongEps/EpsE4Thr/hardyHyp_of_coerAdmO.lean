import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.StrongEps.EpsE4Thr.OpenClass
import Submission.Work.FTS.CoercivityFix.Coer1T.hardyHyp_of_coerAdm
import Submission.Work.Coercivity.Defs
import Submission.Work.FTS.MeridianDyn.Bridge.ProfDerivData_of_regPkg_closed
import Submission.Work.FTS.MeridianDyn.Bridge.Pieces.sliceK_integrableOn_of_continuousOn
import Submission.Work.FTS.MeridianDyn.Bridge.Pieces.L12dens_integrableOn_of_continuousOn
import Submission.Work.FTS.StrongEps.EpsE4Thr.HardyOpen.intB_integrableOn_open
import Submission.Work.FTS.StrongEps.EpsE4Thr.HardyOpen.L12f_sq_div_small_open
import Submission.Work.FTS.StrongEps.EpsE4Thr.HardyOpen.L12f_sq_div_large_open
import Submission.Work.FTS.StrongEps.EpsE4Thr.HardyOpen.L12f_bd0_open
import Submission.Work.FTS.StrongEps.EpsE4Thr.HardyOpen.L12f_bdTop_open

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `HardyHyp` for the *open* coercivity class `CoerAdmO`

This file proves `Work.FTS.StrongEps.EpsE4Thr.hardyHyp_of_coerAdmO`: the analytic hypothesis
package `Work.Coercivity.HardyHyp` (the hypotheses of Lemma `HardyWeight` of Elgindi's paper)
holds for every datum of the *open* interior class

  `CoerAdmO α f` = `RegQo α 5 f ∧ VanishTheta f ∧ axis ∧ L₁₂(f)(0) = 0`,

i.e. `C^∞` on the **open** quadrant `(0,∞) × (0,π/2)` (instead of the strip `z > -1`),
for `0 < α ≤ 10⁻¹⁴`.

This is the open-class companion of the sibling
`Work.FTS.CoercivityFix.Coer1T.hardyHyp_of_coerAdm` (which needs the stronger `SmoothQuad`),
and it is the version the level-four `ε`-chapter needs: the projected mollified slices of the
route are `SmoothOpen` (`coerAdmO_slice_JfamP`) but never `SmoothQuad`.

## The seven fields

* `hslice` — integrability of `θ ↦ K(θ) f z θ / z` on `Iθ`: the open-class
  `Work.FTS.MeridianDyn.Bridge.Pieces.sliceK_integrableOn_of_continuousOn`, whose only
  regularity input is `ContinuousOn (uncurry f) Q0` (from `SmoothOpen.forall 1`).
* `hcont` — continuity of the `L₁₂`-density at every `z > 0`: the open-class
  `Work.FTS.MeridianDyn.Bridge.continuousAt_L12dens_of_smoothOpen_Hk`.
* `hint` — `L12dens ∈ L¹((0,∞))`:
  `Work.FTS.MeridianDyn.Bridge.integrableOn_L12dens_of_smoothOpen_Hk`.
* `intA` — `(L₁₂ f)²/z^{2j} ∈ L¹((0,∞))` for `j ≤ 2`: the open-class ports
  `HardyOpen.L12f_sq_div_small_open` (on `(0,1]`) and `HardyOpen.L12f_sq_div_large_open`
  (on `(1,∞)`), glued with `Ioc 0 1 ∪ Ioi 1 = Ioi 0`.
* `intB` — `(∫_θ f z θ²)/z^{2j} ∈ L¹((0,∞))` for `j ≤ 2`: the open-class port
  `HardyOpen.intB_integrableOn_open`.
* `bd0`, `bdTop` — the boundary terms at `0⁺` and at `∞`: the open-class ports
  `HardyOpen.L12f_bd0_open` / `HardyOpen.L12f_bdTop_open`.

The `ℋ⁴`-membership used everywhere is `HkMem α 4 f`, obtained from the `ℋ⁵`-membership of
`RegQo α 5 f` via `Work.FTS.OpenPkg.HkMem_mono_open` (the open-class monotonicity).
-/

namespace Work.FTS.StrongEps.EpsE4Thr

open MeasureTheory Set Filter
open scoped Real Topology

theorem hardyHyp_of_coerAdmO {α : ℝ} {f : Work.FTS.Galerkin.Fn} (hα : 0 < α)
    (hα1 : α ≤ 1 / 10 ^ 14) (hf : Work.FTS.StrongEps.EpsE4Thr.CoerAdmO α f) :
    Work.Coercivity.HardyHyp f := by
  obtain ⟨hreg, hvan, haxis, hl12⟩ := hf
  obtain ⟨hsm, hmem5, hbdry⟩ := hreg
  have hmem : Work.Spaces.HkMem α 4 f :=
    Work.FTS.OpenPkg.HkMem_mono_open hsm 4 (by norm_num) hmem5
  have hint : MeasureTheory.IntegrableOn (Work.FM.L12dens Work.Spaces.K f) (Set.Ioi 0) :=
    Work.FTS.MeridianDyn.Bridge.integrableOn_L12dens_of_smoothOpen_Hk hsm hmem
  have hcont : ∀ z ∈ Set.Ioi (0 : ℝ), ContinuousAt (Work.FM.L12dens Work.Spaces.K f) z :=
    fun z hz => Work.FTS.MeridianDyn.Bridge.continuousAt_L12dens_of_smoothOpen_Hk hsm hmem hz
  have hl12' : Work.Coercivity.L12f f 0 = 0 := by
    simpa [Work.Coercivity.L12f, Work.FM.L12, Work.Construction.L12] using hl12
  have hC : ContinuousOn (Function.uncurry f) Work.FTS.EllipticEst.Q0 :=
    (hsm.forall 1).continuousOn
  have hU : Set.Ioc (0 : ℝ) 1 ∪ Set.Ioi 1 = Set.Ioi (0 : ℝ) := by
    ext t
    simp only [Set.mem_union, Set.mem_Ioc, Set.mem_Ioi]
    constructor
    · rintro (h | h)
      · exact h.1
      · linarith [h]
    · intro h
      rcases lt_trichotomy t 1 with h' | h' | h'
      · exact Or.inl ⟨h, h'.le⟩
      · exact Or.inl ⟨h, le_of_eq h'⟩
      · exact Or.inr h'
  refine ⟨?_, ?_, hint, ?_, ?_, ?_, ?_⟩
  · intro z hz
    exact Work.FTS.MeridianDyn.Bridge.Pieces.sliceK_integrableOn_of_continuousOn hC hmem z hz
  · exact hcont
  · intro j hj
    rw [← hU]
    exact MeasureTheory.IntegrableOn.union
      (HardyOpen.L12f_sq_div_small_open α hsm hmem hint hl12' hcont j hj)
      (HardyOpen.L12f_sq_div_large_open α hsm hmem hint hcont j)
  · intro j hj
    exact HardyOpen.intB_integrableOn_open α hsm hmem j hj
  · intro j hj
    exact HardyOpen.L12f_bd0_open α hsm hmem hint hl12' j hj
  · intro j hj
    exact HardyOpen.L12f_bdTop_open α hsm hmem j

end Work.FTS.StrongEps.EpsE4Thr
