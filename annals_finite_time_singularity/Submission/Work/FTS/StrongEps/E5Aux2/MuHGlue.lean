import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.FTS.StrongEps.E5Aux2.aestronglyMeasurable_L12dens
import Submission.Work.FTS.StrongEps.E5Aux2.AbsL12densLe
import Submission.Work.FTS.StrongEps.E5Aux2.N0_N_Transport_pt_le
import Submission.Work.FTS.StrongEps.E5Aux2.N0_N_Transport_dens_le
import Submission.Work.FTS.StrongEps.E5Aux2.PTgadgets
import Submission.Work.FTS.StrongEps.EpsConv
import Submission.Work.FTS.StrongEps.EpsMem
import Submission.Work.FTS.StrongEps.EpsLimitDefs
import Submission.Work.FTS.StrongEps.E5Law
import Submission.Work.FTS.StrongEps.N0_tendsto
import Submission.Work.FTS.StrongEps.gRHS_tendsto
import Submission.Work.FTS.StrongEps.mixed_JfamP_tendsto
import Submission.Work.FTS.StrongEps.mixed_Jeps_tendsto
import Submission.Work.FTS.StrongEps.mixed_add
import Submission.Work.FTS.StrongEps.mixed_const_mul
import Submission.Work.FTS.StrongEps.L12_tendsto_of_dominated
import Submission.Work.FTS.StrongEps.E5Aux.dens_tendsto_of_slot_tendsto
import Submission.Work.FTS.StrongEps.ClassCRHS.smoothOpen_L12_radial_classC
import Submission.Work.FTS.GalFields.RHS.SharpAux.Core
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.SmoothN0
import Submission.Work.FTS.StrongEps.HkMem_of_tendsto
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.L12ShiftThetaAux
import Submission.Work.FTS.StrongEps.E5Aux2.l12Slice_JfamP_tendsto
import Submission.Work.FTS.StrongEps.E5Aux2.FK_JfamP_tendsto
import Submission.Work.FTS.NonlinRows.NRow1_7Aux
import Submission.Work.FTS.NonlinRows.Rl1.splitOpen
import Submission.Work.FTS.EllipticEst.UopHk.GsingFactsInterior
import Submission.Work.FTS.OpenPkg.Basic

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `MuHGlue` — measurability and domination glue for the `μ`-convergence

Three general facts used in `muDyn_tendstoH`:

* `aesm_L12dens_of_contOn` — joint continuity of a profile on the open quadrant gives
  a.e.-strong measurability of its `L₁₂`-density;
* `aesm_slice_K_of_contOn` — the same continuity gives the a.e.-strong measurability of the
  angular slice `θ ↦ K θ · Y s θ` at every `s > 0`;
* `integrable_majorant` — the majorant
  `s ↦ C1 (1+C₀) (1+B) (Maj s / s + 1/(1+s)²)` is integrable on `(0,∞)`.
-/

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.E5Aux2

set_option autoImplicit false

/-! ## Measurability of the density from joint continuity on the open quadrant -/

/-- The uncurried profile is a.e.-strongly measurable for the product of the restrictions of
Lebesgue measure to `(0,∞)` and to `Iθ`, from joint continuity on the open quadrant. -/
theorem aesm_uncurry_of_contOn {Y : ℝ → ℝ → ℝ}
    (h : ContinuousOn (Function.uncurry Y) Work.FTS.EllipticEst.Q0) :
    MeasureTheory.AEStronglyMeasurable (Function.uncurry Y)
      ((MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) := by
  have h1 : MeasureTheory.AEStronglyMeasurable (Function.uncurry Y)
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) :=
    Work.Spaces.aesm_of_continuousOn_Qd (Function.uncurry Y) h
  have hle : (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)
      ≤ (MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
    MeasureTheory.Measure.prod_mono
      (MeasureTheory.Measure.restrict_mono Set.Ioi_subset_Ici_self le_rfl) le_rfl
  exact h1.mono_measure hle

/-- **The `L₁₂`-density of a profile that is continuous on the open quadrant is
a.e.-strongly measurable.**  The `θ`-integral is taken against the restricted product measure
of the (a.e. equal) sets `(0,∞) × Iθ` and the open quadrant. -/
theorem aesm_L12dens_of_contOn {Y : ℝ → ℝ → ℝ}
    (h : ContinuousOn (Function.uncurry Y) Work.FTS.EllipticEst.Q0) :
    MeasureTheory.AEStronglyMeasurable (fun s => Work.FM.L12dens Work.Spaces.K Y s)
      (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))) :=
  aestronglyMeasurable_L12dens (aesm_uncurry_of_contOn h).aemeasurable

/-- The angular slice `θ ↦ K θ · Y s θ` is a.e.-strongly measurable on `Iθ` for every `s > 0`,
from joint continuity of `Y` on the open quadrant (the slice is continuous on `(0,π/2)`, which
is co-null in `Iθ`). -/
theorem aesm_slice_K_of_contOn {Y : ℝ → ℝ → ℝ}
    (h : ContinuousOn (Function.uncurry Y) Work.FTS.EllipticEst.Q0) {s : ℝ} (hs : 0 < s) :
    MeasureTheory.AEStronglyMeasurable (fun θ => Work.Spaces.K θ * Y s θ)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
  have hslice : ContinuousOn (fun θ => Y s θ) (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
    h.comp (continuous_const.prodMk continuous_id).continuousOn
      (fun θ hθ => ⟨hs, hθ⟩)
  have hK : ContinuousOn (fun θ => Work.Spaces.K θ) (Set.Ioo (0 : ℝ) (Real.pi / 2)) := by
    unfold Work.Spaces.K
    fun_prop
  have h2 : MeasureTheory.AEStronglyMeasurable (fun θ => Work.Spaces.K θ * Y s θ)
      (MeasureTheory.volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2))) :=
    (hK.mul hslice).aestronglyMeasurable measurableSet_Ioo
  have hcongr : MeasureTheory.volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2))
      = MeasureTheory.volume.restrict Work.Spaces.Iθ :=
    MeasureTheory.Measure.restrict_congr_set
      (MeasureTheory.Ioo_ae_eq_Icc (μ := MeasureTheory.volume) (a := 0) (b := Real.pi / 2))
  rwa [hcongr] at h2

/-! ## Integrability of the majorant -/

/-- `s ↦ 1/(1+s)²` is integrable on `(0,∞)`. -/
theorem integrableOn_one_div_sq : MeasureTheory.IntegrableOn
    (fun s : ℝ => 1 / (1 + s) ^ 2) (Set.Ioi 0) := by
  refine MeasureTheory.IntegrableOn.congr_fun
    (MeasureTheory.Integrable.const_mul
      (Work.FTS.MeridianDyn.Bridge.Pieces.integrableOn_two_div_one_add_sq 0 le_rfl)
      (1 / 2)) ?_ measurableSet_Ioi
  intro s _
  ring

/-- **The majorant of the `ε`-density bound is integrable on `(0,∞)`**, from the integrability
of `Maj s / s`. -/
theorem integrable_majorant {C1 C₀ B : ℝ} {Maj : ℝ → ℝ}
    (hMajint : MeasureTheory.IntegrableOn (fun z => Maj z / z) (Set.Ioi 0)) :
    MeasureTheory.IntegrableOn
      (fun s : ℝ => C1 * (1 + C₀) * (1 + B) * (Maj s / s + 1 / (1 + s) ^ 2))
      (Set.Ioi 0) :=
  ((hMajint.add integrableOn_one_div_sq).const_mul _)

end Work.FTS.StrongEps.E5Aux2
