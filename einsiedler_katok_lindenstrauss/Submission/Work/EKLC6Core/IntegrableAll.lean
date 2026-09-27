import Mathlib
import Submission.Work.EKLC6Core.Basic
import Submission.Work.EKLC6Core.Assembly
import Submission.Work.EKLC6Core.uminus_isHoro
import Submission.Work.EKLC6Core.growthFun_lintegral_lt_top_of_gen_data
import Submission.Work.EKLC6Core.acovariant_of_leafwise
import Submission.Work.EKLC6Core.measurable_growthFun
import Submission.Work.EKLC6Core.ent_le_HcondSig_of_phi_generated
import Submission.Work.EKLC6Core.integrable_growthFun_uij
import Submission.Work.EKLCompLeaf.fixRadon

/-!
# `Work.EKLC6Core.IntegrableAll` — the integrability input of C6

`Work.EKLC6Core.IntegrableGrowthAll`, the last input of `Work.EKLC6Core.P_EntropyLeaf_of_all`, is
the conjunction of `IntegrableGrowth μ (Uminus t) t` and `IntegrableGrowth μ (Uij hij) t` for the
contracted pairs.  Both halves are PROVED here (no `sorry`):

* `Uij`: `Work.EKLC6Core.integrable_growthFun_uij` (Pisa 7.9 for a root group, via the ergodic
  decomposition and `desc_plaque_conull_ergodic_pt`);
* `Uminus t`: `Work.EKLC6Core.growthFun_lintegral_lt_top_of_gen_data` — the finiteness
  `∫⁻ ofReal (growthFun (Uminus t) ν t) < ⊤` (Pisa 7.18/7.41) — together with the a.e.
  non-negativity of `growthFun` (`conjBox (Uminus t) t ⊆ Box1 (Uminus t)`,
  `Work.EKLC6Core.growthFun_uminus_nonneg`) and the bridge
  `MeasureTheory.lintegral_ofReal_ne_top_iff_integrable`.  Since `IsLeafwise` makes the leaf-wise
  measures finite-on-compacts only on the conull domain `X'`, the measurability hypothesis of that
  finiteness lemma is met by passing to `Work.EKLComp.fixRadon ν X'` (which agrees with `ν` on
  `X'`) and transporting back almost everywhere.
-/

open MeasureTheory Filter Topology
open scoped ENNReal

set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

noncomputable section

namespace Work.EKLC6Core

open Work.EKLContract

/-- The full `A`-covariance implies the covariance along the multiples of one parameter. -/
theorem acovariantAlong_of_acovariant {ν : X3 → Measure SL3} {X'' : Set X3}
    (hcov : ACovariant ν X'') (t : Fin 3 → ℝ) : ACovariantAlong ν t X'' :=
  fun z x hx hx' => hcov ((z : ℝ) • t) x hx hx'

/-- **`IntegrableGrowth` for the full stable horospherical subgroup.** -/
theorem integrableGrowth_uminus_holds (hLeaf : P_Leafwise)
    {μ : MeasureTheory.Measure Work.EKLContract.X3}
    [MeasureTheory.IsProbabilityMeasure μ]
    (hAinv : Work.EKLContract.IsAInvariant μ) (t : Fin 3 → ℝ) :
    IntegrableGrowth μ (Work.EKLC6Core.Uminus t) t := by
  intro ν X' hL
  -- make the leaf-wise system finite on compacts everywhere, so that `growthFun` is measurable
  obtain ⟨hL', hfin⟩ := Work.EKLCompLeaf.fixRadon hL
  have hHoro : Work.EKLContract.IsHoro (Work.EKLC6Core.Uminus t) :=
    (Work.EKLC6Core.uminus_isHoro t).1
  obtain ⟨X'', -, -, hX''null, hcov⟩ :=
    Work.EKLC6Core.acovariant_of_leafwise hLeaf hAinv hHoro hL'
  have hcovAlong : Work.EKLC6Core.ACovariantAlong (Work.EKLComp.fixRadon ν X') t X'' :=
    acovariantAlong_of_acovariant hcov t
  have hmeas : Measurable
      (Work.EKLC6Core.growthFun (Work.EKLC6Core.Uminus t) (Work.EKLComp.fixRadon ν X') t) := by
    unfold Work.EKLC6Core.growthFun
    exact ((Work.EKLC6Core.measurable_growthFun hL' hfin hHoro t).log).neg
  have hlt : ∫⁻ x, ENNReal.ofReal
      (Work.EKLC6Core.growthFun (Work.EKLC6Core.Uminus t) (Work.EKLComp.fixRadon ν X') t x) ∂μ
      < ⊤ :=
    Work.EKLC6Core.growthFun_lintegral_lt_top_of_gen_data t (hAinv t) hL' hcovAlong hX''null
      hmeas
  have hnn : 0 ≤ᵐ[μ]
      Work.EKLC6Core.growthFun (Work.EKLC6Core.Uminus t) (Work.EKLComp.fixRadon ν X') t :=
    Work.EKLC6Core.growthFun_uminus_nonneg t hL'
  have hint' : MeasureTheory.Integrable
      (Work.EKLC6Core.growthFun (Work.EKLC6Core.Uminus t) (Work.EKLComp.fixRadon ν X') t) μ :=
    (MeasureTheory.lintegral_ofReal_ne_top_iff_integrable hmeas.aestronglyMeasurable hnn).mp
      (ne_of_lt hlt)
  have hae : (fun x : Work.EKLContract.X3 =>
        Work.EKLC6Core.growthFun (Work.EKLC6Core.Uminus t) ν t x)
      =ᵐ[μ] (fun x : Work.EKLContract.X3 =>
        Work.EKLC6Core.growthFun (Work.EKLC6Core.Uminus t) (Work.EKLComp.fixRadon ν X') t x) := by
    filter_upwards [MeasureTheory.ae_iff.mpr hL.conull] with x hx
    simp only [Work.EKLC6Core.growthFun,
      Work.EKLComp.fixRadon_of_mem (ν := ν) (X' := X') hx]
  exact hint'.congr hae.symm

/-- **`IntegrableGrowthAll`** — the last input of the assembly — PROVED from the sibling
component `P_Leafwise` (used only to read off the `A`-covariance of the leaf-wise system,
EKL (4)). -/
theorem integrableGrowthAll_holds (hLeaf : P_Leafwise) : IntegrableGrowthAll :=
  fun μ hμ hAinv t =>
    ⟨integrableGrowth_uminus_holds hLeaf hAinv t,
      fun i j hij hlt => Work.EKLC6Core.integrable_growthFun_uij t (hAinv t) hij hlt⟩

end Work.EKLC6Core

end
