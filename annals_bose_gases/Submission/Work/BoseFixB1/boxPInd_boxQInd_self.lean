import Mathlib.Tactic.Have
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixB1S.BoxPotOper
import Submission.Work.BoseFixB1S.BoxQIndCore
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB1.boxPInd_boxQInd_self` — the diagonal `P_i Q_i = 0`

FS's box projection in slot `i` (with the box indicator, `Work.UBBInputs8.boxPInd`) is
idempotent — `volA = |A|` is exactly the normalisation making `P_i` a projection — hence its
associated mean-free part `Q_i = 1_A(x_i)·Ψ − P_iΨ` satisfies `P_i Q_i = 0`.  This is the
diagonal (`i = j`) companion of `Work.BoseFixB1S.boxPInd_boxQInd_pointwise`, which covers the
off-diagonal case `i ≠ j`.

The computation is direct: `boxQInd` differs from `Φ` on the box `A` only by the *constant*
`c = volA⁻¹∫_{z∈A} Φ(x|i↦z)dz`, so

  `∫_{z∈A} Q_iΦ(x|i↦z) dz = ∫_{z∈A} Φ(x|i↦z) dz − c·|A| = 0`,

and every remaining factor of `P_i(Q_iΦ)(x)` multiplies that vanishing integral.
-/

noncomputable section

open MeasureTheory
open scoped Real BigOperators ENNReal

namespace Work.BoseFixB1

open Submission.BoseGases

theorem boxPInd_boxQInd_self {N : ℕ} {ℓ volA : ℝ} (hℓ : 0 < ℓ) (hvol : 0 < volA)
    {A : Set (EuclideanSpace ℝ (Fin 3))} (hA : MeasurableSet A)
    (hvolA : volA = (MeasureTheory.volume A).toReal) (hAc : A ⊆ Submission.BoseGases.acube ℓ)
    (i : Fin N) {Φ : Submission.BoseGases.X N → ℝ} (hΦc : Continuous Φ) :
    ∀ x ∈ Submission.BoseGases.abox N ℓ,
      Work.UBBInputs8.boxPInd volA A i (Work.UBBInputs8.boxQInd volA A i Φ) x = 0 := by
  intro x hx
  -- `Φ` is bounded on the (compact) box, so the slot integrals over `A ⊆ acube ℓ` converge.
  obtain ⟨C, _hC0, hC⟩ := Work.BoseFixB1S.exists_abox_bound hℓ hΦc
  have hSint : IntegrableOn (fun z : ℝ³ => Φ (Function.update x i z)) A volume :=
    Work.BoseFixB1S.slotInt_of_bound hℓ hA hAc i x hx hΦc.measurable hC
  have hfin : IsFiniteMeasure (volume.restrict A) :=
    MeasureTheory.isFiniteMeasure_restrict.mpr
      (ne_of_lt (Work.BoseFixB1S.volume_A_lt_top hℓ hAc))
  have hcint : IntegrableOn (fun _ : ℝ³ => (1 / volA) * (∫ w in A, Φ (Function.update x i w)))
      A volume := MeasureTheory.integrable_const _
  -- The slot integral of `Q_iΦ` vanishes: on `A` the mean-free part is `Φ` minus a constant.
  have hkey : (∫ z in A, (Φ (Function.update x i z)
        - (1 / volA) * (∫ w in A, Φ (Function.update x i w)))) = 0 := by
    rw [MeasureTheory.integral_sub hSint hcint, MeasureTheory.setIntegral_const]
    rw [MeasureTheory.Measure.real_def, smul_eq_mul, hvolA.symm]
    field_simp
    ring
  have hcongr : (∫ z in A, Work.UBBInputs8.boxQInd volA A i Φ (Function.update x i z))
      = ∫ z in A, (Φ (Function.update x i z)
          - (1 / volA) * (∫ w in A, Φ (Function.update x i w))) := by
    apply MeasureTheory.setIntegral_congr_fun hA
    intro z hz
    simp only [Work.UBBInputs8.boxQInd, Work.UBBInputs8.boxPInd, Function.update_idem,
      Function.update_self, Set.indicator_of_mem hz]
    ring
  rw [Work.UBBInputs8.boxPInd, hcongr, hkey]
  ring

end Work.BoseFixB1
