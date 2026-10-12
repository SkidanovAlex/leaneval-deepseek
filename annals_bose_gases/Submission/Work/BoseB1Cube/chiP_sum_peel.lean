import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseB1Cube.peelChiSq_le
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseB1Cube.chiP_sum_peel` — the exact `χ`-mass peel of the box-condensate square

For the FS-faithful box projection `Pᵢ = boxPInd volA A i` (`P_{B,i}φ = |B|⁻¹⟨1_B,φ⟩1_B`,
`A = dlBox ℓ d u`, `volA = boxMass ℓ d u = |A|`) and the sliding cutoff
`χ = chiSmallB M ℓ d u` (supported in `A`, `∫_A χ² = chiMass ℓ d u`), one has the **identity**

    ∫_{abox n ℓ} (χ(xᵢ)·PᵢΦ)² = (chiMass / boxMass) · ∫_{abox n ℓ} (PᵢΦ)²

for every slot `i`.  The mechanism is the one-slot kernel identity
`Work.BoseFixB1S.Q0C.one_kernel` (with the weight `g = χ²`)

    ∫_{abox (m+1) ℓ} (PᵢΦ)²·g(xᵢ) = (∫_A g) · ∫_{abox m ℓ} (oneRest volA A i Φ)² ,

together with its `g = 1` companion `Work.BoseFixB1S.Q0C.one_flat`

    ∫_{abox (m+1) ℓ} (PᵢΦ)² = volA · ∫_{abox m ℓ} (oneRest volA A i Φ)² .

Both sides are therefore `chiMass · ∫(oneRest)²`; the box volume cancels.  Summing over the
slots gives the target, an **equality** (not an inequality): the bare `χ²`-weight of the
condensate block is exactly the volume-normalised condensate square, which is why the flat
arm of `PerBoxF` can cancel the χ-weight against the box volume exactly.
-/

noncomputable section

open MeasureTheory
open scoped Real BigOperators ENNReal

namespace Work.BoseB1Cube

open Submission.BoseGases

local notation "E3" => EuclideanSpace ℝ (Fin 3)

set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

/-- **The per-slot peel identity.**  For `n = m + 1` particles, one slot `i`, the sliding
cutoff `χ = chiSmallB M ℓ d u` and the box projection `Pᵢ = boxPInd (boxMass ℓ d u) (dlBox ℓ d u) i`,

    ∫_{abox (m+1) ℓ} (χ(xᵢ)·PᵢΦ)² = (chiMass M ℓ d u / boxMass ℓ d u)·∫_{abox (m+1) ℓ} (PᵢΦ)² . -/
theorem slot_chi_sq_apply {M : ℕ} (hM : 1 ≤ M) {ℓ d : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d)
    (u : E3) (hV : 0 < Work.SmallBoxSliding.boxMass ℓ d u)
    {m : ℕ} {Φ : Submission.BoseGases.X (m + 1) → ℝ} (hΦc : Continuous Φ) (i : Fin (m + 1)) :
    (∫ x in Submission.BoseGases.abox (m + 1) ℓ,
        (Submission.BoseGases.chiSmallB M ℓ d u (x i)
          * Work.UBBInputs8.boxPInd (Work.SmallBoxSliding.boxMass ℓ d u)
              (Submission.BoseGases.dlBox ℓ d u) i Φ x) ^ 2)
      = (Work.SmallBoxSliding.chiMass M ℓ d u / Work.SmallBoxSliding.boxMass ℓ d u)
          * (∫ x in Submission.BoseGases.abox (m + 1) ℓ,
              (Work.UBBInputs8.boxPInd (Work.SmallBoxSliding.boxMass ℓ d u)
                  (Submission.BoseGases.dlBox ℓ d u) i Φ x) ^ 2) := by
  have hA : MeasurableSet (Submission.BoseGases.dlBox ℓ d u) :=
    Work.SmallBoxSliding.measurableSet_dlBox ℓ d u
  have hAc : Submission.BoseGases.dlBox ℓ d u ⊆ Submission.BoseGases.acube ℓ :=
    Work.SmallBoxSliding.dlBox_subset_acube ℓ d u
  have hvolA : Work.SmallBoxSliding.boxMass ℓ d u
      = (volume : Measure E3).real (Submission.BoseGases.dlBox ℓ d u) :=
    Work.SmallBoxSliding.boxMass_eq_measureReal ℓ d u
  have hfin : (volume : Measure E3) (Submission.BoseGases.dlBox ℓ d u) < ⊤ :=
    Work.BoseFixB1S.Q0C.volume_A_lt_top hℓ hAc
  have hχint : Integrable
      (fun z : E3 => (Submission.BoseGases.chiSmallB M ℓ d u z) ^ 2)
      (volume.restrict (Submission.BoseGases.dlBox ℓ d u)) := by
    refine Integrable.mono'
      (g := fun _ : E3 =>
        (Submission.BoseGases.chiSupAbs * Submission.BoseGases.chiSmallDecay M) ^ 2)
      (integrableOn_const (C :=
        (Submission.BoseGases.chiSupAbs * Submission.BoseGases.chiSmallDecay M) ^ 2)
        (s := Submission.BoseGases.dlBox ℓ d u) hfin.ne) ?_ ?_
    · exact ((Work.BoseFixB1S.chiSmallB_continuous hM ℓ d u).pow 2).aestronglyMeasurable
    · filter_upwards with z
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _),
        ← sq_abs (Submission.BoseGases.chiSmallB M ℓ d u z)]
      exact pow_le_pow_left₀ (abs_nonneg _) (Work.BoseFixB1S.abs_chiSmallB_le_supB hM u z) 2
  have hker := Work.BoseFixB1S.Q0C.one_kernel (n := m) (ℓ := ℓ)
    (volA := Work.SmallBoxSliding.boxMass ℓ d u) hℓ hV hA hAc hvolA i hΦc
    (g := fun z : E3 => (Submission.BoseGases.chiSmallB M ℓ d u z) ^ 2) hχint
  have hflat := Work.BoseFixB1S.Q0C.one_flat (n := m) (ℓ := ℓ)
    (volA := Work.SmallBoxSliding.boxMass ℓ d u) hℓ hV hA hAc hvolA i hΦc
  have hAm : (∫ z in Submission.BoseGases.dlBox ℓ d u,
        (Submission.BoseGases.chiSmallB M ℓ d u z) ^ 2)
      = Work.SmallBoxSliding.chiMass M ℓ d u := setIntegral_chiSmallB_sq hM hℓ hd u
  have hL : (∫ x in Submission.BoseGases.abox (m + 1) ℓ,
        (Submission.BoseGases.chiSmallB M ℓ d u (x i)
          * Work.UBBInputs8.boxPInd (Work.SmallBoxSliding.boxMass ℓ d u)
              (Submission.BoseGases.dlBox ℓ d u) i Φ x) ^ 2)
      = ∫ x in Submission.BoseGases.abox (m + 1) ℓ,
          (Work.UBBInputs8.boxPInd (Work.SmallBoxSliding.boxMass ℓ d u)
              (Submission.BoseGases.dlBox ℓ d u) i Φ x) ^ 2
            * (Submission.BoseGases.chiSmallB M ℓ d u (x i)) ^ 2 := by
    apply integral_congr_ae
    filter_upwards with x
    ring
  rw [hL, hker, hAm, hflat]
  field_simp

/-- **`Work.BoseB1Cube.chiP_sum_peel`.**  Summing `slot_chi_sq_apply` over the slots. -/
theorem chiP_sum_peel {M : ℕ} (hM : 1 ≤ M) {ℓ d : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d)
    (u : EuclideanSpace ℝ (Fin 3)) (hV : 0 < Work.SmallBoxSliding.boxMass ℓ d u)
    {n : ℕ} {Φ : Submission.BoseGases.X n → ℝ} (hΦc : Continuous Φ) :
    (∑ i : Fin n, ∫ x in Submission.BoseGases.abox n ℓ,
        (Submission.BoseGases.chiSmallB M ℓ d u (x i)
          * Work.UBBInputs8.boxPInd (Work.SmallBoxSliding.boxMass ℓ d u)
              (Submission.BoseGases.dlBox ℓ d u) i Φ x) ^ 2)
      = (Work.SmallBoxSliding.chiMass M ℓ d u / Work.SmallBoxSliding.boxMass ℓ d u)
          * (∑ i : Fin n, ∫ x in Submission.BoseGases.abox n ℓ,
              (Work.UBBInputs8.boxPInd (Work.SmallBoxSliding.boxMass ℓ d u)
                  (Submission.BoseGases.dlBox ℓ d u) i Φ x) ^ 2) := by
  cases n with
  | zero => simp
  | succ m =>
    rw [Finset.sum_congr rfl (fun i (_ : i ∈ Finset.univ) =>
      slot_chi_sq_apply (m := m) (M := M) hM hℓ hd u hV hΦc i)]
    rw [Finset.mul_sum]

end Work.BoseB1Cube
