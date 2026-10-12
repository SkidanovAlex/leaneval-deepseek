import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BSKinetic.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BSKinetic.bigKinU_one_eq_oneBody`

The one-particle (`N = 1`) case of the big-box family kinetic word: the `N`-body word
`Work.UBBInputs9.tBwordKinBigU 1 ℓ c u Φ` (the corpus's `tBwordKinInd` at the moving box
`Λ(u) = bigBox ℓ u`, window `chiBig ℓ u`, volume `ℓ³`) collapses to the *one-body* form
`Work.BSKinetic.bsOneBody ℓ (fsKinCoeff c) u (slotFun1 Φ)`.

With a single particle there is exactly one slot, so the slot sum `Σ_{i : Fin 1}` is a single
term; the mean-free projection `boxQInd` reduces to the box mean subtraction, and — because the
window `chiBig ℓ u` is supported in `bigBox ℓ u` — the indicator factor in `boxQInd` is invisible
to the amplitude `tBamp` (`Work.UBBInputs9.A.tBamp_boxQInd`).  The amplitude of the level-`1`
state is independent of the ambient configuration `x`, so the `x`-integral over `abox 1 ℓ` is the
constant `ℓ³·‖·‖²` (the window normalisation `abox_volume`), cancelling the `(ℓ³)⁻¹`.
-/

noncomputable section

open MeasureTheory
open scoped ContDiff Topology Real BigOperators ENNReal

namespace Work.BSKinetic

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)
local notation "X1" => Submission.BoseGases.X 1

open Submission.BoseGases

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## 1. The moving box and its window -/

/-- The moving window `chiBig ℓ u` vanishes off the moving box `bigBox ℓ u`. -/
lemma chiBig_eq_zero_of_notMem_bigBox {ℓ : ℝ} (hℓ : 0 < ℓ) (u z : ℝ³)
    (hz : z ∉ Work.UBBInputs9.bigBox ℓ u) : Work.UBBInputs9.chiBig ℓ u z = 0 := by
  have h : z - ℓ • u ∉ Submission.BoseGases.acube ℓ := hz
  exact chiScale_eq_zero_of_notMem_acube hℓ h

/-- The moving box is measurable. -/
lemma measurableSet_bigBox (ℓ : ℝ) (u : ℝ³) :
    MeasurableSet (Work.UBBInputs9.bigBox ℓ u) := by
  have h : Work.UBBInputs9.bigBox ℓ u
      = (fun x : ℝ³ => x - ℓ • u) ⁻¹' Submission.BoseGases.acube ℓ := rfl
  rw [h]
  exact (Submission.BoseGases.acube_measurable ℓ).preimage (by fun_prop)

/-- **Translation of the moving-box integral to the centred cube**:
`∫_{bigBox ℓ u} ψ = ∫_{acube ℓ} ψ(ℓ•u + ·)`. -/
lemma setIntegral_bigBox_eq_translate (ℓ : ℝ) (u : ℝ³) (ψ : ℝ³ → ℝ) :
    ∫ z in Work.UBBInputs9.bigBox ℓ u, ψ z
      = ∫ z in Submission.BoseGases.acube ℓ, ψ (ℓ • u + z) := by
  classical
  rw [← integral_indicator (measurableSet_bigBox ℓ u),
      ← integral_indicator (Submission.BoseGases.acube_measurable ℓ)]
  rw [← Submission.BoseGases.integral_comp_add_left
        ((Work.UBBInputs9.bigBox ℓ u).indicator ψ) (ℓ • u)]
  apply integral_congr_ae
  filter_upwards with z
  rw [Set.indicator_apply, Set.indicator_apply]
  by_cases hz : z ∈ Submission.BoseGases.acube ℓ
  · have hz' : ℓ • u + z ∈ Work.UBBInputs9.bigBox ℓ u := by
      show ℓ • u + z - ℓ • u ∈ Submission.BoseGases.acube ℓ
      rwa [add_sub_cancel_left]
    rw [if_pos hz', if_pos hz]
  · have hz' : ℓ • u + z ∉ Work.UBBInputs9.bigBox ℓ u := by
      show ¬ (ℓ • u + z - ℓ • u ∈ Submission.BoseGases.acube ℓ)
      rwa [add_sub_cancel_left]
    rw [if_neg hz', if_neg hz]

/-! ## 2. The level-`1` projection and amplitude -/

/-- The mean-free projection at a single particle, evaluated at `x_{0←z}`: it is the fibre value
minus the box mean of the fibre. -/
lemma boxQ_update_N1 (volA ℓ : ℝ) (u : ℝ³) (Φ : X1 → ℝ) (x : X1) (z : ℝ³) :
    Work.SmallBoxTBWord.boxQ volA (Work.UBBInputs9.bigBox ℓ u) 0 Φ (Function.update x 0 z)
      = Work.BSKinetic.slotFun1 Φ z
        - (1 / volA) * ∫ z' in Work.UBBInputs9.bigBox ℓ u, Work.BSKinetic.slotFun1 Φ z' := by
  have hupd : Function.update x 0 z = (fun _ : Fin 1 => z) := by funext j; fin_cases j; simp
  have hw : ∀ w : ℝ³, Function.update (fun _ : Fin 1 => z) 0 w = (fun _ => w) :=
    fun w => by funext j; fin_cases j; simp
  have hint : (∫ w in Work.UBBInputs9.bigBox ℓ u,
        Φ (Function.update (fun _ : Fin 1 => z) 0 w))
      = ∫ w in Work.UBBInputs9.bigBox ℓ u, Work.BSKinetic.slotFun1 Φ w := by
    apply integral_congr_ae
    filter_upwards with w
    rw [hw w]
    simp only [Work.BSKinetic.slotFun1]
  simp only [Work.SmallBoxTBWord.boxQ, Work.SmallBoxTBWord.boxP]
  rw [hupd, hint]
  rfl

/-- **The `N = 1` amplitude identity**: the `boxQInd`-projected, moving-box-windowed amplitude of
the one-particle state is the `kinFT` of the windowed mean-free fibre. -/
lemma tBamp_boxQInd_N1 {ℓ : ℝ} (hℓ : 0 < ℓ) (u : ℝ³) (Φ : X1 → ℝ) (p : ℝ³) (x : X1) :
    Work.SmallBoxTBWord.tBamp (Work.UBBInputs9.chiBig ℓ u) p
        (Work.UBBInputs8.boxQInd (ℓ ^ 3) (Work.UBBInputs9.bigBox ℓ u) 0 Φ) 0 x
      = Submission.BoseGases.kinFT
          (fun z : ℝ³ => (Work.BSKinetic.bsWin ℓ u z : ℂ) *
            (Work.BSKinetic.bsQ ℓ u (Work.BSKinetic.slotFun1 Φ) z : ℂ)) p := by
  rw [Work.UBBInputs9.A.tBamp_boxQInd (chiBig_eq_zero_of_notMem_bigBox hℓ u)]
  rw [Work.SmallBoxTBWord.tBamp_eq_kinFT]
  congr 1
  funext z
  rw [boxQ_update_N1 (ℓ ^ 3) ℓ u Φ x z,
      setIntegral_bigBox_eq_translate ℓ u (Work.BSKinetic.slotFun1 Φ)]
  simp only [Work.UBBInputs9.chiBig, Work.BSKinetic.bsWin, Work.BSKinetic.bsQ,
    Work.BSKinetic.bsMean, div_eq_inv_mul, mul_one]

/-! ## 3. The level-`1` slot energy and the reduction to `bsOneBody` -/

/-- The single-slot energy: the `(ℓ³)⁻¹`-normalised, `abox 1 ℓ`-integrated squared amplitude is
exactly the squared `kinFT` of the windowed mean-free fibre.  (The amplitude is independent of the
ambient configuration, and `|abox 1 ℓ| = ℓ³`.) -/
lemma slot_energy_N1 {ℓ : ℝ} (hℓ : 0 < ℓ) (u : ℝ³) (Φ : X1 → ℝ) (p : ℝ³) :
    (ℓ ^ 3)⁻¹ * ∫ x in Submission.BoseGases.abox 1 ℓ,
        ‖Work.SmallBoxTBWord.tBamp (Work.UBBInputs9.chiBig ℓ u) p
            (Work.UBBInputs8.boxQInd (ℓ ^ 3) (Work.UBBInputs9.bigBox ℓ u) 0 Φ) 0 x‖ ^ 2
      = ‖Submission.BoseGases.kinFT
          (fun z : ℝ³ => (Work.BSKinetic.bsWin ℓ u z : ℂ) *
            (Work.BSKinetic.bsQ ℓ u (Work.BSKinetic.slotFun1 Φ) z : ℂ)) p‖ ^ 2 := by
  rw [show (∫ x in Submission.BoseGases.abox 1 ℓ,
        ‖Work.SmallBoxTBWord.tBamp (Work.UBBInputs9.chiBig ℓ u) p
            (Work.UBBInputs8.boxQInd (ℓ ^ 3) (Work.UBBInputs9.bigBox ℓ u) 0 Φ) 0 x‖ ^ 2)
      = ∫ x in Submission.BoseGases.abox 1 ℓ,
        ‖Submission.BoseGases.kinFT
          (fun z : ℝ³ => (Work.BSKinetic.bsWin ℓ u z : ℂ) *
            (Work.BSKinetic.bsQ ℓ u (Work.BSKinetic.slotFun1 Φ) z : ℂ)) p‖ ^ 2 from by
    apply integral_congr_ae
    filter_upwards with x
    rw [tBamp_boxQInd_N1 hℓ u Φ p x]]
  rw [setIntegral_const, Measure.real_def, Submission.BoseGases.abox_volume 1 ℓ hℓ.le,
      ENNReal.toReal_ofReal (by positivity : (0 : ℝ) ≤ (ℓ ^ 3) ^ 1), pow_one]
  rw [smul_eq_mul, ← mul_assoc, inv_mul_cancel₀ (pow_ne_zero 3 (ne_of_gt hℓ)), one_mul]

theorem bigKinU_one_eq_oneBody {ℓ : ℝ} (hℓ : 0 < ℓ) (c : ℝ)
    (u : EuclideanSpace ℝ (Fin 3)) (Φ : Submission.BoseGases.X 1 → ℝ)
    (hΦ : ContDiff ℝ (⊤ : ENat) Φ) :
    Work.UBBInputs9.tBwordKinBigU 1 ℓ c u Φ
      = Work.BSKinetic.bsOneBody ℓ (Submission.BoseGases.fsKinCoeff c) u
          (Work.BSKinetic.slotFun1 Φ) := by
  rw [Work.UBBInputs9.tBwordKinBigU, Work.UBBInputs8.tBwordKinInd,
      Work.UBBInputs8.tBdiagFormInd, Fin.sum_univ_one, Work.BSKinetic.bsOneBody]
  congr 1
  apply integral_congr_ae
  filter_upwards with p
  rw [slot_energy_N1 hℓ u Φ p]

end Work.BSKinetic
