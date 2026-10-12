import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BSKinetic.Decomp.ShiftDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BSKinetic

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

open MeasureTheory
open Submission.BoseGases
open scoped ENNReal

/-! ## The `N = 1` collapse of `tBdiagForm` to `bsW`

With a single slot the `p`-diagonal word `tBdiagForm a A volA χ F φ` is the single term
`(2π)⁻³∫_p F‖p‖·(a³)⁻¹∫_{abox 1 a}‖tBamp χ p (Q_Aφ) 0 x‖²`.  The level-`0` amplitude of the
one-particle state is independent of the ambient configuration `x`, and equals the `p`-Fourier
transform of the windowed mean-free fibre `z ↦ χ z·(φ(1,z) − volA⁻¹∫_A φ(1,z'))`.  Since
`|abox 1 a| = a³`, the `x`-integral cancels the `(a³)⁻¹`, leaving the `F`-weighted `L²` norm²
`bsW F` of that fibre. -/

/-- **The box mean at a single slot**: the mean of `φ (Function.update x 0 ·)` over `A` is the
mean of the fibre `z ↦ φ (fun _ => z)`, since `Function.update x 0 z = fun _ => z` for `x : X 1`. -/
lemma boxP_N1 (volA : ℝ) (A : Set ℝ³) (φ : X 1 → ℝ) (x : X 1) :
    Work.SmallBoxTBWord.boxP volA A 0 φ x
      = (1 / volA) * ∫ z' in A, φ (fun _ : Fin 1 => z') := by
  rw [Work.SmallBoxTBWord.boxP]
  congr 1
  apply integral_congr_ae
  filter_upwards with z
  congr 1
  funext j
  fin_cases j
  simp

/-- **The mean-free projection at a single slot**:
`boxQ volA A 0 φ x = φ x − volA⁻¹∫_A φ(fun _ => z') dz'`. -/
lemma boxQ_N1 (volA : ℝ) (A : Set ℝ³) (φ : X 1 → ℝ) (x : X 1) :
    Work.SmallBoxTBWord.boxQ volA A 0 φ x
      = φ x - (1 / volA) * ∫ z' in A, φ (fun _ : Fin 1 => z') := by
  rw [Work.SmallBoxTBWord.boxQ, boxP_N1]

/-- **The level-`0` amplitude**: `tBamp` of the projected one-particle state is the `kinFT` of the
windowed mean-free fibre. -/
lemma tBamp_boxQ_N1 (volA : ℝ) (A : Set ℝ³) (χ : ℝ³ → ℝ) (φ : X 1 → ℝ) (p : ℝ³) (x : X 1) :
    Work.SmallBoxTBWord.tBamp χ p (Work.SmallBoxTBWord.boxQ volA A 0 φ) 0 x
      = Decomp.bsPsi (fun z : ℝ³ => χ z *
          (φ (fun _ : Fin 1 => z) - (1 / volA) * ∫ z' in A, φ (fun _ : Fin 1 => z'))) p := by
  rw [Work.SmallBoxTBWord.tBamp_eq_kinFT, Decomp.bsPsi]
  congr 1
  funext z
  rw [show Function.update x 0 z = (fun _ : Fin 1 => z) from by funext j; fin_cases j; simp,
    boxQ_N1]
  push_cast
  ring

/-- **The single-slot energy**: the `(a³)⁻¹`-normalised, `abox 1 a`-integrated squared amplitude is
exactly the squared `kinFT` of the windowed mean-free fibre. -/
lemma bsPsi_slot_energy_N1 {a : ℝ} (ha : 0 < a) (volA : ℝ) (A : Set ℝ³) (χ : ℝ³ → ℝ)
    (φ : X 1 → ℝ) (p : ℝ³) :
    (a ^ 3)⁻¹ * ∫ x in abox 1 a,
        ‖Work.SmallBoxTBWord.tBamp χ p (Work.SmallBoxTBWord.boxQ volA A 0 φ) 0 x‖ ^ 2
      = ‖Decomp.bsPsi (fun z : ℝ³ => χ z *
          (φ (fun _ : Fin 1 => z) - (1 / volA) * ∫ z' in A, φ (fun _ : Fin 1 => z'))) p‖ ^ 2 := by
  rw [show (∫ x in abox 1 a,
        ‖Work.SmallBoxTBWord.tBamp χ p (Work.SmallBoxTBWord.boxQ volA A 0 φ) 0 x‖ ^ 2)
      = ∫ x in abox 1 a,
        ‖Decomp.bsPsi (fun z : ℝ³ => χ z *
          (φ (fun _ : Fin 1 => z) - (1 / volA) * ∫ z' in A, φ (fun _ : Fin 1 => z'))) p‖ ^ 2 from by
    apply integral_congr_ae
    filter_upwards with x
    rw [tBamp_boxQ_N1]]
  rw [setIntegral_const, Measure.real_def, Submission.BoseGases.abox_volume 1 a ha.le,
      ENNReal.toReal_ofReal (by positivity : (0 : ℝ) ≤ (a ^ 3) ^ 1), pow_one]
  rw [smul_eq_mul, ← mul_assoc, inv_mul_cancel₀ (pow_ne_zero 3 (ne_of_gt ha)), one_mul]

theorem tBdiagForm_one_eq_bsW {a : ℝ} (ha : 0 < a)
    {A : Set (EuclideanSpace ℝ (Fin 3))} {volA : ℝ} {χ : EuclideanSpace ℝ (Fin 3) → ℝ}
    (F : ℝ → ℝ) (φ : Submission.BoseGases.X 1 → ℝ) :
    Work.SmallBoxTBWord.tBdiagForm a A volA χ F φ
      = ((2 * Real.pi) ^ 3)⁻¹ * Work.BSKinetic.Decomp.bsW F
          (fun z : EuclideanSpace ℝ (Fin 3) => χ z *
            (φ (fun _ : Fin 1 => z)
              - (1 / volA) * ∫ z' in A, φ (fun _ : Fin 1 => z'))) := by
  rw [Work.SmallBoxTBWord.tBdiagForm, Fin.sum_univ_one, Decomp.bsW]
  congr 1
  apply integral_congr_ae
  filter_upwards with p
  rw [bsPsi_slot_energy_N1 ha volA A χ φ p]

end Work.BSKinetic
