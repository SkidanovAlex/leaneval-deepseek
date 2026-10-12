import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Submission.Work.OneBodyKin.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.OneBodyKin.famSym_zero` — the projected family symbol annihilates the zero momentum

The projected moving-box family form annihilates constant functions (`Q_u 1 = 0`), hence its
symbol `Work.OneBodyKin.famSym ℓ F` vanishes at `q = 0` for **every** symbol `F`:

    `famSym ℓ F 0 = 0`.

Direct computation from the definitions `Work.OneBodyKin.Defs.famSym = symA − 2(2π)⁻³ boxHat symD + symC`:

* `boxHat ℓ 0 = ℓ³` (the box `acube ℓ` has volume `ℓ³`);
* `symD ℓ F 0 = ∫_p F‖p‖ profHat(ℓp)²` (the `q = 0` cross term, using `profHat` even);
* `symA ℓ F 0 = (2π)⁻³ ℓ³ ∫_p F‖p‖ profHat(ℓp)²` (the change of variables `p ↦ ℓp`, Haar scaling);

and the two `q = 0` substitutions of `symA` in the identity cancel against the cross term.
-/

noncomputable section

open MeasureTheory

namespace Work.OneBodyKin

set_option autoImplicit false

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-- The box Fourier profile at the origin is the volume of the box: `boxHat ℓ 0 = ℓ³`. -/
lemma boxHat_zero (ℓ : ℝ) (hℓ : 0 ≤ ℓ) : boxHat ℓ 0 = ℓ ^ 3 := by
  unfold boxHat
  simp only [inner_zero_left, Real.cos_zero]
  rw [MeasureTheory.setIntegral_const]
  simp only [smul_eq_mul, mul_one]
  rw [MeasureTheory.Measure.real_def]
  rw [Submission.BoseGases.acube_volume ℓ hℓ, ENNReal.toReal_ofReal (pow_nonneg hℓ 3)]

/-- The `q = 0` cross symbol: `symD ℓ F 0 = ∫_p F‖p‖ profHat(ℓp)²` (parity of `profHat`). -/
lemma symD_zero (ℓ : ℝ) (F : ℝ → ℝ) :
    symD ℓ F 0 = ∫ p : ℝ³, F ‖p‖ * (profHat (ℓ • p)) ^ 2 := by
  unfold symD
  refine integral_congr_ae (Filter.Eventually.of_forall (fun p => ?_))
  simp only [zero_sub, smul_neg, profHat_even]
  ring

/-- The `q = 0` unprojected symbol: `symA ℓ F 0 = (2π)⁻³ ℓ³ ∫_p F‖p‖ profHat(ℓp)²`,
by the Haar change of variables `p ↦ ℓp` (`ℓ > 0`). -/
lemma symA_zero (ℓ : ℝ) (hℓ : 0 < ℓ) (F : ℝ → ℝ) :
    symA ℓ F 0
      = ((2 * Real.pi) ^ 3)⁻¹ * ℓ ^ 3 * ∫ p : ℝ³, F ‖p‖ * (profHat (ℓ • p)) ^ 2 := by
  unfold symA
  have hI : (∫ x : ℝ³, F ‖ℓ⁻¹ • x‖ * (profHat x) ^ 2)
      = ℓ ^ 3 * (∫ y : ℝ³, F ‖y‖ * (profHat (ℓ • y)) ^ 2) := by
    have hcomp := Measure.integral_comp_inv_smul (volume : Measure ℝ³)
        (fun y : ℝ³ => F ‖y‖ * (profHat (ℓ • y)) ^ 2) ℓ
    rw [finrank_euclideanSpace_fin] at hcomp
    rw [show (∫ x : ℝ³, F ‖ℓ⁻¹ • x‖ * (profHat (ℓ • (ℓ⁻¹ • x))) ^ 2)
          = (∫ x : ℝ³, F ‖ℓ⁻¹ • x‖ * (profHat x) ^ 2) from by
        refine integral_congr_ae (Filter.Eventually.of_forall (fun x => ?_))
        simp only [smul_smul, mul_inv_cancel₀ hℓ.ne', one_smul]] at hcomp
    rw [abs_of_pos (pow_pos hℓ 3), smul_eq_mul] at hcomp
    exact hcomp
  rw [show (∫ p : ℝ³, F ‖(0 : ℝ³) + ℓ⁻¹ • p‖ * (profHat p) ^ 2)
        = (∫ x : ℝ³, F ‖ℓ⁻¹ • x‖ * (profHat x) ^ 2) from by
      refine integral_congr_ae (Filter.Eventually.of_forall (fun p => ?_))
      simp]
  rw [hI]
  ring

theorem famSym_zero {ℓ : ℝ} (hℓ : 0 < ℓ) (F : ℝ → ℝ) :
    Work.OneBodyKin.famSym ℓ F 0 = 0 := by
  unfold famSym symC
  rw [boxHat_zero ℓ hℓ.le, symD_zero ℓ F, symA_zero ℓ hℓ F]
  field_simp [hℓ.ne']
  ring

end Work.OneBodyKin
