import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFock.PotGroupDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.pin_e0_eq`

The condensate coefficient of the honest bundle is *pinned*: if `e 0` is, a.e., a constant `c`
times the sharp box indicator `θ_Λ = thetaFun ℓ` (`Λ = boxL ℓ` the cube of side `ℓ`), with
`conj c · c = (ℓ³)⁻¹`, and if in addition the pairing with `θ_Λ` takes the normalised value

    ∫ conj(e 0) · θ_Λ = ℓ^{3/2},

then the constant is the *positive real* `(√(ℓ³))⁻¹`, i.e. `e 0 =ᵐ (√(ℓ³))⁻¹ · θ_Λ`.

The mechanism is a single computation: `conj θ_Λ · θ_Λ = 1_{Λ}` (the indicator of the box, since
`θ_Λ` is real-valued and idempotent), so `∫ conj θ_Λ · θ_Λ = |Λ| = ℓ³` and the pairing hypothesis
reads `conj c · ℓ³ = ℓ^{3/2}`, i.e. `c` is real and equal to `ℓ^{-3/2} = (√(ℓ³))⁻¹`.
-/

namespace Work.BoseBoxFock

open MeasureTheory

/-- **The self-pairing of the sharp box indicator**: since `thetaFun ℓ` is the (complex valued)
indicator of the box `Λ(ℓ) = boxL ℓ`, the product `conj θ · θ` is again that indicator, so its
Bochner integral is the volume `|Λ(ℓ)| = ℓ³`. -/
theorem thetaFun_self_integral {ℓ : ℝ} (hℓ : 0 < ℓ) :
    (∫ z : EuclideanSpace ℝ (Fin 3),
        (starRingEnd ℂ) (Work.BoseK15.corpusBox.thetaFun ℓ z)
          * Work.BoseK15.corpusBox.thetaFun ℓ z) = ((ℓ ^ 3 : ℝ) : ℂ) := by
  have hind : (fun z : EuclideanSpace ℝ (Fin 3) =>
        (starRingEnd ℂ) (Work.BoseK15.corpusBox.thetaFun ℓ z)
          * Work.BoseK15.corpusBox.thetaFun ℓ z)
      = (Work.BoseK15.corpusBox.boxL ℓ).indicator (fun _ => (1 : ℂ)) := by
    funext z
    rw [Work.BoseB4.BoxData.thetaFun_apply]
    by_cases hz : z ∈ Work.BoseK15.corpusBox.boxL ℓ
    · simp [hz]
    · simp [hz]
  rw [hind, MeasureTheory.integral_indicator_const _
    (Work.BoseB4.BoxData.boxL_measurableSet _ ℓ)]
  rw [MeasureTheory.Measure.real_def, Work.BoseB4.BoxData.volume_boxL_toReal _ hℓ]
  simp

theorem pin_e0_eq {m : ℕ} [NeZero m] {ℓ : ℝ} (hℓ : 0 < ℓ)
    {e : Fin m → EuclideanSpace ℝ (Fin 3) → ℂ}
    (hc : ∃ c : ℂ, (starRingEnd ℂ) c * c = ((ℓ ^ 3 : ℝ))⁻¹ ∧
      e 0 =ᵐ[MeasureTheory.volume] fun z => c * Work.BoseK15.corpusBox.thetaFun ℓ z)
    (hpair : (∫ z : EuclideanSpace ℝ (Fin 3),
        (starRingEnd ℂ) (e 0 z) * Work.BoseK15.corpusBox.thetaFun ℓ z)
      = (((ℓ ^ (3 / 2 : ℝ) : ℝ)) : ℂ)) :
    e 0 =ᵐ[MeasureTheory.volume] fun z =>
      ((Real.sqrt (ℓ ^ 3))⁻¹ : ℂ) * Work.BoseK15.corpusBox.thetaFun ℓ z := by
  obtain ⟨c, _, hec⟩ := hc
  have hself : (∫ z : EuclideanSpace ℝ (Fin 3),
      (starRingEnd ℂ) (Work.BoseK15.corpusBox.thetaFun ℓ z)
        * Work.BoseK15.corpusBox.thetaFun ℓ z) = ((ℓ ^ 3 : ℝ) : ℂ) :=
    thetaFun_self_integral hℓ
  -- replace `e 0` by `c · θ` inside the pairing integral
  have hInt1 : (∫ z : EuclideanSpace ℝ (Fin 3),
        (starRingEnd ℂ) (e 0 z) * Work.BoseK15.corpusBox.thetaFun ℓ z)
      = ∫ z : EuclideanSpace ℝ (Fin 3),
        (starRingEnd ℂ) (c * Work.BoseK15.corpusBox.thetaFun ℓ z)
          * Work.BoseK15.corpusBox.thetaFun ℓ z := by
    apply MeasureTheory.integral_congr_ae
    filter_upwards [hec] with z hz
    rw [hz]
  -- the constant comes out of the integral
  have hInt2 : (∫ z : EuclideanSpace ℝ (Fin 3),
        (starRingEnd ℂ) (c * Work.BoseK15.corpusBox.thetaFun ℓ z)
          * Work.BoseK15.corpusBox.thetaFun ℓ z)
      = (starRingEnd ℂ) c * ∫ z : EuclideanSpace ℝ (Fin 3),
        (starRingEnd ℂ) (Work.BoseK15.corpusBox.thetaFun ℓ z)
          * Work.BoseK15.corpusBox.thetaFun ℓ z := by
    rw [← MeasureTheory.integral_const_mul]
    apply MeasureTheory.integral_congr_ae
    filter_upwards with z
    simp only [map_mul]
    ring
  -- the pairing hypothesis therefore reads `conj c · ℓ³ = ℓ^{3/2}`
  have hkey : (starRingEnd ℂ) c * ((ℓ ^ 3 : ℝ) : ℂ) = (((ℓ ^ (3 / 2 : ℝ) : ℝ)) : ℂ) := by
    rw [← hself, ← hInt2, ← hInt1, hpair]
  have hsqrt : Real.sqrt (ℓ ^ 3) = (ℓ ^ (3 / 2 : ℝ)) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast ℓ 3, ← Real.rpow_mul (le_of_lt hℓ)]
    norm_num
  have hkey' : (starRingEnd ℂ) c * ((ℓ ^ 3 : ℝ) : ℂ)
      = ((Real.sqrt (ℓ ^ 3) : ℝ) : ℂ) := by
    rw [hkey, ← hsqrt]
  have hsq : ((Real.sqrt (ℓ ^ 3) : ℝ) : ℂ) * ((Real.sqrt (ℓ ^ 3) : ℝ) : ℂ)
      = ((ℓ ^ 3 : ℝ) : ℂ) := by
    rw [← Complex.ofReal_mul, ← pow_two, Real.sq_sqrt (by positivity)]
  have hsne : ((Real.sqrt (ℓ ^ 3) : ℝ) : ℂ) ≠ 0 := by
    rw [Ne, Complex.ofReal_eq_zero]
    exact ne_of_gt (Real.sqrt_pos_of_pos (by positivity))
  -- cancelling `√(ℓ³)`: `conj c · √(ℓ³) = 1`
  have hconjc : (starRingEnd ℂ) c * ((Real.sqrt (ℓ ^ 3) : ℝ) : ℂ) = 1 := by
    refine mul_right_cancel₀ hsne ?_
    calc ((starRingEnd ℂ) c * ↑(Real.sqrt (ℓ ^ 3))) * ↑(Real.sqrt (ℓ ^ 3))
        = (starRingEnd ℂ) c * (↑(Real.sqrt (ℓ ^ 3)) * ↑(Real.sqrt (ℓ ^ 3))) := by
          rw [mul_assoc]
      _ = (starRingEnd ℂ) c * ((ℓ ^ 3 : ℝ) : ℂ) := by rw [hsq]
      _ = ((Real.sqrt (ℓ ^ 3) : ℝ) : ℂ) := hkey'
      _ = 1 * ((Real.sqrt (ℓ ^ 3) : ℝ) : ℂ) := by rw [one_mul]
  -- hence `conj c = (√(ℓ³))⁻¹`, and conjugating again gives `c = (√(ℓ³))⁻¹` (a real scalar)
  have hcval : c = (((Real.sqrt (ℓ ^ 3) : ℝ) : ℂ))⁻¹ := by
    have h1 : (starRingEnd ℂ) c = (((Real.sqrt (ℓ ^ 3) : ℝ) : ℂ))⁻¹ :=
      eq_inv_of_mul_eq_one_left hconjc
    calc c = (starRingEnd ℂ) ((starRingEnd ℂ) c) := (Complex.conj_conj c).symm
      _ = (starRingEnd ℂ) ((((Real.sqrt (ℓ ^ 3) : ℝ) : ℂ))⁻¹) := by rw [h1]
      _ = (((Real.sqrt (ℓ ^ 3) : ℝ) : ℂ))⁻¹ := by rw [map_inv₀, Complex.conj_ofReal]
  filter_upwards [hec] with z hz
  rw [hz, hcval]

end Work.BoseBoxFock
