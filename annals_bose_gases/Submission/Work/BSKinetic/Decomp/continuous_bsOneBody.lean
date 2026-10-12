import Mathlib.Tactic.Have
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BSKinetic.Decomp.ShiftAux
import Submission.Work.BSKinetic.Decomp.bsShift_L2_tendsto
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

noncomputable section
open MeasureTheory Metric Filter
open scoped ContDiff Topology Real BigOperators

namespace Work.BSKinetic.Decomp

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

open Submission.BoseGases

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option linter.unusedVariables false

/-! ## 1.  The windowed state at the shifted origin -/

lemma bsWin_add_lsmul (ℓ : ℝ) (u z : ℝ³) : bsWin ℓ u (z + ℓ • u) = chiScale ℓ z := by
  rw [bsWin, add_sub_cancel_right]

lemma bsShift_eq_win (ℓ : ℝ) (ψ : ℝ³ → ℝ) (u z : ℝ³) :
    ((bsShift ℓ ψ u z : ℝ) : ℂ)
      = (bsWin ℓ u (z + ℓ • u) : ℂ) * ((bsQ ℓ u ψ (z + ℓ • u) : ℝ) : ℂ) := by
  rw [bsShift_apply, bsWin_add_lsmul]
  simp only [bsQ]
  push_cast
  ring

/-- Translation invariance of the Lebesgue integral on `ℝ³` for complex-valued functions. -/
lemma integral_comp_add_right_c (g : ℝ³ → ℂ) (a : ℝ³) :
    (∫ y : ℝ³, g (y + a)) = ∫ y : ℝ³, g y := by
  let e : ℝ³ ≃ᵐ ℝ³ := MeasurableEquiv.addRight a
  have hmp : MeasurePreserving (⇑e) volume volume := by
    change MeasurePreserving (fun x : ℝ³ => x + a) volume volume
    exact measurePreserving_add_right volume a
  simpa [e] using (hmp.integral_comp' (f := e) (g := g))

/-! ## 2.  Translation covariance of `kinFT` -/

lemma exp_phase_add (p y a : ℝ³) :
    Complex.exp (Complex.I * (inner ℝ p a : ℂ))
        * Complex.exp (-(Complex.I * (inner ℝ p (y + a) : ℂ)))
      = Complex.exp (-(Complex.I * (inner ℝ p y : ℂ))) := by
  rw [← Complex.exp_add]
  congr 1
  rw [inner_add_right]
  push_cast
  ring

lemma kinFT_comp_add (g : ℝ³ → ℂ) (a p : ℝ³) :
    kinFT (fun z => g (z + a)) p
      = Complex.exp (Complex.I * (inner ℝ p a : ℂ)) * kinFT g p := by
  rw [kinFT, kinFT]
  have hpt : ∀ y : ℝ³, Complex.exp (-(Complex.I * (inner ℝ p y : ℂ))) * g (y + a)
      = Complex.exp (Complex.I * (inner ℝ p a : ℂ))
        * (Complex.exp (-(Complex.I * (inner ℝ p (y + a) : ℂ))) * g (y + a)) := by
    intro y
    rw [show Complex.exp (-(Complex.I * ↑(inner ℝ p y))) * g (y + a)
        = (Complex.exp (Complex.I * ↑(inner ℝ p a))
            * Complex.exp (-(Complex.I * ↑(inner ℝ p (y + a))))) * g (y + a) from by
      rw [exp_phase_add]]
    ring
  rw [show (∫ y : ℝ³, Complex.exp (-(Complex.I * (inner ℝ p y : ℂ))) * g (y + a))
      = ∫ y : ℝ³, Complex.exp (Complex.I * (inner ℝ p a : ℂ))
        * (Complex.exp (-(Complex.I * (inner ℝ p (y + a) : ℂ))) * g (y + a)) from
        integral_congr_ae (Eventually.of_forall hpt)]
  rw [integral_const_mul]
  congr 1
  exact integral_comp_add_right_c
    (fun w : ℝ³ => Complex.exp (-(Complex.I * (inner ℝ p w : ℂ))) * g w) a

lemma norm_kinFT_comp_add (g : ℝ³ → ℂ) (a p : ℝ³) :
    ‖kinFT (fun z => g (z + a)) p‖ = ‖kinFT g p‖ := by
  rw [kinFT_comp_add]
  rw [norm_mul]
  have : ‖Complex.exp (Complex.I * (inner ℝ p a : ℂ))‖ = 1 := by
    rw [Complex.norm_exp]
    simp
  rw [this, one_mul]


/-! ## 3.  Integrability and additivity of `bsPsi` -/

lemma hasCompactSupport_bsShift_sub {ℓ : ℝ} (hℓ : 0 < ℓ) {ψ : ℝ³ → ℝ} (u v : ℝ³) :
    HasCompactSupport (fun z : ℝ³ => bsShift ℓ ψ u z - bsShift ℓ ψ v z) := by
  have h : (fun z : ℝ³ => bsShift ℓ ψ u z - bsShift ℓ ψ v z)
      = chiScale ℓ * fun z : ℝ³ =>
          ((ψ (z + ℓ • u) - bsMean ℓ u ψ) - (ψ (z + ℓ • v) - bsMean ℓ v ψ)) := by
    funext z
    show bsShift ℓ ψ u z - bsShift ℓ ψ v z
      = chiScale ℓ z * ((ψ (z + ℓ • u) - bsMean ℓ u ψ) - (ψ (z + ℓ • v) - bsMean ℓ v ψ))
    rw [bsShift_apply, bsShift_apply]
    ring
  rw [h]
  exact (chiScale_hasCompactSupport (ne_of_gt hℓ)).mul_right

/-! ## 5.  The kinetic form at the shifted state -/

theorem bsOneBody_eq_bsW_shift {ℓ : ℝ} (hℓ : 0 < ℓ) (F : ℝ → ℝ)
    (u : ℝ³) (ψ : ℝ³ → ℝ) :
    bsOneBody ℓ F u ψ = ((2 * Real.pi) ^ 3)⁻¹ * bsW F (bsShift ℓ ψ u) := by
  rw [bsOneBody, bsW]
  congr 1
  refine integral_congr_ae (Eventually.of_forall (fun p => ?_))
  have hnorm : ‖bsPsi (bsShift ℓ ψ u) p‖
      = ‖kinFT (fun z : ℝ³ => (bsWin ℓ u z : ℂ) * (bsQ ℓ u ψ z : ℂ)) p‖ := by
    rw [bsPsi]
    have hfun : (fun z : ℝ³ => (bsShift ℓ ψ u z : ℂ))
        = fun z : ℝ³ => (bsWin ℓ u (z + ℓ • u) : ℂ) * (bsQ ℓ u ψ (z + ℓ • u) : ℂ) := by
      funext z; exact bsShift_eq_win ℓ ψ u z
    rw [hfun, norm_kinFT_comp_add (fun x : ℝ³ => (bsWin ℓ u x : ℂ) * (bsQ ℓ u ψ x : ℂ))
      (ℓ • u) p]
  show F ‖p‖ * ‖kinFT (fun z : ℝ³ => (bsWin ℓ u z : ℂ) * (bsQ ℓ u ψ z : ℂ)) p‖ ^ 2
      = F ‖p‖ * ‖bsPsi (bsShift ℓ ψ u) p‖ ^ 2
  rw [hnorm]


/-! ## 6.  The target: continuity of the one-body big-box kinetic form in the box shift -/

lemma bsW_le_const {c K : ℝ} {h : ℝ³ → ℝ} (hd : ContDiff ℝ (⊤ : ENat) h)
    (hc : HasCompactSupport h) (hL2 : bsL2 h ≤ K) (hD : bsDir h ≤ K) :
    bsW (fsKinCoeff c) h ≤ (2 * Real.pi) ^ 3 * (2 * c ^ 2 * K + 2 * K) := by
  have h1 := bsW_le_L2_Dir (c := c) hd hc
  have h2 : 2 * c ^ 2 * bsL2 h + 2 * bsDir h ≤ 2 * c ^ 2 * K + 2 * K := by
    have ha : 2 * c ^ 2 * bsL2 h ≤ 2 * c ^ 2 * K := mul_le_mul_of_nonneg_left hL2 (by positivity)
    have hb : 2 * bsDir h ≤ 2 * K := mul_le_mul_of_nonneg_left hD (by norm_num)
    linarith
  have hX : (2 * Real.pi) ^ 3 * (((2 * Real.pi) ^ 3)⁻¹ * bsW (fsKinCoeff c) h)
      = bsW (fsKinCoeff c) h := by
    rw [← mul_assoc, mul_inv_cancel₀ (by positivity), one_mul]
  have h3 := mul_le_mul_of_nonneg_left (le_trans h1 h2)
    (by positivity : (0 : ℝ) ≤ (2 * Real.pi) ^ 3)
  rwa [hX] at h3

/-! ## the assembly -/

theorem continuous_bsOneBody {ℓ : ℝ} (hℓ : 0 < ℓ) (c : ℝ)
    (ψ : EuclideanSpace ℝ (Fin 3) → ℝ)
    (hψ : ContDiff ℝ (⊤ : ENat) ψ) (hcs : HasCompactSupport ψ) :
    Continuous (fun u : EuclideanSpace ℝ (Fin 3) =>
      Work.BSKinetic.bsOneBody ℓ (Submission.BoseGases.fsKinCoeff c) u ψ) := by
  have hshift : (fun u : ℝ³ => bsOneBody ℓ (fsKinCoeff c) u ψ)
      = fun u : ℝ³ => ((2 * Real.pi) ^ 3)⁻¹ * bsW (fsKinCoeff c) (bsShift ℓ ψ u) :=
    funext (fun u => bsOneBody_eq_bsW_shift hℓ (fsKinCoeff c) u ψ)
  rw [hshift]
  refine Continuous.const_mul ?_ _
  obtain ⟨K, hK0, hK⟩ := Aux.bsShift_H1_bounded hℓ hψ hcs
  refine continuous_iff_continuousAt.mpr (fun u₀ => ?_)
  have hLt : Filter.Tendsto (fun u : ℝ³ =>
      bsL2 (fun z : ℝ³ => bsShift ℓ ψ u z - bsShift ℓ ψ u₀ z)) (nhds u₀) (nhds 0) :=
    bsShift_L2_tendsto hℓ hψ hcs u₀
  have hDt : Filter.Tendsto (fun u : ℝ³ =>
      bsDir (fun z : ℝ³ => bsShift ℓ ψ u z - bsShift ℓ ψ u₀ z)) (nhds u₀) (nhds 0) :=
    Aux.bsShift_H1_tendsto hℓ hψ hcs u₀
  have hAt : Filter.Tendsto (fun u : ℝ³ => (2 * Real.pi) ^ 3 *
      (2 * c ^ 2 * bsL2 (fun z : ℝ³ => bsShift ℓ ψ u z - bsShift ℓ ψ u₀ z)
        + 2 * bsDir (fun z : ℝ³ => bsShift ℓ ψ u z - bsShift ℓ ψ u₀ z)))
      (nhds u₀) (nhds 0) := by
    have h1 : Filter.Tendsto (fun u : ℝ³ => 2 * c ^ 2 *
        bsL2 (fun z : ℝ³ => bsShift ℓ ψ u z - bsShift ℓ ψ u₀ z))
        (nhds u₀) (nhds (2 * c ^ 2 * 0)) := hLt.const_mul (2 * c ^ 2)
    have h2 : Filter.Tendsto (fun u : ℝ³ => 2 *
        bsDir (fun z : ℝ³ => bsShift ℓ ψ u z - bsShift ℓ ψ u₀ z))
        (nhds u₀) (nhds (2 * 0)) := hDt.const_mul 2
    have h3 := (h1.add h2).const_mul ((2 * Real.pi) ^ 3)
    simpa using h3
  have hst : Filter.Tendsto (fun u : ℝ³ => Real.sqrt ((2 * Real.pi) ^ 3 *
      (2 * c ^ 2 * bsL2 (fun z : ℝ³ => bsShift ℓ ψ u z - bsShift ℓ ψ u₀ z)
        + 2 * bsDir (fun z : ℝ³ => bsShift ℓ ψ u z - bsShift ℓ ψ u₀ z))))
      (nhds u₀) (nhds 0) := by
    have h5 := hAt.sqrt
    simpa using h5
  have hsq : Filter.Tendsto (fun u : ℝ³ => Real.sqrt ((2 * Real.pi) ^ 3 *
      (2 * c ^ 2 * bsL2 (fun z : ℝ³ => bsShift ℓ ψ u z - bsShift ℓ ψ u₀ z)
        + 2 * bsDir (fun z : ℝ³ => bsShift ℓ ψ u z - bsShift ℓ ψ u₀ z)))
      * Real.sqrt (4 * ((2 * Real.pi) ^ 3 * (2 * c ^ 2 * K + 2 * K))))
      (nhds u₀) (nhds 0) := by
    have h6 := hst.mul_const (Real.sqrt (4 * ((2 * Real.pi) ^ 3 * (2 * c ^ 2 * K + 2 * K))))
    simpa using h6
  have hbound : ∀ u : ℝ³, ‖bsW (fsKinCoeff c) (bsShift ℓ ψ u)
      - bsW (fsKinCoeff c) (bsShift ℓ ψ u₀)‖
      ≤ Real.sqrt ((2 * Real.pi) ^ 3 *
          (2 * c ^ 2 * bsL2 (fun z : ℝ³ => bsShift ℓ ψ u z - bsShift ℓ ψ u₀ z)
            + 2 * bsDir (fun z : ℝ³ => bsShift ℓ ψ u z - bsShift ℓ ψ u₀ z)))
        * Real.sqrt (4 * ((2 * Real.pi) ^ 3 * (2 * c ^ 2 * K + 2 * K))) := by
    intro u
    rw [Real.norm_eq_abs]
    refine le_trans (Aux.bsW_sub_abs_le (c := c)
      (h₁ := bsShift ℓ ψ u) (h₂ := bsShift ℓ ψ u₀)
      (contDiff_bsShift hℓ hψ u) (hasCompactSupport_bsShift (ne_of_gt hℓ) u)
      (contDiff_bsShift hℓ hψ u₀) (hasCompactSupport_bsShift (ne_of_gt hℓ) u₀)) ?_
    refine mul_le_mul (Real.sqrt_le_sqrt ?_) (Real.sqrt_le_sqrt ?_)
      (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    · have hle := bsW_le_L2_Dir (c := c)
        (h := fun z : ℝ³ => bsShift ℓ ψ u z - bsShift ℓ ψ u₀ z)
        ((contDiff_bsShift hℓ hψ u).sub (contDiff_bsShift hℓ hψ u₀))
        (hasCompactSupport_bsShift_sub hℓ u u₀)
      have hX : (2 * Real.pi) ^ 3 * (((2 * Real.pi) ^ 3)⁻¹ *
          bsW (fsKinCoeff c) (fun z : ℝ³ => bsShift ℓ ψ u z - bsShift ℓ ψ u₀ z))
          = bsW (fsKinCoeff c) (fun z : ℝ³ => bsShift ℓ ψ u z - bsShift ℓ ψ u₀ z) := by
        rw [← mul_assoc, mul_inv_cancel₀ (by positivity), one_mul]
      have hle2 := mul_le_mul_of_nonneg_left hle
        (by positivity : (0 : ℝ) ≤ (2 * Real.pi) ^ 3)
      rwa [hX] at hle2
    · have hb : ∀ v : ℝ³, bsW (fsKinCoeff c) (bsShift ℓ ψ v)
          ≤ (2 * Real.pi) ^ 3 * (2 * c ^ 2 * K + 2 * K) := fun v =>
        bsW_le_const (contDiff_bsShift hℓ hψ v)
          (hasCompactSupport_bsShift (ne_of_gt hℓ) v) (hK v).1 (hK v).2
      have h1 := hb u
      have h2 := hb u₀
      linarith
  have hsq' : Filter.Tendsto (fun u : ℝ³ => bsW (fsKinCoeff c) (bsShift ℓ ψ u)
      - bsW (fsKinCoeff c) (bsShift ℓ ψ u₀)) (nhds u₀) (nhds 0) :=
    squeeze_zero_norm' (Eventually.of_forall hbound) hsq
  have h7 := hsq'.add_const (bsW (fsKinCoeff c) (bsShift ℓ ψ u₀))
  simpa only [ContinuousAt, sub_add_cancel, zero_add] using h7

end Work.BSKinetic.Decomp
