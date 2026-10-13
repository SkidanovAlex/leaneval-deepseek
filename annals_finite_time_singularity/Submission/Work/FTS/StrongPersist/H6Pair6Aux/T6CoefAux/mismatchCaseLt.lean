import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.T6CoefAux.mismatchAux
import Submission.Work.FTS.TransportS.T2SupB2.mixed_pointwise_le_Xn

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The `a₁ < a` case of the mismatch coefficient estimate

This file proves the `a₁ < a` branch of `T6CoefAux.mismatchCoefCase`: the coefficient

`∫∫ w² sin(2θ)^{-γ} · (D_z^{b₁}D_θ^{a₁} A) · (D_z^{b-b₁}D_θ^{a-a₁} f) · (D_z^b D_θ^a f)`

where the `A`-slot carries `1 ≤ a₁` angular derivatives and `a₁ + b₁ ≤ 2`.  The pointwise
bound `|D_z^{b₁}D_θ^{a₁} A(z,θ)| ≤ √15 · Xn α A` (`T2SupB2.mixed_pointwise_le_Xn`) turns
the `A`-factor into the constant `K4`, and the two `f`-factors — both *mixed* slots of total
order `≤ 6` with at least one angular derivative — are absorbed by the `σ^{-γ}`-weighted
AM–GM estimate against the single mixed slots of `HkSq α 6 f` (`mismatchAux.mixed_slot_le`).
-/

namespace Work.FTS.StrongPersist.H6Pair6Aux.T6CoefAux

open scoped Real Topology
open MeasureTheory Set Filter

noncomputable section

/-- The product measure on the quadrant, spelled out (so that every statement below is
syntactically the measure occurring in the goal). -/
local notation "PM" => MeasureTheory.Measure.prod
  (MeasureTheory.volume.restrict Work.Spaces.Iz) (MeasureTheory.volume.restrict Work.Spaces.Iθ)

/-- `|a b| ≤ (a² + b²)/2`. -/
private lemma abs_mul_le_half_sq_add (a b : ℝ) : |a * b| ≤ (a ^ 2 + b ^ 2) / 2 := by
  rw [abs_mul]
  have h := two_mul_le_add_sq |a| |b|
  rw [sq_abs a, sq_abs b] at h
  linarith

set_option maxHeartbeats 1600000 in
theorem mismatchCaseLt : ∃ C : ℝ, 0 < C ∧ ∀ α ∈ Set.Ioc (0 : ℝ) 1,
    ∀ (A f : ℝ → ℝ → ℝ) (K0 K4 : ℝ) (a b a₁ b₁ : ℕ),
      Work.FTS.EllipticEst.SmoothOpen A → Work.Spaces.HkMem α 4 A →
      Work.Spaces.HkMem α 6 A →
      (∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 → |A z θ| ≤ K0) →
      Work.FTS.Nonlin.Xn α A ≤ K4 →
      Work.FTS.EllipticEst.SmoothOpen f → Work.Spaces.HkMem α 7 f →
      Work.Spaces.VanishTheta f →
      1 ≤ a₁ → a₁ + b₁ ≤ 2 → a₁ ≤ a → b₁ ≤ b → a + b ≤ 6 → a₁ < a →
      MeasureTheory.Integrable (fun p : ℝ × ℝ => Work.FTS.TransportS.leafGam α p.1 p.2
          * Work.Spaces.mixed b₁ a₁ A p.1 p.2
          * Work.Spaces.mixed (b - b₁) (a - a₁) f p.1 p.2
          * Work.Spaces.mixed b a f p.1 p.2)
          ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
            (MeasureTheory.volume.restrict Work.Spaces.Iθ)) ∧
      |∫ p, Work.FTS.TransportS.leafGam α p.1 p.2
            * Work.Spaces.mixed b₁ a₁ A p.1 p.2
            * Work.Spaces.mixed (b - b₁) (a - a₁) f p.1 p.2
            * Work.Spaces.mixed b a f p.1 p.2
          ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
            (MeasureTheory.volume.restrict Work.Spaces.Iθ))|
        ≤ C * α ^ (-(3 : ℝ)) * ((1 + K0 + K4) * (1 + Work.Spaces.HkSq α 6 f)) := by
  obtain ⟨Cm, hCmpos, hCm⟩ := Work.FTS.TransportS.T2SupB2.mixed_pointwise_le_Xn
  refine ⟨Cm, hCmpos, ?_⟩
  intro α hα A f K0 K4 a b a₁ b₁ hAsm hA4 hA6 hAbdd hA4bnd hfsm hf7 hfv
    ha₁ hab₁ ha₁a hb₁b hab hlt
  have hα0 : 0 < α := hα.1
  have hα1 : α ≤ 1 := hα.2
  have hK0 : 0 ≤ K0 := by
    have h := hAbdd 1 (Real.pi / 4) one_pos (by linarith [Real.pi_pos])
      (by linarith [Real.pi_pos])
    have h2 := abs_nonneg (A 1 (Real.pi / 4))
    linarith
  have hK4 : 0 ≤ K4 := le_trans (Work.Spaces.HkNorm_nonneg α 4 A) hA4bnd
  have h6 : Work.Spaces.HkMem α 6 f :=
    Work.FTS.OpenPkg.HkMem_mono_open hfsm 6 (by norm_num) hf7
  have hH : 0 ≤ Work.Spaces.HkSq α 6 f := Work.Spaces.HkSq_nonneg α 6 f
  have hα3 : (1 : ℝ) ≤ α ^ (-(3 : ℝ)) := by
    have h := Real.rpow_le_rpow_of_exponent_ge hα0 hα1 (show (-(3 : ℝ)) ≤ 0 by norm_num)
    rwa [Real.rpow_zero] at h
  -- the two mixed `f`-slots and their `σ^{-γ}`-weighted bounds
  have hYint := mixed_slot_le (α := α) 6 hfsm h6 (i := a - a₁) (j := b - b₁)
    (by omega) (by omega)
  have hZint := mixed_slot_le (α := α) 6 hfsm h6 (i := a) (j := b) (by omega) (by omega)
  have hYint' : MeasureTheory.Integrable (fun p : ℝ × ℝ =>
      (Work.Spaces.w p.1) ^ 2 * (Real.sin (2 * p.2)) ^ (-(Work.Spaces.gam α))
        * (Work.Spaces.mixed (b - b₁) (a - a₁) f p.1 p.2) ^ 2) PM := hYint.1
  have hZint' : MeasureTheory.Integrable (fun p : ℝ × ℝ =>
      (Work.Spaces.w p.1) ^ 2 * (Real.sin (2 * p.2)) ^ (-(Work.Spaces.gam α))
        * (Work.Spaces.mixed b a f p.1 p.2) ^ 2) PM := hZint.1
  have hYval : (∫ p, (Work.Spaces.w p.1) ^ 2 * (Real.sin (2 * p.2)) ^ (-(Work.Spaces.gam α))
        * (Work.Spaces.mixed (b - b₁) (a - a₁) f p.1 p.2) ^ 2 ∂PM)
      ≤ Work.Spaces.HkSq α 6 f := hYint.2
  have hZval : (∫ p, (Work.Spaces.w p.1) ^ 2 * (Real.sin (2 * p.2)) ^ (-(Work.Spaces.gam α))
        * (Work.Spaces.mixed b a f p.1 p.2) ^ 2 ∂PM) ≤ Work.Spaces.HkSq α 6 f := hZint.2
  -- the pointwise bound on the `A`-slot
  have hXpt : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      |Work.Spaces.mixed b₁ a₁ A z θ| ≤ Cm * K4 := by
    intro z θ hz hθ0 hθ1
    exact le_trans (hCm α A hα0 hα1 hAsm hA4 b₁ a₁ ha₁ hab₁ z θ hz hθ0 hθ1)
      (mul_le_mul_of_nonneg_left hA4bnd hCmpos.le)
  set F : ℝ × ℝ → ℝ := fun p => Work.FTS.TransportS.leafGam α p.1 p.2
      * Work.Spaces.mixed b₁ a₁ A p.1 p.2
      * Work.Spaces.mixed (b - b₁) (a - a₁) f p.1 p.2
      * Work.Spaces.mixed b a f p.1 p.2 with hFdef
  have hFaesm : MeasureTheory.AEStronglyMeasurable F PM := by
    have h1 : ContinuousOn (fun p : ℝ × ℝ => Work.FTS.TransportS.leafGam α p.1 p.2)
        Work.FTS.EllipticEst.Q0 := by
      unfold Work.FTS.TransportS.leafGam
      exact contOn_w.mul (contOn_sig α)
    have h2 : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.mixed b₁ a₁ A p.1 p.2)
        Work.FTS.EllipticEst.Q0 := (hAsm.mixed b₁ a₁).continuousOn
    have h3 : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.mixed (b - b₁) (a - a₁) f p.1 p.2)
        Work.FTS.EllipticEst.Q0 := (hfsm.mixed (b - b₁) (a - a₁)).continuousOn
    have h4 : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.mixed b a f p.1 p.2)
        Work.FTS.EllipticEst.Q0 := (hfsm.mixed b a).continuousOn
    rw [hFdef]
    exact Work.Spaces.aesm_of_continuousOn_Qd _ (((h1.mul h2).mul h3).mul h4)
  -- the pointwise AM–GM majorant
  have hpt : ∀ᵐ p ∂PM, |F p| ≤ Cm * K4 * ((1 / 2) *
      ((Work.Spaces.w p.1) ^ 2 * (Real.sin (2 * p.2)) ^ (-(Work.Spaces.gam α))
          * (Work.Spaces.mixed (b - b₁) (a - a₁) f p.1 p.2) ^ 2
        + (Work.Spaces.w p.1) ^ 2 * (Real.sin (2 * p.2)) ^ (-(Work.Spaces.gam α))
          * (Work.Spaces.mixed b a f p.1 p.2) ^ 2)) := by
    refine Work.FTS.TransportS.ae_of_forall_Qd (fun z θ hz hθ0 hθ1 => ?_)
    dsimp only
    have hs : 0 < Real.sin (2 * θ) :=
      Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos])
    have hWnn : 0 ≤ (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) :=
      mul_nonneg (sq_nonneg _) (Real.rpow_nonneg hs.le _)
    have hb := hXpt z θ hz hθ0 hθ1
    have hgm : |Work.Spaces.mixed (b - b₁) (a - a₁) f z θ| * |Work.Spaces.mixed b a f z θ|
        ≤ (1 / 2) * ((Work.Spaces.mixed (b - b₁) (a - a₁) f z θ) ^ 2
            + (Work.Spaces.mixed b a f z θ) ^ 2) := by
      have h := abs_mul_le_half_sq_add (Work.Spaces.mixed (b - b₁) (a - a₁) f z θ)
        (Work.Spaces.mixed b a f z θ)
      rw [abs_mul] at h
      linarith
    have hFp : |F (z, θ)| = (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
        * |Work.Spaces.mixed b₁ a₁ A z θ|
        * (|Work.Spaces.mixed (b - b₁) (a - a₁) f z θ| * |Work.Spaces.mixed b a f z θ|) := by
      rw [hFdef]
      simp only [Work.FTS.TransportS.leafGam]
      rw [abs_mul, abs_mul, abs_mul,
        abs_of_nonneg (mul_nonneg (sq_nonneg _) (Real.rpow_nonneg hs.le _))]
      ring
    rw [hFp]
    have hnn : 0 ≤ (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
        * (|Work.Spaces.mixed (b - b₁) (a - a₁) f z θ| * |Work.Spaces.mixed b a f z θ|) :=
      mul_nonneg hWnn (mul_nonneg (abs_nonneg _) (abs_nonneg _))
    have hkey : (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
          * |Work.Spaces.mixed b₁ a₁ A z θ|
          * (|Work.Spaces.mixed (b - b₁) (a - a₁) f z θ| * |Work.Spaces.mixed b a f z θ|)
        ≤ Cm * K4 * ((Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
          * (|Work.Spaces.mixed (b - b₁) (a - a₁) f z θ| * |Work.Spaces.mixed b a f z θ|)) := by
      calc (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
            * |Work.Spaces.mixed b₁ a₁ A z θ|
            * (|Work.Spaces.mixed (b - b₁) (a - a₁) f z θ| * |Work.Spaces.mixed b a f z θ|)
          = ((Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
              * (|Work.Spaces.mixed (b - b₁) (a - a₁) f z θ| * |Work.Spaces.mixed b a f z θ|))
            * |Work.Spaces.mixed b₁ a₁ A z θ| := by ring
        _ ≤ ((Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
              * (|Work.Spaces.mixed (b - b₁) (a - a₁) f z θ| * |Work.Spaces.mixed b a f z θ|))
            * (Cm * K4) := mul_le_mul_of_nonneg_left hb hnn
        _ = Cm * K4 * ((Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
              * (|Work.Spaces.mixed (b - b₁) (a - a₁) f z θ| * |Work.Spaces.mixed b a f z θ|)) := by
            ring
    have hgm2 : (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
          * (|Work.Spaces.mixed (b - b₁) (a - a₁) f z θ| * |Work.Spaces.mixed b a f z θ|)
        ≤ (1 / 2) * ((Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
            * (Work.Spaces.mixed (b - b₁) (a - a₁) f z θ) ^ 2
          + (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
            * (Work.Spaces.mixed b a f z θ) ^ 2) := by
      have h1 := mul_le_mul_of_nonneg_left hgm hWnn
      have h2 : (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
            * ((1 / 2) * ((Work.Spaces.mixed (b - b₁) (a - a₁) f z θ) ^ 2
              + (Work.Spaces.mixed b a f z θ) ^ 2))
          = (1 / 2) * ((Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
              * (Work.Spaces.mixed (b - b₁) (a - a₁) f z θ) ^ 2
            + (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
              * (Work.Spaces.mixed b a f z θ) ^ 2) := by ring
      linarith
    exact hkey.trans (mul_le_mul_of_nonneg_left hgm2 (mul_nonneg hCmpos.le hK4))
  have hMint : MeasureTheory.Integrable (fun p : ℝ × ℝ => Cm * K4 * ((1 / 2) *
      ((Work.Spaces.w p.1) ^ 2 * (Real.sin (2 * p.2)) ^ (-(Work.Spaces.gam α))
          * (Work.Spaces.mixed (b - b₁) (a - a₁) f p.1 p.2) ^ 2
        + (Work.Spaces.w p.1) ^ 2 * (Real.sin (2 * p.2)) ^ (-(Work.Spaces.gam α))
          * (Work.Spaces.mixed b a f p.1 p.2) ^ 2))) PM :=
    ((hYint'.add hZint').const_mul (1 / 2)).const_mul (Cm * K4)
  have hval : (∫ p, Cm * K4 * ((1 / 2) *
      ((Work.Spaces.w p.1) ^ 2 * (Real.sin (2 * p.2)) ^ (-(Work.Spaces.gam α))
          * (Work.Spaces.mixed (b - b₁) (a - a₁) f p.1 p.2) ^ 2
        + (Work.Spaces.w p.1) ^ 2 * (Real.sin (2 * p.2)) ^ (-(Work.Spaces.gam α))
          * (Work.Spaces.mixed b a f p.1 p.2) ^ 2)) ∂PM)
      ≤ Cm * K4 * (1 + Work.Spaces.HkSq α 6 f) := by
    rw [MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul,
      MeasureTheory.integral_add hYint' hZint']
    have hCK : 0 ≤ Cm * K4 := mul_nonneg hCmpos.le hK4
    nlinarith [hYval, hZval, hCK, hH]
  have hmain := abs_integral_le_of_pointwise hMint hFaesm hpt
  have hbnd : |∫ p, F p ∂PM| ≤ Cm * K4 * (1 + Work.Spaces.HkSq α 6 f) := hmain.trans hval
  refine ⟨?_, ?_⟩
  · rw [hFdef]
    exact MeasureTheory.Integrable.mono' hMint hFaesm (by
      filter_upwards [hpt] with p hp
      rwa [hFdef] at hp)
  · calc |∫ p, F p ∂PM|
        ≤ Cm * K4 * (1 + Work.Spaces.HkSq α 6 f) := hbnd
      _ ≤ Cm * (α ^ (-(3 : ℝ)) * ((1 + K0 + K4) * (1 + Work.Spaces.HkSq α 6 f))) := by
          rw [show Cm * K4 * (1 + Work.Spaces.HkSq α 6 f)
              = Cm * (K4 * (1 + Work.Spaces.HkSq α 6 f)) from by ring]
          refine mul_le_mul_of_nonneg_left ?_ (le_of_lt hCmpos)
          have h5 : 0 ≤ 1 + Work.Spaces.HkSq α 6 f := by linarith
          calc K4 * (1 + Work.Spaces.HkSq α 6 f)
              ≤ (1 + K4) * (1 + Work.Spaces.HkSq α 6 f) :=
                mul_le_mul_of_nonneg_right (by linarith) h5
            _ ≤ (1 + K0 + K4) * (1 + Work.Spaces.HkSq α 6 f) :=
                mul_le_mul_of_nonneg_right (by linarith) h5
            _ ≤ α ^ (-(3 : ℝ)) * ((1 + K0 + K4) * (1 + Work.Spaces.HkSq α 6 f)) :=
                le_mul_of_one_le_left (mul_nonneg (by linarith) h5) hα3
      _ = Cm * α ^ (-(3 : ℝ)) * ((1 + K0 + K4) * (1 + Work.Spaces.HkSq α 6 f)) := by ring

end

end Work.FTS.StrongPersist.H6Pair6Aux.T6CoefAux
