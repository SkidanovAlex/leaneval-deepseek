/-
Copyright: work module for the Elgindi finite-time singularity project.

# `TransportS/T2Sup/Ptwise`: the pointwise majorants of a Leibniz summand

The per-term estimates of `TransportS/T2Sup/Main.lean` (`termBoundF`, `termBoundG`,
`termBoundSigma`) each contain an internal *pointwise* domination of the integrand by
`HkIntegrand α 4 g` (for the "sup on the coefficient" and "σ-gain" cases) or by
`√(HkIntegrand α 4 f) · √(HkIntegrand α 4 g)` (for the "sup on a `g`-slot" case).  The
assembly of the per-slot transport bound `T2Slot` needs exactly these pointwise dominations
(as separate lemmas), because the splitting of the Leibniz sum into its summands is done at
the level of the *integrand*: the summands not carrying the delicate order-`3` factor of `f`
are dominated pointwise by an explicitly integrable majorant, which makes them
`θ`-integrable and their marginals integrable.

All declarations here rest on `[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS.TransportS.T2Sup.Main

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.TransportS.T2Sup

set_option autoImplicit false

open Work.FTS.TransportS.SlotT2

/-- `η ≤ γ`. -/
theorem eta_le_gam {α : ℝ} (hα : 0 < α) : Work.Spaces.eta ≤ Work.Spaces.gam α := by
  rw [Work.Spaces.gam]; linarith [hα, Work.Spaces.eta_lt_one]

/-! ## The three pointwise majorants -/

/-- **The "sup on the coefficient" pointwise majorant.**  If `|X| ≤ KF` on the open quadrant
and `G`, `Y` are canonical `q`-slots of `g`, then `canonW q |X| |G| |Y| ≤ KF · HkIntegrand g`. -/
theorem canonW_mul_abs_le_slotW {α q KF : ℝ} {X G Y g : ℝ → ℝ → ℝ}
    (hS2 : SlotWo α q G g) (hS3 : SlotWo α q Y g) (hKF : 0 ≤ KF)
    (hXb : ∀ z θ, 0 < z → 0 < θ → θ < π / 2 → |X z θ| ≤ KF) :
    ∀ z θ, 0 < z → 0 < θ → θ < π / 2 →
      canonW q z θ * |X z θ| * |G z θ| * |Y z θ|
        ≤ KF * Work.Spaces.HkIntegrand α 4 g z θ := by
  intro z θ hz hθ hθ2
  have hθI : θ ∈ Work.Spaces.Iθ := ⟨le_of_lt hθ, le_of_lt hθ2⟩
  have hGsq : canonW q z θ * (G z θ) ^ 2 ≤ Work.Spaces.HkIntegrand α 4 g z θ :=
    hS2 z θ hz hθ hθ2
  have hYsq : canonW q z θ * (Y z θ) ^ 2 ≤ Work.Spaces.HkIntegrand α 4 g z θ :=
    hS3 z θ hz hθ hθ2
  have hHnn : 0 ≤ Work.Spaces.HkIntegrand α 4 g z θ :=
    Work.Spaces.HkIntegrand_nonneg α 4 g z θ
  have hGY : canonW q z θ * |G z θ| * |Y z θ| ≤ Work.Spaces.HkIntegrand α 4 g z θ := by
    rw [canonW_mul_abs_eq (q := q) (G := G) (Y := Y) hθI]
    calc Real.sqrt (canonW q z θ * (G z θ) ^ 2)
          * Real.sqrt (canonW q z θ * (Y z θ) ^ 2)
        ≤ Real.sqrt (Work.Spaces.HkIntegrand α 4 g z θ)
          * Real.sqrt (Work.Spaces.HkIntegrand α 4 g z θ) :=
          mul_le_mul (Real.sqrt_le_sqrt hGsq) (Real.sqrt_le_sqrt hYsq)
            (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
      _ = Work.Spaces.HkIntegrand α 4 g z θ := Real.mul_self_sqrt hHnn
  calc canonW q z θ * |X z θ| * |G z θ| * |Y z θ|
      = |X z θ| * (canonW q z θ * |G z θ| * |Y z θ|) := by ring
    _ ≤ KF * Work.Spaces.HkIntegrand α 4 g z θ :=
        mul_le_mul (hXb z θ hz hθ hθ2) hGY
          (mul_nonneg (mul_nonneg (canonW_nonneg hθI) (abs_nonneg _)) (abs_nonneg _)) hKF

/-- **The σ-gain pointwise majorant.**  If `|X| ≤ CK · sin(2θ)` on the open quadrant with
`CK ≥ 0`, `q ≤ 1 + η`, and `G`, `Y` are canonical `η`- resp. `γ`-slots of `g`, then
`canonW q |X| |G| |Y| ≤ CK · HkIntegrand g`. -/
theorem canonW_mul_abs_le_slotSigma {α q CK : ℝ} {X G Y g : ℝ → ℝ → ℝ}
    (hα : 0 < α)
    (hCK : 0 ≤ CK) (hXb : ∀ z θ, 0 < z → 0 < θ → θ < π / 2 →
      |X z θ| ≤ CK * Real.sin (2 * θ))
    (hq : q ≤ 1 + Work.Spaces.eta)
    (hS2 : SlotWo α Work.Spaces.eta G g) (hS3 : SlotWo α (Work.Spaces.gam α) Y g) :
    ∀ z θ, 0 < z → 0 < θ → θ < π / 2 →
      canonW q z θ * |X z θ| * |G z θ| * |Y z θ|
        ≤ CK * Work.Spaces.HkIntegrand α 4 g z θ := by
  intro z θ hz hθ hθ2
  have hθI : θ ∈ Work.Spaces.Iθ := ⟨le_of_lt hθ, le_of_lt hθ2⟩
  have hσ0 : 0 < Real.sin (2 * θ) := sin_two_pos_of_Ioo ⟨hθ, hθ2⟩
  have hσ1 : Real.sin (2 * θ) ≤ 1 := sin_two_le_one θ
  have hw : 0 ≤ (Work.Spaces.w z) ^ 2 := sq_nonneg _
  have hGnn : 0 ≤ canonW q z θ * |G z θ| * |Y z θ| :=
    mul_nonneg (mul_nonneg (canonW_nonneg hθI) (abs_nonneg _)) (abs_nonneg _)
  have hGsq : canonW Work.Spaces.eta z θ * (G z θ) ^ 2
      ≤ Work.Spaces.HkIntegrand α 4 g z θ := hS2 z θ hz hθ hθ2
  have hYsq : canonW (Work.Spaces.gam α) z θ * (Y z θ) ^ 2
      ≤ Work.Spaces.HkIntegrand α 4 g z θ := hS3 z θ hz hθ hθ2
  have hsplit : Real.sin (2 * θ) * Real.sin (2 * θ) ^ (-q)
      = Real.sin (2 * θ) ^ (1 - q) := by
    rw [show (1:ℝ) - q = 1 + (-q) by ring, Real.rpow_add hσ0, Real.rpow_one]
  have hmix : Real.sin (2 * θ) ^ (1 - q) ≤ Real.sin (2 * θ) ^ (-Work.Spaces.eta) :=
    rpow_one_sub_le hσ0 hσ1 hq
  have hGY : Real.sin (2 * θ) * (canonW q z θ * |G z θ| * |Y z θ|)
      ≤ Work.Spaces.HkIntegrand α 4 g z θ := by
    have h1 : Real.sin (2 * θ) * canonW q z θ
        = (Work.Spaces.w z) ^ 2 * Real.sin (2 * θ) ^ (1 - q) := by
      rw [canonW]
      rw [show Real.sin (2 * θ) * ((Work.Spaces.w z) ^ 2 * Real.sin (2 * θ) ^ (-q))
          = (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ) * Real.sin (2 * θ) ^ (-q)) from by
        ring]
      rw [hsplit]
    have h3 : (Work.Spaces.w z) ^ 2 * Real.sin (2 * θ) ^ (1 - q)
        ≤ (Work.Spaces.w z) ^ 2 * Real.sin (2 * θ) ^ (-Work.Spaces.eta) :=
      mul_le_mul_of_nonneg_left hmix hw
    have hstep1 : Real.sin (2 * θ) * (canonW q z θ * |G z θ| * |Y z θ|)
        ≤ (Work.Spaces.w z) ^ 2 * Real.sin (2 * θ) ^ (-Work.Spaces.eta)
            * (|G z θ| * |Y z θ|) := by
      rw [show Real.sin (2 * θ) * (canonW q z θ * |G z θ| * |Y z θ|)
          = (Real.sin (2 * θ) * canonW q z θ) * (|G z θ| * |Y z θ|) from by ring, h1]
      exact mul_le_mul_of_nonneg_right h3 (mul_nonneg (abs_nonneg _) (abs_nonneg _))
    have hGYabs : |G z θ| * |Y z θ| ≤ (G z θ ^ 2 + Y z θ ^ 2) / 2 := by
      have h := Work.FTS.TransportS.T3BadAux.abs_mul_le_half_sq_add (G z θ) (Y z θ)
      rwa [abs_mul] at h
    have hstep2 : (Work.Spaces.w z) ^ 2 * Real.sin (2 * θ) ^ (-Work.Spaces.eta)
          * (|G z θ| * |Y z θ|)
        ≤ (1 / 2) * ((canonW Work.Spaces.eta z θ * (G z θ) ^ 2)
            + (canonW Work.Spaces.eta z θ * (Y z θ) ^ 2)) := by
      show (Work.Spaces.w z) ^ 2 * Real.sin (2 * θ) ^ (-Work.Spaces.eta)
          * (|G z θ| * |Y z θ|)
        ≤ (1 / 2) * ((Work.Spaces.w z) ^ 2 * Real.sin (2 * θ) ^ (-Work.Spaces.eta)
              * (G z θ) ^ 2
            + (Work.Spaces.w z) ^ 2 * Real.sin (2 * θ) ^ (-Work.Spaces.eta)
              * (Y z θ) ^ 2)
      refine le_trans (mul_le_mul_of_nonneg_left hGYabs
        (mul_nonneg hw (Real.rpow_nonneg hσ0.le _))) ?_
      rw [show (Work.Spaces.w z) ^ 2 * Real.sin (2 * θ) ^ (-Work.Spaces.eta)
            * ((G z θ ^ 2 + Y z θ ^ 2) / 2)
          = (1 / 2) * ((Work.Spaces.w z) ^ 2 * Real.sin (2 * θ) ^ (-Work.Spaces.eta)
              * (G z θ) ^ 2
            + (Work.Spaces.w z) ^ 2 * Real.sin (2 * θ) ^ (-Work.Spaces.eta)
              * (Y z θ) ^ 2) from by ring]
    have h3' : canonW Work.Spaces.eta z θ * (Y z θ) ^ 2
        ≤ canonW (Work.Spaces.gam α) z θ * (Y z θ) ^ 2 := by
      have hle : Real.sin (2 * θ) ^ (-Work.Spaces.eta)
          ≤ Real.sin (2 * θ) ^ (-Work.Spaces.gam α) :=
        rpow_neg_le_neg hσ0 hσ1 (eta_le_gam hα)
      rw [canonW, canonW]
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hle hw) (sq_nonneg _)
    exact le_trans (le_trans hstep1 hstep2) (by linarith [hGsq, le_trans h3' hYsq])
  calc canonW q z θ * |X z θ| * |G z θ| * |Y z θ|
      = |X z θ| * (canonW q z θ * |G z θ| * |Y z θ|) := by ring
    _ ≤ (CK * Real.sin (2 * θ)) * (canonW q z θ * |G z θ| * |Y z θ|) :=
        mul_le_mul_of_nonneg_right (hXb z θ hz hθ hθ2) hGnn
    _ = CK * (Real.sin (2 * θ) * (canonW q z θ * |G z θ| * |Y z θ|)) := by ring
    _ ≤ CK * Work.Spaces.HkIntegrand α 4 g z θ := mul_le_mul_of_nonneg_left hGY hCK

/-- **The "sup on a `g`-slot" pointwise majorant.**  If the middle factor is bounded by `KG`
and `F`, `Y` are canonical `q`-slots of `f` resp. `g`, then
`canonW q |F| |G| |Y| ≤ KG · √(HkIntegrand f) · √(HkIntegrand g)`. -/
theorem canonW_mul_abs_le_slotG {α q KG : ℝ} {F Gm Y f g : ℝ → ℝ → ℝ}
    (hS1 : SlotWo α q F f) (hS3 : SlotWo α q Y g) (hKG : 0 ≤ KG)
    (hGb : ∀ z θ, 0 < z → 0 < θ → θ < π / 2 → |Gm z θ| ≤ KG) :
    ∀ z θ, 0 < z → 0 < θ → θ < π / 2 →
      canonW q z θ * |F z θ| * |Gm z θ| * |Y z θ|
        ≤ KG * (Real.sqrt (Work.Spaces.HkIntegrand α 4 f z θ)
            * Real.sqrt (Work.Spaces.HkIntegrand α 4 g z θ)) := by
  intro z θ hz hθ hθ2
  have hθI : θ ∈ Work.Spaces.Iθ := ⟨le_of_lt hθ, le_of_lt hθ2⟩
  have hFsq : canonW q z θ * (F z θ) ^ 2 ≤ Work.Spaces.HkIntegrand α 4 f z θ :=
    hS1 z θ hz hθ hθ2
  have hYsq : canonW q z θ * (Y z θ) ^ 2 ≤ Work.Spaces.HkIntegrand α 4 g z θ :=
    hS3 z θ hz hθ hθ2
  have hFY : canonW q z θ * |F z θ| * |Y z θ|
      ≤ Real.sqrt (Work.Spaces.HkIntegrand α 4 f z θ)
        * Real.sqrt (Work.Spaces.HkIntegrand α 4 g z θ) := by
    rw [canonW_mul_abs_eq (q := q) (G := F) (Y := Y) hθI]
    exact mul_le_mul (Real.sqrt_le_sqrt hFsq) (Real.sqrt_le_sqrt hYsq)
      (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  calc canonW q z θ * |F z θ| * |Gm z θ| * |Y z θ|
      = (canonW q z θ * |F z θ| * |Y z θ|) * |Gm z θ| := by ring
    _ ≤ (Real.sqrt (Work.Spaces.HkIntegrand α 4 f z θ)
          * Real.sqrt (Work.Spaces.HkIntegrand α 4 g z θ)) * KG :=
        mul_le_mul hFY (hGb z θ hz hθ hθ2) (abs_nonneg _)
          (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
    _ = KG * (Real.sqrt (Work.Spaces.HkIntegrand α 4 f z θ)
          * Real.sqrt (Work.Spaces.HkIntegrand α 4 g z θ)) := by ring

end Work.FTS.TransportS.T2Sup
