/-
Copyright: work module for the Elgindi finite-time singularity project.

# `FlatP/Basic`: the shared elementary pieces of the "flat-price" star row `rowStarP`

This module contains the small, reusable facts that the flat-price row
`Work.FTS.StrongPersist.H6Rows.Npair6BWork.rowStarP` is assembled from:

* `smoothOpen_mul` — the product of two `SmoothOpen` fields is `SmoothOpen`;
* `Wt_sq_eq` — `(Wt α z θ)² = w z² · sin(2θ)^{-γ}` (the public version of the identity
  that `H6Pair6Aux/intSlotLeHkSq` keeps private);
* the radial integral `∫_{Iz} (1+z)^{-2} = 1` (and its integrability), which is the
  `z`-half of every "min-split" estimate: with `p = z/(1+z)` and `q = z/(1+z)²` one has
  the pointwise identity `w z² · p² q² = (1+z)^{-2}` away from `z = 0`;
* `fSlot_le_HkIntegrand` — for a leaf weight `ρ` of the slot `a` and any `a + b ≤ 6`,
  `ρ z θ · (D_z^b D_θ^a f z θ)² ≤ HkIntegrand α 6 f z θ` on the open quadrant.  This is
  the pointwise domination that turns "the datum slot is priced by `HkSq α 6 f`" into an
  honest `L²` statement.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Submission.Work.Spaces.Defs
import Submission.Work.Spaces.HkSq_terms
import Submission.Work.Spaces.sq_mul_div_rpow
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.TransportS.Slots
import Submission.Work.FTS.TransportS.SlotT2.Basic
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6BWork.rowAux

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.H6Rows.Npair6BWork.FlatP

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option linter.unusedVariables false

/-! ## §1. Products of `SmoothOpen` fields -/

theorem smoothOpen_mul {A Q : ℝ → ℝ → ℝ} (hA : Work.FTS.EllipticEst.SmoothOpen A)
    (hQ : Work.FTS.EllipticEst.SmoothOpen Q) :
    Work.FTS.EllipticEst.SmoothOpen (fun z θ => A z θ * Q z θ) := by
  rw [Work.FTS.EllipticEst.smoothOpen_iff_forall] at hA hQ ⊢
  intro n
  exact (hA n).mul (hQ n)

/-! ## §2. The weight identity `(Wt α z θ)² = w z² sin(2θ)^{-γ}` -/

theorem Wt_sq_eq (α z θ : ℝ) (hs : 0 ≤ Real.sin (2 * θ)) :
    (Work.Spaces.Wt α z θ) ^ 2
      = (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) := by
  rw [Work.Spaces.Wt, Work.Spaces.wTheta, mul_pow]
  rw [show ((Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α / 2))) ^ 2
        = ((Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α / 2))) ^ ((2 : ℝ)) from
      (Real.rpow_natCast ((Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α / 2))) 2).symm]
  rw [← Real.rpow_mul hs]
  rw [show (-(Work.Spaces.gam α / 2)) * (2 : ℝ) = -(Work.Spaces.gam α) by ring]

/-- The canonical slot weight is a product of a `z`-weight and a `θ`-weight. -/
theorem canonW_eq (q z θ : ℝ) :
    Work.FTS.TransportS.SlotT2.canonW q z θ
      = (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-q) := rfl

/-! ## §3. The radial integral `∫_{Iz} (1+z)^{-2} = 1` -/

/-- `z ↦ -(1+z)⁻¹` has derivative `((1+z)²)⁻¹` on `z ≥ 0`. -/
theorem hasDerivAt_neg_inv_one_add (x : ℝ) (hx : 0 ≤ x) :
    HasDerivAt (fun z : ℝ => -((1 + z)⁻¹)) (((1 + x) ^ 2)⁻¹) x := by
  have h1 : HasDerivAt (fun z : ℝ => 1 + z) 1 x := by
    simpa using (hasDerivAt_id x).const_add 1
  have hx0 : (1 + x) ≠ 0 := by positivity
  have h2 := (h1.inv hx0).neg
  have hval : -(-1 / (1 + x) ^ 2) = ((1 + x) ^ 2)⁻¹ := by
    rw [div_eq_mul_inv, neg_mul, neg_neg, one_mul]
  rwa [hval] at h2

/-- `-(1+z)⁻¹ → 0` as `z → ∞`. -/
theorem tendsto_neg_inv_one_add :
    Tendsto (fun z : ℝ => -((1 + z)⁻¹)) atTop (𝓝 0) := by
  have h : Tendsto (fun z : ℝ => (1 + z)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp
      (Filter.tendsto_atTop_add_const_left atTop (1 : ℝ) Filter.tendsto_id)
  simpa using h.neg

/-- The radial integral `∫_{Iz} (1+z)⁻² dz = 1`. -/
theorem integral_inv_sq_Iz :
    ∫ z in Work.Spaces.Iz, ((1 + z) ^ 2)⁻¹ = 1 := by
  have hmain := MeasureTheory.integral_Ioi_of_hasDerivAt_of_nonneg'
    (a := (0 : ℝ)) (l := (0 : ℝ))
    (g := fun z : ℝ => -((1 + z)⁻¹)) (g' := fun z : ℝ => ((1 + z) ^ 2)⁻¹)
    (fun x hx => hasDerivAt_neg_inv_one_add x hx) (fun x _ => by positivity)
    tendsto_neg_inv_one_add
  rw [Work.Spaces.Iz, MeasureTheory.integral_Ici_eq_integral_Ioi, hmain]
  norm_num

/-- `z ↦ (1+z)⁻²` is integrable on `Iz`. -/
theorem integrableOn_inv_sq_Iz :
    IntegrableOn (fun z : ℝ => ((1 + z) ^ 2)⁻¹) Work.Spaces.Iz := by
  have h' : IntegrableOn (fun z : ℝ => ((1 + z) ^ 2)⁻¹) (Set.Ioi (0 : ℝ)) :=
    MeasureTheory.integrableOn_Ioi_deriv_of_nonneg'
      (a := (0 : ℝ)) (l := (0 : ℝ))
      (g := fun z : ℝ => -((1 + z)⁻¹)) (g' := fun z : ℝ => ((1 + z) ^ 2)⁻¹)
      (fun x hx => hasDerivAt_neg_inv_one_add x hx) (fun x _ => by positivity)
      tendsto_neg_inv_one_add
  have h'' : IntegrableOn (fun z : ℝ => ((1 + z) ^ 2)⁻¹) (Set.Ici (0 : ℝ)) := by
    rw [MeasureTheory.IntegrableOn,
      ← MeasureTheory.Measure.restrict_congr_set
        (MeasureTheory.Ioi_ae_eq_Ici (μ := volume) (a := (0 : ℝ)))]
    exact h'
  rwa [Work.Spaces.Iz]

/-! ## §4. The datum slot against `HkIntegrand` -/

/-- **The datum-slot domination.**  A leaf weight `ρ` of the slot `a` times the square of
the slot `D_z^b D_θ^a f` is pointwise dominated by `HkIntegrand α 6 f`, for `a + b ≤ 6`. -/
theorem fSlot_le_HkIntegrand {α : ℝ} (hα0 : 0 < α) {f : ℝ → ℝ → ℝ} {a b : ℕ}
    (hab : a + b ≤ 6) {ρ : ℝ → ℝ → ℝ} (hleaf : Work.FTS.TransportS.IsLeafW α a ρ)
    {z θ : ℝ} (hz : 0 < z) (hθ0 : 0 < θ) (hθ1 : θ < Real.pi / 2) :
    ρ z θ * (Work.Spaces.mixed b a f z θ) ^ 2 ≤ Work.Spaces.HkIntegrand α 6 f z θ := by
  have hσ : 0 ≤ Real.sin (2 * θ) :=
    Real.sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith [Real.pi_pos])
  rcases Nat.eq_zero_or_pos a with ha | ha
  · subst ha
    have hρ := Work.FTS.StrongPersist.H6Rows.Npair6BWork.leafW_le_canonW_eta hleaf z θ hz hθ0 hθ1
    have hρ' : ρ z θ ≤ (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) := by
      simpa only [Work.FTS.StrongPersist.H6Rows.Npair6BWork.leafEta_eq_canonW, canonW_eq]
        using hρ
    have hstep : ρ z θ * (Work.Spaces.mixed b 0 f z θ) ^ 2
        ≤ (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
            * (Work.Spaces.mixed b 0 f z θ) ^ 2 :=
      mul_le_mul_of_nonneg_right hρ' (sq_nonneg _)
    have hfinal : (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
          * (Work.Spaces.mixed b 0 f z θ) ^ 2
        ≤ Work.Spaces.HkIntegrand α 6 f z θ := by
      rw [Work.Spaces.mixed_zero_right]
      have hid : (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
            * (Work.Spaces.DzIter b f z θ) ^ 2
          = (Work.Spaces.DzIter b f z θ
              * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 := by
        rw [Work.Spaces.sq_mul_div_rpow (Work.Spaces.DzIter b f z θ) (Work.Spaces.w z)
          (Real.sin (2 * θ)) Work.Spaces.eta hσ (by norm_num [Work.Spaces.eta])]
        ring
      rw [hid]
      exact Work.Spaces.sq_le_HkIntegrand_z α 6 f z θ b (by omega)
    exact le_trans hstep hfinal
  · have hρ := Work.FTS.StrongPersist.H6Rows.Npair6BWork.leafW_le_canonW_gam hα0 hleaf z θ hz hθ0 hθ1
    have hρ' : ρ z θ
        ≤ (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) := by
      simpa only [Work.FTS.StrongPersist.H6Rows.Npair6BWork.leafGam_eq_canonW, canonW_eq]
        using hρ
    have hstep : ρ z θ * (Work.Spaces.mixed b a f z θ) ^ 2
        ≤ (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
            * (Work.Spaces.mixed b a f z θ) ^ 2 :=
      mul_le_mul_of_nonneg_right hρ' (sq_nonneg _)
    have hfinal : (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
          * (Work.Spaces.mixed b a f z θ) ^ 2 ≤ Work.Spaces.HkIntegrand α 6 f z θ := by
      have hid : (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
            * (Work.Spaces.mixed b a f z θ) ^ 2
          = (Work.Spaces.mixed b a f z θ * Work.Spaces.Wt α z θ) ^ 2 := by
        rw [mul_pow, Wt_sq_eq α z θ hσ]
        ring
      rw [hid]
      exact Work.Spaces.sq_le_HkIntegrand_mixed α 6 f z θ a b (by omega) (by omega)
    exact le_trans hstep hfinal

end Work.FTS.StrongPersist.H6Rows.Npair6BWork.FlatP
