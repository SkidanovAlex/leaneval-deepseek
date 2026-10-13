import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.Spaces.HkSq_terms
import Submission.Work.FTS.H2.HkIntegrandSlotSum
import Submission.Work.FTS.H2.HQ.Glue
import Submission.Work.FTS.H2.HQ.HardyThetaQ
import Submission.Work.FTS.H2.T1HardSlice
import Submission.Work.FTS.LocData.SmoothChain

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end


noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.H2.T1Q

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-!
# `Work.H2.T1Q.SlotBoundQ` — the five top-order slots of the `ℋ⁴`-integrand at a fixed `z`

For `g` of class `SmoothQuad` with `HkMem α 4 g` and `z > 0`, the five top-order summands of the
`ℋ⁴`-integrand of `g` — the pure slot `(D_z⁴g)² sin(2θ)^{-η}` and the four mixed slots
`(D_z^jD_θ^ig)² sin(2θ)^{-γ}` with `i + j = 4`, `i ≥ 1` — are:

* integrable in `θ` on `Iθ` (the `η`-slot and each of the ten mixed slots with `1 ≤ i`,
  `i + j ≤ 4`), and
* their `w(z)²`-weighted `θ`-integral is bounded by `∫_θ HkIntegrand α 4 g z θ`.

The integrability comes from the summands of the (integrable) `ℋ⁴`-integrand
(`sq_le_HkIntegrand_z`, `sq_le_HkIntegrand_mixed`); the inequality is the pointwise comparison
`HkIntegrandSlotSum` together with the two squaring identities `slotQ_whz_sq` and `slotQ_wt_sq`
for the weights `w/sin(2θ)^{η/2}` and `W = w·sin(2θ)^{-γ/2}`.  No positivity hypothesis on `α` is
needed: both squaring identities are pure `rpow` algebra on the nonnegative base `sin(2θ)`.
-/

/-! ## Squaring the two weights of `HkIntegrand` -/

/-- `(a^p)^2 = a^(p*2)` for a nonnegative base (the `rpow` form of `mul_pow` for a real
exponent). -/
theorem slotQ_rpow_sq_two {a : ℝ} (ha : 0 ≤ a) (p : ℝ) : (a ^ p) ^ 2 = a ^ (p * 2) := by
  rw [← Real.rpow_natCast (a ^ p) 2]
  exact (Real.rpow_mul ha p 2).symm

/-- Squaring the weight `w(z)/sin(2θ)^{η/2}` of the pure `D_z`-slots. -/
theorem slotQ_whz_sq (z : ℝ) {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)) ^ 2
      = (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-Work.Spaces.eta) := by
  have ha : 0 ≤ Real.sin (2 * θ) := Work.Spaces.sin_two_nonneg_of_Iθ hθ
  rw [div_eq_mul_inv, ← Real.rpow_neg ha (Work.Spaces.eta / 2), mul_pow,
    slotQ_rpow_sq_two ha (-(Work.Spaces.eta / 2)),
    show (-(Work.Spaces.eta / 2)) * 2 = -Work.Spaces.eta by ring]

/-- Squaring the mixed weight `W = Wt α = w·sin(2θ)^{-γ/2}`. -/
theorem slotQ_wt_sq (α z : ℝ) {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    (Work.Spaces.Wt α z θ) ^ 2
      = (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) := by
  have ha : 0 ≤ Real.sin (2 * θ) := Work.Spaces.sin_two_nonneg_of_Iθ hθ
  have hW : Work.Spaces.Wt α z θ
      = Work.Spaces.w z * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α / 2)) := rfl
  rw [hW, mul_pow, slotQ_rpow_sq_two ha (-(Work.Spaces.gam α / 2)),
    show (-(Work.Spaces.gam α / 2)) * 2 = -(Work.Spaces.gam α) by ring]

/-! ## The pointwise slot inequality -/

/-- **The five top-order slots are dominated by the `ℋ⁴`-integrand.**  On `Iθ` the
`w(z)²`-multiple of the sum of the squares of the five top-order derivatives of `g` — with the
angular weights pulled out — is at most `HkIntegrand α 4 g z θ`. -/
theorem slotQ_le_HkIntegrand (α : ℝ) (g : ℝ → ℝ → ℝ) (z : ℝ) {θ : ℝ}
    (hθ : θ ∈ Work.Spaces.Iθ) :
    (Work.Spaces.w z) ^ 2 * ((Work.Spaces.DzIter 4 g z θ) ^ 2
          * (Real.sin (2 * θ)) ^ (-Work.Spaces.eta)
        + ((Work.Spaces.mixed 3 1 g z θ) ^ 2 + (Work.Spaces.mixed 2 2 g z θ) ^ 2
          + (Work.Spaces.mixed 1 3 g z θ) ^ 2 + (Work.Spaces.mixed 0 4 g z θ) ^ 2)
          * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)))
      ≤ Work.Spaces.HkIntegrand α 4 g z θ := by
  have h := Work.FTS.H2.HkIntegrandSlotSum α g z θ
  have hWhz := slotQ_whz_sq z hθ
  have hWt := slotQ_wt_sq α z hθ
  have key : (Work.Spaces.DzIter 4 g z θ
        * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
      + (Work.Spaces.mixed 3 1 g z θ * Work.Spaces.Wt α z θ) ^ 2
      + (Work.Spaces.mixed 2 2 g z θ * Work.Spaces.Wt α z θ) ^ 2
      + (Work.Spaces.mixed 1 3 g z θ * Work.Spaces.Wt α z θ) ^ 2
      + (Work.Spaces.mixed 0 4 g z θ * Work.Spaces.Wt α z θ) ^ 2
      = (Work.Spaces.w z) ^ 2 * ((Work.Spaces.DzIter 4 g z θ) ^ 2
            * (Real.sin (2 * θ)) ^ (-Work.Spaces.eta)
          + ((Work.Spaces.mixed 3 1 g z θ) ^ 2 + (Work.Spaces.mixed 2 2 g z θ) ^ 2
            + (Work.Spaces.mixed 1 3 g z θ) ^ 2 + (Work.Spaces.mixed 0 4 g z θ) ^ 2)
            * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))) := by
    simp only [mul_pow, hWhz, hWt]
    ring
  linarith [h, key]

/-! ## Continuity and almost-everywhere strong measurability of the pure slot -/

/-- The radial weight `p ↦ w(p.1)` is continuous on the open quadrant. -/
theorem slotQ_continuousOn_w_Qd : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.w p.1)
    Work.FTS.H2.HQ.quadQ := by
  have hfun : (fun p : ℝ × ℝ => Work.Spaces.w p.1)
      = fun p : ℝ × ℝ => (1 + p.1) ^ 2 / p.1 ^ 2 := by funext p; rfl
  rw [hfun]
  exact ContinuousOn.div ((continuousOn_const.add continuousOn_fst).pow 2)
    (continuousOn_fst.pow 2) (fun p hp => pow_ne_zero 2 (ne_of_gt hp.1))

/-- `(sin (2·))^c` is continuous on the open quadrant. -/
theorem slotQ_continuousOn_sin_rpow (c : ℝ) :
    ContinuousOn (fun p : ℝ × ℝ => (Real.sin (2 * p.2)) ^ c) Work.FTS.H2.HQ.quadQ :=
  ((Real.continuous_sin.comp (continuous_const.mul continuous_snd)).continuousOn).rpow_const
    (fun p hp => Or.inl (ne_of_gt (Work.FTS.H2.HQ.hq_sin_two_pos_of_mem_Ioo hp.2)))

/-- The weight `p ↦ w(p.1)/sin(2p.2)^{η/2}` is continuous on the open quadrant. -/
theorem slotQ_continuousOn_whz_Qd : ContinuousOn (fun p : ℝ × ℝ =>
    Work.Spaces.w p.1 / (Real.sin (2 * p.2)) ^ (Work.Spaces.eta / 2)) Work.FTS.H2.HQ.quadQ :=
  slotQ_continuousOn_w_Qd.div (slotQ_continuousOn_sin_rpow (Work.Spaces.eta / 2))
    (fun _ hp => ne_of_gt (Real.rpow_pos_of_pos (Work.FTS.H2.HQ.hq_sin_two_pos_of_mem_Ioo hp.2) _))

/-- The `θ`-slice of the squared weighted pure `D_z`-slot is a.e. strongly measurable on `Iθ`,
by continuity on the open quadrant and the nullity of the two endpoints. -/
theorem slotQ_aesm_slice_dzIter_whz (g : ℝ → ℝ → ℝ) (hG : Work.FTS.LocData.SmoothQuad g)
    (i : ℕ) {z : ℝ} (hz : 0 < z) :
    AEStronglyMeasurable (fun θ => (Work.Spaces.DzIter i g z θ
        * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
      (volume.restrict Work.Spaces.Iθ) := by
  refine Work.Spaces.aesm_slice_of_continuousOn_Qd
    (fun p : ℝ × ℝ => (Work.Spaces.DzIter i g p.1 p.2
      * (Work.Spaces.w p.1 / (Real.sin (2 * p.2)) ^ (Work.Spaces.eta / 2))) ^ 2) ?_ hz
  have hDz : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.DzIter i g p.1 p.2)
      Work.FTS.H2.HQ.quadQ :=
    ((Work.FTS.LocData.contDiffOn_DzIter Work.Spaces.isOpen_quadU hG i).continuousOn).mono
      Work.FTS.H2.HQ.quadQ_subset_quadU
  exact (hDz.mul slotQ_continuousOn_whz_Qd).pow 2

/-! ## The target -/

theorem SlotBoundQ (α : ℝ) (g : ℝ → ℝ → ℝ)
    (hsmg : Work.FTS.LocData.SmoothQuad g) (hmg : Work.Spaces.HkMem α 4 g)
    {z : ℝ} (hz : 0 < z) :
    MeasureTheory.IntegrableOn (fun θ => (Work.Spaces.DzIter 4 g z θ) ^ 2
          * (Real.sin (2 * θ)) ^ (-Work.Spaces.eta)) Work.Spaces.Iθ
      ∧ (∀ j i : ℕ, 1 ≤ i → i + j ≤ 4 → MeasureTheory.IntegrableOn
          (fun θ => (Work.Spaces.mixed j i g z θ) ^ 2
            * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))) Work.Spaces.Iθ)
      ∧ (Work.Spaces.w z) ^ 2 * (∫ θ in Work.Spaces.Iθ,
          ((Work.Spaces.DzIter 4 g z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-Work.Spaces.eta)
            + ((Work.Spaces.mixed 3 1 g z θ) ^ 2 + (Work.Spaces.mixed 2 2 g z θ) ^ 2
              + (Work.Spaces.mixed 1 3 g z θ) ^ 2 + (Work.Spaces.mixed 0 4 g z θ) ^ 2)
              * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))))
        ≤ ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 g z θ := by
  have hzI : z ∈ Work.Spaces.Iz := le_of_lt hz
  have hHk : MeasureTheory.IntegrableOn (fun θ => Work.Spaces.HkIntegrand α 4 g z θ)
      Work.Spaces.Iθ := hmg.1 z hzI
  have hwne : Work.Spaces.w z ≠ 0 := by
    rw [Work.Spaces.w]
    exact div_ne_zero (pow_ne_zero 2 (by linarith)) (pow_ne_zero 2 (ne_of_gt hz))
  have hw2ne : (Work.Spaces.w z) ^ 2 ≠ 0 := pow_ne_zero 2 hwne
  -- ## Integrability of the five weighted slot functions, extracted from `HkIntegrand`
  -- the pure `D_z`-slot
  have hZslot : MeasureTheory.IntegrableOn (fun θ => (Work.Spaces.DzIter 4 g z θ
      * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
      Work.Spaces.Iθ :=
    MeasureTheory.Integrable.mono' hHk (slotQ_aesm_slice_dzIter_whz g hsmg 4 hz)
      (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc (fun θ _ => by
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
        exact Work.Spaces.sq_le_HkIntegrand_z α 4 g z θ 4 le_rfl))
  have hDzInt : MeasureTheory.IntegrableOn (fun θ => (Work.Spaces.DzIter 4 g z θ) ^ 2
      * (Real.sin (2 * θ)) ^ (-Work.Spaces.eta)) Work.Spaces.Iθ := by
    have hA : MeasureTheory.IntegrableOn (fun θ => (Work.Spaces.w z) ^ 2
        * ((Work.Spaces.DzIter 4 g z θ) ^ 2
          * (Real.sin (2 * θ)) ^ (-Work.Spaces.eta))) Work.Spaces.Iθ :=
      hZslot.congr_fun (fun θ hθ => by
        show (Work.Spaces.DzIter 4 g z θ
            * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
          = (Work.Spaces.w z) ^ 2 * ((Work.Spaces.DzIter 4 g z θ) ^ 2
            * (Real.sin (2 * θ)) ^ (-Work.Spaces.eta))
        rw [mul_pow, slotQ_whz_sq z hθ]
        ring) measurableSet_Icc
    have hB : MeasureTheory.IntegrableOn (fun θ => ((Work.Spaces.w z) ^ 2)⁻¹
        * ((Work.Spaces.w z) ^ 2 * ((Work.Spaces.DzIter 4 g z θ) ^ 2
          * (Real.sin (2 * θ)) ^ (-Work.Spaces.eta)))) Work.Spaces.Iθ :=
      hA.const_mul _
    exact hB.congr_fun (fun θ _ => inv_mul_cancel_left₀ hw2ne _) measurableSet_Icc
  -- every mixed slot with `1 ≤ i`, `i + j ≤ 4`
  have hMint : ∀ j i : ℕ, 1 ≤ i → i + j ≤ 4 → MeasureTheory.IntegrableOn
      (fun θ => (Work.Spaces.mixed j i g z θ) ^ 2
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))) Work.Spaces.Iθ := by
    intro j i hi hij
    have h1 : MeasureTheory.IntegrableOn (fun θ => (Work.Spaces.mixed j i g z θ
        * Work.Spaces.Wt α z θ) ^ 2) Work.Spaces.Iθ :=
      MeasureTheory.Integrable.mono' hHk (Work.FTS.H2.HQ.aesm_slice_mixed_Wt_sq α g hsmg j i hz)
        (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc (fun θ _ => by
          rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
          exact Work.Spaces.sq_le_HkIntegrand_mixed α 4 g z θ i j hi hij))
    have hA : MeasureTheory.IntegrableOn (fun θ => (Work.Spaces.w z) ^ 2
        * ((Work.Spaces.mixed j i g z θ) ^ 2
          * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)))) Work.Spaces.Iθ :=
      h1.congr_fun (fun θ hθ => by
        show (Work.Spaces.mixed j i g z θ * Work.Spaces.Wt α z θ) ^ 2
          = (Work.Spaces.w z) ^ 2 * ((Work.Spaces.mixed j i g z θ) ^ 2
            * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)))
        rw [mul_pow, slotQ_wt_sq α z hθ]
        ring) measurableSet_Icc
    have hB : MeasureTheory.IntegrableOn (fun θ => ((Work.Spaces.w z) ^ 2)⁻¹
        * ((Work.Spaces.w z) ^ 2 * ((Work.Spaces.mixed j i g z θ) ^ 2
          * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))))) Work.Spaces.Iθ :=
      hA.const_mul _
    exact hB.congr_fun (fun θ _ => inv_mul_cancel_left₀ hw2ne _) measurableSet_Icc
  -- the block of the four top-order mixed slots
  have hBblk : MeasureTheory.IntegrableOn (fun θ =>
      ((Work.Spaces.mixed 3 1 g z θ) ^ 2 + (Work.Spaces.mixed 2 2 g z θ) ^ 2
        + (Work.Spaces.mixed 1 3 g z θ) ^ 2 + (Work.Spaces.mixed 0 4 g z θ) ^ 2)
      * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))) Work.Spaces.Iθ := by
    have h31 := hMint 3 1 (by norm_num) (by norm_num)
    have h22 := hMint 2 2 (by norm_num) (by norm_num)
    have h13 := hMint 1 3 (by norm_num) (by norm_num)
    have h04 := hMint 0 4 (by norm_num) (by norm_num)
    have hall : MeasureTheory.IntegrableOn (fun θ =>
        (Work.Spaces.mixed 3 1 g z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
        + (Work.Spaces.mixed 2 2 g z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
        + (Work.Spaces.mixed 1 3 g z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
        + (Work.Spaces.mixed 0 4 g z θ) ^ 2
          * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))) Work.Spaces.Iθ :=
      ((h31.add h22).add h13).add h04
    exact hall.congr_fun (fun θ _ => by ring) measurableSet_Icc
  refine ⟨hDzInt, hMint, ?_⟩
  -- ## The main inequality
  have hLHS : MeasureTheory.IntegrableOn (fun θ => (Work.Spaces.w z) ^ 2 *
      ((Work.Spaces.DzIter 4 g z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-Work.Spaces.eta)
        + ((Work.Spaces.mixed 3 1 g z θ) ^ 2 + (Work.Spaces.mixed 2 2 g z θ) ^ 2
          + (Work.Spaces.mixed 1 3 g z θ) ^ 2 + (Work.Spaces.mixed 0 4 g z θ) ^ 2)
          * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)))) Work.Spaces.Iθ :=
    (hDzInt.add hBblk).const_mul ((Work.Spaces.w z) ^ 2)
  have hpt : ∀ᵐ θ ∂(volume.restrict Work.Spaces.Iθ), (Work.Spaces.w z) ^ 2 *
      ((Work.Spaces.DzIter 4 g z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-Work.Spaces.eta)
        + ((Work.Spaces.mixed 3 1 g z θ) ^ 2 + (Work.Spaces.mixed 2 2 g z θ) ^ 2
          + (Work.Spaces.mixed 1 3 g z θ) ^ 2 + (Work.Spaces.mixed 0 4 g z θ) ^ 2)
          * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)))
      ≤ Work.Spaces.HkIntegrand α 4 g z θ :=
    MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc
      (fun θ hθ => slotQ_le_HkIntegrand α g z hθ)
  have hmono := MeasureTheory.integral_mono_ae hLHS hHk hpt
  have hcalc : (Work.Spaces.w z) ^ 2 * (∫ θ in Work.Spaces.Iθ,
      ((Work.Spaces.DzIter 4 g z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-Work.Spaces.eta)
        + ((Work.Spaces.mixed 3 1 g z θ) ^ 2 + (Work.Spaces.mixed 2 2 g z θ) ^ 2
          + (Work.Spaces.mixed 1 3 g z θ) ^ 2 + (Work.Spaces.mixed 0 4 g z θ) ^ 2)
          * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))))
      = ∫ θ in Work.Spaces.Iθ, (Work.Spaces.w z) ^ 2 *
      ((Work.Spaces.DzIter 4 g z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-Work.Spaces.eta)
        + ((Work.Spaces.mixed 3 1 g z θ) ^ 2 + (Work.Spaces.mixed 2 2 g z θ) ^ 2
          + (Work.Spaces.mixed 1 3 g z θ) ^ 2 + (Work.Spaces.mixed 0 4 g z θ) ^ 2)
          * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))) :=
    (MeasureTheory.integral_const_mul ((Work.Spaces.w z) ^ 2) _).symm
  rw [hcalc]
  exact hmono

end Work.H2.T1Q
