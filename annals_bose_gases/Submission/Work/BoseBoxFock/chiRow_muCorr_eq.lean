import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFock.chiRowDefs2
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.chiRow_muCorr_eq` — the `μ`-correction row of the `Q₁` χ-sandwich

The `μ`-correction of the χ-row is

    `muCorr ℓ w Φ = 2 Σ_j ∫_{abox n ℓ} (P_jΦ)²·w(x_j)`,

and the lemma says that it is a *pure volume effect*: since `P_jΦ` is constant in the `j`-th
slot (`Q0Sector.aP_const_in_coord`, `Q0Value.aP_fiber_const_one`), the integral over the `j`-th
slot of the box factorizes into `(∫_{acube ℓ} w)·(ℓ³)⁻¹` times the full `abox`-integral of
`(P_jΦ)²`, so

    `muCorr ℓ w Φ = 2·(∫_{acube ℓ} w)·((ℓ³)⁻¹·cS1 ℓ Φ)`.

In other words the whole `μ`-correction is the constant weight `∫_{acube} w` seen through the
condensed-particle count `cS1`, which is exactly the identity the χ-row assembly uses to collapse
the `μ`-row onto the counting rows.

## Mathematics

For `j : Fin (n+1)`, peel the `j`-th slot of `abox (n+1) ℓ` (`Q0Sector.abox_integral_peel`):

    `∫_{abox (n+1) ℓ} F = ∫_{r ∈ abox n ℓ} ∫_{y ∈ acube ℓ} F (kcInsN n j (y, r))`.

With `F = (P_jΦ)²·w(x_j)` the inner integrand is, for every `y`,

    `(P_jΦ (kcInsN n j (y,r)))²·w((kcInsN n j (y,r)) j)`
      `= (P_jΦ (kcInsN n j (0,r)))²·w y`   (`aP_fiber_const_one`, `kc_insN_apply_same`),

so the inner `y`-integral is `(P_jΦ (kcInsN n j (0,r)))²·(∫_{acube} w)`; pulling out the two
constants (`integral_const_mul`, `integral_mul_const`) gives

    `∫_{abox} (P_jΦ)²w(x_j) = (∫_{acube} w)·∫_{r ∈ abox n ℓ} (P_jΦ (kcInsN n j (0,r)))²`.

A second peel of `G := (P_jΦ)²` (whose fibre is constant in `y`, of volume `ℓ³`) gives
`∫_{abox} G = ℓ³·∫_{r} G (kcInsN n j (0,r))`, hence the claim.  Summing over `j`
(`Finset.sum_congr`, `Finset.mul_sum`) and unfolding `muCorr`/`cS1` produces the statement.

All declarations in this file are complete, with no unfinished goals.
-/

noncomputable section

open scoped BigOperators
open MeasureTheory

namespace Work.BoseBoxFock

set_option autoImplicit false
set_option maxHeartbeats 800000

local notation "Sp" => EuclideanSpace ℝ (Fin 3)

open Submission.BoseGases

/-- **The per-slot `μ`-correction identity.**  Because `P_jΦ` is constant in the `j`-th slot,
the weight `w (x j)` only contributes its cube average and the volume of the slot:

    `∫_{abox (n+1) ℓ} (P_jΦ)²·w(x_j) = (∫_{acube ℓ} w)·((ℓ³)⁻¹·∫_{abox (n+1) ℓ} (P_jΦ)²)`. -/
private lemma slot_weight_row {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) (i : Fin (n + 1))
    {Φ : X (n + 1) → ℝ} (hΦc : Continuous Φ) {w : Sp → ℝ}
    (hwm : Measurable w) {K : ℝ} (hw : ∀ x, |w x| ≤ K) :
    (∫ x in abox (n + 1) ℓ, (aP ℓ i Φ x) ^ 2 * w (x i))
      = (∫ z in acube ℓ, w z) * ((ℓ ^ 3)⁻¹ * ∫ x in abox (n + 1) ℓ, (aP ℓ i Φ x) ^ 2) := by
  let G : X (n + 1) → ℝ := fun x => (aP ℓ i Φ x) ^ 2
  let U : X (n + 1) → ℝ := fun x => G x * w (x i)
  let T1 : ℝ := ∫ r in abox n ℓ, G (kcInsN n i (0, r))
  have hG : IntegrableOn G (abox (n + 1) ℓ) volume := by
    simpa [G] using integrableOn_sq_aP hℓ i hΦc
  have hU : IntegrableOn U (abox (n + 1) ℓ) volume := by
    have h := hG.mul_bdd (g := fun x : X (n + 1) => w (x i))
      (hwm.comp (measurable_pi_apply i)).aestronglyMeasurable
      (by
        rw [ae_restrict_iff' (abox_measurable (n + 1) ℓ)]
        exact Filter.Eventually.of_forall (fun x _ => by
          simpa [Real.norm_eq_abs] using hw (x i)))
    exact h
  have hpeel1 := abox_integral_peel (n := n) (ℓ := ℓ) i U hU
  have hpeel2 := abox_integral_peel (n := n) (ℓ := ℓ) i G hG
  -- the fibre of `U` is constant in the peeled variable, and the slot weight gives `w y`
  have hmain : (∫ x in abox (n + 1) ℓ, U x) = (∫ z in acube ℓ, w z) * T1 := by
    calc
      (∫ x in abox (n + 1) ℓ, U x)
          = ∫ r in abox n ℓ, ∫ t in acube ℓ, U (kcInsN n i (t, r)) := hpeel1
      _ = ∫ r in abox n ℓ, ∫ t in acube ℓ, G (kcInsN n i (0, r)) * w t := by
            apply integral_congr_ae
            filter_upwards with r
            apply integral_congr_ae
            filter_upwards with t
            have h1 : (kcInsN n i (t, r)) i = t := kc_insN_apply_same n i t r
            have h2 : G (kcInsN n i (t, r)) = G (kcInsN n i (0, r)) := by
              dsimp [G]
              exact congrArg (fun u : ℝ => u ^ 2) (aP_fiber_const_one hℓ i hΦc t r)
            simp only [U]
            rw [h2, h1]
      _ = ∫ r in abox n ℓ, G (kcInsN n i (0, r)) * (∫ t in acube ℓ, w t) := by
            apply integral_congr_ae
            filter_upwards with r
            rw [MeasureTheory.integral_const_mul]
      _ = (∫ z in acube ℓ, w z) * T1 := by
            dsimp [T1]
            rw [MeasureTheory.integral_mul_const]
            ring
  -- the second peel gives the volume ratio between `abox` and the fibre integral
  have hGvol : (∫ x in abox (n + 1) ℓ, G x) = (ℓ ^ 3) * T1 := by
    calc
      (∫ x in abox (n + 1) ℓ, G x)
          = ∫ r in abox n ℓ, ∫ t in acube ℓ, G (kcInsN n i (t, r)) := hpeel2
      _ = ∫ r in abox n ℓ, ∫ t in acube ℓ, G (kcInsN n i (0, r)) := by
            apply integral_congr_ae
            filter_upwards with r
            apply integral_congr_ae
            filter_upwards with t
            have h2 : G (kcInsN n i (t, r)) = G (kcInsN n i (0, r)) := by
              dsimp [G]
              exact congrArg (fun u : ℝ => u ^ 2) (aP_fiber_const_one hℓ i hΦc t r)
            rw [h2]
      _ = (ℓ ^ 3) * T1 := by
            dsimp [T1]
            rw [show (∫ r in abox n ℓ, ∫ t in acube ℓ, G (kcInsN n i (0, r)))
                = ∫ r in abox n ℓ, (ℓ ^ 3) * G (kcInsN n i (0, r)) from by
                  apply integral_congr_ae
                  filter_upwards with r
                  rw [Submission.BoseGases.integral_const_acube ℓ hℓ]
                  ring]
            rw [MeasureTheory.integral_const_mul]
  have hℓ3 : ℓ ^ 3 ≠ 0 := pow_ne_zero 3 (ne_of_gt hℓ)
  have hT1 : (ℓ ^ 3)⁻¹ * (∫ x in abox (n + 1) ℓ, G x) = T1 := by
    rw [hGvol, ← mul_assoc, inv_mul_cancel₀ hℓ3, one_mul]
  calc
    (∫ x in abox (n + 1) ℓ, (aP ℓ i Φ x) ^ 2 * w (x i))
        = (∫ z in acube ℓ, w z) * T1 := by
          show (∫ x in abox (n + 1) ℓ, U x) = _
          exact hmain
    _ = (∫ z in acube ℓ, w z) * ((ℓ ^ 3)⁻¹ * ∫ x in abox (n + 1) ℓ, (aP ℓ i Φ x) ^ 2) := by
          rw [← hT1]

theorem chiRow_muCorr_eq {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {Φ : Submission.BoseGases.X n → ℝ}
    (hΦc : Continuous Φ) {w : EuclideanSpace ℝ (Fin 3) → ℝ} (hwm : Measurable w)
    {K : ℝ} (hw : ∀ x, |w x| ≤ K) :
    Work.BoseBoxFock.muCorr n ℓ w Φ
      = 2 * (∫ z in Submission.BoseGases.acube ℓ, w z)
          * ((ℓ ^ 3)⁻¹ * Submission.BoseGases.cS1 ℓ Φ) := by
  cases n with
  | zero => simp [muCorr, Submission.BoseGases.cS1]
  | succ m =>
      have h1 : (∑ j : Fin (m + 1), ∫ x in abox (m + 1) ℓ, (aP ℓ j Φ x) ^ 2 * w (x j))
          = ∑ j : Fin (m + 1), (∫ z in acube ℓ, w z)
              * ((ℓ ^ 3)⁻¹ * ∫ x in abox (m + 1) ℓ, (aP ℓ j Φ x) ^ 2) :=
        Finset.sum_congr rfl (fun j _ => slot_weight_row hℓ j hΦc hwm hw)
      have h2 : (∑ j : Fin (m + 1), (∫ z in acube ℓ, w z)
              * ((ℓ ^ 3)⁻¹ * ∫ x in abox (m + 1) ℓ, (aP ℓ j Φ x) ^ 2))
          = (∫ z in acube ℓ, w z)
            * ((ℓ ^ 3)⁻¹ * ∑ j : Fin (m + 1), ∫ x in abox (m + 1) ℓ, (aP ℓ j Φ x) ^ 2) := by
        rw [← Finset.mul_sum]
        congr 1
        rw [Finset.mul_sum]
      have h3 : (∑ j : Fin (m + 1), ∫ x in abox (m + 1) ℓ, (aP ℓ j Φ x) ^ 2)
          = Submission.BoseGases.cS1 ℓ Φ := rfl
      rw [muCorr, h1, h2, h3]
      ring

end Work.BoseBoxFock
