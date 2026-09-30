import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
set_option maxHeartbeats 1000000
open MeasureTheory
open scoped ENNReal
open MeasureTheory.Measure

namespace Commons.Analysis.Integral

private abbrev E (k : ℕ) := EuclideanSpace ℝ (Fin k)

/-- The function `y ↦ (1 + ‖y‖)^(-100k)` is integrable on `E k = ℝᵏ`.  This is
Mathlib's Japanese-bracket integrability (`integrable_one_add_norm`), specialized to
the exponent `100k`, which is larger than the dimension `k` because `k ≥ 1`. -/
private lemma center0_rpow_integrable (k : ℕ) (hk : 1 ≤ k) :
    Integrable (fun y : E k => (1 + ‖y‖) ^ (-((100 * k : ℕ) : ℝ)))
      (volume : Measure (E k)) := by
  have hkn : k < 100 * k := by omega
  have hnr : (Module.finrank ℝ (E k) : ℝ) < ((100 * k : ℕ) : ℝ) := by
    have hfin : Module.finrank ℝ (E k) = k := by simp [E]
    rw [hfin]
    exact_mod_cast hkn
  exact integrable_one_add_norm (μ := (volume : Measure (E k)))
    (r := ((100 * k : ℕ) : ℝ)) hnr

/-- Rescaling invariance of the integrability: `y ↦ (1 + ‖y‖ / R)^(-100k)` is
integrable (rescaling a measure by a positive constant does not change integrability). -/
private lemma scaled_rpow_integrable (k : ℕ) (hk : 1 ≤ k) {R : ℝ} (hR : 0 < R) :
    Integrable (fun y : E k => (1 + ‖y‖ / R) ^ (-((100 * k : ℕ) : ℝ)))
      (volume : Measure (E k)) := by
  let r : ℝ := ((100 * k : ℕ) : ℝ)
  let s : ℝ := R⁻¹
  have hs : s ≠ 0 := inv_ne_zero (ne_of_gt hR)
  let e : E k ≃ᵐ E k := (Homeomorph.smul (isUnit_iff_ne_zero.2 hs).unit).toMeasurableEquiv
  have he_fun : (fun y : E k => e y) = fun y : E k => s • y := by
    funext y
    rfl
  let F0 : E k → ℝ := fun y => (1 + ‖y‖) ^ (-r)
  have hF0 : Integrable F0 (volume : Measure (E k)) := by
    dsimp [F0, r]
    exact center0_rpow_integrable k hk
  have hpk : s ^ Module.finrank ℝ (E k) ≠ 0 := pow_ne_zero _ hs
  have hpos_abs : 0 < abs ((s ^ Module.finrank ℝ (E k))⁻¹) := abs_pos.mpr (inv_ne_zero hpk)
  let c : ℝ≥0∞ := ENNReal.ofReal (abs ((s ^ Module.finrank ℝ (E k))⁻¹))
  have hmap_s : Measure.map (fun y : E k => s • y) (volume : Measure (E k)) =
      c • (volume : Measure (E k)) := by
    dsimp [c]
    exact map_addHaar_smul (μ := (volume : Measure (E k))) hs
  have hmap_e : volume.map e = c • (volume : Measure (E k)) := by
    change Measure.map (fun y : E k => e y) (volume : Measure (E k)) = c • (volume : Measure (E k))
    rw [he_fun]
    exact hmap_s
  have hc0 : c ≠ 0 := by
    dsimp [c]
    exact ne_of_gt ((ENNReal.ofReal_pos).2 hpos_abs)
  have hctop : c ≠ ∞ := by
    dsimp [c]
    exact ne_of_lt ENNReal.ofReal_lt_top
  have hscaled : Integrable F0 (volume.map e) := by
    rw [hmap_e]
    exact (integrable_smul_measure (f := F0) (c := c) hc0 hctop).2 hF0
  have hiff : Integrable F0 (Measure.map (⇑e) (volume : Measure (E k))) ↔
      Integrable (F0 ∘ ⇑e) (volume : Measure (E k)) := by
    exact integrable_map_equiv (α := E k) (δ := E k) (μ := (volume : Measure (E k))) e F0
  have h_after : Integrable (F0 ∘ ⇑e) (volume : Measure (E k)) := hiff.1 hscaled
  have hcomp : Integrable (fun y : E k => F0 (s • y)) (volume : Measure (E k)) := by
    convert h_after using 1
    funext y
    rfl
  have hnorm (y : E k) : ‖s • y‖ = ‖y‖ / R := by
    dsimp [s]
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hR), div_eq_mul_inv, mul_comm]
  have hEq : (fun y : E k => (1 + ‖y‖ / R) ^ (-r)) = fun y : E k => F0 (s • y) := by
    funext y
    dsimp [F0]
    rw [hnorm y]
  rw [hEq]
  exact hcomp

/-- Translation invariance: `x ↦ (1 + ‖x - c‖ / R)^(-100k)` is integrable. -/
private lemma translated_rpow_integrable (k : ℕ) (hk : 1 ≤ k) (c : E k) {R : ℝ} (hR : 0 < R) :
    Integrable (fun x : E k => (1 + ‖x - c‖ / R) ^ (-((100 * k : ℕ) : ℝ)))
      (volume : Measure (E k)) := by
  let r : ℝ := ((100 * k : ℕ) : ℝ)
  let F1 : E k → ℝ := fun y => (1 + ‖y‖ / R) ^ (-r)
  have hF1 : Integrable F1 (volume : Measure (E k)) := by
    dsimp [F1]
    exact scaled_rpow_integrable k hk hR
  have hτ : MeasurePreserving (fun x : E k => -c + x) volume volume :=
    measurePreserving_add_left (μ := (volume : Measure (E k))) (-c)
  have hIntτ : Integrable (fun x : E k => F1 (-c + x)) (volume : Measure (E k)) :=
    hτ.integrable_comp_of_integrable hF1
  have hnc (x : E k) : ‖-c + x‖ = ‖x - c‖ := by
    congr 1
    rw [sub_eq_add_neg, add_comm]
  have hfun : (fun x : E k => F1 (-c + x)) = fun x : E k => (1 + ‖x - c‖ / R) ^ (-r) := by
    funext x
    dsimp [F1]
    rw [hnc x]
  rw [← hfun]
  exact hIntτ

theorem ball_weight_integrable_expr (k : ℕ) (hk : 1 ≤ k)
    (c : EuclideanSpace ℝ (Fin k)) {R : ℝ} (hR : 0 < R) :
    MeasureTheory.Integrable
      (fun x : EuclideanSpace ℝ (Fin k) => ((1 + ‖x - c‖ / R) ^ (100 * k))⁻¹)
      MeasureTheory.volume := by
  have hMain : Integrable
      (fun x : E k => (1 + ‖x - c‖ / R) ^ (-((100 * k : ℕ) : ℝ)))
      (volume : Measure (E k)) := by
    exact translated_rpow_integrable k hk c hR
  have hpt : (fun x : EuclideanSpace ℝ (Fin k) =>
        ((1 + ‖x - c‖ / R) ^ (100 * k))⁻¹) =
      fun x : EuclideanSpace ℝ (Fin k) => (1 + ‖x - c‖ / R) ^ (-((100 * k : ℕ) : ℝ)) := by
    funext x
    have hb : 0 ≤ 1 + ‖x - c‖ / R := by
      have hnorm : 0 ≤ ‖x - c‖ := norm_nonneg _
      have hdiv : 0 ≤ ‖x - c‖ / R := div_nonneg hnorm (le_of_lt hR)
      linarith
    rw [Real.rpow_neg hb, Real.rpow_natCast]
  simpa [hpt] using hMain

end Commons.Analysis.Integral