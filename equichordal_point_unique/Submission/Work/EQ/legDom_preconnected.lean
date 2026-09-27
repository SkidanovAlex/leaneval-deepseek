import Mathlib
import Submission.Work.Analysis.Complex.punctured_ball_connected

namespace Work.EQ

/-- `a ^ k` (natural power) is below `b > 0` exactly when `a` is below `b ^ (1/k)` (real power).
This is the standard `k`-th root rearrangement, for the case that the root exponent is a natural
number `k > 0`. -/
lemma rpow_inv_natCast_lt_iff {a b : ℝ} (ha : 0 ≤ a) (hb : 0 < b) {k : ℕ} (hk : 0 < k) :
    a ^ k < b ↔ a < b ^ (((k : ℝ))⁻¹) := by
  have hkr : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  have hb' : (b ^ (((k : ℝ))⁻¹)) ^ (k : ℝ) = b := by
    rw [← Real.rpow_mul hb.le, inv_mul_cancel₀ hkr.ne', Real.rpow_one]
  have hiff := Real.rpow_lt_rpow_iff ha (le_of_lt (Real.rpow_pos_of_pos hb _)) hkr
    (x := a) (y := b ^ (((k : ℝ))⁻¹)) (z := (k : ℝ))
  rw [hb'] at hiff
  constructor
  · intro h
    refine hiff.mp ?_
    rwa [Real.rpow_natCast]
  · intro h
    have h' : a ^ (k : ℝ) < b := hiff.mpr h
    simpa only [Real.rpow_natCast] using h'

/-- **The punctured orbit domain `{ζ ≠ 0 | ‖κ ζ^k‖ < ρ}` is preconnected.**  For `κ ≠ 0`, `k > 0`
and `ρ > 0` the set of nonzero `ζ` with `‖κ ζ^k‖ < ρ` is a punctured disc of radius
`(ρ/‖κ‖)^{1/k}`, hence preconnected.  (Concretely: it is the image of the connected set
`(0,r) × ℝ` under `(s,t) ↦ s·exp(t·I)`, or equivalently it equals
`Metric.ball 0 ((ρ/‖κ‖)^(1/k)) \ {0}`, and `Work.Analysis.Complex.isConnected_punctured_ball_at`
gives the connectedness of a punctured disc.) -/
theorem legDom_preconnected {κ : ℂ} (hκ : κ ≠ 0) {k : ℕ} (hk : 0 < k) {ρ : ℝ} (hρ : 0 < ρ) :
    IsPreconnected {ζ : ℂ | ζ ≠ 0 ∧ ‖κ * ζ ^ k‖ < ρ} := by
  have hκn : 0 < ‖κ‖ := norm_pos_iff.mpr hκ
  have hb : 0 < ρ / ‖κ‖ := div_pos hρ hκn
  have hr : 0 < (ρ / ‖κ‖) ^ (((k : ℝ))⁻¹) := Real.rpow_pos_of_pos hb _
  -- rewrite the set as the punctured disc of radius `(ρ/‖κ‖)^{1/k} = r`
  have hset : {ζ : ℂ | ζ ≠ 0 ∧ ‖κ * ζ ^ k‖ < ρ}
      = {z : ℂ | 0 < ‖z - 0‖ ∧ ‖z - 0‖ < (ρ / ‖κ‖) ^ (((k : ℝ))⁻¹)} := by
    ext ζ
    simp only [Set.mem_ofPred_eq, sub_zero]
    constructor
    · rintro ⟨hne, hlt⟩
      refine ⟨norm_pos_iff.mpr hne, ?_⟩
      rw [Complex.norm_mul, Complex.norm_pow] at hlt
      have h1 : ‖ζ‖ ^ k < ρ / ‖κ‖ := by
        rw [lt_div_iff₀ hκn]
        rwa [mul_comm]
      exact (rpow_inv_natCast_lt_iff (norm_nonneg ζ) hb hk).mp h1
    · rintro ⟨hpos, hlt⟩
      have hne : ζ ≠ 0 := fun h => by rw [h] at hpos; simp at hpos
      refine ⟨hne, ?_⟩
      rw [Complex.norm_mul, Complex.norm_pow]
      have h1 : ‖ζ‖ ^ k < ρ / ‖κ‖ :=
        (rpow_inv_natCast_lt_iff (norm_nonneg ζ) hb hk).mpr hlt
      rw [lt_div_iff₀ hκn] at h1
      rwa [mul_comm] at h1
  rw [hset]
  exact (_root_.Work.Analysis.Complex.isConnected_punctured_ball_at 0 hr).2

end Work.EQ
