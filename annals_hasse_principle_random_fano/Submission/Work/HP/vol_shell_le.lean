import Mathlib
import Submission.Work.HP.Defs
import Submission.Work.HP.volume_rNorm_ball
import Submission.Work.HP.volume_rNorm_ball_lt
import Submission.Work.HP.one_add_pow_sub_one_le

/-!
# Volume of the thin shell `{1 ≤ rNorm z ≤ 1 + t}`

For `0 < t ≤ 1` the shell `{z : ℝ^{n+1} | 1 ≤ ‖z‖ ≤ 1 + t}` has volume at most
`(2^{n+1} t) · vol(B(1))`, where `B(1) = {z | ‖z‖ ≤ 1}` is the Euclidean unit ball.

Exact computation of the two ball volumes (the closed ball of radius `1+t` via
`volume_rNorm_ball`, the open unit ball via `volume_rNorm_ball_lt`) exhibits the shell
volume as `((1+t)^{n+1} - 1) · vol(B(1))`, and the elementary binomial estimate
`(1+t)^{n+1} - 1 ≤ 2^{n+1} t` for `t ∈ [0,1]` finishes the job.
-/

set_option autoImplicit false

noncomputable section

namespace Work.HP

open MeasureTheory

/-- The `L²`-expression of Mathlib's ball-volume formula specialises to `rNorm` at `p = 2`. -/
private lemma rNorm_eq_lp {ι : Type*} [Fintype ι] (v : ι → ℝ) :
    (∑ i, |v i| ^ (2 : ℝ)) ^ ((1 : ℝ) / 2) = rNorm v := by
  rw [← Real.sqrt_eq_rpow, rNorm]
  congr 1
  exact Finset.sum_congr rfl fun i _ => by rw [Real.rpow_ofNat, sq_abs]

theorem vol_shell_le (n : ℕ) (t : ℝ) (ht0 : 0 < t) (ht1 : t ≤ 1) :
    MeasureTheory.volume {z : Fin (n + 1) → ℝ | 1 ≤ Work.HP.rNorm z ∧ Work.HP.rNorm z ≤ 1 + t}
      ≤ ENNReal.ofReal ((2 : ℝ) ^ (n + 1) * t) *
        MeasureTheory.volume {z : Fin (n + 1) → ℝ | Work.HP.rNorm z ≤ 1} := by
  have ht0' : (0 : ℝ) ≤ t := le_of_lt ht0
  set V0 : ENNReal := MeasureTheory.volume {z : Fin (n + 1) → ℝ | rNorm z ≤ 1} with hV0def
  -- measurability of the norm
  have hcont : Continuous (fun z : Fin (n + 1) → ℝ => rNorm z) := by
    have h : Continuous (fun z : Fin (n + 1) → ℝ => ∑ i, (z i) ^ 2) :=
      continuous_finsetSum Finset.univ (fun i _ => (continuous_apply i).pow 2)
    exact Real.continuous_sqrt.comp h
  have hmeas : Measurable (fun z : Fin (n + 1) → ℝ => rNorm z) := hcont.measurable
  have hmeasB : MeasurableSet {z : Fin (n + 1) → ℝ | rNorm z < 1} :=
    measurableSet_lt hmeas measurable_const
  -- `V0 < ∞`
  have hV0top : V0 ≠ ⊤ := by
    rw [hV0def]
    have h := MeasureTheory.volume_sum_rpow_le (Fin (n + 1)) (p := 2) (by norm_num) (1 : ℝ)
    rw [show {x : Fin (n + 1) → ℝ | (∑ i, |x i| ^ (2 : ℝ)) ^ ((1 : ℝ) / 2) ≤ 1}
        = {x : Fin (n + 1) → ℝ | rNorm x ≤ 1} from by
          ext x; rw [Set.mem_ofPred_eq, Set.mem_ofPred_eq, rNorm_eq_lp x]] at h
    rw [h]
    exact ENNReal.mul_ne_top (ENNReal.pow_ne_top ENNReal.ofReal_ne_top) ENNReal.ofReal_ne_top
  -- volume of the open unit ball equals `V0`
  have hB_eq : MeasureTheory.volume {z : Fin (n + 1) → ℝ | rNorm z < 1} = V0 := by
    rw [hV0def, volume_rNorm_ball_lt (ι := Fin (n + 1)) (1 : ℝ) (by norm_num)]
    simp [Fintype.card_fin, ENNReal.ofReal_one]
  have hBtop : MeasureTheory.volume {z : Fin (n + 1) → ℝ | rNorm z < 1} ≠ ⊤ := by
    rw [hB_eq]; exact hV0top
  -- the shell is the closed ball minus the open unit ball
  have hseteq : {z : Fin (n + 1) → ℝ | 1 ≤ rNorm z ∧ rNorm z ≤ 1 + t}
      = {z : Fin (n + 1) → ℝ | rNorm z ≤ 1 + t} \ {z : Fin (n + 1) → ℝ | rNorm z < 1} := by
    ext z
    simp only [Set.mem_ofPred_eq, Set.mem_sdiff, not_lt]
    tauto
  have hsub : {z : Fin (n + 1) → ℝ | rNorm z < 1} ⊆ {z : Fin (n + 1) → ℝ | rNorm z ≤ 1 + t} := by
    intro z hz
    simp only [Set.mem_ofPred_eq] at hz ⊢
    linarith
  have hC : MeasureTheory.volume {z : Fin (n + 1) → ℝ | 1 ≤ rNorm z ∧ rNorm z ≤ 1 + t}
      = MeasureTheory.volume {z : Fin (n + 1) → ℝ | rNorm z ≤ 1 + t}
        - MeasureTheory.volume {z : Fin (n + 1) → ℝ | rNorm z < 1} := by
    rw [hseteq]
    exact measure_sdiff hsub hmeasB.nullMeasurableSet hBtop
  -- volume of the closed ball of radius `1+t`
  have hA_eq : MeasureTheory.volume {z : Fin (n + 1) → ℝ | rNorm z ≤ 1 + t}
      = ENNReal.ofReal ((1 + t) ^ (n + 1)) * V0 := by
    rw [hV0def]
    have h := volume_rNorm_ball (ι := Fin (n + 1)) (0 : Fin (n + 1) → ℝ) (1 + t) (by linarith)
    simpa [Fintype.card_fin] using h
  rw [hC, hA_eq, hB_eq]
  -- reduce to the real arithmetic estimate
  have hL' : ENNReal.ofReal ((1 + t) ^ (n + 1)) * V0 - 1 * V0
      = (ENNReal.ofReal ((1 + t) ^ (n + 1)) - 1) * V0 :=
    (ENNReal.sub_mul (a := ENNReal.ofReal ((1 + t) ^ (n + 1))) (b := 1) (c := V0)
      (fun _ _ => hV0top)).symm
  have hL : ENNReal.ofReal ((1 + t) ^ (n + 1)) * V0 - V0
      = (ENNReal.ofReal ((1 + t) ^ (n + 1)) - 1) * V0 := by
    simpa using hL'
  have hsub2 : ENNReal.ofReal ((1 + t) ^ (n + 1)) - 1
      = ENNReal.ofReal ((1 + t) ^ (n + 1) - 1) := by
    rw [← ENNReal.ofReal_one]
    exact (ENNReal.ofReal_sub ((1 + t) ^ (n + 1)) (by norm_num : (0 : ℝ) ≤ 1)).symm
  rw [hL, hsub2]
  have hAB : ENNReal.ofReal ((1 + t) ^ (n + 1) - 1)
      ≤ ENNReal.ofReal ((2 : ℝ) ^ (n + 1) * t) :=
    ENNReal.ofReal_le_ofReal (one_add_pow_sub_one_le (n + 1) t ht0' ht1)
  exact mul_le_mul hAB le_rfl zero_le zero_le

end Work.HP
