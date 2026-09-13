/-
# The Harnack inequality for the small-perturbation equation (Savin, Theorem 1.1)

`Φ` is a perturbation of a solution `Q` of `σ₂ = 1` (with `ΔQ > 0`), so that
`s2 (A + D²Φ) = 1` with `A = D²Q` (`s2 A = 1`, `trOp A > 0`), `trOp (A + D²Φ) > 0`.
The statement proved here: if `0 ≤ Φ ≤ Λ` on `ball 0 (5/2)`, `Φ 0 ≤ ε`, and the perturbation is
small (`Λ 2^{2p+4}` and `ε M` controlled by the ellipticity constant `c`), then `Φ ≤ C ε` on
`closedBall 0 (1/6)`, with `C` depending only on the ellipticity data (`A`, `c`, `c'`, `p`) and NOT
on `Φ`, `ε`, `Λ`.

Proof: the from-below sliding-paraboloid machinery (`density_contactPt` + `enlarge_opening` + the
decay lemma) gives
  `|{φ > 1 + 32 M^{j+1}} ∩ S| ≤ (1-θ)^j |S|`,  `φ := Φ/ε`,  `S = closedBall 0 (1/2)`,
while the from-above propagation `propagation_step` shows that a point where `φ ≥ 1 + 32 M^{k+1}`
either has a nearby point with `φ ≥ 1 + 32 M^{k+2}` (the level grows by the factor `M`) or forces a
set of definite measure where `φ ≥ 2(1+32M^{k+1})/M ≥ 1+32M^k`, contradicting the decay estimate at
index `k-1`.  Since `φ ≤ Λ/ε` the growth cannot continue for ever, so the assumption is impossible.
-/
import Mathlib
import ChallengeDeps
import Submission.Savin.PropagationAbove
import Submission.Savin.WeakLEps
import Submission.Savin.Decay
import Submission.Savin.Density
import Submission.Commons.Analysis.Real.sum_Ico_pow_mul_le_tail
import Submission.Commons.Analysis.Real.rpow_quarter_one_sub_le
import Submission.Commons.Analysis.Real.theta_le_fifteen_sixteenth
import Submission.Commons.Analysis.Real.sqrt_eta_properties
import Submission.Commons.Analysis.Real.one_add_128_le_of_pos
import Submission.Commons.Analysis.Real.level_prev_le_of_half_le

open Metric MeasureTheory Filter
open Commons.Analysis.Real
open scoped BigOperators RealInnerProductSpace Topology ENNReal Pointwise

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 16000000

namespace Submission

local notation "ℝ⁴" => EuclideanSpace ℝ (Fin 4)

noncomputable section

/-! ## 0. Elementary preliminaries -/

theorem isSymmetric_one' : (1 : ℝ⁴ →L[ℝ] ℝ⁴).IsSymmetric := by
  intro x y; simp

theorem isSymmetric_smul' {T : ℝ⁴ →L[ℝ] ℝ⁴} (hT : T.IsSymmetric) (k : ℝ) :
    (k • T).IsSymmetric := by
  intro x y
  change inner ℝ ((k • T) x) y = inner ℝ x ((k • T) y)
  rw [smul_apply, smul_apply, real_inner_smul_left, real_inner_smul_right]
  exact congrArg (fun t => k * t) (hT x y)

theorem isSymmetric_sub' {T U : ℝ⁴ →L[ℝ] ℝ⁴} (hT : T.IsSymmetric) (hU : U.IsSymmetric) :
    (T - U).IsSymmetric := by
  intro x y
  change inner ℝ ((T - U) x) y = inner ℝ x ((T - U) y)
  rw [sub_apply, sub_apply, inner_sub_left, inner_sub_right]
  exact congrArg₂ (fun a b => a - b) (hT x y) (hU x y)

/-- The cofactor operator of a symmetric operator is symmetric. -/
theorem cofOp_isSymmetric {S : ℝ⁴ →L[ℝ] ℝ⁴} (hS : S.IsSymmetric) :
    (cofOp S).IsSymmetric := by
  unfold cofOp
  exact isSymmetric_sub' (isSymmetric_smul' isSymmetric_one' _) hS

/-- The image of a ball under `y ↦ x₀ + b • y`, `b > 0`. -/
theorem image_add_smul_closedBall (x₀ : ℝ⁴) {b r : ℝ} (hb : 0 < b) :
    (fun y : ℝ⁴ => x₀ + b • y) '' closedBall 0 r = closedBall x₀ (b * r) := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    rw [mem_closedBall, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
        abs_of_pos hb]
    have hy' : ‖y‖ ≤ r := by simpa [mem_closedBall, dist_zero_right] using hy
    nlinarith [norm_nonneg y]
  · intro hx
    refine ⟨b⁻¹ • (x - x₀), ?_, ?_⟩
    · rw [mem_closedBall, dist_zero_right, norm_smul, Real.norm_eq_abs,
          abs_of_pos (inv_pos.mpr hb), inv_mul_le_iff₀ hb]
      have hx' : ‖x - x₀‖ ≤ b * r := by simpa [mem_closedBall, dist_eq_norm] using hx
      linarith
    · change x₀ + b • (b⁻¹ • (x - x₀)) = x
      rw [smul_smul, mul_inv_cancel₀ (ne_of_gt hb), one_smul, add_sub_cancel]

/-- The volume of a ball of radius `b` about any centre, in terms of the unit ball. -/
theorem volume_closedBall_eq (x₀ : ℝ⁴) {b : ℝ} (hb : 0 < b) :
    volume (closedBall x₀ b) = ENNReal.ofReal (b ^ 4) * volume (closedBall (0 : ℝ⁴) 1) := by
  have h : (fun y : ℝ⁴ => x₀ + b • y) '' closedBall 0 (1 : ℝ) = closedBall x₀ b := by
    rw [image_add_smul_closedBall x₀ hb]; norm_num
  rw [← h, volume_image_add_smul x₀ hb]

theorem volume_unit_closedBall_ne_zero : volume (closedBall (0 : ℝ⁴) 1) ≠ 0 := by
  rw [Measure.addHaar_closedBall_eq_addHaar_ball]
  exact (measure_ball_pos volume (0 : ℝ⁴) (by norm_num)).ne'

theorem volume_unit_closedBall_ne_top : volume (closedBall (0 : ℝ⁴) 1) ≠ ⊤ := by
  rw [Measure.addHaar_closedBall_eq_addHaar_ball]
  exact measure_ball_lt_top.ne

/-! ## 1. From the `σ₂` equation to the linearised equation -/

/-- If `s2 (A + M) = s2 A` then `ε⁻¹ • M` solves the linearised equation with parameter `ε`. -/
theorem fop_inv_smul_eq_zero {A M : ℝ⁴ →L[ℝ] ℝ⁴} (hA : A.IsSymmetric) (hM : M.IsSymmetric)
    {ε : ℝ} (hε : ε ≠ 0) (heq : s2 (A + M) = s2 A) :
    Fop (cofOp A) ε (ε⁻¹ • M) = 0 := by
  have h1 : s2 (A + M) = s2 A + s2 M + pairOp (cofOp A) M := s2_add_expansion hA hM
  have h2 : Fop (cofOp A) 1 M = 0 := by
    rw [Fop]
    linarith
  rw [Fop_smul, show ε * ε⁻¹ = 1 from mul_inv_cancel₀ hε, h2, mul_zero]

/-- Multiplying a function by a constant divides its Hessian operator. -/
theorem hessOp_div_const (c : ℝ) {Φ : ℝ⁴ → ℝ} {x : ℝ⁴} (h : ContDiffAt ℝ 2 Φ x) :
    hessOp (fun y => Φ y / c) x = c⁻¹ • hessOp Φ x := by
  have hfun : (fun y : ℝ⁴ => Φ y / c) = (fun y => c⁻¹ * Φ y) := by
    funext y; rw [div_eq_inv_mul]
  rw [hfun]
  exact hessOp_const_mul c⁻¹ h

theorem harnack_arith_level {M ε : ℝ} (hM4 : 4 ≤ M) (hε : 0 < ε) (k : ℕ) :
    ε * (1 + 32 * M ^ k) < 2 * (ε * (1 + 32 * M ^ (k + 1))) / M := by
  have hMpos : 0 < M := by linarith
  have hMk1 : (1 : ℝ) ≤ M ^ k := one_le_pow₀ (by linarith : (1 : ℝ) ≤ M)
  have hu0 : 0 ≤ ε * M ^ k * M := by positivity
  have hu : ε * M ≤ ε * M ^ k * M := by
    have h1 : M ≤ M ^ k * M := by nlinarith [hMk1, hMpos]
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_left h1 hε.le
  have hεM0 : 0 ≤ ε * M := mul_nonneg hε.le hMpos.le
  rw [lt_div_iff₀ hMpos, pow_succ M k]
  linarith [hu, hu0, hεM0, hε]

theorem harnack_arith_grow {M ε : ℝ} (hM1 : 1 < M) (hε : 0 < ε) (k : ℕ) :
    ε * (1 + 32 * M ^ (k + 2)) ≤ M * (ε * (1 + 32 * M ^ (k + 1))) := by
  have hMpos : 0 < M := by linarith
  rw [pow_succ M (k + 1)]
  nlinarith [hM1, hε, pow_pos hMpos (k + 1)]

/-! ## 2. The Harnack inequality -/

/-- **Savin's Harnack inequality** for the small-perturbation equation (Theorem 1.1 of
*Small perturbation solutions for elliptic equations*, CPDE 32 (2007)), in UNIFORM form: the
constant `C` depends on the base `A` only through the bound `2 trOp (cofOp A) / c ≤ Y`. -/
theorem harnack_uniform {c c' Y p M : ℝ} (hc : 0 < c) (hc'pos : 0 < c') (hYnn : 0 ≤ Y)
    (hp : 0 < p) (hM1 : 1 < M) (hM : M = 1 + 128 * ((1 / p) * (2 ^ p - 1)))
    (hpbig : 16 * c' / c + 2 ≤ p) :
    ∃ C : ℝ, 0 < C ∧ ∀ (A : ℝ⁴ →L[ℝ] ℝ⁴) (hA : A.IsSymmetric) (hA1 : s2 A = 1)
      (htrA : 0 < trOp A) (hcq : ∀ v : ℝ⁴, c * ‖v‖ ^ 2 ≤ ⟪cofOp A v, v⟫)
      (hcq' : ∀ v : ℝ⁴, ⟪cofOp A v, v⟫ ≤ c' * ‖v‖ ^ 2)
      (hYb : 2 * trOp (cofOp A) / c ≤ Y)
      (Φ : ℝ⁴ → ℝ) (ε Λ : ℝ), 0 < ε → 0 < Λ →
      ContDiffOn ℝ 2 Φ (ball 0 (5 / 2)) →
      (∀ x ∈ ball 0 (5 / 2), s2 (A + hessOp Φ x) = 1) →
      (∀ x ∈ ball 0 (5 / 2), 0 < trOp (A + hessOp Φ x)) →
      (∀ x ∈ ball 0 (5 / 2), 0 ≤ Φ x) → (∀ x ∈ ball 0 (5 / 2), Φ x ≤ Λ) → Φ 0 ≤ ε →
      768 * Λ * 2 ^ (2 * p + 4) ≤ c → 1536 * ε * M ≤ c →
      ∀ x ∈ closedBall 0 (1 / 6), Φ x ≤ C * ε := by
  classical
  -- (A) constants depending only on `c, c', Y, M` -- NOT on the base `A`
  have hMpos : 0 < M := by linarith
  have hM4 : 4 ≤ M := by rw [hM]; exact one_add_128_le_of_pos hp
  have hKtY : (0 : ℝ) < 1 + (Y + 3) := by linarith
  set K₀ : ℝ := (1 + 4 * c' / c) ^ 4 with hK₀def
  have hK₀pos : 0 < K₀ := by rw [hK₀def]; positivity
  set B : ℝ := 8 * Real.sqrt M * (1 + 4 * c' / c) + 1 with hBdef
  have hBpos : 0 < B := by rw [hBdef]; positivity
  set η : ℝ := 1 / (8 * Real.sqrt M) with hηdef
  have hη4 : η ^ 4 = 1 / (4096 * M ^ 2) := by
    rw [hηdef]; exact (sqrt_eta_properties hM4).1
  have hη16 : η ≤ 1 / 16 := by rw [hηdef]; exact (sqrt_eta_properties hM4).2.1
  have hηlev : 8 * (M - 1) * η ^ 2 ≤ 1 - 2 / M := by
    rw [hηdef]; exact (sqrt_eta_properties hM4).2.2
  have hηpos : 0 < η := by rw [hηdef]; positivity
  have hB4 : K₀ ≤ η ^ 4 * B ^ 4 := by
    have hsq : (Real.sqrt M) ^ 2 = M := Real.sq_sqrt hMpos.le
    have h4 : (8 * Real.sqrt M * (1 + 4 * c' / c)) ^ 4
        = 4096 * M ^ 2 * (1 + 4 * c' / c) ^ 4 := by
      rw [mul_pow, mul_pow]
      rw [show (Real.sqrt M) ^ 4 = M ^ 2 by
        rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, hsq]]
      norm_num
    have hle : 8 * Real.sqrt M * (1 + 4 * c' / c) ≤ B := by rw [hBdef]; linarith
    have hnn : 0 ≤ 8 * Real.sqrt M * (1 + 4 * c' / c) := by positivity
    have h6 : 4096 * M ^ 2 * (1 + 4 * c' / c) ^ 4 ≤ B ^ 4 := by
      rw [← h4]; exact pow_le_pow_left₀ hnn hle 4
    rw [hK₀def, hη4]
    have h7 : (0 : ℝ) < 4096 * M ^ 2 := by positivity
    have h8 : (1 / (4096 * M ^ 2)) * (4096 * M ^ 2 * (1 + 4 * c' / c) ^ 4)
        = (1 + 4 * c' / c) ^ 4 := by field_simp
    rw [← h8]
    exact mul_le_mul_of_nonneg_left h6 (by positivity)
  -- the uniform rate `θU`, obtained from the bound `2 trOp (cofOp A) / c ≤ Y`
  set θU : ℝ := ((M - 1) / (8 * M)) ^ 4 / ((1 + (Y + 3)) ^ 4 * 5 ^ 4) with hθUdef
  have hθUpos : 0 < θU := by rw [hθUdef]; positivity
  have hθUlt : θU < 15 / 16 := by
    have h1 : ((M - 1) / (8 * M)) ^ 4 ≤ 1 / 4096 := by
      have h2 : (M - 1) / (8 * M) ≤ 1 / 8 := by
        rw [div_le_div_iff₀ (by positivity : (0 : ℝ) < 8 * M) (by norm_num : (0 : ℝ) < 8)]
        linarith
      have h3 : (0 : ℝ) ≤ (M - 1) / (8 * M) := by positivity
      calc ((M - 1) / (8 * M)) ^ 4 ≤ ((1 : ℝ) / 8) ^ 4 := pow_le_pow_left₀ h3 h2 4
        _ = 1 / 4096 := by norm_num
    have h4 : (1 : ℝ) ≤ (1 + (Y + 3)) ^ 4 * 5 ^ 4 := by
      have h5 : (1 : ℝ) ≤ (1 + (Y + 3)) ^ 4 := one_le_pow₀ (by linarith)
      nlinarith [h5]
    have hX0 : (0 : ℝ) ≤ ((M - 1) / (8 * M)) ^ 4 := by positivity
    have h7 : ((M - 1) / (8 * M)) ^ 4 / ((1 + (Y + 3)) ^ 4 * 5 ^ 4)
        ≤ ((M - 1) / (8 * M)) ^ 4 := by
      rw [div_le_iff₀ (by positivity)]
      nlinarith [hX0, h4]
    rw [hθUdef]
    linarith [h1, h7]
  set rU : ℝ := (1 - θU) ^ ((1 : ℝ) / 4) with hrUdef
  have hrUpos : 0 < rU := Real.rpow_pos_of_pos (by linarith : (0:ℝ) < 1 - θU) _
  have hrU1 : rU < 1 := by
    have h := Real.rpow_lt_one (show (0 : ℝ) ≤ 1 - θU by linarith)
      (show (1 : ℝ) - θU < 1 by linarith) (show (0 : ℝ) < 1 / 4 by norm_num)
    rw [hrUdef]; exact h
  have hNex : ∃ n : ℕ, B * rU ^ n < θU / 48 := by
    obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (show (0 : ℝ) < θU / 48 / B by positivity) hrU1
    refine ⟨n, ?_⟩
    have h2 := mul_lt_mul_of_pos_left hn hBpos
    have h3 : B * (θU / 48 / B) = θU / 48 := by field_simp
    linarith [h2, h3]
  set N : ℕ := Nat.find hNex with hNdef
  have hNsmallU : B * rU ^ N < θU / 48 := Nat.find_spec hNex
  have hNge1 : 1 ≤ N := by
    rcases Nat.eq_zero_or_pos N with h | h
    · rw [h] at hNsmallU
      simp only [pow_zero, mul_one] at hNsmallU
      have h1 : B ≥ 1 := by
        rw [hBdef]
        have h2 : 0 ≤ 8 * Real.sqrt M := by positivity
        have h3 : 0 ≤ 1 + 4 * c' / c := by positivity
        nlinarith [mul_nonneg h2 h3]
      have h2 : θU / 48 < 1 := by linarith
      linarith
    · exact h
  refine ⟨1 + 32 * M ^ (N + 1), by positivity, ?_⟩
  intro A hA hA1 htrA hcq hcq' hYb Φ ε Λ hε hΛ hΦ heq hpos hpos0 hub h0 hsmallc hsmallε
  -- (A') the rate associated with the base `A`
  have htrCo : 0 ≤ trOp (cofOp A) := by
    rw [trOp_eq_sum]
    refine Finset.sum_nonneg fun i _ => ?_
    have h2 := hcq (stdB4 i)
    have h3 : ‖stdB4 i‖ = 1 := stdB4.orthonormal.1 i
    rw [h3] at h2
    nlinarith [h2, hc]
  have hYc : 0 ≤ 2 * trOp (cofOp A) / c := div_nonneg (by linarith [htrCo]) hc.le
  have hKt : (0 : ℝ) < 1 + (2 * trOp (cofOp A) / c + 3) := by linarith [hYc]
  set μ : ℝ := ((M - 1) / (8 * M)) ^ 4 / (1 + (2 * trOp (cofOp A) / c + 3)) ^ 4 with hμdef
  set θ : ℝ := μ / 5 ^ 4 with hθdef
  have hμpos : 0 < μ := by
    rw [hμdef]
    exact div_pos (pow_pos (div_pos (by linarith) (by positivity)) 4) (pow_pos hKt 4)
  have hμle1 : μ ≤ 1 := by
    have hX : ((M - 1) / (8 * M)) ^ 4 ≤ 1 := by
      have h2 : (M - 1) / (8 * M) ≤ 1 := by
        rw [div_le_one (by positivity : (0 : ℝ) < 8 * M)]; linarith
      calc ((M - 1) / (8 * M)) ^ 4 ≤ 1 ^ 4 := pow_le_pow_left₀ (by positivity) h2 4
        _ = 1 := by norm_num
    rw [hμdef, div_le_one (by positivity : (0 : ℝ) < (1 + (2 * trOp (cofOp A) / c + 3)) ^ 4)]
    exact le_trans hX (one_le_pow₀ (by linarith [hYc]))
  have hθpos : 0 < θ := by rw [hθdef]; positivity
  have hθlt : θ < 15 / 16 := by
    have h1 : ((M - 1) / (8 * M)) ^ 4 ≤ 1 / 4096 := by
      have h2 : (M - 1) / (8 * M) ≤ 1 / 8 := by
        rw [div_le_div_iff₀ (by positivity : (0 : ℝ) < 8 * M) (by norm_num : (0 : ℝ) < 8)]
        linarith
      have h3 : (0 : ℝ) ≤ (M - 1) / (8 * M) := by positivity
      calc ((M - 1) / (8 * M)) ^ 4 ≤ ((1 : ℝ) / 8) ^ 4 := pow_le_pow_left₀ h3 h2 4
        _ = 1 / 4096 := by norm_num
    have h4 : (1 : ℝ) ≤ (1 + (2 * trOp (cofOp A) / c + 3)) ^ 4 * 5 ^ 4 := by
      have h5 : (1 : ℝ) ≤ (1 + (2 * trOp (cofOp A) / c + 3)) ^ 4 :=
        one_le_pow₀ (by linarith [hYc])
      nlinarith [h5]
    have he : θ = ((M - 1) / (8 * M)) ^ 4 /
        ((1 + (2 * trOp (cofOp A) / c + 3)) ^ 4 * 5 ^ 4) := by
      rw [hθdef, hμdef, div_div]
    rw [he]
    have hX0 : (0 : ℝ) ≤ ((M - 1) / (8 * M)) ^ 4 := by positivity
    have h7 : ((M - 1) / (8 * M)) ^ 4 /
        ((1 + (2 * trOp (cofOp A) / c + 3)) ^ 4 * 5 ^ 4) ≤ ((M - 1) / (8 * M)) ^ 4 := by
      rw [div_le_iff₀ (by positivity)]
      nlinarith [hX0, h4]
    linarith [h1, h7]
  set r : ℝ := (1 - θ) ^ ((1 : ℝ) / 4) with hrdef
  have h1θpos : 0 < 1 - θ := by linarith
  have hrpos : 0 < r := Real.rpow_pos_of_pos h1θpos _
  have hr1 : r < 1 := by
    have h := Real.rpow_lt_one (show (0 : ℝ) ≤ 1 - θ by linarith)
      (show (1 : ℝ) - θ < 1 by linarith) (show (0 : ℝ) < 1 / 4 by norm_num)
    rw [hrdef]; exact h
  have hr4 : r ^ 4 = 1 - θ := by
    rw [hrdef, ← Real.rpow_natCast, ← Real.rpow_mul (by linarith : (0 : ℝ) ≤ 1 - θ)]
    norm_num
  have hrge : r ≤ 1 - θ / 4 := by
    have h := rpow_quarter_one_sub_le (t := θ) hθpos.le (by linarith : θ ≤ 1)
    rw [hrdef]; linarith
  -- comparison with the uniform rate
  have hKtle : 1 + (2 * trOp (cofOp A) / c + 3) ≤ 1 + (Y + 3) := by linarith [hYb]
  have hθUleθ : θU ≤ θ := by
    have hA4 : (0 : ℝ) ≤ ((M - 1) / (8 * M)) ^ 4 := by positivity
    have hPY : 0 < (1 + (Y + 3)) ^ 4 * 5 ^ 4 := by positivity
    have hPA : 0 < (1 + (2 * trOp (cofOp A) / c + 3)) ^ 4 * 5 ^ 4 := by positivity
    have hPYA : (1 + (2 * trOp (cofOp A) / c + 3)) ^ 4 * 5 ^ 4
        ≤ (1 + (Y + 3)) ^ 4 * 5 ^ 4 := by
      have h := pow_le_pow_left₀
        (by positivity : (0:ℝ) ≤ 1 + (2 * trOp (cofOp A) / c + 3)) hKtle 4
      nlinarith
    have hPAeq : ((M - 1) / (8 * M)) ^ 4 / (1 + (2 * trOp (cofOp A) / c + 3)) ^ 4 / 5 ^ 4
        = ((M - 1) / (8 * M)) ^ 4 / ((1 + (2 * trOp (cofOp A) / c + 3)) ^ 4 * 5 ^ 4) := by
      rw [div_div]
    rw [hθUdef, hθdef, hμdef, hPAeq, div_le_div_iff₀ hPY hPA]
    nlinarith [hA4, hPYA]
  have hrle : r ≤ rU := by
    rw [hrdef, hrUdef]
    exact Real.rpow_le_rpow (by linarith : (0:ℝ) ≤ 1 - θ) (by linarith [hθUleθ])
      (by norm_num : (0:ℝ) ≤ 1 / 4)
  have hNsmall : B * r ^ N < θ / 48 := by
    have h1 : B * r ^ N ≤ B * rU ^ N :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by linarith : (0:ℝ) ≤ r) hrle N) hBpos.le
    have h2 : θU / 48 ≤ θ / 48 := by linarith [hθUleθ]
    linarith
  have hkey : K₀ / 16 < η ^ 4 * B ^ 4 * (1 - θ) := by
    have h1 : K₀ * (1 - θ) ≤ η ^ 4 * B ^ 4 * (1 - θ) := by
      nlinarith [hB4, h1θpos]
    have h2 : K₀ / 16 < K₀ * (1 - θ) := by nlinarith [hK₀pos, hθlt]
    linarith
  have hgeom : ∀ k : ℕ, N ≤ k → ∑ j ∈ Finset.Ico N k, B * r ^ j ≤ 1 / 12 :=
    sum_Ico_pow_mul_le_tail hBpos.le hrpos.le hr1 hθpos hrge hNsmall

  -- (D) elementary consequences of the smallness hypotheses
  have h2p4 : (16 : ℝ) ≤ 2 ^ (2 * p + 4) := by
    have h1 : (2 : ℝ) ^ ((4 : ℝ)) ≤ 2 ^ (2 * p + 4) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
    have h2 : (2 : ℝ) ^ ((4 : ℝ)) = 16 := by norm_num
    linarith
  have hΛsmall : 12288 * Λ ≤ c := by
    have h1 : Λ * (768 * 2 ^ (2 * p + 4)) ≤ c := by
      rw [show Λ * (768 * 2 ^ (2 * p + 4)) = 768 * Λ * 2 ^ (2 * p + 4) from by ring]
      exact hsmallc
    have h2 : Λ * 12288 ≤ Λ * (768 * 2 ^ (2 * p + 4)) :=
      mul_le_mul_of_nonneg_left (by nlinarith [h2p4]) hΛ.le
    linarith [h1, h2]
  -- (E) the normalised function
  set φ : ℝ⁴ → ℝ := fun x => Φ x / ε with hφdef
  have hφ2 : ContDiffOn ℝ 2 φ (ball 0 (3 / 2)) := by
    have h1 : ContDiffOn ℝ 2 Φ (ball 0 (3 / 2)) :=
      hΦ.mono (ball_subset_ball (by norm_num))
    have h2 := h1.const_smul (ε⁻¹)
    have h3 : φ = fun x => ε⁻¹ • Φ x := by
      funext x
      simp only [hφdef, smul_eq_mul]
      ring
    rw [h3]
    exact h2
  have heqφ : ∀ x ∈ ball 0 (3 / 2), Fop (cofOp A) ε (hessOp φ x) = 0 := by
    intro x hx
    have hx52 : x ∈ ball 0 (5 / 2) := by
      rw [mem_ball] at hx ⊢; linarith
    have hcd : ContDiffAt ℝ 2 Φ x := hΦ.contDiffAt (isOpen_ball.mem_nhds hx52)
    have h1 : hessOp φ x = ε⁻¹ • hessOp Φ x := by
      rw [hφdef]; exact hessOp_div_const ε hcd
    rw [h1]
    refine fop_inv_smul_eq_zero hA (hessOp_symm_of_contDiffAt hcd) (ne_of_gt hε) ?_
    rw [heq x hx52, hA1]
  have hpos0φ : ∀ x ∈ closedBall 0 1, 0 ≤ φ x := by
    intro x hx
    have hx' : x ∈ ball 0 (5 / 2) := by
      rw [mem_closedBall] at hx; rw [mem_ball]; rw [dist_zero_right] at hx ⊢; linarith
    exact div_nonneg (hpos0 x hx') hε.le
  have hφ0 : φ 0 ≤ 1 := by
    rw [hφdef, div_le_one hε]; exact h0
  -- (F) the maximal level index
  have hKmaxex : ∃ k : ℕ, Λ < ε * (1 + 32 * M ^ (k + 1)) := by
    obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (Λ / ε / 32 + 1) hM1
    refine ⟨n, ?_⟩
    have h1 : Λ / ε / 32 < M ^ n := by linarith
    have h2 : Λ / ε < 32 * M ^ n := by
      have h3 : (Λ / ε / 32) * 32 < M ^ n * 32 :=
        mul_lt_mul_of_pos_right h1 (by norm_num : (0 : ℝ) < 32)
      have h4 : (Λ / ε / 32) * 32 = Λ / ε := div_mul_cancel₀ _ (by norm_num)
      linarith [h3, h4]
    have h5 : Λ < ε * (32 * M ^ n) := by
      have h6 : (Λ / ε) * ε < (32 * M ^ n) * ε := mul_lt_mul_of_pos_right h2 hε
      rw [div_mul_cancel₀ _ (ne_of_gt hε)] at h6
      linarith [h6]
    have h7 : ε * (32 * M ^ n) ≤ ε * (1 + 32 * M ^ (n + 1)) := by
      have h8 : M ^ n ≤ M ^ (n + 1) := by
        rw [pow_succ]; exact le_mul_of_one_le_right (pow_nonneg hMpos.le n) hM1.le
      nlinarith [h8, hε]
    linarith
  set Kmax : ℕ := Nat.find hKmaxex with hKmaxdef
  have hKmax : Λ < ε * (1 + 32 * M ^ (Kmax + 1)) := Nat.find_spec hKmaxex
  have hKmaxmin : ∀ k : ℕ, k < Kmax → ε * (1 + 32 * M ^ (k + 1)) ≤ Λ := by
    intro k hk
    by_contra hcon
    push_neg at hcon
    exact Nat.find_min hKmaxex hk hcon
  -- (G) the concluding argument
  intro x hx
  by_contra hcon
  push_neg at hcon
  have hφx : 1 + 32 * M ^ (N + 1) < φ x := by
    change 1 + 32 * M ^ (N + 1) < Φ x / ε
    rw [lt_div_iff₀ hε]
    exact hcon
  rcases le_or_gt ε Λ with hεΛ | hΛε
  · -- the main case `ε ≤ Λ`
    have hΛ3 : 3 * Λ ≤ c / 2 := by nlinarith [hΛsmall, hΛ]
    have hε48 : 3 * ε * 16 ≤ c / 2 := by nlinarith [hΛsmall, hεΛ, hε]
    have hεM : 3 * ε * (M * 16) ≤ c / 2 := by nlinarith [hsmallε, hε, hMpos]
    have hε16 : 48 * ε * 16 * 2 ^ (2 * p + 4) ≤ c := by
      have h1 : 48 * ε * 16 * 2 ^ (2 * p + 4) ≤ 768 * Λ * 2 ^ (2 * p + 4) := by
        have h2 : 48 * ε * 16 ≤ 768 * Λ := by nlinarith [hεΛ]
        exact mul_le_mul_of_nonneg_right h2 (by positivity)
      linarith [hsmallc]
    -- the base estimate for the decay lemma
    have hbase : volume (closedBall (0 : ℝ⁴) (1 / 2) \ contactPt (16 * M) φ) ≤
        ENNReal.ofReal (1 - (((M - 1) / (8 * M)) ^ 4 /
          (1 + (2 * trOp (cofOp A) / c + 3)) ^ 4))
          * volume (closedBall (0 : ℝ⁴) (1 / 2)) := by
      have hdens := density_contactPt hφ2 (cofOp_isSymmetric hA) hc hcq hε heqφ hε48 hpos0φ
        ⟨0, by simp, hφ0⟩
      have hne : (contactPt 16 φ ∩ ball (0 : ℝ⁴) (1 / 2)).Nonempty := by
        have h1 : (0 : ℝ≥0∞) < ENNReal.ofReal ((1 / 8 : ℝ) ^ 4 /
            (1 + (2 * trOp (cofOp A) / c + 3)) ^ 4) :=
          ENNReal.ofReal_pos.mpr (div_pos (by norm_num) (pow_pos hKt 4))
        have h2 : (0 : ℝ≥0∞) < volume (closedBall (0 : ℝ⁴) (1 / 2)) := by
          rw [Measure.addHaar_closedBall_eq_addHaar_ball]
          exact measure_ball_pos volume 0 (by norm_num)
        have hpos : 0 < volume (contactPt 16 φ ∩ closedBall (0 : ℝ⁴) (1 / 2)) :=
          lt_of_lt_of_le (ENNReal.mul_pos (ne_of_gt h1) (ne_of_gt h2)) hdens
        have hpos' : 0 < volume (contactPt 16 φ ∩ ball (0 : ℝ⁴) (1 / 2)) := by
          rwa [← volume_inter_closedBall]
        exact nonempty_of_measure_ne_zero (ne_of_gt hpos')
      obtain ⟨x₁, hx₁T, hx₁ball⟩ := hne
      have henl := enlarge_opening hφ2 (cofOp_isSymmetric hA) hc hcq hcq' hε heqφ
        (by norm_num : (0 : ℝ) < 16) hp (by norm_num : (0 : ℝ) < 1 / 2) hM1 hM hpbig
        hε16 hεM hx₁T hx₁ball
        (by intro z hz; rw [mem_closedBall] at hz; rw [mem_ball]
            rw [dist_zero_right] at hz ⊢; linarith)
        (by intro z hz; exact hz)
      have hcl : IsClosed (contactPt (16 * M) φ) :=
        isClosed_contactPt ((hφ2.of_le (m := 1) (by norm_num)).mono
          (ball_subset_ball (by norm_num)))
      have hsub : contactPt (16 * M) φ ⊆ closedBall (0 : ℝ⁴) (1 / 2) :=
        contactPt_subset_closedBall
      have hfin : volume (closedBall (0 : ℝ⁴) (1 / 2)) ≠ ⊤ := by
        rw [Measure.addHaar_closedBall_eq_addHaar_ball]
        exact measure_ball_lt_top.ne
      have hfinT : volume (contactPt (16 * M) φ) ≠ ⊤ :=
        ne_top_of_le_ne_top hfin (measure_mono hsub)
      have hms : volume (closedBall (0 : ℝ⁴) (1 / 2) \ contactPt (16 * M) φ)
          = volume (closedBall (0 : ℝ⁴) (1 / 2)) - volume (contactPt (16 * M) φ) :=
        measure_sdiff hsub hcl.nullMeasurableSet hfinT
      have henl' : ENNReal.ofReal μ * volume (closedBall (0 : ℝ⁴) (1 / 2))
          ≤ volume (contactPt (16 * M) φ) := by
        have h3 : (M : ℝ) * 16 = 16 * M := by ring
        rw [h3] at henl
        have heq2 : contactPt (16 * M) φ ∩ closedBall (0 : ℝ⁴) (1 / 2)
            = contactPt (16 * M) φ := by
          ext y; exact ⟨fun h => h.1, fun h => ⟨h, contactPt_subset_closedBall h⟩⟩
        rw [heq2] at henl
        rw [← hμdef] at henl
        exact henl
      have hsum : ENNReal.ofReal μ * volume (closedBall (0 : ℝ⁴) (1 / 2))
          + ENNReal.ofReal (1 - μ) * volume (closedBall (0 : ℝ⁴) (1 / 2))
          = volume (closedBall (0 : ℝ⁴) (1 / 2)) := by
        rw [← add_mul, ← ENNReal.ofReal_add hμpos.le (by linarith),
          show μ + (1 - μ) = 1 by ring, ENNReal.ofReal_one, one_mul]
      rw [hms, tsub_le_iff_right, add_comm]
      calc volume (closedBall (0 : ℝ⁴) (1 / 2))
          = ENNReal.ofReal μ * volume (closedBall (0 : ℝ⁴) (1 / 2))
            + ENNReal.ofReal (1 - μ) * volume (closedBall (0 : ℝ⁴) (1 / 2)) := hsum.symm
        _ ≤ volume (contactPt (16 * M) φ)
            + ENNReal.ofReal (1 - μ) * volume (closedBall (0 : ℝ⁴) (1 / 2)) :=
            add_le_add henl' le_rfl
    -- the decay estimate on superlevel sets
    have hdec : ∀ j : ℕ, j < Kmax →
        volume ({x : ℝ⁴ | 1 + 32 * M ^ (j + 1) < φ x} ∩ closedBall 0 (1 / 2)) ≤
          ENNReal.ofReal ((1 - θ) ^ j) * volume (closedBall (0 : ℝ⁴) (1 / 2)) := by
      intro j hj
      have hlv : ε * (16 * M ^ (j + 1)) ≤ Λ := by
        have h2 : 16 * M ^ (j + 1) ≤ 1 + 32 * M ^ (j + 1) := by
          have hpj := pow_pos hMpos (j + 1); linarith
        exact le_trans (by nlinarith [h2, hε]) (hKmaxmin j hj)
      have hbig : 48 * ε * ((16 * M) * M ^ j) * 2 ^ (2 * p + 4) ≤ c := by
        have h1 : (16 * M) * M ^ j = 16 * M ^ (j + 1) := by rw [pow_succ']; ring
        rw [h1]
        have h4 : 48 * ε * (16 * M ^ (j + 1)) * 2 ^ (2 * p + 4)
            ≤ 48 * Λ * 2 ^ (2 * p + 4) := by
          have h5 : (0 : ℝ) ≤ 2 ^ (2 * p + 4) := by positivity
          nlinarith [hlv, h5]
        have h6 : 48 * Λ * 2 ^ (2 * p + 4) ≤ 768 * Λ * 2 ^ (2 * p + 4) := by
          have h7 : (0 : ℝ) ≤ Λ * 2 ^ (2 * p + 4) := by positivity
          nlinarith [h7]
        linarith [hsmallc, h4, h6]
      have hbig' : 3 * ε * ((16 * M) * M ^ j) ≤ c / 2 := by
        have h1 : (16 * M) * M ^ j = 16 * M ^ (j + 1) := by rw [pow_succ']; ring
        rw [h1]
        have h4 : 3 * ε * (16 * M ^ (j + 1)) ≤ 3 * Λ := by nlinarith [hlv]
        linarith [h4, hΛ3]
      have hdec0 := decay_contactPt hφ2 (cofOp_isSymmetric hA) hc hcq hcq' hε heqφ
        (by positivity : (0 : ℝ) < 16 * M) hp hM1 hM hpbig (K := j) hbig hbig' hbase
      have hset : {x : ℝ⁴ | 1 + 32 * M ^ (j + 1) < φ x} ∩ closedBall (0 : ℝ⁴) (1 / 2)
          ⊆ closedBall (0 : ℝ⁴) (1 / 2) \ contactPt ((16 * M) * M ^ j) φ := by
        intro y hy
        obtain ⟨hy1, hy2⟩ := hy
        refine ⟨hy2, fun hyT => ?_⟩
        have h1 : (16 * M) * M ^ j = 16 * M ^ (j + 1) := by rw [pow_succ']; ring
        have hy1' : 1 + 32 * M ^ (j + 1) < φ y := hy1
        have h2 : φ y ≤ 1 + 2 * (16 * M ^ (j + 1)) :=
          contactPt_le_value (a := 16 * M ^ (j + 1)) (by positivity) (φ := φ)
            (x₁ := (0 : ℝ⁴)) (by simp) hφ0 (h1 ▸ hyT)
        have h4 : 1 + 2 * (16 * M ^ (j + 1)) = 1 + 32 * M ^ (j + 1) := by ring
        linarith [h2, h4, hy1']
      have hθ' : (1 : ℝ) - (((M - 1) / (8 * M)) ^ 4 /
          ((1 + (2 * trOp (cofOp A) / c + 3)) ^ 4 * 5 ^ 4)) = 1 - θ := by
        rw [hθdef, hμdef, div_div]
      rw [hθ'] at hdec0
      exact le_trans (measure_mono hset) hdec0
    -- the chain of growing levels
    have hchain : ∀ k : ℕ, N ≤ k → k ≤ Kmax →
        ∃ y ∈ closedBall (0 : ℝ⁴) (1 / 6 + ∑ j ∈ Finset.Ico N k, B * r ^ j),
          1 + 32 * M ^ (k + 1) ≤ φ y := by
      intro k hNk
      induction k, hNk using Nat.le_induction with
      | base =>
        intro _
        refine ⟨x, ?_, le_of_lt hφx⟩
        rw [mem_closedBall, dist_zero_right]
        have hh : ∑ j ∈ Finset.Ico N N, B * r ^ j = 0 := by simp
        rw [hh]
        have h1 : ‖x‖ ≤ 1 / 6 := by
          have := hx; rw [mem_closedBall, dist_zero_right] at this; exact this
        linarith
      | succ k hNk ih =>
        intro hkK
        obtain ⟨xk, hxkmem, hxkle⟩ := ih (by omega)
        set bk : ℝ := B * r ^ k with hbkdef
        have hbkpos : 0 < bk := by rw [hbkdef]; positivity
        have hbk48 : bk ≤ θ / 48 := by
          rw [hbkdef]
          have h1 : r ^ k ≤ r ^ N := pow_le_pow_of_le_one hrpos.le (le_of_lt hr1) hNk
          nlinarith [hNsmall, hBpos, h1]
        have hxknorm : ‖xk‖ ≤ 1 / 6 + ∑ j ∈ Finset.Ico N k, B * r ^ j := by
          simpa [mem_closedBall, dist_zero_right] using hxkmem
        have hSum : ∑ j ∈ Finset.Ico N k, B * r ^ j ≤ 1 / 12 := hgeom k hNk
        have hxkle1 : ‖xk‖ ≤ 1 / 4 := by linarith
        have hb3 : ball xk (3 * bk / 2) ⊆ ball 0 (5 / 2) := by
          intro z hz
          rw [mem_ball] at hz
          rw [mem_ball, dist_zero_right]
          have h1 : ‖z‖ ≤ ‖z - xk‖ + ‖xk‖ := by
            calc ‖z‖ = ‖(z - xk) + xk‖ := by rw [sub_add_cancel]
              _ ≤ ‖z - xk‖ + ‖xk‖ := norm_add_le _ _
          have h2 : ‖z - xk‖ < 3 * bk / 2 := by rwa [dist_eq_norm] at hz
          linarith
        have hΦloc : ContDiffOn ℝ 2 Φ (ball xk (3 * bk / 2)) := hΦ.mono hb3
        have heqloc : ∀ z ∈ ball xk (3 * bk / 2), s2 (A + hessOp Φ z) = 1 :=
          fun z hz => heq z (hb3 hz)
        have hposloc : ∀ z ∈ ball xk (3 * bk / 2), 0 < trOp (A + hessOp Φ z) :=
          fun z hz => hpos z (hb3 hz)
        by_cases hcase : ∃ z ∈ closedBall xk bk, M * (ε * (1 + 32 * M ^ (k + 1))) < Φ z
        · obtain ⟨z, hzmem, hzgt⟩ := hcase
          refine ⟨z, ?_, ?_⟩
          · rw [mem_closedBall, dist_zero_right]
            have h1 : ‖z - xk‖ ≤ bk := by
              have := hzmem; rw [mem_closedBall, dist_eq_norm] at this; exact this
            have h2 : ∑ j ∈ Finset.Ico N (k + 1), B * r ^ j
                = (∑ j ∈ Finset.Ico N k, B * r ^ j) + B * r ^ k :=
              Finset.sum_Ico_succ_top hNk (fun j => B * r ^ j)
            have h3 : B * r ^ k = bk := hbkdef.symm
            have h4 : ‖z‖ ≤ ‖z - xk‖ + ‖xk‖ := by
              calc ‖z‖ = ‖(z - xk) + xk‖ := by rw [sub_add_cancel]
                _ ≤ ‖z - xk‖ + ‖xk‖ := norm_add_le _ _
            rw [h2, h3]; linarith
          · change 1 + 32 * M ^ (k + 2) ≤ Φ z / ε
            rw [le_div_iff₀ hε]
            have harith := harnack_arith_grow (M := M) (ε := ε) hM1 hε k
            linarith [harith, hzgt]
        · push_neg at hcase
          exfalso
          have hHpos : 0 < ε * (1 + 32 * M ^ (k + 1)) := by positivity
          have hH : ε * (1 + 32 * M ^ (k + 1)) ≤ Φ xk := by
            have h' : (1 + 32 * M ^ (k + 1)) ≤ Φ xk / ε := hxkle
            rw [le_div_iff₀ hε] at h'
            nlinarith [h']
          have hprop := propagation_step hA hA1 htrA hbkpos hM4 hHpos hηpos hη16 hηlev
            hΦloc heqloc hposloc hc hcq hcq' hH hcase
          have hsub2 : closedBall xk (bk / 2) ⊆ closedBall (0 : ℝ⁴) (1 / 2) := by
            intro z hz
            rw [mem_closedBall, dist_zero_right]
            have hz' : ‖z - xk‖ ≤ bk / 2 := by
              have := hz; rw [mem_closedBall, dist_eq_norm] at this; exact this
            have h1 : ‖z‖ ≤ ‖z - xk‖ + ‖xk‖ := by
              calc ‖z‖ = ‖(z - xk) + xk‖ := by rw [sub_add_cancel]
                _ ≤ ‖z - xk‖ + ‖xk‖ := norm_add_le _ _
            linarith
          have harith := harnack_arith_level hM4 hε k
          have hk1 : k - 1 + 1 = k :=
            Nat.succ_pred_eq_of_pos (lt_of_lt_of_le Nat.zero_lt_one (le_trans hNge1 hNk))
          have hsub3 : {z : ℝ⁴ | 2 * (ε * (1 + 32 * M ^ (k + 1))) / M ≤ Φ z}
              ⊆ {z : ℝ⁴ | 1 + 32 * M ^ (k - 1 + 1) < φ z} := by
            intro z hz
            rw [hk1]
            change 1 + 32 * M ^ k < Φ z / ε
            rw [lt_div_iff₀ hε]
            have hz2 : 2 * (ε * (1 + 32 * M ^ (k + 1))) / M ≤ Φ z := hz
            linarith [hz2, harith]
          have hdecsub : volume ({z : ℝ⁴ | 2 * (ε * (1 + 32 * M ^ (k + 1))) / M ≤ Φ z}
              ∩ closedBall xk (bk / 2))
              ≤ ENNReal.ofReal ((1 - θ) ^ (k - 1)) * volume (closedBall (0 : ℝ⁴) (1 / 2)) :=
            le_trans (measure_mono (Set.inter_subset_inter hsub3 hsub2))
              (hdec (k - 1) (by omega))
          have hmul : ENNReal.ofReal (K₀ * ((1 - θ) ^ (k - 1) * (1 / 2) ^ 4))
              = ENNReal.ofReal K₀ * ENNReal.ofReal ((1 - θ) ^ (k - 1))
                * ENNReal.ofReal ((1 / 2 : ℝ) ^ 4) := by
            rw [ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ K₀),
              ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ (1 - θ) ^ (k - 1))]
            ring
          have h3 : ENNReal.ofReal ((η * bk) ^ 4) * volume (closedBall (0 : ℝ⁴) 1)
              ≤ ENNReal.ofReal (K₀ * ((1 - θ) ^ (k - 1) * (1 / 2) ^ 4))
                * volume (closedBall (0 : ℝ⁴) 1) := by
            calc ENNReal.ofReal ((η * bk) ^ 4) * volume (closedBall (0 : ℝ⁴) 1)
                = volume (closedBall xk (η * bk)) :=
                  (volume_closedBall_eq xk (by positivity : (0 : ℝ) < η * bk)).symm
              _ ≤ ENNReal.ofReal K₀ * volume ({z : ℝ⁴ |
                      2 * (ε * (1 + 32 * M ^ (k + 1))) / M ≤ Φ z}
                    ∩ closedBall xk (bk / 2)) := hprop
              _ ≤ ENNReal.ofReal K₀ * (ENNReal.ofReal ((1 - θ) ^ (k - 1))
                    * volume (closedBall (0 : ℝ⁴) (1 / 2))) :=
                  mul_le_mul_of_nonneg_left hdecsub (by simp)
              _ = ENNReal.ofReal (K₀ * ((1 - θ) ^ (k - 1) * (1 / 2) ^ 4))
                    * volume (closedBall (0 : ℝ⁴) 1) := by
                  rw [hmul, volume_closedBall_eq 0 (by norm_num : (0 : ℝ) < 1 / 2)]
                  ring
          have h4 : ENNReal.ofReal ((η * bk) ^ 4)
              ≤ ENNReal.ofReal (K₀ * ((1 - θ) ^ (k - 1) * (1 / 2) ^ 4)) :=
            (ENNReal.mul_le_mul_iff_right volume_unit_closedBall_ne_zero
              volume_unit_closedBall_ne_top).mp (by
                rw [mul_comm (ENNReal.ofReal ((η * bk) ^ 4)) (volume (closedBall (0 : ℝ⁴) 1)),
                  mul_comm (ENNReal.ofReal (K₀ * ((1 - θ) ^ (k - 1) * (1 / 2) ^ 4)))
                    (volume (closedBall (0 : ℝ⁴) 1))] at h3
                exact h3)
          have h5 : (η * bk) ^ 4 ≤ K₀ * ((1 - θ) ^ (k - 1) * (1 / 2) ^ 4) :=
            (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp h4
          have h6 : K₀ * ((1 - θ) ^ (k - 1) * (1 / 2) ^ 4) < (η * bk) ^ 4 := by
            have h1θ : 0 < (1 - θ) ^ (k - 1) := pow_pos h1θpos _
            have h2 : (η * bk) ^ 4 = η ^ 4 * B ^ 4 * (1 - θ) ^ k := by
              have hpk : (r ^ k) ^ 4 = (r ^ 4) ^ k := by
                rw [← pow_mul r k 4, show k * 4 = 4 * k from by ring, pow_mul r 4 k]
              rw [hbkdef, mul_pow, mul_pow, hpk, hr4]
              ring
            rw [h2]
            have h3' : (1 - θ) ^ k = (1 - θ) ^ (k - 1) * (1 - θ) := by
              conv_lhs => rw [← hk1]
              rw [pow_succ]
            rw [h3']
            have e1 : K₀ * ((1 - θ) ^ (k - 1) * (1 / 2) ^ 4) = (K₀ / 16) * (1 - θ) ^ (k - 1) :=
              by ring
            have e2 : η ^ 4 * B ^ 4 * ((1 - θ) ^ (k - 1) * (1 - θ))
                = η ^ 4 * B ^ 4 * (1 - θ) * (1 - θ) ^ (k - 1) := by ring
            rw [e1, e2]
            exact mul_lt_mul_of_pos_right hkey h1θ
          linarith
    by_cases hNK : N ≤ Kmax
    · obtain ⟨y, hymem, hyle⟩ := hchain Kmax hNK le_rfl
      have hy4 : ‖y‖ ≤ 1 / 4 := by
        have h1 : ‖y‖ ≤ 1 / 6 + ∑ j ∈ Finset.Ico N Kmax, B * r ^ j := by
          simpa [mem_closedBall, dist_zero_right] using hymem
        have h2 : ∑ j ∈ Finset.Ico N Kmax, B * r ^ j ≤ 1 / 12 := hgeom Kmax hNK
        linarith
      have hyb : y ∈ ball 0 (5 / 2) := by rw [mem_ball, dist_zero_right]; linarith
      have h1 : ε * (1 + 32 * M ^ (Kmax + 1)) ≤ Φ y := by
        change (1 + 32 * M ^ (Kmax + 1)) ≤ Φ y / ε at hyle
        rw [le_div_iff₀ hε] at hyle
        linarith [hyle]
      have h2 := hub y hyb
      linarith [hKmax, h1, h2]
    · push_neg at hNK
      have hx' : x ∈ ball 0 (5 / 2) := by
        rw [mem_closedBall] at hx; rw [mem_ball]; rw [dist_zero_right] at hx ⊢; linarith
      have h1 := hub x hx'
      have h2 : M ^ (Kmax + 1) ≤ M ^ (N + 1) := pow_le_pow_right₀ hM1.le (by omega)
      have h3 : ε * (1 + 32 * M ^ (Kmax + 1)) ≤ ε * (1 + 32 * M ^ (N + 1)) := by
        nlinarith [h2, hε]
      have h4 : ε * (1 + 32 * M ^ (N + 1)) < Φ x := by nlinarith [hcon]
      linarith [hKmax, h3, h4, h1]
  · -- the trivial case `Λ < ε`
    exfalso
    have hx' : x ∈ ball 0 (5 / 2) := by
      rw [mem_closedBall] at hx; rw [mem_ball]; rw [dist_zero_right] at hx ⊢; linarith
    have h1 := hub x hx'
    have h2 : ε ≤ ε * (1 + 32 * M ^ (N + 1)) := by
      have hMp : (0 : ℝ) ≤ 32 * M ^ (N + 1) := by positivity
      nlinarith [hε, hMp]
    have h3 : ε * (1 + 32 * M ^ (N + 1)) < Φ x := by nlinarith [hcon]
    linarith [h1, h2, h3, hΛε]

end

end Submission
