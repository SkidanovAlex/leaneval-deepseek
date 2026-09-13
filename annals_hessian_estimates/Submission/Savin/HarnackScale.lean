/-
# The scale-invariant (localised) Harnack inequality

`Submission.Savin.HarnackIneq.harnack` is stated on the fixed ball `ball 0 (5/2)` with the
normalisation `Φ 0 ≤ ε`.  For the oscillation/`C^{2,α}` iteration (Savin's Corollary 1.2,
Corollary 3.3, Proposition 4.1) one needs the *same* statement at an arbitrary centre `x₀` and
scale `R`, i.e.

  *(H_R)*  `Φ` a nonnegative solution of `s2 (A + D²Φ) = 1` with `trOp (A + D²Φ) > 0` on
  `ball x₀ (5R/2)`, `Φ ≤ Λ` there, `Φ x₀ ≤ ε`, with `768 Λ 2^{2p+4} ≤ c R²` and
  `1536 ε M ≤ c R²`, satisfies `Φ ≤ C ε` on `closedBall x₀ (R/6)`.

Since the equation `s2 (A + D²Φ) = 1` is invariant under `y ↦ x₀ + R • y` (the Hessian is
unchanged), *(H_R)* follows from `harnack` applied to `y ↦ Φ (x₀ + R • y) / R²`.  This is the
form in which Harnack will be iterated.
-/
import Mathlib
import ChallengeDeps
import Submission.Savin.HarnackIneq

open Metric MeasureTheory Filter
open scoped BigOperators RealInnerProductSpace Topology ENNReal Pointwise

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 4000000

namespace Submission

local notation "ℝ⁴" => EuclideanSpace ℝ (Fin 4)

noncomputable section

/-- Membership in a ball is preserved by an affine scaling about the centre. -/
theorem mem_ball_affine {x₀ z : ℝ⁴} {R : ℝ} (hR : 0 < R) :
    x₀ + R • z ∈ ball x₀ (5 * R / 2) ↔ z ∈ ball 0 (5 / 2) := by
  rw [mem_ball, mem_ball, dist_eq_norm, dist_zero_right, add_sub_cancel_left, norm_smul,
    Real.norm_eq_abs, abs_of_pos hR]
  constructor <;> intro h <;> nlinarith [hR]

/-- The Hessian of `y ↦ Φ (x₀ + R • y)` equals `R² •` the Hessian of `Φ` at the image point; hence
the *normalised* function `y ↦ Φ (x₀ + R • y)/R²` has Hessian exactly `hessOp Φ (x₀ + R • y)`. -/
theorem hessOp_comp_affine_div {Φ : ℝ⁴ → ℝ} {x₀ x : ℝ⁴} {R : ℝ} (hR : 0 < R)
    (hcd : ContDiffAt ℝ 2 Φ (x₀ + R • x)) :
    hessOp (fun y => Φ (x₀ + R • y) / R ^ 2) x = hessOp Φ (x₀ + R • x) := by
  have hcdaff : ContDiffAt ℝ 2 (fun z : ℝ⁴ => Φ (x₀ + R • z)) x :=
    hcd.comp x ((contDiffAt_const (c := x₀)).add (contDiffAt_id.const_smul R))
  have h1 : hessOp (fun y => Φ (x₀ + R • y) / R ^ 2) x
      = (R ^ 2)⁻¹ • hessOp (fun z => Φ (x₀ + R • z)) x := hessOp_div_const (R ^ 2) hcdaff
  have h2 : hessOp (fun z : ℝ⁴ => Φ (x₀ + R • z)) x = (R * R) • hessOp Φ (x₀ + R • x) :=
    hessOp_comp_affine hcd
  have h3 : (R ^ 2)⁻¹ * (R * R) = 1 := by
    field_simp
  rw [h1, h2, smul_smul, h3, one_smul]

/-- **The scale-invariant Harnack inequality**, UNIFORM in the base: the constant depends on
`A` only through the bound `2 trOp (cofOp A) / c ≤ Y`. -/
theorem harnack_scaled_uniform {c c' Y p M : ℝ} (hc : 0 < c) (hc'pos : 0 < c') (hYnn : 0 ≤ Y)
    (hp : 0 < p) (hM1 : 1 < M) (hM : M = 1 + 128 * ((1 / p) * (2 ^ p - 1)))
    (hpbig : 16 * c' / c + 2 ≤ p) :
    ∃ C : ℝ, 0 < C ∧ ∀ (A : ℝ⁴ →L[ℝ] ℝ⁴) (hA : A.IsSymmetric) (hA1 : s2 A = 1)
      (htrA : 0 < trOp A) (hcq : ∀ v : ℝ⁴, c * ‖v‖ ^ 2 ≤ ⟪cofOp A v, v⟫)
      (hcq' : ∀ v : ℝ⁴, ⟪cofOp A v, v⟫ ≤ c' * ‖v‖ ^ 2)
      (hYb : 2 * trOp (cofOp A) / c ≤ Y)
      (Φ : ℝ⁴ → ℝ) (x₀ : ℝ⁴) (R ε Λ : ℝ), 0 < R → 0 < ε → 0 < Λ →
      ContDiffOn ℝ 2 Φ (ball x₀ (5 * R / 2)) →
      (∀ x ∈ ball x₀ (5 * R / 2), s2 (A + hessOp Φ x) = 1) →
      (∀ x ∈ ball x₀ (5 * R / 2), 0 < trOp (A + hessOp Φ x)) →
      (∀ x ∈ ball x₀ (5 * R / 2), 0 ≤ Φ x) → (∀ x ∈ ball x₀ (5 * R / 2), Φ x ≤ Λ) →
      Φ x₀ ≤ ε →
      768 * Λ * 2 ^ (2 * p + 4) ≤ c * R ^ 2 → 1536 * ε * M ≤ c * R ^ 2 →
      ∀ y ∈ closedBall x₀ (R / 6), Φ y ≤ C * ε := by
  obtain ⟨C, hCpos, hC⟩ := harnack_uniform (Y := Y) hc hc'pos hYnn hp hM1 hM hpbig
  refine ⟨C, hCpos, ?_⟩
  intro A hA hA1 htrA hcq hcq' hYb Φ x₀ R ε Λ hR hε hΛ hΦ heq hpos hpos0 hub h0 hsmallc hsmallε
  set Ψ : ℝ⁴ → ℝ := fun y => Φ (x₀ + R • y) / R ^ 2 with hΨdef
  have hR2 : (0 : ℝ) < R ^ 2 := by positivity
  have hne : R ^ 2 ≠ 0 := ne_of_gt hR2
  -- the rescaled function is `C²` and solves the (unchanged) equation
  have hΨ2 : ContDiffOn ℝ 2 Ψ (ball 0 (5 / 2)) := by
    have hinner : ContDiffOn ℝ 2 (fun y : ℝ⁴ => x₀ + R • y) (ball 0 (5 / 2)) :=
      (contDiff_const.add (contDiff_id.const_smul R)).contDiffOn
    have hmap : Set.MapsTo (fun y : ℝ⁴ => x₀ + R • y) (ball 0 (5 / 2))
        (ball x₀ (5 * R / 2)) := fun y hy => (mem_ball_affine hR).mpr hy
    have h1 : ContDiffOn ℝ 2 (fun y : ℝ⁴ => Φ (x₀ + R • y)) (ball 0 (5 / 2)) :=
      hΦ.comp hinner hmap
    have h2 := h1.const_smul ((R ^ 2)⁻¹)
    have h3 : Ψ = fun y => (R ^ 2)⁻¹ • Φ (x₀ + R • y) := by
      funext y
      simp only [hΨdef, smul_eq_mul]
      rw [div_eq_inv_mul]
    rw [h3]
    exact h2
  have hhess : ∀ y ∈ ball 0 (5 / 2), hessOp Ψ y = hessOp Φ (x₀ + R • y) := by
    intro y hy
    have hy' : x₀ + R • y ∈ ball x₀ (5 * R / 2) := (mem_ball_affine hR).mpr hy
    have hcd : ContDiffAt ℝ 2 Φ (x₀ + R • y) := hΦ.contDiffAt (isOpen_ball.mem_nhds hy')
    have h1 : Ψ = fun z => Φ (x₀ + R • z) / R ^ 2 := hΨdef
    rw [h1]
    exact hessOp_comp_affine_div hR hcd
  have heqΨ : ∀ y ∈ ball 0 (5 / 2), s2 (A + hessOp Ψ y) = 1 := by
    intro y hy
    rw [hhess y hy]
    exact heq _ ((mem_ball_affine hR).mpr hy)
  have hposΨ : ∀ y ∈ ball 0 (5 / 2), 0 < trOp (A + hessOp Ψ y) := by
    intro y hy
    rw [hhess y hy]
    exact hpos _ ((mem_ball_affine hR).mpr hy)
  have hpos0Ψ : ∀ y ∈ ball 0 (5 / 2), 0 ≤ Ψ y := by
    intro y hy
    have hy' : x₀ + R • y ∈ ball x₀ (5 * R / 2) := (mem_ball_affine hR).mpr hy
    exact div_nonneg (hpos0 _ hy') hR2.le
  have hΨ0 : Ψ 0 ≤ ε / R ^ 2 := by
    have h1 : Ψ 0 = Φ (x₀ + R • 0) / R ^ 2 := by
      simp only [hΨdef, smul_zero, add_zero]
    rw [h1]
    exact div_le_div_of_nonneg_right (by simpa using h0) hR2.le
  have hsupΨ : ∀ y ∈ ball 0 (5 / 2), Ψ y ≤ Λ / R ^ 2 := by
    intro y hy
    have hy' : x₀ + R • y ∈ ball x₀ (5 * R / 2) := (mem_ball_affine hR).mpr hy
    have h1 : Ψ y = Φ (x₀ + R • y) / R ^ 2 := by
      simp only [hΨdef]
    rw [h1]
    exact div_le_div_of_nonneg_right (hub _ hy') hR2.le
  have hsc : 768 * (Λ / R ^ 2) * 2 ^ (2 * p + 4) ≤ c := by
    rw [div_eq_mul_inv]
    rw [show 768 * (Λ * (R ^ 2)⁻¹) * 2 ^ (2 * p + 4)
        = (768 * Λ * 2 ^ (2 * p + 4)) * (R ^ 2)⁻¹ from by ring]
    rw [mul_inv_le_iff₀ hR2]
    linarith [hsmallc]
  have hse : 1536 * (ε / R ^ 2) * M ≤ c := by
    rw [div_eq_mul_inv]
    rw [show 1536 * (ε * (R ^ 2)⁻¹) * M = (1536 * ε * M) * (R ^ 2)⁻¹ from by ring]
    rw [mul_inv_le_iff₀ hR2]
    linarith [hsmallε]
  have hΛ2 : 0 < Λ / R ^ 2 := div_pos hΛ hR2
  have hε2 : 0 < ε / R ^ 2 := div_pos hε hR2
  have hmain := hC A hA hA1 htrA hcq hcq' hYb Ψ (ε / R ^ 2) (Λ / R ^ 2) hε2 hΛ2 hΨ2 heqΨ
    hposΨ hpos0Ψ hsupΨ hΨ0 hsc hse
  -- translate back
  intro y hy
  have hy' : ‖y - x₀‖ ≤ R / 6 := by simpa [mem_closedBall, dist_eq_norm] using hy
  have hyball : y ∈ ball x₀ (5 * R / 2) := by
    rw [mem_ball, dist_eq_norm]; linarith
  have htarget : x₀ + R • (R⁻¹ • (y - x₀)) = y := by
    rw [smul_smul, mul_inv_cancel₀ (ne_of_gt hR), one_smul, add_sub_cancel]
  have hz : R⁻¹ • (y - x₀) ∈ closedBall (0 : ℝ⁴) (1 / 6) := by
    rw [mem_closedBall, dist_zero_right, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hR),
      inv_mul_le_iff₀ hR]
    linarith
  have hval : Ψ (R⁻¹ • (y - x₀)) ≤ C * (ε / R ^ 2) := hmain _ hz
  have hΨy : Ψ (R⁻¹ • (y - x₀)) = Φ y / R ^ 2 := by
    simp only [hΨdef]
    rw [htarget]
  rw [hΨy] at hval
  have hmul := mul_le_mul_of_nonneg_right hval hR2.le
  rw [div_mul_cancel₀ (Φ y) hne] at hmul
  rw [show C * (ε / R ^ 2) * R ^ 2 = C * ε from by rw [mul_assoc, div_mul_cancel₀ ε hne]] at hmul
  exact hmul

/-- **The scale-invariant Harnack inequality.**  `harnack` at the centre `x₀` and scale `R`. -/
theorem harnack_scaled {A : ℝ⁴ →L[ℝ] ℝ⁴} (hA : A.IsSymmetric) (hA1 : s2 A = 1)
    (htrA : 0 < trOp A) {c c' : ℝ} (hc : 0 < c)
    (hcq : ∀ v : ℝ⁴, c * ‖v‖ ^ 2 ≤ ⟪cofOp A v, v⟫)
    (hcq' : ∀ v : ℝ⁴, ⟪cofOp A v, v⟫ ≤ c' * ‖v‖ ^ 2)
    {p M : ℝ} (hp : 0 < p) (hM1 : 1 < M) (hM : M = 1 + 128 * ((1 / p) * (2 ^ p - 1)))
    (hpbig : 16 * c' / c + 2 ≤ p) :
    ∃ C : ℝ, 0 < C ∧ ∀ (Φ : ℝ⁴ → ℝ) (x₀ : ℝ⁴) (R ε Λ : ℝ), 0 < R → 0 < ε → 0 < Λ →
      ContDiffOn ℝ 2 Φ (ball x₀ (5 * R / 2)) →
      (∀ x ∈ ball x₀ (5 * R / 2), s2 (A + hessOp Φ x) = 1) →
      (∀ x ∈ ball x₀ (5 * R / 2), 0 < trOp (A + hessOp Φ x)) →
      (∀ x ∈ ball x₀ (5 * R / 2), 0 ≤ Φ x) → (∀ x ∈ ball x₀ (5 * R / 2), Φ x ≤ Λ) →
      Φ x₀ ≤ ε →
      768 * Λ * 2 ^ (2 * p + 4) ≤ c * R ^ 2 → 1536 * ε * M ≤ c * R ^ 2 →
      ∀ y ∈ closedBall x₀ (R / 6), Φ y ≤ C * ε := by
  have hc'pos : 0 < c' := by
    have h1 := hcq (stdB4 0)
    have h2 := hcq' (stdB4 0)
    have h3 : ‖stdB4 0‖ = 1 := stdB4.orthonormal.1 0
    simp only [h3, one_pow, mul_one] at h1 h2
    linarith
  have htrCo : 0 ≤ trOp (cofOp A) := by
    rw [trOp_eq_sum]
    refine Finset.sum_nonneg fun i _ => ?_
    have h2 := hcq (stdB4 i)
    have h3 : ‖stdB4 i‖ = 1 := stdB4.orthonormal.1 i
    rw [h3] at h2
    nlinarith [h2, hc]
  have hYnn : 0 ≤ 2 * trOp (cofOp A) / c := div_nonneg (by linarith [htrCo]) hc.le
  obtain ⟨C, hCpos, hC⟩ :=
    harnack_scaled_uniform (Y := 2 * trOp (cofOp A) / c) hc hc'pos hYnn hp hM1 hM hpbig
  exact ⟨C, hCpos, hC A hA hA1 htrA hcq hcq' le_rfl⟩

end

end Submission
