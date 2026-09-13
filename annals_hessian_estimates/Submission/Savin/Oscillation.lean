/-
# Oscillation decay (Savin's Corollary 1.2 / Corollary 3.2)

Given a NONNEGATIVE solution of `s2 (A + D²Φ) = 1` (positive branch) on `ball 0 R`, the two-sided
Harnack inequality `Submission.Savin.HarnackFull.harnack_full` gives, exactly as in
Gilbarg--Trudinger Theorem 8.22,

  `osc_{B_{R/2}} Φ ≤ (1 - δ) osc_{B_R} Φ`.

The proof uses that subtracting a constant does not change the Hessian, so that `Φ - m` is again a
solution; applying `harnack_full` to it at the point where `Φ` is minimal on the half-ball gives the
gain `1/C`.

This is the input of the *iteration* which produces the Holder estimate (Savin's Corollary 3.3);
note the smallness condition has the shape `osc ≲ R²` -- the perturbation must be small compared
with the SQUARE of the scale.
-/
import Mathlib
import ChallengeDeps
import Submission.Savin.HarnackFull

open Metric MeasureTheory Filter
open scoped BigOperators RealInnerProductSpace Topology ENNReal Pointwise

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 4000000

namespace Submission

local notation "ℝ⁴" => EuclideanSpace ℝ (Fin 4)

noncomputable section

/-- Subtracting a constant does not change the Hessian operator. -/
theorem hessOp_sub_const {Φ : ℝ⁴ → ℝ} {m : ℝ} {x : ℝ⁴} (h : ContDiffAt ℝ 2 Φ x) :
    hessOp (fun y => Φ y - m) x = hessOp Φ x := by
  have hs : (fun y : ℝ⁴ => Φ y - m) = (fun y => Φ y + (fun _ : ℝ⁴ => -m) y) := by
    funext y
    show Φ y - m = Φ y + -m
    ring
  rw [hs, hessOp_add h contDiffAt_const]
  have h0 : hessOp (fun _ : ℝ⁴ => (-m : ℝ)) x = 0 := by
    unfold hessOp
    have h1 : fderiv ℝ (fun _ : ℝ⁴ => (-m : ℝ)) = fun _ => (0 : ℝ⁴ →L[ℝ] ℝ) := by
      funext z
      exact fderiv_const_apply (-m)
    rw [h1]
    rw [fderiv_const_apply (0 : ℝ⁴ →L[ℝ] ℝ)]
    ext v w
    simp
  rw [h0, add_zero]

/-- **Oscillation decay.**  Let `Φ ≥ 0` solve `s2 (A + D²Φ) = 1` with the positive branch on
`ball 0 R`, and let `m₁, M₁` be a lower and an upper bound for `Φ` on `ball 0 R`.  If the
oscillation `M₁ - m₁` is small compared with `R²` (the smallness conditions of `harnack_full`
stated with `Λ := M₁ - m₁`), then

  `Φ x - Φ y ≤ (1 - δ) (M₁ - m₁)`   for all `x, y ∈ closedBall 0 (R/2)`.

In particular `osc_{B_{R/2}} ≤ (1-δ) osc_{B_R}`. -/
theorem oscillation_decay_uniform {c c' Y p M : ℝ} (hc : 0 < c) (hc'pos : 0 < c')
    (hYnn : 0 ≤ Y) (hp : 0 < p) (hM1 : 1 < M)
    (hM : M = 1 + 128 * ((1 / p) * (2 ^ p - 1))) (hpbig : 16 * c' / c + 2 ≤ p) :
    ∃ δ : ℝ, 0 < δ ∧ δ < 1 ∧ ∀ (A : ℝ⁴ →L[ℝ] ℝ⁴) (hA : A.IsSymmetric) (hA1 : s2 A = 1)
      (htrA : 0 < trOp A) (hcq : ∀ v : ℝ⁴, c * ‖v‖ ^ 2 ≤ ⟪cofOp A v, v⟫)
      (hcq' : ∀ v : ℝ⁴, ⟪cofOp A v, v⟫ ≤ c' * ‖v‖ ^ 2)
      (hYb : 2 * trOp (cofOp A) / c ≤ Y)
      (Φ : ℝ⁴ → ℝ) (R m₁ M₁ : ℝ), 0 < R →
      ContDiffOn ℝ 2 Φ (ball 0 R) →
      (∀ x ∈ ball 0 R, s2 (A + hessOp Φ x) = 1) →
      (∀ x ∈ ball 0 R, 0 < trOp (A + hessOp Φ x)) →
      (∀ x ∈ ball 0 R, m₁ ≤ Φ x) → (∀ x ∈ ball 0 R, Φ x ≤ M₁) →
      768 * (M₁ - m₁) * 2 ^ (2 * p + 4) ≤ c * R ^ 2 / 25 →
      1536 * (M₁ - m₁) * M ≤ c * R ^ 2 / 25 →
      ∀ x ∈ closedBall 0 (R / 2), ∀ y ∈ closedBall 0 (R / 2),
        Φ x - Φ y ≤ (1 - δ) * (M₁ - m₁) := by
  obtain ⟨C, hCpos, hC⟩ := harnack_full_uniform (Y := Y) hc hc'pos hYnn hp hM1 hM hpbig
  have hC2 : (0 : ℝ) < max C 2 := by positivity
  have h2le : (2 : ℝ) ≤ max C 2 := le_max_right _ _
  refine ⟨1 / max C 2, by positivity, ?_, ?_⟩
  · rw [div_lt_one hC2]; linarith
  · intro A hA hA1 htrA hcq hcq' hYb Φ R m₁ M₁ hR hΦ heq hpos hm hMup hsc hse x hx y hy
    have hCge : C ≤ max C 2 := le_max_left _ _
    have hsub : closedBall (0 : ℝ⁴) (R / 2) ⊆ ball 0 R := by
      intro z hz
      rw [mem_closedBall, dist_zero_right] at hz
      rw [mem_ball, dist_zero_right]
      linarith
    have hmem0 : (0 : ℝ⁴) ∈ ball 0 R := by rw [mem_ball, dist_self]; linarith
    have hMm : m₁ ≤ M₁ := le_trans (hm 0 hmem0) (hMup 0 hmem0)
    by_cases hΛ : M₁ - m₁ = 0
    · -- degenerate case: `Φ` is constant on the half ball
      have hxM : Φ x ≤ m₁ := by have := hMup x (hsub hx); linarith
      have hyM : m₁ ≤ Φ y := hm y (hsub hy)
      have : M₁ - m₁ = 0 := hΛ
      rw [hΛ]; linarith
    · have hΛpos : 0 < M₁ - m₁ := lt_of_le_of_ne (by linarith) (Ne.symm hΛ)
      have hcont : ContinuousOn Φ (closedBall (0 : ℝ⁴) (R / 2)) :=
        (hΦ.continuousOn).mono hsub
      have hmem : (0 : ℝ⁴) ∈ closedBall (0 : ℝ⁴) (R / 2) := by
        rw [mem_closedBall, dist_self]; linarith
      obtain ⟨x₀, hx₀mem, hx₀max⟩ := (isCompact_closedBall (0 : ℝ⁴) (R / 2)).exists_isMaxOn
        ⟨0, hmem⟩ hcont
      obtain ⟨y₀, hy₀mem, hy₀min⟩ := (isCompact_closedBall (0 : ℝ⁴) (R / 2)).exists_isMinOn
        ⟨0, hmem⟩ hcont
      have hx₀max' : ∀ z ∈ closedBall (0 : ℝ⁴) (R / 2), Φ z ≤ Φ x₀ := fun z hz => hx₀max hz
      have hy₀min' : ∀ z ∈ closedBall (0 : ℝ⁴) (R / 2), Φ y₀ ≤ Φ z := fun z hz => hy₀min hz
      -- the shifted function is a nonnegative solution
      have hΦ' : ContDiffOn ℝ 2 (fun w : ℝ⁴ => Φ w - m₁) (ball 0 R) := hΦ.sub contDiffOn_const
      have hpos0' : ∀ z ∈ ball 0 R, 0 ≤ Φ z - m₁ := fun z hz => by linarith [hm z hz]
      have hup' : ∀ z ∈ ball 0 R, Φ z - m₁ ≤ M₁ - m₁ := fun z hz => by linarith [hMup z hz]
      have heq' : ∀ z ∈ ball 0 R, s2 (A + hessOp (fun w => Φ w - m₁) z) = 1 := by
        intro z hz
        have hcd : ContDiffAt ℝ 2 Φ z := hΦ.contDiffAt (isOpen_ball.mem_nhds hz)
        rw [hessOp_sub_const hcd]
        exact heq z hz
      have hpos' : ∀ z ∈ ball 0 R, 0 < trOp (A + hessOp (fun w => Φ w - m₁) z) := by
        intro z hz
        have hcd : ContDiffAt ℝ 2 Φ z := hΦ.contDiffAt (isOpen_ball.mem_nhds hz)
        rw [hessOp_sub_const hcd]
        exact hpos z hz
      have hres := hC A hA hA1 htrA hcq hcq' hYb (fun w : ℝ⁴ => Φ w - m₁) 0 R (M₁ - m₁)
          hR hΛpos hΦ' heq' hpos' hpos0' hup' hsc hse
      have hcompare : Φ x₀ - m₁ ≤ C * (Φ y₀ - m₁) :=
        hres x₀ hx₀mem y₀ hy₀mem
      have hnn : (0 : ℝ) ≤ Φ y₀ - m₁ := hpos0' y₀ (hsub hy₀mem)
      have hcompare1 : Φ x₀ - m₁ ≤ (max C 2) * (Φ y₀ - m₁) :=
        le_trans hcompare (mul_le_mul_of_nonneg_right hCge hnn)
      have hxy : Φ x - Φ y ≤ Φ x₀ - Φ y₀ := by
        have h1 : Φ x ≤ Φ x₀ := hx₀max' x hx
        have h2 : Φ y₀ ≤ Φ y := hy₀min' y hy
        linarith
      have hkey : Φ x₀ - Φ y₀ ≤ (1 - 1 / max C 2) * (M₁ - m₁) := by
        have hd : (Φ x₀ - m₁) / (max C 2) ≤ Φ y₀ - m₁ := by
          rw [div_le_iff₀ hC2, mul_comm]
          exact hcompare1
        have hup : Φ x₀ - m₁ ≤ M₁ - m₁ := hup' x₀ (hsub hx₀mem)
        have hfac : 0 ≤ 1 - 1 / max C 2 := by
          have h1 : 1 / max C 2 ≤ 1 := by
            rw [div_le_one hC2]
            linarith
          linarith
        have hE : Φ x₀ - Φ y₀ ≤ (1 - 1 / max C 2) * (Φ x₀ - m₁) := by
          have h1 : Φ x₀ - Φ y₀ = (Φ x₀ - m₁) - (Φ y₀ - m₁) := by ring
          rw [h1]
          have h2 : (1 - 1 / max C 2) * (Φ x₀ - m₁)
              = (Φ x₀ - m₁) - (Φ x₀ - m₁) / (max C 2) := by ring
          rw [h2]
          linarith [hd]
        calc Φ x₀ - Φ y₀ ≤ (1 - 1 / max C 2) * (Φ x₀ - m₁) := hE
          _ ≤ (1 - 1 / max C 2) * (M₁ - m₁) := mul_le_mul_of_nonneg_left hup hfac
      linarith [hxy, hkey]

/-- **Oscillation decay.**  Let `Φ ≥ 0` solve `s2 (A + D²Φ) = 1` with the positive branch on
`ball 0 R`, and let `m₁, M₁` be a lower and an upper bound for `Φ` on `ball 0 R`.  If the
oscillation `M₁ - m₁` is small compared with `R²` (the smallness conditions of `harnack_full`
stated with `Λ := M₁ - m₁`), then

  `Φ x - Φ y ≤ (1 - δ) (M₁ - m₁)`   for all `x, y ∈ closedBall 0 (R/2)`.

In particular `osc_{B_{R/2}} ≤ (1-δ) osc_{B_R}`. -/
theorem oscillation_decay {A : ℝ⁴ →L[ℝ] ℝ⁴} (hA : A.IsSymmetric) (hA1 : s2 A = 1)
    (htrA : 0 < trOp A) {c c' : ℝ} (hc : 0 < c)
    (hcq : ∀ v : ℝ⁴, c * ‖v‖ ^ 2 ≤ ⟪cofOp A v, v⟫)
    (hcq' : ∀ v : ℝ⁴, ⟪cofOp A v, v⟫ ≤ c' * ‖v‖ ^ 2)
    {p M : ℝ} (hp : 0 < p) (hM1 : 1 < M) (hM : M = 1 + 128 * ((1 / p) * (2 ^ p - 1)))
    (hpbig : 16 * c' / c + 2 ≤ p) :
    ∃ δ : ℝ, 0 < δ ∧ δ < 1 ∧ ∀ (Φ : ℝ⁴ → ℝ) (R m₁ M₁ : ℝ), 0 < R →
      ContDiffOn ℝ 2 Φ (ball 0 R) →
      (∀ x ∈ ball 0 R, s2 (A + hessOp Φ x) = 1) →
      (∀ x ∈ ball 0 R, 0 < trOp (A + hessOp Φ x)) →
      (∀ x ∈ ball 0 R, m₁ ≤ Φ x) → (∀ x ∈ ball 0 R, Φ x ≤ M₁) →
      768 * (M₁ - m₁) * 2 ^ (2 * p + 4) ≤ c * R ^ 2 / 25 →
      1536 * (M₁ - m₁) * M ≤ c * R ^ 2 / 25 →
      ∀ x ∈ closedBall 0 (R / 2), ∀ y ∈ closedBall 0 (R / 2),
        Φ x - Φ y ≤ (1 - δ) * (M₁ - m₁) := by
  obtain ⟨hc'pos, hYnn⟩ := harnack_base_data hc hcq hcq'
  obtain ⟨δ, hδpos, hδ1, hδ⟩ :=
    oscillation_decay_uniform (Y := 2 * trOp (cofOp A) / c) hc hc'pos hYnn hp hM1 hM hpbig
  exact ⟨δ, hδpos, hδ1, hδ A hA hA1 htrA hcq hcq' le_rfl⟩

end

end Submission
