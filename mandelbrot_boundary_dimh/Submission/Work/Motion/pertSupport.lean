import Mathlib
import Submission.Work.Motion.pertSetup

/-!
# Perturbed inverse branches: auxiliary analytic estimates

* Lipschitz/`C^1` bounds on closed balls for smooth maps `ℂ × ℂ → ℂ`,
* the Newton fixed point lemma and its companion lower (expansion) bound.
-/

namespace Work.Motion
namespace Pert

open LeanEval.Dynamics.MandelbrotBoundary
open Set Metric Filter Function
open scoped NNReal

noncomputable section

/-- A `C^1` map `ℂ × ℂ → ℂ` is Lipschitz on every closed ball. -/
theorem lipschitzOnBall {f : ℂ × ℂ → ℂ} (hf : ContDiff ℝ 1 f) (a : ℂ × ℂ) (R : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ closedBall a R, ∀ y ∈ closedBall a R,
      ‖f x - f y‖ ≤ C * ‖x - y‖ := by
  obtain ⟨K, hK⟩ := ContDiffOn.exists_lipschitzOnWith (n := 1) hf.contDiffOn one_ne_zero
    (convex_closedBall a R) (isCompact_closedBall a R)
  refine ⟨(K : ℝ), K.coe_nonneg, fun x hx y hy => ?_⟩
  have h := hK.dist_le_mul x hx y hy
  rwa [dist_eq_norm, dist_eq_norm] at h

/-- A `C^1` map `ℂ × ℂ → ℂ` is bounded on every closed ball. -/
theorem normLeOnBall {f : ℂ × ℂ → ℂ} (hf : ContDiff ℝ 1 f) (a : ℂ × ℂ) (R : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ closedBall a R, ‖f x‖ ≤ C := by
  obtain ⟨C, hC0, hC⟩ := lipschitzOnBall hf a R
  rcases lt_or_ge R 0 with hR | hR
  · refine ⟨0, le_refl 0, fun x hx => ?_⟩
    rw [closedBall_eq_empty.mpr hR] at hx
    exact absurd hx (by simp)
  · refine ⟨‖f a‖ + C * R, ?_, fun x hx => ?_⟩
    · nlinarith [norm_nonneg (f a), hC0, hR]
    · have hxa : ‖x - a‖ ≤ R := by
        have h := hx; rw [mem_closedBall, dist_eq_norm] at h; linarith
      have h1 : ‖f x - f a‖ ≤ C * ‖x - a‖ := hC x hx a (mem_closedBall_self hR)
      have h2 : C * ‖x - a‖ ≤ C * R := mul_le_mul_of_nonneg_left hxa hC0
      calc ‖f x‖ = ‖f a + (f x - f a)‖ := by ring_nf
        _ ≤ ‖f a‖ + ‖f x - f a‖ := norm_add_le _ _
        _ ≤ ‖f a‖ + C * R := by linarith

section Newton

variable {F : ℂ → ℂ} {A B : ℂ} {ε b : ℝ}

/-- MVT bound for the Newton remainder: `‖(F v - B v) - (F v' - B v')‖ ≤ (b/4) ‖v - v'‖`. -/
theorem newton_remainder_bound (hd : ∀ w ∈ closedBall (0 : ℂ) ε, DifferentiableAt ℂ F w)
    (hbd : ∀ w ∈ closedBall (0 : ℂ) ε, ‖deriv F w - B‖ ≤ b / 4)
    {v v' : ℂ} (hv : v ∈ closedBall (0 : ℂ) ε) (hv' : v' ∈ closedBall (0 : ℂ) ε) :
    ‖(F v - B * v) - (F v' - B * v')‖ ≤ (b / 4) * ‖v - v'‖ := by
  have hderiv : ∀ u ∈ closedBall (0 : ℂ) ε,
      deriv (fun u : ℂ => F u - B * u) u = deriv F u - B := by
    intro u hu
    have h2 : HasDerivAt (fun u : ℂ => B * u) B u := by
      simpa using (hasDerivAt_id u).const_mul B
    exact ((hd u hu).hasDerivAt.sub h2).deriv
  have hbound : ∀ u ∈ closedBall (0 : ℂ) ε, ‖deriv (fun u : ℂ => F u - B * u) u‖ ≤ b / 4 := by
    intro u hu; rw [hderiv u hu]; exact hbd u hu
  have h := (convex_closedBall (0 : ℂ) ε).norm_image_sub_le_of_norm_deriv_le
    (f := fun u : ℂ => F u - B * u)
    (fun u hu => (hd u hu).sub (differentiableAt_id.const_mul B)) hbound hv' hv
  simpa using h

/-- **Newton fixed point.** If `F 0 = 0` and `deriv F ≈ B` with `‖B‖ ≥ b > 0` on `closedBall 0 ε`,
then `F v = -A` has a solution in `closedBall 0 ε`, unique there, provided `‖A‖ ≤ b ε / 4`. -/
theorem newtonFixpoint (hb : 0 < b) (hε : 0 < ε)
    (hF0 : F 0 = 0) (hB : b ≤ ‖B‖) (hA : ‖A‖ ≤ b * ε / 4)
    (hd : ∀ w ∈ closedBall (0 : ℂ) ε, DifferentiableAt ℂ F w)
    (hbd : ∀ w ∈ closedBall (0 : ℂ) ε, ‖deriv F w - B‖ ≤ b / 4) :
    ∃ v ∈ closedBall (0 : ℂ) ε, F v = -A ∧
      (∀ w ∈ closedBall (0 : ℂ) ε, F w = -A → w = v) := by
  have hb4 : 0 < b / 4 := by linarith
  have hBpos : 0 < ‖B‖ := lt_of_lt_of_le hb hB
  have hBne : B ≠ 0 := norm_pos_iff.mp hBpos
  set Ψ : ℂ → ℂ := fun w => w - (A + F w) / B with hΨdef
  have hΨeq : ∀ w : ℂ, Ψ w = (B * w - F w - A) / B := by
    intro w; rw [hΨdef]; field_simp; ring
  have hfix : ∀ w : ℂ, Ψ w = w ↔ F w = -A := by
    intro w
    have hΨw : Ψ w = w - (A + F w) / B := by rw [hΨdef]
    constructor
    · intro h
      have h1 : (A + F w) / B = 0 := by
        rw [hΨw] at h
        have h' : w - (A + F w) / B - w = 0 := by rw [h, sub_self]
        rw [show w - (A + F w) / B - w = -((A + F w) / B) by ring] at h'
        exact neg_eq_zero.mp h'
      have h2 : A + F w = 0 := by
        rcases div_eq_zero_iff.mp h1 with h3 | h3
        · exact h3
        · exact absurd h3 hBne
      rw [add_comm] at h2
      exact eq_neg_of_add_eq_zero_left h2
    · intro h
      rw [hΨw, h]; simp
  have hmaps : MapsTo Ψ (closedBall (0 : ℂ) ε) (closedBall (0 : ℂ) ε) := by
    intro w hw
    have hw' : ‖w‖ ≤ ε := by
      have h := hw; rw [mem_closedBall, dist_eq_norm] at h; simpa using h
    rw [mem_closedBall, dist_eq_norm]; simp only [sub_zero]
    have hrem0 := newton_remainder_bound hd hbd (mem_closedBall_self hε.le) hw
    have hrem : ‖B * w - F w‖ ≤ b / 4 * ‖w‖ := by simpa [hF0] using hrem0
    rw [hΨeq, norm_div]
    have h1 : ‖B * w - F w - A‖ ≤ b / 4 * ‖w‖ + ‖A‖ := by
      have h2 : B * w - F w - A = (B * w - F w) - A := by ring
      rw [h2]
      calc ‖(B * w - F w) - A‖ ≤ ‖B * w - F w‖ + ‖A‖ := norm_sub_le _ _
        _ ≤ b / 4 * ‖w‖ + ‖A‖ := by linarith
    have h3 : b / 4 * ‖w‖ + ‖A‖ ≤ b / 2 * ε := by
      have h4 : b / 4 * ‖w‖ ≤ b / 4 * ε := mul_le_mul_of_nonneg_left hw' hb4.le
      linarith
    rw [div_le_iff₀ hBpos]
    calc ‖B * w - F w - A‖ ≤ b / 4 * ‖w‖ + ‖A‖ := h1
      _ ≤ b / 2 * ε := h3
      _ ≤ ε * ‖B‖ := by nlinarith [hB, hb, hε]
  have hcontr : ∀ v ∈ closedBall (0 : ℂ) ε, ∀ v' ∈ closedBall (0 : ℂ) ε,
      ‖Ψ v - Ψ v'‖ ≤ (1 / 4) * ‖v - v'‖ := by
    intro v hv v' hv'
    have hrem := newton_remainder_bound hd hbd hv hv'
    rw [hΨeq, hΨeq, ← sub_div, norm_div]
    have heq : (B * v - F v - A) - (B * v' - F v' - A)
        = -((F v - B * v) - (F v' - B * v')) := by ring
    rw [heq, norm_neg, div_le_iff₀ hBpos]
    have h3 : b / 4 ≤ (1 / 4) * ‖B‖ := by linarith
    have h4 : (b / 4) * ‖v - v'‖ ≤ (1 / 4) * ‖B‖ * ‖v - v'‖ :=
      mul_le_mul_of_nonneg_right h3 (norm_nonneg _)
    calc ‖(F v - B * v) - (F v' - B * v')‖ ≤ (b / 4) * ‖v - v'‖ := hrem
      _ ≤ (1 / 4) * ‖B‖ * ‖v - v'‖ := h4
      _ = (1 / 4) * ‖v - v'‖ * ‖B‖ := by ring
  have hsf : MapsTo Ψ (closedBall (0 : ℂ) ε) (closedBall (0 : ℂ) ε) := hmaps
  have hLipSub : LipschitzWith (1 / 4 : ℝ≥0)
      (MapsTo.restrict Ψ (closedBall (0 : ℂ) ε) (closedBall (0 : ℂ) ε) hsf) := by
    rw [lipschitzWith_iff_dist_le_mul]
    intro x y
    have hx : (x : ℂ) ∈ closedBall (0 : ℂ) ε := x.2
    have hy : (y : ℂ) ∈ closedBall (0 : ℂ) ε := y.2
    have hxy := hcontr x.1 hx y.1 hy
    dsimp only [MapsTo.restrict]
    rw [Subtype.dist_eq, Subtype.dist_eq, dist_eq_norm, dist_eq_norm]
    exact hxy
  have hcK : ContractingWith (1 / 4 : ℝ≥0)
      (MapsTo.restrict Ψ (closedBall (0 : ℂ) ε) (closedBall (0 : ℂ) ε) hsf) :=
    ⟨(by norm_num : (1 / 4 : ℝ≥0) < 1), hLipSub⟩
  obtain ⟨y, hy, hyfix, -, -⟩ := hcK.exists_fixedPoint' isClosed_closedBall.isComplete hsf
    (x := (0 : ℂ)) (mem_closedBall_self hε.le) (by simp)
  refine ⟨y, hy, (hfix y).mp hyfix, fun w hw hwA => ?_⟩
  have hwfix : Ψ w = w := (hfix w).mpr hwA
  have hc := hcontr w hw y hy
  rw [hwfix, hyfix] at hc
  have h0 : ‖w - y‖ = 0 := by nlinarith [norm_nonneg (w - y)]
  exact sub_eq_zero.mp (norm_eq_zero.mp h0)

/-- **Expansion bound** companion to `newtonFixpoint`. -/
theorem newtonLowerBound (hb : 0 < b) (_hF0 : F 0 = 0) (hB : b ≤ ‖B‖)
    (hd : ∀ w ∈ closedBall (0 : ℂ) ε, DifferentiableAt ℂ F w)
    (hbd : ∀ w ∈ closedBall (0 : ℂ) ε, ‖deriv F w - B‖ ≤ b / 4)
    {v v' : ℂ} (hv : v ∈ closedBall (0 : ℂ) ε) (hv' : v' ∈ closedBall (0 : ℂ) ε) :
    b / 4 * ‖v - v'‖ ≤ ‖F v - F v'‖ := by
  have hrem := newton_remainder_bound hd hbd hv hv'
  have hdecomp : F v - F v' = B * (v - v') + ((F v - B * v) - (F v' - B * v')) := by ring
  have hsub : B * (v - v') = (F v - F v') - ((F v - B * v) - (F v' - B * v')) := by
    rw [hdecomp]; ring
  have h1 : ‖B * (v - v')‖ ≤ ‖F v - F v'‖ + ‖(F v - B * v) - (F v' - B * v')‖ := by
    rw [hsub]; exact norm_sub_le _ _
  rw [norm_mul] at h1
  have h2 : b * ‖v - v'‖ ≤ ‖B‖ * ‖v - v'‖ := mul_le_mul_of_nonneg_right hB (norm_nonneg _)
  have h3 : ‖F v - F v'‖ + (b / 4) * ‖v - v'‖ ≥ b * ‖v - v'‖ := by linarith [h1, h2, hrem]
  nlinarith [h3, hb, norm_nonneg (v - v')]

end Newton

end

end Pert
end Work.Motion
