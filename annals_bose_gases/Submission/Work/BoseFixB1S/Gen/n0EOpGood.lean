import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Submission.Work.BoseFixB1S.BoxPIndFlat
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

noncomputable section

open MeasureTheory

namespace Work.BoseFixB1S.Gen

open Submission.BoseGases

set_option autoImplicit false

local notation "kE3" => EuclideanSpace ℝ (Fin 3)

/-- **Bounded on every ball.**  The class of states whose slot fibre functions are automatically
integrable: boundedness on the ball of radius `R` controls `f` on the slot fibre `{x|i↦z : z ∈ A}`
whenever `A` is bounded (`norm_update_le`). -/
def BddOnBalls {N : ℕ} (f : X N → ℝ) : Prop :=
  ∀ R : ℝ, ∃ C : ℝ, ∀ x : X N, ‖x‖ ≤ R → |f x| ≤ C

namespace BddOnBalls

variable {N : ℕ} {f g : X N → ℝ}

theorem add (hf : BddOnBalls f) (hg : BddOnBalls g) : BddOnBalls (f + g) := by
  intro R
  obtain ⟨Cf, hfC⟩ := hf R
  obtain ⟨Cg, hgC⟩ := hg R
  exact ⟨Cf + Cg, fun x hx => by
    calc |(f + g) x| = |f x + g x| := by rw [Pi.add_apply]
      _ ≤ |f x| + |g x| := abs_add_le _ _
      _ ≤ Cf + Cg := add_le_add (hfC x hx) (hgC x hx)⟩

theorem neg (hf : BddOnBalls f) : BddOnBalls (-f) := by
  intro R
  obtain ⟨Cf, hfC⟩ := hf R
  exact ⟨Cf, fun x hx => by
    rw [Pi.neg_apply, abs_neg]
    exact hfC x hx⟩

theorem sub (hf : BddOnBalls f) (hg : BddOnBalls g) : BddOnBalls (f - g) := by
  intro R
  obtain ⟨Cf, hfC⟩ := hf R
  obtain ⟨Cg, hgC⟩ := hg R
  exact ⟨Cf + Cg, fun x hx => by
    have h1 : f x ≤ Cf := (abs_le.mp (hfC x hx)).2
    have h2 : -Cf ≤ f x := (abs_le.mp (hfC x hx)).1
    have h3 : g x ≤ Cg := (abs_le.mp (hgC x hx)).2
    have h4 : -Cg ≤ g x := (abs_le.mp (hgC x hx)).1
    rw [Pi.sub_apply, abs_le]
    exact ⟨by linarith, by linarith⟩⟩

theorem const_mul (c : ℝ) (hf : BddOnBalls f) : BddOnBalls (fun x => c * f x) := by
  intro R
  obtain ⟨Cf, hfC⟩ := hf R
  exact ⟨|c| * Cf, fun x hx => by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (hfC x hx) (abs_nonneg c)⟩

theorem smul (c : ℝ) (hf : BddOnBalls f) : BddOnBalls (c • f) := by
  intro R
  obtain ⟨Cf, hfC⟩ := hf R
  exact ⟨|c| * Cf, fun x hx => by
    rw [Pi.smul_apply, smul_eq_mul, abs_mul]
    exact mul_le_mul_of_nonneg_left (hfC x hx) (abs_nonneg c)⟩

theorem const (c : ℝ) : BddOnBalls (fun _ : X N => c) :=
  fun _ => ⟨|c|, fun _ _ => le_refl _⟩

theorem zero : BddOnBalls (0 : X N → ℝ) :=
  fun _ => ⟨0, fun _ _ => by simp⟩

end BddOnBalls

/-- The elementary cube bound: `‖z‖ ≤ ℓ` for `z ∈ acube ℓ` (with `0 ≤ ℓ`). -/
theorem norm_le_of_mem_acube {ℓ : ℝ} (hℓ : 0 ≤ ℓ) {z : kE3} (hz : z ∈ acube ℓ) : ‖z‖ ≤ ℓ := by
  have hcoord : ∀ m : Fin 3, z m ∈ Set.Icc (-ℓ / 2) (ℓ / 2) := hz
  have h1 : ∀ m : Fin 3, (z m) ^ 2 ≤ (ℓ / 2) ^ 2 := by
    intro m
    have hm : |z m| ≤ ℓ / 2 := by
      rw [abs_le]
      exact ⟨by linarith [(hcoord m).1], (hcoord m).2⟩
    nlinarith [abs_nonneg (z m), sq_abs (z m)]
  have hsq : ∑ m : Fin 3, (z m) ^ 2 ≤ ℓ ^ 2 := by
    calc ∑ m : Fin 3, (z m) ^ 2 ≤ ∑ _m : Fin 3, (ℓ / 2) ^ 2 :=
          Finset.sum_le_sum (fun m _ => h1 m)
      _ = 3 * (ℓ / 2) ^ 2 := by simp
      _ ≤ ℓ ^ 2 := by nlinarith
  have hnormsq : ‖z‖ ^ 2 = ∑ m : Fin 3, (z m) ^ 2 := by
    rw [EuclideanSpace.norm_eq]
    simp [Real.sq_sqrt (Finset.sum_nonneg (fun m _ => sq_nonneg (z m))), Real.norm_eq_abs]
  nlinarith [norm_nonneg z, hℓ]

/-- **The slot-update norm bound**: replacing one slot of `x` by `z` does not increase the norm
beyond `max ‖x‖ ‖z‖` (the norm on `X N` is the sup norm over the slots). -/
theorem norm_update_le {N : ℕ} (x : X N) (i : Fin N) (z : kE3) :
    ‖Function.update x i z‖ ≤ max ‖x‖ ‖z‖ := by
  rw [pi_norm_le_iff_of_nonneg (le_max_of_le_right (norm_nonneg z))]
  intro j
  rw [Function.update_apply]
  by_cases hj : j = i
  · rw [if_pos hj]
    exact le_max_right _ _
  · rw [if_neg hj]
    exact le_trans (norm_le_pi_norm x j) (le_max_left _ _)

/-- The class of states carrying the `n₀`-spectral linearity: measurable functions bounded on every
ball.  It is a `ℝ`-submodule of the state space. -/
def good (N : ℕ) : Submodule ℝ (X N → ℝ) where
  carrier := {f | Measurable f ∧ BddOnBalls f}
  zero_mem' := ⟨measurable_zero, BddOnBalls.zero⟩
  add_mem' := fun hf hg => ⟨hf.1.add hg.1, hf.2.add hg.2⟩
  smul_mem' := fun c f hf => ⟨hf.1.const_smul c, hf.2.smul c⟩

theorem mem_good_iff {N : ℕ} {f : X N → ℝ} :
    f ∈ good N ↔ Measurable f ∧ BddOnBalls f := Iff.rfl

/-- A continuous state is measurable and bounded on every ball. -/
theorem continuous_mem_good {N : ℕ} {f : X N → ℝ} (hf : Continuous f) : f ∈ good N := by
  refine ⟨hf.measurable, fun R => ?_⟩
  obtain ⟨C, hC⟩ := (isCompact_closedBall (0 : X N) R).exists_bound_of_continuousOn
    hf.continuousOn
  exact ⟨C, fun x hx => by
    have h := hC x (by simpa [Metric.mem_closedBall, dist_eq_norm] using hx)
    simpa [Real.norm_eq_abs] using h⟩

end Work.BoseFixB1S.Gen
