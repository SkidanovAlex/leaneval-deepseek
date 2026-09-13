/-
# From Trudinger's interior gradient estimate to the weighted `L¹` estimate

Trudinger--Wang's weighted interior gradient estimate (`Hessian measures II`, Ann. of Math. 150
(1999), Corollary 3.4, p. 587) is the input `(gradp)` of Section 3 of Shankar--Yuan.  Its proof
uses the *classical* interior gradient estimate for solutions of `F_k[u] = ψ₀` with constant
right hand side (`[T2]`, Trudinger, *Weak solutions of Hessian equations*, Comm. PDE 22 (1997);
quoted as Theorem 3.3 of *Hessian measures II*) together with the interpolation inequality of
Lemma 2.6 of that paper.  This file implements that derivation in the case `n = 4`, `k = 2`,
taking the classical estimate as the hypothesis `InteriorGradientBound`.

The two commons lemmas used:

* `Commons.Measure.WeightedInterpolation.weighted_lipschitz_of_osc` — the oscillation bound at
  every scale (Theorem 3.3) implies the intrinsic weighted Lipschitz semi-norm is controlled by
  the intrinsic weighted sup-norm;
* `Commons.Measure.WeightedInterpolation.weighted_le_interpolation` — Trudinger--Wang's
  interpolation inequality (Lemma 2.6): the weighted sup-norm is at most `ε` times the weighted
  Lipschitz semi-norm plus `C ε^{-n} ∫ |u|`.

Combining them with a small `ε` bounds the weighted Lipschitz semi-norm by `C ∫|u|`, which is
Corollary 3.4.  For the application one only needs the estimate on balls `B(x,r) ⊂ B(x,2r)`.
-/
import Mathlib
import Submission.AlexandrovInputs
import Submission.Commons.Measure.WeightedInterpolation.weighted_le_interpolation
import Submission.Commons.Measure.WeightedInterpolation.weighted_lipschitz_of_osc

open HessianEstimates
open Laplacian Metric MeasureTheory Set Filter
open scoped BigOperators ENNReal Topology RealInnerProductSpace InnerProductSpace

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Submission

local notation "ℝ⁴" => EuclideanSpace ℝ (Fin 4)

/-- **Trudinger's interior gradient estimate** (`[T2]`, quoted as Theorem 3.3 of
Trudinger--Wang, *Hessian measures II*) in dimension four: for a classical (`C³`) solution of
`σ₂(D²u) = 1` with `Δu > 0` on an open set `s`, and any ball `B(y,ρ)` contained in `s` on which
`u` is trapped between `m` and `M`, one has `‖Du(y)‖ * ρ ≤ C (M - m)`.  The constant depends
only on the dimension. -/
def InteriorGradientBound : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ (u : ℝ⁴ → ℝ) (s : Set ℝ⁴) (y : ℝ⁴) (ρ M m : ℝ),
    IsOpen s → ContDiffOn ℝ 3 u s → (∀ z ∈ s, σ₂ (H u s z) = 1) → (∀ z ∈ s, 0 < (Δ u) z) →
    0 < ρ → closedBall y ρ ⊆ s → (∀ x ∈ ball y ρ, m ≤ u x ∧ u x ≤ M) →
    ‖fderiv ℝ u y‖ * ρ ≤ C * (M - m)

/-- **Trudinger--Wang's weighted interior gradient estimate** (Corollary 3.4 of *Hessian measures
II*), derived from the classical interior gradient estimate: for a `C³` solution `u` of `σ₂ = 1`
with `Δu > 0` on `ball x (2r)`, bounded by `M₀` there,

  `r^5 |u y - u z| / dist y z ≤ C ∫_{ball x (2r)} |u|`  for `y, z ∈ closedBall x r`. -/
theorem classical_weighted_estimate (hIG : InteriorGradientBound) :
    ∃ C : ℝ, 0 < C ∧ ∀ (u : ℝ⁴ → ℝ) (x : ℝ⁴) (r M₀ : ℝ),
      0 < r → 0 ≤ M₀ →
      ContDiffOn ℝ 3 u (ball x (2 * r)) →
      (∀ z ∈ ball x (2 * r), σ₂ (H u (ball x (2 * r)) z) = 1) →
      (∀ z ∈ ball x (2 * r), 0 < (Δ u) z) →
      (∀ z ∈ ball x (2 * r), |u z| ≤ M₀) →
      ∀ y ∈ closedBall x r, ∀ z ∈ closedBall x r, y ≠ z →
        r ^ 5 * |u y - u z| / dist y z ≤ C * ∫ w in ball x (2 * r), |u w| := by
  obtain ⟨C, hCpos, hC⟩ := hIG
  set C' : ℝ := max C 1 with hC'def
  have hC'pos : 0 < C' := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have hC'nn : 0 ≤ C' := hC'pos.le
  have hCle : C ≤ C' := le_max_left _ _
  set E : ℝ := 8 * (4 : ℝ) ^ (4 : ℕ) * C' + 4 with hEdef
  have hEpos : 0 < E := by rw [hEdef]; positivity
  set ω : ℝ := (volume (Metric.ball (0 : ℝ⁴) 1)).toReal with hωdef
  have hωpos : 0 < ω := by
    rw [hωdef]
    exact ENNReal.toReal_pos (Metric.measure_ball_pos (volume : Measure ℝ⁴) 0 one_pos).ne'
      (ne_of_lt MeasureTheory.measure_ball_lt_top)
  set C'' : ℝ := (2 ^ 26 + 2 ^ 5) / ω + 1 with hC''def
  have hC''pos : 0 < C'' := by rw [hC''def]; positivity
  refine ⟨32 * C'' * E ^ 5, by positivity, ?_⟩
  intro u x r M₀ hr hM₀ hcont hσ2 hΔ hbd y hy z hz hyz
  have hr2 : (0 : ℝ) < 2 * r := by linarith
  -- the intrinsic weight
  set d : ℝ⁴ → ℝ := fun w => 2 * r - dist w x with hddef
  have hdval : ∀ w : ℝ⁴, d w = 2 * r - dist w x := fun w => rfl
  have hdpos : ∀ w ∈ ball x (2 * r), 0 < d w := by
    intro w hw
    rw [hdval]
    have := mem_ball.mp hw
    linarith
  have hdball : ∀ w ∈ ball x (2 * r), Metric.ball w (d w) ⊆ ball x (2 * r) := by
    intro w hw w' hw'
    rw [mem_ball] at hw' ⊢
    have h1 : dist w x < 2 * r := mem_ball.mp hw
    rw [hdval] at hw'
    linarith [dist_triangle w' w x]
  have hdlip : ∀ w w' : ℝ⁴, |d w - d w'| ≤ dist w w' := by
    intro w w'
    have h : d w - d w' = dist w' x - dist w x := by rw [hdval, hdval]; ring
    rw [h, ← Real.dist_eq]
    exact le_trans (dist_dist_dist_le_left w' w x) (le_of_eq (dist_comm w' w))
  -- the intrinsic weighted sup-norm
  set A : ℝ := sSup ((fun w => (d w) ^ 4 * |u w|) '' (ball x (2 * r))) with hAdef
  have hbdd : BddAbove ((fun w => (d w) ^ 4 * |u w|) '' (ball x (2 * r))) := by
    refine ⟨(2 * r) ^ 4 * M₀, ?_⟩
    rintro a ⟨w, hw, rfl⟩
    have h1 : d w ≤ 2 * r := by
      rw [hdval]
      have := mem_ball.mp hw
      linarith [dist_nonneg (x := w) (y := x)]
    have h2 : 0 ≤ d w := (hdpos w hw).le
    have h3 : (d w) ^ 4 ≤ (2 * r) ^ 4 := pow_le_pow_left₀ h2 h1 4
    have h4 : |u w| ≤ M₀ := hbd w hw
    exact mul_le_mul h3 h4 (abs_nonneg _) (by positivity)
  have hA : ∀ w ∈ ball x (2 * r), (d w) ^ 4 * |u w| ≤ A := fun w hw =>
    le_csSup hbdd ⟨w, hw, rfl⟩
  have hAnn : 0 ≤ A :=
    le_trans (mul_nonneg (by positivity) (abs_nonneg _)) (hA x (mem_ball_self hr2))
  have hgrad' : ∀ (y : ℝ⁴) (ρ M m : ℝ), 0 < ρ → Metric.closedBall y ρ ⊆ ball x (2 * r) →
      (∀ w ∈ Metric.ball y ρ, m ≤ u w ∧ u w ≤ M) → ‖fderiv ℝ u y‖ * ρ ≤ C' * (M - m) := by
    intro y ρ M m hρ hsub hb
    have hmM : m ≤ M := le_trans (hb y (mem_ball_self hρ)).1 (hb y (mem_ball_self hρ)).2
    have h1 := hC u (ball x (2 * r)) y ρ M m isOpen_ball hcont hσ2 hΔ hρ hsub hb
    have h2 : C * (M - m) ≤ C' * (M - m) :=
      mul_le_mul_of_nonneg_right hCle (by linarith)
    linarith
  have hlipK : ∀ y ∈ ball x (2 * r), ∀ z ∈ ball x (2 * r), y ≠ z →
      (min (d y) (d z)) ^ 5 * |u y - u z| / dist y z ≤ E * A := by
    have h := Commons.Measure.WeightedInterpolation.weighted_lipschitz_of_osc
      (n := 4) (d := d) (Ω := ball x (2 * r)) (u := u) (C₀ := C') (A := A)
      hC'nn isOpen_ball ⟨x, mem_ball_self hr2⟩ hdpos hdball hdlip
      (hcont.differentiableOn (by norm_num)) hgrad' hA
    have hE : (8 : ℝ) * (4 : ℝ) ^ (4 : ℕ) * C' + 4 = E := hEdef.symm
    intro y hy z hz hyz
    rw [← hE]
    exact h y hy z hz hyz
  have hIint : IntegrableOn u (ball x (2 * r)) volume := by
    refine IntegrableOn.of_bound (MeasureTheory.measure_ball_lt_top (μ := volume)) ?_ M₀ ?_
    · exact (hcont.continuousOn).aestronglyMeasurable measurableSet_ball
    · filter_upwards [ae_restrict_mem measurableSet_ball] with w hw
      simpa [Real.norm_eq_abs] using hbd w hw
  obtain hA0 | hApos := eq_or_lt_of_le hAnn
  · -- degenerate case: `u` vanishes on the ball
    have huz : ∀ w ∈ ball x (2 * r), u w = 0 := by
      intro w hw
      have h := hA w hw
      rw [← hA0] at h
      have hz0 : (d w) ^ 4 * |u w| = 0 := le_antisymm h (mul_nonneg (by positivity) (abs_nonneg _))
      have hd4 : (d w) ^ 4 ≠ 0 := pow_ne_zero 4 (hdpos w hw).ne'
      have h' : |u w| = 0 := by
        rcases mul_eq_zero.mp hz0 with h' | h'
        · exact absurd h' hd4
        · exact h'
      simpa using h'
    have hy' : y ∈ ball x (2 * r) := by
      rw [mem_ball]; rw [mem_closedBall] at hy; linarith
    have hz' : z ∈ ball x (2 * r) := by
      rw [mem_ball]; rw [mem_closedBall] at hz; linarith
    rw [huz y hy', huz z hz']
    have : (0:ℝ) ≤ 32 * C'' * E ^ 5 * ∫ w in ball x (2 * r), |u w| := by positivity
    simpa using this
  · -- main case
    set ε : ℝ := 1 / (2 * E) with hεdef
    have hεpos : 0 < ε := by rw [hεdef]; positivity
    have hε1 : ε ≤ 1 := by
      rw [hεdef, div_le_one (by positivity)]
      linarith [hEpos]
    have hKpos : 0 < E * A := mul_pos hEpos hApos
    have hInterp : A ≤ ε * (E * A) + C'' * ((∫ w in ball x (2 * r), |u w|) / ε ^ 4) := by
      rw [hAdef]
      refine csSup_le ⟨_, x, mem_ball_self hr2, rfl⟩ ?_
      rintro a ⟨w, hw, rfl⟩
      have h := Commons.Measure.WeightedInterpolation.weighted_le_interpolation
        (n := 4) (d := d) (Ω := ball x (2 * r)) (u := u) (K := E * A) (ε := ε)
        hεpos hε1 hKpos isOpen_ball hdpos hdball hdlip hIint hlipK hw
      have hC''eq : (2 ^ (4 * (4 + 2) + 2) + 2 ^ (4 + 1)) /
            (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin 4)) 1)).toReal + 1 = C'' := by
        rw [hC''def, hωdef]
      rwa [hC''eq] at h
    have hAfin : A ≤ 2 * C'' * ((∫ w in ball x (2 * r), |u w|) / ε ^ 4) := by
      have heq : ε * (E * A) = A / 2 := by
        rw [hεdef]
        field_simp
      rw [heq] at hInterp
      linarith
    have hKfin : E * A ≤ E * (2 * C'' * ((∫ w in ball x (2 * r), |u w|) / ε ^ 4)) :=
      mul_le_mul_of_nonneg_left hAfin hEpos.le
    have hy' : y ∈ ball x (2 * r) := by
      rw [mem_ball]; rw [mem_closedBall] at hy; linarith
    have hz' : z ∈ ball x (2 * r) := by
      rw [mem_ball]; rw [mem_closedBall] at hz; linarith
    have hmin : r ^ 5 ≤ (min (d y) (d z)) ^ 5 := by
      refine pow_le_pow_left₀ (by linarith : (0:ℝ) ≤ r) (le_min ?_ ?_) 5
      · rw [hdval]; have := mem_closedBall.mp hy; linarith
      · rw [hdval]; have := mem_closedBall.mp hz; linarith
    have hstep : r ^ 5 * |u y - u z| / dist y z ≤
        (min (d y) (d z)) ^ 5 * |u y - u z| / dist y z :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hmin (abs_nonneg _)) dist_nonneg
    calc r ^ 5 * |u y - u z| / dist y z
        ≤ (min (d y) (d z)) ^ 5 * |u y - u z| / dist y z := hstep
      _ ≤ E * A := hlipK y hy' z hz' hyz
      _ ≤ E * (2 * C'' * ((∫ w in ball x (2 * r), |u w|) / ε ^ 4)) := hKfin
      _ = 32 * C'' * E ^ 5 * ∫ w in ball x (2 * r), |u w| := by
          rw [hεdef]; field_simp; ring

end Submission
