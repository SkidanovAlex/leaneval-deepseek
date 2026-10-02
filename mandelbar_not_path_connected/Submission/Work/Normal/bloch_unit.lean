import Mathlib
import Submission.Work.Normal.bloch_lite

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# Bloch's theorem (weak form) on the unit ball

If `F : ℂ → ℂ` is holomorphic on the unit ball with `F 0 = 0` and `F' 0 = 1`, then the
image `F '' ball 0 1` contains a disc of radius `1/128`.

This is a weak form of Bloch's theorem (Bloch's constant is `> 0.43`, so a much larger
disc is in fact covered); the constant is chosen so that the classical Landau iteration
below has comfortable numerical room.

## Proof outline

The quantitative input is `bloch_lite`: when `‖F'‖ ≤ 2` on the unit ball the image covers
`ball 0 (1/16)` with a preimage in `closedBall 0 (1/4)` (a Banach fixed point argument).

For general `F`, we run Landau's iteration.  Starting at `0` we move, as long as possible,
to a point `z (n+1)` at distance `< 2^{-(n+2)}` from `z n` at which `‖deriv F‖` is more than
twice its value at `z n`.  If the process ever stops at a point `z`, then `deriv F` is
`2`-comparable to `deriv F z` on the ball `ball z (2^{-(n+2)})`; rescaling that ball to the
unit ball gives — through `bloch_lite` — a disc of radius
`2^{-(n+2)} ‖deriv F z‖/16 ≥ 1/64` inside the image.  If the process never stops, the `n`-th
point satisfies `‖deriv F (z n)‖ ≥ 2^n` and `‖z n‖ ≤ 1/2`, contradicting the boundedness of
`deriv F` on the compact ball `closedBall 0 (1/2)`.
-/

open Classical Metric

namespace Work.Normal

/-- The auxiliary step length `ρ n = 2^{-(n+2)}`; these sum to `1/2`. -/
noncomputable def blochRadius (n : ℕ) : ℝ := (1/2 : ℝ) ^ (n + 2)

/-- Landau's recursion: starting from `0`, step to a point of the open disc of radius
`blochRadius n` around the current point where `‖deriv F‖` has more than doubled, whenever
such a point exists; otherwise stay put. -/
noncomputable def blochSeq (F : ℂ → ℂ) : ℕ → ℂ
  | 0 => 0
  | (n+1) => if h : ∃ w ∈ Metric.ball (blochSeq F n) (blochRadius n),
        2 * ‖deriv F (blochSeq F n)‖ < ‖deriv F w‖ then h.choose else blochSeq F n

/-- The "stopping" predicate: `deriv F` is `2`-comparable to its value at `blochSeq F n` on
the whole disc of radius `blochRadius n`. -/
def blochDone (F : ℂ → ℂ) (n : ℕ) : Prop :=
  ∀ w ∈ Metric.ball (blochSeq F n) (blochRadius n),
    ‖deriv F w‖ ≤ 2 * ‖deriv F (blochSeq F n)‖

lemma blochSeq_succ (F : ℂ → ℂ) (n : ℕ) :
    blochSeq F (n+1) = (if h : ∃ w ∈ Metric.ball (blochSeq F n) (blochRadius n),
        2 * ‖deriv F (blochSeq F n)‖ < ‖deriv F w‖ then h.choose else blochSeq F n) := rfl

lemma blochDone_iff (F : ℂ → ℂ) (n : ℕ) :
    blochDone F n ↔ ¬ (∃ w ∈ Metric.ball (blochSeq F n) (blochRadius n),
        2 * ‖deriv F (blochSeq F n)‖ < ‖deriv F w‖) := by
  simp only [blochDone, not_exists, not_and, not_lt]

lemma blochRadius_pos (n : ℕ) : 0 < blochRadius n := by
  rw [blochRadius]; positivity

lemma blochRadius_le_quarter (n : ℕ) : blochRadius n ≤ (1/4 : ℝ) := by
  rw [blochRadius, show (1/4 : ℝ) = (1/2)^2 by norm_num]
  exact pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)

/-- If the recursion has not stopped at level `n`, then it moved away: the derivative
strictly more than doubles and the step is shorter than `blochRadius n`. -/
lemma blochSeq_succ_of_not_done (F : ℂ → ℂ) (n : ℕ) (h : ¬ blochDone F n) :
    (2 * ‖deriv F (blochSeq F n)‖ < ‖deriv F (blochSeq F (n+1))‖) ∧
      ‖blochSeq F (n+1) - blochSeq F n‖ < blochRadius n := by
  have hex : ∃ w ∈ Metric.ball (blochSeq F n) (blochRadius n),
      2 * ‖deriv F (blochSeq F n)‖ < ‖deriv F w‖ := by
    by_contra h'
    exact h ((blochDone_iff F n).mpr h')
  have hstep : blochSeq F (n+1) = hex.choose := by
    rw [blochSeq_succ]; exact dite_eq_left hex
  obtain ⟨hmem, hgt⟩ := hex.choose_spec
  refine ⟨?_, ?_⟩
  · rw [hstep]; exact hgt
  · rw [Metric.mem_ball, dist_eq_norm] at hmem
    rw [hstep]
    exact hmem

/-- As long as the recursion has not stopped, the sequence stays in the ball of radius
`1/2` and the derivative grows like `2^n`. -/
lemma blochSeq_bounds (F : ℂ → ℂ) (h1 : deriv F 0 = 1) :
    ∀ n, (∀ m < n, ¬ blochDone F m) →
      ‖blochSeq F n‖ ≤ 1/2 - (1/2 : ℝ)^(n+1) ∧ (2:ℝ)^n ≤ ‖deriv F (blochSeq F n)‖ := by
  intro n
  induction n with
  | zero =>
      intro _
      refine ⟨?_, ?_⟩
      · rw [show blochSeq F 0 = (0:ℂ) from rfl]; norm_num
      · rw [show blochSeq F 0 = (0:ℂ) from rfl, h1]; norm_num
  | succ n ih =>
      intro h
      have hlt : ∀ m < n, ¬ blochDone F m := fun m hm => h m (Nat.lt_succ_of_lt hm)
      obtain ⟨hnorm, hderiv⟩ := ih hlt
      have hnd : ¬ blochDone F n := h n (Nat.lt_succ_self n)
      obtain ⟨hgt, hdist⟩ := blochSeq_succ_of_not_done F n hnd
      constructor
      · have h1' : ‖blochSeq F (n+1)‖ ≤ ‖blochSeq F n‖ + ‖blochSeq F (n+1) - blochSeq F n‖ := by
          have hh := norm_add_le (blochSeq F n) (blochSeq F (n+1) - blochSeq F n)
          have heq : blochSeq F n + (blochSeq F (n+1) - blochSeq F n) = blochSeq F (n+1) := by ring
          simpa only [heq] using hh
        have hsub_exp : (n+1)+1 = n+2 := by ring
        have key : ‖blochSeq F (n+1)‖ ≤ 1/2 - (1/2 : ℝ)^(n+2) := by
          have hb2 : blochRadius n = (1/2 : ℝ)^(n+2) := rfl
          have hp : (1/2 : ℝ)^(n+1) = 2 * (1/2)^(n+2) := by rw [pow_succ]; ring
          have hd := hdist
          rw [hb2] at hd
          linarith [h1', hnorm, hd, hp]
        rwa [hsub_exp]
      · have hp2 : (2:ℝ)^(n+1) = 2 * (2:ℝ)^n := by rw [pow_succ]; ring
        rw [hp2]
        linarith [hderiv, hgt]

/-- **Rescaling step.**  If on a disc `ball z0 ρ ⊆ ball 0 1` the derivative of `F` is
`2`-comparable to its value at the centre `z0` (and `deriv F z0 ≠ 0`), then the image of the
unit ball contains a disc of radius `ρ ‖deriv F z0‖ / 16`.

This is `bloch_lite` applied to the normalised map
`ζ ↦ (F (z0 + ρ ζ) - F z0) / (ρ * deriv F z0)`. -/
theorem bloch_rescale_aux {F : ℂ → ℂ} (hF : DifferentiableOn ℂ F (Metric.ball 0 1))
    {z0 : ℂ} {ρ : ℝ} (hρ : 0 < ρ)
    (hsub : Metric.ball z0 ρ ⊆ Metric.ball 0 1)
    (hz0 : deriv F z0 ≠ 0)
    (hbd : ∀ w ∈ Metric.ball z0 ρ, ‖deriv F w‖ ≤ 2 * ‖deriv F z0‖) :
    ∃ c : ℂ, Metric.ball c (ρ * ‖deriv F z0‖ / 16) ⊆ F '' (Metric.ball 0 1) := by
  classical
  have hρc : (ρ : ℂ) ≠ 0 := by
    simp only [ne_eq, Complex.ofReal_eq_zero]; exact ne_of_gt hρ
  have hz0mem : z0 ∈ Metric.ball (0:ℂ) 1 := hsub (Metric.mem_ball_self hρ)
  have hFz0 : DifferentiableAt ℂ F z0 := hF.differentiableAt (Metric.isOpen_ball.mem_nhds hz0mem)
  set A : ℂ := ρ * deriv F z0 with hA
  have hA_ne : A ≠ 0 := by rw [hA]; exact mul_ne_zero hρc hz0
  set g : ℂ → ℂ := fun ζ => (F (z0 + ρ * ζ) - F z0) / A with hg
  have hg_diff : DifferentiableOn ℂ g (Metric.ball 0 1) := by
    have hinner : DifferentiableOn ℂ (fun ζ : ℂ => z0 + ρ * ζ) (Metric.ball 0 1) := by fun_prop
    have hmaps : Set.MapsTo (fun ζ : ℂ => z0 + ρ * ζ) (Metric.ball 0 1) (Metric.ball 0 1) := by
      intro ζ hζ
      have hζ1 : ‖ζ‖ < 1 := mem_ball_zero_iff.mp hζ
      apply hsub
      rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, norm_mul, Complex.norm_of_nonneg hρ.le]
      calc ρ * ‖ζ‖ < ρ * 1 := mul_lt_mul_of_pos_left hζ1 hρ
        _ = ρ := mul_one ρ
    rw [hg]
    apply DifferentiableOn.congr (((hF.comp hinner hmaps).sub_const (F z0)).div_const A)
    intro ζ hζ
    rfl
  have hg0 : g 0 = 0 := by simp [hg]
  have hinner0 : HasDerivAt (fun ζ : ℂ => z0 + ρ * ζ) (ρ : ℂ) 0 := by
    have h1 : HasDerivAt (fun ζ : ℂ => ρ * ζ) (ρ : ℂ) 0 := by
      simpa using (hasDerivAt_id (0:ℂ)).const_mul (ρ : ℂ)
    have h2 : HasDerivAt (fun ζ : ℂ => z0 + ρ * ζ) ((0:ℂ) + ρ) 0 :=
      (hasDerivAt_const (0:ℂ) z0).add h1
    rw [zero_add] at h2
    exact h2
  have hcomp0 : HasDerivAt (fun ζ : ℂ => F (z0 + ρ * ζ)) (deriv F z0 * (ρ:ℂ)) 0 := by
    have hF0 : HasDerivAt F (deriv F z0) (z0 + ρ * (0:ℂ)) := by simpa using hFz0.hasDerivAt
    exact hF0.comp 0 hinner0
  have hg1 : deriv g 0 = 1 := by
    have hq : deriv (fun ζ : ℂ => (F (z0 + ρ * ζ) - F z0) / A) 0 = (deriv F z0 * (ρ:ℂ)) / A :=
      (hcomp0.sub_const (F z0)).div_const A |>.deriv
    rw [hg, hq, hA]
    rw [mul_comm (deriv F z0) (ρ:ℂ), div_self (mul_ne_zero hρc hz0)]
  have hgbd : ∀ ζ ∈ Metric.ball (0:ℂ) 1, ‖deriv g ζ‖ ≤ 2 := by
    intro ζ hζ
    have hζ1 : ‖ζ‖ < 1 := mem_ball_zero_iff.mp hζ
    have hw : z0 + ρ * ζ ∈ Metric.ball z0 ρ := by
      rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, norm_mul, Complex.norm_of_nonneg hρ.le]
      calc ρ * ‖ζ‖ < ρ * 1 := mul_lt_mul_of_pos_left hζ1 hρ
        _ = ρ := mul_one ρ
    have hw1 : z0 + ρ * ζ ∈ Metric.ball (0:ℂ) 1 := hsub hw
    have hFw : DifferentiableAt ℂ F (z0 + ρ * ζ) := hF.differentiableAt (Metric.isOpen_ball.mem_nhds hw1)
    have hinner : HasDerivAt (fun y : ℂ => z0 + ρ * y) (ρ : ℂ) ζ := by
      have h1 : HasDerivAt (fun y : ℂ => ρ * y) (ρ : ℂ) ζ := by
        simpa using (hasDerivAt_id ζ).const_mul (ρ : ℂ)
      have h2 : HasDerivAt (fun y : ℂ => z0 + ρ * y) ((0:ℂ) + ρ) ζ :=
        (hasDerivAt_const ζ z0).add h1
      rw [zero_add] at h2
      exact h2
    have hcomp : HasDerivAt (fun y : ℂ => F (z0 + ρ * y)) (deriv F (z0 + ρ * ζ) * (ρ:ℂ)) ζ :=
      hFw.hasDerivAt.comp ζ hinner
    have hq : deriv (fun y : ℂ => (F (z0 + ρ * y) - F z0) / A) ζ
        = (deriv F (z0 + ρ * ζ) * (ρ:ℂ)) / A :=
      (hcomp.sub_const (F z0)).div_const A |>.deriv
    have hderivg : deriv g ζ = deriv F (z0 + ρ * ζ) / deriv F z0 := by
      rw [hg, hq, hA]
      rw [mul_comm (deriv F (z0 + ρ * ζ)) (ρ:ℂ)]
      rw [mul_div_mul_left (deriv F (z0 + ρ * ζ)) (deriv F z0) hρc]
    rw [hderivg, norm_div]
    rw [div_le_iff₀ (norm_pos_iff.mpr hz0)]
    exact hbd _ hw
  have hbloch := bloch_lite hg_diff hg0 hg1 hgbd
  refine ⟨F z0, ?_⟩
  intro b hb
  rw [Metric.mem_ball, dist_eq_norm] at hb
  have hlt : ‖(b - F z0)/A‖ < 1/16 := by
    rw [norm_div, hA, norm_mul, Complex.norm_of_nonneg hρ.le]
    rw [div_lt_iff₀ (mul_pos hρ (norm_pos_iff.mpr hz0))]
    linarith [hb]
  obtain ⟨w, hw, hgw⟩ := hbloch ((b - F z0)/A) hlt
  refine ⟨z0 + ρ * w, ?_, ?_⟩
  · apply hsub
    rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, norm_mul, Complex.norm_of_nonneg hρ.le]
    have hw1 : ‖w‖ ≤ 1/4 := by rwa [mem_closedBall_zero_iff] at hw
    calc ρ * ‖w‖ ≤ ρ * (1/4) := mul_le_mul_of_nonneg_left hw1 hρ.le
      _ < ρ := by linarith
  · have heq : (F (z0 + ρ * w) - F z0)/A = (b - F z0)/A := hgw
    have h1 := congrArg (fun x : ℂ => x * A) heq
    rw [div_mul_cancel₀ (F (z0 + ρ * w) - F z0) hA_ne,
        div_mul_cancel₀ (b - F z0) hA_ne] at h1
    exact sub_left_inj.mp h1

/-- **Bloch's theorem, weak form.**  A holomorphic function on the unit ball with
`F 0 = 0` and `F' 0 = 1` covers a disc of radius `1/128`. -/
theorem bloch_unit {F : ℂ → ℂ} (hF : DifferentiableOn ℂ F (Metric.ball 0 1))
    (h0 : F 0 = 0) (h1 : deriv F 0 = 1) :
    ∃ c : ℂ, Metric.ball c (1/128 : ℝ) ⊆ F '' (Metric.ball 0 1) := by
  classical
  have _h0 : F 0 = 0 := h0
  have hdF' : DifferentiableOn ℂ (deriv F) (Metric.ball 0 1) := hF.deriv Metric.isOpen_ball
  by_cases hP : ∃ n, blochDone F n
  · set n₀ := Nat.find hP with hn₀def
    have hdone : blochDone F n₀ := hn₀def.symm ▸ Nat.find_spec hP
    have hmin : ∀ m < n₀, ¬ blochDone F m := fun m hm => Nat.find_min hP hm
    obtain ⟨hnorm, hderiv⟩ := blochSeq_bounds F h1 n₀ hmin
    have hsub : Metric.ball (blochSeq F n₀) (blochRadius n₀) ⊆ Metric.ball (0:ℂ) 1 := by
      intro w hw
      rw [Metric.mem_ball, dist_eq_norm] at hw
      rw [Metric.mem_ball, dist_eq_norm, sub_zero]
      have h1' : ‖w‖ ≤ ‖w - blochSeq F n₀‖ + ‖blochSeq F n₀‖ := by
        have hh := norm_add_le (w - blochSeq F n₀) (blochSeq F n₀)
        have heq : w - blochSeq F n₀ + blochSeq F n₀ = w := by ring
        simpa only [heq] using hh
      have hq : blochRadius n₀ ≤ (1/4:ℝ) := blochRadius_le_quarter n₀
      have hpos : (0:ℝ) ≤ (1/2)^(n₀+1) := by positivity
      linarith
    have hz0ne : deriv F (blochSeq F n₀) ≠ 0 := by
      intro hh
      rw [hh, norm_zero] at hderiv
      have : (0:ℝ) < 2^n₀ := by positivity
      linarith
    obtain ⟨c, hc⟩ := bloch_rescale_aux hF (blochRadius_pos n₀) hsub hz0ne hdone
    refine ⟨c, fun w hw => ?_⟩
    apply hc
    rw [Metric.mem_ball] at hw ⊢
    have hprod1 : (1/2:ℝ)^n₀ * (2:ℝ)^n₀ = 1 := by rw [← mul_pow]; norm_num
    have hprod : blochRadius n₀ * (2:ℝ)^n₀ = 1/4 := by
      have hpow : blochRadius n₀ = (1/2:ℝ)^n₀ * (1/4) := by rw [blochRadius, pow_add]; norm_num
      rw [hpow]
      calc ((1/2:ℝ)^n₀ * (1/4)) * (2:ℝ)^n₀ = (1/4) * ((1/2:ℝ)^n₀ * (2:ℝ)^n₀) := by ring
        _ = 1/4 := by rw [hprod1, mul_one]
    have hb0 : 0 ≤ blochRadius n₀ := le_of_lt (blochRadius_pos n₀)
    have hstep1 : (1/4 : ℝ) ≤ blochRadius n₀ * ‖deriv F (blochSeq F n₀)‖ := by
      rw [← hprod]; exact mul_le_mul_of_nonneg_left hderiv hb0
    have hrad : (1/128 : ℝ) ≤ blochRadius n₀ * ‖deriv F (blochSeq F n₀)‖ / 16 := by linarith
    linarith [hw, hrad]
  · push Not at hP
    have hcont : ContinuousOn (deriv F) (Metric.closedBall (0:ℂ) (1/2)) :=
      (hdF'.mono (fun z hz => by
        rw [Metric.mem_closedBall, dist_eq_norm, sub_zero] at hz
        rw [Metric.mem_ball, dist_eq_norm, sub_zero]
        linarith)).continuousOn
    obtain ⟨B, hB⟩ := (isCompact_closedBall (0:ℂ) (1/2)).exists_bound_of_continuousOn hcont
    have hkey : ∀ n, (2:ℝ)^n ≤ B := by
      intro n
      obtain ⟨hnorm, hderiv⟩ := blochSeq_bounds F h1 n (fun m _ => hP m)
      have hmem : blochSeq F n ∈ Metric.closedBall (0:ℂ) (1/2) := by
        rw [mem_closedBall_zero_iff]
        have : (0:ℝ) ≤ (1/2)^(n+1) := by positivity
        linarith
      exact le_trans hderiv (hB _ hmem)
    obtain ⟨n, hn⟩ := exists_nat_gt B
    have hcast : (n:ℝ) < (2:ℝ)^n := by exact_mod_cast Nat.lt_two_pow_self
    linarith [hkey n]

end Work.Normal
