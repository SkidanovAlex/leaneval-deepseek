import Mathlib
import Submission.Work.WilE9.Sharp.line_inc_uniform_bound

set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace Work.WilE9.Sharp

/-!
# Continuous coordinate derivatives imply Fréchet differentiability

If `f : (Fin n → ℝ) → ℝ` has, at every point `p` of an open set `U`, a derivative along each
coordinate direction `eᵢ` equal to `g i p`, and the `g i` are continuous on `U`, then `f` is
Fréchet differentiable on `U` with derivative `∑ i, (g i y) • (proj i)`.

This is the classical `C¹ ⇒ differentiable` theorem: existence of partial derivatives together
with their continuity.  (Continuity of `f` itself, one of the hypotheses below, is in fact implied
by the conclusion and is not needed.)

The proof is the textbook one.  Write the increment `x - y` as a telescoping sum of `n` single
coordinate steps (`lineDecomp`), bound each step by the mean-value theorem using only the
continuity of `g i` at `y` (this is the content of `lineIncUniform`), and sum.
-/

/-- The point obtained from `y` by replacing its first `k` coordinates by those of `x`. -/
def interp {n : ℕ} (x y : Fin n → ℝ) (k : ℕ) : Fin n → ℝ :=
  fun j => if (j : ℕ) < k then x j else y j

/-- Telescoping identity: the difference `F x - F y` is the sum of the increments obtained by
changing one coordinate at a time from `y` to `x`. -/
lemma lineDecomp {n : ℕ} (F : (Fin n → ℝ) → ℝ) (x y : Fin n → ℝ) (G : Fin n → ℝ) :
    F x - F y - ∑ i : Fin n, (x i - y i) * G i =
      ∑ k : Fin n,
        ((F (interp x y k + (x k - y k) • Pi.single k (1 : ℝ)) - F (interp x y k))
          - (x k - y k) * G k) := by
  have hx : interp x y n = x := by
    funext j
    simp only [interp]
    rw [if_pos j.isLt]
  have hy : interp x y 0 = y := by
    funext j
    simp only [interp]
    rw [if_neg (Nat.not_lt_zero _)]
  have hsucc : ∀ k : Fin n,
      interp x y ((k:ℕ)+1) = interp x y k + (x k - y k) • Pi.single k (1:ℝ) := by
    intro k
    funext j
    by_cases hjk : j = k
    · subst hjk
      simp only [interp, Pi.add_apply, Pi.smul_apply, Pi.single_eq_same, smul_eq_mul]
      rw [if_pos (Nat.lt_succ_self _), if_neg (Nat.lt_irrefl _)]
      ring
    · have hne : (j:ℕ) ≠ (k:ℕ) := fun h => hjk (Fin.ext h)
      simp only [interp, Pi.add_apply, Pi.smul_apply, Pi.single_eq_of_ne hjk, smul_zero, add_zero]
      by_cases h2 : (j:ℕ) < (k:ℕ)
      · rw [if_pos (by omega : (j:ℕ) < (k:ℕ)+1), if_pos h2]
      · rw [if_neg (by omega : ¬ ((j:ℕ) < (k:ℕ)+1)), if_neg h2]
  have htel : (∑ k : Fin n, (F (interp x y ((k:ℕ)+1)) - F (interp x y (k:ℕ)))) = F x - F y := by
    rw [Fin.sum_univ_eq_sum_range (fun m => F (interp x y (m+1)) - F (interp x y m)) n]
    rw [Finset.sum_range_sub (fun m => F (interp x y m)) n]
    rw [hx, hy]
  rw [Finset.sum_sub_distrib]
  have hA : (∑ k : Fin n, (F (interp x y k + (x k - y k) • Pi.single k (1:ℝ)) - F (interp x y k)))
      = F x - F y := by
    rw [show (∑ k : Fin n, (F (interp x y k + (x k - y k) • Pi.single k (1:ℝ)) - F (interp x y k)))
          = ∑ k : Fin n, (F (interp x y ((k:ℕ)+1)) - F (interp x y (k:ℕ))) from
        Finset.sum_congr rfl (fun k _ => by rw [hsucc k])]
    exact htel
  rw [hA]

theorem hasFDerivAt_of_lineDeriv {n : ℕ} {f : (Fin n → ℝ) → ℝ} {U : Set (Fin n → ℝ)}
    (hU : IsOpen U) (hfc : ContinuousOn f U) (g : Fin n → (Fin n → ℝ) → ℝ)
    (hg : ∀ i, ContinuousOn (g i) U)
    (hl : ∀ i, ∀ p ∈ U, ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
        ∀ t : ℝ, 0 < |t| → |t| < δ →
          |f (p + t • Pi.single i (1 : ℝ)) - f p - t * g i p| ≤ ε * |t|) :
    ∀ y ∈ U, HasFDerivAt f
      (∑ i : Fin n, (g i y) • (ContinuousLinearMap.proj i : (Fin n → ℝ) →L[ℝ] ℝ)) y := by
  intro y hy
  rw [hasFDerivAt_iff_isLittleO, Asymptotics.isLittleO_iff]
  intro ε hε
  -- Work with the smaller tolerance `C = ε / (n+1)`, so that `C * (n+1) = ε`.
  set C : ℝ := ε / ((n : ℝ) + 1) with hC
  have hCpos : 0 < C := by rw [hC]; positivity
  have hCne : ((n : ℝ) + 1) ≠ 0 := by positivity
  have hCmul : C * ((n : ℝ) + 1) = ε := by rw [hC]; exact div_mul_cancel₀ ε hCne
  -- Continuity of the coordinate derivatives at `y`, and the resulting uniform increment bound.
  have hgc : ∀ i : Fin n, ContinuousAt (g i) y := fun i => (hg i).continuousAt (hU.mem_nhds hy)
  obtain ⟨δL, hδLpos, hδL⟩ := line_inc_uniform_bound hU g hl hy hgc C hCpos
  refine Metric.mem_nhds_iff.mpr ⟨δL / 2, by positivity, fun x hx => ?_⟩
  simp only [Set.mem_setOf_eq]
  rw [Metric.mem_ball, dist_eq_norm] at hx
  have hxδ : ‖x - y‖ < δL := by linarith
  -- Every coordinate difference is bounded by the full norm.
  have hkabs : ∀ k : Fin n, |x k - y k| ≤ ‖x - y‖ := by
    intro k
    have h1 := norm_le_pi_norm (x - y) k
    rwa [Pi.sub_apply, Real.norm_eq_abs] at h1
  have hLapp : (∑ i : Fin n, (g i y) • (ContinuousLinearMap.proj i : (Fin n → ℝ) →L[ℝ] ℝ)) (x - y)
      = ∑ i : Fin n, (x i - y i) * g i y := by
    rw [sum_apply]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [smul_apply, ContinuousLinearMap.proj_apply, Pi.sub_apply, smul_eq_mul, mul_comm]
  -- The single-coordinate increment is bounded by `C * |x k - y k|`.
  have hterm : ∀ k : Fin n,
      |(f (interp x y k + (x k - y k) • Pi.single k (1:ℝ)) - f (interp x y k))
        - (x k - y k) * g k y| ≤ C * |x k - y k| := by
    intro k
    have hA : ‖interp x y k - y‖ ≤ ‖x - y‖ := by
      rw [pi_norm_le_iff_of_nonneg (norm_nonneg _)]
      intro j
      by_cases hj : (j : ℕ) < k
      · have he : (interp x y k - y) j = (x - y) j := by
          simp only [Pi.sub_apply, interp]
          rw [if_pos hj]
        rw [he]; exact norm_le_pi_norm (x - y) j
      · have he : (interp x y k - y) j = 0 := by
          simp only [Pi.sub_apply, interp]
          rw [if_neg hj, sub_self]
        rw [he]; simp
    exact hδL (interp x y k) (lt_of_le_of_lt hA hxδ) k (x k - y k)
      (lt_of_le_of_lt (hkabs k) hxδ)
  rw [hLapp, lineDecomp f x y (fun i => g i y), Real.norm_eq_abs]
  calc |∑ k : Fin n,
          ((f (interp x y k + (x k - y k) • Pi.single k (1:ℝ)) - f (interp x y k))
            - (x k - y k) * g k y)|
      ≤ ∑ k : Fin n,
          |(f (interp x y k + (x k - y k) • Pi.single k (1:ℝ)) - f (interp x y k))
            - (x k - y k) * g k y| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ k : Fin n, C * |x k - y k| := Finset.sum_le_sum (fun k _ => hterm k)
    _ = C * ∑ k : Fin n, |x k - y k| := by rw [Finset.mul_sum]
    _ ≤ C * (((n : ℝ) + 1) * ‖x - y‖) := by
          refine mul_le_mul_of_nonneg_left ?_ (le_of_lt hCpos)
          calc ∑ k : Fin n, |x k - y k| ≤ ∑ k : Fin n, ‖x - y‖ :=
                Finset.sum_le_sum (fun k _ => hkabs k)
            _ = (n : ℝ) * ‖x - y‖ := by
                  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
            _ ≤ ((n : ℝ) + 1) * ‖x - y‖ :=
                  mul_le_mul_of_nonneg_right (by linarith : (n : ℝ) ≤ (n : ℝ) + 1) (norm_nonneg _)
    _ = ε * ‖x - y‖ := by rw [← mul_assoc, hCmul]

end Work.WilE9.Sharp
