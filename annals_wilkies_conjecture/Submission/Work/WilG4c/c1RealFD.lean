/-
  WilG4c / `c1RealFD` — the `ε`-`δ` (ℓ²) predicate `HasFDerivEps` is exactly Fréchet
  differentiability with derivative `linMap c`.

  `HasFDerivEps g y c` controls the first-order remainder of `g` at `y` on the `ℓ²`-balls
  `∑ j, (y' j - y j)² < δ²`, whereas Mathlib's `HasFDerivAt g (linMap c) y` controls it on the
  balls of the sup norm `‖y' - y‖ < δ`.  On `Fin M → ℝ` the two families of balls generate the
  same filter, so the predicates agree; the only content is the two elementary norm
  inequalities

    `‖x‖² ≤ ∑ j, x j²`   and   `∑ j, x j² ≤ max M 1 * ‖x‖²`,

  the second with the harmless `max M 1` factor which also covers `M = 0`.
-/
import Mathlib
import Submission.Work.WilG4c.SliceC1Defs

namespace Work.WilG4c

open Filter Asymptotics
open scoped Topology

/-! ## 1. The two elementary `ℓ²`/sup-norm comparisons -/

/-- The `ℓ²` "squared norm" of `x : Fin M → ℝ` is non-negative. -/
lemma sum_sq_nonneg {M : ℕ} (x : Fin M → ℝ) : 0 ≤ ∑ j, x j ^ 2 :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

/-- The sup norm is dominated by the `ℓ²` norm: `‖x‖² ≤ ∑ j, x j²`. -/
lemma sq_norm_le_sum_sq {M : ℕ} (x : Fin M → ℝ) : ‖x‖ ^ 2 ≤ ∑ j, x j ^ 2 := by
  have hS : 0 ≤ ∑ j, x j ^ 2 := sum_sq_nonneg x
  have h : ‖x‖ ≤ Real.sqrt (∑ j, x j ^ 2) := by
    rw [pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)]
    intro i
    rw [Real.norm_eq_abs, ← Real.sqrt_sq_eq_abs]
    exact Real.sqrt_le_sqrt
      (Finset.single_le_sum (fun j _ => sq_nonneg (x j)) (Finset.mem_univ i))
  calc ‖x‖ ^ 2 ≤ (Real.sqrt (∑ j, x j ^ 2)) ^ 2 := pow_le_pow_left₀ (norm_nonneg x) h 2
    _ = ∑ j, x j ^ 2 := Real.sq_sqrt hS

/-- The `ℓ²` squared norm is dominated by `M` times the sup norm squared. -/
lemma sum_sq_le_card_mul_sq_norm {M : ℕ} (x : Fin M → ℝ) :
    ∑ j, x j ^ 2 ≤ (M : ℝ) * ‖x‖ ^ 2 := by
  calc ∑ j, x j ^ 2 ≤ ∑ _j : Fin M, ‖x‖ ^ 2 := Finset.sum_le_sum fun j _ => by
        calc x j ^ 2 = |x j| ^ 2 := (sq_abs (x j)).symm
          _ ≤ ‖x‖ ^ 2 := pow_le_pow_left₀ (abs_nonneg _) (norm_le_pi_norm x j) 2
    _ = (M : ℝ) * ‖x‖ ^ 2 := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

/-- The previous bound with the harmless factor `max M 1`, which is positive even for `M = 0`
(where both sides vanish anyway). -/
lemma sum_sq_le_max_mul_sq_norm {M : ℕ} (x : Fin M → ℝ) :
    ∑ j, x j ^ 2 ≤ max (M : ℝ) 1 * ‖x‖ ^ 2 :=
  (sum_sq_le_card_mul_sq_norm x).trans
    (mul_le_mul_of_nonneg_right (le_max_left _ _) (sq_nonneg _))

/-! ## 2. The equivalence -/

theorem c1RealFD {M : ℕ} (g : (Fin M → ℝ) → ℝ) (y c : Fin M → ℝ) :
    Work.WilG4c.HasFDerivEps g y c ↔ HasFDerivAt g (Work.WilG4c.linMap c) y := by
  rw [hasFDerivAt_iff_isLittleO]
  constructor
  · -- `HasFDerivEps → IsLittleO`: enlarge the sup-ball to an `ℓ²`-ball using `K = max M 1`.
    intro h
    refine IsLittleO.of_bound ?_
    intro c₀ hc₀
    set K : ℝ := max (M : ℝ) 1 with hK
    have hKpos : 0 < K := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
    have hKne : K ≠ 0 := ne_of_gt hKpos
    have hKnn : 0 ≤ K := le_of_lt hKpos
    have hsqrtKpos : 0 < Real.sqrt K := Real.sqrt_pos.2 hKpos
    have hsqrtKsq : Real.sqrt K ^ 2 = K := Real.sq_sqrt hKnn
    set ε' : ℝ := c₀ / Real.sqrt K with hε'
    have hε'pos : 0 < ε' := div_pos hc₀ hsqrtKpos
    have hε'2 : ε' ^ 2 * K = c₀ ^ 2 := by
      rw [hε', div_pow, hsqrtKsq]
      field_simp
    obtain ⟨δ, hδpos, hδ⟩ := h ε' hε'pos
    rw [Metric.eventually_nhds_iff]
    refine ⟨δ / Real.sqrt K, div_pos hδpos hsqrtKpos, ?_⟩
    intro x' hx'
    rw [dist_eq_norm] at hx'
    have hSle : ∑ j, (x' j - y j) ^ 2 ≤ K * ‖x' - y‖ ^ 2 := by
      have hh := sum_sq_le_max_mul_sq_norm (x' - y)
      simp only [Pi.sub_apply] at hh
      rwa [← hK] at hh
    have hSlt : ∑ j, (x' j - y j) ^ 2 < δ ^ 2 := by
      have hD2 : (δ / Real.sqrt K) ^ 2 = δ ^ 2 / K := by rw [div_pow, hsqrtKsq]
      have hstep : K * ‖x' - y‖ ^ 2 < K * (δ / Real.sqrt K) ^ 2 :=
        mul_lt_mul_of_pos_left (pow_lt_pow_left₀ hx' (norm_nonneg _) (by norm_num)) hKpos
      rw [hD2, mul_div_cancel₀ _ hKne] at hstep
      exact lt_of_le_of_lt hSle hstep
    have hA2 : (g x' - g y - linMap c (x' - y)) ^ 2 ≤ ε' ^ 2 * ∑ j, (x' j - y j) ^ 2 := by
      simpa only [linMap_apply, Pi.sub_apply] using hδ x' hSlt
    have hmain : (g x' - g y - linMap c (x' - y)) ^ 2 ≤ (c₀ * ‖x' - y‖) ^ 2 := by
      calc (g x' - g y - linMap c (x' - y)) ^ 2
          ≤ ε' ^ 2 * ∑ j, (x' j - y j) ^ 2 := hA2
        _ ≤ ε' ^ 2 * (K * ‖x' - y‖ ^ 2) := mul_le_mul_of_nonneg_left hSle (sq_nonneg _)
        _ = c₀ ^ 2 * ‖x' - y‖ ^ 2 := by rw [← mul_assoc, hε'2]
        _ = (c₀ * ‖x' - y‖) ^ 2 := by ring
    rw [Real.norm_eq_abs]
    have hsq := (sq_le_sq).1 hmain
    rwa [abs_of_nonneg (mul_nonneg (le_of_lt hc₀) (norm_nonneg _))] at hsq
  · -- `IsLittleO → HasFDerivEps`: shrink the `ℓ²`-ball to a sup-ball.
    intro h ε hε
    obtain ⟨δ, hδpos, hδ⟩ := Metric.eventually_nhds_iff.1 (isLittleO_iff.1 h hε)
    refine ⟨δ, hδpos, fun x' hx' => ?_⟩
    have hSle : ‖x' - y‖ ^ 2 ≤ ∑ j, (x' j - y j) ^ 2 := by
      have hh := sq_norm_le_sum_sq (x' - y)
      simpa only [Pi.sub_apply] using hh
    have hdn : ‖x' - y‖ < δ := by
      have h1 : ‖x' - y‖ ^ 2 < δ ^ 2 := lt_of_le_of_lt hSle hx'
      have h2 : |‖x' - y‖| < |δ| := (sq_lt_sq).1 h1
      rwa [abs_of_nonneg (norm_nonneg _), abs_of_pos hδpos] at h2
    have hA := hδ (y := x') (by rwa [dist_eq_norm])
    have hA2 : (g x' - g y - linMap c (x' - y)) ^ 2 ≤ ε ^ 2 * ∑ j, (x' j - y j) ^ 2 := by
      have h1 : (g x' - g y - linMap c (x' - y)) ^ 2 ≤ (ε * ‖x' - y‖) ^ 2 := by
        have hh := pow_le_pow_left₀ (norm_nonneg _) hA 2
        rwa [Real.norm_eq_abs, sq_abs] at hh
      calc (g x' - g y - linMap c (x' - y)) ^ 2 ≤ (ε * ‖x' - y‖) ^ 2 := h1
        _ = ε ^ 2 * ‖x' - y‖ ^ 2 := by ring
        _ ≤ ε ^ 2 * ∑ j, (x' j - y j) ^ 2 := mul_le_mul_of_nonneg_left hSle (sq_nonneg _)
    simpa only [linMap_apply, Pi.sub_apply] using hA2

end Work.WilG4c
