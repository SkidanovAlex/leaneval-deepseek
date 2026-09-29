import Mathlib
import Submission.Work.C17.seventeen_defs
import Submission.Work.C17.led_real_data
import Submission.Work.C17.led_factor
import Submission.Work.C17.p2x_defs
import Submission.Work.C17.gab_eval
import Submission.Work.C17.p2x_map_factor

/-!
# `P2x` has only simple roots

`P2x = (X − 1)·X·(X + 1)·Q4x` is the leading coefficient of the order-two operator `M` of the
Calegari--Dimitrov--Tang paper's equation (ODE) (see `Work.C17.seventeen_indep`), and `M` has
regular singular points at its roots.  For the local analysis of `M` (Riccati equation, local
exponents `(0,0)`, logarithmic structure of the unlikely series `P`) one needs that those
singularities are *simple* roots:

`Polynomial.rootMultiplicity α ((P2x a b).map (algebraMap ℚ ℂ)) ≤ 1`

for all `a b : ℚ` with `3 ≤ a`, `3 ≤ b`, `a ≠ b` and all `α : ℂ`.

## Proof

Over `ℂ` the quartic `Q4x` factors as `(X² − cX + 1)·(X² − dX + 1)` with
`c = ledC a b`, `d = ledD a b` (`Work.C17.led_factor`), and for `a, b ≥ 3`, `a ≠ b` one has
`2 < c`, `2 < d`, `c ≠ d` (`Work.C17.led_real_data`).  Hence

`(P2x a b).map (algebraMap ℚ ℂ) = GAB c d`

(`GAB c d = (X − 1)·X·(X + 1)·(X² − cX + 1)·(X² − dX + 1)`, see `Submission.Work.C17.p2x_defs`).
That septic has seven pairwise distinct roots: `0, ±1`, and the four roots of the two quadratics
(`led_quad_root` shows that a root of one quadratic is not a root of the other, is not `0`, `±1`,
and is a *simple* root of its quadratic).  A double root `α` of a polynomial `p` forces
`p(α) = p'(α) = 0`; evaluating the explicit formulas for `GAB` and its derivative at `α` shows
that this cannot happen, by the case analysis on whether the quartic part of `GAB` vanishes at
`α`.
-/

namespace Work.C17

open Polynomial

noncomputable section

/-! ## A double root kills the derivative -/

private lemma eval_eq_zero_of_sq_dvd {K : Type*} [CommRing K] (x : K) (p : Polynomial K)
    (h : (Polynomial.X - Polynomial.C x) ^ 2 ∣ p) : Polynomial.eval x p = 0 := by
  obtain ⟨r, rfl⟩ := h
  simp [Polynomial.eval_mul]

private lemma derivative_eval_eq_zero_of_sq_dvd {K : Type*} [CommRing K] (x : K)
    (p : Polynomial K) (h : (Polynomial.X - Polynomial.C x) ^ 2 ∣ p) :
    Polynomial.eval x (Polynomial.derivative p) = 0 := by
  have hd : (Polynomial.X - Polynomial.C x) ^ (2 - 1) ∣ Polynomial.derivative p :=
    Polynomial.pow_sub_one_dvd_derivative_of_pow_dvd h
  have hd' : Polynomial.X - Polynomial.C x ∣ Polynomial.derivative p := by simpa using hd
  exact Polynomial.dvd_iff_isRoot.mp hd'

/-! ## `P2x` and its image in `ℂ[X]` are nonzero -/

private lemma P2x_ne_zero (a b : ℚ) : P2x a b ≠ 0 := by
  show (X - 1) * X * (X + 1) * Q4x a b ≠ 0
  refine mul_ne_zero (mul_ne_zero (mul_ne_zero ?_ ?_) ?_) ?_
  · simpa using (Polynomial.monic_X_sub_C (1 : ℚ)).ne_zero
  · exact Polynomial.X_ne_zero
  · simpa using (Polynomial.monic_X_add_C (1 : ℚ)).ne_zero
  · intro h
    have := congrArg (fun p : Polynomial ℚ => p.eval 0) h
    simp [Q4x] at this

private lemma p2x_map_ne_zero (a b : ℚ) :
    (P2x a b).map (algebraMap ℚ ℂ) ≠ 0 :=
  (Polynomial.map_ne_zero_iff (by exact Rat.cast_injective)).mpr (P2x_ne_zero a b)

/-! ## No double root for the septic `(X−1)X(X+1)(X²−cX+1)(X²−dX+1)` -/

theorem quartic_family_no_double_root (c d : ℝ) (hc : 2 < c) (hd : 2 < d) (hcd : c ≠ d)
    (α : ℂ) : ¬ (X - C α) ^ 2 ∣ GAB (c : ℂ) (d : ℂ) := by
  intro hdiv
  set A : ℂ := α ^ 2 - (c : ℂ) * α + 1 with hA
  set B : ℂ := α ^ 2 - (d : ℂ) * α + 1 with hB
  have hev : (GAB (c : ℂ) (d : ℂ)).eval α = 0 := eval_eq_zero_of_sq_dvd α _ hdiv
  have hder : Polynomial.eval α (Polynomial.derivative (GAB (c : ℂ) (d : ℂ))) = 0 :=
    derivative_eval_eq_zero_of_sq_dvd α _ hdiv
  obtain ⟨h1, h2⟩ := gab_eval (c : ℂ) (d : ℂ) α
  rw [← hA, ← hB] at h1 h2
  have hev' : (α - 1) * α * (α + 1) * (A * B) = 0 := by
    rw [← h1, hev]
  have hder' : (3 * α ^ 2 - 1) * (A * B)
      + (α ^ 3 - α) * ((2 * α - (c : ℂ)) * B + A * (2 * α - (d : ℂ))) = 0 := by
    rw [← h2, hder]
  have hga : (α - 1) * α * (α + 1) ≠ 0 → α ^ 3 - α ≠ 0 := by
    intro hg
    have h : α ^ 3 - α = (α - 1) * α * (α + 1) := by ring
    rw [h]; exact hg
  by_cases hAB : A * B = 0
  · -- the quartic part of `GAB` vanishes at `α`: `α` is a simple root of one quadratic
    have hz : (α ^ 2 - (c : ℂ) * α + 1) * (α ^ 2 - (d : ℂ) * α + 1) = 0 := by
      rw [← hA, ← hB]; exact hAB
    rcases led_quad_root c d hc hd hcd α hz with ⟨hA0, hAction, hBne, hz0, hz1, hzm1⟩ |
      ⟨hB0, hBd, hAne, hz0, hz1, hzm1⟩
    · have hg : (α - 1) * α * (α + 1) ≠ 0 := by
        refine mul_ne_zero (mul_ne_zero (sub_ne_zero.mpr hz1) hz0) ?_
        exact fun h => hzm1 (eq_neg_of_add_eq_zero_left h)
      have hcube : α ^ 3 - α ≠ 0 := hga hg
      have hA0' : A = 0 := by rw [hA]; exact hA0
      have hsum : (α ^ 3 - α) * ((2 * α - (c : ℂ)) * B) = 0 := by
        simpa [hA0'] using hder'
      exact absurd hsum (mul_ne_zero hcube (mul_ne_zero hAction hBne))
    · have hg : (α - 1) * α * (α + 1) ≠ 0 := by
        refine mul_ne_zero (mul_ne_zero (sub_ne_zero.mpr hz1) hz0) ?_
        exact fun h => hzm1 (eq_neg_of_add_eq_zero_left h)
      have hcube : α ^ 3 - α ≠ 0 := hga hg
      have hB0' : B = 0 := by rw [hB]; exact hB0
      have hsum : (α ^ 3 - α) * (A * (2 * α - (d : ℂ))) = 0 := by
        simpa [hB0'] using hder'
      exact absurd hsum (mul_ne_zero hcube (mul_ne_zero hAne hBd))
  · -- `α` is not a root of the quartic part: it must be `0, 1` or `-1`, where `P'` is nonzero
    have hg0 : (α - 1) * α * (α + 1) = 0 := by
      rcases mul_eq_zero.mp hev' with h | h
      · exact h
      · exact absurd h hAB
    have hcube0 : α ^ 3 - α = 0 := by
      have h : α ^ 3 - α = (α - 1) * α * (α + 1) := by ring
      rw [h, hg0]
    have h3 : 3 * α ^ 2 - 1 = 0 := by
      have hsum : (3 * α ^ 2 - 1) * (A * B) = 0 := by
        simpa [hcube0] using hder'
      rcases mul_eq_zero.mp hsum with h | h
      · exact h
      · exact absurd h hAB
    have hcases : α = 1 ∨ α = 0 ∨ α = -1 := by
      rcases mul_eq_zero.mp hg0 with h | h
      · rcases mul_eq_zero.mp h with h' | h'
        · exact Or.inl (sub_eq_zero.mp h')
        · exact Or.inr (Or.inl h')
      · exact Or.inr (Or.inr (eq_neg_of_add_eq_zero_left h))
    rcases hcases with h1 | h0 | hm1
    · rw [h1] at h3; norm_num at h3
    · rw [h0] at h3; norm_num at h3
    · rw [hm1] at h3; norm_num at h3

/-! ## The target -/

theorem p2x_roots_simple (a b : ℚ) (ha : 3 ≤ a) (hb : 3 ≤ b) (hab : a ≠ b) (α : ℂ) :
    Polynomial.rootMultiplicity α ((Work.C17.P2x a b).map (algebraMap ℚ ℂ)) ≤ 1 := by
  obtain ⟨hc, hd, hcd, -, -⟩ := led_real_data a b ha hb hab
  rw [Polynomial.rootMultiplicity_le_iff (p2x_map_ne_zero a b) α 1,
    p2x_map_factor a b ha hb]
  exact quartic_family_no_double_root (ledC a b) (ledD a b) hc hd hcd α

end

end Work.C17
