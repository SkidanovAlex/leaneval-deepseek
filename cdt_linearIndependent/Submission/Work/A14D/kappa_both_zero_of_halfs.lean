import Mathlib
import Submission.Work.A14D.LC_setup
import Submission.Work.A14D.log_structured_vanishes
import Submission.Work.A14D.log_relations_at_real
import Submission.Work.A14D.eqOn_zero_of_ball_ninth_of_realInterval

/-!
# `Work.A14D.kappa_both_zero_of_halfs`

If a holomorphic `X` on the disc `ball ninth δ` and a holomorphic `B` on the punctured disc
`ball ninth δ \ {ninth}` satisfy the two *log - structured* relations

  `κU * X z * log (z - ninth) + B z = 0`  on the upper half disc `halfU δ`,
  `κL * X z * log (z - ninth) + B z = 0`  on the lower half disc `halfL δ`

(with `log` the principal branch, so that the two half discs use the *same* function), then
both products `κU * X` and `κL * X` vanish identically on the disc.

Mathematically: at every real `x` with `1/9 - δ < x < 1/9` the two relations can be pushed to
the boundary from above resp. below (the argument `x - 1/9` is a negative real number, so the
principal log jumps by `2πi`), giving

  `κU * X x * (L + iπ) + B x = 0`,   `κL * X x * (L - iπ) + B x = 0`,   `L = log (1/9 - x)`.

Subtracting, `X x * ((κU - κL) * L + (κU + κL) * iπ) = 0` on that whole interval.  If the
bracket is non-zero at one point of the interval, then `X` vanishes on a real interval, hence
`X ≡ 0` on the disc by the identity theorem.  Otherwise the bracket vanishes identically on the
interval; evaluating at two distinct points `1/9 - δ/2` and `1/9 - δ/4` (where `L` takes the
distinct values `log (δ/2)`, `log (δ/4)`) forces `κU - κL = 0` and then `κU + κL = 0`, i.e.
`κU = κL = 0`.  Either way the conclusion follows.

The two analytic inputs are delegated: `Work.A14D.log_relations_at_real` (the one-sided limits)
and `Work.A14D.eqOn_zero_of_ball_ninth_of_realInterval` (the identity theorem).
-/

namespace Work.A14D

open Complex Metric
open scoped Topology

theorem kappa_both_zero_of_halfs {δ : ℝ} (hδ : 0 < δ) {X B : ℂ → ℂ} {κU κL : ℂ}
    (hX : DifferentiableOn ℂ X (Metric.ball ninth δ))
    (hB : DifferentiableOn ℂ B (Metric.ball ninth δ \ {ninth}))
    (hU : ∀ z ∈ halfU δ, κU * X z * Complex.log (z - ninth) + B z = 0)
    (hL : ∀ z ∈ halfL δ, κL * X z * Complex.log (z - ninth) + B z = 0) :
    ∀ z ∈ Metric.ball ninth δ, κU * X z = 0 ∧ κL * X z = 0 := by
  -- the two one-sided limit relations at a real point `x < 1/9` of the disc
  have hlim := log_relations_at_real hδ hX hB hU hL
  -- `‖(x : ℂ) - ninth‖ = 1/9 - x` for real `x < 1/9`
  have hnorm : ∀ x : ℝ, x < 1 / 9 → ‖(x : ℂ) - ninth‖ = 1 / 9 - x := by
    intro x hx
    have hcast : (x : ℂ) - ninth = ((x - 1 / 9 : ℝ) : ℂ) := by
      have h9 : ninth = ((1 / 9 : ℝ) : ℂ) := by simp [ninth]
      rw [h9]; push_cast; ring
    rw [hcast, Complex.norm_real, Real.norm_eq_abs,
      abs_of_neg (by linarith : x - 1 / 9 < 0)]
    ring
  -- the combined relation on the interval `(1/9 - δ, 1/9)`
  have hcomb : ∀ x : ℝ, 1 / 9 - δ < x → x < 1 / 9 →
      X (x : ℂ) * ((κU - κL) * Real.log (1 / 9 - x) + (κU + κL) * (Real.pi * Complex.I)) = 0 := by
    intro x hxa hxb
    obtain ⟨h1, h2⟩ := hlim x hxa hxb
    rw [hnorm x hxb] at h1 h2
    have e1 := eq_neg_of_add_eq_zero_left h1
    have e2 := eq_neg_of_add_eq_zero_left h2
    have key : κU * X (x : ℂ) * (Real.log (1 / 9 - x) + Real.pi * Complex.I)
        - κL * X (x : ℂ) * (Real.log (1 / 9 - x) - Real.pi * Complex.I) = 0 := by
      rw [e1, e2, sub_self]
    have hrw : X (x : ℂ) * ((κU - κL) * Real.log (1 / 9 - x) + (κU + κL) * (Real.pi * Complex.I))
        = κU * X (x : ℂ) * (Real.log (1 / 9 - x) + Real.pi * Complex.I)
          - κL * X (x : ℂ) * (Real.log (1 / 9 - x) - Real.pi * Complex.I) := by ring
    rw [hrw, key]
  by_cases hex : ∃ x ∈ Set.Ioo (1 / 9 - δ) (1 / 9),
      (κU - κL) * Real.log (1 / 9 - x) + (κU + κL) * (Real.pi * Complex.I) ≠ 0
  · -- the bracket is non-zero somewhere: `X` vanishes on a real interval
    obtain ⟨x₀, hx₀, hfx₀⟩ := hex
    have hx₀lt : x₀ < 1 / 9 := hx₀.2
    have hpos : 0 < 1 / 9 - x₀ := by linarith
    have hx₀mem : (x₀ : ℂ) ∈ Metric.ball ninth δ := by
      rw [Metric.mem_ball, Complex.dist_eq, hnorm x₀ hx₀lt]; linarith [hx₀.1]
    have hcont : ContinuousAt (fun y : ℝ =>
        (κU - κL) * Real.log (1 / 9 - y) + (κU + κL) * (Real.pi * Complex.I)) x₀ := by
      have h1 : ContinuousAt (fun y : ℝ => (1 / 9 - y)) x₀ := by fun_prop
      have h2 : ContinuousAt (fun y : ℝ => ((Real.log (1 / 9 - y) : ℝ) : ℂ)) x₀ :=
        Complex.continuous_ofReal.continuousAt.comp
          ((Real.continuousAt_log (by linarith : (1 / 9 - x₀) ≠ 0)).comp h1)
      exact ((continuousAt_const.mul h2).add continuousAt_const)
    obtain ⟨η₁, hη₁, hη₁'⟩ := (Metric.continuousAt_iff.mp hcont) _
      (norm_pos_iff.mpr hfx₀)
    set η₂ : ℝ := min (x₀ - (1 / 9 - δ)) (1 / 9 - x₀) with hη₂def
    have hη₂pos : 0 < η₂ := by
      rw [hη₂def]; exact lt_min (by linarith [hx₀.1]) hpos
    have hXzero : ∀ z ∈ Metric.ball ninth δ, X z = 0 := by
      refine eqOn_zero_of_ball_ninth_of_realInterval hδ hX (η := min η₁ η₂)
        (lt_min hη₁ hη₂pos) hx₀mem ?_
      intro y hy
      have hy' : dist y x₀ < min η₁ η₂ := by rwa [Real.dist_eq]
      have hy₁ : dist y x₀ < η₁ := lt_of_lt_of_le hy' (min_le_left _ _)
      have hy₂ : |y - x₀| < η₂ := by
        have h2 : dist y x₀ < η₂ := lt_of_lt_of_le hy' (min_le_right _ _)
        rwa [Real.dist_eq] at h2
      have hfy : (κU - κL) * Real.log (1 / 9 - y) + (κU + κL) * (Real.pi * Complex.I) ≠ 0 := by
        intro h0
        have hlt := hη₁' hy₁
        rw [h0, dist_zero_left] at hlt
        exact lt_irrefl _ hlt
      have hymem : y ∈ Set.Ioo (1 / 9 - δ) (1 / 9) := by
        have h := hy₂
        rw [abs_lt] at h
        exact ⟨by linarith [h.1, hη₂def, min_le_left (x₀ - (1 / 9 - δ)) (1 / 9 - x₀)],
               by linarith [h.2, hη₂def, min_le_right (x₀ - (1 / 9 - δ)) (1 / 9 - x₀)]⟩
      exact (mul_eq_zero.mp (hcomb y hymem.1 hymem.2)).resolve_right hfy
    intro z hz
    rw [hXzero z hz]; simp
  · -- the bracket vanishes identically on the interval: evaluate at two distinct points
    push Not at hex
    have hx₁mem : (1 / 9 - δ / 2) ∈ Set.Ioo (1 / 9 - δ) (1 / 9) := by
      constructor <;> linarith
    have hx₂mem : (1 / 9 - δ / 4) ∈ Set.Ioo (1 / 9 - δ) (1 / 9) := by
      constructor <;> linarith
    have e₁ := hex (1 / 9 - δ / 2) hx₁mem
    have e₂ := hex (1 / 9 - δ / 4) hx₂mem
    have hl₁ : Real.log (1 / 9 - (1 / 9 - δ / 2)) = Real.log (δ / 2) := by congr 1; ring
    have hl₂ : Real.log (1 / 9 - (1 / 9 - δ / 4)) = Real.log (δ / 4) := by congr 1; ring
    have hlogne : Real.log (δ / 2) ≠ Real.log (δ / 4) := by
      intro h
      have h3 : Real.exp (Real.log (δ / 2)) = Real.exp (Real.log (δ / 4)) := by rw [h]
      rw [Real.exp_log (by linarith : (0:ℝ) < δ / 2),
        Real.exp_log (by linarith : (0:ℝ) < δ / 4)] at h3
      linarith
    have ha : κU - κL = 0 := by
      have hsub : (κU - κL) * (Real.log (1 / 9 - (1 / 9 - δ / 2))
          - Real.log (1 / 9 - (1 / 9 - δ / 4))) = 0 := by
        linear_combination e₁ - e₂
      rw [hl₁, hl₂, mul_eq_zero] at hsub
      rcases hsub with h | h
      · exact h
      · exact absurd (Complex.ofReal_inj.mp (sub_eq_zero.mp h)) hlogne
    have hb : κU + κL = 0 := by
      have h := e₁
      rw [hl₁, ha] at h
      simp only [zero_mul, zero_add] at h
      exact (mul_eq_zero.mp h).resolve_right
        (mul_ne_zero (by norm_num [Real.pi_ne_zero]) Complex.I_ne_zero)
    have hκU : κU = 0 := by
      have h2 : (2 : ℂ) * κU = 0 := by linear_combination ha + hb
      exact (mul_eq_zero.mp h2).resolve_left (by norm_num)
    have hκL : κL = 0 := by
      have h2 : (2 : ℂ) * κL = 0 := by linear_combination hb - ha
      exact (mul_eq_zero.mp h2).resolve_left (by norm_num)
    intro z hz
    rw [hκU, hκL]; simp

end Work.A14D
