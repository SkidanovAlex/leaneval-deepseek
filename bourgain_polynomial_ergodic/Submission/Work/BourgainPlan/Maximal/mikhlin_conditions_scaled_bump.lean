import Mathlib
import Submission.Work.BourgainPlan.Thm52.CircleLiftDefs
import Submission.Work.BourgainPlan.Maximal.iw_superset

/-!
# The Mikhlin conditions for a scaled bump

`Work.BourgainPlan.Maximal.mikhlin_conditions_scaled_bump`: if `η` is a `C²` bump supported in
`[-1/2, 1/2]` satisfying the Mikhlin conditions with constant `M`, and `|c| ≥ 1`, then the circle
symbol `ξ ↦ η (c · iwRep ξ)` again satisfies the Mikhlin conditions with the *same* constant `M`.

The two ingredients:

* `circleLift_scaled_bump_eq` — the lift of the rescaled symbol is the rescaled bump itself,
  `circleLift (η ∘ (c · iwRep)) = fun x ↦ η (c · (-x))`.  On the fundamental domain
  `Ioc (-1/2) (1/2)` the canonical lift `iwRep` inverts the quotient map, so the lift is
  `x ↦ η (-(c x))`; because `|c| ≥ 1` this already vanishes for `|x| ≥ 1/2`, hence the truncation
  inherent in `circleLift` is invisible.  (The single point `x = 1/2`, where the canonical lift
  wraps around, is handled separately: `iwRep (-(1/2)) = 1/2`, and both the lift and the rescaled
  bump vanish there.)

* `scaled_bump_mikhlin_bounds` — the Mikhlin conditions are *invariant under scaling*: for any
  `d : ℝ`, the function `x ↦ η (d x)` obeys the same three bounds with the same constant `M`,
  because `|x| ‖d · η'(d x)‖ = |d x| ‖η'(d x)‖` (`deriv_comp_mul_left`,
  `iteratedDeriv_comp_const_smul`).

No constant is lost: `|x|·|c|·‖η'(c x)‖ = |c x|·‖η'(c x)‖ ≤ M`.
-/

namespace Work.BourgainPlan.Maximal

open Work.BourgainPlan.Thm52

local notation "Circ" => Work.BourgainPlan.IonescuWainger.Circle

noncomputable section

/-- The canonical lift of the circle point `-1/2` is `1/2`: the interval `Ioc (-1/2) (1/2]` used by
`iwRep` excludes the left endpoint `-1/2`, so the representative of its class is the right
endpoint `1/2`.  (This is the single point where `iwRep` "wraps around", and it is the only point
at which the computation of the lift of a rescaled bump needs care.) -/
lemma iwRep_neg_half : iwRep (-((1/2 : ℝ) : Circ)) = 1 / 2 := by
  have h1 : ((-(1/2) : ℝ) : Circ) = ((1/2 : ℝ) : Circ) := by
    have h := AddCircle.coe_add_period (p := (1 : ℝ)) (-(1/2 : ℝ))
    rw [show (-(1/2 : ℝ)) + 1 = (1/2 : ℝ) by norm_num] at h
    exact h.symm
  have h2 : -((1/2 : ℝ) : Circ) = ((1/2 : ℝ) : Circ) := by
    rw [← AddCircle.coe_neg (1 : ℝ) (x := (1/2 : ℝ))]
    exact h1
  rw [h2]
  simp only [iwRep]
  exact AddCircle.liftIoc_coe_apply (by norm_num [Set.mem_Ioc])

/-- **The lift of a rescaled bump is the rescaled bump.**  If `η` vanishes for `|x| ≥ 1/2` and
`|c| ≥ 1`, then `circleLift (fun ξ => η (c * iwRep ξ)) = fun x => η (c * (-x))`.  The right-hand
side already vanishes outside `(-1/2, 1/2)`, so the truncation defining `circleLift` is invisible.

On `x ∈ Ioc (-1/2) (1/2)` with `x < 1/2` the canonical lift is inverted by
`AddCircle.liftIoc_coe_apply` at `-x ∈ Ioc (-1/2) (1/2]`; at `x = 1/2` the canonical lift of
`-(1/2 : Circ)` is `1/2` (`iwRep_neg_half`) and both sides vanish because `|c|/2 ≥ 1/2`. -/
lemma circleLift_scaled_bump_eq {η : ℝ → ℂ} {c : ℝ} (hc : 1 ≤ |c|)
    (hsupp : ∀ x : ℝ, 1 / 2 ≤ |x| → η x = 0) :
    circleLift (fun ξ => η (c * iwRep ξ)) = fun x : ℝ => η (c * (-x)) := by
  funext x
  by_cases hx : x ∈ Set.Ioc (-(1/2 : ℝ)) (1/2)
  · rw [circleLift_of_mem hx]
    rcases lt_or_eq_of_le hx.2 with hlt | heq
    · -- `x < 1/2`: the canonical lift of `-x` is `-x` itself
      have hmem : -x ∈ Set.Ioc (-(1/2 : ℝ)) (-(1/2 : ℝ) + 1) :=
        ⟨by linarith [hx.1], by linarith [hx.1]⟩
      have hcoe : -((x : ℝ) : Circ) = ((-x : ℝ) : Circ) :=
        (AddCircle.coe_neg (1 : ℝ) (x := x)).symm
      rw [hcoe]
      have hrep : iwRep ((-x : ℝ) : Circ) = -x := by
        simp only [iwRep]
        exact AddCircle.liftIoc_coe_apply hmem
      rw [hrep]
    · -- `x = 1/2`: both sides vanish
      subst heq
      rw [iwRep_neg_half]
      have h1 : (1 : ℝ) / 2 ≤ |c * (1/2)| := by
        rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1/2)]
        linarith [hc]
      have h2 : (1 : ℝ) / 2 ≤ |c * (-(1/2))| := by
        rw [abs_mul, abs_neg, abs_of_pos (by norm_num : (0 : ℝ) < 1/2)]
        linarith [hc]
      rw [hsupp (c * (1/2)) h1, hsupp (c * (-(1/2))) h2]
  · -- `x ∉ Ioc (-1/2) (1/2)`: the lift vanishes, and so does the rescaled bump
    rw [circleLift_of_notMem hx]
    symm
    have hxor : x ≤ -(1/2) ∨ (1/2 : ℝ) < x := by
      by_contra h
      rw [not_or] at h
      exact hx ⟨not_le.mp h.1, not_lt.mp h.2⟩
    have hxabs : (1 : ℝ) / 2 ≤ |x| := by
      rcases hxor with h | h
      · rw [abs_of_neg (by linarith)]; linarith
      · rw [abs_of_pos (by linarith)]; linarith
    have h2 : (1 : ℝ) / 2 ≤ |c * (-x)| := by
      rw [abs_mul, abs_neg]
      calc (1 : ℝ) / 2 ≤ |x| := hxabs
        _ = 1 * |x| := (one_mul _).symm
        _ ≤ |c| * |x| := mul_le_mul_of_nonneg_right hc (abs_nonneg x)
    rw [hsupp (c * -x) h2]

/-- **The Mikhlin conditions are invariant under rescaling.**  If `η` satisfies the three
`L^∞`-bounds with constant `M` (and is `C²`), then so does `x ↦ η (d x)` for any `d : ℝ`, with the
same constant: `|x| ‖deriv (η ∘ (d ·)) x‖ = |x| |d| ‖η'(d x)‖ = |d x| ‖η'(d x)‖` by
`deriv_comp_mul_left`, and similarly `|x|² ‖(η ∘ (d ·))'' x‖ = |d x|² ‖η''(d x)‖` by
`iteratedDeriv_comp_const_smul`. -/
lemma scaled_bump_mikhlin_bounds {η : ℝ → ℂ} {M d : ℝ}
    (hcont : ContDiff ℝ 2 η) (hbd : ∀ x : ℝ, ‖η x‖ ≤ M)
    (h1 : ∀ x : ℝ, |x| * ‖deriv η x‖ ≤ M)
    (h2 : ∀ x : ℝ, |x| ^ 2 * ‖iteratedDeriv 2 η x‖ ≤ M) :
    ContDiff ℝ 2 (fun x : ℝ => η (d * x)) ∧
    (∀ x : ℝ, ‖η (d * x)‖ ≤ M) ∧
    (∀ x : ℝ, |x| * ‖deriv (fun x : ℝ => η (d * x)) x‖ ≤ M) ∧
    (∀ x : ℝ, |x| ^ 2 * ‖iteratedDeriv 2 (fun x : ℝ => η (d * x)) x‖ ≤ M) := by
  refine ⟨?_, fun x => hbd _, ?_, ?_⟩
  · exact hcont.comp (by fun_prop)
  · intro x
    rw [deriv_comp_mul_left d η x, norm_smul, Real.norm_eq_abs]
    have h : |x| * |d| = |d * x| := by rw [abs_mul, mul_comm]
    rw [← mul_assoc, h]
    exact h1 (d * x)
  · intro x
    rw [iteratedDeriv_comp_const_smul hcont d, norm_smul, Real.norm_eq_abs]
    have h : |x| ^ 2 * |d ^ 2| = |d * x| ^ 2 := by rw [abs_pow, abs_mul]; ring
    rw [← mul_assoc, h]
    exact h2 (d * x)

/-- **The Mikhlin conditions for a scaled bump**: if `η` is a `C²` bump bounded by `M` with the Mikhlin bounds `|x|‖η'‖ ≤ M`, `|x|²‖η''‖ ≤ M`, supported in `[-1/2,1/2]`, and `1 ≤ |c|`, then the circle symbol `ξ ↦ η (c · iwRep ξ)` (whose `circleLift` is the rescaled bump `x ↦ η (∓ c x)`, vanishing at the boundary) again satisfies the Mikhlin conditions with the *same* constant `M` — no constant is lost, since `|x|·|c|·‖η'(c x)‖ = |c x|·‖η'(c x)‖ ≤ M`. -/
theorem mikhlin_conditions_scaled_bump {η : ℝ → ℂ} {M c : ℝ} (hM : 0 ≤ M) (hc : 1 ≤ |c|) :
    ContDiff ℝ 2 η →
    (∀ x : ℝ, ‖η x‖ ≤ M) →
    (∀ x : ℝ, |x| * ‖deriv η x‖ ≤ M) →
    (∀ x : ℝ, |x| ^ 2 * ‖iteratedDeriv 2 η x‖ ≤ M) →
    (∀ x : ℝ, 1 / 2 ≤ |x| → η x = 0) →
    ContDiff ℝ 2 (Work.BourgainPlan.Thm52.circleLift
        (fun ξ => η (c * Work.BourgainPlan.Maximal.iwRep ξ))) ∧
    (∀ x : ℝ, ‖Work.BourgainPlan.Thm52.circleLift
        (fun ξ => η (c * Work.BourgainPlan.Maximal.iwRep ξ)) x‖ ≤ M) ∧
    (∀ x : ℝ, |x| * ‖deriv (Work.BourgainPlan.Thm52.circleLift
        (fun ξ => η (c * Work.BourgainPlan.Maximal.iwRep ξ))) x‖ ≤ M) ∧
    (∀ x : ℝ, |x| ^ 2 * ‖iteratedDeriv 2 (Work.BourgainPlan.Thm52.circleLift
        (fun ξ => η (c * Work.BourgainPlan.Maximal.iwRep ξ))) x‖ ≤ M) := by
  intro hcont hbd h1 h2 hsupp
  -- the lift is the rescaled bump `x ↦ η ((-c) · x)`
  have hL : circleLift (fun ξ => η (c * iwRep ξ)) = fun x : ℝ => η ((-c) * x) := by
    rw [circleLift_scaled_bump_eq hc hsupp]
    funext x
    congr 1
    ring
  rw [hL]
  exact scaled_bump_mikhlin_bounds hcont hbd h1 h2

end

end Work.BourgainPlan.Maximal
