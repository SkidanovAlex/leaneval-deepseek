import Mathlib
import Submission.Work.RPCore.Port.ODE.GlobalFlow

open scoped NNReal

namespace Work.RPA3

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-! ## Auxiliary lemmas about the time-hijacked field

This is the general (arbitrary complete normed space) version of `exists_flow_lipschitz`.  The
argument hijacks the time variable: the field `X p = (1, V p.1 p.2)` on `ℝ × E` is time-independent,
jointly Lipschitz and globally bounded, so the ported Picard argument
`Work.RPCore.Port.ODE.exists_isIntegralCurve_of_lipschitzWith` produces global integral curves. -/

/-- Points of `ℝ × E` with the same first coordinate: the product distance is the distance in the
second factor. -/
lemma dist_mk_const_fst_general {a b : E} {r : ℝ} :
    dist ((r, a) : ℝ × E) (r, b) = dist a b := by
  rw [Prod.dist_eq, dist_self]
  exact max_eq_right dist_nonneg

/-- The time-hijacked field `X p = (1, V p.1 p.2)` is Lipschitz with constant `max K 1`. -/
lemma lipschitzWith_timeHijack_general {V : ℝ → E → E} {K : NNReal}
    (hLip : LipschitzWith K (fun p : ℝ × E => V p.1 p.2)) :
    LipschitzWith (max K 1) (fun p : ℝ × E => ((1 : ℝ), V p.1 p.2)) := by
  refine LipschitzWith.of_dist_le_mul fun p q => ?_
  have h := hLip.dist_le_mul p q
  rw [dist_mk_const_fst_general]
  calc dist (V p.1 p.2) (V q.1 q.2) ≤ (K : ℝ) * dist p q := h
    _ ≤ ((max K 1 : NNReal) : ℝ) * dist p q := by
        apply mul_le_mul_of_nonneg_right _ dist_nonneg
        rw [NNReal.coe_max]
        exact le_max_left _ _

/-- The time-hijacked field `X p = (1, V p.1 p.2)` is bounded by `max M 1`. -/
lemma norm_timeHijack_le_general {V : ℝ → E → E} {M : ℝ} (hM : ∀ t x, ‖V t x‖ ≤ M) :
    ∀ z : ℝ × E, ‖((1 : ℝ), V z.1 z.2)‖ ≤ max M 1 := by
  intro z
  rw [Prod.norm_def, norm_one]
  exact max_le (le_max_right _ _) ((hM z.1 z.2).trans (le_max_left _ _))

/-- **Global flows.**  A time-dependent vector field on a complete normed space `E` which is
*jointly* Lipschitz in `(t,x)` and globally bounded has a global flow defined for all real times,
with `HasDerivAt` at every time. -/
theorem exists_flow_lipschitz_general {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] (V : ℝ → E → E) (K : NNReal)
    (hLip : LipschitzWith K (fun p : ℝ × E => V p.1 p.2)) (M : ℝ)
    (hM : ∀ t x, ‖V t x‖ ≤ M) :
    ∃ Φ : ℝ → E → E, (∀ x, Φ 0 x = x) ∧
      ∀ x t, HasDerivAt (fun s => Φ s x) (V t (Φ t x)) t := by
  classical
  have hLipX : LipschitzWith (max K 1) (fun p : ℝ × E => ((1 : ℝ), V p.1 p.2)) :=
    lipschitzWith_timeHijack_general hLip
  have hMX : ∀ z : ℝ × E, ‖((1 : ℝ), V z.1 z.2)‖ ≤ max M 1 := norm_timeHijack_le_general hM
  choose γ hγ using fun y : E =>
    Work.RPCore.Port.ODE.exists_isIntegralCurve_of_lipschitzWith
      (fun p : ℝ × E => ((1 : ℝ), V p.1 p.2)) hLipX hMX (0, y)
  refine ⟨fun t y => (γ y t).2, fun y => ?_, fun y t => ?_⟩
  · show (γ y 0).2 = y
    rw [(hγ y).1]
  · -- the first coordinate of the integral curve is the identity, by uniqueness for `y' = 1`
    have hfst : (γ y t).1 = t := by
      have hd : Differentiable ℝ (fun s => (γ y s).1 - s) := by
        have h1 : Differentiable ℝ (γ y) := fun s => ((hγ y).2 s).differentiableAt
        exact (h1.fst).sub differentiable_id
      have hd0 : ∀ s, deriv (fun s => (γ y s).1 - s) s = 0 := by
        intro s
        have h1 : HasDerivAt (fun s => (γ y s).1) 1 s := by
          have h2 := ((hγ y).2 s).hasFDerivAt.fst.hasDerivAt
          simpa using h2
        have h3 : HasDerivAt (fun s => (γ y s).1 - s) (1 - 1) s :=
          h1.sub (hasDerivAt_id s)
        rw [sub_self] at h3
        exact h3.deriv
      have hc := is_const_of_deriv_eq_zero hd hd0 t 0
      rw [(hγ y).1] at hc
      simp only [sub_zero] at hc
      linarith
    -- the second coordinate solves the original time-dependent ODE
    have hsnd : HasDerivAt (fun s => (γ y s).2) (V (γ y t).1 (γ y t).2) t := by
      have h2 := ((hγ y).2 t).hasFDerivAt.snd.hasDerivAt
      simpa using h2
    rw [hfst] at hsnd
    exact hsnd

end Work.RPA3
