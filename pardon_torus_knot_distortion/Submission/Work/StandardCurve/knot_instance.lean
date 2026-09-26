import Mathlib
import Submission.Work.Core.Torus
import Submission.Work.StandardCurve.injOn_coprime

/-!
# The standard `(p,q)`-torus curve as a `Knot`

This file packages the explicitly parametrized standard `(p,q)`-torus curve as an
element of the smooth-knot structure `Knot` of `ChallengeDeps`, for positive
coprime `p` and `q`.

The four fields of `Knot` are:

* `smooth` : the curve is `C^∞`.  The curve is the image under the linear
  isometry `WithLp.toLp 2` of the explicit componentwise vector
  `curveCoord p q t`, so smoothness reduces to smoothness of finitely many
  ordinary smooth functions (`contDiff_piLp`).
* `periodic` : the curve is `2π`-periodic, because the arguments `p t` and
  `q t` shift by integral multiplies of `2π`.
* `injOn` : injectivity on `[0, 2π)` for coprime `p, q` -- this is
  `Work.StandardCurve.injOn_coprime` from the imported file.
* `immersion` : the derivative never vanishes.  This is the only genuinely
  analytic point.  Differentiating the two first coordinates and taking the
  combination `-x'(t) sin (p t) + y'(t) cos (p t)` leaves
  `p * (2 + cos (q t))`, which is strictly positive since `2 + cos ≥ 1` and
  `p > 0`.  Hence the derivative cannot be the zero vector.

The main result is `Work.StandardCurve.knot_instance`.
-/

set_option linter.unusedSimpArgs false

open LeanEval.KnotTheory.PardonDistortion

namespace Work.StandardCurve

/-- The componentwise expression for the standard `(p,q)`-torus curve: the
coordinates of `standardTorusCurve p q t` as an explicit function
`Fin 3 → ℝ`. -/
noncomputable def curveCoord (p q : ℕ) (t : ℝ) : Fin 3 → ℝ :=
  ![ (2 + Real.cos ((q : ℝ) * t)) * Real.cos ((p : ℝ) * t),
     (2 + Real.cos ((q : ℝ) * t)) * Real.sin ((p : ℝ) * t),
     Real.sin ((q : ℝ) * t) ]

/-- `standardTorusCurve p q t` is `WithLp.toLp 2` applied to `curveCoord`. -/
lemma standardTorusCurve_eq_toLp (p q : ℕ) (t : ℝ) :
    standardTorusCurve p q t = WithLp.toLp 2 (curveCoord p q t) := by
  apply PiLp.ext
  intro i
  fin_cases i <;> rfl

/-- The standard torus curve is `C^∞`. -/
lemma standardTorusCurve_contDiff (p q : ℕ) :
    ContDiff ℝ (⊤ : ℕ∞) (standardTorusCurve p q) := by
  rw [show standardTorusCurve p q = fun t => WithLp.toLp 2 (curveCoord p q t) from
        funext (standardTorusCurve_eq_toLp p q)]
  rw [contDiff_piLp]
  intro i
  fin_cases i <;> (simp [curveCoord]; fun_prop)

/-- Coordinates of a derivative: if `f : ℝ → PiLp p E` is differentiable at `t`
with derivative `f'`, then each coordinate `s ↦ f s i` is differentiable at `t`
with derivative `f' i`. -/
lemma hasDerivAt_apply_piLp {ι : Type} [Fintype ι] {p : ENNReal} [Fact (1 ≤ p)] {E : ι → Type}
    [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace ℝ (E i)]
    {f : ℝ → PiLp p E} {f' : PiLp p E} {t : ℝ} (i : ι)
    (hf : HasDerivAt f f' t) : HasDerivAt (fun s => f s i) (f' i) t := by
  have h := (PiLp.hasFDerivAt_apply p (f t) i).comp t hf.hasFDerivAt
  have h2 := h.hasDerivAt
  convert h2 using 1
  · ext s; rfl
  · rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.toSpanSingleton_apply,
      PiLp.proj_apply, one_smul]

/-- The first coordinate `s ↦ (2 + cos (q s)) cos (p s)` of the standard torus
curve, with its derivative. -/
lemma hasDerivAt_coord_zero (p q : ℕ) (t : ℝ) :
    HasDerivAt (fun s => (2 + Real.cos ((q:ℝ)*s)) * Real.cos ((p:ℝ)*s))
      ((-((q:ℝ) * Real.sin ((q:ℝ)*t))) * Real.cos ((p:ℝ)*t)
        + (2 + Real.cos ((q:ℝ)*t)) * (-((p:ℝ) * Real.sin ((p:ℝ)*t)))) t := by
  have hc : HasDerivAt (fun s => Real.cos ((q:ℝ)*s)) (-((q:ℝ) * Real.sin ((q:ℝ)*t))) t := by
    have h := (Real.hasDerivAt_cos ((q:ℝ)*t)).comp t (hasDerivAt_const_mul (q:ℝ))
    simpa [Function.comp_def, mul_comm, mul_left_comm, mul_assoc] using h
  have hs : HasDerivAt (fun s => Real.cos ((p:ℝ)*s)) (-((p:ℝ) * Real.sin ((p:ℝ)*t))) t := by
    have h := (Real.hasDerivAt_cos ((p:ℝ)*t)).comp t (hasDerivAt_const_mul (p:ℝ))
    simpa [Function.comp_def, mul_comm, mul_left_comm, mul_assoc] using h
  exact (hc.const_add 2).mul hs

/-- The second coordinate `s ↦ (2 + cos (q s)) sin (p s)` of the standard torus
curve, with its derivative. -/
lemma hasDerivAt_coord_one (p q : ℕ) (t : ℝ) :
    HasDerivAt (fun s => (2 + Real.cos ((q:ℝ)*s)) * Real.sin ((p:ℝ)*s))
      ((-((q:ℝ) * Real.sin ((q:ℝ)*t))) * Real.sin ((p:ℝ)*t)
        + (2 + Real.cos ((q:ℝ)*t)) * ((p:ℝ) * Real.cos ((p:ℝ)*t))) t := by
  have hc : HasDerivAt (fun s => Real.cos ((q:ℝ)*s)) (-((q:ℝ) * Real.sin ((q:ℝ)*t))) t := by
    have h := (Real.hasDerivAt_cos ((q:ℝ)*t)).comp t (hasDerivAt_const_mul (q:ℝ))
    simpa [Function.comp_def, mul_comm, mul_left_comm, mul_assoc] using h
  have hs : HasDerivAt (fun s => Real.sin ((p:ℝ)*s)) ((p:ℝ) * Real.cos ((p:ℝ)*t)) t := by
    have h := (Real.hasDerivAt_sin ((p:ℝ)*t)).comp t (hasDerivAt_const_mul (p:ℝ))
    simpa [Function.comp_def, mul_comm, mul_left_comm, mul_assoc] using h
  exact (hc.const_add 2).mul hs

/-- The third coordinate `s ↦ sin (q s)` of the standard torus curve, with its
derivative. -/
lemma hasDerivAt_coord_two (q : ℕ) (t : ℝ) :
    HasDerivAt (fun s => Real.sin ((q:ℝ)*s)) ((q:ℝ) * Real.cos ((q:ℝ)*t)) t := by
  have h := (Real.hasDerivAt_sin ((q:ℝ)*t)).comp t (hasDerivAt_const_mul (q:ℝ))
  simpa [Function.comp_def, mul_comm, mul_left_comm, mul_assoc] using h

/-- The first coordinate of the derivative of the standard torus curve. -/
lemma deriv_apply_zero (p q : ℕ) (t : ℝ) :
    deriv (standardTorusCurve p q) t 0 =
      ((-((q:ℝ) * Real.sin ((q:ℝ)*t))) * Real.cos ((p:ℝ)*t)
        + (2 + Real.cos ((q:ℝ)*t)) * (-((p:ℝ) * Real.sin ((p:ℝ)*t)))) := by
  have hcont := standardTorusCurve_contDiff p q
  have hdiff : DifferentiableAt ℝ (standardTorusCurve p q) t :=
    (hcont.contDiffAt).differentiableAt (by simp)
  have hG : HasDerivAt (standardTorusCurve p q) (deriv (standardTorusCurve p q) t) t :=
    hdiff.hasDerivAt
  have h0 : HasDerivAt (fun s => standardTorusCurve p q s 0)
      (deriv (standardTorusCurve p q) t 0) t := hasDerivAt_apply_piLp 0 hG
  exact h0.unique (hasDerivAt_coord_zero p q t)

/-- The second coordinate of the derivative of the standard torus curve. -/
lemma deriv_apply_one (p q : ℕ) (t : ℝ) :
    deriv (standardTorusCurve p q) t 1 =
      ((-((q:ℝ) * Real.sin ((q:ℝ)*t))) * Real.sin ((p:ℝ)*t)
        + (2 + Real.cos ((q:ℝ)*t)) * ((p:ℝ) * Real.cos ((p:ℝ)*t))) := by
  have hcont := standardTorusCurve_contDiff p q
  have hdiff : DifferentiableAt ℝ (standardTorusCurve p q) t :=
    (hcont.contDiffAt).differentiableAt (by simp)
  have hG : HasDerivAt (standardTorusCurve p q) (deriv (standardTorusCurve p q) t) t :=
    hdiff.hasDerivAt
  have h0 : HasDerivAt (fun s => standardTorusCurve p q s 1)
      (deriv (standardTorusCurve p q) t 1) t := hasDerivAt_apply_piLp 1 hG
  exact h0.unique (hasDerivAt_coord_one p q t)

/-- The componentwise curve `curveCoord` is `2π`-periodic. -/
lemma curveCoord_add_two_pi (p q : ℕ) (t : ℝ) :
    curveCoord p q (t + 2 * Real.pi) = curveCoord p q t := by
  funext i
  fin_cases i <;>
    · simp only [curveCoord, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
        Matrix.cons_val_fin_one]
      have hp : (p:ℝ) * (t + 2 * Real.pi) = (p:ℝ) * t + (p:ℝ) * (2 * Real.pi) := by ring
      have hq : (q:ℝ) * (t + 2 * Real.pi) = (q:ℝ) * t + (q:ℝ) * (2 * Real.pi) := by ring
      rw [hp, hq]
      simp only [Real.cos_add_nat_mul_two_pi, Real.sin_add_nat_mul_two_pi]

/-- The standard torus curve is `2π`-periodic. -/
lemma standardTorusCurve_periodic (p q : ℕ) (t : ℝ) :
    standardTorusCurve p q (t + 2 * Real.pi) = standardTorusCurve p q t := by
  rw [standardTorusCurve_eq_toLp p q (t + 2 * Real.pi), standardTorusCurve_eq_toLp p q t,
    curveCoord_add_two_pi p q t]

/-- The derivative of the standard torus curve never vanishes (for `p > 0`). -/
lemma standardTorusCurve_deriv_ne_zero (p q : ℕ) (hp : 0 < p) (t : ℝ) :
    deriv (standardTorusCurve p q) t ≠ 0 := by
  intro hzero
  have hzero0 : deriv (standardTorusCurve p q) t 0 = 0 := by
    have := congrArg (fun v : R3 => v 0) hzero
    simpa using this
  have hzero1 : deriv (standardTorusCurve p q) t 1 = 0 := by
    have := congrArg (fun v : R3 => v 1) hzero
    simpa using this
  rw [deriv_apply_zero p q t] at hzero0
  rw [deriv_apply_one p q t] at hzero1
  have hpos : 0 < (p:ℝ) * (2 + Real.cos ((q:ℝ)*t)) := by
    have hp' : (0:ℝ) < (p:ℝ) := by exact_mod_cast hp
    have hcos : (1:ℝ) ≤ 2 + Real.cos ((q:ℝ)*t) := by
      linarith [Real.neg_one_le_cos ((q:ℝ)*t)]
    exact mul_pos hp' (by linarith)
  -- `-x'(t) sin (p t) + y'(t) cos (p t) = p (2 + cos (q t)) (sin² + cos²)`.
  have key : -((-(↑q * Real.sin (↑q * t)) * Real.cos (↑p * t)
        + (2 + Real.cos (↑q * t)) * -(↑p * Real.sin (↑p * t)))) * Real.sin (↑p * t)
      + ((-(↑q * Real.sin (↑q * t)) * Real.sin (↑p * t)
        + (2 + Real.cos (↑q * t)) * (↑p * Real.cos (↑p * t)))) * Real.cos (↑p * t)
      = (↑p * (2 + Real.cos (↑q * t))) * (Real.sin (↑p * t) ^ 2 + Real.cos (↑p * t) ^ 2) :=
    by ring
  rw [Real.sin_sq_add_cos_sq, mul_one, hzero0, hzero1] at key
  have key2 : (0:ℝ) = (p:ℝ) * (2 + Real.cos ((q:ℝ)*t)) := by
    rw [← key]; ring
  exact (ne_of_gt hpos) key2.symm

/-- **The standard `(p,q)`-torus curve is a knot.**  For positive coprime `p, q`
there is a smooth knot whose underlying curve is exactly
`standardTorusCurve p q`. -/
theorem knot_instance (p q : ℕ) (hp : 0 < p) (hq : 0 < q) (hc : Nat.Coprime p q) :
    ∃ K : LeanEval.KnotTheory.PardonDistortion.Knot,
      ∀ t, K.curve t = LeanEval.KnotTheory.PardonDistortion.standardTorusCurve p q t := by
  refine ⟨{ curve := standardTorusCurve p q
            smooth := standardTorusCurve_contDiff p q
            periodic := standardTorusCurve_periodic p q
            injOn := injOn_coprime p q hp hq hc
            immersion := fun t => standardTorusCurve_deriv_ne_zero p q hp t }, ?_⟩
  intro t
  rfl

end Work.StandardCurve
