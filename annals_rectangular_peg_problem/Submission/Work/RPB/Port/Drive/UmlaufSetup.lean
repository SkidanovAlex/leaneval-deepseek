import Mathlib

/-!
# Setup for Hopf's Umlaufsatz (`Work.RPB.Port.Drive.umlauf`)

Definitions used by the proof of `Submission.Drive.UmlaufProp`:

* `curve γ : ℝ → ℝ × ℝ` is the plane curve `t ↦ γ (Circle.exp t)`.
* `toC : ℝ × ℝ → ℂ` is the linear identification `(x,y) ↦ x + y * I`.
* `dirOf z : Circle` is the direction of a nonzero complex number (junk at `0`).
* `tangDir c t`, `secDir c s t` are the directions of the tangent and of the secant.
* `tri t₀` is the closed triangle `{t₀ ≤ s ≤ t ≤ t₀ + 2π}` on which Hopf's secant map lives,
  and `sigmaPt c t₀` is Hopf's map `σ` (tangent/secant direction) on it.
-/

namespace Work.RPB.Port.Drive

open scoped ContDiff

/-- The plane curve underlying a parametrised Jordan curve: `t ↦ γ (Circle.exp t)`. -/
noncomputable def curve (γ : Circle → ℝ × ℝ) : ℝ → ℝ × ℝ := fun t => γ (Circle.exp t)

/-- The linear identification `(x, y) ↦ x + y * I` of `ℝ × ℝ` with `ℂ`. -/
noncomputable def toC : ℝ × ℝ → ℂ := fun p => (p.1 : ℂ) + (p.2 : ℂ) * Complex.I

@[simp] lemma toC_re (p : ℝ × ℝ) : (toC p).re = p.1 := by simp [toC]
@[simp] lemma toC_im (p : ℝ × ℝ) : (toC p).im = p.2 := by simp [toC]

@[simp] lemma toC_zero : toC 0 = 0 := by simp [toC]

@[simp] lemma toC_add (p q : ℝ × ℝ) : toC (p + q) = toC p + toC q := by
  apply Complex.ext <;> simp [toC]

@[simp] lemma toC_sub (p q : ℝ × ℝ) : toC (p - q) = toC p - toC q := by
  apply Complex.ext <;> simp [toC]

@[simp] lemma toC_neg (p : ℝ × ℝ) : toC (-p) = -toC p := by
  apply Complex.ext <;> simp [toC]

@[simp] lemma toC_smul (a : ℝ) (p : ℝ × ℝ) : toC (a • p) = (a : ℂ) * toC p := by
  apply Complex.ext <;> simp [toC]

/-- Euler's formula, read through `toC`. -/
lemma toC_cos_sin (a : ℝ) : toC (Real.cos a, Real.sin a) = Complex.exp (a * Complex.I) := by
  apply Complex.ext
  · rw [toC_re, Complex.exp_ofReal_mul_I_re]
  · rw [toC_im, Complex.exp_ofReal_mul_I_im]

lemma toC_injective : Function.Injective toC := by
  intro p q h
  have h1 : p.1 = q.1 := by simpa using congrArg Complex.re h
  have h2 : p.2 = q.2 := by simpa using congrArg Complex.im h
  exact Prod.ext h1 h2

/-- The norm of a real number, viewed in `ℂ`. -/
lemma norm_ofReal_complex (r : ℝ) : ‖(r : ℂ)‖ = |r| := by
  have h : ‖(r : ℂ)‖ ^ 2 = r ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_ofReal]; ring
  nlinarith [norm_nonneg (r : ℂ), abs_nonneg r, sq_abs r]

lemma toC_eq_zero_iff {p : ℝ × ℝ} : toC p = 0 ↔ p = 0 := by
  simpa using toC_injective.eq_iff (a := p) (b := 0)

lemma toC_ne_zero_iff {p : ℝ × ℝ} : toC p ≠ 0 ↔ p ≠ 0 :=
  not_congr toC_eq_zero_iff

lemma continuous_toC : Continuous toC := by
  refine Continuous.add ?_ ?_
  · exact Complex.continuous_ofReal.comp continuous_fst
  · exact (Complex.continuous_ofReal.comp continuous_snd).mul continuous_const

/-- Direction of a nonzero complex number, as a point of the unit circle. -/
noncomputable def dirOfNonzero (z : ℂ) (h : z ≠ 0) : Circle where
  val := z / (‖z‖ : ℂ)
  property := mem_sphere_zero_iff_norm.2 (by
    rw [norm_div, norm_ofReal_complex, abs_of_nonneg (norm_nonneg z)]
    exact div_self (norm_ne_zero_iff.mpr h))

/-- The direction of a complex number, as a point of the unit circle.
At `z = 0` it takes the junk value `1`. -/
noncomputable def dirOf (z : ℂ) : Circle := if h : z = 0 then 1 else dirOfNonzero z h

lemma dirOf_coe {z : ℂ} (hz : z ≠ 0) : (dirOf z : ℂ) = z / (‖z‖ : ℂ) := by
  rw [dirOf, dif_neg hz]
  rfl

lemma dirOf_zero : dirOf 0 = 1 := by
  rw [dirOf, dif_pos rfl]

/-- The direction of the tangent of a curve at a point. -/
noncomputable def tangDir (c : ℝ → ℝ × ℝ) (t : ℝ) : Circle := dirOf (toC (deriv c t))

/-- The direction of the secant from `c s` to `c t`. -/
noncomputable def secDir (c : ℝ → ℝ × ℝ) (s t : ℝ) : Circle := dirOf (toC (c t - c s))

/-- The closed triangle `{t₀ ≤ s ≤ t ≤ t₀ + 2π}`. -/
def tri (t₀ : ℝ) : Set (ℝ × ℝ) := {p | t₀ ≤ p.1 ∧ p.1 ≤ p.2 ∧ p.2 ≤ t₀ + 2 * Real.pi}

/-- The corner `(t₀, t₀)` of the triangle, used as the basepoint for the lift. -/
def triBase (t₀ : ℝ) : tri t₀ :=
  ⟨(t₀, t₀), le_rfl, le_rfl, by linarith [Real.pi_pos]⟩

lemma convex_tri (t₀ : ℝ) : Convex ℝ (tri t₀) := by
  intro p hp q hq a b ha hb hab
  simp only [tri, Set.mem_setOf_eq] at hp hq ⊢
  have e1 : (a • p + b • q).1 = a * p.1 + b * q.1 := rfl
  have e2 : (a • p + b • q).2 = a * p.2 + b * q.2 := rfl
  rw [e1, e2]
  refine ⟨?_, ?_, ?_⟩
  · have h3 : t₀ = a * t₀ + b * t₀ := by rw [← add_mul, hab, one_mul]
    linarith [mul_le_mul_of_nonneg_left hp.1 ha, mul_le_mul_of_nonneg_left hq.1 hb]
  · linarith [mul_le_mul_of_nonneg_left hp.2.1 ha, mul_le_mul_of_nonneg_left hq.2.1 hb]
  · have h3 : t₀ + 2 * Real.pi =
        a * (t₀ + 2 * Real.pi) + b * (t₀ + 2 * Real.pi) := by
      rw [← add_mul, hab, one_mul]
    linarith [mul_le_mul_of_nonneg_left hp.2.2 ha, mul_le_mul_of_nonneg_left hq.2.2 hb]

lemma nonempty_tri (t₀ : ℝ) : (tri t₀).Nonempty := ⟨(t₀, t₀), (triBase t₀).2⟩

instance instContractibleTri (t₀ : ℝ) : ContractibleSpace (tri t₀) :=
  (convex_tri t₀).contractibleSpace (nonempty_tri t₀)

instance instLocallyPathConnectedTri (t₀ : ℝ) : LocallyPathConnectedSpace (tri t₀) :=
  (convex_tri t₀).locallyPathConnectedSpace

/-- Hopf's secant map: the direction of the secant `c t - c s` in the interior,
tangent direction on the diagonal, and the negated tangent direction at the far corner. -/
noncomputable def sigmaPt (c : ℝ → ℝ × ℝ) (t₀ : ℝ) (p : ℝ × ℝ) : Circle :=
  if p.1 = t₀ ∧ p.2 = t₀ + 2 * Real.pi then -(tangDir c t₀)
  else if p.1 < p.2 then secDir c p.1 p.2
  else tangDir c p.1

/-- Hopf's secant map, as a map on the closed triangle. -/
noncomputable def sigma (c : ℝ → ℝ × ℝ) (t₀ : ℝ) : tri t₀ → Circle :=
  fun p => sigmaPt c t₀ p.1

/-- A regular closed plane curve: `C¹`, with nowhere vanishing derivative, `2π`-periodic and
injective up to the period. This is the exact structure of `t ↦ γ (Circle.exp t)` for a smooth
embedded closed plane curve `γ`. -/
structure RegCurve (c : ℝ → ℝ × ℝ) : Prop where
  /-- The curve is `C¹`. -/
  contDiff : ContDiff ℝ 1 c
  /-- The derivative never vanishes. -/
  deriv_ne_zero : ∀ t, deriv c t ≠ 0
  /-- The curve is `2π`-periodic. -/
  periodic : ∀ t, c (t + 2 * Real.pi) = c t
  /-- Two parameters give the same point exactly when they differ by a period. -/
  eq_iff : ∀ s t, c s = c t ↔ ∃ k : ℤ, s = t + 2 * Real.pi * k
  /-- The derivative is `2π`-periodic. -/
  deriv_periodic : ∀ t, deriv c (t + 2 * Real.pi) = deriv c t

end Work.RPB.Port.Drive
