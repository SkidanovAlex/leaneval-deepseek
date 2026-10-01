import Mathlib
import Submission.Work.ZeroFreeTables.tf71Q_defs
import Submission.Work.ZeroFreeTables.testFn71_defs

noncomputable section
namespace Work.ZeroFreeTables

/-- Derivative of the `t`-dependent factor of the antiderivative `tf71Q`. -/
private lemma deriv_P (u v γ W ζ T t : ℝ) :
    HasDerivAt
      (fun s : ℝ => (u - (1/2)*s) * Real.cos (ζ*s) + (v - (T/2)*s) * Real.sin (ζ*s)
        + (2*γ - W - s))
      ((-(1/2)) * Real.cos (ζ*t) - (u - (1/2)*t) * ζ * Real.sin (ζ*t)
        - (T/2) * Real.sin (ζ*t) + (v - (T/2)*t) * ζ * Real.cos (ζ*t) - 1) t := by
  have h1 : HasDerivAt (fun s : ℝ => (u - (1/2)*s) * Real.cos (ζ*s))
      ((-(1/2)) * Real.cos (ζ*t) - (u - (1/2)*t) * ζ * Real.sin (ζ*t)) t := by
    refine (((hasDerivAt_const_mul (1/2)).const_sub u).mul
      ((Real.hasDerivAt_cos (ζ*t)).comp t (hasDerivAt_const_mul ζ))).congr_deriv ?_
    simp only [Function.comp_apply]; ring
  have h2 : HasDerivAt (fun s : ℝ => (v - (T/2)*s) * Real.sin (ζ*s))
      ((-(T/2)) * Real.sin (ζ*t) + (v - (T/2)*t) * ζ * Real.cos (ζ*t)) t := by
    refine (((hasDerivAt_const_mul (T/2)).const_sub v).mul
      ((Real.hasDerivAt_sin (ζ*t)).comp t (hasDerivAt_const_mul ζ))).congr_deriv ?_
    simp only [Function.comp_apply]; ring
  have h3 : HasDerivAt (fun s : ℝ => 2*γ - W - s) (-1) t :=
    (hasDerivAt_id t).const_sub (2*γ - W)
  refine ((h1.add h2).add h3).congr_deriv ?_
  ring

/-- The algebraic identity `λ·P + P' = cf/A` underlying the derivative of `tf71Q`. -/
private lemma key_ident (A ζ T lam γ u v β W t : ℝ) (hA : A = lam * (1+T^2)) (hζ : ζ = lam*T)
    (hu : lam*u + ζ*v - 1/2 = A*γ - 1) (hv : lam*v - ζ*u - T/2 = β) :
    lam * ((u - (1/2)*t) * Real.cos (ζ*t) + (v - (T/2)*t) * Real.sin (ζ*t) + (2*γ - W - t))
      + ((-(1/2)) * Real.cos (ζ*t) - (u - (1/2)*t) * ζ * Real.sin (ζ*t)
         - (T/2) * Real.sin (ζ*t) + (v - (T/2)*t) * ζ * Real.cos (ζ*t) - 1)
    = (A*γ - 1 - (A/2)*t) * Real.cos (ζ*t) + β * Real.sin (ζ*t)
      + (2*lam*γ - lam*W - lam*t - 1) := by
  simp only [hA, hζ] at hu hv ⊢
  linear_combination (Real.cos (lam*T*t)) * hu + (Real.sin (lam*T*t)) * hv

/-- Abstract form of the derivative computation for `tf71Q`. -/
private lemma hasDerivAt_form (A ζ T lam γ u v β W t : ℝ)
    (hA : A = lam * (1+T^2)) (hζ : ζ = lam*T)
    (hu : lam*u + ζ*v - 1/2 = A*γ - 1) (hv : lam*v - ζ*u - T/2 = β) :
    HasDerivAt (fun s : ℝ => A * Real.exp (lam * s) *
        ((u - (1/2)*s) * Real.cos (ζ*s) + (v - (T/2)*s) * Real.sin (ζ*s) + (2*γ - W - s)))
      (Real.exp (lam * t) * (A * ((A*γ - 1 - (A/2)*t) * Real.cos (ζ*t) + β * Real.sin (ζ*t)
        + (2*lam*γ - lam*W - lam*t - 1)))) t := by
  have hexp : HasDerivAt (fun s : ℝ => Real.exp (lam * s)) (Real.exp (lam*t) * lam) t :=
    (Real.hasDerivAt_exp (lam*t)).comp t (hasDerivAt_const_mul lam)
  have hAe : HasDerivAt (fun s : ℝ => A * Real.exp (lam*s)) (A * (Real.exp (lam*t) * lam)) t :=
    hexp.const_mul A
  have hprod := hAe.mul (deriv_P u v γ W ζ T t)
  refine hprod.congr_deriv ?_
  have hk := key_ident A ζ T lam γ u v β W t hA hζ hu hv
  rw [← hk]
  ring

/-- `tf71β` in terms of `sin` and `cos`. -/
private lemma tf71β_eq (θ : ℝ) :
    tf71β θ = 2 * (Real.cos θ / Real.sin θ) - Real.cos (2*θ) / Real.sin (2*θ) := by
  rw [tf71β, Real.tan_eq_sin_div_cos, Real.tan_eq_sin_div_cos, inv_div, inv_div]

/-- The closed form of `tf71cf` written with `tf71A`, `tf71β` and the constant term. -/
private lemma tf71cf_closed (θ lam t : ℝ) (hθ0 : 0 < θ) (hθ1 : θ < Real.pi / 2) :
    tf71cf θ lam t = tf71A θ lam * ((tf71A θ lam * tf71γ θ lam - 1 - (tf71A θ lam/2)*t)
        * Real.cos (tf71ζ θ lam * t) + tf71β θ * Real.sin (tf71ζ θ lam * t)
        + (2*lam*tf71γ θ lam - 2 - lam*t)) := by
  have hs : Real.sin θ ≠ 0 := tf71_sinθ_ne hθ0 hθ1
  have hs2 : Real.sin (2*θ) ≠ 0 := tf71_sin2θ_ne hθ0 hθ1
  rw [tf71β_eq θ]
  simp only [tf71cf, tf71A]
  rw [Real.sin_sub, Real.sin_sub]
  field_simp [hs, hs2]
  ring

theorem tf71Q_hasDerivAt (θ lam : ℝ) (hθ0 : 0 < θ) (hθ1 : θ < Real.pi / 2) (hlam : 0 < lam)
    (t : ℝ) :
    HasDerivAt (Work.ZeroFreeTables.tf71Q θ lam)
      (Real.exp (lam * t) * Work.ZeroFreeTables.tf71cf θ lam t) t := by
  have hlam0 : lam ≠ 0 := ne_of_gt hlam
  have htan0 : Real.tan θ ≠ 0 := ne_of_gt (tf71_tan_pos hθ0 hθ1)
  have hu : lam * tf71Qu θ lam + tf71ζ θ lam * tf71Qv θ lam - 1/2
      = tf71A θ lam * tf71γ θ lam - 1 := by
    simp only [tf71Qu, tf71Qv, tf71A, tf71ζ, tf71γ]
    field_simp
    ring
  have hv : lam * tf71Qv θ lam - tf71ζ θ lam * tf71Qu θ lam - Real.tan θ/2 = tf71β θ := by
    simp only [tf71Qu, tf71Qv, tf71A, tf71ζ, tf71γ]
    field_simp
    ring
  have hmain := hasDerivAt_form (tf71A θ lam) (tf71ζ θ lam) (Real.tan θ) lam (tf71γ θ lam)
    (tf71Qu θ lam) (tf71Qv θ lam) (tf71β θ) (1/lam) t rfl rfl hu hv
  refine hmain.congr_deriv ?_
  rw [tf71cf_closed θ lam t hθ0 hθ1]
  have hW : lam * (1/lam) = 1 := by field_simp
  rw [hW]
  ring

end Work.ZeroFreeTables
