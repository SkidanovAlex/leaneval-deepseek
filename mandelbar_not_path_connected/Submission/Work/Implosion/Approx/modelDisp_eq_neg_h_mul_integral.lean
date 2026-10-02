/-
Copyright: subproject `Submission/Work/Implosion/` of `mandelbar_not_path_connected`.

# The displacement as an integral (the "integrated" form of the Écalle coordinate)

`Disp.lean` defines the displacement of the Écalle coordinate as a difference of two
complex logarithms,

  `modelDisp a h u = (log (1+A₁) − log (1+A₂)) / (2a)`,   `A₁ = dispNum1 a h u`, `A₂ = dispNum2 a h u`,

and records `A₁ − A₂ = −2a·h(ζ(u))`.  This file proves the *integral representation*

  `modelDisp a h u = −h(ζ(u)) · ½ · ∫_{−1}^{1} (1 + (A₁+A₂)/2 + t·(A₂−A₁)/2)^{-1} dt`,

valid whenever the affine path `t ↦ 1 + (A₁+A₂)/2 + t·(A₂−A₁)/2` from `1+A₁` to `1+A₂`
stays in the slit plane.  This is the way the displacement is used in the estimates of
Hubbard–Schleicher §4: it shows that the increment of the Écalle coordinate is the
endpoint value `h(ζ(u))` weighted by a mean of `1/(1+A)` along the chord, so bounds on `h`
transfer directly to bounds on `modelDisp`.

The analytic content is the fundamental theorem of calculus for the branch of `log` on the
slit plane (`Complex.hasDerivAt_log`), applied to the chord.
-/
import Mathlib
import Submission.Work.Implosion.Ecalle
import Submission.Work.Implosion.Disp

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.Implosion.Approx

open Complex

/-- **The chord form of `log(1+A₂) − log(1+A₁)`.**  If the affine chord
`t ↦ 1 + (A₁+A₂)/2 + t·(A₂−A₁)/2`, `t ∈ [−1,1]`, joining `1+A₁` to `1+A₂` lies in the slit
plane, then

  `(A₂−A₁)/2 · ∫_{−1}^{1} (1 + (A₁+A₂)/2 + t·(A₂−A₁)/2)^{-1} dt = log(1+A₂) − log(1+A₁)`.

This is the fundamental theorem of calculus for the principal branch of the logarithm
along the chord. -/
theorem chord_mul_integral_eq_log_sub_log (A₁ A₂ : ℂ)
    (hslit : ∀ t : ℝ, t ∈ Set.Icc (-1:ℝ) 1 →
      (1 + (A₁+A₂)/2 + (t:ℂ)*((A₂-A₁)/2)) ∈ Complex.slitPlane) :
    ((A₂-A₁)/2) * ∫ t in (-1:ℝ)..1, (1 + (A₁+A₂)/2 + (t:ℂ)*((A₂-A₁)/2))⁻¹
      = Complex.log (1+A₂) - Complex.log (1+A₁) := by
  set c : ℂ := 1 + (A₁+A₂)/2 with hc
  set d : ℂ := (A₂-A₁)/2 with hd
  have hslit' : ∀ t : ℝ, t ∈ Set.Icc (-1:ℝ) 1 → c + (t:ℂ)*d ∈ Complex.slitPlane := by
    intro t ht; rw [hc, hd]; exact hslit t ht
  -- the chord is differentiable with derivative `d`, and `log` is holomorphic on the slit plane
  have hderiv : ∀ x ∈ Set.uIcc (-1:ℝ) 1,
      HasDerivAt (fun t : ℝ => Complex.log (c + (t:ℂ)*d)) (d * (c + (x:ℂ)*d)⁻¹) x := by
    intro x hx
    have hx' : x ∈ Set.Icc (-1:ℝ) 1 := by rwa [Set.uIcc_of_le (by norm_num)] at hx
    have hG : HasDerivAt (fun t : ℝ => c + (t:ℂ)*d) d x := by
      have h1 : HasDerivAt (fun y : ℝ => (y:ℂ)) (1:ℂ) x := by
        simpa using (hasDerivAt_id x).ofReal_comp
      have h2 := h1.mul_const d
      simpa using h2.const_add c
    have := hG.clog_real (hslit' x hx')
    rw [div_eq_mul_inv] at this
    exact this
  have hint : IntervalIntegrable (fun x : ℝ => d * (c + (x:ℂ)*d)⁻¹) MeasureTheory.volume
      (-1:ℝ) 1 := by
    apply ContinuousOn.intervalIntegrable
    apply ContinuousOn.mul continuousOn_const
    apply ContinuousOn.inv₀
    · fun_prop
    · intro x hx
      exact Complex.slitPlane_ne_zero (hslit' x (by rwa [Set.uIcc_of_le (by norm_num)] at hx))
  have key := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
  rw [← intervalIntegral.integral_const_mul, key]
  simp only [hc, hd]
  congr 1 <;> push_cast <;> ring_nf

/-- **The displacement is `−h(ζ)` times the chord mean of `1/(1+A)`.**

`modelDisp a h u = −h(ζ(u)) · ½ · ∫_{−1}^{1} (1 + (A₁+A₂)/2 + t·(A₂−A₁)/2)^{-1} dt`,
where `A₁ = dispNum1 a h u`, `A₂ = dispNum2 a h u` and `ζ(u) = ecalPt a u`, provided the
chord joining `1+A₁` to `1+A₂` lies in the slit plane. -/
theorem modelDisp_eq_neg_h_mul_integral (a : ℂ) (h : ℂ → ℂ) (u : ℂ) (ha : a ≠ 0)
    (hslit : ∀ t : ℝ, t ∈ Set.Icc (-1:ℝ) 1 →
      (1 + (dispNum1 a h u + dispNum2 a h u) / 2
        + (t:ℂ) * ((dispNum2 a h u - dispNum1 a h u) / 2)) ∈ Complex.slitPlane) :
    modelDisp a h u
      = -(h (ecalPt a u)) * ((1:ℂ)/2) * ∫ t in (-1:ℝ)..1,
          (1 + (dispNum1 a h u + dispNum2 a h u) / 2
            + (t:ℂ) * ((dispNum2 a h u - dispNum1 a h u) / 2))⁻¹ := by
  have h2a : (2:ℂ)*a ≠ 0 := by simp [ha]
  have hkey := chord_mul_integral_eq_log_sub_log (dispNum1 a h u) (dispNum2 a h u) hslit
  -- `h(ζ) = (A₂−A₁)/(2a)`, from the exact identity `A₁ − A₂ = −2a·h(ζ)`.
  have hhz : h (ecalPt a u) = (dispNum2 a h u - dispNum1 a h u)/(2*a) := by
    have hsub := dispNum1_sub_dispNum2 a h u
    have hsub' : dispNum2 a h u - dispNum1 a h u = 2*a*h (ecalPt a u) := by
      linear_combination -hsub
    rw [hsub', mul_div_cancel_left₀ _ h2a]
  rw [modelDisp, hhz]
  -- regroup the right-hand side and apply the chord representation
  rw [show -((dispNum2 a h u - dispNum1 a h u)/(2*a)) * ((1:ℂ)/2)
        * (∫ t in (-1:ℝ)..1, (1 + (dispNum1 a h u + dispNum2 a h u) / 2
            + (t:ℂ) * ((dispNum2 a h u - dispNum1 a h u) / 2))⁻¹)
      = -(((dispNum2 a h u - dispNum1 a h u)/2)
        * (∫ t in (-1:ℝ)..1, (1 + (dispNum1 a h u + dispNum2 a h u) / 2
            + (t:ℂ) * ((dispNum2 a h u - dispNum1 a h u) / 2))⁻¹))/(2*a) from by ring]
  rw [hkey]
  ring

end Work.Implosion.Approx
