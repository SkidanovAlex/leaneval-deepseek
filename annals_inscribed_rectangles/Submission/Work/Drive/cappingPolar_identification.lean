import Mathlib
import Submission.Work.Drive.CappingDefs

namespace Work.Drive

/-! ### Helpers for the polar identification -/

/-- From `polarLift p = polarLift q` with both radii positive, the radii agree: squaring the two
coordinate equalities and adding uses `cos² + sin² = 1`. -/
lemma polarLift_radius_eq {p q : ℝ × ℝ} (hp : 0 < p.1) (hq : 0 < q.1)
    (h : polarLift p = polarLift q) : p.1 = q.1 := by
  have h1 : p.1 * Real.cos (2 * Real.pi * p.2) = q.1 * Real.cos (2 * Real.pi * q.2) := by
    simpa [polarLift] using congrArg Prod.fst h
  have h2 : p.1 * Real.sin (2 * Real.pi * p.2) = q.1 * Real.sin (2 * Real.pi * q.2) := by
    simpa [polarLift] using congrArg Prod.snd h
  have e1 : (p.1 * Real.cos (2 * Real.pi * p.2)) ^ 2
      = (q.1 * Real.cos (2 * Real.pi * q.2)) ^ 2 := by rw [h1]
  have e2 : (p.1 * Real.sin (2 * Real.pi * p.2)) ^ 2
      = (q.1 * Real.sin (2 * Real.pi * q.2)) ^ 2 := by rw [h2]
  have hs : p.1 ^ 2 = q.1 ^ 2 := by
    nlinarith [e1, e2, Real.cos_sq_add_sin_sq (2 * Real.pi * p.2),
      Real.cos_sq_add_sin_sq (2 * Real.pi * q.2)]
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp hs with h' | h'
  · exact h'
  · nlinarith [hp, hq]

/-- From `polarLift p = polarLift q`, equal radii and positivity, the angles differ by an integer:
the unit-circle parametrisation `t ↦ (cos (2π t), sin (2π t))` factors through `Circle.exp`, whose
kernel is `2πℤ`. -/
lemma polarLift_angle_sub {p q : ℝ × ℝ} (hq : 0 < q.1)
    (h : polarLift p = polarLift q) (hpq : p.1 = q.1) :
    ∃ m : ℤ, p.2 = q.2 + m := by
  have h1 : Real.cos (2 * Real.pi * p.2) = Real.cos (2 * Real.pi * q.2) := by
    have hh : p.1 * Real.cos (2 * Real.pi * p.2) = q.1 * Real.cos (2 * Real.pi * q.2) := by
      simpa [polarLift] using congrArg Prod.fst h
    rw [hpq] at hh
    exact mul_left_cancel₀ (ne_of_gt hq) hh
  have h2 : Real.sin (2 * Real.pi * p.2) = Real.sin (2 * Real.pi * q.2) := by
    have hh : p.1 * Real.sin (2 * Real.pi * p.2) = q.1 * Real.sin (2 * Real.pi * q.2) := by
      simpa [polarLift] using congrArg Prod.snd h
    rw [hpq] at hh
    exact mul_left_cancel₀ (ne_of_gt hq) hh
  have hc : Circle.exp (2 * Real.pi * p.2) = Circle.exp (2 * Real.pi * q.2) := by
    apply Subtype.ext
    rw [Circle.coe_exp, Circle.coe_exp, Complex.exp_ofReal_mul_I, Complex.exp_ofReal_mul_I, h1, h2]
  obtain ⟨m, hm⟩ := Circle.exp_eq_exp.mp hc
  refine ⟨m, ?_⟩
  have hkey : 2 * Real.pi * p.2 = 2 * Real.pi * (q.2 + (m : ℝ)) := by rw [hm]; ring
  exact mul_left_cancel₀ (by positivity : (2 * Real.pi : ℝ) ≠ 0) hkey

/-- The converse direction of the injectivity modulo `ℤ`: equal radii and angles differing by an
integer give the same point, by the `2π`-periodicity of `cos` and `sin`. -/
lemma polarLift_eq_of {p q : ℝ × ℝ} (hpq : p.1 = q.1) (h : ∃ m : ℤ, p.2 = q.2 + m) :
    polarLift p = polarLift q := by
  obtain ⟨m, hm⟩ := h
  ext <;> simp only [polarLift]
  · rw [hpq, hm]
    have : 2 * Real.pi * (q.2 + (m : ℝ)) = 2 * Real.pi * q.2 + (m : ℝ) * (2 * Real.pi) := by ring
    rw [this, Real.cos_add_int_mul_two_pi]
  · rw [hpq, hm]
    have : 2 * Real.pi * (q.2 + (m : ℝ)) = 2 * Real.pi * q.2 + (m : ℝ) * (2 * Real.pi) := by ring
    rw [this, Real.sin_add_int_mul_two_pi]

/-- Existence of the polar angle: every non-zero vector is a `polarLift` value with positive radius,
via `Complex.arg` and the norm. -/
lemma polarLift_surjective (v : ℝ × ℝ) (hv : v ≠ 0) :
    ∃ p : ℝ × ℝ, 0 < p.1 ∧ polarLift p = v := by
  obtain ⟨x, y⟩ := v
  have hv' : x ≠ 0 ∨ y ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hv (by rw [hcon.1, hcon.2]; rfl)
  set w : ℂ := (x : ℂ) + (y : ℂ) * Complex.I with hw
  have hwne : w ≠ 0 := by
    intro h
    have hre : w.re = 0 := by rw [h]; simp
    have him : w.im = 0 := by rw [h]; simp
    rw [hw] at hre him
    simp at hre him
    rcases hv' with hx | hy
    · exact hx hre
    · exact hy him
  refine ⟨(‖w‖, Complex.arg w / (2 * Real.pi)), ?_, ?_⟩
  · exact norm_pos_iff.mpr hwne
  · have hre : w.re = x := by rw [hw]; simp
    have him : w.im = y := by rw [hw]; simp
    simp only [polarLift]
    have harg : 2 * Real.pi * (Complex.arg w / (2 * Real.pi)) = Complex.arg w := by
      field_simp
    rw [harg, Complex.cos_arg hwne, Complex.sin_arg, hre, him]
    ext <;> field_simp

/-- The explicit derivative of `polarLift` at `p`: the matrix
`[[cos (2πψ), -2πr sin (2πψ)], [sin (2πψ), 2πr cos (2πψ)]]` (`r = p.1`, `ψ = p.2`), whose
determinant is `2πr`. -/
noncomputable def polarLiftDeriv (p : ℝ × ℝ) : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ) :=
  ((ContinuousLinearMap.fst ℝ ℝ ℝ).smulRight (Real.cos (2 * Real.pi * p.2))
      + (ContinuousLinearMap.snd ℝ ℝ ℝ).smulRight
          (-(2 * Real.pi * p.1) * Real.sin (2 * Real.pi * p.2))).prod
    ((ContinuousLinearMap.fst ℝ ℝ ℝ).smulRight (Real.sin (2 * Real.pi * p.2))
      + (ContinuousLinearMap.snd ℝ ℝ ℝ).smulRight
          ((2 * Real.pi * p.1) * Real.cos (2 * Real.pi * p.2)))

lemma hasFDerivAt_polarLift (p : ℝ × ℝ) :
    HasFDerivAt polarLift (polarLiftDeriv p) p := by
  have hcos : HasFDerivAt (fun p : ℝ × ℝ => Real.cos (2 * Real.pi * p.2))
      ((ContinuousLinearMap.toSpanSingleton ℝ (-Real.sin (2 * Real.pi * p.2))).comp
        ((2 * Real.pi) • ContinuousLinearMap.snd ℝ ℝ ℝ)) p := by
    have hinner : HasFDerivAt (fun p : ℝ × ℝ => 2 * Real.pi * p.2)
        ((2 * Real.pi) • ContinuousLinearMap.snd ℝ ℝ ℝ) p :=
      (hasFDerivAt_snd (𝕜 := ℝ)).const_mul (2 * Real.pi)
    exact (Real.hasDerivAt_cos (2 * Real.pi * p.2)).hasFDerivAt.comp p hinner
  have hsin : HasFDerivAt (fun p : ℝ × ℝ => Real.sin (2 * Real.pi * p.2))
      ((ContinuousLinearMap.toSpanSingleton ℝ (Real.cos (2 * Real.pi * p.2))).comp
        ((2 * Real.pi) • ContinuousLinearMap.snd ℝ ℝ ℝ)) p := by
    have hinner : HasFDerivAt (fun p : ℝ × ℝ => 2 * Real.pi * p.2)
        ((2 * Real.pi) • ContinuousLinearMap.snd ℝ ℝ ℝ) p :=
      (hasFDerivAt_snd (𝕜 := ℝ)).const_mul (2 * Real.pi)
    exact (Real.hasDerivAt_sin (2 * Real.pi * p.2)).hasFDerivAt.comp p hinner
  have h1 : HasFDerivAt (fun p : ℝ × ℝ => p.1 * Real.cos (2 * Real.pi * p.2))
      ((ContinuousLinearMap.fst ℝ ℝ ℝ).smulRight (Real.cos (2 * Real.pi * p.2))
        + (ContinuousLinearMap.snd ℝ ℝ ℝ).smulRight
            (-(2 * Real.pi * p.1) * Real.sin (2 * Real.pi * p.2))) p := by
    refine (hasFDerivAt_fst.mul hcos).congr_fderiv ?_
    refine ContinuousLinearMap.ext (fun x => ?_)
    simp only [add_apply, smul_apply,
      ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.toSpanSingleton_apply, smul_eq_mul]
    ring
  have h2 : HasFDerivAt (fun p : ℝ × ℝ => p.1 * Real.sin (2 * Real.pi * p.2))
      ((ContinuousLinearMap.fst ℝ ℝ ℝ).smulRight (Real.sin (2 * Real.pi * p.2))
        + (ContinuousLinearMap.snd ℝ ℝ ℝ).smulRight
            ((2 * Real.pi * p.1) * Real.cos (2 * Real.pi * p.2))) p := by
    refine (hasFDerivAt_fst.mul hsin).congr_fderiv ?_
    refine ContinuousLinearMap.ext (fun x => ?_)
    simp only [add_apply, smul_apply,
      ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.toSpanSingleton_apply, smul_eq_mul]
    ring
  have h := h1.prodMk h2
  exact h

lemma fderiv_polarLift (p : ℝ × ℝ) :
    fderiv ℝ polarLift p = polarLiftDeriv p :=
  (hasFDerivAt_polarLift p).fderiv

lemma polarLiftDeriv_surjective (p : ℝ × ℝ) (hp : 0 < p.1) :
    Function.Surjective (polarLiftDeriv p) := by
  intro y
  obtain ⟨y1, y2⟩ := y
  refine ⟨(y1 * Real.cos (2 * Real.pi * p.2) + y2 * Real.sin (2 * Real.pi * p.2),
      (y2 * Real.cos (2 * Real.pi * p.2) - y1 * Real.sin (2 * Real.pi * p.2))
        / (2 * Real.pi * p.1)), ?_⟩
  have hk : (2 * Real.pi * p.1) ≠ 0 := by positivity
  simp only [polarLiftDeriv, ContinuousLinearMap.prod_apply, add_apply,
      ContinuousLinearMap.smulRight_apply, smul_eq_mul, ContinuousLinearMap.coe_fst',
      ContinuousLinearMap.coe_snd', Prod.mk.injEq]
  set c := Real.cos (2 * Real.pi * p.2) with hc
  set s := Real.sin (2 * Real.pi * p.2) with hs
  have hcs : c ^ 2 + s ^ 2 = 1 := by rw [hc, hs]; exact Real.cos_sq_add_sin_sq _
  constructor
  · field_simp
    ring_nf
    linear_combination y1 * hcs
  · field_simp
    ring_nf
    linear_combination y2 * hcs

/-- **The polar identification `(0,∞) × S¹ ≅ ℝ² ∖ {0}`: the analytic half of the capping.**

`polarLift (r, ψ) = (r cos (2πψ), r sin (2πψ))` (see `Submission.Work.Drive.CappingDefs`) is the polar
parametrisation of the punctured plane with `ℝ/ℤ`-valued angle.  This asserts that `polarLift` identifies
`(0,∞) × ℝ/ℤ` with `ℝ² ∖ {0}`: (i) for positive radii, `polarLift p = polarLift q` holds iff `p.1 = q.1`
and the angles differ by an integer (injectivity modulo the `ℤ`-period); (ii) every non-zero vector is a
`polarLift` value with positive radius (existence of the polar angle); (iii) `fderiv ℝ polarLift p` is onto
at every point of positive radius — equivalently invertible, since the Jacobian has determinant
`2π r ≠ 0` — so `polarLift` is a local diffeomorphism there.

This is the position-angle coordinate of the boundary torus of the configuration space
`(ℝ² ∖ {0}) × S¹ × {0}`.  With the already-proven torus-level gluing facts in `CappingDefs`
(`glueTorus_preimage_t21`: the gluing `(θ, φ) ↦ (φ, θ + 2φ)` carries the `(2,1)`-torus-knot family onto
the meridian family) and with `Work.Drive.doubledTangent_winding` (the doubled tangent direction winds
twice over a period, so the boundary `∂M` of the configuration Möbius strip is a `(2,1)`-curve), this
makes `∂M` a meridian after the gluing, i.e. a curve bounding a disk of the cap.  That is the input the
chain-level representative of Hugelmeyer's class `ω_P` needs on the route to `Work.Drive.chainParity`; it
is the first (analytic) brick of the capping. -/
theorem cappingPolar_identification :
    (∀ p q : ℝ × ℝ, 0 < p.1 → 0 < q.1 →
        (polarLift p = polarLift q ↔ p.1 = q.1 ∧ ∃ m : ℤ, p.2 = q.2 + m)) ∧
      (∀ v : ℝ × ℝ, v ≠ 0 → ∃ p : ℝ × ℝ, 0 < p.1 ∧ polarLift p = v) ∧
      (∀ p : ℝ × ℝ, 0 < p.1 → Function.Surjective (fderiv ℝ polarLift p)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro p q hp hq
    constructor
    · intro h
      exact ⟨polarLift_radius_eq hp hq h, polarLift_angle_sub hq h (polarLift_radius_eq hp hq h)⟩
    · rintro ⟨hpq, hm⟩
      exact polarLift_eq_of hpq hm
  · intro v hv
    exact polarLift_surjective v hv
  · intro p hp
    rw [fderiv_polarLift]
    exact polarLiftDeriv_surjective p hp

end Work.Drive
