import Mathlib
import Submission.Work.Diff.GE.uhlenbeck_defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The inverse-square-root family of a family of symmetric matrices

This file proves

`Work.Diff.GE.matrix_sqrt_family_kit`:
for a family `M : ℝ → Matrix (Fin n) (Fin n) ℝ` of symmetric matrices with `M t = 1` and
derivative `Dt` at `t` within `[0,T)`, there is a family `Φ` of matrices with `Φ t = 1`,
`Φ sᵀ * M s * Φ s = 1` for `s` close to `t`, and `Φ' t = -(1/2) • Dt`.

The construction is carried out in an arbitrary complete normed `ℝ`-algebra `𝔸` (the `NormedRing`
and `NormedAlgebra ℝ` structures on matrices are those declared in
`Submission.Work.Diff.GE.uhlenbeck_defs`):

* the squaring map `A ↦ A * A` is strictly differentiable at `1` with derivative
  `A ↦ 2 • A` (as a continuous linear *equivalence*, built from `ContinuousLinearEquiv.equivOfInverse'`
  so that its coercion is *definitionally* the derivative produced by `HasStrictFDerivAt.mul'`);

* hence, by the inverse function theorem (`HasStrictFDerivAt.localInverse`), there is a local square
  root `sqrtNear` on a neighbourhood of `1`, whose derivative at `1` is `A ↦ (1/2) • A`, and whose
  basic properties are `sqrtNear 1 = 1`, `sqrtNear y * sqrtNear y = y` eventually near `1`, and
  `sqrtNear (x * x) = x` eventually near `1`;

* for a differentiable family `M` with `M t = 1`, the family `Φ s := sqrtNear (Ring.inverse (M s))`
  satisfies `Φ s * Φ s = Ring.inverse (M s)` eventually along `nhdsWithin t (Set.Ico 0 T)`, and
  `Φ' t = -(1/2) • Dt` by the chain rule (the derivative of `Ring.inverse` at `1` is `-id`);

* symmetry of `Φ s` (a matrix argument): `(Φ s)ᵀ` is another square root of the symmetric matrix
  `Ring.inverse (M s)` close to `1`, and `sqrtNear` is injective near `1` on squares; hence
  `(Φ s)ᵀ = Φ s`, and then `(Φ s)ᵀ * M s * Φ s = Φ s * M s * Φ s = 1` because `Φ s * Φ s * M s = 1`.
-/

namespace Work.Diff.GE

open scoped RightActions Topology Matrix
open Filter

section Abstract

/-- The squaring map on a normed `ℝ`-algebra, and the inverse square root near the identity.

`sqrtEquiv 𝔸` is the continuous linear equivalence "multiplication by `2`", presented through
`ContinuousLinearEquiv.equivOfInverse'` from the two continuous linear maps
`x ↦ x * 1 + 1 * x` and `x ↦ (1/2) • x`.  Its coercion to a continuous linear map is
*definitionally* the derivative of the squaring map at `1` as produced by
`HasStrictFDerivAt.mul'`, which is what makes the inverse function theorem applicable below. -/
noncomputable def sqrtEquiv {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] : 𝔸 ≃L[ℝ] 𝔸 :=
  ContinuousLinearEquiv.equivOfInverse'
    ((1 : 𝔸) •> (1 : 𝔸 →L[ℝ] 𝔸) + (1 : 𝔸 →L[ℝ] 𝔸) <• (1 : 𝔸))
    ((1 / 2 : ℝ) • (1 : 𝔸 →L[ℝ] 𝔸))
    (by ext z; simp; module) (by ext z; simp; module)

/-- The inverse of `sqrtEquiv` is multiplication by `1/2` (definitional). -/
lemma sqrtEquiv_symm_coe {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] :
    (((sqrtEquiv (𝔸 := 𝔸)).symm : 𝔸 ≃L[ℝ] 𝔸) : 𝔸 →L[ℝ] 𝔸)
      = ((1 / 2 : ℝ) • (1 : 𝔸 →L[ℝ] 𝔸)) := rfl

/-- The squaring map is strictly differentiable at `1`, with derivative `sqrtEquiv`. -/
lemma hasStrictFDerivAt_mul_self {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] :
    HasStrictFDerivAt (fun A : 𝔸 => A * A)
      ((sqrtEquiv (𝔸 := 𝔸) : 𝔸 ≃L[ℝ] 𝔸) : 𝔸 →L[ℝ] 𝔸) (1 : 𝔸) := by
  have h1 : HasStrictFDerivAt (fun A : 𝔸 => A) (1 : 𝔸 →L[ℝ] 𝔸) (1 : 𝔸) :=
    hasStrictFDerivAt_id 1
  have hmul := h1.mul' h1
  exact hmul

/-- The local square root near `1`, obtained from the inverse function theorem applied to the
squaring map. -/
noncomputable def sqrtNear {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] :
    𝔸 → 𝔸 :=
  (hasStrictFDerivAt_mul_self (𝔸 := 𝔸)).localInverse (fun A : 𝔸 => A * A)
    (sqrtEquiv (𝔸 := 𝔸)) 1

lemma sqrtNear_one {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] :
    sqrtNear (𝔸 := 𝔸) 1 = 1 := by
  have h := (hasStrictFDerivAt_mul_self (𝔸 := 𝔸)).localInverse_apply_image
    (f := fun A : 𝔸 => A * A) (f' := sqrtEquiv (𝔸 := 𝔸)) (a := 1)
  simpa [sqrtNear] using h

lemma sqrtNear_mul_self {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] :
    ∀ᶠ y in 𝓝 (1 : 𝔸), sqrtNear (𝔸 := 𝔸) y * sqrtNear (𝔸 := 𝔸) y = y := by
  have h := (hasStrictFDerivAt_mul_self (𝔸 := 𝔸)).eventually_right_inverse
    (f := fun A : 𝔸 => A * A) (f' := sqrtEquiv (𝔸 := 𝔸)) (a := 1)
  simpa [sqrtNear] using h

lemma sqrtNear_sq_eq {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] :
    ∀ᶠ x in 𝓝 (1 : 𝔸), sqrtNear (𝔸 := 𝔸) (x * x) = x := by
  have h := (hasStrictFDerivAt_mul_self (𝔸 := 𝔸)).eventually_left_inverse
    (f := fun A : 𝔸 => A * A) (f' := sqrtEquiv (𝔸 := 𝔸)) (a := 1)
  simpa [sqrtNear] using h

/-- The derivative of the local square root at `1` is multiplication by `1/2`. -/
lemma sqrtNear_deriv {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] :
    HasStrictFDerivAt (sqrtNear (𝔸 := 𝔸)) ((1 / 2 : ℝ) • (1 : 𝔸 →L[ℝ] 𝔸)) (1 : 𝔸) := by
  have h := (hasStrictFDerivAt_mul_self (𝔸 := 𝔸)).to_localInverse
    (f := fun A : 𝔸 => A * A) (f' := sqrtEquiv (𝔸 := 𝔸)) (a := 1)
  simpa only [sqrtNear, sqrtEquiv_symm_coe, mul_one] using h

/-- The family `s ↦ sqrtNear (Ring.inverse (M s))` of inverse square roots of a differentiable
family of symmetric elements with `M t = 1`. -/
theorem sqrt_family_abstract {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸]
    (M : ℝ → 𝔸) (Dt : 𝔸) (t T : ℝ) (hMt : M t = 1)
    (hdiff : HasDerivWithinAt M Dt (Set.Ico 0 T) t) :
    (∀ᶠ s in nhdsWithin t (Set.Ico 0 T),
        sqrtNear (𝔸 := 𝔸) (Ring.inverse (M s)) * sqrtNear (𝔸 := 𝔸) (Ring.inverse (M s))
          = Ring.inverse (M s)) ∧
    (∀ᶠ s in nhdsWithin t (Set.Ico 0 T), IsUnit (M s)) ∧
    Tendsto (fun s => sqrtNear (𝔸 := 𝔸) (Ring.inverse (M s)))
      (nhdsWithin t (Set.Ico 0 T)) (𝓝 1) ∧
    HasDerivWithinAt (fun s => sqrtNear (𝔸 := 𝔸) (Ring.inverse (M s)))
      ((-(1 / 2) : ℝ) • Dt) (Set.Ico 0 T) t := by
  have hinvF : HasFDerivAt (fun x : 𝔸 => Ring.inverse x)
      (-(ContinuousLinearMap.mulLeftRight ℝ 𝔸 (1 : 𝔸) (1 : 𝔸))) (M t) := by
    have h := hasStrictFDerivAt_ringInverse (𝕜 := ℝ) (1 : 𝔸ˣ)
    have hf : HasFDerivAt (fun x : 𝔸 => Ring.inverse x)
        (-(ContinuousLinearMap.mulLeftRight ℝ 𝔸 (1 : 𝔸) (1 : 𝔸))) (1 : 𝔸) := by
      simpa using h.hasFDerivAt
    simpa [hMt] using hf
  have hMinv : Tendsto (fun s => Ring.inverse (M s)) (nhdsWithin t (Set.Ico 0 T))
      (𝓝 (1 : 𝔸)) := by
    have h := (hinvF.continuousAt).tendsto.comp hdiff.continuousWithinAt
    rw [hMt, Ring.inverse_one] at h
    simpa [Function.comp_def] using h
  have hΦ_tend : Tendsto (fun s => sqrtNear (𝔸 := 𝔸) (Ring.inverse (M s)))
      (nhdsWithin t (Set.Ico 0 T)) (𝓝 (1 : 𝔸)) := by
    have hcont : ContinuousAt (sqrtNear (𝔸 := 𝔸)) (1 : 𝔸) :=
      (sqrtNear_deriv (𝔸 := 𝔸)).hasFDerivAt.continuousAt
    have h := hcont.tendsto.comp hMinv
    rw [sqrtNear_one] at h
    simpa [Function.comp_def] using h
  have hΦsq : ∀ᶠ s in nhdsWithin t (Set.Ico 0 T),
      sqrtNear (𝔸 := 𝔸) (Ring.inverse (M s)) * sqrtNear (𝔸 := 𝔸) (Ring.inverse (M s))
        = Ring.inverse (M s) := by
    have h := hMinv.eventually (sqrtNear_mul_self (𝔸 := 𝔸))
    simpa [Function.comp_def] using h
  have hunits : ∀ᶠ s in nhdsWithin t (Set.Ico 0 T), IsUnit (M s) := by
    have hball : Metric.ball (1 : 𝔸) 1 ∈ 𝓝 (M t) := by
      rw [hMt]; exact Metric.ball_mem_nhds (1 : 𝔸) zero_lt_one
    refine (Filter.Tendsto.eventually hdiff.continuousWithinAt hball).mono ?_
    intro s hs
    have hs' : ‖(1 : 𝔸) - M s‖ < 1 := by
      simpa [Metric.mem_ball, dist_eq_norm, norm_sub_rev] using hs
    have h2 := isUnit_one_sub_of_norm_lt_one hs'
    simpa [sub_sub_cancel] using h2
  have hderiv : HasDerivWithinAt (fun s => sqrtNear (𝔸 := 𝔸) (Ring.inverse (M s)))
      ((-(1 / 2) : ℝ) • Dt) (Set.Ico 0 T) t := by
    have h1 : HasDerivWithinAt (fun s => Ring.inverse (M s)) (-Dt) (Set.Ico 0 T) t := by
      have h := hinvF.comp_hasDerivWithinAt t hdiff
      have hd : ((-(ContinuousLinearMap.mulLeftRight ℝ 𝔸 (1 : 𝔸) (1 : 𝔸))) Dt) = -Dt := by
        simp [ContinuousLinearMap.mulLeftRight_apply]
      rw [hd] at h
      simpa [Function.comp_def] using h
    have hsq : HasFDerivAt (sqrtNear (𝔸 := 𝔸)) ((1 / 2 : ℝ) • (1 : 𝔸 →L[ℝ] 𝔸))
        (Ring.inverse (M t)) := by
      have h := (sqrtNear_deriv (𝔸 := 𝔸)).hasFDerivAt
      simpa [hMt, Ring.inverse_one] using h
    have h := hsq.comp_hasDerivWithinAt t h1
    have hval : ((1 / 2 : ℝ) • (1 : 𝔸 →L[ℝ] 𝔸)) (-Dt) = (-(1 / 2) : ℝ) • Dt := by
      simp [smul_neg]
    rw [hval] at h
    simpa [Function.comp_def] using h
  exact ⟨hΦsq, hunits, hΦ_tend, hderiv⟩

end Abstract

theorem matrix_sqrt_family_kit (n : ℕ) (M : ℝ → Matrix (Fin n) (Fin n) ℝ)
    (Dt : Matrix (Fin n) (Fin n) ℝ) (t T : ℝ)
    (hMt : M t = 1) (hsym : ∀ s, (M s).transpose = M s)
    (hdiff : HasDerivWithinAt M Dt (Set.Ico 0 T) t) :
    ∃ Φ : ℝ → Matrix (Fin n) (Fin n) ℝ,
      Φ t = 1 ∧
      (∀ᶠ s in nhdsWithin t (Set.Ico 0 T), (Φ s).transpose * M s * Φ s = 1) ∧
      HasDerivWithinAt Φ ((-(1/2) : ℝ) • Dt) (Set.Ico 0 T) t := by
  classical
  obtain ⟨hΦsq, hunits, hΦ_tend, hΦderiv⟩ :=
    sqrt_family_abstract (𝔸 := Matrix (Fin n) (Fin n) ℝ) M Dt t T hMt hdiff
  have hg : Continuous (fun A : Matrix (Fin n) (Fin n) ℝ => A.transpose) :=
    continuous_id.matrix_transpose
  have hPtr : Tendsto
      (fun s => (sqrtNear (𝔸 := Matrix (Fin n) (Fin n) ℝ) (Ring.inverse (M s))).transpose)
      (nhdsWithin t (Set.Ico 0 T)) (𝓝 1) := by
    have h := hg.continuousAt.tendsto.comp hΦ_tend
    rw [Matrix.transpose_one] at h
    simpa [Function.comp_def] using h
  -- the inverse of a symmetric unit is symmetric
  have htrans : ∀ᶠ s in nhdsWithin t (Set.Ico 0 T),
      (Ring.inverse (M s)).transpose = Ring.inverse (M s) := by
    refine hunits.mono ?_
    intro s hu
    obtain ⟨u, hsu⟩ : ∃ u : (Matrix (Fin n) (Fin n) ℝ)ˣ, Units.val u = M s :=
      ⟨hu.unit, hu.unit_spec⟩
    rw [← hsu]
    let v : (Matrix (Fin n) (Fin n) ℝ)ˣ :=
      Units.mk (Units.val u).transpose (Units.val (u⁻¹)).transpose
        (by rw [← Matrix.transpose_mul, Units.inv_mul, Matrix.transpose_one])
        (by rw [← Matrix.transpose_mul, Units.mul_inv, Matrix.transpose_one])
    have hv : Units.val v = Units.val u := by
      show (Units.val u).transpose = Units.val u
      rw [hsu, hsym s]
    have hvv : v = u := Units.ext hv
    have hv' : Units.val v⁻¹ = (Units.val (u⁻¹)).transpose := by
      simp only [v, Units.inv_mk]
    calc (Ring.inverse (Units.val u)).transpose
        = (Units.val (u⁻¹)).transpose := by rw [Ring.inverse_unit]
      _ = Units.val v⁻¹ := by rw [hv']
      _ = Units.val (u⁻¹) := by rw [hvv]
      _ = Ring.inverse (Units.val u) := by rw [Ring.inverse_unit]
  -- the square root of a symmetric element close to 1 is symmetric
  have hΦsym : ∀ᶠ s in nhdsWithin t (Set.Ico 0 T),
      (sqrtNear (𝔸 := Matrix (Fin n) (Fin n) ℝ) (Ring.inverse (M s))).transpose
        = sqrtNear (𝔸 := Matrix (Fin n) (Fin n) ℝ) (Ring.inverse (M s)) := by
    have hsqt := hPtr.eventually (sqrtNear_sq_eq (𝔸 := Matrix (Fin n) (Fin n) ℝ))
    refine (hΦsq.and (htrans.and hsqt)).mono ?_
    intro s ⟨h1, h2, h3⟩
    have h4 : (sqrtNear (𝔸 := Matrix (Fin n) (Fin n) ℝ) (Ring.inverse (M s))).transpose
        * (sqrtNear (𝔸 := Matrix (Fin n) (Fin n) ℝ) (Ring.inverse (M s))).transpose
        = Ring.inverse (M s) := by
      rw [← Matrix.transpose_mul, h1, h2]
    rw [← h3, h4]
  refine ⟨fun s => sqrtNear (𝔸 := Matrix (Fin n) (Fin n) ℝ) (Ring.inverse (M s)), ?_, ?_, ?_⟩
  · show sqrtNear (𝔸 := Matrix (Fin n) (Fin n) ℝ) (Ring.inverse (M t)) = 1
    rw [hMt, Ring.inverse_one, sqrtNear_one]
  · refine (hΦsym.and (hΦsq.and hunits)).mono ?_
    intro s hfac
    obtain ⟨h1, h2, h3⟩ := hfac
    dsimp only
    set P : Matrix (Fin n) (Fin n) ℝ :=
      sqrtNear (𝔸 := Matrix (Fin n) (Fin n) ℝ) (Ring.inverse (M s)) with hP
    obtain ⟨u, hsu⟩ : ∃ u : (Matrix (Fin n) (Fin n) ℝ)ˣ, Units.val u = M s :=
      ⟨h3.unit, h3.unit_spec⟩
    have h1' : P * P = Units.val (u⁻¹) := by
      rw [h2, ← hsu, Ring.inverse_unit]
    have hPPM : P * P * M s = 1 := by
      rw [h1', ← hsu]
      exact Units.inv_mul u
    have hPPM' : P * (P * M s) = 1 := by
      rw [← mul_assoc]; exact hPPM
    have hMPP : M s * P * P = 1 := by
      have h := congrArg Matrix.transpose hPPM
      simpa [Matrix.transpose_mul, h1, hsym s, ← mul_assoc] using h
    have hcomm : M s * P = P * M s := by
      have key : (M s * P) * (P * (P * M s)) = M s * P := by rw [hPPM', mul_one]
      have key2 : (M s * P) * (P * (P * M s)) = ((M s * P) * P) * (P * M s) :=
        (mul_assoc _ _ _).symm
      rw [key2, hMPP, one_mul] at key
      exact key.symm
    rw [h1, hcomm.symm, hMPP]
  · exact hΦderiv

end Work.Diff.GE
