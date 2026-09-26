import Mathlib
import Submission.Work.Drive.Mono.offK_defs

namespace Work.Drive.Mono

/-- **The tangent equation of the surface at a zero of `surfPoly ∘ ψ⁻¹ ∘ γ` with vanishing derivative.**

`surfPoly y = (‖y‖²+3)² - 16 (y₀²+y₁²)` vanishes exactly on the standard torus of revolution, so
`t ↦ surfPoly (ψ⁻¹ (γ t))` vanishes exactly where the smooth curve `γ` meets the surface
`F = ψ(standard torus)`.  Its derivative at such a point is a nonzero multiple of `⟪normal_F, γ'⟫`
(the gradient of `surfPoly` is normal to the level set): hence, if `γ t₀` is on the surface and that
derivative *vanishes*, then `γ'(t₀)` is **tangent** to the surface, i.e. is the image under the
differential of the parametrisation `param ψ = ψ ∘ torusMap` of some parameter direction.

This is the local form of `Work.Drive.Mono.exists_tangentDir_eq_deriv_of_mem_carrier`
(`Submission/Work/Drive/Mono/knot_deriv_of_sweepHeight_crit.lean`), whose hypothesis is the stronger
"`γ` lies on the surface in a neighbourhood": the proof is the same computation, with the vanishing
of the composite replaced by the vanishing of its derivative at `t₀`. -/
theorem tangent_of_surfPoly_deriv_zero
    (ψ : Submission.Diffeo) (γ : ℝ → LeanEval.KnotTheory.PardonDistortion.R3)
    (hγ : ContDiff ℝ (⊤ : ℕ∞) γ)
    {t₀ : ℝ} {p₀ : ℝ × ℝ} (hp : γ t₀ = Work.Smooth.Morse.param ψ p₀)
    (hderiv : deriv (fun t : ℝ => Work.Drive.Mono.surfPoly (ψ.invFun (γ t))) t₀ = 0) :
    ∃ r : ℝ × ℝ, fderiv ℝ (Work.Smooth.Morse.param ψ) p₀ r = deriv γ t₀ := by
  classical
  have hx₀ : γ t₀ = ψ (Work.Core.torusMap p₀.1 p₀.2) := by rw [hp]; rfl
  have hinv : ψ.invFun (γ t₀) = Work.Core.torusMap p₀.1 p₀.2 := by rw [hx₀, ψ.left_inv]
  have hγd : HasDerivAt γ (deriv γ t₀) t₀ :=
    ((hγ.differentiable (by simp)).differentiableAt).hasDerivAt
  have hψinv : HasFDerivAt ψ.invFun (fderiv ℝ ψ.invFun (γ t₀)) (γ t₀) :=
    (ψ.smooth_invFun.hasStrictFDerivAt (by simp)).hasFDerivAt
  have hcomp1 : HasDerivAt (fun t => ψ.invFun (γ t))
      ((fderiv ℝ ψ.invFun (γ t₀)) (deriv γ t₀)) t₀ := hψinv.comp_hasDerivAt t₀ hγd
  have hL : HasFDerivAt surfPoly (fderiv ℝ surfPoly (ψ.invFun (γ t₀))) (ψ.invFun (γ t₀)) :=
    (surfPoly_contDiff.hasStrictFDerivAt (by simp)).hasFDerivAt
  have hcomp2 : HasDerivAt (fun t => surfPoly (ψ.invFun (γ t)))
      ((fderiv ℝ surfPoly (ψ.invFun (γ t₀)))
        ((fderiv ℝ ψ.invFun (γ t₀)) (deriv γ t₀))) t₀ :=
    hL.comp_hasDerivAt (l := surfPoly) t₀ hcomp1
  have hval : (fderiv ℝ surfPoly (ψ.invFun (γ t₀)))
      ((fderiv ℝ ψ.invFun (γ t₀)) (deriv γ t₀)) = 0 := by
    rw [← hcomp2.deriv, hderiv]
  rw [hinv] at hval
  set w : LeanEval.KnotTheory.PardonDistortion.R3 := (fderiv ℝ ψ.invFun (γ t₀)) (deriv γ t₀) with hw
  have hker : fderiv ℝ surfPoly (Work.Core.torusMap p₀.1 p₀.2) w = 0 := hval
  have hformula : fderiv ℝ surfPoly (Work.Core.torusMap p₀.1 p₀.2) w =
      16 * (2 + Real.cos p₀.2) *
        (Real.cos p₀.2 * (w 0 * Real.cos p₀.1 + w 1 * Real.sin p₀.1)
          + Real.sin p₀.2 * w 2) := by
    change fderiv ℝ (fun y : LeanEval.KnotTheory.PardonDistortion.R3 => (y 0 ^ 2 + y 1 ^ 2 + y 2 ^ 2 + 3) ^ 2
        - 16 * (y 0 ^ 2 + y 1 ^ 2)) (Work.Core.torusMap p₀.1 p₀.2) w = _
    rw [Work.Smooth.BoxGeneric.Vertex.fderiv_torusLevel]
    have hD : (Work.Core.torusMap p₀.1 p₀.2) 0 ^ 2 + (Work.Core.torusMap p₀.1 p₀.2) 1 ^ 2
        + (Work.Core.torusMap p₀.1 p₀.2) 2 ^ 2 + 3 = 4 * (2 + Real.cos p₀.2) := by
      rw [Work.Core.torusMap_apply_zero, Work.Core.torusMap_apply_one, Work.Core.torusMap_apply_two]
      nlinarith [Real.sin_sq_add_cos_sq p₀.1, Real.sin_sq_add_cos_sq p₀.2]
    rw [hD, Work.Core.torusMap_apply_zero, Work.Core.torusMap_apply_one,
      Work.Core.torusMap_apply_two]
    ring
  have hbracket : Real.cos p₀.2 * (w 0 * Real.cos p₀.1 + w 1 * Real.sin p₀.1)
      + Real.sin p₀.2 * w 2 = 0 := by
    have hpos : (0 : ℝ) < 16 * (2 + Real.cos p₀.2) := by
      have h := Real.neg_one_le_cos p₀.2; linarith
    have h0 : 16 * (2 + Real.cos p₀.2) *
        (Real.cos p₀.2 * (w 0 * Real.cos p₀.1 + w 1 * Real.sin p₀.1)
          + Real.sin p₀.2 * w 2) = 0 := by
      rw [← hformula, hker]
    exact (mul_eq_zero.mp h0).resolve_left (ne_of_gt hpos)
  have hz : (2 + Real.cos p₀.2 - 2) ^ 2 + Real.sin p₀.2 ^ 2 = 1 := by
    have h := Real.sin_sq_add_cos_sq p₀.2
    nlinarith [h]
  have hbracket' : (2 + Real.cos p₀.2 - 2) * (w 0 * Real.cos p₀.1 + w 1 * Real.sin p₀.1)
      + Real.sin p₀.2 * w 2 = 0 := by
    rw [show (2 : ℝ) + Real.cos p₀.2 - 2 = Real.cos p₀.2 by ring]
    exact hbracket
  have hρpos : (0 : ℝ) < 2 + Real.cos p₀.2 := by
    have h := Real.neg_one_le_cos p₀.2; linarith
  obtain ⟨r₁, r₂, hr1, hr2, hr3⟩ := Work.Smooth.BoxGeneric.Vertex.torus_combination_of_tangential
    (ρ := 2 + Real.cos p₀.2) (z := Real.sin p₀.2) (u := p₀.1)
    (w0 := w 0) (w1 := w 1) (w2 := w 2) hρpos hz hbracket'
  have htd : Work.Smooth.Morse.torusDeriv p₀ (r₁, r₂) = w := by
    rw [Work.Smooth.Morse.torusDeriv_apply, WithLp.ext_iff]
    funext i
    fin_cases i
    · simp only [WithLp.ofLp_add, WithLp.ofLp_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
        Work.Smooth.Morse.dtheta, Work.Smooth.Morse.dphi, ↓reduceIte, neg_mul]
      exact hr1
    · simp only [WithLp.ofLp_add, WithLp.ofLp_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
        Work.Smooth.Morse.dtheta, Work.Smooth.Morse.dphi, ↓reduceIte, neg_mul]
      exact hr2
    · simp only [WithLp.ofLp_add, WithLp.ofLp_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
        Work.Smooth.Morse.dtheta, Work.Smooth.Morse.dphi, ↓reduceIte, reduceCtorEq, neg_mul]
      split_ifs with h
      · exact absurd h (by decide)
      · have h3' : r₂ * Real.cos p₀.2 = w 2 := by
          have h3 := hr3
          rw [show (2 : ℝ) + Real.cos p₀.2 - 2 = Real.cos p₀.2 by ring] at h3
          exact h3
        rw [h3']
        simp
  have hright : (fderiv ℝ (ψ : LeanEval.KnotTheory.PardonDistortion.R3 → LeanEval.KnotTheory.PardonDistortion.R3) (Work.Core.torusMap p₀.1 p₀.2)).comp
      (fderiv ℝ ψ.invFun (γ t₀)) = ContinuousLinearMap.id ℝ LeanEval.KnotTheory.PardonDistortion.R3 := by
    have hmain : HasFDerivAt (fun y : LeanEval.KnotTheory.PardonDistortion.R3 => ψ (ψ.invFun y))
        ((fderiv ℝ (ψ : LeanEval.KnotTheory.PardonDistortion.R3 → LeanEval.KnotTheory.PardonDistortion.R3) (Work.Core.torusMap p₀.1 p₀.2)).comp
          (fderiv ℝ ψ.invFun (γ t₀))) (γ t₀) := by
      have hψ2 : HasFDerivAt (fun y : LeanEval.KnotTheory.PardonDistortion.R3 => ψ y)
          (fderiv ℝ (ψ : LeanEval.KnotTheory.PardonDistortion.R3 → LeanEval.KnotTheory.PardonDistortion.R3) (ψ.invFun (γ t₀))) (ψ.invFun (γ t₀)) :=
        (ψ.smooth_toFun.hasStrictFDerivAt (by simp)).hasFDerivAt
      have hcomp := hψ2.comp (γ t₀) hψinv
      rw [hinv] at hcomp
      exact hcomp
    have hid : (fun y : LeanEval.KnotTheory.PardonDistortion.R3 => ψ (ψ.invFun y)) = id := funext fun y => ψ.right_inv y
    rw [hid] at hmain
    exact hmain.unique (hasFDerivAt_id (γ t₀))
  have hw_eq : fderiv ℝ (ψ : LeanEval.KnotTheory.PardonDistortion.R3 → LeanEval.KnotTheory.PardonDistortion.R3) (Work.Core.torusMap p₀.1 p₀.2) w = deriv γ t₀ := by
    have h := congrArg (fun (L : LeanEval.KnotTheory.PardonDistortion.R3 →L[ℝ] LeanEval.KnotTheory.PardonDistortion.R3) => L (deriv γ t₀)) hright
    simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply, ← hw] using h
  refine ⟨(r₁, r₂), ?_⟩
  rw [Work.Smooth.Morse.fderiv_param ψ p₀, ContinuousLinearMap.comp_apply, htd]
  exact hw_eq

end Work.Drive.Mono
