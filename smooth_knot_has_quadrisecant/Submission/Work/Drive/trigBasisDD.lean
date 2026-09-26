import Mathlib
import Submission.Work.Drive.knotPerturbDefs
import Submission.Work.Drive.tangencyBadSet

/-!
# The second derivative of the scalar trigonometric basis

`knotPerturbDefs` supplies the degree-`≤ 4` trigonometric basis
`trigBasis : Fin 9 → ℝ → ℝ` (`1, cos t, sin t, cos 2t, sin 2t, cos 3t, sin 3t, cos 4t, sin 4t`)
and its derivative `trigBasisD`.  This file adds the **second** derivative `trigBasisDD`
together with the corresponding acceleration of the correction,
`perturbAccCorr c = deriv (perturbVelCorr c)`.

These are the coefficient directions that the tangent-chord rank computation needs: the
second derivative in the coefficient variable of `t ↦ pertVelV r c t` is
`Σ j, (trigBasisDD j t) • c j`.
-/

namespace Work.Drive

open LeanEval.KnotTheory.Quadrisecant

noncomputable section

/-- The second derivative of the scalar basis of the perturbation space. -/
noncomputable def trigBasisDD : Fin 9 → ℝ → ℝ
  | 0 => fun _ => 0
  | 1 => fun t => -Real.cos t
  | 2 => fun t => -Real.sin t
  | 3 => fun t => -4 * Real.cos (2 * t)
  | 4 => fun t => -4 * Real.sin (2 * t)
  | 5 => fun t => -9 * Real.cos (3 * t)
  | 6 => fun t => -9 * Real.sin (3 * t)
  | 7 => fun t => -16 * Real.cos (4 * t)
  | _ => fun t => -16 * Real.sin (4 * t)

private lemma deriv_mul_sin (a k : ℝ) :
    deriv (fun t : ℝ => a * Real.sin (k * t)) = fun t => a * k * Real.cos (k * t) := by
  funext t
  have h2 : HasDerivAt (fun t : ℝ => k * t) k t := by simpa using (hasDerivAt_id t).const_mul k
  have h1 : HasDerivAt (fun t : ℝ => Real.sin (k * t)) (Real.cos (k * t) * k) t :=
    (Real.hasDerivAt_sin (k * t)).comp t h2
  have h : HasDerivAt (fun t : ℝ => a * Real.sin (k * t)) (a * (Real.cos (k * t) * k)) t :=
    h1.const_mul a
  rw [h.deriv]; ring

private lemma deriv_mul_cos (a k : ℝ) :
    deriv (fun t : ℝ => a * Real.cos (k * t)) = fun t => -a * k * Real.sin (k * t) := by
  funext t
  have h2 : HasDerivAt (fun t : ℝ => k * t) k t := by simpa using (hasDerivAt_id t).const_mul k
  have h1 : HasDerivAt (fun t : ℝ => Real.cos (k * t)) (-Real.sin (k * t) * k) t :=
    (Real.hasDerivAt_cos (k * t)).comp t h2
  have h : HasDerivAt (fun t : ℝ => a * Real.cos (k * t)) (a * (-Real.sin (k * t) * k)) t :=
    h1.const_mul a
  rw [h.deriv]; ring

/-- The second derivative of the basis is `trigBasisDD`. -/
theorem deriv_trigBasisD (j : Fin 9) : deriv (trigBasisD j) = trigBasisDD j := by
  fin_cases j
  · show deriv (fun _ : ℝ => (0:ℝ)) = fun _ => (0:ℝ)
    funext t; exact deriv_const t 0
  · show deriv (fun t : ℝ => -Real.sin t) = fun t => -Real.cos t
    funext t
    have h : HasDerivAt (fun t : ℝ => -Real.sin t) (-(Real.cos t)) t :=
      (Real.hasDerivAt_sin t).neg
    rw [h.deriv]
  · show deriv Real.cos = fun t => -Real.sin t
    funext t; simpa using Real.deriv_cos
  · show deriv (fun t : ℝ => -2 * Real.sin (2 * t)) = fun t => -4 * Real.cos (2 * t)
    rw [deriv_mul_sin (-2) 2]; funext t; ring
  · show deriv (fun t : ℝ => 2 * Real.cos (2 * t)) = fun t => -4 * Real.sin (2 * t)
    rw [deriv_mul_cos 2 2]; funext t; ring
  · show deriv (fun t : ℝ => -3 * Real.sin (3 * t)) = fun t => -9 * Real.cos (3 * t)
    rw [deriv_mul_sin (-3) 3]; funext t; ring
  · show deriv (fun t : ℝ => 3 * Real.cos (3 * t)) = fun t => -9 * Real.sin (3 * t)
    rw [deriv_mul_cos 3 3]; funext t; ring
  · show deriv (fun t : ℝ => -4 * Real.sin (4 * t)) = fun t => -16 * Real.cos (4 * t)
    rw [deriv_mul_sin (-4) 4]; funext t; ring
  · show deriv (fun t : ℝ => 4 * Real.cos (4 * t)) = fun t => -16 * Real.sin (4 * t)
    rw [deriv_mul_cos 4 4]; funext t; ring

theorem contDiff_trigBasisDD (j : Fin 9) : ContDiff ℝ ⊤ (trigBasisDD j) := by
  rw [← deriv_trigBasisD j]
  exact ContDiff.deriv' (n := ⊤) (by simpa using contDiff_trigBasisD j)

theorem periodic_trigBasisDD (j : Fin 9) : Function.Periodic (trigBasisDD j) (2 * Real.pi) := by
  rw [← deriv_trigBasisD j]
  intro t
  have hx : deriv (fun y : ℝ => trigBasisD j (y + 2 * Real.pi)) t = deriv (trigBasisD j) t := by
    rw [show (fun y : ℝ => trigBasisD j (y + 2 * Real.pi)) = trigBasisD j from funext (fun y => periodic_trigBasisD j y)]
  rwa [deriv_comp_add_const (trigBasisD j) (2 * Real.pi) t] at hx

lemma trigBasisDD_red (j : Fin 9) {t : ℝ} (ht : t ∈ Set.Icc 0 (2 * Real.pi)) :
    trigBasisDD j (red t) = trigBasisDD j t := by
  by_cases h : t = 2 * Real.pi
  · rw [red, if_pos h, h]
    simpa using ((periodic_trigBasisDD j) 0).symm
  · rw [red, if_neg h]

/-- The acceleration of the correction: the second derivative of `perturbCorr c`. -/
noncomputable def perturbAccCorr (c : Fin 9 → Space) : ℝ → Space :=
  fun t => ∑ j, (trigBasisDD j t) • c j

theorem deriv_perturbVelCorr (c : Fin 9 → Space) :
    deriv (perturbVelCorr c) = perturbAccCorr c := by
  funext t
  change deriv (∑ j : Fin 9, fun s : ℝ => (trigBasisD j s) • c j) t = ∑ j, (trigBasisDD j t) • c j
  rw [deriv_sum]
  · refine Finset.sum_congr rfl fun j _ => ?_
    rw [deriv_smul_const]
    · rw [deriv_trigBasisD]
    · exact ((contDiff_trigBasisD j).differentiable (by simp)).differentiableAt
  · intro j _
    exact ((contDiff_trigBasisD j).differentiable (by simp)).differentiableAt.smul_const (c j)

theorem contDiff_perturbVelCorr (c : Fin 9 → Space) : ContDiff ℝ ⊤ (perturbVelCorr c) := by
  apply ContDiff.sum
  intro j _
  exact (contDiff_trigBasisD j).smul_const (c j)

theorem contDiff_perturbAccCorr (c : Fin 9 → Space) : ContDiff ℝ ⊤ (perturbAccCorr c) := by
  apply ContDiff.sum
  intro j _
  exact (contDiff_trigBasisDD j).smul_const (c j)

theorem periodic_perturbAccCorr (c : Fin 9 → Space) :
    Function.Periodic (perturbAccCorr c) (2 * Real.pi) := by
  intro t
  simp only [perturbAccCorr]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [periodic_trigBasisDD j t]

/-- The acceleration of the perturbed curve: the derivative of its velocity is the base
acceleration plus the acceleration of the correction. -/
theorem deriv_pertVelV (r : ℝ → Space) (hr : ContDiff ℝ ⊤ r) (c : Coeff) :
    deriv (pertVelV r c) = deriv (deriv r) + perturbAccCorr (eCoeff c) := by
  have h1 : pertVelV r c = velocity r + perturbVelCorr (eCoeff c) := by
    funext t; simp [pertVelV, perturbVel]
  rw [h1]
  have hd1 : Differentiable ℝ (velocity r) := (hr.deriv' (n := ⊤)).differentiable (by simp)
  have hd2 : Differentiable ℝ (perturbVelCorr (eCoeff c)) :=
    (contDiff_perturbVelCorr _).differentiable (by simp)
  have h2 : deriv (velocity r + perturbVelCorr (eCoeff c))
      = deriv (velocity r) + deriv (perturbVelCorr (eCoeff c)) := by
    funext x
    exact deriv_add hd1.differentiableAt hd2.differentiableAt
  rw [h2, deriv_perturbVelCorr]
  rfl

/-- The `c`-slice of the acceleration of the perturbed velocity is differentiable, with
derivative `linSum (fun j => trigBasisDD j t)`. -/
theorem hasFDerivAt_deriv_pertVelV_slice (r : ℝ → Space) (hr : ContDiff ℝ ⊤ r) (t : ℝ)
    (c₀ : Coeff) :
    HasFDerivAt (fun c : Coeff => deriv (pertVelV r c) t)
      (linSum (fun j => trigBasisDD j t)) c₀ := by
  have h := (hasFDerivAt_const ((deriv (deriv r)) t) c₀).add
    ((linSum (fun j => trigBasisDD j t)).hasFDerivAt (x := c₀))
  rw [zero_add] at h
  refine h.congr_of_eventuallyEq ?_
  exact Filter.Eventually.of_forall fun c => by
    simp [deriv_pertVelV r hr c, perturbAccCorr, linSum_apply, coeffProj_apply]

end

end Work.Drive
