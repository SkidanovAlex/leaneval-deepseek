import Mathlib
import Submission.Work.TorusCover.Basic
import Submission.Work.Core.torusMap_eq_iff

/-!
# The standard torus of revolution as a `TorusParam`

The parametrised torus `TorusParam` bundles periodicity, injectivity modulo `2π`
and a uniform positive lower bound `c * ‖u‖ ≤ ‖fderiv ℝ (psiMap psi) p u‖` for
the derivative of the parametrisation.

Here we exhibit the standard torus of revolution (`Work.Core.torusMap`) as a
`TorusParam` with constant `c = 1`.  The lower bound is sharp: along the
longitude direction the derivative has norm exactly `2 + cos φ ≥ 1`, and along
the meridian direction exactly `1`.

The parametrisation is the composition of the finite-dimensional `L²`-rearrangement
`WithLp.toLp 2` with the `ℝ³`-valued component map
`p ↦ (fun i => …)`; the derivative is the `L²`-rearrangement of the
componentwise derivative.  Its squared norm works out to
`(2 + cos y)² u₁² + u₂²`, whence the bound.
-/

open LeanEval.KnotTheory.PardonDistortion
open scoped ENNReal

namespace Work.TorusCover

/-- `psiMap torusMap` is `C¹`.  The parametrisation is the `L²`-rearrangement of
a smooth componentwise function. -/
lemma contDiff_psiMap_torusMap :
    ContDiff ℝ (1 : ℕ∞) (psiMap Work.Core.torusMap) := by
  have h1 : ContDiff ℝ (1 : ℕ∞) (fun x : Fin 3 → ℝ => WithLp.toLp 2 x) :=
    PiLp.contDiff_toLp (𝕜 := ℝ) (n := (1 : ℕ∞)) (p := 2)
  have h2 : ContDiff ℝ (1 : ℕ∞) (fun p : ℝ × ℝ => fun i : Fin 3 =>
      if i.val = 0 then (2 + Real.cos p.2) * Real.cos p.1
      else if i.val = 1 then (2 + Real.cos p.2) * Real.sin p.1 else Real.sin p.2) := by
    rw [contDiff_pi]
    intro i
    fin_cases i <;> simp <;> fun_prop
  exact h1.comp h2

/-- The components of the derivative of `psiMap torusMap` are the derivatives of
the components. -/
lemma fderiv_psiMap_torusMap_ofLp (x y u1 u2 : ℝ) (i : Fin 3) :
    ((fderiv ℝ (psiMap Work.Core.torusMap) (x, y)) (u1, u2)).ofLp i
      = (fderiv ℝ (fun q : ℝ × ℝ => (psiMap Work.Core.torusMap) q i) (x, y)) (u1, u2) := by
  have hf : HasFDerivAt (psiMap Work.Core.torusMap)
      (fderiv ℝ (psiMap Work.Core.torusMap) (x, y)) (x, y) :=
    (contDiff_psiMap_torusMap.differentiable (by norm_num)).differentiableAt.hasFDerivAt
  have hfi : HasFDerivWithinAt (fun q : ℝ × ℝ => ((psiMap Work.Core.torusMap) q).ofLp i)
      ((PiLp.proj 2 (fun _ : Fin 3 => ℝ) i) ∘L
        (fderiv ℝ (psiMap Work.Core.torusMap) (x, y))) Set.univ (x, y) :=
    (hasFDerivWithinAt_piLp (p := 2) (f := psiMap Work.Core.torusMap)
      (f' := fderiv ℝ (psiMap Work.Core.torusMap) (x, y)) (t := Set.univ) (y := (x, y))).mp
      hf.hasFDerivWithinAt i
  have hfiA : HasFDerivAt (fun q : ℝ × ℝ => ((psiMap Work.Core.torusMap) q).ofLp i)
      ((PiLp.proj 2 (fun _ : Fin 3 => ℝ) i) ∘L
        (fderiv ℝ (psiMap Work.Core.torusMap) (x, y))) (x, y) :=
    hfi.hasFDerivAt (by simp)
  have h := hfiA.fderiv
  have key : (fun q : ℝ × ℝ => ((psiMap Work.Core.torusMap) q).ofLp i)
      = (fun q : ℝ × ℝ => (psiMap Work.Core.torusMap) q i) := by
    funext q; simp
  rw [key] at h
  have h2 := congrArg (fun (L : (ℝ × ℝ) →L[ℝ] ℝ) => L (u1, u2)) h
  simp only [ContinuousLinearMap.comp_apply, PiLp.proj_apply] at h2
  rw [h2]

/-- The squared norm of the derivative of the standard torus parametrisation. -/
lemma norm_sq_fderiv_psiMap_torusMap (x y u1 u2 : ℝ) :
    ‖(fderiv ℝ (psiMap Work.Core.torusMap) (x, y)) (u1, u2)‖ ^ 2
      = (2 + Real.cos y) ^ 2 * u1 ^ 2 + u2 ^ 2 := by
  have e0 : (fun q : ℝ × ℝ => (psiMap Work.Core.torusMap) q (0 : Fin 3))
      = (fun q : ℝ × ℝ => (2 + Real.cos q.2) * Real.cos q.1) := by
    funext q; simp [psiMap, Work.Core.torusMap_apply_zero]
  have e1 : (fun q : ℝ × ℝ => (psiMap Work.Core.torusMap) q (1 : Fin 3))
      = (fun q : ℝ × ℝ => (2 + Real.cos q.2) * Real.sin q.1) := by
    funext q; simp [psiMap, Work.Core.torusMap_apply_one]
  have e2 : (fun q : ℝ × ℝ => (psiMap Work.Core.torusMap) q (2 : Fin 3))
      = (fun q : ℝ × ℝ => Real.sin q.2) := by
    funext q; simp [psiMap, Work.Core.torusMap_apply_two]
  have d0 : (fderiv ℝ (fun q : ℝ × ℝ => (2 + Real.cos q.2) * Real.cos q.1) (x, y)) (u1, u2)
      = -(2 + Real.cos y) * Real.sin x * u1 - Real.sin y * Real.cos x * u2 := by
    have hc : DifferentiableAt ℝ (fun p : ℝ × ℝ => 2 + Real.cos p.2) (x, y) := by fun_prop
    have hd : DifferentiableAt ℝ (fun p : ℝ × ℝ => Real.cos p.1) (x, y) := by fun_prop
    rw [fderiv_fun_mul hc hd]; simp [fderiv_fst, fderiv_snd]; ring
  have d1 : (fderiv ℝ (fun q : ℝ × ℝ => (2 + Real.cos q.2) * Real.sin q.1) (x, y)) (u1, u2)
      = (2 + Real.cos y) * Real.cos x * u1 - Real.sin y * Real.sin x * u2 := by
    have hc : DifferentiableAt ℝ (fun p : ℝ × ℝ => 2 + Real.cos p.2) (x, y) := by fun_prop
    have hd : DifferentiableAt ℝ (fun p : ℝ × ℝ => Real.sin p.1) (x, y) := by fun_prop
    rw [fderiv_fun_mul hc hd]; simp [fderiv_fst, fderiv_snd]; ring
  have d2 : (fderiv ℝ (fun q : ℝ × ℝ => Real.sin q.2) (x, y)) (u1, u2) = Real.cos y * u2 := by
    simp [fderiv_snd]
  rw [PiLp.norm_sq_eq_of_L2]
  simp only [fderiv_psiMap_torusMap_ofLp]
  rw [Fin.sum_univ_three, e0, e1, e2]
  simp only [Real.norm_eq_abs, sq_abs]
  rw [d0, d1, d2]
  linear_combination
    (((2 + Real.cos y) ^ 2 * u1 ^ 2 + Real.sin y ^ 2 * u2 ^ 2)) * (Real.sin_sq_add_cos_sq x)
    + (u2 ^ 2) * (Real.sin_sq_add_cos_sq y)

/-- The uniform derivative lower bound for the standard torus parametrisation, with
the sharp constant `c = 1`. -/
lemma deriv_lower_torusMap :
    ∀ x y (u : ℝ × ℝ),
      1 * ‖u‖ ≤ ‖fderiv ℝ (psiMap Work.Core.torusMap) (x, y) u‖ := by
  intro x y u
  obtain ⟨u1, u2⟩ := u
  rw [one_mul]
  set D := (fderiv ℝ (psiMap Work.Core.torusMap) (x, y)) (u1, u2)
  have hDsq : ‖D‖ ^ 2 = (2 + Real.cos y) ^ 2 * u1 ^ 2 + u2 ^ 2 :=
    norm_sq_fderiv_psiMap_torusMap x y u1 u2
  have hcos : (1 : ℝ) ≤ (2 + Real.cos y) ^ 2 := by nlinarith [Real.neg_one_le_cos y]
  have h1 : |u1| ≤ ‖D‖ := by
    have hu : u1 ^ 2 ≤ ‖D‖ ^ 2 := by rw [hDsq]; nlinarith
    have := sq_le_sq.mp hu
    simpa [abs_of_nonneg (norm_nonneg D)] using this
  have h2 : |u2| ≤ ‖D‖ := by
    have hu : u2 ^ 2 ≤ ‖D‖ ^ 2 := by
      rw [hDsq]; nlinarith [sq_nonneg ((2 + Real.cos y) * u1)]
    have := sq_le_sq.mp hu
    simpa [abs_of_nonneg (norm_nonneg D)] using this
  simpa [Prod.norm_def, Real.norm_eq_abs] using max_le h1 h2

/-- The standard torus of revolution as a bundled `TorusParam`, with `c = 1`. -/
noncomputable def torusParamModel : TorusParam where
  psi := Work.Core.torusMap
  periodic_fst := Work.Core.torusMap_add_two_pi_left
  periodic_snd := Work.Core.torusMap_add_two_pi_right
  inj_mod := Work.Core.torusMap_eq_iff
  c := 1
  c_pos := by norm_num
  deriv_lower := deriv_lower_torusMap
  contDiff := contDiff_psiMap_torusMap

theorem exists_torusParam_torusMap :
    ∃ P : Work.TorusCover.TorusParam, P.psi = Work.Core.torusMap ∧ P.c = 1 :=
  ⟨torusParamModel, rfl, rfl⟩

end Work.TorusCover
