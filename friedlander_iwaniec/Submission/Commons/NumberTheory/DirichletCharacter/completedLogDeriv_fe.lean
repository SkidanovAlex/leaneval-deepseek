import Mathlib.Data.FunLike.Fintype
import Submission.Commons.NumberTheory.DirichletCharacter.completedLFunction_eq
import Submission.Commons.NumberTheory.DirichletCharacter.rootNumber_norm_eq_one
import Submission.Port.LogDerivCompat

open Complex DirichletCharacter Filter
open scoped Real Topology
set_option autoImplicit false
noncomputable section

namespace Commons.NumberTheory.DirichletCharacter

/-! ### Non-differentiability of the completed Riemann zeta function at its poles -/

/-- The completed Riemann zeta function has a simple pole of residue `-1` at `s = 0`. -/
private lemma completedRiemannZeta_residue_zero :
    Tendsto (fun s : ℂ => s * completedRiemannZeta s) (𝓝[≠] 0) (𝓝 (-1)) := by
  have h := HurwitzZeta.completedHurwitzZetaEven_residue_zero (a := (0 : UnitAddCircle))
  convert h using 1
  · ext s
    simp [HurwitzZeta.completedHurwitzZetaEven_zero]
  · simp

/-- The completed Riemann zeta function is not continuous (hence not differentiable) at `s = 1`,
since it has a simple pole there. -/
private lemma not_continuousAt_completedRiemannZeta_one : ¬ ContinuousAt completedRiemannZeta 1 := by
  have hres := completedRiemannZeta_residue_one
  intro hc
  have hc' : ContinuousAt (fun s : ℂ => (s - 1) * completedRiemannZeta s) 1 := by
    exact (continuousAt_id.sub continuousAt_const).mul hc
  have ht0 : Tendsto (fun s : ℂ => (s - 1) * completedRiemannZeta s) (𝓝[≠] 1) (𝓝 (0 : ℂ)) := by
    simpa using continuousAt_iff_punctured_nhds.mp hc'
  exact hres.not_tendsto (disjoint_nhds_nhds.mpr (by simp : (1 : ℂ) ≠ 0)) ht0

private lemma not_differentiableAt_completedRiemannZeta_one :
    ¬ DifferentiableAt ℂ completedRiemannZeta 1 :=
  mt DifferentiableAt.continuousAt not_continuousAt_completedRiemannZeta_one

/-- The completed Riemann zeta function is not continuous (hence not differentiable) at `s = 0`,
since it has a simple pole there. -/
private lemma not_continuousAt_completedRiemannZeta_zero : ¬ ContinuousAt completedRiemannZeta 0 := by
  have hres := completedRiemannZeta_residue_zero
  intro hc
  have hc' : ContinuousAt (fun s : ℂ => s * completedRiemannZeta s) 0 :=
    continuousAt_id.mul hc
  have ht0 : Tendsto (fun s : ℂ => s * completedRiemannZeta s) (𝓝[≠] 0) (𝓝 (0 : ℂ)) := by
    simpa using continuousAt_iff_punctured_nhds.mp hc'
  exact hres.not_tendsto (disjoint_nhds_nhds.mpr (by simp : (-1 : ℂ) ≠ 0)) ht0

private lemma not_differentiableAt_completedRiemannZeta_zero :
    ¬ DifferentiableAt ℂ completedRiemannZeta 0 :=
  mt DifferentiableAt.continuousAt not_continuousAt_completedRiemannZeta_zero

/-! ### The logarithmic derivative of the functional equation -/

/-- Logarithmic derivative of the functional equation for the completed Dirichlet
L-function: for primitive `χ`,
`logDeriv (completedLFunction χ) s = -log N - logDeriv (completedLFunction χ⁻¹) (1 - s)`
whenever both completed L-values in question are nonzero.

Derivation: differentiate
`completedLFunction χ s = (N:ℂ)^(1/2 - s) * χ.rootNumber * completedLFunction χ⁻¹ (1 - s)`
(`Commons.NumberTheory.DirichletCharacter.completedLFunction_eq`), using
`Submission.Port.logDeriv_mul_fun`, the log-derivative `-log N` of the cpow factor, and the chain rule for the
composition `s ↦ 1 - s` (its log-derivative contribution is
`-logDeriv (completedLFunction χ⁻¹) (1 - s)` since `deriv (1 - s) = -1`). -/
theorem completedLogDeriv_fe {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (hχprim : χ.IsPrimitive) (s : ℂ)
    (hΛ : DirichletCharacter.completedLFunction χ s ≠ 0)
    (hΛc : DirichletCharacter.completedLFunction (χ⁻¹) (1 - s) ≠ 0) :
    logDeriv (DirichletCharacter.completedLFunction χ) s =
      -((Real.log (N : ℝ) : ℂ)) -
        logDeriv (DirichletCharacter.completedLFunction (χ⁻¹)) (1 - s) := by
  classical
  by_cases htriv : χ = 1
  · -- Trivial character: primitivity forces N = 1, and both sides are computed from the
    -- functional equation `Λ(s) = Λ(1 - s)` of the completed Riemann zeta function.
    have hN1 : N = 1 := by
      have hc := (DirichletCharacter.isPrimitive_def (χ := χ)).mp hχprim
      have hc1 : conductor χ = 1 := by rw [htriv, DirichletCharacter.conductor_one]
      exact hc.symm.trans hc1
    subst N
    subst htriv
    -- From now on the completed L-function is the completed Riemann zeta function.
    have hχi : (1 : DirichletCharacter ℂ 1)⁻¹ = (1 : DirichletCharacter ℂ 1) := by simp
    have hmod : DirichletCharacter.completedLFunction (1 : DirichletCharacter ℂ 1) =
        completedRiemannZeta := DirichletCharacter.completedLFunction_modOne_eq
    rw [hχi, hmod] at ⊢
    by_cases hz : s = 0
    · subst s
      have hld0 : logDeriv completedRiemannZeta 0 = 0 :=
        logDeriv_eq_zero_of_not_differentiableAt completedRiemannZeta 0
          not_differentiableAt_completedRiemannZeta_zero
      have hld1 : logDeriv completedRiemannZeta 1 = 0 :=
        logDeriv_eq_zero_of_not_differentiableAt completedRiemannZeta 1
          not_differentiableAt_completedRiemannZeta_one
      simp [hld0, hld1]
    · by_cases ho : s = 1
      · subst s
        have hld0 : logDeriv completedRiemannZeta 0 = 0 :=
          logDeriv_eq_zero_of_not_differentiableAt completedRiemannZeta 0
            not_differentiableAt_completedRiemannZeta_zero
        have hld1 : logDeriv completedRiemannZeta 1 = 0 :=
          logDeriv_eq_zero_of_not_differentiableAt completedRiemannZeta 1
            not_differentiableAt_completedRiemannZeta_one
        simp [hld0, hld1]
      · -- `s` is away from the poles `0` and `1` (and so is `1 - s`).
        have h1s0 : (1 : ℂ) - s ≠ 0 := by
          intro h
          apply ho
          exact (sub_eq_zero.mp h).symm
        have h1s1 : (1 : ℂ) - s ≠ 1 := by
          intro h
          apply hz
          exact sub_right_injective (b := (1 : ℂ)) (by simpa using h)
        have hdf : DifferentiableAt ℂ completedRiemannZeta (1 - s) :=
          differentiableAt_completedZeta h1s0 h1s1
        have hfun : completedRiemannZeta =
            completedRiemannZeta ∘ (fun z : ℂ => 1 - z) := by
          funext z
          exact (completedRiemannZeta_one_sub z).symm
        have hldcomp : logDeriv (completedRiemannZeta ∘ (fun z : ℂ => 1 - z)) s =
            -logDeriv completedRiemannZeta (1 - s) := by
          have hld := logDeriv_comp (f := completedRiemannZeta)
            (g := fun z : ℂ => 1 - z) (x := s) hdf (by fun_prop)
          have hdg' : deriv (fun z : ℂ => 1 - z) s = -1 := by
            simp [deriv_const_sub_id]
          rw [hdg'] at hld
          simpa [mul_comm] using hld
        have hstep : logDeriv completedRiemannZeta s =
            -logDeriv completedRiemannZeta (1 - s) := by
          conv_lhs => rw [hfun]
          rw [hldcomp]
        rw [hstep]
        simp [Real.log_one]
  · -- Nontrivial character: `completedLFunction χ` is a product of three factors
    --   (N:ℂ)^(1/2 - z) · χ.rootNumber · completedLFunction χ⁻¹ (1 - z),
    -- whose logarithmic derivative is `-log N - logDeriv (completedLFunction χ⁻¹) (1 - s)`.
    let C : ℂ → ℂ := DirichletCharacter.completedLFunction (χ⁻¹)
    let f1 : ℂ → ℂ := fun z => (N : ℂ) ^ (1 / 2 - z)
    let A : ℂ → ℂ := fun z => f1 z * χ.rootNumber
    have hN0 : (N : ℂ) ≠ 0 := by exact_mod_cast (NeZero.ne N)
    have hf1s0 : f1 s ≠ 0 := by
      dsimp [f1]
      exact (Complex.cpow_ne_zero_iff (x := (N : ℂ)) (y := (1 / 2 - s))).2 (Or.inl hN0)
    have hrn0 : χ.rootNumber ≠ 0 := by
      intro hz0
      have hnorm := rootNumber_norm_eq_one χ hχprim
      rw [hz0, norm_zero] at hnorm
      norm_num at hnorm
    have hAs0 : A s ≠ 0 := by
      dsimp [A]
      exact mul_ne_zero hf1s0 hrn0
    have hCs0 : C (1 - s) ≠ 0 := by
      dsimp [C]
      exact hΛc
    have hgexp : DifferentiableAt ℂ (fun z : ℂ => (1 / 2 : ℂ) - z) s := by fun_prop
    have hdf1 : DifferentiableAt ℂ f1 s := by
      dsimp [f1]
      exact DifferentiableAt.const_cpow (f := fun z : ℂ => (1 / 2 : ℂ) - z) hgexp (Or.inl hN0)
    have hdA : DifferentiableAt ℂ A s := by
      dsimp [A]
      exact hdf1.mul (differentiableAt_const χ.rootNumber)
    have hCinv1 : (χ⁻¹) ≠ 1 := by
      intro hInv
      apply htriv
      calc
        χ = (χ⁻¹)⁻¹ := by simp
        _ = (1 : DirichletCharacter ℂ N)⁻¹ := by rw [hInv]
        _ = 1 := by simp
    have hdC : DifferentiableAt ℂ C (1 - s) := by
      dsimp [C]
      exact (differentiable_completedLFunction (χ := χ⁻¹) hCinv1) (1 - s)
    have hdcomp : DifferentiableAt ℂ (fun z : ℂ => C (1 - z)) s := by
      have : DifferentiableAt ℂ (fun z : ℂ => 1 - z) s := by fun_prop
      exact DifferentiableAt.comp s hdC this
    have hdexp' : deriv (fun z : ℂ => (1 / 2 : ℂ) - z) s = -1 := by
      simp [deriv_const_sub_id]
    have hlogf1 : logDeriv f1 s = -log (N : ℂ) := by
      have hderiv : deriv f1 s =
          log (N : ℂ) * deriv (fun z : ℂ => (1 / 2 : ℂ) - z) s * f1 s := by
        dsimp [f1]
        simpa using Complex.deriv_const_cpow (f := fun z : ℂ => (1 / 2 : ℂ) - z) hgexp (N : ℂ)
      calc
        logDeriv f1 s = deriv f1 s / f1 s := rfl
        _ = log (N : ℂ) * deriv (fun z : ℂ => (1 / 2 : ℂ) - z) s * f1 s / f1 s := by rw [hderiv]
        _ = -log (N : ℂ) := by
          rw [hdexp']
          field_simp [hf1s0]
    have hlogA : logDeriv A s = logDeriv f1 s := by
      dsimp [A]
      exact logDeriv_mul_const s χ.rootNumber hrn0
    have hlogcomp : logDeriv (fun z : ℂ => C (1 - z)) s = -logDeriv C (1 - s) := by
      have hld := logDeriv_comp (f := C) (g := fun z : ℂ => 1 - z) (x := s) hdC
        (by fun_prop : DifferentiableAt ℂ (fun z : ℂ => 1 - z) s)
      have hdg' : deriv (fun z : ℂ => 1 - z) s = -1 := by
        simp [deriv_const_sub_id]
      rw [hdg'] at hld
      rw [show (C ∘ (fun z : ℂ => 1 - z)) = (fun z : ℂ => C (1 - z)) by rfl] at hld
      simpa [mul_comm] using hld
    have hmain : logDeriv (fun z : ℂ => A z * C (1 - z)) s =
        -log (N : ℂ) - logDeriv C (1 - s) := by
      have hmul := Submission.Port.logDeriv_mul_fun (x := s) (f := A) (g := fun z : ℂ => C (1 - z))
        hAs0 hCs0 hdA hdcomp
      rw [hlogA, hlogcomp, hlogf1] at hmul
      simpa [sub_eq_add_neg] using hmul
    calc
      logDeriv (DirichletCharacter.completedLFunction χ) s
          = logDeriv (fun z : ℂ => f1 z * χ.rootNumber * C (1 - z)) s := by
              congr 1
              funext z
              dsimp [C, f1]
              exact completedLFunction_eq χ hχprim z
      _ = logDeriv (fun z : ℂ => A z * C (1 - z)) s := by
              rfl
      _ = -log (N : ℂ) - logDeriv C (1 - s) := hmain
      _ = -((Real.log (N : ℝ) : ℂ)) -
            logDeriv (DirichletCharacter.completedLFunction (χ⁻¹)) (1 - s) := by
              have hlog : log (N : ℂ) = (Real.log (N : ℝ) : ℂ) := by
                simp [Complex.natCast_log]
              rw [← hlog]

end Commons.NumberTheory.DirichletCharacter