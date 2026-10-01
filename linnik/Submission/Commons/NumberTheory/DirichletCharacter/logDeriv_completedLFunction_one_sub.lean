import Mathlib.Data.FunLike.Fintype
import Submission.Commons.NumberTheory.DirichletCharacter.rectInt_logDeriv_gammaFactor_mul_eq

open Complex
open scoped Real Topology BigOperators

namespace Commons.NumberTheory.DirichletCharacter

noncomputable section

/-- The inverse of a non-trivial Dirichlet character is non-trivial. -/
private lemma inv_ne_one {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N} (hχ : χ ≠ 1) :
    χ⁻¹ ≠ 1 := by
  intro h
  apply hχ
  calc χ = (χ⁻¹)⁻¹ := by rw [inv_inv]
    _ = (1 : DirichletCharacter ℂ N)⁻¹ := by rw [h]
    _ = 1 := by simp

/-- `logDeriv` of `u ↦ c ^ (1/2 - u)`. -/
private lemma logDeriv_cpow_half_sub (c : ℂ) (hc : c ≠ 0) (u : ℂ) :
    logDeriv (fun z : ℂ => c ^ ((1 / 2 : ℂ) - z)) u = -Complex.log c := by
  have hinner : HasDerivAt (fun z : ℂ => (1 / 2 : ℂ) - z) (-1) u := by
    exact (hasDerivAt_id u).const_sub ((1 / 2 : ℂ))
  have houter : HasDerivAt (fun w : ℂ => c ^ w)
      (c ^ ((1 / 2 : ℂ) - u) * Complex.log c) ((1 / 2 : ℂ) - u) :=
    (Complex.hasStrictDerivAt_const_cpow (Or.inl hc)).hasDerivAt
  have hcomp : HasDerivAt (fun z : ℂ => c ^ ((1 / 2 : ℂ) - z))
      (c ^ ((1 / 2 : ℂ) - u) * Complex.log c * (-1)) u :=
    houter.comp u hinner
  rw [logDeriv_apply, hcomp.deriv]
  have hne : c ^ ((1 - 2 * u) / 2) ≠ 0 := Complex.cpow_ne_zero_iff.mpr (Or.inl hc)
  field_simp

/-- The completed Riemann zeta function is not differentiable at `0`. -/
private lemma not_differentiableAt_completedRiemannZeta_zero :
    ¬ DifferentiableAt ℂ completedRiemannZeta 0 := by
  intro hd
  have hfun : completedRiemannZeta = fun s : ℂ => completedRiemannZeta₀ s - s⁻¹ - (1 - s)⁻¹ := by
    funext s
    rw [completedRiemannZeta_eq]
    ring
  have hdiff : DifferentiableAt ℂ
      (fun s : ℂ => completedRiemannZeta₀ s - s⁻¹ - (1 - s)⁻¹) 0 := by
    rw [← hfun]; exact hd
  have hA : DifferentiableAt ℂ (fun s : ℂ => completedRiemannZeta₀ s) 0 :=
    differentiable_completedZeta₀.differentiableAt
  have hB : DifferentiableAt ℂ (fun s : ℂ => (1 - s)⁻¹) 0 := by
    have h1 : DifferentiableAt ℂ (fun s : ℂ => 1 - s) 0 := by fun_prop
    exact h1.inv (by norm_num)
  have hC : DifferentiableAt ℂ (fun s : ℂ => s⁻¹) 0 := by
    have h' : DifferentiableAt ℂ
        (fun s : ℂ => completedRiemannZeta₀ s - (1 - s)⁻¹ -
          (completedRiemannZeta₀ s - s⁻¹ - (1 - s)⁻¹)) 0 :=
      (hA.sub hB).sub hdiff
    convert h' using 1
    ext s; ring
  rw [differentiableAt_inv_iff] at hC
  exact hC rfl

/-- The completed Riemann zeta function is not differentiable at `1`. -/
private lemma not_differentiableAt_completedRiemannZeta_one :
    ¬ DifferentiableAt ℂ completedRiemannZeta 1 := by
  intro hd
  have hfun : completedRiemannZeta = fun s : ℂ => completedRiemannZeta₀ s - s⁻¹ - (1 - s)⁻¹ := by
    funext s
    rw [completedRiemannZeta_eq]
    ring
  have hdiff : DifferentiableAt ℂ
      (fun s : ℂ => completedRiemannZeta₀ s - s⁻¹ - (1 - s)⁻¹) 1 := by
    rw [← hfun]; exact hd
  have hA : DifferentiableAt ℂ (fun s : ℂ => completedRiemannZeta₀ s) 1 :=
    differentiable_completedZeta₀.differentiableAt
  have hB : DifferentiableAt ℂ (fun s : ℂ => s⁻¹) 1 := by
    have h1 : DifferentiableAt ℂ (fun s : ℂ => s) 1 := by fun_prop
    exact h1.inv (by norm_num)
  have hC : DifferentiableAt ℂ (fun s : ℂ => (1 - s)⁻¹) 1 := by
    have h' : DifferentiableAt ℂ
        (fun s : ℂ => completedRiemannZeta₀ s - s⁻¹ -
          (completedRiemannZeta₀ s - s⁻¹ - (1 - s)⁻¹)) 1 :=
      (hA.sub hB).sub hdiff
    convert h' using 1
    ext s; ring
  have hinner : DifferentiableAt ℂ (fun t : ℂ => 1 - t) 0 := by fun_prop
  have hC' : DifferentiableAt ℂ (fun s : ℂ => (1 - s)⁻¹) ((fun t : ℂ => 1 - t) 0) := by
    simpa using hC
  have h0 : DifferentiableAt ℂ ((fun s : ℂ => (1 - s)⁻¹) ∘ (fun t : ℂ => 1 - t)) 0 :=
    hC'.comp 0 hinner
  have h0' : DifferentiableAt ℂ (fun t : ℂ => t⁻¹) 0 := by
    convert h0 using 1
    ext t
    simp only [Function.comp_apply]
    congr 1
    ring
  rw [differentiableAt_inv_iff] at h0'
  exact h0' rfl

/-- The completed Riemann zeta function satisfies the logarithmic-derivative functional
equation at level `1`.  (Junk values of `deriv` at the poles `0` and `1` are harmless, since
both sides are then `0`.) -/
private lemma logDeriv_completedRiemannZeta_one_sub (s : ℂ) :
    logDeriv completedRiemannZeta s = - logDeriv completedRiemannZeta (1 - s) := by
  by_cases hs : s = 0 ∨ s = 1
  · have hz : logDeriv completedRiemannZeta s = 0 := by
      rcases hs with rfl | rfl
      · exact logDeriv_eq_zero_of_not_differentiableAt _ _
          not_differentiableAt_completedRiemannZeta_zero
      · exact logDeriv_eq_zero_of_not_differentiableAt _ _
          not_differentiableAt_completedRiemannZeta_one
    have hz' : logDeriv completedRiemannZeta (1 - s) = 0 := by
      rcases hs with rfl | rfl
      · simpa using logDeriv_eq_zero_of_not_differentiableAt _ _
          not_differentiableAt_completedRiemannZeta_one
      · simpa using logDeriv_eq_zero_of_not_differentiableAt _ _
          not_differentiableAt_completedRiemannZeta_zero
    rw [hz, hz']; ring
  · simp only [not_or] at hs
    obtain ⟨hs0, hs1⟩ := hs
    have h1s0 : 1 - s ≠ 0 := by
      intro h; exact hs1 (by linear_combination -h)
    have h1s1 : 1 - s ≠ 1 := by
      intro h; exact hs0 (by linear_combination -h)
    have hd2 : DifferentiableAt ℂ completedRiemannZeta (1 - s) :=
      differentiableAt_completedZeta h1s0 h1s1
    have hg : (fun u : ℂ => completedRiemannZeta (1 - u)) = completedRiemannZeta := by
      funext u; exact completedRiemannZeta_one_sub u
    have e1 : logDeriv completedRiemannZeta s
        = logDeriv (fun u : ℂ => completedRiemannZeta (1 - u)) s := by
      rw [hg]
    have e2 : logDeriv (fun u : ℂ => completedRiemannZeta (1 - u)) s
        = logDeriv completedRiemannZeta (1 - s) * deriv (fun u : ℂ => 1 - u) s := by
      have h := logDeriv_comp (f := completedRiemannZeta) (g := fun u : ℂ => 1 - u)
        (x := s) hd2 (by fun_prop)
      simpa only [Function.comp_def] using h
    have hderiv : deriv (fun u : ℂ => 1 - u) s = -1 := by
      simpa using (hasDerivAt_id s).const_sub (1 : ℂ)
    rw [e1, e2, hderiv]; ring

/-- **Functional equation for the logarithmic derivative of the completed L-function.** -/
theorem logDeriv_completedLFunction_one_sub {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (hχprim : χ.IsPrimitive) {s : ℂ}
    (h1 : DirichletCharacter.completedLFunction χ s ≠ 0)
    (h2 : DirichletCharacter.completedLFunction χ⁻¹ (1 - s) ≠ 0) :
    logDeriv (DirichletCharacter.completedLFunction χ) s
      = -(Real.log (N : ℝ) : ℂ) - logDeriv (DirichletCharacter.completedLFunction χ⁻¹) (1 - s) := by
  by_cases htriv : χ = 1
  · -- The trivial character: necessarily `N = 1`, and everything reduces to the completed zeta.
    have hN1 : N = 1 := by
      have hcond : DirichletCharacter.conductor χ = N := hχprim
      rw [htriv] at hcond
      rw [DirichletCharacter.conductor_one] at hcond
      exact hcond.symm
    subst hN1
    rw [htriv]
    simp only [inv_one, Nat.cast_one, Real.log_one, Complex.ofReal_zero, neg_zero, zero_sub,
      DirichletCharacter.completedLFunction_modOne_eq]
    exact logDeriv_completedRiemannZeta_one_sub s
  · -- Nontrivial character: differentiate the functional equation.
    have hN : (N : ℂ) ≠ 0 := by exact_mod_cast (NeZero.ne N)
    have hlogN : ((Real.log (N : ℝ) : ℂ)) = Complex.log (N : ℂ) := by
      rw [Complex.ofReal_log (Nat.cast_nonneg N), Complex.ofReal_natCast]
    rw [hlogN]
    have hc0 : χ.rootNumber ≠ 0 := by
      intro h
      have := rootNumber_norm_eq_one χ hχprim
      rw [h] at this
      norm_num at this
    set Λ := DirichletCharacter.completedLFunction χ with hΛ
    set Λi := DirichletCharacter.completedLFunction χ⁻¹ with hΛi
    have hFE : ∀ u : ℂ, Λ u = (N : ℂ) ^ ((1 / 2 : ℂ) - u) * χ.rootNumber * Λi (1 - u) := by
      intro u
      simpa [hΛ, hΛi] using completedLFunction_eq χ hχprim u
    set F : ℂ → ℂ := fun u => (N : ℂ) ^ ((1 / 2 : ℂ) - u) * χ.rootNumber with hF
    set G : ℂ → ℂ := fun u => Λi (1 - u) with hG
    have hFG : ∀ u, Λ u = F u * G u := by intro u; rw [hFE u, hF, hG]
    have hF0 : F s ≠ 0 :=
      mul_ne_zero (Complex.cpow_ne_zero_iff.mpr (Or.inl hN)) hc0
    have hG0 : G s ≠ 0 := by
      rw [hG]
      exact h2
    have hFd : DifferentiableAt ℂ F s := by
      rw [hF]
      exact (DifferentiableAt.const_cpow (by fun_prop) (Or.inl hN)).mul_const _
    have hΛid : Differentiable ℂ Λi :=
      DirichletCharacter.differentiable_completedLFunction (χ := χ⁻¹) (inv_ne_one htriv)
    have hGd : DifferentiableAt ℂ G s := by
      rw [hG]
      exact hΛid.differentiableAt.comp s (by fun_prop)
    have hFderiv : logDeriv F s = -Complex.log (N : ℂ) := by
      rw [hF, logDeriv_mul_const (f := fun u : ℂ => (N : ℂ) ^ ((1 / 2 : ℂ) - u)) s
        χ.rootNumber hc0]
      exact logDeriv_cpow_half_sub (N : ℂ) hN s
    have hGderiv : logDeriv G s = - logDeriv Λi (1 - s) := by
      rw [hG]
      have hcomp : (fun u : ℂ => Λi (1 - u)) = Λi ∘ (fun u : ℂ => 1 - u) := rfl
      rw [hcomp, logDeriv_comp _ (by fun_prop)]
      · have hd : deriv (fun u : ℂ => 1 - u) s = -1 := by
          simpa using (hasDerivAt_id s).const_sub (1 : ℂ)
        rw [hd]; ring
      · exact hΛid.differentiableAt
    have hΛFG : Λ = fun u : ℂ => F u * G u := by funext u; exact hFG u
    rw [hΛFG]; erw [logDeriv_mul (f := F) (g := G) s hF0 hG0 hFd hGd]; rw [hFderiv, hGderiv]
    ring

end

end Commons.NumberTheory.DirichletCharacter