import Submission.Work.FunctionalEquations.DeltaGen
import Submission.Work.CKFinal.Shadow.Util
import Submission.Work.CKFinal.Shadow.Basic
import Submission.Work.CKFinal.Shadow.Gen
import Submission.Work.CKFinal.Shadow.ValuePatternGen

open scoped ContDiff
set_option linter.dupNamespace false

namespace Work.CKFinal.Shadow

namespace Work.FunctionalEquations
export _root_.Work.FunctionalEquations (FourierInversionRadial)
end Work.FunctionalEquations

/-!
# The samples of the general-`k₀` interpolation basis are Kronecker deltas

For a solution `S : InterpolationSolutionGen n k₀` of the general-`k₀` functional
equations, the four samples of the `i`-th basis function are `1` at the sample `i` and
`0` at every other sample:

`coeffs n k₀ (S.basis i).1 = fun j => if j = i then 1 else 0`.

The value/derivative pattern at the sample points is `ValuePatternGen` (CKMRV Section 8);
the passage to the samples of the basis functions uses that the Fourier transform
exchanges `a_m ↔ ã_m` and `b_m ↔ b̃_m`, together with Fourier inversion for radial
Schwartz functions. This mirrors the `k₀ = 1` development in
`Submission.Work.FunctionalEquations.BasisCoeffsDelta`.
-/

namespace Work.FunctionalEquations

open LeanEval.Analysis.CKMRVInterpolation Work.Core Work.FE Filter Topology
open scoped FourierTransform SchwartzMap

/-- The first radial derivative at a point of the positive axis is the one-variable
derivative of the profile `r ↦ g (realIncl r)`.  (Local copy, to avoid importing the
`k₀ = 1` auxiliary file.) -/
private lemma dgen_radialDeriv_one_of_nonneg {n : ℕ} [NeZero n] (g : E n → ℂ) {r : ℝ}
    (hr : 0 ≤ r) :
    radialDeriv 1 g (realIncl (n := n) r) = deriv (g ∘ realIncl (n := n)) r := by
  rw [radialDeriv, iteratedDeriv_one, Work.Sampling.realIncl_norm, abs_of_nonneg hr]
  rfl

/-- The value sample of `coeffs` is evaluation at the sample point. -/
private lemma dgen_coeffs_zero {n : ℕ} [NeZero n] (k₀ : ℕ) (f : 𝓢(E n, ℂ))
    (k : Set.Ici k₀) :
    coeffs n k₀ f (k, 0) = f (samplePoint (n := n) (k.1 : ℝ)) := by
  simp [coeffs, Function.uncurry_apply_pair, samplePoint]

/-- The Fourier-value sample of `coeffs` is the Fourier transform at the sample point. -/
private lemma dgen_coeffs_one {n : ℕ} [NeZero n] (k₀ : ℕ) (f : 𝓢(E n, ℂ))
    (k : Set.Ici k₀) :
    coeffs n k₀ f (k, 1)
      = (FourierTransform.fourierCLM ℂ (𝓢(E n, ℂ)) f) (samplePoint (n := n) (k.1 : ℝ)) := by
  simp [coeffs, Function.uncurry_apply_pair, samplePoint]

/-- The radial-derivative sample of `coeffs` is the first radial derivative at the
sample point. -/
private lemma dgen_coeffs_two {n : ℕ} [NeZero n] (k₀ : ℕ) (f : 𝓢(E n, ℂ))
    (k : Set.Ici k₀) :
    coeffs n k₀ f (k, 2) = radialDeriv 1 (⇑f) (samplePoint (n := n) (k.1 : ℝ)) := by
  rw [show samplePoint (n := n) (k.1 : ℝ) = realIncl (Real.sqrt (2 * (k.1 : ℝ))) from rfl]
  rw [dgen_radialDeriv_one_of_nonneg (g := ⇑f) (Real.sqrt_nonneg _)]
  simp [coeffs, Function.uncurry_apply_pair]

/-- The radial-derivative of the Fourier sample of `coeffs` is the first radial
derivative of the Fourier transform at the sample point. -/
private lemma dgen_coeffs_three {n : ℕ} [NeZero n] (k₀ : ℕ) (f : 𝓢(E n, ℂ))
    (k : Set.Ici k₀) :
    coeffs n k₀ f (k, 3)
      = radialDeriv 1 (⇑(FourierTransform.fourierCLM ℂ (𝓢(E n, ℂ)) f))
          (samplePoint (n := n) (k.1 : ℝ)) := by
  rw [show samplePoint (n := n) (k.1 : ℝ) = realIncl (Real.sqrt (2 * (k.1 : ℝ))) from rfl]
  rw [dgen_radialDeriv_one_of_nonneg (g := ⇑(FourierTransform.fourierCLM ℂ (𝓢(E n, ℂ)) f))
    (Real.sqrt_nonneg _)]
  simp [coeffs, Function.uncurry_apply_pair]

/-- The condition `(k, s) = (m, s)` only involves the first coordinate. -/
private lemma dgen_ite_diag {α : Type*} [DecidableEq α] {k m : α} (s : Fin 4) (a : ℂ) :
    (if (k, s) = (m, s) then a else 0) = (if k = m then a else 0) := by
  by_cases h : k = m
  · subst h; simp
  · rw [if_neg h, if_neg (fun hh => h (Prod.ext_iff.mp hh).1)]

/-- **The samples of the general-`k₀` interpolation basis are Kronecker deltas.** -/
theorem DeltaGen {n : ℕ} [NeZero n] {k₀ : ℕ} (hk : 1 ≤ k₀)
    (S : InterpolationSolutionGen n k₀) :
    ∀ i : SampleIdx k₀, coeffs n k₀ (S.basis i).1 = fun j => if j = i then (1 : ℂ) else 0 := by
  have hpat := ValuePatternGen hk S
  intro i
  obtain ⟨m, s⟩ := i
  have hFF1 : FourierTransform.fourierCLM ℂ (𝓢(E n, ℂ))
      (FourierTransform.fourierCLM ℂ (𝓢(E n, ℂ)) (S.basis (m, 0)).1)
      = (S.basis (m, 0)).1 := by
    ext y
    exact FourierInversionRadial (S.basis (m, 0)).1 (S.basis (m, 0)).2 y
  have hFF2 : FourierTransform.fourierCLM ℂ (𝓢(E n, ℂ))
      (FourierTransform.fourierCLM ℂ (𝓢(E n, ℂ)) (S.basis (m, 2)).1)
      = (S.basis (m, 2)).1 := by
    ext y
    exact FourierInversionRadial (S.basis (m, 2)).1 (S.basis (m, 2)).2 y
  fin_cases s
  · funext j
    obtain ⟨k, t⟩ := j
    fin_cases t
    · show coeffs n k₀ (S.basis (m, (0 : Fin 4))).1 (k, (0 : Fin 4))
          = (if (k, (0 : Fin 4)) = (m, (0 : Fin 4)) then (1 : ℂ) else 0)
      rw [dgen_coeffs_zero, dgen_ite_diag (0 : Fin 4) (1 : ℂ)]
      exact (hpat m k).1
    · show coeffs n k₀ (S.basis (m, (0 : Fin 4))).1 (k, (1 : Fin 4))
          = (if (k, (1 : Fin 4)) = (m, (0 : Fin 4)) then (1 : ℂ) else 0)
      rw [dgen_coeffs_one, ← S.fourier_basis m,
        if_neg (by simp : ¬ ((k, (1 : Fin 4)) = (m, (0 : Fin 4))))]
      exact (hpat m k).2.1
    · show coeffs n k₀ (S.basis (m, (0 : Fin 4))).1 (k, (2 : Fin 4))
          = (if (k, (2 : Fin 4)) = (m, (0 : Fin 4)) then (1 : ℂ) else 0)
      rw [dgen_coeffs_two, if_neg (by simp : ¬ ((k, (2 : Fin 4)) = (m, (0 : Fin 4))))]
      exact (hpat m k).2.2.2.2.1
    · show coeffs n k₀ (S.basis (m, (0 : Fin 4))).1 (k, (3 : Fin 4))
          = (if (k, (3 : Fin 4)) = (m, (0 : Fin 4)) then (1 : ℂ) else 0)
      rw [dgen_coeffs_three, ← S.fourier_basis m,
        if_neg (by simp : ¬ ((k, (3 : Fin 4)) = (m, (0 : Fin 4))))]
      exact (hpat m k).2.2.2.2.2.1
  · funext j
    obtain ⟨k, t⟩ := j
    fin_cases t
    · show coeffs n k₀ (S.basis (m, (1 : Fin 4))).1 (k, (0 : Fin 4))
          = (if (k, (0 : Fin 4)) = (m, (1 : Fin 4)) then (1 : ℂ) else 0)
      rw [dgen_coeffs_zero, if_neg (by simp : ¬ ((k, (0 : Fin 4)) = (m, (1 : Fin 4))))]
      exact (hpat m k).2.1
    · show coeffs n k₀ (S.basis (m, (1 : Fin 4))).1 (k, (1 : Fin 4))
          = (if (k, (1 : Fin 4)) = (m, (1 : Fin 4)) then (1 : ℂ) else 0)
      rw [dgen_coeffs_one, S.fourier_basis m, hFF1, dgen_ite_diag (1 : Fin 4) (1 : ℂ)]
      exact (hpat m k).1
    · show coeffs n k₀ (S.basis (m, (1 : Fin 4))).1 (k, (2 : Fin 4))
          = (if (k, (2 : Fin 4)) = (m, (1 : Fin 4)) then (1 : ℂ) else 0)
      rw [dgen_coeffs_two, if_neg (by simp : ¬ ((k, (2 : Fin 4)) = (m, (1 : Fin 4))))]
      exact (hpat m k).2.2.2.2.2.1
    · show coeffs n k₀ (S.basis (m, (1 : Fin 4))).1 (k, (3 : Fin 4))
          = (if (k, (3 : Fin 4)) = (m, (1 : Fin 4)) then (1 : ℂ) else 0)
      rw [dgen_coeffs_three, S.fourier_basis m, hFF1,
        if_neg (by simp : ¬ ((k, (3 : Fin 4)) = (m, (1 : Fin 4))))]
      exact (hpat m k).2.2.2.2.1
  · funext j
    obtain ⟨k, t⟩ := j
    fin_cases t
    · show coeffs n k₀ (S.basis (m, (2 : Fin 4))).1 (k, (0 : Fin 4))
          = (if (k, (0 : Fin 4)) = (m, (2 : Fin 4)) then (1 : ℂ) else 0)
      rw [dgen_coeffs_zero, if_neg (by simp : ¬ ((k, (0 : Fin 4)) = (m, (2 : Fin 4))))]
      exact (hpat m k).2.2.1
    · show coeffs n k₀ (S.basis (m, (2 : Fin 4))).1 (k, (1 : Fin 4))
          = (if (k, (1 : Fin 4)) = (m, (2 : Fin 4)) then (1 : ℂ) else 0)
      rw [dgen_coeffs_one, ← S.fourier_basis' m,
        if_neg (by simp : ¬ ((k, (1 : Fin 4)) = (m, (2 : Fin 4))))]
      exact (hpat m k).2.2.2.1
    · show coeffs n k₀ (S.basis (m, (2 : Fin 4))).1 (k, (2 : Fin 4))
          = (if (k, (2 : Fin 4)) = (m, (2 : Fin 4)) then (1 : ℂ) else 0)
      rw [dgen_coeffs_two, dgen_ite_diag (2 : Fin 4) (1 : ℂ)]
      exact (hpat m k).2.2.2.2.2.2.1
    · show coeffs n k₀ (S.basis (m, (2 : Fin 4))).1 (k, (3 : Fin 4))
          = (if (k, (3 : Fin 4)) = (m, (2 : Fin 4)) then (1 : ℂ) else 0)
      rw [dgen_coeffs_three, ← S.fourier_basis' m,
        if_neg (by simp : ¬ ((k, (3 : Fin 4)) = (m, (2 : Fin 4))))]
      exact (hpat m k).2.2.2.2.2.2.2
  · funext j
    obtain ⟨k, t⟩ := j
    fin_cases t
    · show coeffs n k₀ (S.basis (m, (3 : Fin 4))).1 (k, (0 : Fin 4))
          = (if (k, (0 : Fin 4)) = (m, (3 : Fin 4)) then (1 : ℂ) else 0)
      rw [dgen_coeffs_zero, if_neg (by simp : ¬ ((k, (0 : Fin 4)) = (m, (3 : Fin 4))))]
      exact (hpat m k).2.2.2.1
    · show coeffs n k₀ (S.basis (m, (3 : Fin 4))).1 (k, (1 : Fin 4))
          = (if (k, (1 : Fin 4)) = (m, (3 : Fin 4)) then (1 : ℂ) else 0)
      rw [dgen_coeffs_one, S.fourier_basis' m, hFF2,
        if_neg (by simp : ¬ ((k, (1 : Fin 4)) = (m, (3 : Fin 4))))]
      exact (hpat m k).2.2.1
    · show coeffs n k₀ (S.basis (m, (3 : Fin 4))).1 (k, (2 : Fin 4))
          = (if (k, (2 : Fin 4)) = (m, (3 : Fin 4)) then (1 : ℂ) else 0)
      rw [dgen_coeffs_two, if_neg (by simp : ¬ ((k, (2 : Fin 4)) = (m, (3 : Fin 4))))]
      exact (hpat m k).2.2.2.2.2.2.2
    · show coeffs n k₀ (S.basis (m, (3 : Fin 4))).1 (k, (3 : Fin 4))
          = (if (k, (3 : Fin 4)) = (m, (3 : Fin 4)) then (1 : ℂ) else 0)
      rw [dgen_coeffs_three, S.fourier_basis' m, hFF2, dgen_ite_diag (3 : Fin 4) (1 : ℂ)]
      exact (hpat m k).2.2.2.2.2.2.1

end Work.FunctionalEquations


end Work.CKFinal.Shadow
