import Mathlib
import Submission.Work.KMTAreas.A7.lacModDiffDefs

set_option autoImplicit false

namespace Work.KMTAreas.A7

open scoped BigOperators

noncomputable section

/-! ## Differentiating the modulated block

The modulated block `modBlock Φ s l ξ = Φ (s ξ) · e (l ξ)` of `lacModDiffDefs` is differentiable
whenever `Φ` is, with the closed-form derivative `modBlockD Φ s l`; and `modBlockD` is itself
differentiable whenever `deriv Φ` is, with derivative `modBlockD2 Φ s l`.  The hypotheses

* `hΦd : ∀ y, HasDerivAt Φ (deriv Φ y) y`  (i.e. `Φ` is differentiable with derivative `deriv Φ`), and
* `hΦd2 : ∀ y, HasDerivAt (deriv Φ) (iteratedDeriv 2 Φ y) y`

are exactly the differentiability statements that the closed forms need; nothing else is used.
-/

/-- The character `ξ ↦ e (c ξ) = exp (2 π i c ξ)` is differentiable with derivative
`(2 π i c) · e (c ξ)`. -/
lemma hasDerivAt_ee_mul (c x : ℝ) :
    HasDerivAt (fun ξ : ℝ => ee (c * ξ)) ((2 * ↑Real.pi * Complex.I * ↑c) * ee (c * x)) x := by
  have hinner : HasDerivAt (fun ξ : ℝ => (2 * ↑Real.pi * Complex.I * ↑c) * (ξ : ℂ))
      (2 * ↑Real.pi * Complex.I * ↑c) x := by
    simpa using ((hasDerivAt_id x).ofReal_comp.const_mul (2 * ↑Real.pi * Complex.I * ↑c))
  have key := hinner.cexp
  have hfun : (fun ξ : ℝ => Complex.exp ((2 * ↑Real.pi * Complex.I * ↑c) * (ξ : ℂ))) =
      (fun ξ : ℝ => ee (c * ξ)) := by
    funext ξ
    simp only [ee]
    push_cast
    ring_nf
  rw [hfun] at key
  have hval : (2 * ↑Real.pi * Complex.I * ↑c) * ee (c * x) =
      Complex.exp ((2 * ↑Real.pi * Complex.I * ↑c) * (x : ℂ)) * (2 * ↑Real.pi * Complex.I * ↑c) := by
    have h : ee (c * x) = Complex.exp ((2 * ↑Real.pi * Complex.I * ↑c) * (x : ℂ)) := by
      simp only [ee]; push_cast; ring_nf
    rw [h]; ring
  rw [hval]
  exact key

/-- Chain rule for a scalar multiple: if `f` is differentiable at `s * ξ` then `y ↦ f (s * y)` is
differentiable at `ξ`, with derivative `s • f'`. -/
lemma hasDerivAt_comp_const_mul {f : ℝ → ℂ} {f' : ℂ} {s ξ : ℝ}
    (hf : HasDerivAt f f' (s * ξ)) : HasDerivAt (fun y : ℝ => f (s * y)) (s • f') ξ := by
  have hlin : HasDerivAt (fun y : ℝ => s * y) s ξ := hasDerivAt_const_mul (x := ξ) s
  simpa [Function.comp_def] using
    HasDerivAt.scomp (x := ξ) (h := fun y : ℝ => s * y) (h' := s) (g₁ := f) (g₁' := f') hf hlin

/-- The first derivative of the modulated block. -/
lemma hasDerivAt_modBlock {Φ : ℝ → ℂ} (hΦd : ∀ y : ℝ, HasDerivAt Φ (deriv Φ y) y)
    (s l : ℝ) (ξ : ℝ) :
    HasDerivAt (modBlock Φ s l) (modBlockD Φ s l ξ) ξ := by
  have hcomp : HasDerivAt (fun y : ℝ => Φ (s * y)) (s • deriv Φ (s * ξ)) ξ :=
    hasDerivAt_comp_const_mul (hΦd (s * ξ))
  have h0 : HasDerivAt (modBlock Φ s l)
      ((s • deriv Φ (s * ξ)) * ee (l * ξ)
        + Φ (s * ξ) * ((2 * ↑Real.pi * Complex.I * ↑l) * ee (l * ξ))) ξ := by
    unfold modBlock
    exact hcomp.mul (hasDerivAt_ee_mul l ξ)
  have hval : (s • deriv Φ (s * ξ)) * ee (l * ξ)
        + Φ (s * ξ) * ((2 * ↑Real.pi * Complex.I * ↑l) * ee (l * ξ)) = modBlockD Φ s l ξ := by
    simp only [modBlockD, Complex.real_smul]
  rwa [hval] at h0

/-- The second derivative of the modulated block. -/
lemma hasDerivAt_modBlockD {Φ : ℝ → ℂ} (hΦd : ∀ y : ℝ, HasDerivAt Φ (deriv Φ y) y)
    (hΦd2 : ∀ y : ℝ, HasDerivAt (deriv Φ) (iteratedDeriv 2 Φ y) y) (s l : ℝ) (ξ : ℝ) :
    HasDerivAt (modBlockD Φ s l) (modBlockD2 Φ s l ξ) ξ := by
  -- the four pieces `s (deriv Φ)(s ·)`, `e (l ·)`, `Φ (s ·)`, `(2πi l) e (l ·)`
  have hA : HasDerivAt (fun y : ℝ => s * deriv Φ (s * y))
      (s * (s * iteratedDeriv 2 Φ (s * ξ))) ξ := by
    have h1 : HasDerivAt (fun y : ℝ => deriv Φ (s * y)) (s • iteratedDeriv 2 Φ (s * ξ)) ξ :=
      hasDerivAt_comp_const_mul (hΦd2 (s * ξ))
    simpa only [Complex.real_smul] using h1.const_mul (s : ℂ)
  have hB : HasDerivAt (fun y : ℝ => ee (l * y)) ((2 * ↑Real.pi * Complex.I * ↑l) * ee (l * ξ)) ξ :=
    hasDerivAt_ee_mul l ξ
  have hC : HasDerivAt (fun y : ℝ => Φ (s * y)) (s • deriv Φ (s * ξ)) ξ :=
    hasDerivAt_comp_const_mul (hΦd (s * ξ))
  have hD : HasDerivAt (fun y : ℝ => (2 * ↑Real.pi * Complex.I * ↑l) * ee (l * y))
      ((2 * ↑Real.pi * Complex.I * ↑l) * ((2 * ↑Real.pi * Complex.I * ↑l) * ee (l * ξ))) ξ :=
    hB.const_mul _
  have h0 : HasDerivAt (modBlockD Φ s l)
      ((s * (s * iteratedDeriv 2 Φ (s * ξ))) * ee (l * ξ)
        + (s * deriv Φ (s * ξ)) * ((2 * ↑Real.pi * Complex.I * ↑l) * ee (l * ξ))
        + ((s • deriv Φ (s * ξ)) * ((2 * ↑Real.pi * Complex.I * ↑l) * ee (l * ξ))
          + Φ (s * ξ) * ((2 * ↑Real.pi * Complex.I * ↑l)
              * ((2 * ↑Real.pi * Complex.I * ↑l) * ee (l * ξ))))) ξ := by
    unfold modBlockD
    exact (hA.mul hB).add (hC.mul hD)
  have hval : (s * (s * iteratedDeriv 2 Φ (s * ξ))) * ee (l * ξ)
        + (s * deriv Φ (s * ξ)) * ((2 * ↑Real.pi * Complex.I * ↑l) * ee (l * ξ))
        + ((s • deriv Φ (s * ξ)) * ((2 * ↑Real.pi * Complex.I * ↑l) * ee (l * ξ))
          + Φ (s * ξ) * ((2 * ↑Real.pi * Complex.I * ↑l)
              * ((2 * ↑Real.pi * Complex.I * ↑l) * ee (l * ξ)))) = modBlockD2 Φ s l ξ := by
    simp only [modBlockD2, Complex.real_smul]
    ring
  rwa [hval] at h0

/-- The finite difference symbol `∑_{n<K} ε n (modBlock σ_{n+1}, λ_{n+1} - modBlock σ_n, λ_n)` is
differentiable, with the derivative obtained by termwise differentiation;
and the same for the first derivative. -/
theorem lacModDiff_hasDerivAt {Φ : ℝ → ℂ} (hΦd : ∀ y : ℝ, HasDerivAt Φ (deriv Φ y) y)
    (hΦd2 : ∀ y : ℝ, HasDerivAt (deriv Φ) (iteratedDeriv 2 Φ y) y)
    (sigma lam : ℕ → ℝ) (eps : ℕ → ℂ) (K : ℕ) :
    (∀ ξ : ℝ, HasDerivAt (fun ξ : ℝ => ∑ n ∈ Finset.range K,
        eps n * (modBlock Φ (sigma (n + 1)) (lam (n + 1)) ξ - modBlock Φ (sigma n) (lam n) ξ))
      (∑ n ∈ Finset.range K,
        eps n * (modBlockD Φ (sigma (n + 1)) (lam (n + 1)) ξ - modBlockD Φ (sigma n) (lam n) ξ)) ξ) ∧
    (∀ ξ : ℝ, HasDerivAt (fun ξ : ℝ => ∑ n ∈ Finset.range K,
        eps n * (modBlockD Φ (sigma (n + 1)) (lam (n + 1)) ξ - modBlockD Φ (sigma n) (lam n) ξ))
      (∑ n ∈ Finset.range K,
        eps n * (modBlockD2 Φ (sigma (n + 1)) (lam (n + 1)) ξ - modBlockD2 Φ (sigma n) (lam n) ξ)) ξ) := by
  have hsum₁ : ∀ ξ : ℝ, HasDerivAt
      (fun ξ : ℝ => ∑ n ∈ Finset.range K,
        eps n * (modBlock Φ (sigma (n + 1)) (lam (n + 1)) ξ - modBlock Φ (sigma n) (lam n) ξ))
      (∑ n ∈ Finset.range K,
        eps n * (modBlockD Φ (sigma (n + 1)) (lam (n + 1)) ξ - modBlockD Φ (sigma n) (lam n) ξ)) ξ := by
    intro ξ
    have h : ∀ n ∈ Finset.range K, HasDerivAt
        (fun y : ℝ => eps n * (modBlock Φ (sigma (n + 1)) (lam (n + 1)) y
          - modBlock Φ (sigma n) (lam n) y))
        (eps n * (modBlockD Φ (sigma (n + 1)) (lam (n + 1)) ξ
          - modBlockD Φ (sigma n) (lam n) ξ)) ξ := by
      intro n _
      exact (((hasDerivAt_modBlock hΦd (sigma (n + 1)) (lam (n + 1)) ξ).sub
        (hasDerivAt_modBlock hΦd (sigma n) (lam n) ξ))).const_mul (eps n)
    have hfun : (fun ξ : ℝ => ∑ n ∈ Finset.range K, eps n *
          (modBlock Φ (sigma (n + 1)) (lam (n + 1)) ξ - modBlock Φ (sigma n) (lam n) ξ))
        = (∑ n ∈ Finset.range K, fun y : ℝ => eps n *
          (modBlock Φ (sigma (n + 1)) (lam (n + 1)) y - modBlock Φ (sigma n) (lam n) y)) := by
      funext ξ
      rw [Finset.sum_apply]
    rw [hfun]
    exact HasDerivAt.sum h
  have hsum₂ : ∀ ξ : ℝ, HasDerivAt
      (fun ξ : ℝ => ∑ n ∈ Finset.range K,
        eps n * (modBlockD Φ (sigma (n + 1)) (lam (n + 1)) ξ - modBlockD Φ (sigma n) (lam n) ξ))
      (∑ n ∈ Finset.range K,
        eps n * (modBlockD2 Φ (sigma (n + 1)) (lam (n + 1)) ξ - modBlockD2 Φ (sigma n) (lam n) ξ)) ξ := by
    intro ξ
    have h : ∀ n ∈ Finset.range K, HasDerivAt
        (fun y : ℝ => eps n * (modBlockD Φ (sigma (n + 1)) (lam (n + 1)) y
          - modBlockD Φ (sigma n) (lam n) y))
        (eps n * (modBlockD2 Φ (sigma (n + 1)) (lam (n + 1)) ξ
          - modBlockD2 Φ (sigma n) (lam n) ξ)) ξ := by
      intro n _
      exact (((hasDerivAt_modBlockD hΦd hΦd2 (sigma (n + 1)) (lam (n + 1)) ξ).sub
        (hasDerivAt_modBlockD hΦd hΦd2 (sigma n) (lam n) ξ))).const_mul (eps n)
    have hfun : (fun ξ : ℝ => ∑ n ∈ Finset.range K, eps n *
          (modBlockD Φ (sigma (n + 1)) (lam (n + 1)) ξ - modBlockD Φ (sigma n) (lam n) ξ))
        = (∑ n ∈ Finset.range K, fun y : ℝ => eps n *
          (modBlockD Φ (sigma (n + 1)) (lam (n + 1)) y - modBlockD Φ (sigma n) (lam n) y)) := by
      funext ξ
      rw [Finset.sum_apply]
    rw [hfun]
    exact HasDerivAt.sum h
  exact ⟨hsum₁, hsum₂⟩

end

end Work.KMTAreas.A7
