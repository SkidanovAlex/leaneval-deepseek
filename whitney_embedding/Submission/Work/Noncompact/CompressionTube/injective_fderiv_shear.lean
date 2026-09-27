import Mathlib

/-!
# The shear `(u, s) ↦ (u, (1 - χ u) * s + χ u * g s)` has injective derivative

This file proves `Work.Noncompact.CompressionTube.injective_fderiv_shear`: for a smooth
`χ : E → ℝ` with `0 ≤ χ ≤ 1` and a smooth `g : ℝ → ℝ` with everywhere positive derivative,
the shear

`F (u, s) = (u, (1 - χ u) * s + χ u * g s)`

has injective Fréchet derivative at every point.

Writing `p = (x, t)`, the derivative of `F` at `p` is the continuous linear map

`(h, s) ↦ (h, ((1 - χ x) + χ x * deriv g t) * s + (g t - t) * dχ(x)(h))`,

whose "vertical" coefficient `(1 - χ x) + χ x * deriv g t` is positive: it is a convex
combination of the positive numbers `1` and `deriv g t` (`χ x ∈ [0, 1]`).  Hence the kernel of
the derivative is trivial.

This is the "immersion" half of the immersion statement for the shear used in the construction
of the compression of the domain (`Work.Noncompact.CompressionTube`): the shear is used to push
the tube of a point of `B` past the bounded level `L`, and the fact that it is an immersion is
one of the three properties (`smooth`, `injective`, `immersion`) that a compression must have.
-/

namespace Work.Noncompact.CompressionTube

/-- **The derivative of the shear is injective, pointwise form.**

The Fréchet derivative at `(x, t)` of `(u, s) ↦ (u, (1 - χ u) * s + χ u * g s)` is the
continuous linear map with block form

`(h, s) ↦ (h, ((1 - χ x) + χ x * deriv g t) * s + (g t - t) * dχ(x)(h))`;

its second block is diagonal with the positive entry `(1 - χ x) + χ x * deriv g t`, so the
kernel is trivial. -/
private lemma shear_fderiv_injective {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (χ : E → ℝ) (g : ℝ → ℝ) (hχ0 : ∀ u : E, 0 ≤ χ u) (hχ1 : ∀ u : E, χ u ≤ 1)
    (hg' : ∀ s : ℝ, 0 < deriv g s) (x : E) (t : ℝ) :
    Function.Injective ((ContinuousLinearMap.fst ℝ E ℝ).prod
      (((1 - χ x) • (ContinuousLinearMap.snd ℝ E ℝ)
        + t • (-((fderiv ℝ χ x) ∘SL (ContinuousLinearMap.fst ℝ E ℝ))))
       + (χ x • ((fderiv ℝ g t) ∘SL (ContinuousLinearMap.snd ℝ E ℝ))
        + g t • ((fderiv ℝ χ x) ∘SL (ContinuousLinearMap.fst ℝ E ℝ))))) := by
  -- name the derivative and compute its value on the vertical vector `(0, 1)`
  set ψ : (E × ℝ) →L[ℝ] ℝ :=
      (((1 - χ x) • (ContinuousLinearMap.snd ℝ E ℝ)
        + t • (-((fderiv ℝ χ x) ∘SL (ContinuousLinearMap.fst ℝ E ℝ))))
       + (χ x • ((fderiv ℝ g t) ∘SL (ContinuousLinearMap.snd ℝ E ℝ))
        + g t • ((fderiv ℝ χ x) ∘SL (ContinuousLinearMap.fst ℝ E ℝ)))) with hψ
  have hψ01 : ψ ((0 : E), (1 : ℝ)) = (1 - χ x) + χ x * deriv g t := by
    rw [hψ]
    simp
  -- the vertical entry is positive
  have hpos : 0 < (1 - χ x) + χ x * deriv g t := by
    rcases lt_or_eq_of_le (hχ1 x) with h | h
    · have h1 : 0 < 1 - χ x := by linarith
      have h2 : 0 ≤ χ x * deriv g t := mul_nonneg (hχ0 x) (le_of_lt (hg' t))
      linarith
    · rw [h]
      simpa using hg' t
  intro v w hvw
  -- the kernel of `fst.prod ψ` is trivial
  have key : ∀ u : E × ℝ, ((ContinuousLinearMap.fst ℝ E ℝ).prod ψ) u = 0 → u = 0 := by
    intro u hu
    have hufst : u.1 = 0 := by
      have := congrArg Prod.fst hu
      simpa using this
    have huψ : ψ u = 0 := by
      have := congrArg Prod.snd hu
      simpa using this
    have hu_eq : u = u.2 • ((0 : E), (1 : ℝ)) := by
      ext <;> simp [hufst]
    have h2 : u.2 * ψ ((0 : E), (1 : ℝ)) = 0 := by
      rw [← smul_eq_mul, ← map_smul, ← hu_eq]
      exact huψ
    rw [hψ01] at h2
    have hu2 : u.2 = 0 := (mul_eq_zero.mp h2).resolve_right (ne_of_gt hpos)
    ext <;> simp [hufst, hu2]
  have hzer : ((ContinuousLinearMap.fst ℝ E ℝ).prod ψ) (v - w) = 0 := by
    rw [map_sub, hvw, sub_self]
  exact sub_eq_zero.mp (key (v - w) hzer)

theorem injective_fderiv_shear {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (χ : E → ℝ) (g : ℝ → ℝ) (hχd : ContDiff ℝ ((⊤ : ℕ∞)) χ) (hgd : ContDiff ℝ ((⊤ : ℕ∞)) g)
    (hχ0 : ∀ u : E, 0 ≤ χ u) (hχ1 : ∀ u : E, χ u ≤ 1) (hg' : ∀ s : ℝ, 0 < deriv g s) :
    ∀ p : E × ℝ, Function.Injective
      (fderiv ℝ (fun q : E × ℝ => (q.1, (1 - χ q.1) * q.2 + χ q.1 * g q.2)) p) := by
  intro p
  -- differentiability of the ingredients
  have hχ_diff : DifferentiableAt ℝ χ p.1 := (hχd.differentiable (by decide)).differentiableAt
  have hg_diff : DifferentiableAt ℝ g p.2 := (hgd.differentiable (by decide)).differentiableAt
  have hχfst : HasFDerivAt (fun q : E × ℝ => χ q.1)
      ((fderiv ℝ χ p.1) ∘SL (ContinuousLinearMap.fst ℝ E ℝ)) p :=
    (hχ_diff.hasFDerivAt).comp p (ContinuousLinearMap.fst ℝ E ℝ).hasFDerivAt
  have hgcomp : HasFDerivAt (fun q : E × ℝ => g q.2)
      ((fderiv ℝ g p.2) ∘SL (ContinuousLinearMap.snd ℝ E ℝ)) p :=
    (hg_diff.hasFDerivAt).comp p (ContinuousLinearMap.snd ℝ E ℝ).hasFDerivAt
  have h1 : HasFDerivAt (fun q : E × ℝ => 1 - χ q.1)
      (-((fderiv ℝ χ p.1) ∘SL (ContinuousLinearMap.fst ℝ E ℝ))) p :=
    hχfst.const_sub 1
  have hsnd : HasFDerivAt (fun q : E × ℝ => q.2) (ContinuousLinearMap.snd ℝ E ℝ) p :=
    (ContinuousLinearMap.snd ℝ E ℝ).hasFDerivAt
  have hφ1 : HasFDerivAt (fun q : E × ℝ => (1 - χ q.1) * q.2)
      ((1 - χ p.1) • (ContinuousLinearMap.snd ℝ E ℝ)
        + p.2 • (-((fderiv ℝ χ p.1) ∘SL (ContinuousLinearMap.fst ℝ E ℝ)))) p :=
    h1.mul hsnd
  have hφ2 : HasFDerivAt (fun q : E × ℝ => χ q.1 * g q.2)
      (χ p.1 • ((fderiv ℝ g p.2) ∘SL (ContinuousLinearMap.snd ℝ E ℝ))
        + g p.2 • ((fderiv ℝ χ p.1) ∘SL (ContinuousLinearMap.fst ℝ E ℝ))) p :=
    hχfst.mul hgcomp
  have hφ : HasFDerivAt (fun q : E × ℝ => (1 - χ q.1) * q.2 + χ q.1 * g q.2)
      (((1 - χ p.1) • (ContinuousLinearMap.snd ℝ E ℝ)
        + p.2 • (-((fderiv ℝ χ p.1) ∘SL (ContinuousLinearMap.fst ℝ E ℝ))))
       + (χ p.1 • ((fderiv ℝ g p.2) ∘SL (ContinuousLinearMap.snd ℝ E ℝ))
        + g p.2 • ((fderiv ℝ χ p.1) ∘SL (ContinuousLinearMap.fst ℝ E ℝ)))) p :=
    hφ1.add hφ2
  -- the full derivative, through the product rule
  have hF : HasFDerivAt (fun q : E × ℝ => (q.1, (1 - χ q.1) * q.2 + χ q.1 * g q.2))
      ((ContinuousLinearMap.fst ℝ E ℝ).prod
        (((1 - χ p.1) • (ContinuousLinearMap.snd ℝ E ℝ)
          + p.2 • (-((fderiv ℝ χ p.1) ∘SL (ContinuousLinearMap.fst ℝ E ℝ))))
         + (χ p.1 • ((fderiv ℝ g p.2) ∘SL (ContinuousLinearMap.snd ℝ E ℝ))
          + g p.2 • ((fderiv ℝ χ p.1) ∘SL (ContinuousLinearMap.fst ℝ E ℝ))))) p :=
    (ContinuousLinearMap.fst ℝ E ℝ).hasFDerivAt.prodMk hφ
  rw [hF.fderiv]
  exact shear_fderiv_injective χ g hχ0 hχ1 hg' p.1 p.2

end Work.Noncompact.CompressionTube
