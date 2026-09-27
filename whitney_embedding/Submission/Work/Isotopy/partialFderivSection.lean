import Mathlib

/-!
# The partial derivative of a two-variable map vs. the derivative of its section

`Work.Isotopy.exists_localInverse_param` takes as its hypothesis the injectivity of the *partial*
derivative of `G : ℝ × E → F` at a base point `(s₀,p)`, namely of
`v ↦ fderiv ℝ G (s₀,p) (0, v)`.  The natural hypothesis available in geometric applications is
instead the injectivity of the derivative of the *section* `x ↦ G (s₀, x)` at `p`.

This file records, standalone and in general form, that the two are the same map:

* `fderiv_section_eq` — `(fun v => fderiv ℝ G (s₀,p) (0,v)) = fderiv ℝ (fun x => G (s₀,x)) p`
  (chain rule with the section `x ↦ (s₀,x)`, whose derivative is `ContinuousLinearMap.inr`);
* `injective_partial_of_section` — hence injectivity transfers in the direction needed.

This is the general form of `Work.Whitney.CutPush.slice_partial_fderiv`
(`CutPush/slice_graph.lean`), where the same computation was carried out for a particular `G`
(a projected family of slices) at the particular base point `0`; it is kept here so that the arc
family can be fed to `exists_localInverse_param` without importing the slice chapter.
-/

namespace Work.Isotopy

/-- **The partial derivative in the second variable is the derivative of the section.** -/
theorem fderiv_section_eq {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (G : ℝ × E → F) (s₀ : ℝ) (p : E) (hG : DifferentiableAt ℝ G (s₀, p)) :
    (fun v : E => fderiv ℝ G (s₀, p) (0, v)) = fderiv ℝ (fun x : E => G (s₀, x)) p := by
  have h1 : HasFDerivAt (fun x : E => (s₀, x)) (ContinuousLinearMap.inr ℝ ℝ E) p :=
    hasFDerivAt_prodMk_right (𝕜 := ℝ) s₀ p
  have h3 : HasFDerivAt (fun x : E => G (s₀, x))
      ((fderiv ℝ G (s₀, p)).comp (ContinuousLinearMap.inr ℝ ℝ E)) p :=
    hG.hasFDerivAt.comp p h1
  funext v
  rw [h3.fderiv]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.inr_apply]

/-- **Injectivity of the section derivative transfers to the partial derivative** — the direction in
which the hypothesis of `exists_localInverse_param` is discharged from a regularity hypothesis on the
section. -/
theorem injective_partial_of_section {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (G : ℝ × E → F) (s₀ : ℝ) (p : E) (hG : DifferentiableAt ℝ G (s₀, p))
    (h : Function.Injective (fderiv ℝ (fun x : E => G (s₀, x)) p)) :
    Function.Injective (fun v : E => fderiv ℝ G (s₀, p) (0, v)) := by
  intro u v huv
  apply h
  rw [← congrFun (fderiv_section_eq G s₀ p hG) u, ← congrFun (fderiv_section_eq G s₀ p hG) v]
  exact huv

/-- **Nonvanishing of the second partial derivative from nonvanishing of the section derivative** —
the form in which a *regular* family of arcs (`‖fderiv (Φ lam) t‖ ≠ 0`) feeds
`exists_localInverse_param` when the ambient space is one-dimensional. -/
theorem partial_apply_one_ne_zero_of_section {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (G : ℝ × ℝ → E) (s₀ x₀ : ℝ) (hG : DifferentiableAt ℝ G (s₀, x₀))
    (h : fderiv ℝ (fun x : ℝ => G (s₀, x)) x₀ 1 ≠ 0) :
    fderiv ℝ G (s₀, x₀) (0, 1) ≠ 0 := by
  have h2 := congrFun (fderiv_section_eq G s₀ x₀ hG) 1
  rw [h2]
  exact h


/-! ## Binder order (frozen), and the trail-point data for `exists_localInverse_param`

**Convention.**  For a lemma about a map at a point the binders are, in this order: the map, then the
*point/parameter data*, then the hypotheses — and every hypothesis's type mentions only binders that
come before it (Lean enforces the latter; the convention keeps it from being violated by accident, and
freezes the explicit-argument order of every call site).  Concretely:
`(G : ℝ × E → F) (s₀ : ℝ) (p : E) (hG : DifferentiableAt ℝ G (s₀, p))`, never
`(G) (hG : … (s₀,p)) (s₀) (p)`.
-/


/-- **Joint smoothness gives differentiability at every trail point.** -/
theorem differentiableAt_uncurry {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (Φ : ℝ → ℝ → E) (hΦ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Function.uncurry Φ))
    (s₀ x₀ : ℝ) : DifferentiableAt ℝ (Function.uncurry Φ) (s₀, x₀) :=
  hΦ.differentiable (by simp) (s₀, x₀)

/-- **A linear functional on `ℝ` that does not vanish at `1` is injective.** -/
theorem injective_of_apply_one_ne_zero {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : ℝ →L[ℝ] E) (h : f 1 ≠ 0) : Function.Injective f := by
  intro x y hxy
  have h1 : f (x - y) = 0 := by rw [map_sub, hxy, sub_self]
  have h2 : (x - y) • f 1 = 0 := by
    rw [← map_smul]
    simpa using h1
  have h3 : x - y = 0 := by
    rcases smul_eq_zero.mp h2 with h' | h'
    · exact h'
    · exact absurd h' h
  exact sub_eq_zero.mp h3

/-- **The partial derivative of a jointly smooth family, along the source direction, does not
vanish** — the form in which `himm` (`fderiv ℝ (Φ lam) t 1 ≠ 0` on the trail) discharges the
regularity hypothesis of `exists_localInverse_param` at a point of the trail box. -/
theorem partial_apply_one_ne_zero_uncurry {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (Φ : ℝ → ℝ → E) (hΦ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Function.uncurry Φ))
    (s₀ x₀ : ℝ) (h : fderiv ℝ (fun x : ℝ => Φ s₀ x) x₀ 1 ≠ 0) :
    fderiv ℝ (Function.uncurry Φ) (s₀, x₀) (0, 1) ≠ 0 := by
  have h1 : (fun v : ℝ => fderiv ℝ (Function.uncurry Φ) (s₀, x₀) (0, v))
      = fderiv ℝ (fun x : ℝ => (Function.uncurry Φ) (s₀, x)) x₀ :=
    fderiv_section_eq (Function.uncurry Φ) s₀ x₀
      (differentiableAt_uncurry Φ hΦ s₀ x₀)
  rw [congrFun h1 1]
  simpa using h

/-- **The injectivity hypothesis of `exists_localInverse_param`**, discharged from the regularity of
the family on the trail: with `Φ lam` regular at `t`, the partial derivative
`v ↦ fderiv ℝ (Function.uncurry Φ) (lam, t) (0, v)` of `ℝ` to the target is injective. -/
theorem injective_partial_uncurry {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (Φ : ℝ → ℝ → E) (hΦ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Function.uncurry Φ))
    (s₀ x₀ : ℝ) (h : fderiv ℝ (fun x : ℝ => Φ s₀ x) x₀ 1 ≠ 0) :
    Function.Injective (fun v : ℝ => fderiv ℝ (Function.uncurry Φ) (s₀, x₀) (0, v)) := by
  have h1 : (fun v : ℝ => fderiv ℝ (Function.uncurry Φ) (s₀, x₀) (0, v))
      = fderiv ℝ (fun x : ℝ => (Function.uncurry Φ) (s₀, x)) x₀ :=
    fderiv_section_eq (Function.uncurry Φ) s₀ x₀
      (differentiableAt_uncurry Φ hΦ s₀ x₀)
  rw [h1]
  exact injective_of_apply_one_ne_zero _ (by simpa using h)

end Work.Isotopy
