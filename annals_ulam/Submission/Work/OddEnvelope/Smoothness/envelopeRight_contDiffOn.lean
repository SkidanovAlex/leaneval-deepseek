import Mathlib
import Submission.Work.OddEnvelope.Defs

/-!
# Smoothness of the right branch of the envelope profile

`envelopeRight h y t = σ t + h σ` where `σ = σ(t)` is the unique slope with `y σ = t`.  Since
`y` is strictly decreasing (hence injective) on `(0,∞)` and every `t ∈ (0,1)` has a positive
preimage under `y`, the map `t ↦ σ(t)` is the inverse of `y`, and it is smooth/analytic wherever
`deriv y ≠ 0`.  This file proves that `envelopeRight h y` is `C^ω` (equivalently, analytic) on
`(0,1)`.  (The order `⊤ : WithTop ENat` in the statement is `ω`, analyticity, since
`ω = ⊤ : WithTop ℕ∞`.)

The argument is the inverse function theorem for analytic functions: for `t₀ ∈ (0,1)` with
`σ₀ = σ(t₀) > 0`, the local inverse `L` of `y` at `σ₀` (which exists because `deriv y σ₀ ≠ 0`)
is analytic at `y σ₀ = t₀`; near `t₀` it is positive and hence coincides with `σ` by injectivity
of `y` on `(0,∞)`.  Therefore `envelopeRight h y = (σ ↦ σ * y σ + h σ) ∘ L` near `t₀` is
analytic at `t₀`.
-/

namespace Work.OddEnvelope.Smoothness

open Set Filter
open scoped Topology ContDiff

/-- The right branch `t ↦ σ t + h σ` of the envelope profile (with `y σ = t`) is `C^ω` on the
open interval `(0,1)`. -/
theorem envelopeRight_contDiffOn {h y : ℝ → ℝ}
    (hy : ContDiffOn ℝ (⊤ : WithTop ENat) y (Set.Ioi 0)) (hyd : ∀ s, 0 < s → deriv y s < 0)
    (hh : ContDiffOn ℝ (⊤ : WithTop ENat) h (Set.Ioi 0))
    (hsurj : ∀ t ∈ Set.Ioo (0 : ℝ) 1, ∃ σ, 0 < σ ∧ y σ = t) :
    ContDiffOn ℝ (⊤ : WithTop ENat) (Work.OddEnvelope.envelopeRight h y) (Set.Ioo (0 : ℝ) 1) := by
  -- `y` is strictly decreasing on `(0,∞)`, hence injective there.
  have hy_anti : StrictAntiOn y (Set.Ioi (0 : ℝ)) := by
    apply strictAntiOn_of_deriv_neg (convex_Ioi 0) hy.continuousOn
    intro x hx
    rw [interior_Ioi] at hx
    exact hyd x hx
  have hy_inj : Set.InjOn y (Set.Ioi (0 : ℝ)) := hy_anti.injOn
  -- The defining properties of `slopeRight y t` for `t ∈ (0,1)`.
  have hsl_mem : ∀ t ∈ Set.Ioo (0 : ℝ) 1, slopeRight y t ∈ Set.Ioi (0 : ℝ) :=
    fun t ht => Function.invFunOn_mem (hsurj t ht)
  have hsl_eq : ∀ t ∈ Set.Ioo (0 : ℝ) 1, y (slopeRight y t) = t :=
    fun t ht => Function.invFunOn_eq (hsurj t ht)
  -- Pointwise analyticity of the envelope.
  have hpoint : ∀ t₀ ∈ Set.Ioo (0 : ℝ) 1, AnalyticAt ℝ (envelopeRight h y) t₀ := by
    intro t₀ ht₀
    have hσ₀ : slopeRight y t₀ ∈ Set.Ioi (0 : ℝ) := hsl_mem t₀ ht₀
    have hyσ₀ : y (slopeRight y t₀) = t₀ := hsl_eq t₀ ht₀
    -- `y` is analytic at `σ₀`, with non-vanishing derivative
    have hyA : AnalyticAt ℝ y (slopeRight y t₀) :=
      (hy.analyticOn).analyticAt (isOpen_Ioi.mem_nhds hσ₀)
    have hne : deriv y (slopeRight y t₀) ≠ 0 := (hyd _ hσ₀).ne
    -- the local inverse `L` of `y` at `σ₀`
    let L : ℝ → ℝ :=
      hyA.hasStrictDerivAt.localInverse y (deriv y (slopeRight y t₀)) (slopeRight y t₀) hne
    have hLA : AnalyticAt ℝ L t₀ := by
      have h := hyA.analyticAt_localInverse hne
      rwa [hyσ₀] at h
    have hLt₀ : L t₀ = slopeRight y t₀ := by
      have h := HasStrictFDerivAt.localInverse_apply_image
        (hyA.hasStrictDerivAt.hasStrictFDerivAt_equiv hne)
      rw [hyσ₀] at h
      exact h
    have hLright : ∀ᶠ x in 𝓝 t₀, y (L x) = x := by
      have h := hyA.hasStrictDerivAt.eventually_right_inverse hne
      rw [hyσ₀] at h
      exact h
    have hLpos : ∀ᶠ x in 𝓝 t₀, 0 < L x := by
      have hmem : Set.Ioi (0 : ℝ) ∈ 𝓝 (L t₀) := by
        rw [hLt₀]; exact isOpen_Ioi.mem_nhds hσ₀
      exact hLA.continuousAt.eventually hmem
    -- the smooth/analytic expression `σ ↦ σ * y σ + h σ` composed with `L`
    have hgA : AnalyticAt ℝ (fun σ : ℝ => σ * y σ + h σ) (L t₀) := by
      have hyA' : AnalyticAt ℝ y (L t₀) := by rwa [hLt₀]
      have hhA : AnalyticAt ℝ h (L t₀) := by
        rw [hLt₀]
        exact (hh.analyticOn).analyticAt (isOpen_Ioi.mem_nhds hσ₀)
      exact (analyticAt_id.mul hyA').add hhA
    have hcomp : AnalyticAt ℝ ((fun σ : ℝ => σ * y σ + h σ) ∘ L) t₀ :=
      AnalyticAt.comp hgA hLA
    -- near `t₀`, `L` is positive and hence agrees with `slopeRight y`
    refine hcomp.congr ?_
    filter_upwards [hLright, hLpos, isOpen_Ioo.mem_nhds ht₀] with x hx_right hx_pos hx_Ioo
    have hsl : slopeRight y x = L x := by
      have h1 : L x ∈ Set.Ioi (0 : ℝ) := hx_pos
      have h2 : slopeRight y x ∈ Set.Ioi (0 : ℝ) := hsl_mem x hx_Ioo
      have h3 : y (L x) = y (slopeRight y x) := by rw [hx_right, hsl_eq x hx_Ioo]
      exact (hy_inj h1 h2 h3).symm
    simp only [Function.comp_apply, envelopeRight]
    rw [hsl, hx_right]
  -- conclude `ContDiffOn` (i.e. analyticity) on the open set `(0,1)`
  rw [contDiffOn_omega_iff_analyticOn (isOpen_Ioo.uniqueDiffOn)]
  intro t₀ ht₀
  exact (hpoint t₀ ht₀).analyticWithinAt

/-- **The `C^∞` (smooth) version of `envelopeRight_contDiffOn`.**

The statement of `envelopeRight_contDiffOn` is phrased with the order `⊤ : WithTop ENat`, which
is `ω`: analyticity.  In this workspace the chord-endpoint data is supplied by
`Work.OddEnvelope.IsEnvelopeCurve`, whose smoothness fields are stated with `∞` (finite infinity,
i.e. `C^∞`, smoothness) rather than with `ω`.  For consumers in that situation we record here the
same conclusion `ContDiffOn ℝ ∞` under `C^∞` hypotheses; it is proved by the same argument, with
the inverse function theorem for `C^n` maps (`ContDiffAt.to_localInverse`) in place of the
analytic one. -/
theorem envelopeRight_contDiffOn_smooth {h y : ℝ → ℝ}
    (hy : ContDiffOn ℝ ∞ y (Set.Ioi 0)) (hyd : ∀ s, 0 < s → deriv y s < 0)
    (hh : ContDiffOn ℝ ∞ h (Set.Ioi 0))
    (hsurj : ∀ t ∈ Set.Ioo (0 : ℝ) 1, ∃ σ, 0 < σ ∧ y σ = t) :
    ContDiffOn ℝ ∞ (Work.OddEnvelope.envelopeRight h y) (Set.Ioo (0 : ℝ) 1) := by
  have hy_anti : StrictAntiOn y (Set.Ioi (0 : ℝ)) := by
    apply strictAntiOn_of_deriv_neg (convex_Ioi 0) hy.continuousOn
    intro x hx
    rw [interior_Ioi] at hx
    exact hyd x hx
  have hy_inj : Set.InjOn y (Set.Ioi (0 : ℝ)) := hy_anti.injOn
  have hsl_mem : ∀ t ∈ Set.Ioo (0 : ℝ) 1, slopeRight y t ∈ Set.Ioi (0 : ℝ) :=
    fun t ht => Function.invFunOn_mem (hsurj t ht)
  have hsl_eq : ∀ t ∈ Set.Ioo (0 : ℝ) 1, y (slopeRight y t) = t :=
    fun t ht => Function.invFunOn_eq (hsurj t ht)
  have hpoint : ∀ t₀ ∈ Set.Ioo (0 : ℝ) 1, ContDiffAt ℝ ∞ (envelopeRight h y) t₀ := by
    intro t₀ ht₀
    have hσ₀ : slopeRight y t₀ ∈ Set.Ioi (0 : ℝ) := hsl_mem t₀ ht₀
    have hyσ₀ : y (slopeRight y t₀) = t₀ := hsl_eq t₀ ht₀
    have hyAt : ContDiffAt ℝ ∞ y (slopeRight y t₀) := hy.contDiffAt (isOpen_Ioi.mem_nhds hσ₀)
    have hn : (∞ : WithTop ENat) ≠ 0 := by simp
    have hsd : HasStrictDerivAt y (deriv y (slopeRight y t₀)) (slopeRight y t₀) :=
      hyAt.hasStrictDerivAt hn
    have hne : deriv y (slopeRight y t₀) ≠ 0 := (hyd _ hσ₀).ne
    let f' : ℝ ≃L[ℝ] ℝ :=
      ContinuousLinearEquiv.unitsEquivAut ℝ (Units.mk0 (deriv y (slopeRight y t₀)) hne)
    have hf' : HasFDerivAt y (f' : ℝ →L[ℝ] ℝ) (slopeRight y t₀) :=
      (hsd.hasStrictFDerivAt_equiv hne).hasFDerivAt
    let L : ℝ → ℝ := hyAt.localInverse hf' hn
    have hLcont : ContDiffAt ℝ ∞ L t₀ := by
      have h := hyAt.to_localInverse hf' hn
      rwa [hyσ₀] at h
    have hLt₀ : L t₀ = slopeRight y t₀ := by
      have h := hyAt.localInverse_apply_image hf' hn
      rwa [hyσ₀] at h
    have hLright : ∀ᶠ x in 𝓝 t₀, y (L x) = x := by
      have h := HasStrictFDerivAt.eventually_right_inverse (hyAt.hasStrictFDerivAt' hf' hn)
      rwa [hyσ₀] at h
    have hLpos : ∀ᶠ x in 𝓝 t₀, 0 < L x := by
      have hmem : Set.Ioi (0 : ℝ) ∈ 𝓝 (L t₀) := by
        rw [hLt₀]; exact isOpen_Ioi.mem_nhds hσ₀
      exact hLcont.continuousAt.eventually hmem
    have hgA : ContDiffAt ℝ ∞ (fun σ : ℝ => σ * y σ + h σ) (L t₀) := by
      have hyA' : ContDiffAt ℝ ∞ y (L t₀) := by rwa [hLt₀]
      have hhA : ContDiffAt ℝ ∞ h (L t₀) := by
        rw [hLt₀]
        exact hh.contDiffAt (isOpen_Ioi.mem_nhds hσ₀)
      exact (contDiffAt_id.mul hyA').add hhA
    have hcomp : ContDiffAt ℝ ∞ ((fun σ : ℝ => σ * y σ + h σ) ∘ L) t₀ :=
      ContDiffAt.comp t₀ hgA hLcont
    refine hcomp.congr_of_eventuallyEq ?_
    filter_upwards [hLright, hLpos, isOpen_Ioo.mem_nhds ht₀] with x hx_right hx_pos hx_Ioo
    have hsl : slopeRight y x = L x := by
      have h1 : L x ∈ Set.Ioi (0 : ℝ) := hx_pos
      have h2 : slopeRight y x ∈ Set.Ioi (0 : ℝ) := hsl_mem x hx_Ioo
      have h3 : y (L x) = y (slopeRight y x) := by rw [hx_right, hsl_eq x hx_Ioo]
      exact (hy_inj h1 h2 h3).symm
    simp only [Function.comp_apply, envelopeRight]
    rw [hsl, hx_right]
  intro t₀ ht₀
  exact (hpoint t₀ ht₀).mono (subset_univ _)

end Work.OddEnvelope.Smoothness
