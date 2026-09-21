import Mathlib
import Submission.Work.OddEnvelope.Defs

/-!
# The derivative of the right branch of the envelope profile (`C^∞` hypotheses)

Let `y : ℝ → ℝ` be `C^∞` on `(0,∞)` with `deriv y < 0` there, let `h` be `C^∞` on `(0,∞)`, and
assume that `y` maps `(0,∞)` onto `(0,1)`.  Then the right branch of the envelope profile

  `envelopeRight h y t = σ t * t + h (σ t)`,   where `σ t = slopeRight y t` is the unique
positive slope with `y (σ t) = t`,

is differentiable on `(0,1)` with derivative `kSlope h y (σ t)`, i.e.

  `deriv (envelopeRight h y) t = (y σ + σ y' σ + h' σ) / y' σ`  at `σ = σ t`.

The hypotheses here are `C^∞` on `(0,∞)` (the order `(↑(⊤ : ENat) : WithTop ENat)`), which is
what the structure `Work.OddEnvelope.IsEnvelopeCurve` supplies; this is the version consumed by
the odd-dimensional construction.

The proof is the classical inverse-function argument, and it is *strict*: `y` is strictly
antitone on `(0,∞)` (hence injective), so `slopeRight y` is a left inverse of `y` near `σ t`;
`ContDiffAt.hasStrictDerivAt` turns the smoothness of `y` at `σ t` into strict differentiability
there, and `HasStrictDerivAt.to_local_left_inverse` then gives

  `HasStrictDerivAt (slopeRight y) ((deriv y σ)⁻¹) t`.

The claim follows from the product and chain rules, together with the fact that
`envelopeRight h y = (σ ↦ σ * y σ + h σ) ∘ slopeRight y` near `t` (both factors are equal there
because `y (slopeRight y u) = u` for `u ∈ (0,1)`).
-/

namespace Work.OddEnvelope.Smoothness

noncomputable section

open Set Filter
open scoped Topology ContDiff

theorem envelopeRight_deriv_Cinf {h y : ℝ → ℝ}
    (hy : ContDiffOn ℝ (↑(⊤ : ENat) : WithTop ENat) y (Set.Ioi 0)) (hyd : ∀ s, 0 < s → deriv y s < 0)
    (hh : ContDiffOn ℝ (↑(⊤ : ENat) : WithTop ENat) h (Set.Ioi 0))
    (hsurj : ∀ t ∈ Set.Ioo (0 : ℝ) 1, ∃ σ, 0 < σ ∧ y σ = t) :
    ∀ t ∈ Set.Ioo (0 : ℝ) 1,
      deriv (Work.OddEnvelope.envelopeRight h y) t =
        Work.OddEnvelope.kSlope h y (Work.OddEnvelope.slopeRight y t) := by
  intro t ht
  obtain ⟨σ, hσpos, hσt⟩ := hsurj t ht
  -- `y` is strictly decreasing on `(0,∞)`, hence injective there.
  have hy_anti : StrictAntiOn y (Set.Ioi (0 : ℝ)) := by
    apply strictAntiOn_of_deriv_neg (convex_Ioi 0) hy.continuousOn
    intro x hx
    rw [interior_Ioi] at hx
    exact hyd x hx
  have hy_inj : Set.InjOn y (Set.Ioi (0 : ℝ)) := hy_anti.injOn
  -- `slopeRight y t` is the given preimage `σ`.
  have hst : Work.OddEnvelope.slopeRight y t = σ := by
    rw [← hσt]
    exact hy_inj.leftInvOn_invFunOn hσpos
  -- strict differentiability of `y` and `h` at `σ`
  have hyAt : ContDiffAt ℝ (↑(⊤ : ENat) : WithTop ENat) y σ :=
    hy.contDiffAt (isOpen_Ioi.mem_nhds hσpos)
  have hhAt : ContDiffAt ℝ (↑(⊤ : ENat) : WithTop ENat) h σ :=
    hh.contDiffAt (isOpen_Ioi.mem_nhds hσpos)
  have hn : (↑(⊤ : ENat) : WithTop ENat) ≠ 0 := by simp
  have hsd : HasStrictDerivAt y (deriv y σ) σ := hyAt.hasStrictDerivAt hn
  have hne : deriv y σ ≠ 0 := (hyd σ hσpos).ne
  -- `slopeRight y` is a left inverse of `y` near `σ`, hence has derivative `(deriv y σ)⁻¹` at `t`.
  have hg : ∀ᶠ x in 𝓝 σ, Work.OddEnvelope.slopeRight y (y x) = x := by
    filter_upwards [isOpen_Ioi.mem_nhds hσpos] with x hx
    exact hy_inj.leftInvOn_invFunOn hx
  have hslope_at : HasStrictDerivAt (Work.OddEnvelope.slopeRight y) ((deriv y σ)⁻¹) t := by
    have h := hsd.to_local_left_inverse hne hg
    rwa [hσt] at h
  -- the derivative of `σ ↦ σ * y σ + h σ` at `σ`
  have hy_deriv : HasDerivAt y (deriv y σ) σ := hsd.hasDerivAt
  have hh_deriv : HasDerivAt h (deriv h σ) σ := (hhAt.hasStrictDerivAt hn).hasDerivAt
  have hg_deriv : HasDerivAt (fun u : ℝ => u * y u + h u)
      (y σ + σ * deriv y σ + deriv h σ) σ := by
    have h1 : HasDerivAt (fun u : ℝ => u * y u) (1 * y σ + σ * deriv y σ) σ :=
      (hasDerivAt_id σ).mul hy_deriv
    have h2 : HasDerivAt (fun u : ℝ => u * y u + h u)
        ((1 * y σ + σ * deriv y σ) + deriv h σ) σ := h1.add hh_deriv
    simpa using h2
  have hg_deriv' : HasDerivAt (fun u : ℝ => u * y u + h u)
      (y σ + σ * deriv y σ + deriv h σ) (Work.OddEnvelope.slopeRight y t) := by
    rw [hst]; exact hg_deriv
  have hcomp := HasDerivAt.comp t hg_deriv' hslope_at.hasDerivAt
  -- `envelopeRight h y` agrees with `(σ ↦ σ * y σ + h σ) ∘ slopeRight y` near `t`
  have heq : Work.OddEnvelope.envelopeRight h y =ᶠ[𝓝 t]
      ((fun u : ℝ => u * y u + h u) ∘ Work.OddEnvelope.slopeRight y) := by
    filter_upwards [isOpen_Ioo.mem_nhds ht] with u hu
    have hsl : y (Work.OddEnvelope.slopeRight y u) = u := Function.invFunOn_eq (hsurj u hu)
    simp only [Function.comp_apply, Work.OddEnvelope.envelopeRight]
    rw [hsl]
  rw [heq.deriv_eq, hcomp.deriv, hst]
  simp only [Work.OddEnvelope.kSlope]
  rw [div_eq_mul_inv]

end

end Work.OddEnvelope.Smoothness
