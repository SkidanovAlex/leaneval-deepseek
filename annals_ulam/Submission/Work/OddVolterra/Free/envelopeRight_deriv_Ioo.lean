import Mathlib
import Submission.Work.OddEnvelope.Smoothness.envelopeRight_deriv_Cinf

namespace Work.OddVolterra.Free

noncomputable section

open Set Filter
open scoped Topology ContDiff

/-- The derivative of the right branch of the envelope profile, on the general interval `(0,b)`
instead of `(0,1)`.

This is `Work.OddEnvelope.Smoothness.envelopeRight_deriv_Cinf`
(`Submission/Work/OddEnvelope/Smoothness/envelopeRight_deriv_Cinf.lean`, proved) with `1` replaced
by `b` in the surjectivity hypothesis and in the conclusion; the proof is a verbatim copy with
`Set.Ioo (0 : ℝ) 1` replaced by `Set.Ioo (0 : ℝ) b` (all its uses are pointwise). -/
theorem envelopeRight_deriv_Ioo {h y : ℝ → ℝ} {b : ℝ}
    (hy : ContDiffOn ℝ (↑(⊤ : ENat) : WithTop ENat) y (Set.Ioi 0))
    (hyd : ∀ s : ℝ, 0 < s → deriv y s < 0)
    (hh : ContDiffOn ℝ (↑(⊤ : ENat) : WithTop ENat) h (Set.Ioi 0))
    (hsurj : ∀ t ∈ Set.Ioo (0 : ℝ) b, ∃ σ : ℝ, 0 < σ ∧ y σ = t) :
    ∀ t ∈ Set.Ioo (0 : ℝ) b,
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

end Work.OddVolterra.Free
