import Mathlib
import Submission.Work.OddEnvelope.Smoothness.envelopeRight_contDiffOn

namespace Work.OddVolterra.Free

open Set Filter
open scoped Topology ContDiff

/-- Smoothness (C^ω) of the right branch of the envelope profile on the general interval `(0,b)`
instead of `(0,1)`.

This is `Work.OddEnvelope.Smoothness.envelopeRight_contDiffOn`
(`Submission/Work/OddEnvelope/Smoothness/envelopeRight_contDiffOn.lean`, proved) with `1` replaced
by `b` in the surjectivity hypothesis and in the conclusion; the proof is a verbatim copy with
`Set.Ioo (0 : ℝ) 1` replaced by `Set.Ioo (0 : ℝ) b` (the inverse-function argument is pointwise).
Consumers downgrade along `ContDiffOn.of_le` to obtain `ContDiffOn ℝ 1`. -/
theorem envelopeRight_contDiffOn_Ioo {h y : ℝ → ℝ} {b : ℝ}
    (hy : ContDiffOn ℝ (↑(⊤ : ENat) : WithTop ENat) y (Set.Ioi 0))
    (hyd : ∀ s : ℝ, 0 < s → deriv y s < 0)
    (hh : ContDiffOn ℝ (↑(⊤ : ENat) : WithTop ENat) h (Set.Ioi 0))
    (hsurj : ∀ t ∈ Set.Ioo (0 : ℝ) b, ∃ σ : ℝ, 0 < σ ∧ y σ = t) :
    ContDiffOn ℝ (↑(⊤ : ENat) : WithTop ENat) (Work.OddEnvelope.envelopeRight h y)
      (Set.Ioo (0 : ℝ) b) := by
  have hy_anti : StrictAntiOn y (Set.Ioi (0 : ℝ)) := by
    apply strictAntiOn_of_deriv_neg (convex_Ioi 0) hy.continuousOn
    intro x hx
    rw [interior_Ioi] at hx
    exact hyd x hx
  have hy_inj : Set.InjOn y (Set.Ioi (0 : ℝ)) := hy_anti.injOn
  have hsl_mem : ∀ t ∈ Set.Ioo (0 : ℝ) b, Work.OddEnvelope.slopeRight y t ∈ Set.Ioi (0 : ℝ) :=
    fun t ht => Function.invFunOn_mem (hsurj t ht)
  have hsl_eq : ∀ t ∈ Set.Ioo (0 : ℝ) b, y (Work.OddEnvelope.slopeRight y t) = t :=
    fun t ht => Function.invFunOn_eq (hsurj t ht)
  have hpoint : ∀ t₀ ∈ Set.Ioo (0 : ℝ) b,
      ContDiffAt ℝ (∞ : WithTop ENat) (Work.OddEnvelope.envelopeRight h y) t₀ := by
    intro t₀ ht₀
    have hσ₀ : Work.OddEnvelope.slopeRight y t₀ ∈ Set.Ioi (0 : ℝ) := hsl_mem t₀ ht₀
    have hyσ₀ : y (Work.OddEnvelope.slopeRight y t₀) = t₀ := hsl_eq t₀ ht₀
    have hyAt : ContDiffAt ℝ (∞ : WithTop ENat) y (Work.OddEnvelope.slopeRight y t₀) :=
      hy.contDiffAt (isOpen_Ioi.mem_nhds hσ₀)
    have hn : ((∞ : WithTop ENat)) ≠ 0 := by simp
    have hsd : HasStrictDerivAt y (deriv y (Work.OddEnvelope.slopeRight y t₀))
        (Work.OddEnvelope.slopeRight y t₀) :=
      hyAt.hasStrictDerivAt hn
    have hne : deriv y (Work.OddEnvelope.slopeRight y t₀) ≠ 0 := (hyd _ hσ₀).ne
    let f' : ℝ ≃L[ℝ] ℝ :=
      ContinuousLinearEquiv.unitsEquivAut ℝ
        (Units.mk0 (deriv y (Work.OddEnvelope.slopeRight y t₀)) hne)
    have hf' : HasFDerivAt y (f' : ℝ →L[ℝ] ℝ) (Work.OddEnvelope.slopeRight y t₀) :=
      (hsd.hasStrictFDerivAt_equiv hne).hasFDerivAt
    let L : ℝ → ℝ := hyAt.localInverse hf' hn
    have hLcont : ContDiffAt ℝ (∞ : WithTop ENat) L t₀ := by
      have h := hyAt.to_localInverse hf' hn
      rwa [hyσ₀] at h
    have hLt₀ : L t₀ = Work.OddEnvelope.slopeRight y t₀ := by
      have h := hyAt.localInverse_apply_image hf' hn
      rwa [hyσ₀] at h
    have hLright : ∀ᶠ x in 𝓝 t₀, y (L x) = x := by
      have h := HasStrictFDerivAt.eventually_right_inverse (hyAt.hasStrictFDerivAt' hf' hn)
      rwa [hyσ₀] at h
    have hLpos : ∀ᶠ x in 𝓝 t₀, 0 < L x := by
      have hmem : Set.Ioi (0 : ℝ) ∈ 𝓝 (L t₀) := by
        rw [hLt₀]; exact isOpen_Ioi.mem_nhds hσ₀
      exact hLcont.continuousAt.eventually hmem
    have hgA : ContDiffAt ℝ (∞ : WithTop ENat) (fun σ : ℝ => σ * y σ + h σ) (L t₀) := by
      have hyA' : ContDiffAt ℝ (∞ : WithTop ENat) y (L t₀) := by rwa [hLt₀]
      have hhA : ContDiffAt ℝ (∞ : WithTop ENat) h (L t₀) := by
        rw [hLt₀]
        exact hh.contDiffAt (isOpen_Ioi.mem_nhds hσ₀)
      exact (contDiffAt_id.mul hyA').add hhA
    have hcomp : ContDiffAt ℝ (∞ : WithTop ENat)
        ((fun σ : ℝ => σ * y σ + h σ) ∘ L) t₀ :=
      ContDiffAt.comp t₀ hgA hLcont
    refine hcomp.congr_of_eventuallyEq ?_
    filter_upwards [hLright, hLpos, isOpen_Ioo.mem_nhds ht₀] with x hx_right hx_pos hx_Ioo
    have hsl : Work.OddEnvelope.slopeRight y x = L x := by
      have h1 : L x ∈ Set.Ioi (0 : ℝ) := hx_pos
      have h2 : Work.OddEnvelope.slopeRight y x ∈ Set.Ioi (0 : ℝ) := hsl_mem x hx_Ioo
      have h3 : y (L x) = y (Work.OddEnvelope.slopeRight y x) := by
        rw [hx_right, hsl_eq x hx_Ioo]
      exact (hy_inj h1 h2 h3).symm
    simp only [Function.comp_apply, Work.OddEnvelope.envelopeRight]
    rw [hsl, hx_right]
  intro t₀ ht₀
  exact (hpoint t₀ ht₀).mono (subset_univ _)

end Work.OddVolterra.Free
