import Mathlib
import Submission.Work.FatouParabolic.Core.Defs
import Submission.Work.FatouParabolic.Core.exists_flowerImageFix
import Submission.Work.ELRig.deriv_ne_zero_of_injOn

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.FatouParabolic.Core

open Set Filter
open scoped Topology

/-- **The inverse branch of the Fatou coordinate on the tail of a horizontal strip.**

Given a Leau–Fatou flower `fl` at a parabolic fixed point together with its petal image property
(the image of the petal under `φa` exhausts the tail of every horizontal strip), and given a height
`B > 0`, there is a horizontal level `C` and a *right inverse* `Ψ₀` of `fl.φa` on the strip tail
`{τ | C < τ.re, |τ.im| < B}`: `Ψ₀ τ` lies in the petal, `fl.φa (Ψ₀ τ) = τ`, `Ψ₀` is equivariant for
the dynamics (`F (Ψ₀ τ) = Ψ₀ (τ + 1)`) and is complex differentiable at `τ`.

`Ψ₀` is the local inverse of the injective holomorphic map `fl.φa` on the (open) petal; the
equivariance is forced because both `F (Ψ₀ τ)` and `Ψ₀ (τ + 1)` lie in the petal and have the same
`φa`-value `τ + 1` (the Abel equation `fl.φa_shift`), and `fl.φa` is injective on `Pa`. -/
theorem exists_petalInverse {F g : ℂ → ℂ} {z₀ : ℂ}
    (fl : Work.FatouParabolic.FlowerImageFix F g z₀) (hF : Differentiable ℂ F) {B : ℝ} (hB : 0 < B) :
    ∃ C : ℝ, ∃ Ψ₀ : ℂ → ℂ, ∀ τ : ℂ, C < τ.re → |τ.im| < B →
      Ψ₀ τ ∈ fl.Pa ∧ fl.φa (Ψ₀ τ) = τ ∧ F (Ψ₀ τ) = Ψ₀ (τ + 1) ∧ DifferentiableAt ℂ Ψ₀ τ := by
  obtain ⟨C, hC⟩ := fl.image_strip B (le_of_lt hB)
  let Ψ₀ : ℂ → ℂ := fun τ =>
    if h : C < τ.re ∧ |τ.im| < B then Classical.choose (hC τ h.1 (le_of_lt h.2)) else 0
  have hspec : ∀ τ : ℂ, (C < τ.re ∧ |τ.im| < B) →
      Ψ₀ τ ∈ fl.Pa ∧ fl.φa (Ψ₀ τ) = τ := by
    intro τ h
    have hveq : Ψ₀ τ = Classical.choose (hC τ h.1 (le_of_lt h.2)) := by
      simp only [Ψ₀]
      exact dite_eq_left h
    obtain ⟨hz, hφ⟩ := Classical.choose_spec (hC τ h.1 (le_of_lt h.2))
    rw [hveq]
    exact ⟨hz, hφ⟩
  refine ⟨C, Ψ₀, ?_⟩
  intro τ hτ hτB
  have hτS : C < τ.re ∧ |τ.im| < B := ⟨hτ, hτB⟩
  have hτS' : C < (τ + 1).re ∧ |(τ + 1).im| < B :=
    ⟨by simp only [Complex.add_re, Complex.one_re]; linarith, by simpa using hτB⟩
  obtain ⟨hzmem, hzφ⟩ := hspec τ hτS
  obtain ⟨hz1mem, hz1φ⟩ := hspec (τ + 1) hτS'
  have hmaps : F (Ψ₀ τ) ∈ fl.Pa := fl.mapsTo_Pa hzmem
  have habel : fl.φa (F (Ψ₀ τ)) = fl.φa (Ψ₀ τ) + 1 := fl.φa_shift (Ψ₀ τ) hzmem
  have heqφ : fl.φa (F (Ψ₀ τ)) = fl.φa (Ψ₀ (τ + 1)) := by rw [habel, hzφ, hz1φ]
  have heqF : F (Ψ₀ τ) = Ψ₀ (τ + 1) := fl.φa_fatou.2 hmaps hz1mem heqφ
  refine ⟨hzmem, hzφ, heqF, ?_⟩
  -- differentiability of the local inverse of `φa`
  have hopen : IsOpen fl.Pa := fl.isOpen_Pa
  have hmem_nhds : fl.Pa ∈ 𝓝 (Ψ₀ τ) := hopen.mem_nhds hzmem
  have hdiffOn : DifferentiableOn ℂ fl.φa fl.Pa := fl.φa_fatou.1.2.1
  have hdat : DifferentiableAt ℂ fl.φa (Ψ₀ τ) := hdiffOn.differentiableAt hmem_nhds
  have han : AnalyticAt ℂ fl.φa (Ψ₀ τ) :=
    (hdiffOn.analyticOn hopen).analyticAt hmem_nhds
  have hsd : HasStrictDerivAt fl.φa (deriv fl.φa (Ψ₀ τ)) (Ψ₀ τ) := han.hasStrictDerivAt
  have hne : deriv fl.φa (Ψ₀ τ) ≠ 0 :=
    Work.ELRig.deriv_ne_zero_of_injOn hdiffOn hopen fl.φa_fatou.2 hzmem
  have hev : ∀ᶠ x in 𝓝 (Ψ₀ τ), Ψ₀ (fl.φa x) = x := by
    have hcont : ContinuousAt fl.φa (Ψ₀ τ) := hdat.continuousAt
    have hS1 : ∀ᶠ x in 𝓝 (Ψ₀ τ), C < (fl.φa x).re :=
      (Complex.continuous_re.continuousAt.comp hcont).eventually
        (isOpen_Ioi.mem_nhds (by
          show C < (fl.φa (Ψ₀ τ)).re
          rw [hzφ]; exact hτ))
    have hS2 : ∀ᶠ x in 𝓝 (Ψ₀ τ), |(fl.φa x).im| < B := by
      have hcontim : ContinuousAt (fun x : ℂ => (fl.φa x).im) (Ψ₀ τ) :=
        Complex.continuous_im.continuousAt.comp hcont
      refine hcontim.eventually ((isOpen_lt continuous_abs continuous_const).mem_nhds ?_)
      show |(fl.φa (Ψ₀ τ)).im| < B
      rw [hzφ]
      exact hτB
    filter_upwards [hmem_nhds, hS1, hS2] with x hxmem hx1 hx2
    exact fl.φa_fatou.2 (hspec (fl.φa x) ⟨hx1, hx2⟩).1 hxmem (hspec (fl.φa x) ⟨hx1, hx2⟩).2
  have hsds : HasStrictDerivAt Ψ₀ (deriv fl.φa (Ψ₀ τ))⁻¹ (fl.φa (Ψ₀ τ)) :=
    hsd.to_local_left_inverse hne hev
  have hd : DifferentiableAt ℂ Ψ₀ (fl.φa (Ψ₀ τ)) := hsds.hasDerivAt.differentiableAt
  rwa [hzφ] at hd

end Work.FatouParabolic.Core
