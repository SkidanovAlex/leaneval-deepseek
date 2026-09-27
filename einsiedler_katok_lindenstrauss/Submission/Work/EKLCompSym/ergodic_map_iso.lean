import Mathlib
import Submission.Work.EKLCompSym.Basic
import Submission.Work.EKLCompSym.isAInvariant_map_iso

/-!
# `A`-ergodicity is transported by the `S₃`-symmetry `iso τ`

`Work.EKLCompSym.iso τ` is the permutation-matrix symmetry of `X₃ = SL₃(ℝ)/Γ₃`; it intertwines
the `aDiag t`-action with the `aDiag (t ∘ τ)`-action (`iso_smul_aDiag` in
`Submission.Work.EKLCompSym.Basic`).  Since `t ↦ t ∘ τ` is a bijection of `Fin 3 → ℝ`, the push
forward `(iso τ)_* μ` inherits both `A`-invariance and `A`-ergodicity from `μ`.

The invariance half is proved in `Submission.Work.EKLCompSym.isAInvariant_map_iso`; here we
transport ergodicity: an `A`-a.e.-invariant set `E` for `(iso τ)_* μ` pulls back to an
`A`-a.e.-invariant set `iso τ ⁻¹' E` for `μ`, on which the hypothesis applies.
-/

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.style.haveILetI false

noncomputable section

namespace Work.EKLCompSym

open Work.EKLContract MeasureTheory
open scoped Matrix symmDiff

/-- `A`-ergodicity is preserved by the push-forward along the `S₃`-symmetry `iso τ` of `X₃`:
`iso τ` conjugates the `A`-action to itself (via the bijection `t ↦ t ∘ τ` of `Fin 3 → ℝ`), so
the `A`-a.e.-invariant measurable sets of `(iso τ)_* μ` are exactly the images of those of `μ`. -/
theorem ergodic_map_iso {μ : MeasureTheory.Measure Work.EKLContract.X3}
    [MeasureTheory.IsProbabilityMeasure μ]
    (h : Work.EKLContract.IsAErgodic μ) (τ : Equiv.Perm (Fin 3)) :
    Work.EKLContract.IsAErgodic (MeasureTheory.Measure.map (Work.EKLCompSym.iso τ) μ) := by
  refine ⟨isAInvariant_map_iso τ h.1, ?_⟩
  intro E hE hEinv
  set E' : Set X3 := (iso τ) ⁻¹' E with hE'def
  have hE'meas : MeasurableSet E' := (measurable_iso τ) hE
  -- `E'` is `A`-a.e.-invariant for `μ`, since `iso τ` intertwines the two `aDiag`-actions.
  have hE'inv : ∀ s : Fin 3 → ℝ, (fun x : X3 => aDiag s • x) ⁻¹' E' =ᵐ[μ] E' := by
    intro s
    have h1 : (MeasureTheory.Measure.map (iso τ) μ)
        (((fun y : X3 => aDiag (s ∘ ⇑τ) • y) ⁻¹' E) ∆ E) = 0 := by
      have h2 := hEinv (s ∘ ⇑τ)
      rwa [← measure_symmDiff_eq_zero_iff] at h2
    have hcomp : (fun y : X3 => aDiag (s ∘ ⇑τ) • y) ∘ (iso τ)
        = (iso τ) ∘ (fun x : X3 => aDiag s • x) := by
      funext x
      simp only [Function.comp_apply]
      rw [iso_smul_aDiag τ s x]
    have hset : ((fun x : X3 => aDiag s • x) ⁻¹' E') ∆ E'
        = (iso τ) ⁻¹' (((fun y : X3 => aDiag (s ∘ ⇑τ) • y) ⁻¹' E) ∆ E) := by
      rw [Set.preimage_symmDiff, hE'def]
      rw [← Set.preimage_comp, ← Set.preimage_comp, hcomp]
    rw [← measure_symmDiff_eq_zero_iff]
    rw [hset]
    have hs : MeasurableSet (((fun y : X3 => aDiag (s ∘ ⇑τ) • y) ⁻¹' E) ∆ E) :=
      (((continuous_const_smul (aDiag (s ∘ ⇑τ))).measurable) hE).symmDiff hE
    rw [← Measure.map_apply (measurable_iso τ) hs]
    exact h1
  rcases h.2 E' hE'meas hE'inv with h0 | hc
  · left
    rw [Measure.map_apply (measurable_iso τ) hE, ← hE'def]
    exact h0
  · right
    rw [Measure.map_apply (measurable_iso τ) hE.compl, Set.preimage_compl, ← hE'def]
    exact hc

end Work.EKLCompSym

end
