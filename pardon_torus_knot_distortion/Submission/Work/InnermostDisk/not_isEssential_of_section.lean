import Mathlib
import Submission.Work.InnermostDisk.Defs

/-!
# A loop lying in a set that lifts to the parameter plane is inessential

This file proves `Work.InnermostDisk.not_isEssential_of_section`, the "chart/section" step
of Pardon's innermost-disc argument.

If `s ⊆ ℝ³` is a subset of `ℝ³` that admits a *continuous section* `σ` of the parametrisation
of the torus `P` — that is, a continuous `σ : C(s, ℝ × ℝ)` with `P.psi (σ x).1 (σ x).2 = x`
for all `x ∈ s` — then every closed curve `γ` of `F = P.carrier` whose image lies in `s` is
*inessential* (its winding vector vanishes).

The reason is that `t ↦ σ ⟨γ.γ t, _⟩` is then a continuous lift of `γ` to the parameter plane
which is manifestly `2π`-periodic, hence has winding vector `0`; since the winding vector of a
closed curve does not depend on the chosen lift (`Work.CoreTopology.LiftOf.winding_eq`), `γ`
itself has vanishing winding vector.

In the application `s` is a small chart neighbourhood of a point of the torus, on which the
parametrisation `P.psi` is a homeomorphism; the conclusion is then that a loop contained in a
small enough ball around a point of the torus is null-homotopic in the torus.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set

namespace Work.InnermostDisk

open Work.CoreTopology

noncomputable section

/-- A lift of a closed curve whose two parameter functions return to their starting values
after one period has vanishing winding vector: it is the lift of a null-homotopic loop. -/
theorem winding_eq_zero_of_period_eq {P : ParamTorus} {γ : ClosedCurve P} (L : LiftOf P γ)
    (hΘ : L.Θ (2 * Real.pi) = L.Θ 0) (hΦ : L.Φ (2 * Real.pi) = L.Φ 0) :
    L.winding = (0, 0) := by
  refine Prod.ext ?_ ?_
  · have hmul : (L.winding).1 * (2 * Real.pi) = 0 := by
      have h := L.winding_spec.1
      rw [hΘ] at h
      linarith
    have h1' : (((L.winding).1 : ℤ) : ℝ) = 0 := by
      rcases mul_eq_zero.mp hmul with h | h
      · exact h
      · exact absurd h two_pi_ne_zero
    exact_mod_cast h1'
  · have hmul : (L.winding).2 * (2 * Real.pi) = 0 := by
      have h := L.winding_spec.2
      rw [hΦ] at h
      linarith
    have h2' : (((L.winding).2 : ℤ) : ℝ) = 0 := by
      rcases mul_eq_zero.mp hmul with h | h
      · exact h
      · exact absurd h two_pi_ne_zero
    exact_mod_cast h2'

/-- **A closed curve lying in the domain of a chart of the torus is inessential.**

If `σ : s → ℝ × ℝ` is a continuous section of the parametrisation `P.psi` over a subset
`s ⊆ ℝ³`, then any closed curve `γ` of the torus `F = P.carrier` whose image is contained in
`s` has vanishing winding vector, i.e. is null-homotopic in `F`.

Indeed `t ↦ σ ⟨γ.γ t, _⟩` is a continuous lift of `γ`; it is `2π`-periodic because `γ` is, so
its winding vector is `0`; the winding vector is independent of the lift. -/
theorem not_isEssential_of_section {P : Work.CoreTopology.ParamTorus}
    {s : Set LeanEval.KnotTheory.PardonDistortion.R3} (σ : C(s, ℝ × ℝ))
    (hσ : ∀ x : s, P.psi (σ x).1 (σ x).2 = (x : LeanEval.KnotTheory.PardonDistortion.R3))
    {γ : Work.CoreTopology.ClosedCurve P} (hγ : ∀ t : ℝ, γ.γ t ∈ s) :
    ¬ Work.CoreTopology.IsEssential P γ := by
  rintro ⟨L, hL⟩
  -- the section provides a lift of `γ` to the parameter plane
  have hcont : Continuous fun t : ℝ => (⟨γ.γ t, hγ t⟩ : s) :=
    γ.cont.subtype_mk _
  let L' : LiftOf P γ :=
    { Θ := fun t => (σ ⟨γ.γ t, hγ t⟩).1
      Φ := fun t => (σ ⟨γ.γ t, hγ t⟩).2
      contΘ := (continuous_fst.comp σ.continuous).comp hcont
      contΦ := (continuous_snd.comp σ.continuous).comp hcont
      lifts := fun t => hσ ⟨γ.γ t, hγ t⟩ }
  -- this lift is periodic with `γ`, hence has vanishing winding vector
  have hγper : (⟨γ.γ (2 * Real.pi), hγ (2 * Real.pi)⟩ : s) = ⟨γ.γ 0, hγ 0⟩ := by
    apply Subtype.ext
    simpa using (γ.periodic 0)
  have hΘ : L'.Θ (2 * Real.pi) = L'.Θ 0 := by
    show (σ ⟨γ.γ (2 * Real.pi), hγ (2 * Real.pi)⟩).1 = (σ ⟨γ.γ 0, hγ 0⟩).1
    rw [hγper]
  have hΦ : L'.Φ (2 * Real.pi) = L'.Φ 0 := by
    show (σ ⟨γ.γ (2 * Real.pi), hγ (2 * Real.pi)⟩).2 = (σ ⟨γ.γ 0, hγ 0⟩).2
    rw [hγper]
  have hw : L'.winding = (0, 0) := winding_eq_zero_of_period_eq L' hΘ hΦ
  exact hL (by rw [← L.winding_eq L']; exact hw)

end

end Work.InnermostDisk
