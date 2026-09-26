import Mathlib
import Submission.Work.Drive.Mono.AEGenConsumer2

/-!
# The inputs of the `BoxGenE`-crux consumer: G4 + G5

`Work.Drive.Mono.boxShrink_of_cruxCoreWdAEG2` consumes the property `Work.Drive.Mono.ShiftGoodCentre`
(there is a centre, near the given one, at which `HasEssBox` holds and `BoxGenE` holds at almost
every level).  Here that property is derived from the two inputs of the lead's
`NOTES_LEAD_junctionGen.md`:

* **G4** (third conjunct of `Work.Drive.Mono.boxGenE_pairSard`): `HasEssBox` survives a small diagonal
  shift of the centre;
* **G5**: for a.e. shift `τ` and a.e. level `s`, the shifted box satisfies `BoxGenE`.  This is the
  combination of `Work.Drive.Mono.ae_boxGen`, G1 and G3 (the first and second conjuncts of
  `boxGenE_pairSard`) with G2 `Work.Drive.Mono.ae_faceNoBend`; the combinining lemma is
  `Work.Drive.Mono.ae_boxGenE_shift` below.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set MeasureTheory
open scoped ENNReal Topology

namespace Work.Drive.Mono

noncomputable section

/-- **G5: `BoxGenE` at a shifted centre, almost everywhere.**  From the pair-Sard inputs
(`FaceCrossReg` a.e. in `(s, u)`, `VertEdgeFinite` a.e. in `(τ, s)`), the no-bend input (`FaceNoBend`
a.e. in `u`) and the proved `Work.Drive.Mono.ae_boxGen`. -/
theorem ae_boxGenE_shift (ψ : Submission.Diffeo)
    (h1 : ∀ (c : R3) (σ : Equiv.Perm (Fin 3)),
      ∀ᵐ s ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ),
        ∀ᵐ u ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ), FaceCrossReg ψ c σ s u)
    (h2 : ∀ (c : R3) (σ : Equiv.Perm (Fin 3)) (s : ℝ),
      ∀ᵐ u ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ), FaceNoBend ψ c σ s u)
    (h3 : ∀ (c : R3) (σ : Equiv.Perm (Fin 3)),
      ∀ᵐ τ ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ),
        ∀ᵐ s ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ),
          VertEdgeFinite ψ (c + τ • diagVec) σ s) :
    ∀ (c : R3) (σ : Equiv.Perm (Fin 3)),
      ∀ᵐ τ ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ),
        ∀ᵐ s ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ), BoxGenE ψ (c + τ • diagVec) σ s := by
  intro c σ
  filter_upwards [h3 c σ] with τ hτ
  filter_upwards [hτ, h1 (c + τ • diagVec) σ, ae_boxGen ψ (c + τ • diagVec) σ] with s hτs h1s hbgs
  exact ⟨hbgs, hτs, h1s.and (h2 (c + τ • diagVec) σ s)⟩

/-- **G4 + G5 give the generic-centre property** `Work.Drive.Mono.ShiftGoodCentre`: choose the shift
`τ` in the interval `(-τ₀, τ₀)` of G4 that is not in the null set of G5. -/
theorem shiftGoodCentre_of_pairSard
    (hG4 : ∀ (P : Work.CoreTopology.ParamTorus) (r : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)),
      Submission.HasEssBox P r c σ →
        ∃ τ₀ : ℝ, 0 < τ₀ ∧
          ∀ τ : ℝ, |τ| < τ₀ → Submission.HasEssBox P r (c + τ • diagVec) σ)
    (hG5 : ∀ (ψ : Submission.Diffeo) (c : R3) (σ : Equiv.Perm (Fin 3)),
      ∀ᵐ τ ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ),
        ∀ᵐ s ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ), BoxGenE ψ (c + τ • diagVec) σ s) :
    ShiftGoodCentre := by
  intro ψ r c σ hbox
  obtain ⟨τ₀, hτ₀, hboxτ⟩ := hG4 (Work.Drive.EpsSphere.torusOf ψ) r c σ hbox
  have hcompl : MeasureTheory.volume {τ : ℝ |
      ¬ (∀ᵐ s ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ),
          BoxGenE ψ (c + τ • diagVec) σ s)} = 0 := by
    rw [← MeasureTheory.ae_iff]
    exact hG5 ψ c σ
  have hIoo : MeasureTheory.volume (Set.Ioo (-τ₀) τ₀) ≠ 0 := by
    rw [Real.volume_Ioo]
    simp [hτ₀]
  have hex : ∃ τ ∈ Set.Ioo (-τ₀) τ₀,
      (∀ᵐ s ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ),
        BoxGenE ψ (c + τ • diagVec) σ s) := by
    by_contra hcon
    have hcon' : ∀ τ ∈ Set.Ioo (-τ₀) τ₀,
        ¬ (∀ᵐ s ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ),
            BoxGenE ψ (c + τ • diagVec) σ s) :=
      fun τ hτ h => hcon ⟨τ, hτ, h⟩
    have hsub : Set.Ioo (-τ₀) τ₀ ⊆ {τ : ℝ |
        ¬ (∀ᵐ s ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ),
            BoxGenE ψ (c + τ • diagVec) σ s)} :=
      fun τ hτ => hcon' τ hτ
    have hle := MeasureTheory.measure_mono
      (μ := (MeasureTheory.volume : MeasureTheory.Measure ℝ)) hsub
    rw [hcompl] at hle
    exact hIoo (le_antisymm hle (bot_le))
  obtain ⟨τ, hτI, hτae⟩ := hex
  exact ⟨c + τ • diagVec, hboxτ τ (abs_lt.mpr hτI), hτae⟩

end

end Work.Drive.Mono
