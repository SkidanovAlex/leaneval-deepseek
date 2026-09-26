import Mathlib
import Submission.Work.Drive.Mono.g3OneEvDefs
import Submission.Work.Drive.Mono.ae_oneEvBad_slice_null
import Submission.Work.Drive.Mono.g3_exists_dense_heightGood_noVanishing
import Submission.Work.Drive.Mono.Band.exists_adapted_basis

/-!
# The one-event slice nullity holds at almost every cutting level

`Work.Drive.Mono.G3OneEv ψ s · c σ` is the package of `Work.Drive.Mono.g3OneEvDefs` at a cutting
level `u`: a countable dense family `Q` of `HeightGood` height directions with no vanishing sweep
coordinate, an adapted frame for every member, and the nullity of the `(h, τ)`-slice of the bad set
`Work.Drive.Mono.OneEvBad` of the direction triple of each member — at that same level `u`.

Here the package is produced for almost every `u`: the family and its frames are chosen once and for
all (independently of `u`) by
`Work.Drive.Mono.g3_exists_dense_heightGood_noVanishing` and
`Work.Drive.Mono.Band.exists_adapted_basis`, and the nullity for all members simultaneously is the
countable intersection (`MeasureTheory.ae_all_iff` over `↥Q`) of the per-member a.e. nullity
`Work.Drive.Mono.ae_oneEvBad_slice_null`.
-/

namespace Work.Drive.Mono

open LeanEval.KnotTheory.PardonDistortion MeasureTheory Set
open scoped RealInnerProductSpace

noncomputable section

/-- **The one-event slice nullity holds at almost every cutting level.** -/
theorem g3_ae_oneEv (ψ : Submission.Diffeo) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) :
    ∀ᵐ u ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ), G3OneEv ψ s u c σ := by
  classical
  obtain ⟨Q, hQc, hQH, hQd, hQnv⟩ := g3_exists_dense_heightGood_noVanishing ψ σ
  haveI : Countable ↥Q := Countable.to_subtype hQc
  -- no member of `Q` is the origin: otherwise the sweep direction would be `shiftVσ σ 1`, which
  -- does vanish in the coordinates different from `σ 2`
  have hne : ∀ ng ∈ Q, ng ≠ 0 := by
    intro ng hng h0
    have hunit : unitDir ng = 0 := by
      rw [h0, unitDir, norm_zero, inv_zero, zero_smul]
    have north : orthDir (Work.BoxShrink.shiftVσ σ 1) (unitDir ng)
        = Work.BoxShrink.shiftVσ σ 1 := by
      rw [hunit, orthDir, inner_zero_right, zero_smul, sub_zero,
        norm_shiftVσ_one σ, inv_one, one_smul]
    have hz : (Work.BoxShrink.shiftVσ σ 1 : R3) (σ 0) = 0 := by
      rw [Work.BoxShrink.shiftVσ_apply,
        if_neg (fun hc => absurd (σ.injective hc) (by decide))]
    exact (hQnv ng hng (σ 0)) (by rw [north]; exact hz)
  -- the adapted frame of every member
  have hframe_exists : ∀ ng ∈ Q, ∃ a b : R3,
      G3Frame (Work.BoxShrink.shiftVσ σ 1) ng a b := by
    intro ng hng
    have hun : ‖unitDir ng‖ = 1 := unitDir_norm ng (hne ng hng)
    have hproj : Work.BoxShrink.shiftVσ σ 1
        - inner ℝ (Work.BoxShrink.shiftVσ σ 1) (unitDir ng) • unitDir ng ≠ 0 := by
      intro hcon
      have hz : orthDir (Work.BoxShrink.shiftVσ σ 1) (unitDir ng) = 0 := by
        rw [orthDir, hcon, norm_zero, inv_zero, zero_smul]
      exact (hQnv ng hng 0) (by rw [hz]; rfl)
    have hv1 : ‖orthDir (Work.BoxShrink.shiftVσ σ 1) (unitDir ng)‖ = 1 :=
      g3_norm_orthDir_eq_one hproj
    have hvo : inner ℝ (orthDir (Work.BoxShrink.shiftVσ σ 1) (unitDir ng)) (unitDir ng) = 0 :=
      g3_inner_orthDir_eq_zero hun
    obtain ⟨a, b, ha, hb, hab, hva, hvb, hnb⟩ :=
      Work.Drive.Mono.Band.exists_adapted_basis hv1 hun hvo
    exact ⟨a, b, hun, hv1, hvo, ha, hb, hab, hva, hvb, hnb⟩
  let af : R3 → R3 := fun ng => if h : ng ∈ Q then (hframe_exists ng h).choose else 0
  let bf : R3 → R3 := fun ng => if h : ng ∈ Q then (hframe_exists ng h).choose_spec.choose else 0
  have haf : ∀ ng (h : ng ∈ Q),
      G3Frame (Work.BoxShrink.shiftVσ σ 1) ng (af ng) (bf ng) := by
    intro ng h
    have h1 : af ng = (hframe_exists ng h).choose := dif_pos h
    have h2 : bf ng = (hframe_exists ng h).choose_spec.choose := dif_pos h
    rw [h1, h2]
    exact (hframe_exists ng h).choose_spec.choose_spec
  have hnull : ∀ᵐ u ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ), ∀ ng ∈ Q,
      MeasureTheory.volume {y : ℝ × ℝ |
        Work.Drive.Mono.OneEvBad ψ s c σ (orthDir (Work.BoxShrink.shiftVσ σ 1) (unitDir ng))
          (af ng) (bf ng) u y.1 y.2} = 0 := by
    have h1 : ∀ ng : ↥Q, ∀ᵐ u ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ),
        MeasureTheory.volume {y : ℝ × ℝ |
          Work.Drive.Mono.OneEvBad ψ s c σ
            (orthDir (Work.BoxShrink.shiftVσ σ 1) (unitDir ng.1)) (af ng.1) (bf ng.1) u
            y.1 y.2} = 0 := by
      intro ng
      obtain ⟨_hun, hv1, _hvo, ha, hb, hab, hva, hvb, _⟩ := haf ng.1 ng.2
      exact Work.Drive.Mono.ae_oneEvBad_slice_null ψ c σ
        (orthDir (Work.BoxShrink.shiftVσ σ 1) (unitDir ng.1))
        (af ng.1) (bf ng.1) hv1 ha hb hab hva hvb
    have h2 := (MeasureTheory.ae_all_iff).mpr h1
    filter_upwards [h2] with u hu
    intro ng hng
    exact hu ⟨ng, hng⟩
  filter_upwards [hnull] with u hu
  exact ⟨Q, af, bf, hQc, hQH, hQd, hQnv, fun ng hng => haf ng hng, hu⟩

end

end Work.Drive.Mono
