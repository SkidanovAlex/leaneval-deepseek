import Mathlib
import Submission.Work.Drive.oFatDefsS
import Submission.Work.Drive.ofatObstruction_edges

namespace Work.Drive

open LeanEval.KnotTheory.Quadrisecant

/-- **`ShortMid` is a lifted trisecant.**  The middle clause of `ShortMid r δs` is verbatim the
middle clause of `OFatR r ρ` (the fatness bounds are simply dropped), so the same argument as
`ofatR_subset_liftedTrisecant` applies word for word. -/
lemma shortMid_subset_liftedTrisecant {r : ℝ → Space} (hr : IsSmoothKnot r) (δs : ℝ) :
    ShortMid r δs ⊆ liftedTrisecant r := by
  rintro q ⟨h0, h1, -, u, -, -, hu3⟩
  refine mem_liftedTrisecant_iff.mpr ⟨h0, h1, ?_⟩
  rw [stripSecantClass_eq_mobiusCover]
  refine (HasMiddleOnClass_iff r (stripPair q h0 h1)).mpr ⟨(u : AddCircle period), ?_⟩
  show knotMap r (u : AddCircle period) ∈
    openSegment ℝ (knotMap r ((stripPair q h0 h1).1.1)) (knotMap r ((stripPair q h0 h1).1.2))
  simp only [stripPair]
  rw [knotMap_eq_r hr u, knotMap_eq_r hr q.1, knotMap_eq_r hr (q.1 + q.2)]
  exact hu3

/-- **The `E3′` edge band.**  For a knot without inflections and `ρ, δs > 0` with `δs < period/2`,
the closure of `Work.Drive.OFatObstructionS r ρ δs = OFatObstruction r ρ ∪ ShortMid r δs` is
contained in a band `{δ ≤ q.2 ≤ period - δ}` with `δ > 0`.

Proof: `ShortMid r δs ⊆ liftedTrisecant r` (its middle clause is the same as `OFatR`'s, cf.
`ofatR_subset_liftedTrisecant`), so `Work.Drive.shortSecantsFree_of_noInflection` gives a uniform
`δ₁ > 0` with `δ₁ ≤ q.2 ≤ period - δ₁` for every point of `ShortMid` and of `OFatObstruction`; the
closed band propagates to the closure (`closure_subset_band` in `ofatObstruction_edges`). -/
theorem ofatObstructionS_edges {r : ℝ → Space} (hr : IsSmoothKnot r)
    (hinfl : ∀ t : ℝ, LinearIndependent ℝ ![deriv r t, deriv (deriv r) t])
    {ρ δs : ℝ} (hρ : 0 < ρ) (hδs : 0 < δs) (hδsP : δs < period / 2) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ q ∈ closure (OFatObstructionS r ρ δs),
      δ ≤ q.2 ∧ q.2 ≤ period - δ := by
  -- the band for the `OFatObstruction` part, and the uniform band for the trisecant locus
  obtain ⟨δ₁, hδ₁pos, hδ₁⟩ := ofatObstruction_edges hr hinfl hρ
  obtain ⟨δ₂, hδ₂pos, hδ₂⟩ := shortSecantsFree_of_noInflection hr hinfl
  refine ⟨min δ₁ δ₂, lt_min hδ₁pos hδ₂pos, ?_⟩
  intro q hq
  rw [OFatObstructionS, closure_union] at hq
  rcases hq with hq | hq
  · obtain ⟨h1, h2⟩ := hδ₁ q hq
    exact ⟨le_trans (min_le_left _ _) h1, by linarith [min_le_left δ₁ δ₂]⟩
  · -- `ShortMid ⊆ liftedTrisecant`, and the band of the trisecant locus passes to the closure
    have hsub : closure (ShortMid r δs) ⊆ closure (liftedTrisecant r) :=
      closure_mono (shortMid_subset_liftedTrisecant hr δs)
    obtain ⟨h1, h2⟩ := closure_subset_band hδ₂ q (hsub hq)
    exact ⟨le_trans (min_le_right _ _) h1, by linarith [min_le_right δ₁ δ₂]⟩

end Work.Drive
