import Mathlib
import Submission.Work.Drive.Mono.Geom3Defs
import Submission.Work.Drive.Mono.BoxGenE
import Submission.Work.Drive.Mono.edgeFree_of_margin

/-!
# The vertical-edge margin, almost everywhere in the level

`Work.Drive.Mono.VertEdgeFinite ψ c σ s` says that the surface `F = torusOf ψ` meets the box edge
lines pinned at `|y (σ i) − c (σ i)| = boxSide i * s` (`i = 0, 1`) in a *finite* set `A` of points.
Consequently the set of *heights* `z (σ 2) − c (σ 2)` realized on `A` is finite, and for every level
`u` outside that finite set the whole edge locus keeps the height `z (σ 2) − (c (σ 2) + u)` away from
`0` by a *uniform positive* margin `mE`.  Since a finite set of reals is null, this holds for almost
every `u` — which is exactly clause (c) (`Work.Drive.Mono.EdgeFree` from a margin) as it is consumed
by `Work.Drive.Mono.edgeFree_of_margin`.

This is the `ae`-producer for `Work.Drive.Mono.EdgeFree`: `VertEdgeFinite` (a conjunct of
`Work.Drive.Mono.BoxGenE`, proved a.e. in the centre/level by `Work.Drive.Mono.ae_diag_vertEdgeFinite`)
gives the margin a.e. in the cutting level.
-/

open MeasureTheory

namespace Work.Drive.Mono

set_option maxHeartbeats 800000

/-- **The vertical-edge margin holds for almost every cutting level.**  If the edge locus
`{|z (σ 0) − c (σ 0)| = boxSide 0 s} ∩ {|z (σ 1) − c (σ 1)| = boxSide 1 s} ∩ F` is finite, then for
almost every level `u` there is a uniform positive lower bound `mE` for the height
`|z (σ 2) − (c (σ 2) + u)|` over that locus. -/
theorem g3_vertEdge_margin_ae (ψ : Submission.Diffeo)
    {c : LeanEval.KnotTheory.PardonDistortion.R3} {σ : Equiv.Perm (Fin 3)} {s : ℝ}
    (hVE : Work.Drive.Mono.VertEdgeFinite ψ c σ s) :
    ∀ᵐ u ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ),
      ∃ mE : ℝ, 0 < mE ∧ ∀ z : LeanEval.KnotTheory.PardonDistortion.R3,
        z ∈ (Work.Drive.EpsSphere.torusOf ψ).carrier →
        |z (σ 0) - c (σ 0)| = Submission.boxSide 0 * s →
        |z (σ 1) - c (σ 1)| = Submission.boxSide 1 * s →
        mE ≤ |z (σ 2) - (c (σ 2) + u)| := by
  -- The edge locus and the finite set of heights it realizes.
  set A : Set LeanEval.KnotTheory.PardonDistortion.R3 :=
      {z : LeanEval.KnotTheory.PardonDistortion.R3 |
        z ∈ (Work.Drive.EpsSphere.torusOf ψ).carrier ∧
        |z (σ 0) - c (σ 0)| = Submission.boxSide 0 * s ∧
        |z (σ 1) - c (σ 1)| = Submission.boxSide 1 * s} with hA
  have hAfin : A.Finite := by rw [hA]; exact hVE
  set B : Set ℝ :=
      (fun z : LeanEval.KnotTheory.PardonDistortion.R3 => z (σ 2) - c (σ 2)) '' A with hB
  have hBfin : B.Finite := by rw [hB]; exact hAfin.image _
  -- Off the finite set of bad levels, the edge locus is bounded away from the level.
  have hmain : ∀ u : ℝ, u ∉ B → ∃ mE : ℝ, 0 < mE ∧
      ∀ z : LeanEval.KnotTheory.PardonDistortion.R3,
        z ∈ (Work.Drive.EpsSphere.torusOf ψ).carrier →
        |z (σ 0) - c (σ 0)| = Submission.boxSide 0 * s →
        |z (σ 1) - c (σ 1)| = Submission.boxSide 1 * s →
        mE ≤ |z (σ 2) - (c (σ 2) + u)| := by
    intro u huB
    set F : Finset LeanEval.KnotTheory.PardonDistortion.R3 := hAfin.toFinset with hFdef
    have hFmem : ∀ z : LeanEval.KnotTheory.PardonDistortion.R3, z ∈ F ↔ z ∈ A :=
      fun z => Set.Finite.mem_toFinset hAfin
    by_cases hne : F.Nonempty
    · -- The edge locus is nonempty: take the minimum of the realized distances.
      have hMne : (F.image (fun z => |z (σ 2) - (c (σ 2) + u)|)).Nonempty := hne.image _
      refine ⟨(F.image (fun z => |z (σ 2) - (c (σ 2) + u)|)).min' hMne, ?_, ?_⟩
      · -- the minimum is a realized distance, which is positive off `B`
        obtain ⟨z, hzF, hzval⟩ :=
          Finset.mem_image.mp
            (Finset.min'_mem (F.image (fun z => |z (σ 2) - (c (σ 2) + u)|)) hMne)
        have hzA : z ∈ A := (hFmem z).mp hzF
        have hzB : z (σ 2) - c (σ 2) ∈ B := by rw [hB]; exact ⟨z, hzA, rfl⟩
        have hneq : z (σ 2) - c (σ 2) ≠ u := fun h => huB (h ▸ hzB)
        rw [← hzval]
        exact abs_pos.mpr (fun hzero => hneq (by linarith [hzero]))
      · -- and it bounds every realized distance
        intro z hz h0 h1
        have hzA : z ∈ A := by rw [hA]; exact ⟨hz, h0, h1⟩
        have hzF : z ∈ F := (hFmem z).mpr hzA
        exact Finset.min'_le (F.image (fun z => |z (σ 2) - (c (σ 2) + u)|))
          |z (σ 2) - (c (σ 2) + u)| (Finset.mem_image.mpr ⟨z, hzF, rfl⟩)
    · -- The edge locus is empty: any positive margin works.
      refine ⟨1, one_pos, ?_⟩
      intro z hz h0 h1
      have hzA : z ∈ A := by rw [hA]; exact ⟨hz, h0, h1⟩
      exact absurd ⟨z, (hFmem z).mpr hzA⟩ hne
  -- A finite set of levels is null.
  filter_upwards [hBfin.countable.ae_notMem
    (MeasureTheory.volume : MeasureTheory.Measure ℝ)] with u hu
  exact hmain u hu

end Work.Drive.Mono
