import Mathlib
import Submission.Work.Noncompact.CompressionTube.Notation
import Submission.Work.Noncompact.CompressionTube.CorridorDefs
import Submission.Work.Noncompact.CompressionTube.LaneData

/-!
# The minimal per-stage lane interface (v4)

`LaneData.Lane` is the exact hypothesis list of the proved ray assembly
`Work.Noncompact.CompressionTube.ray_of_pieces_with_germs`.  The recursion that produces a lane
route by route only ever *delivers* the following data at stage `i` (see
`NOTES_S112_immersedLine_design_v4.md` §3.2, and `stageStep.exists_stage_piece` which produces
precisely this shape):

* the piece `P i` from `h.Q i` to `h.Q (i+1)`, smooth, an immersion and injective on `[0,1]`,
  with image in the corridor `h.C i`;
* its incoming germ datum at `h.Q i` (chart, direction, length) and its outgoing germ datum at
  `h.Q (i+1)`;

and *nothing else*: the trace-ball field, the rootedness radii and the terminal-trace invariant of
`laneAssembly.LaneState` are not outputs of the piece engine.  The consecutive separation
`P i '' Icc ∩ P (i+1) '' Icc ⊆ {h.Q (i+1)}` is, however, produced together with the piece (it is the
`hD`-conclusion of `exists_stage_region_of_piece'`), so it is carried by the *step relation*.

This file records that interface; the assembly from it to `Lane` (and hence, via
`LaneData.exists_immersedProperLine_of_twoLanes`, to the immersed proper line) is the lemma
`Work.Noncompact.CompressionTube.lane_of_data`.
-/

namespace Work.Noncompact.CompressionTube

open Set Topology Function
open scoped Manifold ContDiff _root_.Topology

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (MC n) smoothOrder M] [T2Space M] [SecondCountableTopology M]

/-- **The data delivered at one stage of the lane recursion.** -/
structure LaneDatum {b : M} {W : Set M} (h : CorridorChain b W) (i : ℕ) where
  /-- the piece of stage `i`, from `h.Q i` to `h.Q (i+1)` -/
  P : ℝ → M
  hsm : ContMDiff MCreal (MC n) smoothOrder P
  himm : ∀ t : ℝ, t ∈ Set.Icc (0:ℝ) 1 → Function.Injective (mfderiv MCreal (MC n) P t)
  hinj : Set.InjOn P (Set.Icc (0:ℝ) 1)
  hP0 : P 0 = h.Q i
  hP1 : P 1 = h.Q (i + 1)
  /-- the piece stays in its corridor -/
  hsub : P '' Set.Icc (0:ℝ) 1 ⊆ h.C i
  /-- the incoming germ datum at `h.Q i` -/
  cin : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n))
  uin : EuclideanSpace ℝ (Fin n)
  ein : ℝ
  hcin : cin ∈ IsManifold.maximalAtlas (MC n) smoothOrder M
  hsrin : h.Q i ∈ cin.source
  hein : 0 < ein
  huin : uin ≠ 0
  hgin : ∀ t : ℝ, 0 ≤ t → t ≤ ein → P t = cin.symm (cin (h.Q i) + t • uin)
  /-- the outgoing germ datum at `h.Q (i+1)` -/
  cout : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n))
  uout : EuclideanSpace ℝ (Fin n)
  eout : ℝ
  hcout : cout ∈ IsManifold.maximalAtlas (MC n) smoothOrder M
  hsrot : h.Q (i + 1) ∈ cout.source
  heout : 0 < eout
  huout : uout ≠ 0
  hgout : ∀ t : ℝ, 1 - eout ≤ t → t ≤ 1 →
    P t = cout.symm (cout (h.Q (i + 1)) + (t - 1) • uout)

/-- **The step relation between two consecutive stages.**  The pieces share the straight germ at the
common junction, and — this is the datum produced by the routing at stage `i+1` — their images meet
only at that junction. -/
structure LaneDatumStep {b : M} {W : Set M} (h : CorridorChain b W) (i : ℕ)
    (s : LaneDatum (n := n) (M := M) h i) (t : LaneDatum (n := n) (M := M) h (i + 1)) : Prop where
  /-- the germ datum at the common junction is shared -/
  cin_eq : t.cin = s.cout
  uin_eq : t.uin = s.uout
  /-- the new piece's incoming germ is no longer than the old piece's outgoing germ (the outgoing
  germ may always be shrunk, so this is free) -/
  ein_le : t.ein ≤ s.eout
  /-- the two consecutive pieces meet only at the junction -/
  hsepij : s.P '' Set.Icc (0:ℝ) 1 ∩ t.P '' Set.Icc (0:ℝ) 1 ⊆ {s.P 1}

end

end Work.Noncompact.CompressionTube
