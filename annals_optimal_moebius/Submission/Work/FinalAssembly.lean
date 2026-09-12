import Submission.Work.Relation4Assembly
import Submission.Work.FoliationInterface
import Submission.Commons.Geometry.Moebius.tpattern_escape_of_disjoint

open OptimalMoebius Topology Filter
open scoped BigOperators Matrix Topology Metric
set_option autoImplicit false
set_option maxHeartbeats 800000
local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)
local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-!
# Final assembly: the T-pattern escape gives the Lemma-G witness

Chaining three green layers:

* `Commons.Geometry.Moebius.tpattern_escape_of_disjoint`: for two
  perpendicular coplanar bends of a band foliation with DISJOINT image
  segments, one endpoint of one bend is at perpendicular distance `> 1`
  from the line through the other bend's endpoints;
* `Submission.Work.Relation4Assembly.lemmaG_witness_of_boundary_far`:
  such a far boundary point yields the Lemma-G witness
  `∃ t, 2a > max (aspectDelta t) (aspectNu t)`;
* the translation between the project's `Submission.BandFoliation` and the
  commons' `Commons.PaperMoebius.BandFoliation` (same fields; the `chord`
  function is transported verbatim so all terms agree definitionally).

The only remaining input is the disjointness of the two image segments for
the T-pattern pair (`0 < δ < a`), which follows from the monotonicity of the
spliced endpoint heights plus injectivity of `f`.

Build: `lake build Submission.Work.FinalAssembly` (rc=0 target).
-/

noncomputable section
namespace Submission

open Submission.PaperBand

/-- Transport a project pre-bend chord to the commons structure. -/
def toCommonsBendData (b : BendData) : Commons.PaperMoebius.BendData where
  A := b.A
  B := b.B
  left_coord := b.left_coord
  right_coord := b.right_coord

variable {a : ℝ} {f : ℝ² → ℝ³}

/-- Transport the project's embedding to the commons structure. -/
def toCommonsEmbedding (hf : IsMoebiusEmbedding a f) : Commons.PaperMoebius.IsMoebiusEmbedding a f where
  periodic := hf.periodic
  smooth := hf.smooth
  isometry := hf.isometry
  embedding := hf.embedding

/-- Transport the project's band foliation to the commons structure
(same chords). -/
def toCommons (hf : IsMoebiusEmbedding a f)
    (F : BandFoliation a f hf) : Commons.PaperMoebius.BandFoliation a f (toCommonsEmbedding hf) where
  chord := fun y => toCommonsBendData (F.chord y)
  centre := fun y => F.centre y
  deck := fun y => ⟨(F.deck y).1, (F.deck y).2⟩
  cont_left := F.cont_left
  cont_right := F.cont_right
  preBend := fun y => F.preBend y

end Submission

namespace Submission

open Submission.PaperBand

/-- The `preBend` isometry in the explicit `!₂` coordinates of the chord. -/
lemma preBend_vec {a : ℝ} {f : ℝ² → ℝ³} {hf : IsMoebiusEmbedding a f}
    (F : BandFoliation a f hf) (y : ℝ) :
    ‖f !₂[1, ((F.chord y).B) 1] - f !₂[0, ((F.chord y).A) 1]‖
      = ‖(!₂[1, ((F.chord y).B) 1] : ℝ²) - !₂[0, ((F.chord y).A) 1]‖ := by
  have hA : (F.chord y).A = !₂[0, ((F.chord y).A) 1] := leftEdge_eq_vec (F.chord y).left_coord
  have hB : (F.chord y).B = !₂[1, ((F.chord y).B) 1] := rightEdge_eq_vec (F.chord y).right_coord
  have hp := F.preBend y
  have e1 : f !₂[1, ((F.chord y).B) 1] = f ((F.chord y).B) := congrArg f hB.symm
  have e2 : f !₂[0, ((F.chord y).A) 1] = f ((F.chord y).A) := congrArg f hA.symm
  have e3 : (!₂[1, ((F.chord y).B) 1] : ℝ²) = (F.chord y).B := hB.symm
  have e4 : (!₂[0, ((F.chord y).A) 1] : ℝ²) = (F.chord y).A := hA.symm
  rw [e1, e2, e3, e4]
  exact hp

/-- **A far boundary point of a pre-bend chord yields the Lemma-G
witness.**  The witness boundary point is given as `f (1,s)`, the chord by
its preimage heights `α, β`, and the decomposition by the perpendicular
component `n` about the chord's midpoint. -/
theorem witness_of_boundary_point {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    (ha : 0 < a) {α β s : ℝ} {W : ℝ³} {c : ℝ} {n : ℝ³}
    (hW : W = f !₂[1, s])
    (hdec : W - (1 / 2 : ℝ) • (f !₂[1, β] + f !₂[0, α])
        = c • (f !₂[1, β] - f !₂[0, α]) + n)
    (hperp : inner ℝ n (f !₂[1, β] - f !₂[0, α]) = 0) (hn : 1 < ‖n‖)
    (himg : ‖f !₂[1, β] - f !₂[0, α]‖ = ‖(!₂[1, β] : ℝ²) - !₂[0, α]‖) :
    ∃ t : ℝ, 2 * a > max (aspectDelta t) (aspectNu t) := by
  have hdec' : f !₂[1, s] - (1 / 2 : ℝ) • (f !₂[1, β] + f !₂[0, α])
      = c • (f !₂[1, β] - f !₂[0, α]) + n := by
    rw [← hW]; exact hdec
  exact lemmaG_witness_of_boundary_far hf ha himg hdec' hperp hn

end Submission

namespace Submission

open Submission.PaperBand

open BandFoliation

/-- Rewrite the perpendicular decomposition of a chord leaf into the
explicit `!₂` coordinates. -/
lemma decomp_vec {a : ℝ} {f : ℝ² → ℝ³} {hf : IsMoebiusEmbedding a f}
    (F : BandFoliation a f hf) (y : ℝ) {W : ℝ³} {c : ℝ} {n : ℝ³}
    (hdec : W - (1 / 2 : ℝ) • (f (B F y) + f (A F y))
        = c • (f (B F y) - f (A F y)) + n) :
    W - (1 / 2 : ℝ) • (f !₂[1, ((F.chord y).B) 1] + f !₂[0, ((F.chord y).A) 1])
      = c • (f !₂[1, ((F.chord y).B) 1] - f !₂[0, ((F.chord y).A) 1]) + n := by
  have hA' : f (A F y) = f !₂[0, ((F.chord y).A) 1] :=
    congrArg f (leftEdge_eq_vec (F.chord y).left_coord)
  have hB' : f (B F y) = f !₂[1, ((F.chord y).B) 1] :=
    congrArg f (rightEdge_eq_vec (F.chord y).right_coord)
  rw [hA', hB'] at hdec
  exact hdec

/-- Same for the perpendicularity statement. -/
lemma perp_vec {a : ℝ} {f : ℝ² → ℝ³} {hf : IsMoebiusEmbedding a f}
    (F : BandFoliation a f hf) (y : ℝ) {n : ℝ³}
    (hperp : inner ℝ n (f (B F y) - f (A F y)) = 0) :
    inner ℝ n (f !₂[1, ((F.chord y).B) 1] - f !₂[0, ((F.chord y).A) 1]) = 0 := by
  have hA' : f (A F y) = f !₂[0, ((F.chord y).A) 1] :=
    congrArg f (leftEdge_eq_vec (F.chord y).left_coord)
  have hB' : f (B F y) = f !₂[1, ((F.chord y).B) 1] :=
    congrArg f (rightEdge_eq_vec (F.chord y).right_coord)
  rw [hA', hB'] at hperp
  exact hperp

/-- **The Lemma-G witness from the T-pattern**, given disjointness of the
two image segments. -/
theorem witness_of_tpattern {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f) (ha : 0 < a)
    (F : BandFoliation a f hf) {y δ : ℝ}
    (hdisj : ∀ v w : ℝ², v ∈ Set.range (fun s : ℝ =>
        (1 - s) • (F.chord y).A + s • (F.chord y).B) →
      w ∈ Set.range (fun s : ℝ =>
        (1 - s) • (F.chord (y + δ)).A + s • (F.chord (y + δ)).B) →
      f v ≠ f w)
    (hδ0 : 0 < δ) (hδa : δ < a)
    (hperp : WithLp.ofLp (BandFoliation.imageDir F y) ⬝ᵥ
        WithLp.ofLp (BandFoliation.imageDir F (y + δ)) = 0)
    (hcop : WithLp.ofLp (BandFoliation.imageMid F y - BandFoliation.imageMid F (y + δ)) ⬝ᵥ
        (WithLp.ofLp (BandFoliation.imageDir F y) ⨯₃
          WithLp.ofLp (BandFoliation.imageDir F (y + δ))) = 0) :
    ∃ t : ℝ, 2 * a > max (aspectDelta t) (aspectNu t) := by
  have hesc := Commons.Geometry.Moebius.tpattern_escape_of_disjoint
    (toCommonsEmbedding hf) ha (toCommons hf F) hdisj hδ0 hδa hperp hcop
  rcases hesc with ⟨c, n, hdec, hp, hn⟩ | ⟨c, n, hdec, hp, hn⟩
    | ⟨c, n, hdec, hp, hn⟩ | ⟨c, n, hdec, hp, hn⟩
  · refine witness_of_boundary_point hf ha
      (α := ((F.chord y).A) 1) (β := ((F.chord y).B) 1)
      (s := ((F.chord (y + δ)).A) 1 - a) (W := f ((F.chord (y + δ)).A))
      (c := c) (n := n) ?_ (decomp_vec F y hdec) (perp_vec F y hp) hn (preBend_vec F y)
    have hA2 : f ((F.chord (y + δ)).A) = f !₂[0, ((F.chord (y + δ)).A) 1] :=
      congrArg f (leftEdge_eq_vec (F.chord (y + δ)).left_coord)
    rw [hA2]
    exact (f_leftEdge_eq_rightEdge_minus hf (((F.chord (y + δ)).A) 1)).symm
  · refine witness_of_boundary_point hf ha
      (α := ((F.chord y).A) 1) (β := ((F.chord y).B) 1)
      (s := ((F.chord (y + δ)).B) 1) (W := f ((F.chord (y + δ)).B))
      (c := c) (n := n) ?_ (decomp_vec F y hdec) (perp_vec F y hp) hn (preBend_vec F y)
    exact congrArg f (rightEdge_eq_vec (F.chord (y + δ)).right_coord)
  · refine witness_of_boundary_point hf ha
      (α := ((F.chord (y + δ)).A) 1) (β := ((F.chord (y + δ)).B) 1)
      (s := ((F.chord y).A) 1 - a) (W := f ((F.chord y).A))
      (c := c) (n := n) ?_ (decomp_vec F (y + δ) hdec) (perp_vec F (y + δ) hp) hn
      (preBend_vec F (y + δ))
    have hA1 : f ((F.chord y).A) = f !₂[0, ((F.chord y).A) 1] :=
      congrArg f (leftEdge_eq_vec (F.chord y).left_coord)
    rw [hA1]
    exact (f_leftEdge_eq_rightEdge_minus hf (((F.chord y).A) 1)).symm
  · refine witness_of_boundary_point hf ha
      (α := ((F.chord (y + δ)).A) 1) (β := ((F.chord (y + δ)).B) 1)
      (s := ((F.chord y).B) 1) (W := f ((F.chord y).B))
      (c := c) (n := n) ?_ (decomp_vec F (y + δ) hdec) (perp_vec F (y + δ) hp) hn
      (preBend_vec F (y + δ))
    exact congrArg f (rightEdge_eq_vec (F.chord y).right_coord)

end Submission
