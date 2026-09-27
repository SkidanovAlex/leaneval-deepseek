import Mathlib
import Submission.Work.Drive.Interfaces
import Submission.Work.Drive.SmoothArcs
import Submission.Work.Drive.CancelSignedSmooth
import Submission.Work.Drive.ReduceSignedSmooth
import Submission.Work.Whitney.EndgameSigned

/-! Guidance from the project lead (the requester):

# Guidance (project lead) — exists_embedding_of_compact_connected_smooth

This is PLUMBING, not new geometry. `Work.Whitney.exists_embedding_of_compact_connected_signed`
(Whitney/EndgameSigned.lean l.46, PROVED) is exactly this statement with `HasPushSigned` (arbitrary continuous
arcs) in place of `Work.Drive.HasPushSignedSmooth` (Drive/Interfaces.lean: the same, plus both arcs `C^∞` on ℝ and
immersive on [0,1]). The lead changed the interface because a continuous arc is what made the push hard: the
flattening needs a smooth arc. The endgame CHOOSES the arcs itself, so it can choose smooth ones.

Route: copy the signed chain and thread the smoothness through it.
- `exists_reduce_double_points_signed.lean` (l.~295) takes the arcs from
  `Work.Whitney.exists_disjoint_arcs_avoiding_finite` (continuous, injective on [0,1], disjoint except at the
  ends, avoiding a finite set D). You need a SMOOTH version: arcs `C^∞` on ℝ, immersive on [0,1], and everything
  else unchanged. Request it as its own lemma (`Drive/exists_smooth_disjoint_arcs_avoiding_finite`) or prove it:
  - n ≥ 3, M compact and connected. Smooth arc bricks: `Noncompact/CompressionTube/immersedArcWithGerm.lean`
    (smooth immersed embedded arc in a connected open set), `Noncompact/ProperLine/exists_contMDiff_arc_in_ne.lean`,
    `Noncompact/ProperLine/slitRouting.lean` (`exists_arc_avoiding_arcs`).
  - γ₂ must avoid γ₁. The complement of a compact smooth arc in a connected n-manifold (n ≥ 2) is connected.
  - Check the bricks' hypotheses (manifold class, boundaryless) before relying on them.
  - The reparametrisation to [0,1] must keep the derivative nonzero on [0,1].
- Then `HasCancelSigned` → a smooth-arc `HasCancelSignedSmooth`, and `hasCancelSigned_of_hasPushSigned` →
  its smooth version. This should be verbatim, since the cancellation only passes the arcs through.
- `hasReduceNFT_of_signed` → its smooth version, and finally this theorem.
Put the copies under `Submission/Work/Drive/` with new names. Do not edit the proved Whitney files.
-/

namespace Work.Drive

open scoped Manifold ContDiff
open Topology Work.Whitney

/-- **The reduction step of the signed endgame, smooth-arc form.**  This is
`Work.Whitney.hasReduceNFT_of_signed` with the smooth cancellation interface
`Work.Drive.HasCancelSignedSmooth` (which the smooth collar push
`Work.Drive.HasPushSignedSmooth` supplies). -/
theorem hasReduceNFT_of_signed_smooth {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (𝓡 n) ∞ M]
    [T2Space M] [CompactSpace M] [ConnectedSpace M] [SecondCountableTopology M]
    (hn : 3 ≤ n) (hins : Work.Whitney.HasInsertionSigned n M)
    (hcancel : HasCancelSignedSmooth n M) : Work.Whitney.HasReduceNFT n M :=
  fun f hf himm hfin hsimple htrans p₁ p₂ hp₁p₂ hfp =>
    exists_reduce_double_points_signed_smooth (M := M) hn hins hcancel f hf himm hfin hsimple htrans
      p₁ p₂ hp₁p₂ hfp

open scoped Manifold ContDiff in
/-- The compact connected `n ≥ 3` case from the SMOOTH-arc signed push. -/
theorem exists_embedding_of_compact_connected_smooth {n : ℕ} (hn : 3 ≤ n) {M : Type*}
    [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    [T2Space M] [CompactSpace M] [ConnectedSpace M] [SecondCountableTopology M]
    (hpush : Work.Drive.HasPushSignedSmooth n M) (hins : Work.Whitney.HasInsertionSigned n M)
    (hgen : ∃ g : M → EuclideanSpace ℝ (Fin (2 * n)),
      ContMDiff (𝓡 n) (𝓡 (2 * n)) ∞ g ∧
      (∀ x, Function.Injective (mfderiv (𝓡 n) (𝓡 (2 * n)) g x)) ∧
      (Work.Whitney.doubleSet g).Finite ∧ Work.Whitney.SimpleDP g ∧
      (∀ p : M × M, p ∈ Work.Whitney.doubleSet g →
        (mfderiv (𝓡 n) (𝓡 (2 * n)) g p.1).range ⊔
        (mfderiv (𝓡 n) (𝓡 (2 * n)) g p.2).range = ⊤)) :
    ∃ e : M → EuclideanSpace ℝ (Fin (2 * n)),
      ContMDiff (𝓡 n) (𝓡 (2 * n)) ∞ e ∧ Topology.IsEmbedding e ∧
      ∀ x : M, Function.Injective (mfderiv (𝓡 n) (𝓡 (2 * n)) e x) := by
  obtain ⟨g, hg, hgimm, hgfin, hgsimple, hgtrans⟩ := hgen
  exact Work.Whitney.exists_embedding_of_reduce_NFT hn
    (hasReduceNFT_of_signed_smooth hn hins (hasCancelSignedSmooth_of_hasPushSignedSmooth hpush))
    g hg hgimm hgfin hgsimple (Work.Whitney.transDP'_of_range hg hgtrans)

end Work.Drive
