import Mathlib
import Submission.Work.Whitney.exists_reduce_double_points_signed
import Submission.Work.Whitney.CancelSigned
import Submission.Work.Whitney.InsertSigned
import Submission.Work.Whitney.EndgameNFTrans
import Submission.Work.Whitney.exists_simple_transverse_immersion
import Submission.Work.Embedding.exists_embedding_of_components

/-!
# The *signed* endgame of Whitney's strong embedding theorem

The sign-free interfaces `Work.Whitney.HasPushNFT` / `Work.Whitney.HasCancelNFT` are false in
general (a same-type pair of double points cannot be disengaged), so the compact branch of the
target is driven by the *signed* interfaces `Work.Whitney.HasPushSigned`,
`Work.Whitney.HasInsertionSigned` (proved) and the reduction step
`Work.Whitney.exists_reduce_double_points_signed` (proved).

This file contains the packaging: the signed reduction interface `HasReduceNFT` (obtained from the
signed insertion and the signed cancellation, via `Work.Whitney.hasCancelSigned_of_hasPushSigned`),
and the compact connected / compact packagings, mirroring
`Submission/Work/Whitney/EndgameNFTrans.lean`.
-/

namespace Work.Whitney

open scoped Manifold ContDiff
open Topology

set_option linter.unusedVariables false

/-- **The reduction interface, from the signed insertion and cancellation.** -/
theorem hasReduceNFT_of_signed {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (𝓡 n) ∞ M]
    [T2Space M] [CompactSpace M] [ConnectedSpace M] [SecondCountableTopology M]
    (hn : 3 ≤ n) (hins : HasInsertionSigned n M) (hcancel : HasCancelSigned n M) :
    HasReduceNFT n M :=
  fun f hf himm hfin hsimple htrans p₁ p₂ hp₁p₂ hfp =>
    exists_reduce_double_points_signed (M := M) hn hins hcancel f hf himm hfin hsimple htrans
      p₁ p₂ hp₁p₂ hfp

/-- **The compact connected branch of Whitney's strong embedding theorem, signed form.**  A compact
connected smooth `n`-manifold (`n ≥ 3`), without any orientability hypothesis, admits a smooth
embedding into `ℝ^{2n}` with injective derivative, given the signed push, the signed insertion, and
the general position input. -/
theorem exists_embedding_of_compact_connected_signed {n : ℕ} (hn : 3 ≤ n) {M : Type*}
    [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (𝓡 n) ∞ M]
    [T2Space M] [CompactSpace M] [ConnectedSpace M] [SecondCountableTopology M]
    (hpush : HasPushSigned n M) (hins : HasInsertionSigned n M)
    (hgen : ∃ g : M → EuclideanSpace ℝ (Fin (2 * n)),
      ContMDiff (𝓡 n) (𝓡 (2 * n)) ∞ g ∧
      (∀ x, Function.Injective (mfderiv (𝓡 n) (𝓡 (2 * n)) g x)) ∧
      (doubleSet g).Finite ∧ SimpleDP g ∧
      (∀ p : M × M, p ∈ doubleSet g →
        (mfderiv (𝓡 n) (𝓡 (2 * n)) g p.1).range ⊔
        (mfderiv (𝓡 n) (𝓡 (2 * n)) g p.2).range = ⊤)) :
    ∃ e : M → EuclideanSpace ℝ (Fin (2 * n)),
      ContMDiff (𝓡 n) (𝓡 (2 * n)) ∞ e ∧
      IsEmbedding e ∧
      ∀ x : M, Function.Injective (mfderiv (𝓡 n) (𝓡 (2 * n)) e x) := by
  obtain ⟨g, hg, hgimm, hgfin, hgsimple, hgtrans⟩ := hgen
  exact exists_embedding_of_reduce_NFT hn
    (hasReduceNFT_of_signed hn hins (hasCancelSigned_of_hasPushSigned hpush))
    g hg hgimm hgfin hgsimple (transDP'_of_range hg hgtrans)

/-- **The compact branch of Whitney's strong embedding theorem, signed form.**  A compact smooth
`n`-manifold (`n ≥ 3`), orientable or not, admits a smooth embedding into `ℝ^{2n}` with injective
derivative, given the signed push and the signed insertion on each compact open submanifold. -/
theorem exists_embedding_of_compact_signed {n : ℕ} (hn : 3 ≤ n) {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (𝓡 n) ∞ M]
    [T2Space M] [CompactSpace M] [SecondCountableTopology M]
    (hpush : ∀ (U : TopologicalSpace.Opens M) [CompactSpace U], HasPushSigned n U)
    (hins : ∀ (U : TopologicalSpace.Opens M) [CompactSpace U], HasInsertionSigned n U) :
    ∃ e : M → EuclideanSpace ℝ (Fin (2 * n)),
      ContMDiff (𝓡 n) (𝓡 (2 * n)) ∞ e ∧
      IsEmbedding e ∧
      ∀ x : M, Function.Injective (mfderiv (𝓡 n) (𝓡 (2 * n)) e x) := by
  classical
  refine Work.Embedding.exists_embedding_of_components (n := n) (by omega) ?_
  intro U hUconn hUcpt
  haveI : CompactSpace U := isCompact_iff_compactSpace.mp hUcpt
  haveI : ConnectedSpace U := isConnected_iff_connectedSpace.mp hUconn
  exact exists_embedding_of_compact_connected_signed hn (hpush U) (hins U)
    (exists_simple_transverse_immersion (n := n) hn)

end Work.Whitney
