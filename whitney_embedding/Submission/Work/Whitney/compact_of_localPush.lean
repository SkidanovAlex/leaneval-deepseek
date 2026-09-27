import Mathlib
import Submission.Work.Whitney.EndgameNFTrans
import Submission.Work.Whitney.hasInsertionNF

/-!
# The compact case of Whitney's embedding theorem, packaged on a push interface

Everything in the compact case of the target theorem except the *push* is already proved:

* the insertion step is `Work.Whitney.hasInsertionNF` (`Submission/Work/Whitney/hasInsertionNF.lean`);
* the general position input (a smooth immersion into `ℝ^{2n}` with finitely many simple transverse
  double points) is built inside `Work.Whitney.exists_embedding_of_compact_NFT` from
  `Work.Whitney.exists_simple_transverse_immersion`;
* the endgame (insertion, cancellation, and the strong induction on the number of double points) is
  `Work.Whitney.exists_embedding_of_compact_NFT`
  (`Submission/Work/Whitney/EndgameNFTrans.lean`), whose push input is `Work.Whitney.HasPushNFT`.

This file records that reduction in the two forms of the push interface that occur in the tree:

* `Work.Whitney.exists_embedding_of_compact_of_pushNFT` — on the **collar (bigon) push**
  `HasPushNFT`.  This is the sound interface: `HasPushNFT` is the push at the two double points of
  a clean region, i.e. the classical Whitney move along the bigon spanned by the two arcs, whose
  construction is *not* local at a single double point.

* `Work.Whitney.exists_embedding_of_compact_of_localPush` — on the **local cut-form push**
  `Work.Whitney.LocalPushNTrans` of `EndgameNF.lean`.  Kept for the record; see the warning below.

## WARNING (SESSION 14): the `LocalPushNTrans` hypothesis is probably not provable

The cut clause of `LocalPushNTrans` says that for `x ∈ W ∖ K` with `ψ (f x) = f z` one has
`z ∉ K`, where `K` contains the `p₁`-component of `f⁻¹'(closure (support ψ))` and is disjoint from
the `p₂`-component (both forced by the frontier clause and the clopen argument of
`NOTES_cut_push_session_L.md` §1).  So the pushed `p₂`-sheet inside the support must avoid the
`p₁`-sheet piece inside the support.  Those two pieces are complementary-dimensional disks in the
`2n`-ball `B ⊇ support ψ` with boundaries on `∂B` (hence fixed by `ψ`, which is the identity off
the support), and they meet transversely exactly at the double point `q` (which *is* displaced, so
`q ∈ support ψ`).  The intersection pairing of relative chains in `(B, ∂B)` is invariant under
ambient isotopies fixing `∂B`, so `[ψ D]·[E] = [D]·[E] = ±1 ≠ 0` and hence `ψ D ∩ E ≠ ∅`: *no*
compactly supported ambient isotopy can separate the two sheets.  Consequently the local cut-form
push cannot exist, and the route
`LocalPushNTrans → hasAmbientPushData_of_localPushTrans → cancellation` is blocked.  The classical
reason is that the Whitney move needs the *disc* (the bigon between the two double points) to make
room; a purely local push at one double point has none.
-/

namespace Work.Whitney

open scoped Manifold ContDiff
open Topology

set_option linter.unusedVariables false
set_option maxHeartbeats 800000

/-- **The compact case of Whitney's embedding theorem, from the collar (bigon) push.** -/
theorem exists_embedding_of_compact_of_pushNFT {n : ℕ} (hn : 3 ≤ n) {M : Type*}
    [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (𝓡 n) ∞ M] [T2Space M] [CompactSpace M] [SecondCountableTopology M]
    (hpush : ∀ (U : TopologicalSpace.Opens M) [CompactSpace U], HasPushNFT n U) :
    ∃ e : M → EuclideanSpace ℝ (Fin (2 * n)),
      ContMDiff (𝓡 n) (𝓡 (2 * n)) ∞ e ∧
      IsEmbedding e ∧
      ∀ x : M, Function.Injective (mfderiv (𝓡 n) (𝓡 (2 * n)) e x) :=
  exists_embedding_of_compact_NFT (n := n) hn hpush
    (fun U _ => hasInsertionNF (n := n) (by omega))

/-- **The compact case of Whitney's embedding theorem, from the local cut-form push.**

Kept for the record: the hypothesis is probably unprovable (see the module warning), but the
statement is a correct conditional one, and it says exactly what a local push would buy. -/
theorem exists_embedding_of_compact_of_localPush {n : ℕ} (hn : 3 ≤ n) {M : Type*}
    [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (𝓡 n) ∞ M] [T2Space M] [CompactSpace M] [SecondCountableTopology M]
    (hpush : ∀ (U : TopologicalSpace.Opens M) [CompactSpace U], LocalPushNTrans n U) :
    ∃ e : M → EuclideanSpace ℝ (Fin (2 * n)),
      ContMDiff (𝓡 n) (𝓡 (2 * n)) ∞ e ∧
      IsEmbedding e ∧
      ∀ x : M, Function.Injective (mfderiv (𝓡 n) (𝓡 (2 * n)) e x) :=
  exists_embedding_of_compact_NFT (n := n) hn
    (fun U _ => hasPushNFT_of_localPushNTrans (hpush U))
    (fun U _ => hasInsertionNF (n := n) (by omega))

end Work.Whitney
