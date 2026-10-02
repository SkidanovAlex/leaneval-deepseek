import Mathlib
import Submission.Work.SphHomology.Defs
import Submission.Work.SphHomology.Main
import Submission.Work.SphHomology.BaseCase
import Submission.Work.SphHomology.Induction
import Submission.Work.SphHomology.PieceCharted
import Submission.Work.SphHomology.Topology
import Submission.Work.Cohomology.euclidean_open_homology_vanishing
import Submission.Work.Tubular.PuncturedDiscPair.compl_homology_vanishing
import Submission.Work.Tubular.PuncturedDiscPair.sphSub_charted
import Submission.Work.Tubular.PuncturedDiscPair.t2Space_sphSub
import Submission.Work.Tubular.PuncturedDiscPair.sphOver_fibre_clopen

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option backward.isDefEq.respectTransparency false

namespace Work.Tubular.PuncturedDiscPair

/-- **The sphere bundle of a Euclidean real bundle over the complement of a point has no homology
above `8 + (k-1)`.**

The sphere bundle `S(Z)` of a Euclidean bundle `Z` of rank `k ≥ 1` over a compact connected base
`B` charted on `ℝ⁸` is a compact `(8 + (k-1))`-manifold, so it is charted on `ℝ^{8+(k-1)}
(`sphSub_charted`, `t2Space_sphSub`).  The fibre `sphOver Z {b₀}` over `b₀` is a closed nonempty
subset meeting every connected component of `S(Z)` (any clopen set containing it is everything:
`eq_univ_of_isClopen_of_sphOver_singleton`), so the general dimension bound
`isZero_homology_compl_of_clopen_meets` for the complement of such a set applies. -/
theorem sphOver_punctured_vanishing {B : Type} [TopologicalSpace B] [CompactSpace B]
    [T2Space B] [ConnectedSpace B] [ChartedSpace (EuclideanSpace ℝ (Fin 8)) B] {ι : Type}
    {k : ℕ} (hk : 1 ≤ k)
    (Z : Work.TangentClasses.RealBundle B (EuclideanSpace ℝ (Fin k)) ι)
    (hZ : Work.Thom.IsEuclidean Z) (b₀ : B) (m : ℕ) (hm : 8 + (k - 1) ≤ m) :
    CategoryTheory.Limits.IsZero ((Work.Cohomology.singularChains ℤ
      (TopCat.of (Work.SphHomology.sphOver Z ({b₀}ᶜ)))).homology m) := by
  classical
  haveI : ChartedSpace (EuclideanSpace ℝ (Fin (8 + (k - 1)))) (Work.Thom.SphSub Z) :=
    (sphSub_charted hk Z hZ).some
  haveI : T2Space (Work.Thom.SphSub Z) := t2Space_sphSub Z
  haveI : CompactSpace (Work.Thom.SphSub Z) := Work.SphHomology.compactSpace_sphSub Z hZ
  -- the complement of the fibre over `b₀` is the part of the sphere bundle over `{b₀}ᶜ`
  have hset : (Work.SphHomology.sphOver Z ({b₀} : Set B))ᶜ = Work.SphHomology.sphOver Z ({b₀}ᶜ) := by
    ext p
    rw [Set.mem_compl_iff, Work.SphHomology.mem_sphOver, Work.SphHomology.mem_sphOver]
    simp
  -- the fibre over `b₀` is nonempty
  have hFne : (Work.SphHomology.sphOver Z ({b₀} : Set B)).Nonempty := by
    refine ⟨⟨⟨b₀, EuclideanSpace.single (⟨0, by omega⟩ : Fin k) (1 : ℝ)⟩, ?_⟩, ?_⟩
    · show Work.Thom.fibreNorm Z _ = 1
      rw [Work.Thom.fibreNorm_mk]
      simp
    · show Z.proj _ ∈ ({b₀} : Set B)
      simp
  rw [← hset]
  exact isZero_homology_compl_of_clopen_meets (n := 8 + (k - 1))
    (M := TopCat.of (Work.Thom.SphSub Z)) (by omega) (Work.SphHomology.sphOver Z ({b₀} : Set B))
    (Work.SphHomology.isClosed_sphOver Z isClosed_singleton) hFne
    (fun W hW hFW => eq_univ_of_isClopen_of_sphOver_singleton Z hZ b₀ hW hFW) m hm

end Work.Tubular.PuncturedDiscPair
