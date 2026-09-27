import Mathlib
import Submission.Work.Whitney.reduce_double_points_abstract
import Submission.Work.Whitney.endgame_abstract
import Submission.Work.Whitney.pairDet_ne_zero_iff

/-!
# The assembly of the endgame for compact manifolds

* `Work.Whitney.transDP_of_range` converts the *intrinsic* transversality of a smooth immersion
  (`range (mfderiv f p.1) ⊔ range (mfderiv f p.2) = ⊤`, the form produced by the generic projection
  `Work.Whitney.exists_immersion_transverse_of_embedding`) into the `pairDet`-based certificate
  `Work.Whitney.TransDP A f` needed by the insertion step, using
  `Work.Whitney.pairDet_ne_zero_iff` and the smoothness of the charts of `A`.

* `Work.Whitney.exists_embedding_of_compact_connected` is the endgame assembled: for a compact
  connected `n`-manifold (`n ≥ 3`) which carries a smooth oriented atlas of *smooth* charts and an
  immersion `g : M → ℝ^{2n}` with finitely many *simple transverse* double points, the reduction step
  can be iterated to produce a smooth embedding `M → ℝ^{2n}` with injective derivative.

The remaining inputs are the two geometric ones described in `Submission.lean`:
the *existence* of such an immersion `g` (generic position: no triple points; this is where the
projection `Work.Whitney.exists_immersion_transverse_of_embedding` of the weak Whitney embedding
has to be upgraded), and the instantiation of `Work.Whitney.HasReduction` (insertion + Whitney
cancellation).
-/

namespace Work.Whitney

open scoped Manifold ContDiff
open Topology

/-- **Intrinsic transversality gives the `pairDet` certificate.** -/
theorem transDP_of_range {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    (A : Set (OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n))))
    (hA : IsSmoothOrientedAtlas A)
    (f : M → EuclideanSpace ℝ (Fin (2 * n)))
    (hf : ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n)))) ((⊤ : ℕ∞) : WithTop ℕ∞) f)
    (h : ∀ p : M × M, p ∈ doubleSet f →
      (mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n)))) f p.1).range ⊔
      (mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n)))) f p.2).range = ⊤) :
    TransDP A f := by
  intro p hp
  obtain ⟨c₁, hc₁, hp₁⟩ := hA.1.1 p.1
  obtain ⟨c₂, hc₂, hp₂⟩ := hA.1.1 p.2
  obtain ⟨hc₁sm, hc₁inv⟩ := hA.2 c₁ hc₁
  obtain ⟨hc₂sm, hc₂inv⟩ := hA.2 c₂ hc₂
  refine ⟨c₁, c₂, hc₁, hc₂, hp₁, hp₂, ?_⟩
  rw [pairDet_ne_zero_iff f c₁ c₂ p.1 p.2 hp₁ hp₂
    ((hc₁sm p.1 hp₁).mdifferentiableAt (by simp))
    ((hc₂sm p.2 hp₂).mdifferentiableAt (by simp))
    ((hc₁inv (c₁ p.1) (c₁.map_source hp₁)).mdifferentiableAt (by simp))
    ((hc₂inv (c₂ p.2) (c₂.map_source hp₂)).mdifferentiableAt (by simp))
    ((hf p.1).mdifferentiableAt (by simp)) ((hf p.2).mdifferentiableAt (by simp))]
  exact h p hp

/-- **The endgame for a compact connected manifold, assembled.**  Given an immersion `g : M → ℝ^{2n}`
with finitely many simple transverse double points, the reduction step can be iterated to produce a
smooth embedding. -/
theorem exists_embedding_of_compact_connected {n : ℕ} (hn : 3 ≤ n) {M : Type*}
    [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    [T2Space M] [CompactSpace M] [ConnectedSpace M] [SecondCountableTopology M]
    (hred : HasReduction n M)
    (A : Set (OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n))))
    (hA : IsSmoothOrientedAtlas A)
    (hgen : ∃ g : M → EuclideanSpace ℝ (Fin (2 * n)),
      ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n)))) ((⊤ : ℕ∞) : WithTop ℕ∞) g ∧
      (∀ x, Function.Injective
        (mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
          (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n)))) g x)) ∧
      (doubleSet g).Finite ∧ SimpleDP g ∧
      (∀ p : M × M, p ∈ doubleSet g →
        (mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
          (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n)))) g p.1).range ⊔
        (mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
          (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n)))) g p.2).range = ⊤)) :
    ∃ e : M → EuclideanSpace ℝ (Fin (2 * n)),
      ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n)))) ((⊤ : ℕ∞) : WithTop ℕ∞) e ∧
      IsEmbedding e ∧
      ∀ x : M, Function.Injective
        (mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
          (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n)))) e x) := by
  obtain ⟨g, hg, hgimm, hgfin, hgsimple, hgtrans⟩ := hgen
  exact exists_embedding_of_reduce hn hred A hA g hg hgimm hgfin hgsimple
    (transDP_of_range A hA g hg hgtrans)

end Work.Whitney
