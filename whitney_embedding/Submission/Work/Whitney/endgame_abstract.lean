import Mathlib
import Submission.Work.Whitney.InsertedDoublePoint
import Submission.Work.Whitney.reduce_double_points_abstract
import Submission.Work.Whitney.isEmbedding_of_injective_of_compactSpace

/-!
# The iteration of the Whitney endgame

`Work.Whitney.exists_embedding_of_reduce` is the *combinatorial* heart of the endgame of Whitney's
strong embedding theorem: if a single simple transverse double point of a smooth immersion
`f : M → ℝ^{2n}` (with `M` a compact connected `n`-manifold, `n ≥ 3`) can be removed while
preserving the invariants `SimpleDP` ("every double point has exactly two preimages") and `TransDP`
("every double point is transverse"), then *all* double points can be removed, so that `f` can be
deformed into an embedding.

The reduction hypothesis `Work.Whitney.HasReduction` is supplied by
`Work.Whitney.exists_reduce_double_points` (insertion + Whitney cancellation) prefixed
`fun f hf himm hfin A hA hs ht p₁ p₂ hp hfp => ...`.
-/

namespace Work.Whitney

open scoped Manifold ContDiff
open Topology

/-- **The interface of the reduction step**: one simple transverse double point can be removed,
preserving the invariants. -/
def HasReduction (n : ℕ) (M : Type*) [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    [T2Space M] [CompactSpace M] [ConnectedSpace M] [SecondCountableTopology M] : Prop :=
  ∀ (f : M → EuclideanSpace ℝ (Fin (2 * n)))
    (hf : ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n)))) ((⊤ : ℕ∞) : WithTop ℕ∞) f)
    (himm : ∀ y, Function.Injective
      (mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n)))) f y))
    (hfin : (doubleSet f).Finite)
    (A : Set (OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n))))
    (hA : IsSmoothOrientedAtlas A) (hsimple : SimpleDP f) (htrans : TransDP A f)
    (p₁ p₂ : M) (hp₁p₂ : p₁ ≠ p₂) (hfp : f p₁ = f p₂),
    ∃ f'' : M → EuclideanSpace ℝ (Fin (2 * n)),
      ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n)))) ((⊤ : ℕ∞) : WithTop ℕ∞) f'' ∧
      (∀ y, Function.Injective
        (mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
          (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n)))) f'' y)) ∧
      (doubleSet f'').Finite ∧
      (doubleSet f'').ncard + 2 = (doubleSet f).ncard ∧
      SimpleDP f'' ∧ TransDP A f''

/-- **The endgame**: if every simple transverse double point can be removed, then a smooth
immersion `f : M → ℝ^{2n}` of a compact connected `n`-manifold (`n ≥ 3`) with finitely many
simple transverse double points can be improved to a smooth embedding. -/
theorem exists_embedding_of_reduce {n : ℕ} (hn : 3 ≤ n) {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    [T2Space M] [CompactSpace M] [ConnectedSpace M] [SecondCountableTopology M]
    (hred : HasReduction n M)
    (A : Set (OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n))))
    (hA : IsSmoothOrientedAtlas A)
    (f : M → EuclideanSpace ℝ (Fin (2 * n)))
    (hf : ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n)))) ((⊤ : ℕ∞) : WithTop ℕ∞) f)
    (himm : ∀ y, Function.Injective
      (mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n)))) f y))
    (hfin : (doubleSet f).Finite) (hsimple : SimpleDP f) (htrans : TransDP A f) :
    ∃ e : M → EuclideanSpace ℝ (Fin (2 * n)),
      ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n)))) ((⊤ : ℕ∞) : WithTop ℕ∞) e ∧
      IsEmbedding e ∧
      ∀ x : M, Function.Injective
        (mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
          (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n)))) e x) := by
  classical
  suffices H : ∀ k : ℕ, ∀ f : M → EuclideanSpace ℝ (Fin (2 * n)),
      (doubleSet f).ncard = k →
      ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n)))) ((⊤ : ℕ∞) : WithTop ℕ∞) f →
      (∀ y, Function.Injective
        (mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
          (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n)))) f y)) →
      (doubleSet f).Finite → SimpleDP f → TransDP A f →
      ∃ e : M → EuclideanSpace ℝ (Fin (2 * n)),
        ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
          (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n)))) ((⊤ : ℕ∞) : WithTop ℕ∞) e ∧
        IsEmbedding e ∧
        ∀ x : M, Function.Injective
          (mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
            (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n)))) e x) from
    H (doubleSet f).ncard f rfl hf himm hfin hsimple htrans
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro f hk hf himm hfin hsimple htrans
    by_cases hempty : (doubleSet f).Nonempty
    · obtain ⟨P, hP⟩ := hempty
      obtain ⟨hPne, hPeq⟩ := mem_doubleSet.mp hP
      obtain ⟨f'', hf''c, hf''imm, hf''fin, hcard, hsimple'', htrans''⟩ :=
        hred f hf himm hfin A hA hsimple htrans P.1 P.2 hPne hPeq
      have hk' : (doubleSet f'').ncard < k := by omega
      exact ih (doubleSet f'').ncard hk' f'' rfl hf''c hf''imm hf''fin hsimple'' htrans''
    · have hinj : Function.Injective f := by
        intro x y hxy
        by_contra hne
        exact hempty ⟨(x, y), by rw [mem_doubleSet]; exact ⟨hne, hxy⟩⟩
      exact ⟨f, hf, isEmbedding_of_injective_of_compactSpace f hf hinj, himm⟩

end Work.Whitney
