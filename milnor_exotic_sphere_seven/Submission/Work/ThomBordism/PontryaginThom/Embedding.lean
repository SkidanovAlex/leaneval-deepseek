import Submission.Work.ThomBordism.PontryaginThom.Defs

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The embedding half of item 1

Item 1 of the chapter asks for an embedding `V ↪ ℝ^{8+k}` of each closed oriented smooth
`8`-manifold.  The **embedding theorem is in Mathlib** (Whitney's weak embedding theorem for
compact manifolds); its exact form is

```lean
public theorem exists_embedding_euclidean_of_compact
    {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type uM} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [T2Space M] [CompactSpace M] :
    ∃ (n : ℕ) (e : M → EuclideanSpace ℝ (Fin n)),
      CMDiff ∞ e ∧ IsClosedEmbedding e ∧ ∀ x : M, Injective (mfderiv% e x)
```

(`Mathlib/Geometry/Manifold/WhitneyEmbedding.lean`): a **closed** `C^∞` embedding whose derivative
is injective at every point, into `EuclideanSpace ℝ (Fin n)` for *some* `n` (not a prescribed one).
The version needed in `ℝ^{8+k}` with a prescribed codimension follows from it only after enlarging
the last coordinate, and the injection of the derivative is exactly the ``immersion'' part needed to
have a normal bundle at all.

The two other ingredients of item 1 — the **normal bundle** `ν` (of rank `n - 8`) and a **tubular
neighbourhood**, hence the collapse `S^{8+k} → Th(ν)` — are *not* in Mathlib, so they enter the
chapter as the data of `PTRep` (see `Defs.lean`); this file only records that the embedding itself
is available and in what exact form.
-/

set_option autoImplicit false

open Function Topology
open scoped Manifold ContDiff

namespace Work.ThomBordism.PontryaginThom

noncomputable section

/-- **Mathlib's Whitney embedding theorem, in the vocabulary of the project**: every closed
oriented smooth (`C^∞`) `8`-manifold embeds into `EuclideanSpace ℝ (Fin n)` for some `n`, by a
closed `C^∞` embedding with injective derivative. -/
theorem exists_embedding_of_smooth8 (M : Work.Drive.Smooth8) :
    ∃ (n : ℕ) (e : M.pt → EuclideanSpace ℝ (Fin n)),
      ContMDiff (𝓡 8) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ e ∧ IsClosedEmbedding e ∧
        ∀ x : M.pt, Injective (mfderiv (𝓡 8) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) e x) :=
  exists_embedding_euclidean_of_compact (I := 𝓡 8) (M := M.pt)

/-- **Item 1, the embedding, for the chapter's own model `Man8`** (which is `C^∞`): every
`Work.ThomBordism.Man8` embeds into `EuclideanSpace ℝ (Fin n)` for some `n`, by a closed `C^∞`
embedding with injective derivative.  The injectivity of the derivative is the "immersion" part
needed for the existence of a normal bundle at all. -/
theorem exists_embedding_man8 (V : Man8) :
    ∃ (n : ℕ) (e : V.pt → EuclideanSpace ℝ (Fin n)),
      ContMDiff (𝓡 8) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ e ∧ IsClosedEmbedding e ∧
        ∀ x : V.pt, Injective (mfderiv (𝓡 8) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) e x) :=
  exists_embedding_euclidean_of_compact (I := 𝓡 8) (M := V.pt)

end

end Work.ThomBordism.PontryaginThom
