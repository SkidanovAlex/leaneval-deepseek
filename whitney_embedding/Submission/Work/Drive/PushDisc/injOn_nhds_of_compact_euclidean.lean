import Mathlib
import Submission.Work.Embedding.immersion_locally_injective
import Submission.Work.Routing.injOn_nhds_of_compact_of_locallyInjOn
import Submission.Work.Drive.Whitney.modelChart

/-!
# The Euclidean form of `injOn_nhds_of_compact_injOn`

The `θ`-assembly of the framing chart produces a diffeo `θ` of the model space
`Mdl k = ℝ × ℝ × ℝ^k × ℝ^k` which, on the plane `{u = 0, v = 0}`, is the disc approximation `Δ`;
`θ` is a local diffeo along `K̂ = {(x,y,0,0)}` and `Δ` is injective on the lens `K_c`.  Hence `θ` is
injective on a *neighbourhood* of `K̂`, which is what the globalisation (L5) needs.

This file records the Euclidean form of that point-set step (the manifold form is
`Work.Drive.PushDisc.injOn_nhds_of_compact_injOn`), assembled from two proved bricks:

* `Work.Embedding.local_injOn_of_injective_fderiv` (local injectivity from an injective derivative);
* `Work.Routing.injOn_nhds_of_compact_of_locallyInjOn` (local injectivity at a compact set + injective
  there + continuous there ⟹ injective on a neighbourhood).
-/

namespace Work.Drive.PushDisc

open scoped ContDiff

/-- **A `C^∞` map with injective derivative everywhere, injective on a compact set, is injective on
an open neighbourhood of it.** -/
theorem injOn_nhds_of_compact_injOn_euclidean {n N : ℕ}
    (F : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin N))
    (hF : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) F)
    (himm : ∀ x, Function.Injective (fderiv ℝ F x))
    (K : Set (EuclideanSpace ℝ (Fin n))) (hKc : IsCompact K) (hKinj : Set.InjOn F K) :
    ∃ O : Set (EuclideanSpace ℝ (Fin n)), IsOpen O ∧ K ⊆ O ∧ Set.InjOn F O := by
  refine Work.Routing.injOn_nhds_of_compact_of_locallyInjOn hKc ?_ ?_ hKinj
  · intro x _
    exact Work.Embedding.local_injOn_of_injective_fderiv (V := Set.univ) isOpen_univ
      (Set.mem_univ x) hF.contDiffOn (himm x)
  · intro x _
    exact hF.continuous.continuousAt

end Work.Drive.PushDisc

namespace Work.Drive.PushDisc

/-- **The local form** (the derivative is assumed injective only at the points of `K`), which is the
form the `θ`-assembly uses. -/
theorem injOn_nhds_of_compact_injOn_euclidean_local {n N : ℕ}
    (F : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin N))
    (hF : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) F)
    (K : Set (EuclideanSpace ℝ (Fin n))) (hKc : IsCompact K)
    (himm : ∀ x ∈ K, Function.Injective (fderiv ℝ F x))
    (hKinj : Set.InjOn F K) :
    ∃ O : Set (EuclideanSpace ℝ (Fin n)), IsOpen O ∧ K ⊆ O ∧ Set.InjOn F O := by
  refine Work.Routing.injOn_nhds_of_compact_of_locallyInjOn hKc ?_ ?_ hKinj
  · intro x hx
    exact Work.Embedding.local_injOn_of_injective_fderiv (V := Set.univ) isOpen_univ
      (Set.mem_univ x) hF.contDiffOn (himm x hx)
  · intro x _
    exact hF.continuous.continuousAt

/-- **The general form used by the `θ`-assembly**: a `C^∞` self-map of `ℝ^m` that is injective on a
compact set and has an invertible derivative at each of its points is injective on a neighbourhood of
it.  (The consumer derives `Set.InjOn θ S` from `θ (x,y,0,0) = Δ (x,y)` and the injectivity of `Δ`.) -/
theorem exists_isOpen_injOn_of_compact_injOn {m : ℕ}
    (θ : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin m))
    (hθ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) θ)
    (S : Set (EuclideanSpace ℝ (Fin m))) (hSc : IsCompact S)
    (hθS : Set.InjOn θ S)
    (hdθ : ∀ ξ ∈ S, Function.Injective (fderiv ℝ θ ξ)) :
    ∃ O : Set (EuclideanSpace ℝ (Fin m)), IsOpen O ∧ S ⊆ O ∧ Set.InjOn θ O :=
  injOn_nhds_of_compact_injOn_euclidean_local θ hθ S hSc hdθ hθS

end Work.Drive.PushDisc
