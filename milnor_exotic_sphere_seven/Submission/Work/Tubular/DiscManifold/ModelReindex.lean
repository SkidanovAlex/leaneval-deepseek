import Mathlib
import Submission.Work.SignatureBordism.BallBoundary

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-!
# The reindexing of the product model of the normal disc bundle

The normal disc bundle `D_ε(ν)` of an embedding `V ↪ ℝ^{8+k}` is, over a chart of `V`, a product
`ℝ^8 × D^k`: it is naturally a charted space modelled on `ℝ^8 × Half (k-1)`, with the product model
`(𝓡 8).prod (hModel (k-1))` of Mathlib.  Its *stated* model, however, is the half-space
`EuclideanHalfSpace (8+k)` (see `Work.Tubular.NormalDiscManifold`), so one needs the linear
reindexing

  `EuclideanHalfSpace (8 + k) ≃ₜ ℝ^8 × Half (k-1)`,

which puts the **first `k`** coordinates of `ℝ^{8+k}` in the fibre factor (`Half (k-1)`) — so that
the half-space condition sits in the fibre direction, as the geometry dictates — and the remaining
`8` coordinates in the base factor.

`HalfModelReindex` packages that reindexing together with the two continuous linear maps realizing
it (`split` and `join`) and the characteristic formulas used in the transition computation; its
existence is `Work.Tubular.DiscManifold.exists_halfModelReindex`.
-/

open scoped Manifold ContDiff Topology

namespace Work.Tubular.DiscManifold

open Work.SignatureBordism

/-- **The reindexing of the product model of the disc bundle.**  `Λ` is the homeomorphism
`EuclideanHalfSpace (8+k) ≃ₜ ℝ^8 × Half (k-1)`; `split` and `join` are the underlying continuous
linear maps on the ambient spaces, and the fields record that `Λ` is the split (in particular the
`0`-th coordinate of `ℝ^{8+k}` becomes the `0`-th coordinate of the *fibre* factor, which is what
makes the half-space condition transfer). -/
structure HalfModelReindex (k : ℕ) [NeZero k] where
  /-- the homeomorphism of model spaces -/
  Λ : EuclideanHalfSpace (8 + k) ≃ₜ
    (EuclideanSpace ℝ (Fin 8) × EuclideanHalfSpace ((k - 1) + 1))
  /-- the "split" of the ambient space, into the base and the fibre part -/
  split : EuclideanSpace ℝ (Fin (8 + k)) →L[ℝ]
    (EuclideanSpace ℝ (Fin 8) × EuclideanSpace ℝ (Fin ((k - 1) + 1)))
  /-- the "assembly", inverse to the split -/
  join : (EuclideanSpace ℝ (Fin 8) × EuclideanSpace ℝ (Fin ((k - 1) + 1))) →L[ℝ]
    EuclideanSpace ℝ (Fin (8 + k))
  /-- the fibre part of the split carries the `0`-th coordinate of `ℝ^{8+k}` -/
  split_snd_zero : ∀ x : EuclideanSpace ℝ (Fin (8 + k)), (split x).2 0 = x 0
  /-- the base part of `Λ` is the base part of the split -/
  Λ_fst : ∀ x : EuclideanHalfSpace (8 + k), (Λ x).1 = (split x.val).1
  /-- the fibre part of `Λ` is the fibre part of the split -/
  Λ_snd_val : ∀ x : EuclideanHalfSpace (8 + k),
    ((Λ x).2 : EuclideanHalfSpace ((k - 1) + 1)).val = (split x.val).2
  /-- the inverse of `Λ` is the assembly -/
  Λ_symm_val : ∀ (a : EuclideanSpace ℝ (Fin 8)) (b : EuclideanHalfSpace ((k - 1) + 1)),
    ((Λ.symm (a, b)).val) = join (a, b.val)

end Work.Tubular.DiscManifold
