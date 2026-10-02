import Mathlib
import Submission.Work.Tubular.mem_boundary_normalDiscSub
import Submission.Work.Tubular.DiscManifold.Manifold

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The normal disc bundle as a charted space modelled on `EuclideanHalfSpace (7 + k + 1)`

`Work.Tubular.nonempty_normalDiscManifold_of_tubeChart` (and
`Work.Tubular.disc_isManifold_half`, on which it rests) produce the manifold structure of the normal
disc bundle `D_ε(ν)` of an embedding `E : V ↪ ℝ^{8+k}` at the model space
`EuclideanHalfSpace (8 + k)`.

Some consumers (`Work.Surgery.HasCollar`, whose model is `𝓡∂ (n+1)`) read that structure at the
numerically equal, but not definitionally equal, index `7 + k + 1` instead.  Since
`EuclideanHalfSpace` is a function of its index, the two model spaces are canonically homeomorphic
by relabelling the coordinates of `ℝ^{7+k+1} = ℝ^{8+k}`; this file constructs that homeomorphism
(`nonempty_halfSpaceHomeomorph_of_eq`) and transfers the charted space across it
(`Work.Tubular.chartedSpaceOfModelHomeo`), proving
`Work.Tubular.exists_chartedSpace_normalDisc_add`.

The relabelling `e : Fin m ≃ Fin n` used must fix the `0`-th coordinate, because the half-space
condition is the condition `0 ≤ x 0` on the `0`-th coordinate; for `m = 7 + k + 1`, `n = 8 + k` the
canonical `finCongr` does fix it.
-/

open scoped Manifold ContDiff Topology

namespace Work.Tubular

noncomputable section

/-- **The half-space model depends on its index only up to relabelling of the coordinates.**

A bijection `e : Fin m ≃ Fin n` of the coordinate sets that fixes the `0`-th coordinate induces a
homeomorphism `EuclideanHalfSpace m ≃ₜ EuclideanHalfSpace n`: it is the linearly isometric
relabelling `LinearIsometryEquiv.piLpCongrLeft` of the ambient Euclidean spaces, which preserves the
half-space condition `0 ≤ x 0`. -/
theorem nonempty_halfSpaceHomeomorph {m n : ℕ} [NeZero m] [NeZero n] (e : Fin m ≃ Fin n)
    (he : e.symm 0 = 0) : Nonempty (EuclideanHalfSpace m ≃ₜ EuclideanHalfSpace n) := by
  -- the relabelling of the ambient Euclidean spaces
  let φ : EuclideanSpace ℝ (Fin m) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n) :=
    LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ e
  -- its coordinate formula
  have hφ : ∀ (v : EuclideanSpace ℝ (Fin m)) (i : Fin n), (φ v).ofLp i = v.ofLp (e.symm i) := by
    intro v i
    simp [φ, LinearIsometryEquiv.piLpCongrLeft_apply, Equiv.piCongrLeft'_apply]
  -- the half-space condition is preserved, because the `0`-th coordinate is
  have h0 : ∀ v : EuclideanSpace ℝ (Fin m), 0 ≤ (φ v) 0 ↔ 0 ≤ v 0 := by
    intro v
    rw [hφ v 0, he]
  refine ⟨{ toFun := fun x => ⟨φ x.val, (h0 x.val).mpr x.property⟩
            invFun := fun y => ⟨φ.symm y.val, ?_⟩
            left_inv := ?_
            right_inv := ?_
            continuous_toFun := ?_
            continuous_invFun := ?_ }⟩
  · -- the inverse lands in the half space, because `φ` is a bijection preserving the condition
    refine (h0 (φ.symm y.val)).mp ?_
    rw [LinearIsometryEquiv.apply_symm_apply]
    exact y.property
  · intro x
    exact Subtype.ext (LinearIsometryEquiv.symm_apply_apply φ x.val)
  · intro y
    exact Subtype.ext (LinearIsometryEquiv.apply_symm_apply φ y.val)
  · exact Continuous.subtype_mk (φ.continuous.comp continuous_subtype_val) _
  · exact Continuous.subtype_mk (φ.symm.continuous.comp continuous_subtype_val) _

/-- The case of `nonempty_halfSpaceHomeomorph` relevant here: two equal indices give homeomorphic
half-space models, via the canonical relabelling `finCongr` (which fixes `0`). -/
theorem nonempty_halfSpaceHomeomorph_of_eq {m n : ℕ} [NeZero m] [NeZero n] (h : m = n) :
    Nonempty (EuclideanHalfSpace m ≃ₜ EuclideanHalfSpace n) :=
  nonempty_halfSpaceHomeomorph (finCongr h) (by
    rw [finCongr_symm_apply]
    exact Fin.cast_zero _)

/-- **The normal disc bundle is a charted space modelled on `EuclideanHalfSpace (7 + k + 1)`.**

This is the charted space of `D_ε(ν)` built from the tube chart `C` and the reindexing `R` (the
one that `Work.Tubular.disc_isManifold_half` and `Work.Tubular.nonempty_normalDiscManifold_of_tubeChart`
use, at the model `EuclideanHalfSpace (8 + k)`), read at the numerically equal index `7 + k + 1`
along the canonical homeomorphism of the model spaces `nonempty_halfSpaceHomeomorph_of_eq`. -/
theorem exists_chartedSpace_normalDisc_add {V : Work.ThomBordism.Man8} {k : ℕ} [NeZero k] {ε : ℝ}
    {E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k)}
    (C : Work.Tubular.TubeChart E ε) (R : Work.Tubular.DiscManifold.HalfModelReindex k) :
    Nonempty (ChartedSpace (EuclideanHalfSpace (7 + k + 1)) (Work.Tubular.NormalDiscSub E ε)) := by
  obtain ⟨Ψ⟩ := nonempty_halfSpaceHomeomorph_of_eq (show 7 + k + 1 = 8 + k by omega)
  exact ⟨chartedSpaceOfModelHomeo (chartedSpaceOfModelHomeo (discChartedSpace C) R.Λ) Ψ⟩

end

end Work.Tubular
