import Mathlib
import Submission.Work.ThomBordism.absThomCompare
import Submission.Work.Tubular.exists_euclidean_normalBundle

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The norm-like function of the Euclidean normal bundle of an embedded `8`-manifold

The comparison `H^n(E⁺) ≅ H^n(E, E∖0)` of `Work.ThomBordism.absThomCompare` is stated for an
*arbitrary* real bundle over a compact Hausdorff base with a supplied norm-like function
(`Work.ThomBordism.NormLike Z`).  The normal bundle of an embedding of a closed `8`-manifold in
`ℝ^{8+k}` is, by `Work.Tubular.exists_euclidean_normalBundle`, naturally homeomorphic (with
matching fibrewise norms) to the concrete normal total space `Work.Tubular.NormalTotal E`; that
bundle is *Euclidean* in the sense of `Work.Thom.IsEuclidean`.

Here we close the loop: **a Euclidean real bundle over a compact Hausdorff base is norm-like** —
its fibrewise norm `Work.Thom.fibreNorm` is continuous (`Work.Thom.continuous_fibreNorm`),
non-negative, positively homogeneous, vanishes exactly on the zero section, and its closed unit
ball is compact (`Work.Tubular.isCompact_closedDiscSet`).  Applied to the Euclidean normal bundle
of `exists_euclidean_normalBundle`, this produces the requested norm-like function
`Work.ThomBordism.normLikeEuclideanNormal`.
-/

namespace Work.ThomBordism

open Work.TangentClasses

/-- **A Euclidean real bundle over a compact Hausdorff base is norm-like**: its fibrewise norm
`Work.Thom.fibreNorm` is a norm-like function in the sense of `Work.ThomBordism.NormLike`.

All the fields are immediate from the existing lemmas, except the compactness of the closed unit
ball, which is `Work.Tubular.isCompact_closedDiscSet`. -/
theorem nonempty_normLike_of_isEuclidean {B : Type} [TopologicalSpace B] [CompactSpace B]
    [T2Space B] {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    {ι : Type} (Z : RealBundle B F ι) (hZ : Work.Thom.IsEuclidean Z) :
    Nonempty (NormLike Z) := by
  refine ⟨{ f := Work.Thom.fibreNorm Z
          , continuous_f := Work.Thom.continuous_fibreNorm hZ
          , nonneg := ?_
          , smul := ?_
          , eq_zero := ?_
          , isCompact_le_one := ?_ }⟩
  · intro p
    exact norm_nonneg _
  · intro c hc p
    refine (Work.Thom.fibreNorm_smul (Z := Z) p.1 c (show F from p.2)).trans ?_
    rw [abs_of_nonneg hc]
  · intro p
    obtain ⟨x, v⟩ := p
    rw [Work.Thom.fibreNorm]
    exact norm_eq_zero
  · exact Work.Tubular.isCompact_closedDiscSet Z hZ

/-- **The normal bundle of an embedding of a closed `8`-manifold in `ℝ^{8+k}` carries a norm-like
function.**  The bundle `ν`, its Euclidean structure and the norm-preserving homeomorphism with the
concrete normal total space are supplied by
`Work.Tubular.exists_euclidean_normalBundle`; the norm-like function is
`nonempty_normLike_of_isEuclidean`. -/
theorem normLikeEuclideanNormal {V : Work.ThomBordism.Man8} {k : ℕ}
    (E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k)) :
    ∃ (ι : Type) (ν : Work.TangentClasses.RealBundle V.pt (Work.Tubular.Euc k) ι),
      Nonempty (Work.ThomBordism.NormLike ν) ∧
      ∃ φ : ν.TotalSpace ≃ₜ Work.Tubular.NormalTotal E,
        (∀ p : ν.TotalSpace,
          Work.Thom.fibreNorm ν p = Work.Tubular.normalNorm E (φ p)) := by
  obtain ⟨ι, ν, hEucl, φ, hφ⟩ := Work.Tubular.exists_euclidean_normalBundle E
  exact ⟨ι, ν, nonempty_normLike_of_isEuclidean ν hEucl, φ, hφ⟩

end Work.ThomBordism
