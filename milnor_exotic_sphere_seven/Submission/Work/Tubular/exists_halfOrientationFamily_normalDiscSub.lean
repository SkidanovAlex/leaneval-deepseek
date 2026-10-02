import Mathlib
import Submission.Work.Tubular.chartedSpace_normalDisc_add
import Submission.Work.Tubular.hasCollar_normalDiscSub
import Submission.Work.Orient.Boundary
import Submission.Work.Tubular.normalDiscHalfOrientationData
import Submission.Work.Tubular.mem_boundary_normalDiscSub_add
import Submission.Work.Tubular.exists_halfOrientationFamily_euclidean
import Submission.Work.Tubular.res_pieceClass

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option backward.isDefEq.respectTransparency false

open scoped Manifold Topology
open CategoryTheory CategoryTheory.Limits

namespace Work.Tubular

theorem exists_halfOrientationFamily_normalDiscSub {V : Work.ThomBordism.Man8} {k : ℕ} [NeZero k]
    {ε : ℝ} {E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k)}
    (C : Work.Tubular.TubeChart E ε) (R : Work.Tubular.DiscManifold.HalfModelReindex k) :
    letI : ChartedSpace (EuclideanHalfSpace (7 + k + 1)) (Work.Tubular.NormalDiscSub E ε) :=
      Work.Tubular.chartedSpace_normalDisc_add C R
    ∃ γ : ∀ x : Work.Tubular.NormalDiscSub E ε,
        x ∉ (modelWithCornersEuclideanHalfSpace (7 + k + 1)).boundary (Work.Tubular.NormalDiscSub E ε) →
        Work.Orient.LocH (TopCat.of (Work.Tubular.NormalDiscSub E ε)) (7 + k + 1) x,
      Work.Orient.IsHalfOrientationFamily (7 + k) (TopCat.of (Work.Tubular.NormalDiscSub E ε)) γ := by
  classical
  letI : ChartedSpace (EuclideanHalfSpace (7 + k + 1)) (NormalDiscSub E ε) :=
    chartedSpace_normalDisc_add C R
  -- the two degrees `8 + k` and `7 + k + 1` agree
  have hdeg : (8 + k) = (7 + k + 1) := by omega
  -- the boundary of the disc bundle is the sphere bundle
  have hbd : ∀ x : NormalDiscSub E ε,
      (x ∉ (modelWithCornersEuclideanHalfSpace (7 + k + 1)).boundary (NormalDiscSub E ε))
        ↔ normalNorm E (x : NormalTotal E) < ε := by
    intro x
    rw [mem_boundary_normalDiscSub_add C R x]
    exact ⟨fun h => lt_of_le_of_ne x.2 h, fun h hb => ne_of_lt h hb⟩
  -- the Euclidean model family
  obtain ⟨γ₀, hγ₀gen, hγ₀coh⟩ := exists_halfOrientationFamily_euclidean (8 + k) (by omega)
  refine ⟨fun x hx => hdeg ▸ transferredClass C γ₀ x ((hbd x).mp hx), ?_, ?_⟩
  · -- the transferred class generates the local group
    intro x hx
    exact (span_relH_cast hdeg (transferredClass C γ₀ x ((hbd x).mp hx))).mpr
      (span_transferredClass C γ₀ hγ₀gen x ((hbd x).mp hx))
  · -- coherence over a coordinate half-ball
    intro K hK hKb
    have hK' : ∀ q ∈ K, normalNorm E (q : NormalTotal E) < ε := fun q hq => (hbd q).mp (hKb q hq)
    have hKc : IsCompact K := hK.isCompact
    have hcont : Continuous (fun q : NormalDiscSub E ε => tubeMap E (q : NormalTotal E)) :=
      (continuous_tubeMap E).comp continuous_subtype_val
    have hKimg : IsCompact (tubeImage (E := E) K) := hKc.image hcont
    obtain ⟨a', ha'⟩ := hγ₀coh (tubeImage (E := E) K) hKimg
    refine ⟨hdeg ▸ pieceClass C K hK' hKc a', ?_⟩
    intro x hx hxK
    rw [resRelH_cast (Set.singleton_subset_iff.mpr hxK) hdeg]
    exact (cast_inj' (F := fun n => (Work.Cohomology.relChains (TopCat.of (NormalDiscSub E ε))
        (discRelSub (E := E) ({x} : Set (NormalDiscSub E ε)))).homology n) hdeg).mpr
      (res_pieceClass C γ₀ hK' hKc a' ha' x hxK ((hbd x).mp hx))

end Work.Tubular
