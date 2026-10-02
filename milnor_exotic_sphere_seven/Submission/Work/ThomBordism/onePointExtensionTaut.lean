import Mathlib
import Submission.Work.ThomBordism.Interface
import Submission.Work.ThomBordism.PontryaginThom.Geometry
import Submission.Work.ThomBordism.PontryaginThom.NormalData
import Submission.Work.Tubular.exists_euclidean_normalBundle
import Submission.Work.Tubular.Compact
import Submission.Work.PTGeometric.PadAmb
import Submission.Work.ThomBordism.Grassmann.EvalBundle

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option maxHeartbeats 1600000

namespace Work.ThomBordism

open scoped Topology

/-- The fibrewise norm of the concrete normal total space is the norm of its normal vector. -/
theorem normalNorm_eq_norm_vec {V : Work.ThomBordism.Man8} {N : ℕ}
    (E : Work.ThomBordism.PontryaginThom.EmbeddingData V N)
    (q : Work.Tubular.NormalTotal E) :
    Work.Tubular.normalNorm E q = ‖Work.Tubular.NormalTotal.vec q‖ := rfl

/-- **A continuous map `G` out of the normal total space which realises the Gauss map pointwise is
proper**: the `evalVec` condition identifies the vector part of `G p` with the padded normal vector
of `p`, whose norm is a coercive function (the homeomorphism `eucNormalHomeomorph` carries it to
`normalNorm`, whose sublevel sets are compact). -/
theorem isCompact_preimage_of_evalVec {V : Work.ThomBordism.Man8} {k : ℕ}
    (E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k))
    (ND : Work.ThomBordism.PontryaginThom.NormalData V k E.e)
    (G : C((Work.Tubular.normalBundle E ND).TotalSpace,
        (Work.ThomBordism.Grassmann.tautologicalBundle k 10).TotalSpace))
    (heval : ∀ p, Work.ThomBordism.Grassmann.evalVec (G p)
        = Work.PTGeometric.padEuc k 10 (by norm_num)
            (Work.Tubular.NormalTotal.vec (Work.Tubular.bundleToNormal E ND p)))
    {K : Set (Work.ThomBordism.Grassmann.tautologicalBundle k 10).TotalSpace}
    (hKc : IsClosed K) (hK : IsCompact K) : IsCompact (G ⁻¹' K) := by
  -- a uniform bound for `‖evalVec‖` on `K`
  obtain ⟨M, hM⟩ : ∃ M : ℝ,
      ∀ q ∈ K, ‖Work.ThomBordism.Grassmann.evalVec q‖ ≤ M := by
    by_cases hne : K.Nonempty
    · have hcont : ContinuousOn (fun q =>
          ‖Work.ThomBordism.Grassmann.evalVec q‖) K :=
        Work.ThomBordism.Grassmann.continuous_evalVec.continuousOn.norm
      have hb : BddAbove ((fun q => ‖Work.ThomBordism.Grassmann.evalVec q‖) '' K) :=
        hK.bddAbove_image hcont
      exact ⟨sSup ((fun q => ‖Work.ThomBordism.Grassmann.evalVec q‖) '' K),
        fun q hq => le_csSup hb (Set.mem_image_of_mem _ hq)⟩
    · rw [Set.not_nonempty_iff_eq_empty] at hne
      exact ⟨0, by simp [hne]⟩
  -- the preimage lies in a compact sublevel set of the fibrewise norm
  have hsub : G ⁻¹' K ⊆ {p : (Work.Tubular.normalBundle E ND).TotalSpace |
      ‖Work.Tubular.NormalTotal.vec (Work.Tubular.bundleToNormal E ND p)‖ ≤ M} := by
    intro p hp
    have h1 : ‖Work.ThomBordism.Grassmann.evalVec (G p)‖ ≤ M := hM (G p) hp
    rw [heval p] at h1
    rwa [Work.PTGeometric.norm_padEuc] at h1
  have hcomp : IsCompact {p : (Work.Tubular.normalBundle E ND).TotalSpace |
      ‖Work.Tubular.NormalTotal.vec (Work.Tubular.bundleToNormal E ND p)‖ ≤ M} := by
    have hC : IsCompact {q : Work.Tubular.NormalTotal E | Work.Tubular.normalNorm E q ≤ M} :=
      Work.Tubular.isCompact_normalClosedDiscSet E M
    have hnorm : ∀ q : Work.Tubular.NormalTotal E,
        Work.Tubular.normalNorm E q = ‖Work.Tubular.NormalTotal.vec q‖ :=
      fun q => normalNorm_eq_norm_vec E q
    have heq : {p : (Work.Tubular.normalBundle E ND).TotalSpace |
        ‖Work.Tubular.NormalTotal.vec (Work.Tubular.bundleToNormal E ND p)‖ ≤ M}
        = (Work.Tubular.eucNormalHomeomorph E ND).symm ''
          {q : Work.Tubular.NormalTotal E | Work.Tubular.normalNorm E q ≤ M} := by
      ext p
      rw [Set.mem_setOf_eq, Set.mem_image]
      constructor
      · intro hp
        refine ⟨Work.Tubular.bundleToNormal E ND p, ?_, ?_⟩
        · rw [Set.mem_setOf_eq, hnorm]; exact hp
        · rw [← Work.Tubular.eucNormalHomeomorph_apply E ND p]
          exact (Work.Tubular.eucNormalHomeomorph E ND).symm_apply_apply p
      · rintro ⟨q, hq, hqp⟩
        rw [Set.mem_setOf_eq] at hq
        have hpq : Work.Tubular.bundleToNormal E ND p = q := by
          rw [← Work.Tubular.eucNormalHomeomorph_apply E ND p, ← hqp]
          exact (Work.Tubular.eucNormalHomeomorph E ND).apply_symm_apply q
        rw [hpq, ← hnorm]
        exact hq
    rw [heq]
    exact hC.image (Work.Tubular.eucNormalHomeomorph E ND).symm.continuous
  exact hcomp.of_isClosed_subset (hKc.preimage G.continuous) hsub

theorem onePointExtensionTaut {V : Work.ThomBordism.Man8} {k : ℕ}
    (E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k))
    (ND : Work.ThomBordism.PontryaginThom.NormalData V k E.e)
    (G : C((Work.Tubular.normalBundle E ND).TotalSpace,
        (Work.ThomBordism.Grassmann.tautologicalBundle k 10).TotalSpace))
    (heval : ∀ p, Work.ThomBordism.Grassmann.evalVec (G p)
        = Work.PTGeometric.padEuc k 10 (by norm_num)
            (Work.Tubular.NormalTotal.vec (Work.Tubular.bundleToNormal E ND p))) :
    ∃ J : C(OnePoint (Work.Tubular.normalBundle E ND).TotalSpace,
        OnePoint (Work.ThomBordism.Grassmann.tautologicalBundle k 10).TotalSpace),
      (∀ p, J (OnePoint.some p) = OnePoint.some (G p)) ∧ J OnePoint.infty = OnePoint.infty := by
  refine ⟨⟨OnePoint.map G, ?_⟩, fun p => rfl, rfl⟩
  refine OnePoint.continuous_map G.continuous ?_
  rw [(Filter.hasBasis_coclosedCompact (X := (Work.Tubular.normalBundle E ND).TotalSpace)).tendsto_iff
    (Filter.hasBasis_coclosedCompact
      (X := (Work.ThomBordism.Grassmann.tautologicalBundle k 10).TotalSpace))]
  rintro K ⟨hKc, hKcomp⟩
  exact ⟨G ⁻¹' K, ⟨hKc.preimage G.continuous,
    isCompact_preimage_of_evalVec E ND G heval hKc hKcomp⟩, fun x hx hxK => hx hxK⟩

end Work.ThomBordism
