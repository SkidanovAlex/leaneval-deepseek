import Mathlib
import Submission.Work.Drive.exists_chartedSpace_isManifold_projective

/-!
# A transparent smooth structure on the projective space `ℝPⁿ`

`Submission/Work/Drive/exists_chartedSpace_isManifold_projective` proves that
`ℝPⁿ = Projectivization ℝ (EuclideanSpace ℝ (Fin (n+1)))` carries *some* charted-space structure,
modelled on `ℝⁿ`, for which it is a smooth manifold.  That statement is an `∃`, so the structure (and
hence its charts, through which smoothness of maps *into* `ℝPⁿ` has to be checked) is opaque.

This file *defines* the structure explicitly, with the atlas `Set.range projChart` of the classical
affine charts `[v] ↦ (v_j / v_i)_{j ≠ i}` (`Work.Drive.projChart`), so that smoothness into `ℝPⁿ`
can be reduced to the concrete maps `projChartMap i`.  The proof that this structure is a smooth
manifold is the one of the existing existential statement, copied.
-/

namespace Work.Drive

open Manifold
open scoped Manifold ContDiff LinearAlgebra.Projectivization
open Set

noncomputable section

variable {n : ℕ}

/-- Every point of `ℝPⁿ` lies in one of the projective charts. -/
lemma exists_mem_projChartSource (p : Projectivization ℝ (Eucl n)) :
    ∃ i : Fin (n + 1), p ∈ projChartSource i := by
  have h : ∃ i : Fin (n + 1), p.rep.ofLp i ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    refine p.rep_nonzero ?_
    ext k
    exact hcon k
  obtain ⟨i, hi⟩ := h
  exact ⟨i, by
    rw [← Projectivization.mk_rep p]
    exact (mem_projChartSource_iff' p.rep_nonzero).mpr hi⟩

/-- **The transparent smooth structure on `ℝPⁿ`**: the charted-space structure whose atlas is the
range of the classical affine charts `projChart i`. -/
def projCharted (n : ℕ) :
    ChartedSpace (EuclideanSpace ℝ (Fin n))
      (Projectivization ℝ (EuclideanSpace ℝ (Fin (n + 1)))) where
  atlas := Set.range (projChart (n := n))
  chartAt := fun p => projChart (Classical.choose (exists_mem_projChartSource p))
  mem_chart_source := fun p => Classical.choose_spec (exists_mem_projChartSource p)
  chart_mem_atlas := fun p => Set.mem_range_self _

/-- The chart at a point of `projCharted n` is one of the projective charts. -/
lemma projCharted_chartAt_mem (n : ℕ) (p : Projectivization ℝ (Eucl n)) :
    (projCharted n).chartAt p ∈ Set.range (projChart (n := n)) :=
  Set.mem_range_self _

/-- Every chart of `projCharted n` is a projective chart, and conversely. -/
lemma projCharted_mem_atlas_iff (n : ℕ) (e : OpenPartialHomeomorph (Projectivization ℝ (Eucl n))
    (EuclideanSpace ℝ (Fin n))) :
    e ∈ @atlas _ _ _ _ (projCharted n) ↔ e ∈ Set.range (projChart (n := n)) := Iff.rfl

/-- **`ℝPⁿ` is a smooth manifold for the transparent structure `projCharted n`.** -/
theorem isManifold_projCharted (n : ℕ) :
    letI := projCharted n
    IsManifold (𝓡 n) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (Projectivization ℝ (EuclideanSpace ℝ (Fin (n + 1)))) := by
  letI : ChartedSpace (EuclideanSpace ℝ (Fin n)) (Projectivization ℝ (Eucl n)) := projCharted n
  haveI : HasGroupoid (Projectivization ℝ (Eucl n)) (contDiffGroupoid ∞ (𝓡 n)) :=
    hasGroupoid_of_pregroupoid _ (fun {e e'} he he' => by
      obtain ⟨i, rfl⟩ := he
      obtain ⟨i', rfl⟩ := he'
      have key := @contDiffOn_trans n i i'
      simpa only [contDiffPregroupoid, modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm,
        Set.range_id, Set.preimage_id, Set.inter_univ, Function.comp_def, id_eq] using key)
  exact IsManifold.mk' (𝓡 n) ∞ _

end

end Work.Drive
