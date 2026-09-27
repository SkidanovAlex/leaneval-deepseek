import Mathlib
import Submission.Work.Drive.ProjectiveTopology
import Submission.Work.Drive.ProjectiveDefs

/-!
# A projective line is connected

`Work.Drive.projLine U` is the set of points of the projective space represented by a non-zero vector
of the subspace `U` (`Submission/Work/Drive/ProjectiveDefs.lean`): for `finrank U = 2` in a
`3`-dimensional space it is a projective line, for `finrank U = 3` in a `4`-dimensional space a
projective plane.

This file proves that it is **preconnected** as soon as `2 ≤ finrank U` — the projective model of the
elementary fact that the complement of a point in a real vector space of dimension `> 1` is connected.
The topological structure is the quotient topology of `Submission/Work/Drive/ProjectiveTopology.lean`.

Why it matters for the chain route: the *class line* of the cut of two projective planes is
`projLine (U ⊓ ker φ)` for the `3`-plane `U` of the chart's class image and the functional `φ` of the
swept plane; since both are hyperplanes of a `4`-dimensional space, `finrank (U ⊓ ker φ) ≥ 2`, so the
class line is preconnected.  That is exactly the hypothesis `hLpre` of
`Work.Drive.diskCut_clampedSweep_eq_classCut_or_empty_of_classLine`
(`Submission/Work/Drive/cutDichotomy.lean`): the *sign rigidity* of the cut is then free of any
connectedness assumption on the disk-level class-cut.

All declarations are sorry-free and rest only on `propext`, `Classical.choice` and `Quot.sound`.
-/

namespace Work.Drive

open scoped LinearAlgebra.Projectivization

noncomputable section

/-- **The non-zero vectors of a subspace of dimension `≥ 2` form a preconnected set**: the complement
of the origin in a real vector space of rank `> 1` is path connected
(`isPathConnected_compl_singleton_of_one_lt_rank`, transported along the coe `U → V`). -/
theorem isPreconnected_coe_compl_singleton {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (U : Submodule ℝ V) (hU : 2 ≤ Module.finrank ℝ U) :
    IsPreconnected {v : V | v ∈ U ∧ v ≠ 0} := by
  have hrank : 1 < Module.rank ℝ U :=
    Module.one_lt_rank_of_one_lt_finrank (by omega)
  have hpc : IsPreconnected ({0}ᶜ : Set U) :=
    (isPathConnected_compl_singleton_of_one_lt_rank hrank 0).isConnected.isPreconnected
  have : PreconnectedSpace ↥({0}ᶜ : Set U) := isPreconnected_iff_preconnectedSpace.mp hpc
  have himg : IsPreconnected (Set.range fun p : ↥({0}ᶜ : Set U) => (((p.1 : U)) : V)) :=
    isPreconnected_range (continuous_subtype_val.comp continuous_subtype_val)
  have hset : Set.range (fun p : ↥({0}ᶜ : Set U) => (((p.1 : U)) : V))
      = {v : V | v ∈ U ∧ v ≠ 0} := by
    ext v
    constructor
    · rintro ⟨p, rfl⟩
      refine ⟨p.1.2, ?_⟩
      intro h
      exact p.2 (by simpa using h : (p.1 : U) = 0)
    · rintro ⟨hvU, hv0⟩
      refine ⟨⟨⟨v, hvU⟩, ?_⟩, rfl⟩
      simpa using hv0
  rwa [hset] at himg

/-- **A projective line (or plane) is preconnected.** -/
theorem isPreconnected_projLine {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (U : Submodule ℝ V) (hU : 2 ≤ Module.finrank ℝ U) :
    IsPreconnected (projLine U) := by
  have hpc : IsPreconnected {v : V | v ∈ U ∧ v ≠ 0} := isPreconnected_coe_compl_singleton U hU
  have : PreconnectedSpace ↥{v : V | v ∈ U ∧ v ≠ 0} := isPreconnected_iff_preconnectedSpace.mp hpc
  have hf : Continuous fun p : ↥{v : V | v ∈ U ∧ v ≠ 0} =>
      Projectivization.mk ℝ p.1 p.2.2 :=
    (continuous_projectivizationMk ℝ V).comp
      (Continuous.subtype_mk continuous_subtype_val fun p => p.2.2)
  have hrange : Set.range (fun p : ↥{v : V | v ∈ U ∧ v ≠ 0} =>
      Projectivization.mk ℝ p.1 p.2.2) = projLine U := by
    ext q
    constructor
    · rintro ⟨p, rfl⟩
      exact ⟨p.1, p.2.2, p.2.1, rfl⟩
    · rintro ⟨v, hv, hvU, rfl⟩
      exact ⟨⟨v, hvU, hv⟩, rfl⟩
  rw [← hrange]
  exact isPreconnected_range hf

/-- **The class line of a cut of two projective planes in `ℝP³` is preconnected.**  For two
`3`-dimensional subspaces `U`, `W` of the `4`-dimensional `Eucl 3` (the class image of the chart and
the normal hyperplane of the swept plane) one has `finrank (U ⊓ W) ≥ 3 + 3 − 4 = 2`, so
`projLine (U ⊓ W)` — the class line `projLine U ∩ projLine W` of the cut, by
`Work.Drive.projLine_inf_eq` — is preconnected.  This discharges the hypothesis `hLpre` of
`Work.Drive.diskCut_clampedSweep_eq_classCut_or_empty_of_classLine` in the design. -/
theorem isPreconnected_projLine_inf {U W : Submodule ℝ (Eucl 3)}
    (hU : Module.finrank ℝ U = 3) (hW : Module.finrank ℝ W = 3) :
    IsPreconnected (projLine (U ⊓ W)) := by
  apply isPreconnected_projLine
  have hsup := Submodule.finrank_sup_add_finrank_inf_eq U W
  have hle : Module.finrank ℝ ↥(U ⊔ W : Submodule ℝ (Eucl 3)) ≤ 4 :=
    calc Module.finrank ℝ ↥(U ⊔ W : Submodule ℝ (Eucl 3))
        ≤ Module.finrank ℝ (Eucl 3) := Submodule.finrank_le _
      _ = 4 := finrank_euclideanSpace_fin
  omega

end

end Work.Drive
