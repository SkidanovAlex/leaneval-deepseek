import Mathlib
import Submission.Work.InnermostDisk.Slicing
import Submission.Work.InnermostDisk.Instances
import Submission.Work.Smooth.Jordan.Family
import Submission.Work.Smooth.Jordan.familyDiscs_of_schoenfliesData
import Submission.Work.Smooth.SphereJordan.RoundSphere
import Submission.Work.Smooth.Schoenflies.Unconditional
import Submission.Work.Topology.Classical.SchoenfliesSphere

/-!
# A sphere sliced by the trace curves of the surface

`Work.InnermostDisk.SphereSlicing P S` is the classical PL datum of Pardon's innermost argument:
the components of `S ∩ F` together with a disc inside `S` bounded by each of them and the nesting
of those discs.  This file *constructs* that datum from the trace data actually available in the
application: an embedded sphere `S` whose intersection with the surface `F = P.carrier` is given as
a finite union of pairwise disjoint simple closed curves `cs i` of `F`,

`S ∩ F = ⋃ i, Set.range (cs i).γ`.

Nothing beyond the trace data is assumed: the discs and their nesting come from the
Jordan–Schoenflies theorem on the sphere (`Work.Smooth.SphereJordan.jordanSchoenfliesSphere`,
unconditional in `Work.Smooth.Schoenflies.planeHypothesis`) transported to `S`
(`Work.Topology.Classical.nonempty_schoenfliesData_of_embeddedSphere`) and repackaged as
`Work.Smooth.Jordan.FamilyDiscs` (`Work.Smooth.Jordan.familyDiscs_of_schoenfliesData`); the two
*covering* clauses of `SphereSlicing` are consequences of the covering hypothesis, using that the
range of a loop is preconnected while the ranges of the `cs i` are compact and pairwise disjoint
(`Work.InnermostDisk.exists_subset_of_preconnected_iUnion`).

The `n = 0` case is not exceptional: the empty union forces `S ∩ F = ∅`, so the `covers` clause is
vacuous (a loop of `F` inside `S` would give a point of the empty union).
-/

open LeanEval.KnotTheory.PardonDistortion
open Set
open Work.CoreTopology

namespace Work.InnermostDisk

noncomputable section

theorem sphereSlicing_of_isEmbeddedSphere_of_traceCurves {P : Work.CoreTopology.ParamTorus} {S : Set LeanEval.KnotTheory.PardonDistortion.R3} (hsphere : Work.InnermostDisk.IsEmbeddedSphere S) (n : ℕ) (cs : Fin n → Work.CoreTopology.ClosedCurve P) (hsimple : ∀ i, Work.CoreTopology.IsSimple P (cs i)) (hdisj : ∀ i j, i ≠ j → Disjoint (Set.range (cs i).γ) (Set.range (cs j).γ)) (hcover : S ∩ P.carrier = ⋃ i, Set.range (cs i).γ) : Nonempty (Work.InnermostDisk.SphereSlicing P S) := by
  classical
  -- The trace curves lie in the sphere, so they are simple closed curves *on* `S`.
  have hmemS : ∀ i : Fin n, ∀ t : ℝ, (cs i).γ t ∈ S := by
    intro i t
    have h2 : (cs i).γ t ∈ S ∩ P.carrier := by
      rw [hcover]
      exact Set.mem_iUnion.mpr ⟨i, ⟨t, rfl⟩⟩
    exact h2.1
  have hsS : ∀ i : Fin n, Work.Smooth.Jordan.IsSimpleClosedCurveOn S (cs i).γ :=
    fun i => ⟨hmemS i, (cs i).cont, (cs i).periodic, hsimple i⟩
  -- Jordan–Schoenflies on the embedded sphere `S`, and the nested discs.
  have hsch : Work.Topology.Classical.SchoenfliesData S (Fin n) (fun i => (cs i).γ) :=
    (Work.Topology.Classical.nonempty_schoenfliesData_of_embeddedSphere
      (Work.Smooth.SphereJordan.jordanSchoenfliesSphere Work.Smooth.Schoenflies.planeHypothesis)
      hsphere hsS hdisj).some
  have hfd : Work.Smooth.Jordan.FamilyDiscs S (Fin n) (fun i => (cs i).γ) :=
    (Work.Smooth.Jordan.familyDiscs_of_schoenfliesData hsch hsS hdisj).some
  -- A loop of `F` inside `S` lies in one of the trace curves.
  have hcovers : ∀ γ' : Work.CoreTopology.ClosedCurve P, (∀ t : ℝ, γ'.γ t ∈ S) →
      ∃ i : Fin n, Set.range γ'.γ ⊆ Set.range (cs i).γ := by
    intro γ' hγ'
    have hK : Set.range γ'.γ ⊆ ⋃ i, Set.range (cs i).γ := by
      rintro x ⟨t, rfl⟩
      have h2 : γ' t ∈ S ∩ P.carrier := ⟨hγ' t, γ'.mem t⟩
      rwa [hcover] at h2
    exact exists_subset_of_preconnected_iUnion
      (isPreconnected_range γ'.cont) ⟨γ'.γ 0, ⟨0, rfl⟩⟩
      (fun i : Fin n => Set.range (cs i).γ)
      (fun i => isClosed_range_closedCurve (cs i)) hdisj hK
  -- The nesting clauses of the slicing.
  have hinside : ∀ i j : Fin n, (∃ z : Disc,
      ‖(z : ℂ)‖ < 1 ∧ hfd.disc i z ∈ Set.range (cs j).γ) → hfd.rank j < hfd.rank i := by
    intro i j hh
    by_cases hij : i = j
    · subst hij
      exact absurd hh (hfd.not_insideOpen_self i)
    · exact hfd.nested i j hij hh
  have hinside_subset : ∀ i j : Fin n, (∃ z : Disc,
      ‖(z : ℂ)‖ < 1 ∧ hfd.disc i z ∈ Set.range (cs j).γ) →
      Set.range (cs j).γ ⊆ Set.range (hfd.disc i) := by
    intro i j hh
    rintro x ⟨θ, rfl⟩
    exact hfd.inside_subset i j hh ⟨circlePoint θ, hfd.disc_boundary j θ⟩
  -- The interior of a disc meets `F` only along the trace curves.
  have hcovers_int : ∀ i : Fin n, ∀ z : Disc, ‖(z : ℂ)‖ < 1 →
      hfd.disc i z ∈ P.carrier → ∃ j : Fin n, hfd.disc i z ∈ Set.range (cs j).γ := by
    intro i z _ hzp
    have h2 : hfd.disc i z ∈ S ∩ P.carrier := ⟨hfd.disc_mem i z, hzp⟩
    rw [hcover] at h2
    exact Set.mem_iUnion.mp h2
  exact ⟨{ ι := Fin n
           fintype := inferInstance
           c := cs
           simple := hsimple
           disjoint := hdisj
           mem := hmemS
           covers := hcovers
           disc := hfd.disc
           disc_inj := hfd.disc_inj
           disc_boundary := hfd.disc_boundary
           disc_mem := hfd.disc_mem
           rank := hfd.rank
           inside := hinside
           inside_subset := hinside_subset
           covers_interior := hcovers_int }⟩

end

end Work.InnermostDisk
