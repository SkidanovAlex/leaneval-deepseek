import Mathlib
import Submission.Work.Serre.Engine
import Submission.Work.RatHurewicz.RelHomotopy
import Submission.Work.Serre.mpathQ_isSerreFibration
import Submission.Work.Serre.mpathQ_fibreHomeo
import Submission.Work.Serre.ratFibreTransport
import Submission.Work.Stems.mappingTheoremOfHomotopyFibreAcyclic
import Submission.Work.Serre.OneCell.Prelim

/-!
# Rational acyclicity of the homotopy fibre is independent of the base point

The homotopy fibre of a map `f : A → X` over a point `a : A` depends on `a`, but its rational
homology does not depend on the path component of `a` in `A`:

`Work.Rat.homotopyFibre_ratAcyclicBelow_of_path`.

The proof replaces `f` by a fibration.  The mapping path space `Work.Serre.mpath f` has the
projection `Work.Serre.mpathQ f : mpath f → X`, which is a Serre fibration
(`Work.Serre.mpathQ_isSerreFibration`) for *every* `f`, and the strict fibre of `mpathQ f` over
`f a` is homeomorphic to the homotopy fibre of `f` at `a` (`Work.Serre.mpathQ_fibreHomeo`).

For a path `η : Path a₀ a₁` in `A`, the path `f ∘ η` in `X` joins `f a₀` and `f a₁`; the fibres of
the Serre fibration `mpathQ f` over the two ends of a path have isomorphic rational homology
`Work.Serre.ratH_fibre_iso_of_path`, whence so do `H_*(homotopyFibre f a₀;ℚ)` and
`H_*(homotopyFibre f a₁;ℚ)` in every degree, and the conclusion follows from
`Work.Stems.ratAcyclicBelow_of_ratH_iso`.
-/

namespace Work.Rat

open scoped Topology unitInterval

theorem homotopyFibre_ratAcyclicBelow_of_path {A X : Type} [TopologicalSpace A] [TopologicalSpace X]
    (f : C(A, X)) {a₀ a₁ : A} (η : Path a₀ a₁) {N : ℕ}
    (h : Work.Serre.RatAcyclicBelow (Work.RatHurewicz.homotopyFibre f a₀) N) :
    Work.Serre.RatAcyclicBelow (Work.RatHurewicz.homotopyFibre f a₁) N := by
  refine Work.Stems.ratAcyclicBelow_of_ratH_iso h (fun j => ?_)
  -- `mpathQ f` is a Serre fibration, and the path `f ∘ η` joins the two relevant base points
  have hp : Work.StemsB.IsSerreFibration (Work.Serre.mpathQ f) :=
    Work.Serre.mpathQ_isSerreFibration f
  have hγ0 : ((η.map f.continuous).toContinuousMap : C(unitInterval, X)) 0 = f a₀ := by simp
  have hγ1 : ((η.map f.continuous).toContinuousMap : C(unitInterval, X)) 1 = f a₁ := by simp
  obtain ⟨emid⟩ := Work.Serre.ratH_fibre_iso_of_path (Work.Serre.mpathQ f) hp
    ((η.map f.continuous).toContinuousMap) j
  rw [hγ0, hγ1] at emid
  -- and the strict fibre of `mpathQ f` over `f a` is the homotopy fibre of `f` at `a`
  obtain ⟨e₀⟩ := Work.Serre.mpathQ_fibreHomeo f a₀
  obtain ⟨e₁⟩ := Work.Serre.mpathQ_fibreHomeo f a₁
  exact ⟨(Work.Serre.OneCell.nonempty_ratH_iso_of_homeo e₀.symm j).some ≪≫
    emid ≪≫ (Work.Serre.OneCell.nonempty_ratH_iso_of_homeo e₁ j).some⟩

end Work.Rat
