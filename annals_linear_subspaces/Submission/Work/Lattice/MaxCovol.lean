import Mathlib
import Submission.Work.Lattice.MaxRankData
import Submission.Work.Lattice.IntrinsicIndex
import Submission.Work.Lattice.PresentationLattice

/-!
# The intrinsic max-norm covolume of a subgroup, and its comparison with the Euclidean one

For the max-norm `φ`-theory (the flag of the §3 flow lattice, see the roadmap) one needs the
`cnorm`-analogue of the intrinsic covolume `latticeCovol`:

`maxCovol X` := the `log cnorm` of the wedge of a presentation family of the subgroup
`X ≤ Λ` (`PresentationLattice.exists_basis_family_of_le_lattice`; any two presentation families
differ by an integer matrix with determinant `±1`, so `cnorm (⋀·)` does not depend on the
choice).

The two comparison lemmas with the Euclidean `latticeCovol` are

* `maxCovol_le_log_latticeCovol` : `maxCovol X ≤ log (latticeCovol X)`  (`cnorm ≤ ‖·‖`);
* `log_latticeCovol_le_maxCovol_add` : `log (latticeCovol X) ≤ maxCovol X + ½log (choose d j)`
  (`‖·‖ ≤ √(choose d j)·cnorm`).

Module `Submission.Work.Lattice.MaxCovol`, namespace `Submission.MaxCovol`.
-/

noncomputable section

open Module exteriorPower InnerProductGeometry Real
open scoped BigOperators
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1000000

namespace Submission.MaxCovol

open Submission.GraysonLattice
open Submission.GraysonData
open Submission.ExteriorCoordinates
open Submission.MaxNorm
open Submission.MaxNormFlow
open Submission.MaxEuclidData
open Submission.LatticePolygon

variable {d : ℕ}

/-- The presentation family used to define `maxCovol`. -/
noncomputable def presFam (Λ : Submodule ℤ (E d)) [DiscreteTopology Λ] [IsZLattice ℝ Λ]
    (hΛfin : Module.finrank ℤ Λ = d) (X : Submodule ℤ (E d)) (hXΛ : X ≤ Λ) (hX0 : X ≠ ⊥) :
    Fin (subDim X) → E d :=
  Classical.choose (exists_basis_family_of_le_lattice (d := d) Λ hΛfin X hXΛ hX0)

lemma presFam_linearIndependent {Λ : Submodule ℤ (E d)} [DiscreteTopology Λ]
    [IsZLattice ℝ Λ] {hΛfin : Module.finrank ℤ Λ = d} {X : Submodule ℤ (E d)} {hXΛ : X ≤ Λ}
    {hX0 : X ≠ ⊥} : LinearIndependent ℝ (presFam (d := d) Λ hΛfin X hXΛ hX0) :=
  (Classical.choose_spec (exists_basis_family_of_le_lattice (d := d) Λ hΛfin X hXΛ hX0)).1

lemma presFam_mem {Λ : Submodule ℤ (E d)} [DiscreteTopology Λ] [IsZLattice ℝ Λ]
    {hΛfin : Module.finrank ℤ Λ = d} {X : Submodule ℤ (E d)} {hXΛ : X ≤ Λ} {hX0 : X ≠ ⊥} :
    ∀ r, presFam (d := d) Λ hΛfin X hXΛ hX0 r ∈ (Λ : Set (E d)) :=
  (Classical.choose_spec (exists_basis_family_of_le_lattice (d := d) Λ hΛfin X hXΛ hX0)).2.1

lemma presFam_span {Λ : Submodule ℤ (E d)} [DiscreteTopology Λ] [IsZLattice ℝ Λ]
    {hΛfin : Module.finrank ℤ Λ = d} {X : Submodule ℤ (E d)} {hXΛ : X ≤ Λ} {hX0 : X ≠ ⊥} :
    X = Submodule.span ℤ (Set.range (presFam (d := d) Λ hΛfin X hXΛ hX0)) :=
  (Classical.choose_spec (exists_basis_family_of_le_lattice (d := d) Λ hΛfin X hXΛ hX0)).2.2

lemma presFam_mem_self {Λ : Submodule ℤ (E d)} [DiscreteTopology Λ] [IsZLattice ℝ Λ]
    {hΛfin : Module.finrank ℤ Λ = d} {X : Submodule ℤ (E d)} {hXΛ : X ≤ Λ} {hX0 : X ≠ ⊥}
    (i : Fin (subDim X)) : presFam (d := d) Λ hΛfin X hXΛ hX0 i ∈ X := by
  have h := presFam_span (d := d) (Λ := Λ) (hΛfin := hΛfin) (X := X) (hXΛ := hXΛ) (hX0 := hX0)
  exact h.ge (Submodule.subset_span (Set.mem_range_self i))

/-- The **intrinsic max-norm covolume** of a subgroup `X` of a full-rank lattice `Λ`
(`0` for `X = ⊥`). -/
noncomputable def maxCovol (Λ : Submodule ℤ (E d)) [DiscreteTopology Λ] [IsZLattice ℝ Λ]
    (hΛfin : Module.finrank ℤ Λ = d) (X : Submodule ℤ (E d)) (hXΛ : X ≤ Λ) : ℝ :=
  if h : X = ⊥ then 0
  else Real.log (cnorm (subDim_le_ambient X)
    (exteriorPower.ιMulti ℝ (subDim X) (presFam (d := d) Λ hΛfin X hXΛ h)))

/-- The Euclidean covolume of `X` in terms of the presentation family. -/
lemma latticeCovol_eq_norm_presFam {Λ : Submodule ℤ (E d)} [DiscreteTopology Λ]
    [IsZLattice ℝ Λ] {hΛfin : Module.finrank ℤ Λ = d} {X : Submodule ℤ (E d)} {hXΛ : X ≤ Λ}
    {hX0 : X ≠ ⊥} :
    latticeCovol X = ‖exteriorPower.ιMulti ℝ (subDim X)
      (presFam (d := d) Λ hΛfin X hXΛ hX0)‖ := by
  have hr : 0 < subDim X := by
    by_contra h
    have hz : subDim X = 0 := by omega
    exact hX0 ((subDim_eq_zero_iff_bot X).mp hz)
  have h := latticeCovol_span (d := d) (r := subDim X) hr _ (presFam_linearIndependent (d := d)
    (Λ := Λ) (hΛfin := hΛfin) (X := X) (hXΛ := hXΛ) (hX0 := hX0))
  have h2 := congrArg (fun Y : Submodule ℤ (E d) => latticeCovol Y)
    (presFam_span (d := d) (Λ := Λ) (hΛfin := hΛfin) (X := X) (hXΛ := hXΛ) (hX0 := hX0))
  rw [h2]
  exact h

/-- **`maxCovol X ≤ log (latticeCovol X)`** (`cnorm ≤ ‖·‖`). -/
theorem maxCovol_le_log_latticeCovol {Λ : Submodule ℤ (E d)} [DiscreteTopology Λ]
    [IsZLattice ℝ Λ] {hΛfin : Module.finrank ℤ Λ = d} {X : Submodule ℤ (E d)} {hXΛ : X ≤ Λ} :
    maxCovol (d := d) Λ hΛfin X hXΛ ≤ Real.log (latticeCovol X) := by
  rw [maxCovol]
  by_cases h : X = ⊥
  · rw [dif_pos h, h]
    rw [logCovol_bot]
  · rw [dif_neg h,
      latticeCovol_eq_norm_presFam (d := d) (Λ := Λ) (hΛfin := hΛfin) (X := X)
        (hXΛ := hXΛ) (hX0 := h)]
    exact log_cnorm_le_log_norm (subDim_le_ambient X) _

/-- **`log (latticeCovol X) ≤ maxCovol X + ½log (choose d (subDim X))`**
(`‖·‖ ≤ √(choose d j)·cnorm`). -/
theorem log_latticeCovol_le_maxCovol_add {Λ : Submodule ℤ (E d)} [DiscreteTopology Λ]
    [IsZLattice ℝ Λ] {hΛfin : Module.finrank ℤ Λ = d} {X : Submodule ℤ (E d)} {hXΛ : X ≤ Λ} :
    Real.log (latticeCovol X) ≤ maxCovol (d := d) Λ hΛfin X hXΛ +
      (1 / 2) * Real.log (Nat.choose d (subDim X)) := by
  rw [maxCovol]
  by_cases h : X = ⊥
  · rw [dif_pos h, h, logCovol_bot]
    have h0 : subDim (⊥ : Submodule ℤ (E d)) = 0 := (subDim_eq_zero_iff_bot ⊥).mpr rfl
    rw [h0]
    simp
  · rw [dif_neg h,
      latticeCovol_eq_norm_presFam (d := d) (Λ := Λ) (hΛfin := hΛfin) (X := X)
        (hXΛ := hXΛ) (hX0 := h)]
    exact log_norm_le_log_cnorm_add (subDim_le_ambient X) _

end Submission.MaxCovol

end
