import Mathlib
import Submission.Work.Lattice.MaxPhiPolygon
import Submission.Work.Lattice.PhiPolygon
import Submission.Work.Lattice.DataAttainment
import Submission.Work.Lattice.FlowSubgroupBasis
import Submission.Work.Lattice.PolygonLipschitz

/-!
# The Euclidean and max-norm data/polygon are `A₂`-close — route 2 for the max-norm flag

Route 2 of the roadmap's max-norm-flag plan uses the **Euclidean** tight realisers (whose
existence is `PhiPolygon.exists_saturated_tight_at_angular` / `DataAttainment`) as *near-minimisers*
of the max-norm data.  The quantitative input is that the two data functions differ by at most
`A₂ d j = ½ log (choose d j) ≤ (d/2) log 2`:

* `maxRankDataSet_nonempty` — a rank-`j` subgroup of a full-rank lattice gives a family;
* **`rankData_le_maxRankData_add`** — `rankData Λ j ≤ maxRankData Λ j + A₂ d j`
  (for each `ℝ`-independent family `v` of size `j`, the subgroup `span ℤ v` has
  `log covol ≤ log cnorm(⋀v) + A₂`, via `latticeCovol_span` + `log_norm_le_log_cnorm_add`);
* **`phiData_le_maxphiData_add`** — the slacked data inequality;
* **`phiPolygon_le_maxphiPolygon_add`** — `phiPolygon Λ A j ≤ maxphiPolygon Λ A j + (d/2)log 2`
  (from `Polygon.largestConvexMinorant_le_add` with the uniform bound `A₂ d j ≤ (d/2)log 2`).

Consequently a **Euclidean-tight** saturated member `V` (i.e. `phi A V = phiPolygon Λ A (subDim V)`)
satisfies `maxPhi A V ≤ maxphiPolygon Λ A (subDim V) + (d/2)log 2` — it is a max-norm
near-minimiser with the *constant* slack `(d/2)log 2`, which the `φ`-slack `A` can absorb.

Module `Submission.Work.Lattice.MaxEuclidBridge`, namespace `Submission.MaxEuclidBridge`.
-/

noncomputable section

open Module exteriorPower InnerProductGeometry Real
open scoped BigOperators
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1000000

namespace Submission.MaxEuclidBridge

open Submission.GraysonLattice
open Submission.GraysonData
open Submission.ExteriorCoordinates
open Submission.Polygon
open Submission.LatticePolygon
open Submission.MaxNorm
open Submission.UniformBddBelow
open Submission.PhiSlack
open Submission.PhiPolygon
open Submission.MaxPhi
open Submission.MaxPhiPolygon
open Submission.MaxRankData
open Submission.MaxEuclidData

variable {d : ℕ}

/-- **Nonemptiness of the max-norm rank data.**  A rank-`j` subgroup of a full-rank lattice
(`1 ≤ j ≤ d`) provides a family of size `j`. -/
lemma maxRankDataSet_nonempty {Λ : Submodule ℤ (E d)} [DiscreteTopology Λ] [IsZLattice ℝ Λ]
    (hΛfin : Module.finrank ℤ Λ = d) {j : ℕ} (hj : 1 ≤ j) (hjd : j ≤ d) :
    (maxRankDataSet (d := d) Λ j hjd).Nonempty := by
  classical
  obtain ⟨W, hWle, hdim, -⟩ := exists_subgroup_covol_le_prod (d := d) Λ hΛfin hj hjd
  have hW0 : W ≠ ⊥ := by
    intro h
    rw [h] at hdim
    have : subDim (⊥ : Submodule ℤ (E d)) = 0 := (subDim_eq_zero_iff_bot ⊥).mpr rfl
    omega
  obtain ⟨cW, hli, hmem, -⟩ := exists_basis_family_of_le_lattice (d := d) Λ hΛfin W hWle hW0
  have hli' : LinearIndependent ℝ (fun i : Fin j => cW (Fin.cast hdim.symm i)) :=
    hli.comp (Fin.cast hdim.symm) (Fin.cast_injective hdim.symm)
  exact ⟨Real.log (cnorm hjd (exteriorPower.ιMulti ℝ j fun i => cW (Fin.cast hdim.symm i))),
    (fun i => cW (Fin.cast hdim.symm i)), fun i => hmem _, hli', rfl⟩

/-- **`rankData ≤ maxRankData + A₂`.** -/
theorem rankData_le_maxRankData_add {Λ : Submodule ℤ (E d)} [DiscreteTopology Λ]
    [IsZLattice ℝ Λ] (hΛfin : Module.finrank ℤ Λ = d) {j : ℕ} (hj : 1 ≤ j) (hjd : j ≤ d) :
    rankData Λ j ≤ maxRankData (d := d) Λ j hjd + A₂ d j := by
  classical
  have hne := maxRankDataSet_nonempty (d := d) (Λ := Λ) hΛfin hj hjd
  have hmain : rankData Λ j - A₂ d j ≤ maxRankData (d := d) Λ j hjd := by
    refine le_csInf hne (fun r hr => ?_)
    obtain ⟨v, hvmem, hvli, rfl⟩ := hr
    set W : Submodule ℤ (E d) := Submodule.span ℤ (Set.range v) with hWdef
    have hWle : W ≤ Λ := Submodule.span_le.mpr (Set.range_subset_iff.mpr hvmem)
    have hdim : subDim W = j := hWdef ▸ subDim_span_range_of_linearIndependent v hvli
    have hbdE := rankData_bddBelow_of_lattice Λ hΛfin j hjd
    have h1 : rankData Λ j ≤ Real.log (latticeCovol W) :=
      csInf_le hbdE ⟨W, hWle, hdim, rfl⟩
    have hcov : latticeCovol W = ‖exteriorPower.ιMulti ℝ j v‖ := by
      rw [hWdef]; exact latticeCovol_span (by omega) v hvli
    have h2 : Real.log (latticeCovol W) ≤
        Real.log (cnorm hjd (exteriorPower.ιMulti ℝ j v)) + A₂ d j := by
      rw [hcov, A₂]
      exact log_norm_le_log_cnorm_add hjd _
    linarith [h1, h2]
  linarith [hmain]

/-- **`phiData ≤ maxphiData + A₂`.** -/
theorem phiData_le_maxphiData_add {Λ : Submodule ℤ (E d)} [DiscreteTopology Λ]
    [IsZLattice ℝ Λ] (hΛfin : Module.finrank ℤ Λ = d) (A : ℝ) {j : ℕ} (hj : 1 ≤ j)
    (hjd : j ≤ d) :
    phiData Λ A j ≤ maxphiData (d := d) Λ A j + A₂ d j := by
  have h1 : rankData Λ j ≤ maxRankData (d := d) Λ j hjd + A₂ d j :=
    rankData_le_maxRankData_add (d := d) (Λ := Λ) hΛfin hj hjd
  have h2 : maxphiData (d := d) Λ A j =
      maxRankData (d := d) Λ j hjd + A * ((j : ℝ) * ((d : ℝ) - (j : ℝ))) := by
    rw [maxphiData, dif_pos hjd]
  rw [h2, phiData]
  linarith

/-- **The Euclidean polygon lies below the max-norm polygon plus `(d/2)log 2`.** -/
theorem phiPolygon_le_maxphiPolygon_add {Λ : Submodule ℤ (E d)} [DiscreteTopology Λ]
    [IsZLattice ℝ Λ] (hΛfin : Module.finrank ℤ Λ = d) (A : ℝ) {i : ℕ}
    (hi : i ≤ Module.finrank ℤ Λ) :
    phiPolygon Λ A i ≤ maxphiPolygon (d := d) Λ A i + (d : ℝ) * Real.log 2 / 2 := by
  have hpointwise : ∀ j : ℕ, j ≤ Module.finrank ℤ Λ →
      phiData Λ A j ≤ maxphiData (d := d) Λ A j + (d : ℝ) * Real.log 2 / 2 := by
    intro j hj
    by_cases hj0 : j = 0
    · subst hj0
      rw [maxphiData, dif_pos (Nat.zero_le d), maxRankData_eq_zero (Nat.zero_le d) rfl,
        phiData]
      have h0 : rankData Λ 0 = 0 := by
        rw [rankData, rankDataSet_zero Λ, csInf_singleton]
      rw [h0]
      have hA2 := A₂_le_log_two (d := d) (j := 0) (Nat.zero_le d)
      rw [A₂, Nat.choose_zero_right, Nat.cast_one, Real.log_one, mul_zero] at hA2
      linarith [hA2]
    · have hj1 : 1 ≤ j := Nat.one_le_iff_ne_zero.mpr hj0
      have hjd : j ≤ d := by rw [← hΛfin]; exact hj
      have hA := A₂_le_log_two (d := d) (j := j) hjd
      linarith [phiData_le_maxphiData_add (d := d) (Λ := Λ) hΛfin A hj1 hjd, hA]
  refine le_trans (largestConvexMinorant_le_add (phiData Λ A)
    (maxphiData (d := d) Λ A) hpointwise hi) ?_
  rw [maxphiPolygon]

/-- **A Euclidean-tight member is a max-norm near-minimiser.**  For a saturated `V ≤ Λ` with
`phi A V = phiPolygon Λ A (subDim V)`,

`maxPhi A V ≤ maxphiPolygon Λ A (subDim V) + (d/2)log 2`. -/
theorem maxPhi_le_maxphiPolygon_add_of_tight {Λ V : Submodule ℤ (E d)} [DiscreteTopology Λ]
    [IsZLattice ℝ Λ] (hΛfin : Module.finrank ℤ Λ = d) {A : ℝ} {hVΛ : V ≤ Λ}
    (hVtight : phi A V = phiPolygon Λ A (subDim V)) :
    maxPhi (d := d) Λ hΛfin A V hVΛ ≤
      maxphiPolygon (d := d) Λ A (subDim V) + (d : ℝ) * Real.log 2 / 2 := by
  have hi : subDim V ≤ Module.finrank ℤ Λ := by rw [hΛfin]; exact subDim_le_ambient V
  calc maxPhi (d := d) Λ hΛfin A V hVΛ ≤ phi A V := maxPhi_le_phi
    _ = phiPolygon Λ A (subDim V) := hVtight
    _ ≤ maxphiPolygon (d := d) Λ A (subDim V) + (d : ℝ) * Real.log 2 / 2 :=
        phiPolygon_le_maxphiPolygon_add (d := d) (Λ := Λ) hΛfin A hi

end Submission.MaxEuclidBridge

end
