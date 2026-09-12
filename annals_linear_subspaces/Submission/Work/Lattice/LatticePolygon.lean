import Mathlib
import Submission.Work.Lattice.GraysonLattice
import Submission.Work.Lattice.LatticeDataEndpoints
import Submission.Work.Lattice.IntSubgroupCovol
import Submission.Work.Polygon.DiscreteConvex

/-!
# P1-general: per-rank Grayson data and polygon of a general lattice

For a general full-rank lattice `Λ ≤ ℝᵈ` (`finrank ℤ Λ = d`), the Grayson data of the
paper §3 is the per-rank infimum of the log-covolumes over the discrete subgroups of `Λ`,

    `rankData Λ j := sInf { log covol(W) | W ≤ Λ, dim_ℝ(span_ℝ W) = j }`,

and the **Grayson polygon** of `Λ` is the largest convex minorant of this data over
`{0,…,d}` (`largestConvexMinorant` of the discrete-convex layer):

    `polygon Λ := largestConvexMinorant d (rankData Λ)`.

This module records the definitions and the two structural lemmas that every consumer
uses:
- **rank-0 endpoint**: `rankDataSet Λ 0 = {0}` and `rankData Λ 0 = 0` (the trivial
  subgroup is the only rank-0 one, `logCovol_bot`), hence `polygon Λ 0 = 0`;
- **polygon below the data**: with `BddBelow (rankDataSet Λ j)` (per-rank data bounded
  below — automatic for the lattices of the §3 route by the discreteness of covolumes;
  kept as an explicit hypothesis until the uniform bound is recorded), every subgroup
  `W ≤ Λ` of rank `j` satisfies `polygon Λ (subDim W) ≤ log covol(W)`, and the data value
  satisfies `rankData Λ j ≤ log covol(W)`.

(All rank-`j` values are only ever used for `1 ≤ j ≤ d`; the definition is total on
`ℕ` with junk values beyond, which the hypotheses `j ≤ d` of the consumers control.)

All declarations are Mathlib + Submission.GraysonLattice + Submission.Polygon only.
-/

noncomputable section

open Set Module Real
open scoped BigOperators
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

namespace Submission.LatticePolygon

open Submission.GraysonLattice
open Submission.GraysonData
open Submission.Polygon

/-- The rank-`j` data set of a lattice `Λ ≤ ℝᵈ`: the log-covolumes of its rank-`j`
discrete subgroups. -/
def rankDataSet {d : ℕ} (Λ : Submodule ℤ (E d)) (j : ℕ) : Set ℝ :=
  {r | ∃ W : Submodule ℤ (E d), W ≤ Λ ∧ subDim W = j ∧ r = Real.log (latticeCovol W)}

/-- The rank-`j` data value of `Λ`: the infimum of the log-covolumes of its rank-`j`
discrete subgroups. -/
def rankData {d : ℕ} (Λ : Submodule ℤ (E d)) (j : ℕ) : ℝ :=
  sInf (rankDataSet Λ j)

/-- The **Grayson polygon** of `Λ`: the largest convex function on `{0,…,d}` lying below
the per-rank data `rankData Λ`. -/
def polygon {d : ℕ} (Λ : Submodule ℤ (E d)) (i : ℕ) : ℝ :=
  largestConvexMinorant (Module.finrank ℤ Λ) (rankData Λ) i

/-- The rank-`0` data set is the singleton `{0}`: the only rank-0 subgroup is `⊥` and its
Grayson value is `log 1 = 0`. -/
lemma rankDataSet_zero {d : ℕ} (Λ : Submodule ℤ (E d)) :
    rankDataSet Λ 0 = ({0} : Set ℝ) := by
  ext r
  constructor
  · rintro ⟨W, hWle, hdim, rfl⟩
    have hW0 : W = ⊥ := (subDim_eq_zero_iff_bot W).mp hdim
    subst W
    simp [logCovol_bot]
  · intro hr
    have hr0 : r = 0 := by simpa using hr
    subst r
    refine ⟨⊥, bot_le, ?_, logCovol_bot.symm⟩
    exact (subDim_eq_zero_iff_bot (⊥ : Submodule ℤ (E d))).mpr rfl

/-- The rank-`0` data value is `0`. -/
lemma rankData_zero {d : ℕ} (Λ : Submodule ℤ (E d)) : rankData Λ 0 = 0 := by
  dsimp [rankData]
  rw [rankDataSet_zero Λ]
  simp

/-- The polygon starts at `0`. -/
lemma polygon_zero {d : ℕ} (Λ : Submodule ℤ (E d)) : polygon Λ 0 = 0 := by
  dsimp [polygon]
  exact largestConvexMinorant_zero_left (Module.finrank ℤ Λ) (rankData Λ) (rankData_zero Λ)

/-- The rank-`j` data value lies below the log-covolume of any rank-`j` subgroup of `Λ`
(provided the data set is bounded below): `rankData Λ j ≤ log covol(W)`. -/
lemma rankData_le_covol {d : ℕ} (Λ : Submodule ℤ (E d)) {j : ℕ} {W : Submodule ℤ (E d)}
    (hWle : W ≤ Λ) (hdim : subDim W = j)
    (hbd : BddBelow (rankDataSet Λ j)) :
    rankData Λ j ≤ Real.log (latticeCovol W) := by
  dsimp [rankData]
  exact csInf_le hbd ⟨W, hWle, hdim, rfl⟩

/-- **Polygon below the data**: for every subgroup `W ≤ Λ` (of real dimension `j ≤ d`),
the polygon value at `j` lies below the log-covolume of `W` — the Grayson-polygon axiom
`c_Λ(dim W) ≤ φ(W)`, in the per-rank-data form (with the bounded-below hypothesis on the
data set). -/
lemma polygon_le_covol {d : ℕ} (Λ : Submodule ℤ (E d)) {W : Submodule ℤ (E d)}
    (hWle : W ≤ Λ) (hjd : subDim W ≤ Module.finrank ℤ Λ)
    (hbd : BddBelow (rankDataSet Λ (subDim W))) :
    polygon Λ (subDim W) ≤ Real.log (latticeCovol W) := by
  have h1 : polygon Λ (subDim W) ≤ rankData Λ (subDim W) := by
    dsimp [polygon]
    exact largestConvexMinorant_le_g (Module.finrank ℤ Λ) (rankData Λ) hjd
  exact le_trans h1 (rankData_le_covol Λ hWle rfl hbd)


open Submission.GraysonLattice
open Commons.Lattice.SuccessiveMinima
set_option linter.unnecessarySimpa false

/-- The real span of a `ℤ`-submodule of `ℝᵈ` has dimension at most `d`. -/
lemma subDim_le_ambient {d : ℕ} (W : Submodule ℤ (E d)) : subDim W ≤ d := by
  dsimp [subDim]
  calc
    Module.finrank ℝ (realSpan W) ≤ Module.finrank ℝ (E d) := Submodule.finrank_le (realSpan W)
    _ = d := by
          have hb := (EuclideanSpace.basisFun (Fin d) ℝ).toBasis
          simpa using (hb.finrank_eq (Fin d))

/-- **Boundedness of the rank data of the integer lattice**: `BddBelow (rankDataSet ℤᵈ j)`
(a lower bound `0`: every rank-`j` subgroup of `ℤᵈ` has covolume `≥ 1`, hence
log-covolume `≥ 0`). -/
lemma bddBelow_rankDataSet_stdIntLattice {d j : ℕ} :
    BddBelow (rankDataSet (stdIntLattice d) j) := by
  refine ⟨0, ?_⟩
  rintro r ⟨W, hWle, hdim, rfl⟩
  exact logCovol_nonneg_of_le_intLattice W hWle

/-- **Polygon below the data, no boundedness hypothesis** (integer-lattice case): for every
`W ≤ ℤᵈ`, `polygon ℤᵈ (dim W) ≤ log covol(W)`. -/
lemma polygon_le_covol_stdIntLattice {d : ℕ} {W : Submodule ℤ (E d)}
    (hWle : W ≤ stdIntLattice d)
    (hjd : subDim W ≤ Module.finrank ℤ (stdIntLattice d)) :
    polygon (stdIntLattice d) (subDim W) ≤ Real.log (latticeCovol W) :=
  polygon_le_covol (stdIntLattice d) hWle hjd (bddBelow_rankDataSet_stdIntLattice (j := subDim W))

/-- **One-sided Prop 4(2) lower bound for the integer lattice**: the Grayson polygon of
`ℤᵈ` satisfies `c(j) ≤ Σ_{i : Fin j} log λ_{i.val+1}(ℤᵈ)` for every `1 ≤ j ≤ d`
(hypothesis-free below-data via `polygon_le_covol_stdIntLattice` +
`GraysonLattice.convex_belowData_le_sum_log`). -/
theorem polygon_le_sum_log_stdIntLattice {d : ℕ} (Λ : Submodule ℤ (E d)) [DiscreteTopology Λ]
    [IsZLattice ℝ Λ] (hΛeq : Λ = stdIntLattice d) (hΛfin : Module.finrank ℤ Λ = d) {j : ℕ}
    (hj1 : 1 ≤ j) (hjd : j ≤ d) :
    polygon Λ j ≤ ∑ i : Fin j, Real.log (successiveMinimum Λ (i.val + 1)) := by
  subst Λ
  refine Submission.GraysonLattice.convex_belowData_le_sum_log (stdIntLattice d) hΛfin hj1 hjd
    (polygon (stdIntLattice d)) ?_
  intro W hWle
  exact polygon_le_covol_stdIntLattice hWle (by
    have hle : subDim W ≤ d := subDim_le_ambient W
    exact le_trans hle hΛfin.ge)

end Submission.LatticePolygon

end

