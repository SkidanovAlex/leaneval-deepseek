import Mathlib
import Submission.Work.Lattice.FiniteSaturatedHulls
import Submission.Work.Lattice.UniformBddBelow
import Submission.Work.Lattice.LatticePolygon

/-!
# Data attainment — the rank-`r` covolume-spectrum infimum is attained

With the mixed-rank covolume-spectrum discreteness closed (H1–H3, sessions 121–123:
`FiniteSaturatedHulls.finite_mixedRankSpectrum`), the ROADMAP-105 item (ii)
"attainment" of the Grayson data now follows in its strongest (exact) form: for a
full-rank lattice `Λ ≤ ℝᵈ` and every rank `0 < r ≤ d`, the rank-`r` data value

    `rankData Λ r = sInf { log covol(W) | W ≤ Λ, subDim W = r }`

is **attained** by some rank-`r` subgroup `W ≤ Λ`:

    `exists_subgroup_logCovol_eq_rankData` :
        ∃ W ≤ Λ, subDim W = r ∧ log covol(W) = rankData Λ r

**Proof.**  `S := rankDataSet Λ r` is nonempty (a rank-`r` realiser-span subgroup exists,
`GraysonLattice.exists_subgroup_covol_le_prod`) and bounded below (uniform theorem
`UniformBddBelow.rankData_bddBelow_of_lattice`).  Pick a member value `m₀ ∈ S` and
consider the finite set `B` of rank-`r` subgroups with covol `≤ e^{m₀}` (exactly the
spectrum-discreteness `finite_mixedRankSpectrum`, using `log covol ≤ m₀ ⟺ covol ≤ e^{m₀}`
from covol-positivity).  The set `T := S ∩ {x ≤ m₀}` equals the finite set of values
`{log covol(W) : W ∈ B}`, so it has a minimum `x₀`.  Then `x₀` is a lower bound of all of
`S` (members below `m₀` are in `B`, hence ≥ `x₀` by minimality; members above `m₀` are
≥ `m₀ ≥ x₀`), so `x₀ = sInf S = rankData Λ r` (`le_csInf` + `csInf_le`), and `x₀ ∈ S`
gives the realising subgroup.

This is the P2-general input: the polygon value `c(j)` at the angular ranks will be
realised (up to `O(1)`) by taking the subgroup attaining `rankData` at rank `j`
together with the `polygon ≤ rankData ≤ c` control.

All declarations are Mathlib + Submission (FiniteSaturatedHulls/UniformBddBelow/
LatticePolygon/GraysonLattice/IntrinsicIndex).
-/

noncomputable section

open Set Module Real
open scoped BigOperators
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option maxHeartbeats 800000

namespace Submission.DataAttainment

open Submission.GraysonData
open Submission.GraysonLattice
open Submission.IntrinsicIndex
open Submission.LatticePolygon
open Submission.UniformBddBelow
open Submission.FiniteSaturatedHulls
open Submission.MixedRankSpectrum

/-- Covol-positivity of the rank-`r` members: `subDim W = r` with `0 < r` and `W ≤ Λ`
force `0 < latticeCovol W`. -/
lemma covol_pos_of_rank {d r : ℕ} (Λ : Submodule ℤ (E d)) [DiscreteTopology Λ]
    [IsZLattice ℝ Λ] {W : Submodule ℤ (E d)} (hWle : W ≤ Λ) (hr0 : 0 < r)
    (hdim : subDim W = r) : 0 < latticeCovol W := by
  have hW0 : W ≠ ⊥ := by
    intro hz
    have hz' : subDim W = 0 := (subDim_eq_zero_iff_bot W).mpr hz
    omega
  exact latticeCovol_pos (d := d) Λ W hWle hW0

/-- **Data attainment**: for a full-rank lattice `Λ ≤ ℝᵈ` and a rank `0 < r ≤ d`, the
rank-`r` covolume-spectrum data value `rankData Λ r` is attained by a rank-`r` subgroup
`W ≤ Λ`: `log covol(W) = rankData Λ r`.  (The infimum over the log-covolumes is a
minimum — covolume-spectrum discreteness.) -/
theorem exists_subgroup_logCovol_eq_rankData {d r : ℕ} (Λ : Submodule ℤ (E d))
    [DiscreteTopology Λ] [IsZLattice ℝ Λ] (hr0 : 0 < r) (hrd : r ≤ d) :
    ∃ W : Submodule ℤ (E d), W ≤ Λ ∧ subDim W = r ∧
      Real.log (latticeCovol W) = rankData Λ r := by
  classical
  have hΛfin : Module.finrank ℤ Λ = d := finrank_zLattice (d := d) Λ
  let S : Set ℝ := rankDataSet Λ r
  have hbdd : BddBelow S := by
    dsimp [S]
    exact rankData_bddBelow_of_lattice Λ hΛfin r hrd
  -- nonempty: a rank-`r` subgroup exists (realiser-span block lemma)
  have hneS : S.Nonempty := by
    dsimp [S, rankDataSet]
    rcases exists_subgroup_covol_le_prod (d := d) Λ hΛfin (by omega : 1 ≤ r) hrd with
      ⟨W, hWle, hdim, _h⟩
    exact ⟨Real.log (latticeCovol W), ⟨W, hWle, hdim, rfl⟩⟩
  rcases hneS with ⟨m₀, hm₀S⟩
  -- finite set of rank-r subgroups with covol ≤ e^{m₀}
  let B : Type := {W : Submodule ℤ (E d) // W ≤ Λ ∧ subDim W = r ∧
    latticeCovol W ≤ Real.exp m₀}
  haveI : Finite B := by
    dsimp [B]
    simpa [mixedRankSpectrumStatement] using
      (finite_mixedRankSpectrum (d := d) Λ hr0 hrd (Real.exp m₀))
  -- the value set T := S ∩ {x ≤ m₀} equals the image of B under the log-covol map
  let T : Set ℝ := {x : ℝ | x ∈ S ∧ x ≤ m₀}
  have hTrange : T = Set.range (fun W : B => Real.log (latticeCovol W.1)) := by
    ext x
    constructor
    · -- x ∈ T ⟹ x = log covol of a member of B
      intro hxT
      have hxS : x ∈ S := hxT.1
      have hxm : x ≤ m₀ := hxT.2
      dsimp [S, rankDataSet] at hxS
      rcases hxS with ⟨W, hWle, hdim, rfl⟩
      -- W qualifies for B: log covol W ≤ m₀ ⟺ covol W ≤ e^{m₀}
      have hpos : 0 < latticeCovol W := covol_pos_of_rank Λ hWle hr0 hdim
      have hc : latticeCovol W ≤ Real.exp m₀ := by
        have hlog : Real.log (latticeCovol W) ≤ m₀ := hxm
        have hExp : Real.exp (Real.log (latticeCovol W)) ≤ Real.exp m₀ :=
          (Real.exp_le_exp).mpr hlog
        simpa [Real.exp_log hpos] using hExp
      refine ⟨⟨W, hWle, hdim, hc⟩, rfl⟩
    · -- x = log covol of a member of B ⟹ x ∈ T
      rintro ⟨W, rfl⟩
      have hWle : W.1 ≤ Λ := W.2.1
      have hdim : subDim W.1 = r := W.2.2.1
      have hcov : latticeCovol W.1 ≤ Real.exp m₀ := W.2.2.2
      have hpos : 0 < latticeCovol W.1 := covol_pos_of_rank Λ hWle hr0 hdim
      have hlog : Real.log (latticeCovol W.1) ≤ m₀ := by
        have hle : Real.log (latticeCovol W.1) ≤ Real.log (Real.exp m₀) :=
          Real.log_le_log hpos hcov
        simpa using hle.trans (le_of_eq (Real.log_exp m₀))
      exact ⟨⟨W.1, hWle, hdim, rfl⟩, hlog⟩
  have hTfin : T.Finite := by
    rw [hTrange]
    exact Set.finite_range (fun W : B => Real.log (latticeCovol W.1))
  have hTmem₀ : m₀ ∈ T := ⟨hm₀S, le_rfl⟩
  -- minimum of the finite nonempty value set T
  let t : Finset ℝ := hTfin.toFinset
  have htne : t.Nonempty := by
    have hmt : m₀ ∈ hTfin.toFinset := (hTfin.mem_toFinset).mpr hTmem₀
    dsimp [t]
    exact ⟨m₀, hmt⟩
  let x₀ : ℝ := t.min' htne
  have hx₀mem : x₀ ∈ T := by
    dsimp [x₀]
    exact (hTfin.mem_toFinset).mp (Finset.min'_mem t htne)
  have hx₀min : ∀ x : ℝ, x ∈ T → x₀ ≤ x := by
    intro x hxT
    dsimp [x₀]
    have hxt : x ∈ t := (hTfin.mem_toFinset).mpr hxT
    exact Finset.min'_le t x hxt
  have hx₀m₀ : x₀ ≤ m₀ := hx₀min m₀ hTmem₀
  have hx₀T : x₀ ∈ S ∧ x₀ ≤ m₀ := by
    simpa [T] using hx₀mem
  have hx₀S : x₀ ∈ S := hx₀T.1
  -- x₀ is a lower bound of all of S
  have hx₀lb : ∀ b : ℝ, b ∈ S → x₀ ≤ b := by
    intro b hbS
    by_cases hbm : b ≤ m₀
    · exact hx₀min b (by simp [T, hbS, hbm])
    · have hm₀b : m₀ < b := lt_of_not_ge hbm
      exact le_trans hx₀m₀ (le_of_lt hm₀b)
  have hle : x₀ ≤ sInf S := le_csInf ⟨m₀, hm₀S⟩ (by intro b hbS; exact hx₀lb b hbS)
  have hge : sInf S ≤ x₀ := csInf_le hbdd hx₀S
  have hx₀eq : x₀ = sInf S := le_antisymm hle hge
  -- x₀ ∈ rankDataSet Λ r gives the realising subgroup
  have hx₀data : x₀ ∈ rankDataSet Λ r := by simpa [S] using hx₀S
  rcases hx₀data with ⟨W, hWle, hdim, hx₀eqW⟩
  refine ⟨W, hWle, hdim, ?_⟩
  calc
    Real.log (latticeCovol W) = x₀ := hx₀eqW.symm
    _ = sInf S := hx₀eq
    _ = rankData Λ r := by
      dsimp [S]
      rfl

end Submission.DataAttainment
