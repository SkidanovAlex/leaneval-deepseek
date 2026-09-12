import Mathlib
import Submission.Work.Polygon.DataTightness
import Submission.Work.Polygon.AngularRanks
import Submission.Work.Lattice.LatticePolygon
import Submission.Work.Lattice.DataAttainment

/-!
# Angular-rank data tightness and realisation (P2-general input)

For a full-rank lattice `Λ ≤ ℝᵈ` (`E d`, `finrank ℤ Λ = d`) with Grayson polygon
`c = polygon Λ` (`largestConvexMinorant d (rankData Λ)`), the pure-function tightness
`Submission.DataTightness.largestConvexMinorant_tight_at_angular` — instantiated with
`g := rankData Λ` — says that the polygon is **tight against the data at its angular
vertices**:

    `rankData_eq_polygon_at_angular` :
        for `1 ≤ s < numBlocks d (polygon Λ)`, `j := blockStart d (polygon Λ) s`:
        `rankData Λ j = polygon Λ j`.

Combined with the exact attainment of the rank-data infimum
(`Submission.DataAttainment.exists_subgroup_logCovol_eq_rankData` — the closed
covolume-spectrum discreteness), each angular rank is realised by a subgroup:

    `exists_subgroup_polygon_at_angular` :
        ∃ W ≤ Λ, subDim W = j ∧ log covol(W) = polygon Λ j.

These are the *value realisations* of the P2-general Harder–Narasimhan flag at the
canonical angular ranks `j = blockStart d (polygon Λ) s` (`1 ≤ s < numBlocks`), the
ranks at which the paper's Prop 4 evaluates the covolumes of the flag subgroups
`V_{j_s}`; the endpoint ranks `0` and `d` are realised by `⊥` and `Λ` themselves.  The
nesting of the realised subgroups into a flag is the next P2 step (needs the subgroup
submodularity / replacement argument).

All declarations are Mathlib + Submission (DataTightness/LatticePolygon/DataAttainment).
-/

noncomputable section

open Set Module Real
open scoped BigOperators
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySimpa false
set_option linter.style.haveILetI false
set_option maxHeartbeats 800000

namespace Submission.AngularTightness

open Submission.GraysonData
open Submission.GraysonLattice
open Submission.IntrinsicIndex
open Submission.LatticePolygon
open Submission.AngularRanks
open Submission.Polygon
open Submission.GraysonEndpoints
open Submission.Submodularity
open Submission.UniformBddBelow
open Submission.DataTightness
open Submission.DataAttainment

/-- After `numBlocks` steps of a `ℕ`-indexed function `c` the canonical boundary sequence
has reached `d` (`numBlocks d c ≤ d`). -/
lemma numBlocks_le {d : ℕ} (c : ℕ → ℝ) : numBlocks d c ≤ d := by
  have hd_wit : blockStart d c d = d := blockStart_d_eq_d d c
  exact Nat.find_min' (show ∃ n : ℕ, blockStart d c n = d from ⟨d, hd_wit⟩) hd_wit

/-- **Rank-data tightness at the angular ranks**: for a full-rank lattice `Λ ≤ ℝᵈ`, at
every angular rank `j := blockStart d (polygon Λ) s` of its Grayson polygon
(`1 ≤ s < numBlocks d (polygon Λ)`), the polygon equals the rank-`j` data value
`rankData Λ j` (instantiation of the pure angular-vertex tightness of the largest convex
minorant with `g := rankData Λ`). -/
theorem rankData_eq_polygon_at_angular {d : ℕ} (Λ : Submodule ℤ (E d))
    [DiscreteTopology Λ] [IsZLattice ℝ Λ] (hΛfin : Module.finrank ℤ Λ = d) {s : ℕ}
    (hs1 : 1 ≤ s) (hsN : s < numBlocks d (polygon Λ)) :
    rankData Λ (blockStart d (polygon Λ) s) = polygon Λ (blockStart d (polygon Λ) s) := by
  classical
  have hpoly : ∀ k : ℕ, k ≤ d → polygon Λ k = largestConvexMinorant d (rankData Λ) k := by
    intro k hk
    dsimp [polygon]
    rw [hΛfin]
  have hblock : ∀ k : ℕ, blockStart d (polygon Λ) k =
      blockStart d (largestConvexMinorant d (rankData Λ)) k := by
    intro k
    have hc := blockStart_congr (d := d) (c := polygon Λ)
      (c' := largestConvexMinorant d (rankData Λ))
      (by intro i hi; exact hpoly i hi)
    exact hc k
  have hN : numBlocks d (polygon Λ) = numBlocks d (largestConvexMinorant d (rankData Λ)) :=
    numBlocks_congr (d := d) (c := polygon Λ) (c' := largestConvexMinorant d (rankData Λ))
      (by intro i hi; exact hpoly i hi)
  have htight := largestConvexMinorant_tight_at_angular (d := d) (g := rankData Λ) hs1 (by
    simpa [hN] using hsN)
  -- htight : LCM d (rankData Λ) (blockStart d (LCM d (rankData Λ)) s) = rankData Λ (...)
  have htight' : polygon Λ (blockStart d (polygon Λ) s) =
      rankData Λ (blockStart d (polygon Λ) s) := by
    rw [hblock]
    rw [hpoly (blockStart d (largestConvexMinorant d (rankData Λ)) s)
      (blockStart_le_d d (largestConvexMinorant d (rankData Λ)) s)]
    exact htight
  exact htight'.symm

theorem exists_subgroup_polygon_at_angular {d : ℕ} (Λ : Submodule ℤ (E d))
    [DiscreteTopology Λ] [IsZLattice ℝ Λ] (hΛfin : Module.finrank ℤ Λ = d) {s : ℕ}
    (hs1 : 1 ≤ s) (hsN : s < numBlocks d (polygon Λ)) :
    ∃ W : Submodule ℤ (E d), W ≤ Λ ∧
      subDim W = blockStart d (polygon Λ) s ∧
      Real.log (latticeCovol W) = polygon Λ (blockStart d (polygon Λ) s) := by
  classical
  have hj0 : 0 < blockStart d (polygon Λ) s := by
    have hnumle : numBlocks d (polygon Λ) ≤ d := numBlocks_le (polygon Λ)
    have hsle : s ≤ d := le_trans (Nat.le_of_lt hsN) hnumle
    have h₁ : s ≤ blockStart d (polygon Λ) s := blockStart_n_ge d (polygon Λ) s hsle
    omega
  have hjd : blockStart d (polygon Λ) s ≤ d := blockStart_le_d d (polygon Λ) s
  have hrank : rankData Λ (blockStart d (polygon Λ) s) =
      polygon Λ (blockStart d (polygon Λ) s) :=
    rankData_eq_polygon_at_angular (d := d) Λ hΛfin hs1 hsN
  rcases exists_subgroup_logCovol_eq_rankData (d := d) Λ hj0 hjd with
    ⟨W, hWle, hdim, hlog⟩
  refine ⟨W, hWle, hdim, ?_⟩
  rw [← hrank]
  exact hlog

/-- **Rank-data tightness at the left endpoint**: `polygon Λ 0 = rankData Λ 0` (both are
`0`; the pure left-endpoint tightness of the largest convex minorant instantiated with
`g := rankData Λ`). -/
theorem polygon_eq_rankData_endpoint_left {d : ℕ} (Λ : Submodule ℤ (E d))
    [DiscreteTopology Λ] [IsZLattice ℝ Λ] :
    polygon Λ 0 = rankData Λ 0 := by
  classical
  have ht := largestConvexMinorant_left_tight (Module.finrank ℤ Λ) (rankData Λ)
  dsimp [polygon]
  exact ht

/-- **Rank-data tightness at the right endpoint**: for a full-rank lattice
(`finrank ℤ Λ = d`), `polygon Λ d = rankData Λ d` (the pure right-endpoint tightness of
the largest convex minorant instantiated with `g := rankData Λ`). -/
theorem polygon_eq_rankData_endpoint_right {d : ℕ} (Λ : Submodule ℤ (E d))
    [DiscreteTopology Λ] [IsZLattice ℝ Λ] (hΛfin : Module.finrank ℤ Λ = d) :
    polygon Λ d = rankData Λ d := by
  classical
  have ht := largestConvexMinorant_right_tight (Module.finrank ℤ Λ) (rankData Λ)
  dsimp [polygon]
  rw [hΛfin] at ht ⊢
  exact ht

/-- The full lattice has rank `d` (`subDim Λ = d` for a full-rank `Λ ≤ ℝᵈ`). -/
lemma subDim_full {d : ℕ} (Λ : Submodule ℤ (E d)) [DiscreteTopology Λ] [IsZLattice ℝ Λ] :
    subDim Λ = d := by
  classical
  dsimp [subDim]
  have hV : realSpan Λ = ⊤ := (inferInstance : IsZLattice ℝ Λ).span_top
  have hf : Module.finrank ℝ (realSpan Λ) = Module.finrank ℝ (E d) := by
    calc
      Module.finrank ℝ (realSpan Λ) = Module.finrank ℝ (⊤ : Submodule ℝ (E d)) := by
            exact (LinearEquiv.ofEq (realSpan Λ) (⊤ : Submodule ℝ (E d)) hV).finrank_eq
      _ = Module.finrank ℝ (E d) := (Submodule.topEquiv (R := ℝ) (M := E d)).finrank_eq
  have hE : Module.finrank ℝ (E d) = d := by
    have hb := (EuclideanSpace.basisFun (Fin d) ℝ).toBasis
    simpa using (hb.finrank_eq (Fin d))
  rw [hf, hE]

/-- **Full-rank log-covolume lower bound**: for a full-rank subgroup `W ≤ Λ` of a
full-rank lattice, `log covol Λ ≤ log covol W` (ambient-covolume index identity
`covol W = covol Λ · [Λ : W]` with `[Λ : W] ≥ 1` and covolume positivity). -/
lemma logCovol_le_of_fullRank {d : ℕ} (Λ : Submodule ℤ (E d)) [DiscreteTopology Λ]
    [IsZLattice ℝ Λ] (W : Submodule ℤ (E d)) (hWΛ : W ≤ Λ) (hdim : subDim W = d) :
    Real.log (latticeCovol Λ) ≤ Real.log (latticeCovol W) := by
  classical
  haveI : DiscreteTopology W := discreteTopology_of_le Λ W hWΛ
  haveI : IsZLattice ℝ W := isZLattice_of_subDim W hdim
  have hspanW : Submodule.span ℝ (W : Set (E d)) = ⊤ := realSpan_eq_top_of_subDim W hdim
  have hcw : latticeCovol W = ZLattice.covolume (E := E d) W :=
    latticeCovol_eq_covolume_of_span_top (d := d) W hspanW
  have hcΛ : latticeCovol Λ = ZLattice.covolume (E := E d) Λ :=
    latticeCovol_eq_covolume_of_span_top (d := d) Λ (inferInstance : IsZLattice ℝ Λ).span_top
  have hidx : ZLattice.covolume (E := E d) W =
      ZLattice.covolume (E := E d) Λ *
        (W.toAddSubgroup.relIndex Λ.toAddSubgroup : ℝ) :=
    covol_eq_covol_lattice_mul_relIndex (d := d) Λ W hWΛ
  have hposΛ : 0 < ZLattice.covolume (E := E d) Λ := ZLattice.covolume_pos Λ
  have hposW : 0 < ZLattice.covolume (E := E d) W := ZLattice.covolume_pos W
  have hdiv : (W.toAddSubgroup.relIndex Λ.toAddSubgroup : ℝ) =
      ZLattice.covolume (E := E d) W / ZLattice.covolume (E := E d) Λ := by
    have hEq := congrArg (fun t : ℝ => t / ZLattice.covolume (E := E d) Λ) hidx
    rw [hEq]
    field_simp [ne_of_gt hposΛ]
  have hri_pos : 0 < (W.toAddSubgroup.relIndex Λ.toAddSubgroup : ℝ) := by
    rw [hdiv]
    exact div_pos hposW hposΛ
  have hri1 : (1 : ℝ) ≤ (W.toAddSubgroup.relIndex Λ.toAddSubgroup : ℝ) := by
    have hne : W.toAddSubgroup.relIndex Λ.toAddSubgroup ≠ 0 := by
      exact_mod_cast (ne_of_gt hri_pos)
    exact_mod_cast (Nat.succ_le_of_lt (Nat.pos_of_ne_zero hne))
  have hge : latticeCovol Λ ≤ latticeCovol W := by
    rw [hcw, hcΛ]
    rw [hidx]
    simpa using (mul_le_mul_of_nonneg_left hri1 (le_of_lt hposΛ))
  have hpos : 0 < latticeCovol Λ := by
    rw [hcΛ]
    exact hposΛ
  exact Real.log_le_log hpos hge

/-- **Top-rank data value = full-lattice covolume**: for a full-rank lattice `Λ ≤ ℝᵈ`,
`rankData Λ d = log covol(Λ)` — the infimum over the full-rank subgroups of `Λ` is
attained at `Λ` itself (every full-rank subgroup has covolume at least that of `Λ`). -/
theorem rankData_eq_logCovol_full {d : ℕ} (Λ : Submodule ℤ (E d)) [DiscreteTopology Λ]
    [IsZLattice ℝ Λ] (hΛfin : Module.finrank ℤ Λ = d) :
    rankData Λ d = Real.log (latticeCovol Λ) := by
  classical
  let S : Set ℝ := rankDataSet Λ d
  have hbdd : BddBelow S := by
    dsimp [S]
    exact rankData_bddBelow_of_lattice Λ hΛfin d (le_rfl)
  -- Λ itself is a member
  have hmemΛ : Real.log (latticeCovol Λ) ∈ S := by
    dsimp [S, rankDataSet]
    refine ⟨Λ, le_rfl, subDim_full Λ, rfl⟩
  -- every member is ≥ log covol Λ
  have hlb : ∀ r : ℝ, r ∈ S → Real.log (latticeCovol Λ) ≤ r := by
    rintro r ⟨W, hWle, hdim, rfl⟩
    exact logCovol_le_of_fullRank Λ W hWle hdim
  have hle : Real.log (latticeCovol Λ) ≤ sInf S :=
    le_csInf ⟨Real.log (latticeCovol Λ), hmemΛ⟩ (by intro r hr; exact hlb r hr)
  have hge : sInf S ≤ Real.log (latticeCovol Λ) := csInf_le hbdd hmemΛ
  have hx : sInf S = Real.log (latticeCovol Λ) := le_antisymm hge hle
  dsimp [rankData, S] at hx ⊢
  exact hx

/-- **Top-rank polygon value = full-lattice covolume**: `polygon Λ d = log covol(Λ)` for
a full-rank lattice (right-endpoint tightness + top-rank data equality) — the endpoint
`d` of the Grayson polygon is realised by `Λ` itself. -/
theorem polygon_eq_logCovol_full {d : ℕ} (Λ : Submodule ℤ (E d)) [DiscreteTopology Λ]
    [IsZLattice ℝ Λ] (hΛfin : Module.finrank ℤ Λ = d) :
    polygon Λ d = Real.log (latticeCovol Λ) := by
  calc
    polygon Λ d = rankData Λ d := polygon_eq_rankData_endpoint_right (d := d) Λ hΛfin
    _ = Real.log (latticeCovol Λ) := rankData_eq_logCovol_full (d := d) Λ hΛfin

/-- **Top-rank polygon realisation**: for a full-rank lattice, the top rank `d` of the
Grayson polygon is realised by `Λ` itself: `∃ W ≤ Λ`, `subDim W = d` and
`log covol(W) = polygon Λ d`. -/
theorem exists_fullRank_polygon_realisation {d : ℕ} (Λ : Submodule ℤ (E d))
    [DiscreteTopology Λ] [IsZLattice ℝ Λ] (hΛfin : Module.finrank ℤ Λ = d) :
    ∃ W : Submodule ℤ (E d), W ≤ Λ ∧ subDim W = d ∧
      Real.log (latticeCovol W) = polygon Λ d := by
  refine ⟨Λ, le_rfl, subDim_full Λ, ?_⟩
  exact (polygon_eq_logCovol_full (d := d) Λ hΛfin).symm

end Submission.AngularTightness

end
