import Mathlib
import Submission.Work.Lattice.PhiSlack
import Submission.Work.Lattice.AngularTightness
import Submission.Work.Polygon.DataTightness
import Submission.Work.Polygon.AngularRanks

/-!
# The `φ_A`-Grayson polygon and its tight saturated realisers (P2-general HN flag, part 2)

Building on `Submission.PhiSlack` (the slack `φ_A(V⊓W) + φ_A(V⊔W) + 2A ≤ φ_A(V) + φ_A(W)`
for incomparable saturated subgroups and the compatibility lemma for tight realisers),
this module instantiates the abstract layer at the **`φ_A`-Grayson polygon**

    `phiData Λ A j  = rankData Λ j + A · j · (d − j)`,
    `phiPolygon Λ A = largestConvexMinorant (finrank ℤ Λ) (phiData Λ A)`

and proves the pieces the Harder–Narasimhan flag construction consumes:

* `phiPolygon_le_phi` — the polygon lies below the `φ_A`-data of **every** subgroup
  `X ≤ Λ` (`phiPolygon Λ A (subDim X) ≤ phi A X`), the hypothesis of the compatibility
  lemma in its global form;
* `phiPolygon_eq_data_at_angular` — tightness of the polygon against the data at its
  angular ranks (`largestConvexMinorant_tight_at_angular`);
* `exists_saturated_tight_at_angular` — at every angular rank there is a **saturated**
  subgroup `V ≤ Λ` realising the polygon value (`phi A V = phiPolygon Λ A (subDim V)`),
  obtained by saturating the data-attaining subgroup of
  `DataAttainment.exists_subgroup_logCovol_eq_rankData` (the hull keeps the rank,
  does not increase the covolume, and saturation is idempotent);
* `tight_comparable` / `le_of_tight_of_subDim_le` — the tight saturated realisers are
  pairwise comparable, and the comparison is by rank: a tight realiser of a smaller rank
  lies inside a tight realiser of a larger rank.

Together: at the angular ranks the tight realisers form a chain — the skeleton of the
Harder–Narasimhan filtration of `Λ` for the submodular functional `φ_A`.

All declarations are Mathlib + Submission (`PhiSlack`, `AngularTightness`,
`DataTightness`, `AngularRanks`).
-/

noncomputable section

open Set Module Real
open scoped BigOperators
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option maxHeartbeats 800000

namespace Submission.PhiPolygon

open Submission.GraysonData
open Submission.GraysonLattice
open Submission.JoinSubmodularity
open Submission.IntrinsicIndex
open Submission.MixedRankSpectrum
open Submission.LatticePolygon
open Submission.Polygon
open Submission.PhiSlack
open Submission.AngularRanks
open Submission.UniformBddBelow
open Submission.DataAttainment
open Submission.DataTightness
open Submission.AngularTightness

/-- The **`φ_A`-rank data** of `Λ`: the rank-`j` data of the log-covolume, slacked by the
quadratic term `A · j · (d − j)`. -/
noncomputable def phiData {d : ℕ} (Λ : Submodule ℤ (E d)) (A : ℝ) (j : ℕ) : ℝ :=
  rankData Λ j + A * ((j : ℝ) * ((d : ℝ) - (j : ℝ)))

/-- The **`φ_A`-Grayson polygon** of `Λ`: the largest convex minorant of the slacked
rank data. -/
noncomputable def phiPolygon {d : ℕ} (Λ : Submodule ℤ (E d)) (A : ℝ) (i : ℕ) : ℝ :=
  largestConvexMinorant (Module.finrank ℤ Λ) (phiData Λ A) i

/-- The polygon lies below the slacked data (`largestConvexMinorant_le_g`). -/
lemma phiPolygon_le_data {d : ℕ} (Λ : Submodule ℤ (E d)) (A : ℝ) {j : ℕ}
    (hj : j ≤ Module.finrank ℤ Λ) : phiPolygon Λ A j ≤ phiData Λ A j :=
  largestConvexMinorant_le_g (Module.finrank ℤ Λ) (phiData Λ A) hj

/-- The slacked polygon is discrete-convex on the slope range. -/
lemma phiPolygon_convex {d : ℕ} (Λ : Submodule ℤ (E d)) (A : ℝ) :
    DiscreteConvexOn (phiPolygon Λ A) (Module.finrank ℤ Λ) :=
  largestConvexMinorant_convex (Module.finrank ℤ Λ) (phiData Λ A)

/-- **The `φ_A`-polygon lies below the `φ_A`-data**: for every subgroup `X ≤ Λ` of a
full-rank lattice `Λ`, `phiPolygon Λ A (subDim X) ≤ phi A X`. -/
theorem phiPolygon_le_phi {d : ℕ} (Λ X : Submodule ℤ (E d)) [DiscreteTopology Λ]
    [IsZLattice ℝ Λ] (hΛfin : Module.finrank ℤ Λ = d) (A : ℝ) (hX : X ≤ Λ) :
    phiPolygon Λ A (subDim X) ≤ phi A X := by
  have hjd : subDim X ≤ Module.finrank ℤ Λ := by
    rw [hΛfin]
    exact subDim_le_ambient X
  have hbd : BddBelow (rankDataSet Λ (subDim X)) := by
    rw [hΛfin] at hjd
    exact rankData_bddBelow_of_lattice Λ hΛfin (subDim X) hjd
  refine le_trans (phiPolygon_le_data Λ A hjd) ?_
  have hrc := rankData_le_covol Λ hX rfl hbd
  simp only [phiData, phi]
  linarith

/-- **Tightness of the `φ_A`-polygon at its angular ranks**: at every angular rank
`j = blockStart d (phiPolygon Λ A) s`, the polygon equals the slacked data. -/
theorem phiPolygon_eq_data_at_angular {d : ℕ} (Λ : Submodule ℤ (E d))
    [DiscreteTopology Λ] [IsZLattice ℝ Λ] (hΛfin : Module.finrank ℤ Λ = d) (A : ℝ) {s : ℕ}
    (hs1 : 1 ≤ s) (hsN : s < numBlocks d (phiPolygon Λ A)) :
    phiPolygon Λ A (blockStart d (phiPolygon Λ A) s) =
      phiData Λ A (blockStart d (phiPolygon Λ A) s) := by
  classical
  have hpoly : ∀ k : ℕ, phiPolygon Λ A k = largestConvexMinorant d (phiData Λ A) k := by
    intro k
    dsimp [phiPolygon]
    rw [hΛfin]
  have hblock : ∀ k : ℕ, blockStart d (phiPolygon Λ A) k =
      blockStart d (largestConvexMinorant d (phiData Λ A)) k :=
    blockStart_congr (d := d) (c := phiPolygon Λ A)
      (c' := largestConvexMinorant d (phiData Λ A)) (by intro i _hi; exact hpoly i)
  have hN : numBlocks d (phiPolygon Λ A) =
      numBlocks d (largestConvexMinorant d (phiData Λ A)) :=
    numBlocks_congr (d := d) (c := phiPolygon Λ A)
      (c' := largestConvexMinorant d (phiData Λ A)) (by intro i _hi; exact hpoly i)
  have htight := largestConvexMinorant_tight_at_angular d (phiData Λ A) hs1
    (by simpa [hN] using hsN)
  rw [hblock, hpoly (blockStart d (largestConvexMinorant d (phiData Λ A)) s)]
  exact htight

/-- **Saturated tight realisers at the angular ranks**: for a full-rank lattice `Λ`, every
angular rank `j` of the `φ_A`-polygon is realised by a *saturated* subgroup
`V ≤ Λ` (`phi A V = phiPolygon Λ A j`, `subDim V = j`). -/
theorem exists_saturated_tight_at_angular {d : ℕ} (Λ : Submodule ℤ (E d))
    [DiscreteTopology Λ] [IsZLattice ℝ Λ] (hΛfin : Module.finrank ℤ Λ = d) {A : ℝ}
    {s : ℕ} (hs1 : 1 ≤ s) (hsN : s < numBlocks d (phiPolygon Λ A)) :
    ∃ V : Submodule ℤ (E d), V ≤ Λ ∧ Saturated Λ V ∧
      subDim V = blockStart d (phiPolygon Λ A) s ∧
      phi A V = phiPolygon Λ A (blockStart d (phiPolygon Λ A) s) := by
  classical
  have hnumle : numBlocks d (phiPolygon Λ A) ≤ d := numBlocks_le (phiPolygon Λ A)
  have hsle : s ≤ d := le_trans (Nat.le_of_lt hsN) hnumle
  have hj0 : 0 < blockStart d (phiPolygon Λ A) s := by
    have h₁ : s ≤ blockStart d (phiPolygon Λ A) s := blockStart_n_ge d (phiPolygon Λ A) s hsle
    omega
  have hjd : blockStart d (phiPolygon Λ A) s ≤ d := blockStart_le_d d (phiPolygon Λ A) s
  have htight : phiPolygon Λ A (blockStart d (phiPolygon Λ A) s) =
      phiData Λ A (blockStart d (phiPolygon Λ A) s) :=
    phiPolygon_eq_data_at_angular Λ hΛfin A hs1 hsN
  rcases exists_subgroup_logCovol_eq_rankData (d := d) Λ hj0 hjd with ⟨W, hWle, hdim, hlog⟩
  have hphiW : phi A W = phiData Λ A (blockStart d (phiPolygon Λ A) s) := by
    simp only [phi, phiData]
    rw [hlog, hdim]
  have hW0 : W ≠ ⊥ := by
    intro hz
    have : subDim W = 0 := (subDim_eq_zero_iff_bot W).mpr hz
    omega
  -- saturate
  have hVle : hull Λ W ≤ Λ := hull_le_Λ Λ W
  have hsat : Saturated Λ (hull Λ W) := by
    dsimp [Saturated]
    exact (hull_idempotent Λ W hWle).symm
  have hsubV : subDim (hull Λ W) = blockStart d (phiPolygon Λ A) s := by
    rw [subDim_hull_eq Λ W hWle, hdim]
  have hcov : latticeCovol (hull Λ W) ≤ latticeCovol W := covol_hull_le_covol Λ W hWle hW0
  have hposV : 0 < latticeCovol (hull Λ W) :=
    latticeCovol_pos Λ (hull Λ W) (hull_le_Λ Λ W) (fun hz => by
      have hle : W ≤ (⊥ : Submodule ℤ (E d)) := by
        simpa [hz] using W_le_hull Λ W hWle
      exact hW0 (le_bot_iff.mp hle))
  have hposW : 0 < latticeCovol W := latticeCovol_pos Λ W hWle hW0
  have hlogV : Real.log (latticeCovol (hull Λ W)) ≤ Real.log (latticeCovol W) :=
    Real.log_le_log hposV hcov
  -- two-sided comparison of φ
  have hle1 : phi A (hull Λ W) ≤ phiData Λ A (blockStart d (phiPolygon Λ A) s) := by
    simp only [phi, phiData]
    rw [hsubV]
    linarith [hlogV, hphiW]
  have hle2 : phiPolygon Λ A (blockStart d (phiPolygon Λ A) s) ≤ phi A (hull Λ W) := by
    have h := phiPolygon_le_phi Λ (hull Λ W) hΛfin A hVle
    rwa [hsubV] at h
  refine ⟨hull Λ W, hVle, hsat, hsubV, le_antisymm ?_ hle2⟩
  rw [← htight] at hle1
  exact hle1

/-- **Equal-rank saturated subgroups with equal rank coincide** (a saturated subgroup is
determined by its real span, and comparability plus equal rank forces equal real spans). -/
lemma eq_of_le_of_subDim_eq {d : ℕ} (Λ V W : Submodule ℤ (E d)) [DiscreteTopology Λ]
    (hVsat : Saturated Λ V) (hWsat : Saturated Λ W) (hle : W ≤ V)
    (hsub : subDim W = subDim V) : W = V := by
  have hspanle : realSpan W ≤ realSpan V := Submodule.span_mono (by intro x hx; exact hle hx)
  have heq : realSpan W = realSpan V :=
    Submodule.eq_of_le_of_finrank_eq hspanle (by simpa [subDim] using hsub)
  have hh : hull Λ W = hull Λ V := by
    ext x
    rw [hull_mem_iff, hull_mem_iff, heq]
  rw [hWsat, hh]
  exact hVsat.symm

/-- **The tight saturated realisers are pairwise comparable** (the compatibility lemma
instantiated at the `φ_A`-polygon). -/
theorem tight_comparable {d : ℕ} (Λ V W : Submodule ℤ (E d)) [DiscreteTopology Λ]
    [IsZLattice ℝ Λ] (hΛfin : Module.finrank ℤ Λ = d) {A : ℝ} (hA : 0 < A)
    (hVsat : Saturated Λ V) (hWsat : Saturated Λ W)
    (hVtight : phi A V = phiPolygon Λ A (subDim V))
    (hWtight : phi A W = phiPolygon Λ A (subDim W)) : V ≤ W ∨ W ≤ V := by
  have hcvx : DiscreteConvexOn (phiPolygon Λ A) d := by
    have h := phiPolygon_convex Λ A
    rwa [hΛfin] at h
  exact comparable_of_tight_of_le_data Λ V W hΛfin hA hVsat hWsat hcvx
    (fun X hX => phiPolygon_le_phi Λ X hΛfin A hX) hVtight hWtight

/-- **The chain order**: a tight saturated realiser of smaller rank lies inside a tight
saturated realiser of larger rank. -/
theorem le_of_tight_of_subDim_le {d : ℕ} (Λ V W : Submodule ℤ (E d)) [DiscreteTopology Λ]
    [IsZLattice ℝ Λ] (hΛfin : Module.finrank ℤ Λ = d) {A : ℝ} (hA : 0 < A)
    (hVsat : Saturated Λ V) (hWsat : Saturated Λ W)
    (hVtight : phi A V = phiPolygon Λ A (subDim V))
    (hWtight : phi A W = phiPolygon Λ A (subDim W)) (hle : subDim V ≤ subDim W) :
    V ≤ W := by
  rcases tight_comparable Λ V W hΛfin hA hVsat hWsat hVtight hWtight with h | h
  · exact h
  · have hsub : subDim W = subDim V := le_antisymm (Submodule.finrank_mono
      (Submodule.span_mono (by intro x hx; exact h hx))) hle
    have hWV : W = V := eq_of_le_of_subDim_eq Λ V W hVsat hWsat h hsub
    rw [← hWV]

end Submission.PhiPolygon
