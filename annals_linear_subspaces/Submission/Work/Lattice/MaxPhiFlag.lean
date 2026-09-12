import Mathlib
import Submission.Work.Lattice.MaxPhiPolygon
import Submission.Work.Lattice.MaxAttainment
import Submission.Work.Polygon.DataTightness
import Submission.Work.Lattice.AngularTightness

/-!
# The angular layer of the max-norm polygon: tightness and saturated tight realisers

The first two pieces of the max-norm flag (`maxPhi`-analogue of `PhiPolygon`):

* **`maxphiPolygon_eq_data_at_angular`** — at every angular rank of `maxphiPolygon Λ A` the
  polygon equals the slacked max-norm data.  This is the general property of the largest convex
  minorant (`Polygon.largestConvexMinorant_tight_at_angular`), so no attainment input is needed;
* **`exists_saturated_tight_at_angular`** — at every angular rank there is a *saturated* subgroup
  `V ≤ Λ` with `maxPhi A V = maxphiPolygon Λ A (blockStart …)` and `subDim V = blockStart …`
  (the attained, saturated realiser of `MaxAttainment.exists_saturated_maxCovol_eq_maxRankData`).

Module `Submission.Work.Lattice.MaxPhiFlag`, namespace `Submission.MaxPhiFlag`.
-/

noncomputable section

open Module exteriorPower InnerProductGeometry Real
open scoped BigOperators
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1000000

namespace Submission.MaxPhiFlag

open Submission.GraysonLattice
open Submission.GraysonData
open Submission.Polygon
open Submission.AngularRanks
open Submission.AngularTightness
open Submission.JoinSubmodularity
open Submission.DataTightness
open Submission.MaxRankData
open Submission.MaxPhi
open Submission.MaxPhiPolygon
open Submission.MaxCovol
open Submission.MaxAttainment
open Submission.PhiPolygon
open Submission.LatticePolygon

variable {d : ℕ}

/-- **Tightness of the max-norm polygon at its angular ranks**: at every angular rank
`j = blockStart d (maxphiPolygon Λ A) s` (`1 ≤ s < numBlocks`), the polygon equals the slacked
max-norm data. -/
theorem maxphiPolygon_eq_data_at_angular (Λ : Submodule ℤ (E d))
    [DiscreteTopology Λ] [IsZLattice ℝ Λ] (hΛfin : Module.finrank ℤ Λ = d) (A : ℝ) {s : ℕ}
    (hs1 : 1 ≤ s) (hsN : s < numBlocks d (maxphiPolygon Λ A)) :
    maxphiPolygon Λ A (blockStart d (maxphiPolygon Λ A) s) =
      maxphiData Λ A (blockStart d (maxphiPolygon Λ A) s) := by
  classical
  have hpoly : ∀ k : ℕ, maxphiPolygon Λ A k = largestConvexMinorant d (maxphiData Λ A) k := by
    intro k
    dsimp [maxphiPolygon]
    rw [hΛfin]
  have hblock : ∀ k : ℕ, blockStart d (maxphiPolygon Λ A) k =
      blockStart d (largestConvexMinorant d (maxphiData Λ A)) k :=
    blockStart_congr (d := d) (c := maxphiPolygon Λ A)
      (c' := largestConvexMinorant d (maxphiData Λ A)) (by intro i _hi; exact hpoly i)
  have hN : numBlocks d (maxphiPolygon Λ A) =
      numBlocks d (largestConvexMinorant d (maxphiData Λ A)) :=
    numBlocks_congr (d := d) (c := maxphiPolygon Λ A)
      (c' := largestConvexMinorant d (maxphiData Λ A)) (by intro i _hi; exact hpoly i)
  have htight := largestConvexMinorant_tight_at_angular d (maxphiData Λ A) hs1
    (by simpa [hN] using hsN)
  rw [hblock, hpoly (blockStart d (largestConvexMinorant d (maxphiData Λ A)) s)]
  exact htight

/-- **Saturated max-norm tight realisers at the angular ranks.**  For a full-rank lattice `Λ`
whose max-norm data is bounded below at every rank `1 ≤ j ≤ d`, every angular rank
`j = blockStart d (maxphiPolygon Λ A) s` (`1 ≤ s < numBlocks`) is realised by a *saturated*
subgroup `V ≤ Λ` with `maxPhi A V = maxphiPolygon Λ A j` and `subDim V = j`. -/
theorem exists_saturated_tight_at_angular (Λ : Submodule ℤ (E d))
    [DiscreteTopology Λ] [IsZLattice ℝ Λ] (hΛfin : Module.finrank ℤ Λ = d) (A : ℝ) {s : ℕ}
    (hs1 : 1 ≤ s) (hsN : s < numBlocks d (maxphiPolygon Λ A))
    (hBdd : ∀ (j : ℕ) (_hj : 1 ≤ j) (hjd : j ≤ d),
      BddBelow (maxRankDataSet (d := d) Λ j hjd)) :
    ∃ (V : Submodule ℤ (E d)) (hVΛ : V ≤ Λ), Saturated Λ V ∧
      subDim V = blockStart d (maxphiPolygon Λ A) s ∧
      maxPhi (d := d) Λ hΛfin A V hVΛ =
        maxphiPolygon Λ A (blockStart d (maxphiPolygon Λ A) s) := by
  classical
  have hnumle : numBlocks d (maxphiPolygon Λ A) ≤ d := numBlocks_le (maxphiPolygon Λ A)
  have hsle : s ≤ d := le_trans (Nat.le_of_lt hsN) hnumle
  have hj0 : 0 < blockStart d (maxphiPolygon Λ A) s := by
    have h₁ : s ≤ blockStart d (maxphiPolygon Λ A) s :=
      blockStart_n_ge d (maxphiPolygon Λ A) s hsle
    omega
  have hjd : blockStart d (maxphiPolygon Λ A) s ≤ d := blockStart_le_d d (maxphiPolygon Λ A) s
  have htight : maxphiPolygon Λ A (blockStart d (maxphiPolygon Λ A) s) =
      maxphiData Λ A (blockStart d (maxphiPolygon Λ A) s) :=
    maxphiPolygon_eq_data_at_angular Λ hΛfin A hs1 hsN
  obtain ⟨V, hVΛ, hVsat, hdim, hcov⟩ :=
    exists_saturated_maxCovol_eq_maxRankData (d := d) (Λ := Λ) hΛfin hj0 hjd (hBdd _ hj0 hjd)
  refine ⟨V, hVΛ, hVsat, hdim, ?_⟩
  have hdat : maxphiData (d := d) Λ A (blockStart d (maxphiPolygon Λ A) s) =
      maxRankData (d := d) Λ (blockStart d (maxphiPolygon Λ A) s) hjd +
        A * (((blockStart d (maxphiPolygon Λ A) s : ℕ) : ℝ) *
          ((d : ℝ) - ((blockStart d (maxphiPolygon Λ A) s : ℕ) : ℝ))) := by
    rw [maxphiData, dif_pos hjd]
  rw [maxPhi, hcov, htight, hdat]
  congr 1
  rw [hdim]

/-! ## The max-norm flag -/

/-- `blockStart` is non-decreasing over all pairs. -/
lemma blockStart_mono_le {d : ℕ} (c : ℕ → ℝ) {s t : ℕ} (hst : s ≤ t) :
    blockStart d c s ≤ blockStart d c t := by
  induction t, hst using Nat.le_induction with
  | base => exact le_rfl
  | succ t hst ih => exact le_trans ih (blockStart_mono d c t)

/-- **The saturated max-norm tight realisers are pairwise comparable** (the compatibility lemma
instantiated at `maxphiPolygon`). -/
theorem maxPhi_tight_comparable {Λ V W : Submodule ℤ (E d)} [DiscreteTopology Λ]
    [IsZLattice ℝ Λ] (hΛfin : Module.finrank ℤ Λ = d) {A : ℝ}
    (hA : (d : ℝ) * Real.log 2 / 2 < A)
    (hVsat : Saturated Λ V) (hWsat : Saturated Λ W)
    (hVtight : maxPhi (d := d) Λ hΛfin A V (saturated_le Λ V hVsat) =
      maxphiPolygon Λ A (subDim V))
    (hWtight : maxPhi (d := d) Λ hΛfin A W (saturated_le Λ W hWsat) =
      maxphiPolygon Λ A (subDim W))
    (hBdd : ∀ (j : ℕ) (hjd : j ≤ d), BddBelow (maxRankDataSet (d := d) Λ j hjd)) :
    V ≤ W ∨ W ≤ V := by
  have hcvx : DiscreteConvexOn (maxphiPolygon Λ A) d := by
    have h := maxphiPolygon_convex Λ A
    rwa [hΛfin] at h
  refine maxPhi_comparable_of_tight (d := d) (Λ := Λ) (V := V) (W := W) hΛfin hA hVsat hWsat
    hcvx hVtight hWtight ?_ ?_
  · exact maxphiPolygon_le_maxPhi (d := d) (Λ := Λ) (X := V ⊓ W) hΛfin A
      (le_trans inf_le_left (saturated_le Λ V hVsat)) (hBdd _ (subDim_le_ambient (V ⊓ W)))
  · exact maxphiPolygon_le_maxPhi (d := d) (Λ := Λ) (X := V ⊔ W) hΛfin A
      (sup_le (saturated_le Λ V hVsat) (saturated_le Λ W hWsat))
      (hBdd _ (subDim_le_ambient (V ⊔ W)))

/-- **The chain order of max-norm tight realisers**: a tight saturated realiser of smaller rank
lies inside a tight saturated realiser of larger rank. -/
theorem le_of_maxPhi_tight_of_subDim_le {Λ V W : Submodule ℤ (E d)} [DiscreteTopology Λ]
    [IsZLattice ℝ Λ] (hΛfin : Module.finrank ℤ Λ = d) {A : ℝ}
    (hA : (d : ℝ) * Real.log 2 / 2 < A)
    (hVsat : Saturated Λ V) (hWsat : Saturated Λ W)
    (hVtight : maxPhi (d := d) Λ hΛfin A V (saturated_le Λ V hVsat) =
      maxphiPolygon Λ A (subDim V))
    (hWtight : maxPhi (d := d) Λ hΛfin A W (saturated_le Λ W hWsat) =
      maxphiPolygon Λ A (subDim W))
    (hBdd : ∀ (j : ℕ) (hjd : j ≤ d), BddBelow (maxRankDataSet (d := d) Λ j hjd))
    (hle : subDim V ≤ subDim W) : V ≤ W := by
  rcases maxPhi_tight_comparable (Λ := Λ) (V := V) (W := W) hΛfin hA hVsat hWsat hVtight hWtight
    hBdd with h | h
  · exact h
  · have hsub : subDim W = subDim V := le_antisymm (Submodule.finrank_mono
      (Submodule.span_mono (by intro x hx; exact h hx))) hle
    have hWV : W = V := eq_of_le_of_subDim_eq Λ V W hVsat hWsat h hsub
    rw [← hWV]

/-- **The max-norm Harder–Narasimhan flag.**  For a full-rank lattice `Λ` (with max-norm data
bounded below at every rank `j ≤ d`) and `A > (d/2)log 2`, there is a family of saturated
subgroups indexed by the interior angular ranks of `maxphiPolygon Λ A`, monotone under inclusion,
realising the angular rank and the polygon value at each index. -/
theorem exists_tight_flag (Λ : Submodule ℤ (E d)) [DiscreteTopology Λ] [IsZLattice ℝ Λ]
    (hΛfin : Module.finrank ℤ Λ = d) {A : ℝ} (hA : (d : ℝ) * Real.log 2 / 2 < A)
    (hBdd : ∀ (j : ℕ) (hjd : j ≤ d), BddBelow (maxRankDataSet (d := d) Λ j hjd)) :
    ∃ (V : {s : ℕ // 1 ≤ s ∧ s < numBlocks d (maxphiPolygon Λ A)} → Submodule ℤ (E d))
      (hV : ∀ s, V s ≤ Λ) (hVsat : ∀ s, Saturated Λ (V s)),
      (∀ s, subDim (V s) = blockStart d (maxphiPolygon Λ A) s.1 ∧
        maxPhi (d := d) Λ hΛfin A (V s) (hV s) =
          maxphiPolygon Λ A (blockStart d (maxphiPolygon Λ A) s.1)) ∧
      (∀ s t, s ≤ t → V s ≤ V t) := by
  classical
  choose V hVΛ hrest using fun (s : {s : ℕ // 1 ≤ s ∧ s < numBlocks d (maxphiPolygon Λ A)}) =>
    exists_saturated_tight_at_angular Λ hΛfin A s.2.1 s.2.2 (fun j _ hjd => hBdd j hjd)
  refine ⟨V, hVΛ, fun s => (hrest s).1,
    fun s => ⟨(hrest s).2.1, (hrest s).2.2⟩, ?_⟩
  intro s t hst
  have hsat_s : Saturated Λ (V s) := (hrest s).1
  have hsat_t : Saturated Λ (V t) := (hrest t).1
  have hdim_s : subDim (V s) = blockStart d (maxphiPolygon Λ A) s.1 := (hrest s).2.1
  have hdim_t : subDim (V t) = blockStart d (maxphiPolygon Λ A) t.1 := (hrest t).2.1
  have hle : subDim (V s) ≤ subDim (V t) := by
    rw [hdim_s, hdim_t]
    exact blockStart_mono_le (maxphiPolygon Λ A) hst
  have htights : maxPhi (d := d) Λ hΛfin A (V s) (saturated_le Λ (V s) hsat_s) =
      maxphiPolygon Λ A (subDim (V s)) := by
    rw [hdim_s]
    exact (hrest s).2.2
  have htightt : maxPhi (d := d) Λ hΛfin A (V t) (saturated_le Λ (V t) hsat_t) =
      maxphiPolygon Λ A (subDim (V t)) := by
    rw [hdim_t]
    exact (hrest t).2.2
  exact le_of_maxPhi_tight_of_subDim_le (Λ := Λ) (V := V s) (W := V t) hΛfin hA hsat_s hsat_t
    htights htightt hBdd hle


end Submission.MaxPhiFlag

end
