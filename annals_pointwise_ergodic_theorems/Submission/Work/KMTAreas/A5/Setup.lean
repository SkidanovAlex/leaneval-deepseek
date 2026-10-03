/-
# Area A5: the objects of the minor-arc estimate

The two minor-arc parts of the halved average at scale `N` for the concrete Ionescu--Wainger
projections `kmtPj ρ`:

* `minorArc₁ ρ L K N P u v = Ã_N(u - Π_{≤L,≤K} u, v)`;
* `minorArc₂ ρ L K K₂ N P u v = Ã_N(Π_{≤L,≤K} u, v - Π_{≤L,≤K₂} v)`,

the two terms of the bilinear expansion `Ã_N(u,v) - R_N(u,v)` of the §4 splitting, where
`R_N` is the major-arc part.  This file also fixes the weight `improvWeight c ρ L N` produced by
`ImprovKMT` (the single-scale minor arc estimate of area A4) and the elementary facts about it.
-/
import Submission.Work.KMTAreas.A5.Basic

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Work.KMTAreas.A5

noncomputable section

open MeasureTheory Polynomial Finset Filter Topology
open scoped ENNReal NNReal BigOperators
open Work.KMTContract
open Work.Analysis.EndVar
open Work.Analysis.IonescuWainger
open Submission.PointwiseErgodicTheorems

/-- The first minor-arc part: `Ã_N(u - Π_{≤L,≤K} u, v)`. -/
def minorArc₁ (ρ : ℝ) (L : ℕ) (K : ℤ) (N : ℝ≥0) (P : ℤ[X]) (u v : ℤ → ℂ) : ℤ → ℂ :=
  AhalfR TZ N X P (u - kmtProj ρ L K u) v

/-- The second minor-arc part: `Ã_N(Π_{≤L,≤K} u, v - Π_{≤L,≤K₂} v)`. -/
def minorArc₂ (ρ : ℝ) (L : ℕ) (K K₂ : ℤ) (N : ℝ≥0) (P : ℤ[X]) (u v : ℤ → ℂ) : ℤ → ℂ :=
  AhalfR TZ N X P (kmtProj ρ L K u) (v - kmtProj ρ L K₂ v)

@[simp] theorem minorArc₁_zero_right (ρ : ℝ) (L : ℕ) (K : ℤ) (N : ℝ≥0) (P : ℤ[X])
    (u : ℤ → ℂ) : minorArc₁ ρ L K N P u 0 = 0 := by
  simp [minorArc₁, AhalfR_zero_right]

@[simp] theorem minorArc₂_zero_right (ρ : ℝ) (L : ℕ) (K K₂ : ℤ) (N : ℝ≥0) (P : ℤ[X])
    (u : ℤ → ℂ) : minorArc₂ ρ L K K₂ N P u 0 = 0 := by
  simp [minorArc₂, AhalfR_zero_right]

@[simp] theorem minorArc₁_zero_left (ρ : ℝ) (L : ℕ) (K : ℤ) (N : ℝ≥0) (P : ℤ[X])
    (v : ℤ → ℂ) : minorArc₁ ρ L K N P 0 v = 0 := by
  simp [minorArc₁, AhalfR_zero_left]

@[simp] theorem minorArc₂_zero_left (ρ : ℝ) (L : ℕ) (K K₂ : ℤ) (N : ℝ≥0) (P : ℤ[X])
    (v : ℤ → ℂ) : minorArc₂ ρ L K K₂ N P 0 v = 0 := by
  simp [minorArc₂, AhalfR_zero_left]

/-- The weight produced by `ImprovKMT`: `2^{-c (L-1)} + (Log N)^{-c/ρ}`. -/
noncomputable def improvWeight (c ρ : ℝ) (L N : ℕ) : ℝ≥0 :=
  Real.toNNReal ((2 : ℝ) ^ (-(c * ((L : ℝ) - 1))) + ((logN N : ℝ)) ^ (-(c / ρ)))

theorem improvWeight_coe (c ρ : ℝ) (L N : ℕ) :
    ((improvWeight c ρ L N : ℝ≥0) : ℝ≥0∞)
      = ENNReal.ofReal ((2 : ℝ) ^ (-(c * ((L : ℝ) - 1))) + ((logN N : ℝ)) ^ (-(c / ρ))) := by
  have hr : 0 ≤ (2 : ℝ) ^ (-(c * ((L : ℝ) - 1))) + ((logN N : ℝ)) ^ (-(c / ρ)) := by
    have h1 : (0 : ℝ) < (2 : ℝ) ^ (-(c * ((L : ℝ) - 1))) :=
      Real.rpow_pos_of_pos (by norm_num) _
    have h2 : (0 : ℝ) ≤ ((logN N : ℝ)) ^ (-(c / ρ)) :=
      Real.rpow_nonneg (by exact_mod_cast logN_nonneg N) _
    linarith
  rw [improvWeight, Real.toNNReal_of_nonneg hr]
  exact (ENNReal.ofReal_eq_coe_nnreal hr).symm

theorem improvWeight_pos (c ρ : ℝ) (L N : ℕ) : 0 < improvWeight c ρ L N := by
  rw [improvWeight]
  refine Real.toNNReal_pos.mpr ?_
  have h1 : (0 : ℝ) < (2 : ℝ) ^ (-(c * ((L : ℝ) - 1))) :=
    Real.rpow_pos_of_pos (by norm_num) _
  have h2 : (0 : ℝ) ≤ ((logN N : ℝ)) ^ (-(c / ρ)) :=
    Real.rpow_nonneg (by exact_mod_cast logN_nonneg N) _
  linarith

end

end Work.KMTAreas.A5
