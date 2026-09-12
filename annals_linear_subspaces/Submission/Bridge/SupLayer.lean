import Mathlib
import Submission.Bridge.Projective

/-!
# Bridge, subspace layer: `distSubspaces` equals the maximal unit residual

This file (Mathlib-only, generic finite-dimensional real inner product space `E`) proves the
core identification behind the challenge's `distSubspaces`: for subspaces `v` (the *smaller*
one, measured line-by-line) and `x`, with `finrank v < finrank x`,

`distSubspacesMirror v x = planeResidualCore v x`

where the mirror definitions replicate the challenge's (with the sine-of-angle line distances
of `Submission.Bridge.Projective.lineToSubspace`), and `planeResidualCore` is the maximal
orthogonal residual over unit vectors of `v` (the `δ(v,x)` of the model work, up to the choice
of projection notation).

Combined with `Projective.lineToSubspace_mk_unit`, this is what allows model-side bounds on
`planeResidual` to be transferred to the challenge's `distSubspaces`.
-/

noncomputable section

open scoped LinearAlgebra.Projectivization
open Module Real InnerProductGeometry
open Real

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Submission.Bridge.SupLayer

open Submission.Bridge.Core
open Submission.Bridge.Projective

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- The set of orthogonal residuals of unit vectors of `V` (with respect to projection onto
`x`): the set whose supremum is the operator-norm distance `δ(V,x)`. -/
def unitResidualSet (V x : Submodule ℝ E) : Set ℝ :=
  {r : ℝ | ∃ u : E, u ∈ V ∧ ‖u‖ = 1 ∧ ‖u - x.starProjection u‖ = r}

/-- `δ(V,x)`: the largest orthogonal residual over unit vectors of `V`. -/
def planeResidualCore (V x : Submodule ℝ E) : ℝ :=
  sSup (unitResidualSet V x)

/-- Mirror of `LinearSubspaces.distSubspaces` (same shape, line distances via sine of angle). -/
def distSubspacesMirror (x y : Submodule ℝ E) : ℝ :=
  if finrank ℝ y ≤ finrank ℝ x then
    ⨆ Y : {Y : ℙ ℝ E // Y.submodule ≤ y}, lineToSubspace Y.1 x
  else
    ⨆ X : {X : ℙ ℝ E // X.submodule ≤ x}, lineToSubspace X.1 y

/-- Values of residuals lie in `[0, 2]`, so the residual set is bounded above. -/
lemma bddAbove_unitResidualSet (V x : Submodule ℝ E) : BddAbove (unitResidualSet V x) := by
  refine ⟨2, ?_⟩
  rintro r ⟨u, huV, hu1, rfl⟩
  calc
    ‖u - x.starProjection u‖ ≤ ‖u‖ + ‖x.starProjection u‖ := norm_sub_le _ _
    _ ≤ 2 := by
        rw [hu1]
        have hπ : ‖x.starProjection u‖ ≤ ‖u‖ := x.norm_starProjection_apply_le u
        rw [hu1] at hπ
        nlinarith

/-- The residual set is nonempty as soon as `V` has a unit vector. -/
lemma unitResidualSet_nonempty_of_ne_bot (V x : Submodule ℝ E) (hV : V ≠ ⊥) :
    (unitResidualSet V x).Nonempty := by
  rcases exists_unit_of_ne_bot V hV with ⟨u, huV, hu1⟩
  exact ⟨‖u - x.starProjection u‖, u, huV, hu1, rfl⟩

/-- A line `Y ≤ v` has its residual value realized by a unit vector `u ∈ v` spanning it. -/
lemma lineToSubspace_eq_unit_residual_of_le {v x : Submodule ℝ E} (hxne : x ≠ ⊥)
    (Y : {Y : ℙ ℝ E // Y.submodule ≤ v}) :
    ∃ u : E, u ∈ v ∧ ‖u‖ = 1 ∧ lineToSubspace Y.1 x = ‖u - x.starProjection u‖ := by
  classical
  let u : E := (‖Y.1.rep‖)⁻¹ • Y.1.rep
  have hz0 : Y.1.rep ≠ 0 := Y.1.rep_nonzero
  have hz0' : (‖Y.1.rep‖) ≠ 0 := norm_ne_zero_iff.mpr hz0
  have huV : u ∈ v := by
    unfold u
    exact v.smul_mem (‖Y.1.rep‖)⁻¹ (Y.2 (rep_mem_self Y.1))
  have hu1 : ‖u‖ = 1 := by
    unfold u
    rw [norm_smul]
    rw [Real.norm_of_nonneg (inv_nonneg.mpr (norm_nonneg Y.1.rep))]
    rw [inv_mul_cancel₀ hz0']
  refine ⟨u, huV, hu1, ?_⟩
  -- Y and (mk u) span the same line, so the distances agree; then use the unit-line identity
  have hu0 : u ≠ 0 := ne_zero_of_norm_eq_one hu1
  have hsame : ∃ a : ℝ, a ≠ 0 ∧ (Projectivization.mk ℝ u hu0).rep = a • Y.1.rep := by
    rcases mk_rep_smul u hu0 with ⟨b, hb0, hrep⟩
    refine ⟨b * (‖Y.1.rep‖)⁻¹, ?_, ?_⟩
    · exact mul_ne_zero hb0 (inv_ne_zero hz0')
    · rw [hrep]
      unfold u
      rw [mul_smul]
  have heq : lineToSubspace Y.1 x = lineToSubspace (Projectivization.mk ℝ u hu0) x := by
    exact (lineToSubspace_eq_of_eq_rep (X := Y.1)
      (X' := Projectivization.mk ℝ u hu0) (s := x) hsame)
  rw [heq]
  exact lineToSubspace_mk_unit u hu1 hu0 x hxne

/-- **Upper bound**: the challenge-style distance (sup over lines of `v`, when `v` is the
smaller subspace) is at most the maximal residual `δ(v,x)`. -/
lemma distSubspacesMirror_le_planeResidualCore_of_lt (v x : Submodule ℝ E)
    (hvx : finrank ℝ v < finrank ℝ x) (hvn : v ≠ ⊥) (hxne : x ≠ ⊥) :
    distSubspacesMirror v x ≤ planeResidualCore v x := by
  classical
  -- the condition in the mirror def: finrank x ≤ finrank v is false
  have hcond : ¬ finrank ℝ x ≤ finrank ℝ v := by exact not_le_of_gt hvx
  unfold distSubspacesMirror planeResidualCore
  rw [if_neg hcond]
  haveI : Nonempty {Y : ℙ ℝ E // Y.submodule ≤ v} := by
    rcases exists_unit_of_ne_bot v hvn with ⟨w, hwv, hw1⟩
    exact ⟨⟨Projectivization.mk ℝ w (ne_zero_of_norm_eq_one hw1), by
      rw [Projectivization.submodule_mk]
      exact (Submodule.span_singleton_le_iff_mem w v).mpr hwv⟩⟩
  apply ciSup_le
  intro Y
  rcases lineToSubspace_eq_unit_residual_of_le (v := v) (x := x) hxne Y with ⟨u, huV, hu1, hY⟩
  have hmem : ‖u - x.starProjection u‖ ∈ unitResidualSet v x := by
    exact ⟨u, huV, hu1, rfl⟩
  calc
    lineToSubspace Y.1 x = ‖u - x.starProjection u‖ := hY
    _ ≤ sSup (unitResidualSet v x) := le_csSup (bddAbove_unitResidualSet v x) hmem

/-- **Lower bound**: the maximal residual `δ(v,x)` is at most the challenge-style distance. -/
lemma planeResidualCore_le_distSubspacesMirror_of_lt (v x : Submodule ℝ E)
    (hvx : finrank ℝ v < finrank ℝ x) (hvn : v ≠ ⊥) (hxne : x ≠ ⊥) :
    planeResidualCore v x ≤ distSubspacesMirror v x := by
  classical
  have hcond : ¬ finrank ℝ x ≤ finrank ℝ v := by exact not_le_of_gt hvx
  unfold distSubspacesMirror planeResidualCore
  rw [if_neg hcond]
  apply csSup_le (unitResidualSet_nonempty_of_ne_bot v x hvn)
  intro r hr
  rcases hr with ⟨u, huV, hu1, rfl⟩
  -- the line of u is ≤ v, and the value equals the residual
  have hu0 : u ≠ 0 := ne_zero_of_norm_eq_one hu1
  let Y : {Y : ℙ ℝ E // Y.submodule ≤ v} :=
    ⟨Projectivization.mk ℝ u hu0, by
      rw [Projectivization.submodule_mk]
      exact (Submodule.span_singleton_le_iff_mem u v).mpr huV⟩
  have hY : lineToSubspace Y.1 x = ‖u - x.starProjection u‖ := by
    exact lineToSubspace_mk_unit u hu1 hu0 x hxne
  have hbdd : BddAbove (Set.range (fun X : {X : ℙ ℝ E // X.submodule ≤ v} =>
      lineToSubspace X.1 x)) := by
    refine ⟨2, ?_⟩
    rintro y ⟨X, rfl⟩
    rcases lineToSubspace_eq_unit_residual_of_le (v := v) (x := x) hxne X with ⟨w, hwV, hw1, hX⟩
    change lineToSubspace X.1 x ≤ 2
    rw [hX]
    calc
      ‖w - x.starProjection w‖ ≤ ‖w‖ + ‖x.starProjection w‖ := norm_sub_le _ _
      _ ≤ 2 := by
        have hπ : ‖x.starProjection w‖ ≤ ‖w‖ := x.norm_starProjection_apply_le w
        nlinarith [hw1]
  calc
    ‖u - x.starProjection u‖ = lineToSubspace Y.1 x := hY.symm
    _ ≤ ⨆ X : {X : ℙ ℝ E // X.submodule ≤ v}, lineToSubspace X.1 x := le_ciSup hbdd Y

/-- **Main identification** (strict case): for `finrank v < finrank x` the challenge-style
`distSubspaces v x` equals the maximal unit residual `δ(v,x)`. -/
lemma distSubspacesMirror_eq_planeResidualCore_of_lt (v x : Submodule ℝ E)
    (hvx : finrank ℝ v < finrank ℝ x) (hvn : v ≠ ⊥) (hxne : x ≠ ⊥) :
    distSubspacesMirror v x = planeResidualCore v x := by
  exact le_antisymm
    (distSubspacesMirror_le_planeResidualCore_of_lt v x hvx hvn hxne)
    (planeResidualCore_le_distSubspacesMirror_of_lt v x hvx hvn hxne)

/-- **First branch**: the supremum over the lines of `a` (each measured against `b`) equals
the maximal unit residual of `a` onto `b`.  This is the content of `distSubspacesMirror x y`
when the dimension hypothesis selects the first branch (`finrank y ≤ finrank x`, where
`x := a`-measured and `y := b` provides the lines... precisely: the first branch of
`distSubspacesMirror v x` is the sup over lines of `x` measured to `v`, i.e. this lemma with
`a := x`, `b := v`). -/
lemma firstBranchSup_eq_planeResidualCore (a b : Submodule ℝ E) (ha : a ≠ ⊥) (hb : b ≠ ⊥) :
    (⨆ X : {X : ℙ ℝ E // X.submodule ≤ a}, lineToSubspace X.1 b) = planeResidualCore a b := by
  classical
  unfold planeResidualCore
  apply le_antisymm
  · haveI : Nonempty {X : ℙ ℝ E // X.submodule ≤ a} := by
      rcases exists_unit_of_ne_bot a ha with ⟨w, hwa, hw1⟩
      exact ⟨⟨Projectivization.mk ℝ w (ne_zero_of_norm_eq_one hw1), by
        rw [Projectivization.submodule_mk]
        exact (Submodule.span_singleton_le_iff_mem w a).mpr hwa⟩⟩
    apply ciSup_le
    intro X
    rcases lineToSubspace_eq_unit_residual_of_le (v := a) (x := b) hb X with ⟨u, hua, hu1, hX⟩
    have hmem : ‖u - b.starProjection u‖ ∈ unitResidualSet a b := by
      exact ⟨u, hua, hu1, rfl⟩
    calc
      lineToSubspace X.1 b = ‖u - b.starProjection u‖ := hX
      _ ≤ sSup (unitResidualSet a b) := le_csSup (bddAbove_unitResidualSet a b) hmem
  · apply csSup_le (unitResidualSet_nonempty_of_ne_bot a b ha)
    intro r hr
    rcases hr with ⟨u, hua, hu1, rfl⟩
    have hu0 : u ≠ 0 := ne_zero_of_norm_eq_one hu1
    let Y : {Y : ℙ ℝ E // Y.submodule ≤ a} :=
      ⟨Projectivization.mk ℝ u hu0, by
        rw [Projectivization.submodule_mk]
        exact (Submodule.span_singleton_le_iff_mem u a).mpr hua⟩
    have hY : lineToSubspace Y.1 b = ‖u - b.starProjection u‖ :=
      lineToSubspace_mk_unit u hu1 hu0 b hb
    have hbdd : BddAbove (Set.range (fun X : {X : ℙ ℝ E // X.submodule ≤ a} =>
        lineToSubspace X.1 b)) := by
      refine ⟨2, ?_⟩
      rintro y ⟨X, rfl⟩
      rcases lineToSubspace_eq_unit_residual_of_le (v := a) (x := b) hb X with ⟨w, hwa, hw1, hX⟩
      change lineToSubspace X.1 b ≤ 2
      rw [hX]
      calc
        ‖w - b.starProjection w‖ ≤ ‖w‖ + ‖b.starProjection w‖ := norm_sub_le _ _
        _ ≤ 2 := by
          have hπ : ‖b.starProjection w‖ ≤ ‖w‖ := b.norm_starProjection_apply_le w
          nlinarith [hw1]
    calc
      ‖u - b.starProjection u‖ = lineToSubspace Y.1 b := hY.symm
      _ ≤ ⨆ X : {X : ℙ ℝ E // X.submodule ≤ a}, lineToSubspace X.1 b := le_ciSup hbdd Y

end Submission.Bridge.SupLayer
