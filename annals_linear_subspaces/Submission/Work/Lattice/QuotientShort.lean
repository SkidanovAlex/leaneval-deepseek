import Mathlib
import Submission.Work.Lattice.WedgeProjection
import Submission.Work.Lattice.PhiPolygon
import Submission.Work.Lattice.IntrinsicIndex

/-!
# No short vector in the quotient (P2/P3 block layer, step A2)

The block analysis of paper §3 (Prop 4) controls the quotient lattice `W/V` of a nested
pair of tight subgroups `V ≤ W` of a full-rank lattice `Λ`.  The *lower* side — the
quotient has no vector much shorter than `e^{slope}` where `slope` is the slope of the
`φ`-Grayson polygon across the block containing `dim V` — is a direct consequence of
**`φ_A`-polygon below the data** (`PhiPolygon.phiPolygon_le_phi`) plus the exact
projection-covolume identity of `WedgeProjection`:

  for `V` a *tight* saturated subgroup (`φ_A(V) = phiPolygon Λ A (dim V)`) and any
  `w ∈ Λ` with `w ∉ realSpan V`, the quotient lattice `(V + ℤw)/V` has its generator of
  norm `‖w − π_V w‖` (the distance of `w` to `realSpan V`) bounded below by

      `log ‖w − π_V w‖ ≥ phiPolygon Λ A (dim V + 1) − phiPolygon Λ A (dim V) − A·d`.

Indeed `V' := V + ℤw` has rank `dim V + 1`, so the polygon lies below its data
(`phiPolygon Λ A (dim V + 1) ≤ log covol V' + A·(dim V+1)(d−dim V−1)`), while the projection
identity gives `log covol V' ≤ log covol V + log ‖w − π_V w‖`, and the tightness of `V`
expresses `log covol V` through `phiPolygon Λ A (dim V)`.  (On a block of the polygon,
consecutive differences of `phiPolygon` all equal the chord slope, so this is exactly the
"no vector shorter than the chord slope" statement the paper's Prop-4 induction uses.)

All declarations are Mathlib + Submission (WedgeProjection, PhiPolygon, IntrinsicIndex).
-/

noncomputable section
open Set Module Real
open scoped BigOperators
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1200000

namespace Submission.QuotientShort

open Submission.GraysonData
open Submission.GraysonLattice
open Submission.JoinSubmodularity
open Submission.IntrinsicIndex
open Submission.PhiSlack
open Submission.PhiPolygon
open Submission.WedgeProjection

/-- **No short vector in the quotient of a tight subgroup.**  Let `Λ` be a full-rank
lattice, `A > 0`, `V ≤ Λ` a nonzero saturated subgroup tight for the `φ_A`-polygon
(`phi A V = phiPolygon Λ A (subDim V)`), and `w ∈ Λ` with `w ∉ realSpan V`.  Then

`log ‖w − π_V w‖ ≥ phiPolygon Λ A (subDim V + 1) − phiPolygon Λ A (subDim V) − A·d`. -/
theorem log_dist_ge_polygon_slope {d : ℕ} (Λ : Submodule ℤ (E d)) [DiscreteTopology Λ]
    [IsZLattice ℝ Λ] (hΛfin : Module.finrank ℤ Λ = d) {A : ℝ} (hA : 0 < A)
    (V : Submodule ℤ (E d)) (hVsat : Saturated Λ V) (hV0 : V ≠ ⊥)
    (hVtight : phi A V = phiPolygon Λ A (subDim V))
    {w : E d} (hwΛ : w ∈ (Λ : Set (E d))) (hw : w ∉ realSpan V) :
    Real.log ‖w - (realSpan V).starProjection w‖ ≥
      phiPolygon Λ A (subDim V + 1) - phiPolygon Λ A (subDim V) - A * (d : ℝ) := by
  classical
  have hVle : V ≤ Λ := saturated_le Λ V hVsat
  rcases exists_basis_family_int_of_le_lattice (d := d) Λ hΛfin V hVle hV0 with
    ⟨u, hliRu, _hzli, hmemu, hspanu⟩
  have hb0 : 0 < subDim V := Nat.pos_of_ne_zero fun hz => hV0 ((subDim_eq_zero_iff_bot V).mp hz)
  -- real span identification
  have hspanR : Submodule.span ℝ (Set.range u) = realSpan V := by
    calc Submodule.span ℝ (Set.range u)
        = realSpan (Submodule.span ℤ (Set.range u)) := by
          rw [realSpan]
          exact (Submodule.span_span_of_tower (R := ℤ) (S := ℝ) (M := E d)
            (s := Set.range u)).symm
      _ = realSpan V := by rw [← hspanu]
  have hwspan : w ∉ Submodule.span ℝ (Set.range u) := by
    rw [hspanR]
    exact hw
  have hli_uw : LinearIndependent ℝ
      (Fin.snoc (α := fun _ : Fin (subDim V + 1) => E d) u w) :=
    linearIndependent_finSnoc.mpr ⟨hliRu, hwspan⟩
  -- V' := span of the appended family
  set V' : Submodule ℤ (E d) := Submodule.span ℤ (Set.range
    (Fin.snoc (α := fun _ : Fin (subDim V + 1) => E d) u w)) with hV'def
  have hV'le : V' ≤ Λ := by
    rw [hV'def, Submodule.span_le]
    rintro x ⟨i, rfl⟩
    rcases Fin.eq_castSucc_or_eq_last i with ⟨k, rfl⟩ | rfl
    · rw [Fin.snoc_castSucc]
      exact hmemu k
    · rw [Fin.snoc_last]
      exact hwΛ
  have hsubV' : subDim V' = subDim V + 1 := by
    rw [hV'def]
    exact subDim_span_range_of_linearIndependent _ hli_uw
  -- the covolume bound (projection identity)
  have hcov := latticeCovol_snoc_le_mul_dist (d := d) (r := subDim V) hb0 u w hliRu hli_uw
  have hcov' : latticeCovol V' ≤ latticeCovol V *
      ‖w - (realSpan V).starProjection w‖ := by
    have h1 : latticeCovol V' = latticeCovol (Submodule.span ℤ (Set.range
        (Fin.snoc (α := fun _ : Fin (subDim V + 1) => E d) u w))) := by rw [hV'def]
    have h2 : latticeCovol (Submodule.span ℤ (Set.range u)) = latticeCovol V :=
      (congrArg latticeCovol hspanu).symm
    rw [h1, ← h2, ← hspanR]
    exact hcov
  -- positivity of the two covolumes and of the distance
  have hdist0 : 0 < ‖w - (realSpan V).starProjection w‖ := by
    rw [norm_pos_iff]
    intro h0
    have h2 : w - (realSpan V).starProjection w = 0 := h0
    have h1 : w = (realSpan V).starProjection w := by
      have h3 := congrArg (fun x : E d => x + (realSpan V).starProjection w) h2
      simpa using h3
    exact hw (by rw [h1]; exact Submodule.starProjection_apply_mem _ w)
  have hcovVpos : 0 < latticeCovol V := latticeCovol_pos Λ V hVle hV0
  have hcovV'pos : 0 < latticeCovol V' := latticeCovol_pos Λ V' hV'le (by
    intro hz
    have hz0 : subDim V' = 0 := (subDim_eq_zero_iff_bot V').mpr hz
    rw [hsubV'] at hz0
    omega)
  -- log form
  have hlog : Real.log (latticeCovol V') ≤
      Real.log (latticeCovol V) + Real.log ‖w - (realSpan V).starProjection w‖ := by
    have h := Real.log_le_log hcovV'pos hcov'
    rwa [Real.log_mul hcovVpos.ne' hdist0.ne'] at h
  -- the polygon bound at V'
  have hpoly : phiPolygon Λ A (subDim V') ≤ phi A V' := phiPolygon_le_phi Λ V' hΛfin A hV'le
  -- tightness of V
  have htight : Real.log (latticeCovol V) = phiPolygon Λ A (subDim V) -
      A * ((subDim V : ℝ) * ((d : ℝ) - (subDim V : ℝ))) := by
    have h := hVtight
    simp only [phi] at h
    linarith [h]
  -- the arithmetic identity for the A-terms
  have hpoly' : phiPolygon Λ A (subDim V + 1) ≤
      Real.log (latticeCovol V') +
        A * (((subDim V : ℝ) + 1) * ((d : ℝ) - ((subDim V : ℝ) + 1))) := by
    have h := hpoly
    simp only [phi] at h
    rw [hsubV'] at h
    have hcast : ((subDim V + 1 : ℕ) : ℝ) = (subDim V : ℝ) + 1 := by push_cast; ring
    rw [hcast] at h
    exact h
  have hAid : A * ((subDim V : ℝ) * ((d : ℝ) - (subDim V : ℝ))) -
      A * (((subDim V : ℝ) + 1) * ((d : ℝ) - ((subDim V : ℝ) + 1))) =
      A * (2 * (subDim V : ℝ) + 1 - (d : ℝ)) := by ring
  have hAcmp : A * (-(d : ℝ)) ≤ A * (2 * (subDim V : ℝ) + 1 - (d : ℝ)) := by
    have hle : -(d : ℝ) ≤ 2 * (subDim V : ℝ) + 1 - (d : ℝ) := by
      have : (0 : ℝ) ≤ (subDim V : ℝ) := Nat.cast_nonneg _
      linarith
    exact mul_le_mul_of_nonneg_left hle (le_of_lt hA)
  linarith [hlog, hpoly', htight, hAid, hAcmp]

end Submission.QuotientShort
