import Mathlib
import Submission.Work.Lattice.MaxCovol
import Submission.Work.Lattice.PhiSlack

/-!
# The slacked max-norm Grayson value, and its submodularity

The Euclidean flag theory (`PhiSlack`, `PhiPolygon`, `PhiFlag`) uses
`phi A W = log (latticeCovol W) + A·dim W·(d − dim W)`.  For the **max-norm** polygon of the
§3 flow (which is what the accounting of de Saxcé's Lemma 4 needs, see the roadmap) the
corresponding object replaces the Euclidean covolume by the max-norm one
(`MaxCovol.maxCovol`):

`maxPhi A W = maxCovol W + A·dim W·(d − dim W)`.

This module records

* `A₂ d j := ½ log (choose d j)` — the norm-comparability constant;
* `maxPhi_le_phi` / `phi_le_maxPhi_add` — the pointwise comparison
  `maxPhi A X ≤ phi A X ≤ maxPhi A X + A₂ d (subDim X)`;
* **`maxPhi_incomparable_slack`** — submodularity with slack for incomparable saturated
  `V, W ≤ Λ`:
  `maxPhi(V⊓W) + maxPhi(V⊔W) + 2A ≤ maxPhi V + maxPhi W + A₂ d (subDim V) + A₂ d (subDim W)`
  (Euclidean `PhiSlack.phi_incomparable_slack` + the two comparisons).

So the incomparable-case slack `2A` of the Euclidean theory survives the change of norm as soon
as `A` dominates the comparability constants, which is the input the max-norm flag argument needs.

Module `Submission.Work.Lattice.MaxPhi`, namespace `Submission.MaxPhi`.
-/

noncomputable section

open Module exteriorPower InnerProductGeometry Real
open scoped BigOperators
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1000000

namespace Submission.MaxPhi

open Submission.GraysonLattice
open Submission.GraysonData
open Submission.LatticePolygon
open Submission.PhiSlack
open Submission.MaxCovol
open Submission.JoinSubmodularity

variable {d : ℕ}

/-- The norm-comparability constant `A₂ d j = ½ log (choose d j)`. -/
noncomputable def A₂ (d j : ℕ) : ℝ := (1 / 2) * Real.log (Nat.choose d j)

/-- **The slacked max-norm Grayson value** `maxPhi A W = maxCovol W + A·dim W·(d − dim W)`. -/
noncomputable def maxPhi (Λ : Submodule ℤ (E d)) [DiscreteTopology Λ] [IsZLattice ℝ Λ]
    (hΛfin : Module.finrank ℤ Λ = d) (A : ℝ) (W : Submodule ℤ (E d)) (hWΛ : W ≤ Λ) : ℝ :=
  maxCovol (d := d) Λ hΛfin W hWΛ + A * ((subDim W : ℝ) * ((d : ℝ) - (subDim W : ℝ)))

/-- The max-norm value is below the Euclidean one. -/
theorem maxPhi_le_phi {Λ X : Submodule ℤ (E d)} [DiscreteTopology Λ] [IsZLattice ℝ Λ]
    {hΛfin : Module.finrank ℤ Λ = d} {A : ℝ} {hXΛ : X ≤ Λ} :
    maxPhi (d := d) Λ hΛfin A X hXΛ ≤ phi A X := by
  rw [maxPhi, phi]
  linarith [maxCovol_le_log_latticeCovol (d := d) (Λ := Λ) (hΛfin := hΛfin) (X := X)
    (hXΛ := hXΛ)]

/-- The Euclidean value is below the max-norm one plus `A₂`. -/
theorem phi_le_maxPhi_add {Λ X : Submodule ℤ (E d)} [DiscreteTopology Λ] [IsZLattice ℝ Λ]
    {hΛfin : Module.finrank ℤ Λ = d} {A : ℝ} {hXΛ : X ≤ Λ} :
    phi A X ≤ maxPhi (d := d) Λ hΛfin A X hXΛ + A₂ d (subDim X) := by
  rw [maxPhi, phi, A₂]
  linarith [log_latticeCovol_le_maxCovol_add (d := d) (Λ := Λ) (hΛfin := hΛfin) (X := X)
    (hXΛ := hXΛ)]

/-- **Submodularity with slack for the max-norm value** (incomparable case). -/
theorem maxPhi_incomparable_slack {Λ V W : Submodule ℤ (E d)} [DiscreteTopology Λ]
    [IsZLattice ℝ Λ] (hΛfin : Module.finrank ℤ Λ = d) {A : ℝ} (hA : 0 < A)
    (hVsat : Saturated Λ V) (hWsat : Saturated Λ W)
    (hinc : ¬ (V ≤ W) ∧ ¬ (W ≤ V)) :
    maxPhi (d := d) Λ hΛfin A V (saturated_le Λ V hVsat) +
        maxPhi (d := d) Λ hΛfin A W (saturated_le Λ W hWsat) ≥
      maxPhi (d := d) Λ hΛfin A (V ⊓ W)
          (le_trans inf_le_left (saturated_le Λ V hVsat)) +
        maxPhi (d := d) Λ hΛfin A (V ⊔ W)
          (sup_le (saturated_le Λ V hVsat) (saturated_le Λ W hWsat)) +
        2 * A - (A₂ d (subDim V) + A₂ d (subDim W)) := by
  have hslack := phi_incomparable_slack Λ V W hΛfin hA hVsat hWsat hinc
  have h1 := maxPhi_le_phi (d := d) (Λ := Λ) (hΛfin := hΛfin) (A := A)
    (X := V) (hXΛ := saturated_le Λ V hVsat)
  have h2 := maxPhi_le_phi (d := d) (Λ := Λ) (hΛfin := hΛfin) (A := A)
    (X := W) (hXΛ := saturated_le Λ W hWsat)
  have h3 := phi_le_maxPhi_add (d := d) (Λ := Λ) (hΛfin := hΛfin) (A := A)
    (X := V) (hXΛ := saturated_le Λ V hVsat)
  have h4 := phi_le_maxPhi_add (d := d) (Λ := Λ) (hΛfin := hΛfin) (A := A)
    (X := W) (hXΛ := saturated_le Λ W hWsat)
  have h5 := maxPhi_le_phi (d := d) (Λ := Λ) (hΛfin := hΛfin) (A := A)
    (X := V ⊓ W) (hXΛ := le_trans inf_le_left (saturated_le Λ V hVsat))
  have h6 := maxPhi_le_phi (d := d) (Λ := Λ) (hΛfin := hΛfin) (A := A)
    (X := V ⊔ W) (hXΛ := sup_le (saturated_le Λ V hVsat) (saturated_le Λ W hWsat))
  linarith [hslack, h1, h2, h3, h4, h5, h6]

/-! ## The comparability of tight realisers for the max-norm value -/

/-- The crude bound `A₂ d j ≤ (d/2)·log 2` (since `choose d j ≤ 2^d`). -/
lemma A₂_le_log_two {d j : ℕ} (hjd : j ≤ d) :
    A₂ d j ≤ (d : ℝ) * Real.log 2 / 2 := by
  have hch : (Nat.choose d j : ℝ) ≤ (2 : ℝ) ^ d := by
    have h := (Nat.sum_range_choose d).le
    -- `∑_{k ≤ d} choose d k = 2^d`, so each term is at most `2^d`
    exact_mod_cast (Finset.single_le_sum (f := fun k => Nat.choose d k)
      (fun k _ => Nat.zero_le _) (Finset.mem_range.mpr (Nat.lt_succ_of_le hjd))) |>.trans_eq (by
        rw [Nat.sum_range_choose])
  have hpos : (0 : ℝ) < (Nat.choose d j : ℝ) := by
    exact_mod_cast Nat.choose_pos hjd
  rw [A₂]
  have hlog : Real.log (Nat.choose d j : ℝ) ≤ (d : ℝ) * Real.log 2 := by
    have := Real.log_le_log hpos hch
    rwa [Real.log_pow] at this
  linarith

/-- **Compatibility of tight realisers for the max-norm value.**  Let `c` be discrete-convex on
`{0,…,d}` and below the max-norm data at `V⊓W` and `V⊔W`.  If the saturated subgroups `V, W ≤ Λ`
are max-norm-tight (`maxPhi A V = c (subDim V)`, `maxPhi A W = c (subDim W)`), then `V` and `W`
are comparable, provided `A > (d/2)·log 2 ≥ A₂`. -/
theorem maxPhi_comparable_of_tight {Λ V W : Submodule ℤ (E d)} [DiscreteTopology Λ]
    [IsZLattice ℝ Λ] (hΛfin : Module.finrank ℤ Λ = d) {A : ℝ}
    (hA : (d : ℝ) * Real.log 2 / 2 < A)
    (hVsat : Saturated Λ V) (hWsat : Saturated Λ W) {c : ℕ → ℝ}
    (hcvx : Submission.Polygon.DiscreteConvexOn c d)
    (hVtight : maxPhi (d := d) Λ hΛfin A V (saturated_le Λ V hVsat) = c (subDim V))
    (hWtight : maxPhi (d := d) Λ hΛfin A W (saturated_le Λ W hWsat) = c (subDim W))
    (hinf : c (subDim (V ⊓ W)) ≤ maxPhi (d := d) Λ hΛfin A (V ⊓ W)
      (le_trans inf_le_left (saturated_le Λ V hVsat)))
    (hsup : c (subDim (V ⊔ W)) ≤ maxPhi (d := d) Λ hΛfin A (V ⊔ W)
      (sup_le (saturated_le Λ V hVsat) (saturated_le Λ W hWsat))) :
    V ≤ W ∨ W ≤ V := by
  by_contra hcon
  rw [not_or] at hcon
  have hinc : ¬ (V ≤ W) ∧ ¬ (W ≤ V) := hcon
  have hApos : 0 < A := by
    have h0 : 0 ≤ (d : ℝ) * Real.log 2 / 2 := by positivity
    linarith
  have hslack := maxPhi_incomparable_slack (Λ := Λ) (V := V) (W := W) hΛfin (A := A) hApos
    hVsat hWsat hinc
  have hmk : subDim (V ⊓ W) < subDim V :=
    subDim_inf_lt_of_ne Λ V W hVsat hWsat (fun h => hinc.1 (inf_eq_left.mp h))
  have hmℓ : subDim (V ⊓ W) < subDim W := by
    simpa [inf_comm] using subDim_inf_lt_of_ne Λ W V hWsat hVsat
      (fun h => hinc.2 (inf_eq_left.mp h))
  have hadd := subDim_inf_add_subDim_sup Λ V W hVsat hWsat
  have hmaxn : max (subDim V) (subDim W) ≤ subDim (V ⊔ W) := by omega
  have hnd : subDim (V ⊔ W) ≤ d := subDim_le_ambient (V ⊔ W)
  have heq : subDim (V ⊓ W) + subDim (V ⊔ W) =
      min (subDim V) (subDim W) + max (subDim V) (subDim W) := by omega
  have hconv := Submission.Polygon.convex_rank_equation hcvx
    (m := subDim (V ⊓ W)) (k := min (subDim V) (subDim W))
    (ℓ := max (subDim V) (subDim W)) (n := subDim (V ⊔ W))
    (le_min hmk.le hmℓ.le) (le_trans (min_le_left _ _) (le_max_left _ _)) hmaxn hnd heq
  have hconv' : c (subDim (V ⊓ W)) + c (subDim (V ⊔ W)) ≥
      c (subDim V) + c (subDim W) := by
    have : c (min (subDim V) (subDim W)) + c (max (subDim V) (subDim W)) =
        c (subDim V) + c (subDim W) := by
      rcases le_total (subDim V) (subDim W) with h | h
      · rw [min_eq_left h, max_eq_right h]
      · rw [min_eq_right h, max_eq_left h, add_comm]
    rwa [this] at hconv
  have hb := A₂_le_log_two (d := d) (j := subDim V) (subDim_le_ambient V)
  have hb' := A₂_le_log_two (d := d) (j := subDim W) (subDim_le_ambient W)
  linarith [hslack, hconv', hVtight, hWtight, hinf, hsup, hb, hb']

end Submission.MaxPhi

end
