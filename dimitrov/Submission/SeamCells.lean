import Mathlib
import Submission.E2bCells
import Submission.E2bTelescope
import Submission.SepLemma
import Submission.StarGeom

/-!
# Seam cells: windows crossing the arg branch ±π (the last direction)

`Submission.E2bCells` supplies the window/gap cell zeros for angular ranges
inside `(−π, π]` (non-seam cells).  The only remaining geometric case is a
window that crosses the branch of `Complex.arg` at `π` -- possible only for
the LAST direction `x := (dirList S).get i` of the spike spine, and only
when `x + δ > π` (unavoidable when `x = π`, i.e. a spike on the negative
real axis).  This module proves the seam window zero for `x < π`:

    seam_window_zero_lt_pi :  cellExpr (pull h) u B (x−δ) (x+δ) = 0

PROOF (split at `π` + shift + glue):
* lower piece `(x−δ, π)`: ordinary above-the-tip window cell
  (`E2bCells.window_cell_zero_gen`; the window contains only `x` by the
  consecutive-gap separation, and spikes along `x` are short);
* upper piece `(π, x+δ)`: shifted by `−2π` to `(−π, d)`,
  `d := x + δ − 2π ∈ (−π, 0)`; the rectangle over `(−π, d)` is star-free
  because all directions are `≥ x₀ > d` (interior points have argument in
  `(−π, d]`; the boundary at `im = −π` lies on the negative real axis of
  argument `π`, which is NOT a direction since `x < π` and `x` is the last
  direction) -- `expRect_avoids_star_from_npi` + `cellExpr_zero_npi`;
* glue `cellExpr_split_zero` (arc integrability supplied as hypotheses).

Both seam cases are PROVED here:

* `seam_window_zero_lt_pi` (direction `x < π`, window crossing above `π`):
  split at `π`; lower piece above-tip window cell; upper piece shifted by
  `−2π` to `(−π, d)` (`d := x+δ−2π`), star-free because no direction lies
  in `(−π, d]` (wrap gap) and `π` is not a direction
  (`expRect_avoids_star_from_npi` + `cellExpr_zero_npi`);
* `seam_window_zero_pi` (direction `x = π`): same split, but the negative
  real axis IS a spike direction, so the boundary of the shifted cell at
  `im = −π` is handled by the modulus bound `‖−e^t‖ = e^t ≥ e^u` above all
  `π`-spike tips (`expRect_avoids_star_pi_boundary`).
-/

noncomputable section
open scoped Complex Real Interval BigOperators
open Complex
open MeasureTheory

namespace Submission.SeamCells

open Submission.XTransfer
open Submission.DirSet
open Submission.DirCycle
open Submission.E2bT
open Submission.Fold
open Submission.PolyaShell
open Submission.E2bCells

/-- Star-avoidance for a w-rectangle whose imaginary range starts at `−π`
(the arg-branch): interior points have argument in `(−π, ymax]` (covered by
`hno`), and the boundary points at `im = −π` lie on the negative real axis
(argument `π`, excluded by `hnopi`). -/
lemma expRect_avoids_star_from_npi {S : Finset ℂ} (hS0 : ∀ z ∈ S, z ≠ 0)
    {xmin xmax ymax : ℝ} (hy : -Real.pi < ymax) (hyu : ymax ≤ Real.pi)
    (hno : ∀ z ∈ S,
      Complex.arg (z ^ 2) ∉ Set.Icc (-Real.pi) ymax ∧
      Complex.arg (z ^ 4) ∉ Set.Icc (-Real.pi) ymax)
    (hnopi : ∀ z ∈ S,
      Complex.arg (z ^ 2) ≠ Real.pi ∧ Complex.arg (z ^ 4) ≠ Real.pi) :
    ∀ w ∈ ([[xmin, xmax]] ×ℂ [[-Real.pi, ymax]]), Complex.exp w ∉ star S := by
  intro w hw hws
  have hwim : w.im ∈ Set.Icc (-Real.pi) ymax := by
    have hwim0 := (Complex.mem_reProdIm.mp hw).2
    have hu : Set.uIcc (-Real.pi) ymax = Set.Icc (-Real.pi) ymax := Set.uIcc_of_le (le_of_lt hy)
    simpa [hu] using hwim0
  have hstar : ∃ z ∈ S, Complex.exp w ∈ segment ℝ 0 (z ^ 2) ∨ Complex.exp w ∈ segment ℝ 0 (z ^ 4) := by
    change ∃ z ∈ S, Complex.exp w ∈ segment ℝ 0 (z ^ 2) ∨ Complex.exp w ∈ segment ℝ 0 (z ^ 4) at hws
    exact hws
  rcases hstar with ⟨z, hz, hseg⟩
  have hexp0 : Complex.exp w ≠ 0 := Complex.exp_ne_zero w
  by_cases hmin : -Real.pi < w.im
  · have hargw : Complex.arg (Complex.exp w) = w.im := StarGeom.arg_exp_eq_im hmin (le_trans hwim.2 hyu)
    rcases hseg with h2 | h4
    · have harg2 : Complex.arg (z ^ 2) = w.im := by
        calc
          Complex.arg (z ^ 2) = Complex.arg (Complex.exp w) :=
            (StarGeom.arg_eq_of_mem_segment_zero_ne_zero h2 hexp0).symm
          _ = w.im := hargw
      exfalso
      exact (hno z hz).1 (by
        rw [harg2]
        exact hwim)
    · have harg4 : Complex.arg (z ^ 4) = w.im := by
        calc
          Complex.arg (z ^ 4) = Complex.arg (Complex.exp w) :=
            (StarGeom.arg_eq_of_mem_segment_zero_ne_zero h4 hexp0).symm
          _ = w.im := hargw
      exfalso
      exact (hno z hz).2 (by
        rw [harg4]
        exact hwim)
  · have hmin_eq : w.im = -Real.pi := le_antisymm (le_of_not_gt hmin) hwim.1
    have hargw : Complex.arg (Complex.exp w) = Real.pi := by
      have harg := Complex.arg_exp w
      rw [hmin_eq] at harg
      rw [harg]
      rw [toIocMod_eq_iff Real.two_pi_pos (a := -Real.pi) (b := -Real.pi) (c := Real.pi)]
      constructor
      · constructor
        · linarith
        · linarith
      · refine ⟨-1, ?_⟩
        simp
        ring
    rcases hseg with h2 | h4
    · have harg2 : Complex.arg (z ^ 2) = Real.pi := by
        calc
          Complex.arg (z ^ 2) = Complex.arg (Complex.exp w) :=
            (StarGeom.arg_eq_of_mem_segment_zero_ne_zero h2 hexp0).symm
          _ = Real.pi := hargw
      exact (hnopi z hz).1 harg2
    · have harg4 : Complex.arg (z ^ 4) = Real.pi := by
        calc
          Complex.arg (z ^ 4) = Complex.arg (Complex.exp w) :=
            (StarGeom.arg_eq_of_mem_segment_zero_ne_zero h4 hexp0).symm
          _ = Real.pi := hargw
      exact (hnopi z hz).2 harg4

/-- Cell zero for the shifted upper seam piece (range starting at −π). -/
lemma cellExpr_zero_npi {S : Finset ℂ} (hS0 : ∀ z ∈ S, z ≠ 0)
    {h : ℂ → ℂ} (hh : DifferentiableOn ℂ h (Submission.XTransfer.star S)ᶜ)
    (u B : ℝ) {d : ℝ} (hnd : -Real.pi < d) (hdu : d ≤ Real.pi)
    (hno : ∀ z ∈ S,
      Complex.arg (z ^ 2) ∉ Set.Icc (-Real.pi) d ∧
      Complex.arg (z ^ 4) ∉ Set.Icc (-Real.pi) d)
    (hnopi : ∀ z ∈ S,
      Complex.arg (z ^ 2) ≠ Real.pi ∧ Complex.arg (z ^ 4) ≠ Real.pi) :
    cellExpr (Submission.E2bCore.pull h) u B (-Real.pi) d = 0 := by
  have hR : ∀ w ∈ ([[u, B]] ×ℂ [[-Real.pi, d]]),
      Complex.exp w ∈ (Submission.XTransfer.star S)ᶜ := by
    intro w hw
    exact expRect_avoids_star_from_npi hS0 hnd hdu hno hnopi w hw
  exact Fold.pullback_cell_zero h u B (-Real.pi) d
    (sector_cauchy_of_star_compl hh u B (-Real.pi) d hR)

/-- The first direction is the minimum of `dirSet S`. -/
lemma dirList_head_le (S : Finset ℂ) (hlen0 : 0 < (dirList S).length)
    {θ : ℝ} (hθ : θ ∈ dirSet S) :
    (dirList S).get ⟨0, hlen0⟩ ≤ θ := by
  classical
  rcases (List.mem_iff_get.mp ((dirList_mem_iff S θ).mpr hθ)) with ⟨k, rfl⟩
  exact dirList_get_mono S (i := ⟨0, hlen0⟩) (j := k) (by
    have hk0 : 0 ≤ k.val := Nat.zero_le k.val
    simpa using hk0)

/-- If `i` is the last index, `(dirList S).get i` is the maximum direction. -/
lemma dirList_last_ge (S : Finset ℂ) (i : Fin (dirList S).length)
    (hlast : i.val + 1 = (dirList S).length) {θ : ℝ} (hθ : θ ∈ dirSet S) :
    θ ≤ (dirList S).get i := by
  classical
  rcases (List.mem_iff_get.mp ((dirList_mem_iff S θ).mpr hθ)) with ⟨k, rfl⟩
  have hki : k.val ≤ i.val := by
    have hk : k.val < (dirList S).length := k.isLt
    omega
  exact dirList_get_mono S (i := k) (j := i) hki

/-- **Seam window zero (direction below `π`).**  The window of the last
direction `x` (crossing above `π`) has zero boundary integral: split at `π`,
the lower piece `(x−δ, π)` is an above-tip window cell
(`window_cell_zero_gen`) and the upper piece `(π, x+δ)`, shifted by `−2π`
to `(−π, x+δ−2π)`, is a direction-free gap cell (`cellExpr_zero_npi`); the
glue is `cellExpr_split_zero` (integrability supplied by hypothesis). -/
theorem seam_window_zero_lt_pi (S : Finset ℂ) (hS0 : ∀ z ∈ S, z ≠ 0)
    {h : ℂ → ℂ} (hh : DifferentiableOn ℂ h (Submission.XTransfer.star S)ᶜ)
    (δ u B : ℝ) (hδ : 0 < δ)
    (hsep : ∀ (j : ℕ) (hj : j + 1 < (dirList S).length),
      (dirList S).get ⟨j + 1, hj⟩ -
        (dirList S).get ⟨j, Nat.lt_trans (Nat.lt_succ_self j) hj⟩ > 2 * δ)
    (i : Fin (dirList S).length) (hlast : i.val + 1 = (dirList S).length)
    (hwrap : 2 * Real.pi + (dirList S).get ⟨0, by
        have h0 : 0 < (dirList S).length := by
          have : i.val < (dirList S).length := i.isLt
          omega
        exact h0⟩ - (dirList S).get i > 2 * δ)
    (hxlt : (dirList S).get i < Real.pi)
    (hxseam : Real.pi < (dirList S).get i + δ)
    (hcl : -Real.pi < (dirList S).get i - δ)
    (hshort : ∀ w ∈ spikeEndpoints S,
      Complex.arg w = (dirList S).get i → ‖w‖ < Real.exp u)
    (hub : u ≤ B)
    (hbarc1 : IntervalIntegrable (fun y : ℝ =>
        Submission.E2bCore.pull h (B + y * Complex.I)) volume ((dirList S).get i - δ) Real.pi)
    (hbarc2 : IntervalIntegrable (fun y : ℝ =>
        Submission.E2bCore.pull h (B + y * Complex.I)) volume Real.pi ((dirList S).get i + δ))
    (huarc1 : IntervalIntegrable (fun y : ℝ =>
        Submission.E2bCore.pull h (u + y * Complex.I)) volume ((dirList S).get i - δ) Real.pi)
    (huarc2 : IntervalIntegrable (fun y : ℝ =>
        Submission.E2bCore.pull h (u + y * Complex.I)) volume Real.pi ((dirList S).get i + δ)) :
    cellExpr (Submission.E2bCore.pull h) u B
      ((dirList S).get i - δ) ((dirList S).get i + δ) = 0 := by
  classical
  let x : ℝ := (dirList S).get i
  have hlen0 : 0 < (dirList S).length := by
    have : i.val < (dirList S).length := i.isLt
    omega
  have hxseam' : Real.pi < x + δ := by simpa [x] using hxseam
  have hxlt' : x < Real.pi := by simpa [x] using hxlt
  have hcl' : -Real.pi < x - δ := by simpa [x] using hcl
  -- lower piece zero (above-the-tip window over (x−δ, π))
  have hsepiL : ∀ θ ∈ dirSet S, θ ∈ Set.Icc (x - δ) Real.pi → θ = x := by
    intro θ hθ hwin
    have hwin' : θ ∈ Set.Icc (x - δ) (x + δ) := by
      exact ⟨hwin.1, le_trans hwin.2 (le_of_lt hxseam')⟩
    exact SepLemma.dirList_window_separated (S := S) (δ := δ) hsep i hθ (by simpa [x] using hwin')
  have hpieceL : cellExpr (Submission.E2bCore.pull h) u B (x - δ) Real.pi = 0 := by
    simpa [x] using (Submission.E2bCells.window_cell_zero_gen S hS0 hh u B hub (x := x)
      (c := x - δ) (d := Real.pi) (by linarith [hδ]) hcl' (le_refl Real.pi) hsepiL
      (by simpa [x] using hshort))
  -- upper piece: shift (π, x+δ) by −2π to (−π, d)
  let d : ℝ := x + δ - 2 * Real.pi
  have hd : d ≤ Real.pi := by
    dsimp [d]
    have hxle : x ≤ Real.pi := le_of_lt hxlt'
    linarith
  have hdn : -Real.pi < d := by
    dsimp [d]
    linarith [hxseam']
  -- no direction in [−π, d]: all directions ≥ x₀ > d (from hwrap)
  have hnoDir : ∀ θ ∈ dirSet S, θ ∉ Set.Icc (-Real.pi) d := by
    intro θ hθ hθd
    let x0 : ℝ := (dirList S).get ⟨0, hlen0⟩
    let xi : ℝ := (dirList S).get i
    have hmin : x0 ≤ θ := by
      simpa [x0] using dirList_head_le S hlen0 hθ
    have hx0gt : d < x0 := by
      have hwrap0 : 2 * Real.pi + x0 - xi > 2 * δ := by
        have hw : (dirList S).get ⟨0, by
            have h0 : 0 < (dirList S).length := by
              have : i.val < (dirList S).length := i.isLt
              omega
            exact h0⟩ = (dirList S).get ⟨0, hlen0⟩ := by
          exact congrArg (fun e : Fin (dirList S).length => (dirList S).get e)
            (Fin.ext rfl)
        dsimp [x0, xi]
        simpa [hw] using hwrap
      dsimp [x0, xi] at hwrap0
      dsimp [d, x, x0, xi]
      linarith [hwrap0, hδ]
    have hdθ : d < θ := lt_of_lt_of_le hx0gt hmin
    exact (not_lt_of_ge hθd.2) hdθ
  have hno : ∀ z ∈ S,
      Complex.arg (z ^ 2) ∉ Set.Icc (-Real.pi) d ∧
      Complex.arg (z ^ 4) ∉ Set.Icc (-Real.pi) d :=
    endpoints_no_arg_of_dirSet_free (S := S) (c := -Real.pi) (d := d) hnoDir
  -- no endpoint at argument π (x < π and x is the last direction)
  have hnopi : ∀ z ∈ S,
      Complex.arg (z ^ 2) ≠ Real.pi ∧ Complex.arg (z ^ 4) ≠ Real.pi := by
    intro z hz
    constructor
    · intro h
      have hargD : Complex.arg (z ^ 2) ∈ dirSet S := arg_sq_mem_dirSet hz
      have hle : Complex.arg (z ^ 2) ≤ x := by
        simpa [x] using dirList_last_ge S i hlast hargD
      have : x < Complex.arg (z ^ 2) := by simpa [← h] using hxlt'
      linarith
    · intro h
      have hargD : Complex.arg (z ^ 4) ∈ dirSet S := arg_pow4_mem_dirSet hz
      have hle : Complex.arg (z ^ 4) ≤ x := by
        simpa [x] using dirList_last_ge S i hlast hargD
      have : x < Complex.arg (z ^ 4) := by simpa [← h] using hxlt'
      linarith
  have hpieceR' : cellExpr (Submission.E2bCore.pull h) u B (-Real.pi) d = 0 :=
    cellExpr_zero_npi hS0 hh u B hdn hd hno hnopi
  have hpieceR : cellExpr (Submission.E2bCore.pull h) u B Real.pi (x + δ) = 0 := by
    have hs := cellExpr_sub_two_pi h u B Real.pi (x + δ)
    have hc1 : Real.pi - 2 * Real.pi = -Real.pi := by ring
    have hc2 : (x + δ) - 2 * Real.pi = d := rfl
    rw [hc1] at hs
    rw [hc2] at hs
    have hconv : cellExpr (Submission.E2bCore.pull h) u B Real.pi (x + δ) =
        cellExpr (Submission.E2bCore.pull h) u B (-Real.pi) d := hs.symm
    rw [hconv]
    exact hpieceR'
  -- glue
  exact cellExpr_split_zero h u B (x - δ) Real.pi (x + δ)
    (by simpa [x] using hpieceL) (by simpa [x] using hpieceR)
    hbarc1 hbarc2 huarc1 huarc2

lemma expRect_avoids_star_pi_boundary {S : Finset ℂ} (hS0 : ∀ z ∈ S, z ≠ 0)
    {xmin xmax ymax : ℝ} (hx : xmin ≤ xmax) (hy : -Real.pi < ymax) (hyu : ymax ≤ Real.pi)
    (hno : ∀ z ∈ S,
      Complex.arg (z ^ 2) ∉ Set.Icc (-Real.pi) ymax ∧
      Complex.arg (z ^ 4) ∉ Set.Icc (-Real.pi) ymax)
    (hshortπ : ∀ w ∈ spikeEndpoints S, Complex.arg w = Real.pi → ‖w‖ < Real.exp xmin) :
    ∀ w ∈ ([[xmin, xmax]] ×ℂ [[-Real.pi, ymax]]), Complex.exp w ∉ star S := by
  intro w hw hws
  have hwim : w.im ∈ Set.Icc (-Real.pi) ymax := by
    have hwim0 := (Complex.mem_reProdIm.mp hw).2
    have hu : Set.uIcc (-Real.pi) ymax = Set.Icc (-Real.pi) ymax := Set.uIcc_of_le (le_of_lt hy)
    simpa [hu] using hwim0
  have hwre : w.re ∈ Set.Icc xmin xmax := by
    have hwre0 := (Complex.mem_reProdIm.mp hw).1
    have hu : Set.uIcc xmin xmax = Set.Icc xmin xmax := Set.uIcc_of_le hx
    simpa [hu] using hwre0
  have hstar : ∃ z ∈ S, Complex.exp w ∈ segment ℝ 0 (z ^ 2) ∨ Complex.exp w ∈ segment ℝ 0 (z ^ 4) := by
    change ∃ z ∈ S, Complex.exp w ∈ segment ℝ 0 (z ^ 2) ∨ Complex.exp w ∈ segment ℝ 0 (z ^ 4) at hws
    exact hws
  rcases hstar with ⟨z, hz, hseg⟩
  have hexp0 : Complex.exp w ≠ 0 := Complex.exp_ne_zero w
  by_cases hmin : -Real.pi < w.im
  · have hargw : Complex.arg (Complex.exp w) = w.im := StarGeom.arg_exp_eq_im hmin (le_trans hwim.2 hyu)
    rcases hseg with h2 | h4
    · have harg2 : Complex.arg (z ^ 2) = w.im := by
        calc
          Complex.arg (z ^ 2) = Complex.arg (Complex.exp w) :=
            (StarGeom.arg_eq_of_mem_segment_zero_ne_zero h2 hexp0).symm
          _ = w.im := hargw
      exfalso
      exact (hno z hz).1 (by
        rw [harg2]
        exact hwim)
    · have harg4 : Complex.arg (z ^ 4) = w.im := by
        calc
          Complex.arg (z ^ 4) = Complex.arg (Complex.exp w) :=
            (StarGeom.arg_eq_of_mem_segment_zero_ne_zero h4 hexp0).symm
          _ = w.im := hargw
      exfalso
      exact (hno z hz).2 (by
        rw [harg4]
        exact hwim)
  · have hmin_eq : w.im = -Real.pi := le_antisymm (le_of_not_gt hmin) hwim.1
    -- boundary: X = exp w = −e^{w.re}, ‖X‖ = exp (w.re) ≥ exp xmin > ‖z²‖, ‖z⁴‖ (π-spikes)
    have hXarg : Complex.arg (Complex.exp w) = Real.pi := by
      have harg := Complex.arg_exp w
      rw [hmin_eq] at harg
      rw [harg]
      rw [toIocMod_eq_iff Real.two_pi_pos (a := -Real.pi) (b := -Real.pi) (c := Real.pi)]
      constructor
      · constructor
        · linarith
        · linarith
      · refine ⟨-1, ?_⟩
        simp
        ring
    have hXnorm : Real.exp xmin ≤ ‖Complex.exp w‖ := by
      have hre_ge : xmin ≤ w.re := hwre.1
      have hexpmono : Real.exp xmin ≤ Real.exp w.re := Real.exp_le_exp.mpr hre_ge
      rw [Complex.norm_exp]
      exact hexpmono
    rcases hseg with h2 | h4
    · have harg2 : Complex.arg (z ^ 2) = Real.pi := by
        calc
          Complex.arg (z ^ 2) = Complex.arg (Complex.exp w) :=
            (StarGeom.arg_eq_of_mem_segment_zero_ne_zero h2 hexp0).symm
          _ = Real.pi := hXarg
      have hshort' : ‖z ^ 2‖ < Real.exp xmin := hshortπ (z ^ 2) (spikeEndpoints_mem_sq S hz) harg2
      have hle_norm : ‖Complex.exp w‖ ≤ ‖z ^ 2‖ := by
        rcases (mem_segment_zero_iff (z ^ 2) (Complex.exp w)).mp h2 with ⟨t, ht01, htX⟩
        calc
          ‖Complex.exp w‖ = ‖t • (z ^ 2)‖ := by rw [htX]
          _ = t * ‖z ^ 2‖ := by
            rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ht01.1]
          _ ≤ ‖z ^ 2‖ := mul_le_of_le_one_left (norm_nonneg (z ^ 2)) ht01.2
      linarith
    · have harg4 : Complex.arg (z ^ 4) = Real.pi := by
        calc
          Complex.arg (z ^ 4) = Complex.arg (Complex.exp w) :=
            (StarGeom.arg_eq_of_mem_segment_zero_ne_zero h4 hexp0).symm
          _ = Real.pi := hXarg
      have hshort' : ‖z ^ 4‖ < Real.exp xmin := hshortπ (z ^ 4) (spikeEndpoints_mem_pow4 S hz) harg4
      have hle_norm : ‖Complex.exp w‖ ≤ ‖z ^ 4‖ := by
        rcases (mem_segment_zero_iff (z ^ 4) (Complex.exp w)).mp h4 with ⟨t, ht01, htX⟩
        calc
          ‖Complex.exp w‖ = ‖t • (z ^ 4)‖ := by rw [htX]
          _ = t * ‖z ^ 4‖ := by
            rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ht01.1]
          _ ≤ ‖z ^ 4‖ := mul_le_of_le_one_left (norm_nonneg (z ^ 4)) ht01.2
      linarith



/-- **Seam window zero at `x = π`.**  The window of the last direction
`x = π` (which necessarily crosses the seam) has zero boundary integral:
split at `π`; the lower piece `(π−δ, π)` is an above-tip window cell, the
upper piece `(π, π+δ)` shifts by `−2π` to `(−π, −π+δ)` which is star-free
(every `π`-spike is shorter than `e^u`, so the negative-axis boundary of the
shifted cell is above all tips); glue by `cellExpr_split_zero`. -/
theorem seam_window_zero_pi (S : Finset ℂ) (hS0 : ∀ z ∈ S, z ≠ 0)
    {h : ℂ → ℂ} (hh : DifferentiableOn ℂ h (Submission.XTransfer.star S)ᶜ)
    (δ u B : ℝ) (hδ : 0 < δ)
    (hsep : ∀ (j : ℕ) (hj : j + 1 < (dirList S).length),
      (dirList S).get ⟨j + 1, hj⟩ -
        (dirList S).get ⟨j, Nat.lt_trans (Nat.lt_succ_self j) hj⟩ > 2 * δ)
    (i : Fin (dirList S).length) (hlast : i.val + 1 = (dirList S).length)
    (hwrap : 2 * Real.pi + (dirList S).get ⟨0, by
        have h0 : 0 < (dirList S).length := by
          have : i.val < (dirList S).length := i.isLt
          omega
        exact h0⟩ - (dirList S).get i > 2 * δ)
    (hxeq : (dirList S).get i = Real.pi)
    (hcl : -Real.pi < (dirList S).get i - δ)
    (hshort : ∀ w ∈ spikeEndpoints S,
      Complex.arg w = (dirList S).get i → ‖w‖ < Real.exp u)
    (hub : u ≤ B)
    (hbarc1 : IntervalIntegrable (fun y : ℝ =>
        Submission.E2bCore.pull h (B + y * Complex.I)) volume ((dirList S).get i - δ) Real.pi)
    (hbarc2 : IntervalIntegrable (fun y : ℝ =>
        Submission.E2bCore.pull h (B + y * Complex.I)) volume Real.pi ((dirList S).get i + δ))
    (huarc1 : IntervalIntegrable (fun y : ℝ =>
        Submission.E2bCore.pull h (u + y * Complex.I)) volume ((dirList S).get i - δ) Real.pi)
    (huarc2 : IntervalIntegrable (fun y : ℝ =>
        Submission.E2bCore.pull h (u + y * Complex.I)) volume Real.pi ((dirList S).get i + δ)) :
    cellExpr (Submission.E2bCore.pull h) u B
      ((dirList S).get i - δ) ((dirList S).get i + δ) = 0 := by
  classical
  let x : ℝ := (dirList S).get i
  have hxeq' : x = Real.pi := by simpa [x] using hxeq
  have hlen0 : 0 < (dirList S).length := by
    have : i.val < (dirList S).length := i.isLt
    omega
  have hcl' : -Real.pi < x - δ := by simpa [x] using hcl
  have hxseam' : Real.pi < x + δ := by
    rw [hxeq']
    linarith [hδ]
  -- lower piece zero (above-the-tip window over (x−δ, π))
  have hsepiL : ∀ θ ∈ dirSet S, θ ∈ Set.Icc (x - δ) Real.pi → θ = x := by
    intro θ hθ hwin
    have hwin' : θ ∈ Set.Icc (x - δ) (x + δ) := by
      exact ⟨hwin.1, le_trans hwin.2 (le_of_lt hxseam')⟩
    exact SepLemma.dirList_window_separated (S := S) (δ := δ) hsep i hθ (by simpa [x] using hwin')
  have hpieceL : cellExpr (Submission.E2bCore.pull h) u B (x - δ) Real.pi = 0 := by
    simpa [x] using (Submission.E2bCells.window_cell_zero_gen S hS0 hh u B hub (x := x)
      (c := x - δ) (d := Real.pi) (by linarith [hδ]) hcl' (le_refl Real.pi) hsepiL
      (by simpa [x] using hshort))
  -- upper piece: shift (π, x+δ) by −2π to (−π, d), d = −π + δ
  let d : ℝ := x + δ - 2 * Real.pi
  have hdval : d = -Real.pi + δ := by
    dsimp [d]
    rw [hxeq']
    ring
  have hd : d ≤ Real.pi := by
    dsimp [d]
    rw [hxeq']
    linarith
  have hdn : -Real.pi < d := by
    dsimp [d]
    rw [hxeq']
    linarith
  -- no direction in [−π, d]: all directions ≥ x₀ > d (from hwrap)
  have hnoDir : ∀ θ ∈ dirSet S, θ ∉ Set.Icc (-Real.pi) d := by
    intro θ hθ hθd
    let x0 : ℝ := (dirList S).get ⟨0, hlen0⟩
    let xi : ℝ := (dirList S).get i
    have hmin : x0 ≤ θ := by
      simpa [x0] using dirList_head_le S hlen0 hθ
    have hx0gt : d < x0 := by
      have hwrap0 : 2 * Real.pi + x0 - xi > 2 * δ := by
        have hw : (dirList S).get ⟨0, by
            have h0 : 0 < (dirList S).length := by
              have : i.val < (dirList S).length := i.isLt
              omega
            exact h0⟩ = (dirList S).get ⟨0, hlen0⟩ := by
          exact congrArg (fun e : Fin (dirList S).length => (dirList S).get e)
            (Fin.ext rfl)
        dsimp [x0, xi]
        simpa [hw] using hwrap
      have hxi_eq : xi = Real.pi := by
        dsimp [xi]
        simpa [x] using hxeq'
      have hwrap0' : 2 * Real.pi + x0 - Real.pi > 2 * δ := by
        simpa [hxi_eq] using hwrap0
      dsimp [d]
      rw [hxeq']
      linarith [hwrap0', hδ]
    have hdθ : d < θ := lt_of_lt_of_le hx0gt hmin
    exact (not_lt_of_ge hθd.2) hdθ
  have hno : ∀ z ∈ S,
      Complex.arg (z ^ 2) ∉ Set.Icc (-Real.pi) d ∧
      Complex.arg (z ^ 4) ∉ Set.Icc (-Real.pi) d :=
    endpoints_no_arg_of_dirSet_free (S := S) (c := -Real.pi) (d := d) hnoDir
  -- every π-spike is short (hshort at argument x = π)
  have hshortπ : ∀ w ∈ spikeEndpoints S, Complex.arg w = Real.pi → ‖w‖ < Real.exp u := by
    intro w hw hargπ
    exact hshort w hw (by
      rw [← hxeq] at hargπ
      exact hargπ)
  -- star-avoidance of the shifted upper cell
  have hR : ∀ w ∈ ([[u, B]] ×ℂ [[-Real.pi, d]]),
      Complex.exp w ∉ star S := by
    intro w hw
    exact expRect_avoids_star_pi_boundary hS0 hub hdn hd hno hshortπ w hw
  have hpieceR' : cellExpr (Submission.E2bCore.pull h) u B (-Real.pi) d = 0 := by
    exact Fold.pullback_cell_zero h u B (-Real.pi) d
      (sector_cauchy_of_star_compl hh u B (-Real.pi) d (by
        intro w hw
        exact hR w hw))
  have hpieceR : cellExpr (Submission.E2bCore.pull h) u B Real.pi (x + δ) = 0 := by
    have hs := cellExpr_sub_two_pi h u B Real.pi (x + δ)
    have hc1 : Real.pi - 2 * Real.pi = -Real.pi := by ring
    have hc2 : (x + δ) - 2 * Real.pi = d := rfl
    rw [hc1] at hs
    rw [hc2] at hs
    have hconv : cellExpr (Submission.E2bCore.pull h) u B Real.pi (x + δ) =
        cellExpr (Submission.E2bCore.pull h) u B (-Real.pi) d := hs.symm
    rw [hconv]
    exact hpieceR'
  -- glue
  exact cellExpr_split_zero h u B (x - δ) Real.pi (x + δ)
    (by simpa [x] using hpieceL) (by simpa [x] using hpieceR)
    hbarc1 hbarc2 huarc1 huarc2
end Submission.SeamCells
