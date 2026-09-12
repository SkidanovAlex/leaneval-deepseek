import Mathlib
import Submission.SpineGaps
import Submission.SeamCells
import Submission.E2bCells
import Submission.E2bTelescope
import Submission.SepLemma
import Submission.SeamIntegrability
import Submission.DirCycle
import Submission.DirSet

/-!
# E2b instantiation: cell zeros for the star over `S` (from dirList data)

`Submission.E2bAssembly.circle_eq_cap_sum_x` (the deformation identity in
direction form) consumes per-window `hwin` and per-gap `hgap` cell zeros
plus six integrability families.  This module instantiates those zeros for
the actual hedgehog `star S` whose directions are `(dirList S).get j`:

* `hgap_interior_dirList` (interior gaps `j < s−1`): the gap cell
  `(x_j + δ, x_{j+1} − δ)` between consecutive directions has zero boundary
  integral -- a direct instantiation of
  `Submission.SpineGaps.gap_cell_between_dirList`;
* `hgap_wrap_dirList` (`j = s−1`, the wrap gap): the cell over
  `(x_last + δ, x_0 + 2π − δ)` closing the spine has zero boundary integral
  -- split at `π` (upper piece shifted by `−2π`, star-free since
  `x_last < π` in the split branch) and glued by `cellExpr_split_zero`, or
  shifted whole by `−2π` when it lies above `π`;
* window cells via `Submission.E2bCells` (non-seam) and
  `Submission.SeamCells` (seam) (later).
-/

noncomputable section
open scoped Complex Real Interval BigOperators
open Complex
open MeasureTheory

namespace Submission.E2bInst

open Submission.DirCycle
open Submission.DirSet
open Submission.Fold
open Submission.SpineGaps
open Submission.SeamCells
open Submission.E2bT
open Submission.SepLemma
open Submission.SeamIntegrability

/-- **Interior gap `hgap` (`j < s−1`).**  For the gap between consecutive
directions `x_j < x_{j+1}` (whose width exceeds `2δ`), the pulled-back cell
over `[A, B] × (x_j + δ, x_{j+1} − δ)` has zero boundary integral for every
`h` holomorphic off the hedgehog.  (This is the `hgap` hypothesis of
`Submission.E2bAssembly.circle_eq_cap_sum_x` for `j < s−1`.) -/
theorem hgap_interior_dirList (S : Finset ℂ) (hS0 : ∀ z ∈ S, z ≠ 0)
    {h : ℂ → ℂ} (hh : DifferentiableOn ℂ h (Submission.XTransfer.star S)ᶜ)
    (A B : ℝ) {δ : ℝ} (hδ : 0 < δ)
    {j : ℕ} (hj : j < (dirList S).length) (hj1 : j + 1 < (dirList S).length)
    (hsep : (dirList S).get ⟨j + 1, hj1⟩ - (dirList S).get ⟨j, hj⟩ > 2 * δ) :
    cellExpr (Submission.E2bCore.pull h) A B
      ((dirList S).get ⟨j, hj⟩ + δ) ((dirList S).get ⟨j + 1, hj1⟩ - δ) = 0 := by
  have hxc : (dirList S).get ⟨j, hj⟩ < (dirList S).get ⟨j, hj⟩ + δ := by linarith [hδ]
  have hcd : (dirList S).get ⟨j, hj⟩ + δ < (dirList S).get ⟨j + 1, hj1⟩ - δ := by linarith [hsep]
  have hdy : (dirList S).get ⟨j + 1, hj1⟩ - δ < (dirList S).get ⟨j + 1, hj1⟩ := by linarith [hδ]
  change cellExpr (fun w : ℂ => h (Complex.exp w) * Complex.exp w) A B
      ((dirList S).get ⟨j, hj⟩ + δ) ((dirList S).get ⟨j + 1, hj1⟩ - δ) = 0
  exact SpineGaps.gap_cell_between_dirList S hS0 hh A B ⟨j, hj⟩ hj1 hxc hcd hdy


theorem hgap_wrap_dirList (S : Finset ℂ) (hS0 : ∀ z ∈ S, z ≠ 0)
    {h : ℂ → ℂ} (hh : DifferentiableOn ℂ h (Submission.XTransfer.star S)ᶜ)
    (A B : ℝ) {δ : ℝ} (hδ : 0 < δ)
    (i : Fin (dirList S).length) (hlast : i.val + 1 = (dirList S).length)
    (hδx0 : δ < (dirList S).get ⟨0, by
        have h0 : 0 < (dirList S).length := by
          have : i.val < (dirList S).length := i.isLt
          omega
        exact h0⟩ + Real.pi)
    (hwrap0 : 2 * Real.pi + (dirList S).get ⟨0, by
        have h0 : 0 < (dirList S).length := by
          have : i.val < (dirList S).length := i.isLt
          omega
        exact h0⟩ - (dirList S).get i > 2 * δ)
    (hBarc1 : IntervalIntegrable (fun y : ℝ =>
        Submission.E2bCore.pull h (B + y * Complex.I)) volume
          ((dirList S).get i + δ) Real.pi)
    (hBarc2 : IntervalIntegrable (fun y : ℝ =>
        Submission.E2bCore.pull h (B + y * Complex.I)) volume
          Real.pi ((dirList S).get ⟨0, by
            have h0 : 0 < (dirList S).length := by
              have : i.val < (dirList S).length := i.isLt
              omega
            exact h0⟩ + 2 * Real.pi - δ))
    (hAarc1 : IntervalIntegrable (fun y : ℝ =>
        Submission.E2bCore.pull h (A + y * Complex.I)) volume
          ((dirList S).get i + δ) Real.pi)
    (hAarc2 : IntervalIntegrable (fun y : ℝ =>
        Submission.E2bCore.pull h (A + y * Complex.I)) volume
          Real.pi ((dirList S).get ⟨0, by
            have h0 : 0 < (dirList S).length := by
              have : i.val < (dirList S).length := i.isLt
              omega
            exact h0⟩ + 2 * Real.pi - δ)) :
    cellExpr (Submission.E2bCore.pull h) A B
      ((dirList S).get i + δ)
      ((dirList S).get ⟨0, by
        have h0 : 0 < (dirList S).length := by
          have : i.val < (dirList S).length := i.isLt
          omega
        exact h0⟩ + 2 * Real.pi - δ) = 0 := by
  classical
  let hlen0 : 0 < (dirList S).length := by
    have : i.val < (dirList S).length := i.isLt
    omega
  let x0 : ℝ := (dirList S).get ⟨0, hlen0⟩
  let xl : ℝ := (dirList S).get i
  let lo : ℝ := xl + δ
  let hi : ℝ := x0 + 2 * Real.pi - δ
  have hx0le : x0 ≤ Real.pi := by
    dsimp [x0]
    exact (dirList_get_mem_Ioc S ⟨0, hlen0⟩).2
  have hxl_lt_pi_aux : xl ≤ Real.pi := by
    dsimp [xl]
    exact (dirList_get_mem_Ioc S i).2
  have hxl_gt : -Real.pi < xl := by
    dsimp [xl]
    exact (dirList_get_mem_Ioc S i).1
  have hlo_gt : -Real.pi < lo := by
    dsimp [lo]
    linarith [hxl_gt, hδ]
  have hδx0' : δ < x0 + Real.pi := by
    dsimp [x0]
    have hw : (dirList S).get ⟨0, by
        have h0 : 0 < (dirList S).length := by
          have : i.val < (dirList S).length := i.isLt
          omega
        exact h0⟩ = (dirList S).get ⟨0, hlen0⟩ := by
      exact congrArg (fun e : Fin (dirList S).length => (dirList S).get e) (Fin.ext rfl)
    simpa [hw] using hδx0
  have hwrap' : 2 * Real.pi + x0 - xl > 2 * δ := by
    have hw : (dirList S).get ⟨0, by
        have h0 : 0 < (dirList S).length := by
          have : i.val < (dirList S).length := i.isLt
          omega
        exact h0⟩ = (dirList S).get ⟨0, hlen0⟩ := by
      exact congrArg (fun e : Fin (dirList S).length => (dirList S).get e) (Fin.ext rfl)
    dsimp [x0, xl]
    simpa [hw] using hwrap0
  have hhi_gt_lo : lo < hi := by
    dsimp [lo, hi]
    linarith [hwrap']
  have hdir_ge_x0 : ∀ θ ∈ dirSet S, x0 ≤ θ := by
    intro θ hθ
    dsimp [x0]
    exact dirList_head_le S hlen0 hθ
  have hdir_le_xl : ∀ θ ∈ dirSet S, θ ≤ xl := by
    intro θ hθ
    dsimp [xl]
    exact dirList_last_ge S i hlast hθ
  -- helper: no endpoint argument in a range strictly below the first direction
  have mk_no_below : ∀ {c d : ℝ}, (∀ θ ∈ dirSet S, θ < c) →
      ∀ z ∈ S, Complex.arg (z ^ 2) ∉ Set.Icc c d ∧ Complex.arg (z ^ 4) ∉ Set.Icc c d := by
    intro c d hg z hz
    have hnoDir : ∀ θ ∈ dirSet S, θ ∉ Set.Icc c d := by
      intro θ hθ hθd
      exact (not_lt_of_ge hθd.1) (hg θ hθ)
    exact endpoints_no_arg_of_dirSet_free (S := S) (c := c) (d := d) hnoDir z hz
  -- helper: no endpoint argument in a range strictly above the last direction
  have mk_no_above : ∀ {c d : ℝ}, (∀ θ ∈ dirSet S, d < θ) →
      ∀ z ∈ S, Complex.arg (z ^ 2) ∉ Set.Icc c d ∧ Complex.arg (z ^ 4) ∉ Set.Icc c d := by
    intro c d hg z hz
    have hnoDir : ∀ θ ∈ dirSet S, θ ∉ Set.Icc c d := by
      intro θ hθ hθd
      exact (not_lt_of_ge hθd.2) (hg θ hθ)
    exact endpoints_no_arg_of_dirSet_free (S := S) (c := c) (d := d) hnoDir z hz
  -- no endpoint has argument π when xl < π
  have mk_nopi : xl < Real.pi →
      ∀ z ∈ S, Complex.arg (z ^ 2) ≠ Real.pi ∧ Complex.arg (z ^ 4) ≠ Real.pi := by
    intro hxl_pi z hz
    constructor
    · intro h
      have hargD : Complex.arg (z ^ 2) ∈ dirSet S := arg_sq_mem_dirSet hz
      have hle : Complex.arg (z ^ 2) ≤ xl := hdir_le_xl _ hargD
      linarith
    · intro h
      have hargD : Complex.arg (z ^ 4) ∈ dirSet S := arg_pow4_mem_dirSet hz
      have hle : Complex.arg (z ^ 4) ≤ xl := hdir_le_xl _ hargD
      linarith
  by_cases hle : lo ≤ Real.pi
  · -- lo ≤ π: split at π: left piece (lo, π) (empty when lo = π) is
    -- direction-free (all directions ≤ xl < lo); right piece (π, hi)
    -- shifts by −2π to (−π, x0−δ), star-free (no π-direction since
    -- xl < π, no direction below x0).
    have hz_l : cellExpr (Submission.E2bCore.pull h) A B lo Real.pi = 0 := by
      have hxl_lo : xl < lo := by dsimp [lo]; linarith [hδ]
      by_cases hlo_lt : lo < Real.pi
      · have hno := mk_no_below (c := lo) (d := Real.pi) (by
          intro θ hθ
          have hθxl : θ ≤ xl := hdir_le_xl θ hθ
          linarith [hxl_lo])
        change cellExpr (fun w : ℂ => h (Complex.exp w) * Complex.exp w) A B lo Real.pi = 0
        exact Fold.gap_cell_zero hS0 hh A B hlo_lt hlo_gt (le_refl Real.pi) hno
      · have hlo_eq : lo = Real.pi := le_antisymm hle (le_of_not_gt hlo_lt)
        rw [hlo_eq]
        exact Fold.cellExpr_self (Submission.E2bCore.pull h) A B Real.pi
    have hz_r : cellExpr (Submission.E2bCore.pull h) A B Real.pi hi = 0 := by
      have hxl_pi : xl < Real.pi := by
        dsimp [lo] at hle
        linarith
      have hnd : -Real.pi < x0 - δ := by linarith [hδx0']
      have hno := mk_no_above (c := -Real.pi) (d := x0 - δ) (by
        intro θ hθ
        have hge : x0 ≤ θ := hdir_ge_x0 θ hθ
        linarith [hδ])
      have hnopi := mk_nopi hxl_pi
      have hzero : cellExpr (Submission.E2bCore.pull h) A B (-Real.pi) (x0 - δ) = 0 :=
        cellExpr_zero_npi hS0 hh A B hnd (by linarith [hδ, hx0le]) hno hnopi
      have hc1 : Real.pi - 2 * Real.pi = -Real.pi := by ring
      have hc2 : hi - 2 * Real.pi = x0 - δ := by dsimp [hi]; ring
      have hs := Submission.E2bT.cellExpr_sub_two_pi h A B Real.pi hi
      rw [hc1] at hs
      rw [hc2] at hs
      exact hs.symm.trans hzero
    -- glue (works also for the degenerate left piece, whose arc
    -- integrability over (lo,π) = (π,π) is the given hypothesis)
    exact Submission.E2bT.cellExpr_split_zero h A B lo Real.pi hi
      (by simpa [lo] using hz_l) (by simpa [lo, hi] using hz_r)
      hBarc1 hBarc2 hAarc1 hAarc2
  · -- π < lo: the whole gap cell lies above π; shift by −2π to
    -- (lo−2π, x0−δ) ⊆ (−π, π], direction-free (all directions ≥ x0 > x0−δ).
    have hlo_gt_pi : Real.pi < lo := lt_of_not_ge hle
    have hc'gt : -Real.pi < lo - 2 * Real.pi := by
      dsimp [lo]
      linarith [hlo_gt_pi]
    have hd'le : x0 - δ ≤ Real.pi := by linarith [hδ, hx0le]
    have hc'd' : lo - 2 * Real.pi < x0 - δ := by
      have hhi' : lo < x0 + 2 * Real.pi - δ := by simpa [hi] using hhi_gt_lo
      linarith
    have hno := mk_no_above (c := lo - 2 * Real.pi) (d := x0 - δ) (by
      intro θ hθ
      have hge : x0 ≤ θ := hdir_ge_x0 θ hθ
      linarith [hδ])
    have hzero' : cellExpr (Submission.E2bCore.pull h) A B (lo - 2 * Real.pi) (x0 - δ) = 0 := by
      change cellExpr (fun w : ℂ => h (Complex.exp w) * Complex.exp w) A B (lo - 2 * Real.pi) (x0 - δ) = 0
      exact Fold.gap_cell_zero hS0 hh A B hc'd' hc'gt hd'le hno
    have hconv : cellExpr (Submission.E2bCore.pull h) A B lo hi =
        cellExpr (Submission.E2bCore.pull h) A B (lo - 2 * Real.pi) (x0 - δ) := by
      have hs := Submission.E2bT.cellExpr_add_two_pi h A B (lo - 2 * Real.pi) (x0 - δ)
      have hc1 : (lo - 2 * Real.pi) + 2 * Real.pi = lo := by ring
      have hc2 : (x0 - δ) + 2 * Real.pi = hi := by dsimp [hi]; ring
      rw [hc1] at hs
      rw [hc2] at hs
      exact hs
    rw [hconv]
    exact hzero'


/-! ## Windows (`hwin`) -- non-seam case

For a direction `x := (dirList S).get j` whose closed `δ`-window stays
inside `(−π, π]`, with short spikes along `x` (`hshort`) and the
consecutive-gap separation (`hsep`), the above-the-tip window cell
`[u, B] × (x−δ, x+δ)` has zero boundary integral: this is the `hwin`
hypothesis of `Submission.E2bAssembly.circle_eq_cap_sum_x` for a non-seam
window (via `Submission.E2bCells.nonseam_window_zero_of_sep`). -/

/-- **Non-seam window `hwin` (direction form).**  ℕ-indexed wrapper of
`Submission.E2bCells.nonseam_window_zero_of_sep`. -/
theorem hwin_nonseam_dirList (S : Finset ℂ) (hS0 : ∀ z ∈ S, z ≠ 0)
    {h : ℂ → ℂ} (hh : DifferentiableOn ℂ h (Submission.XTransfer.star S)ᶜ)
    (δ u B : ℝ) (hδ : 0 < δ)
    (hsep : ∀ (j : ℕ) (hj : j + 1 < (dirList S).length),
      (dirList S).get ⟨j + 1, hj⟩ -
        (dirList S).get ⟨j, Nat.lt_trans (Nat.lt_succ_self j) hj⟩ > 2 * δ)
    {j : ℕ} (hj : j < (dirList S).length)
    (hshort : ∀ w ∈ spikeEndpoints S,
      Complex.arg w = (dirList S).get ⟨j, hj⟩ → ‖w‖ < Real.exp u)
    (hcl : -Real.pi < (dirList S).get ⟨j, hj⟩ - δ)
    (hdu : (dirList S).get ⟨j, hj⟩ + δ ≤ Real.pi)
    (hub : u ≤ B) :
    cellExpr (Submission.E2bCore.pull h) u B
      ((dirList S).get ⟨j, hj⟩ - δ) ((dirList S).get ⟨j, hj⟩ + δ) = 0 := by
  exact Submission.E2bCells.nonseam_window_zero_of_sep S hS0 hh δ u B hδ hsep ⟨j, hj⟩
    hshort hcl hdu hub


/-! ## Windows (`hwin`) -- seam cases

For the LAST direction `x := (dirList S).get i` whose window crosses the
arg branch (`π < x + δ`), the seam window zero
`Submission.SeamCells.seam_window_zero_lt_pi` applies, fed with the four
arc-integrability facts `Submission.SeamIntegrability.seam_arcB_1/_2` and
`seam_arcU_1/_2` and the window-separation `hsepi` (from the
consecutive-gap bounds by `Submission.SepLemma.dirList_window_separated`).
This is the `hwin` hypothesis of `circle_eq_cap_sum_x` for the seam window
in the `x < π` case. -/

/-- **Seam window `hwin`, case `x < π`.** -/
theorem hwin_seam_lt_pi_dirList (S : Finset ℂ) (hS0 : ∀ z ∈ S, z ≠ 0)
    {h : ℂ → ℂ} (hh : DifferentiableOn ℂ h (Submission.XTransfer.star S)ᶜ)
    (δ u B : ℝ) (hδ : 0 < δ) (hδle : δ ≤ Real.pi)
    (hsep : ∀ (j : ℕ) (hj : j + 1 < (dirList S).length),
      (dirList S).get ⟨j + 1, hj⟩ -
        (dirList S).get ⟨j, Nat.lt_trans (Nat.lt_succ_self j) hj⟩ > 2 * δ)
    (i : Fin (dirList S).length) (hlast : i.val + 1 = (dirList S).length)
    (hwrap0 : 2 * Real.pi + (dirList S).get ⟨0, by
        have h0 : 0 < (dirList S).length := by
          have : i.val < (dirList S).length := i.isLt
          omega
        exact h0⟩ - (dirList S).get i > 2 * δ)
    (hδx0 : δ < (dirList S).get ⟨0, by
        have h0 : 0 < (dirList S).length := by
          have : i.val < (dirList S).length := i.isLt
          omega
        exact h0⟩ + Real.pi)
    (hxlt : (dirList S).get i < Real.pi)
    (hxseam : Real.pi < (dirList S).get i + δ)
    (hcl : -Real.pi < (dirList S).get i - δ)
    (hshort : ∀ w ∈ spikeEndpoints S,
      Complex.arg w = (dirList S).get i → ‖w‖ < Real.exp u)
    (hshortπ : ∀ w ∈ spikeEndpoints S,
      Complex.arg w = Real.pi → ‖w‖ < Real.exp u)
    (hub : u ≤ B)
    (hBigB : ∀ w ∈ spikeEndpoints S, ‖w‖ < Real.exp B) :
    cellExpr (Submission.E2bCore.pull h) u B
      ((dirList S).get i - δ) ((dirList S).get i + δ) = 0 := by
  classical
  have hsepi : ∀ θ ∈ dirSet S,
      θ ∈ Set.Icc ((dirList S).get i - δ) ((dirList S).get i + δ) →
        θ = (dirList S).get i := fun θ hθ hwin =>
    dirList_window_separated (S := S) (δ := δ) hsep i hθ hwin
  exact seam_window_zero_lt_pi S hS0 hh δ u B hδ hsep i hlast hwrap0 hxlt hxseam hcl
    hshort hub
    (seam_arcB_1 S hS0 hh B hδ i hBigB)
    (seam_arcB_2 S hS0 hh B hδ i hBigB)
    (seam_arcU_1 S hS0 hh δ u hδ i hxseam hsepi hshort hshortπ hcl)
    (seam_arcU_2 S hS0 hh δ u hδ hδle i hlast hwrap0 hshortπ)


/-- **Seam window `hwin`, case `x = π`** (the last direction is exactly at
the branch; its window necessarily crosses). -/
theorem hwin_seam_pi_dirList (S : Finset ℂ) (hS0 : ∀ z ∈ S, z ≠ 0)
    {h : ℂ → ℂ} (hh : DifferentiableOn ℂ h (Submission.XTransfer.star S)ᶜ)
    (δ u B : ℝ) (hδ : 0 < δ) (hδle : δ ≤ Real.pi)
    (hsep : ∀ (j : ℕ) (hj : j + 1 < (dirList S).length),
      (dirList S).get ⟨j + 1, hj⟩ -
        (dirList S).get ⟨j, Nat.lt_trans (Nat.lt_succ_self j) hj⟩ > 2 * δ)
    (i : Fin (dirList S).length) (hlast : i.val + 1 = (dirList S).length)
    (hwrap0 : 2 * Real.pi + (dirList S).get ⟨0, by
        have h0 : 0 < (dirList S).length := by
          have : i.val < (dirList S).length := i.isLt
          omega
        exact h0⟩ - (dirList S).get i > 2 * δ)
    (hxeq : (dirList S).get i = Real.pi)
    (hcl : -Real.pi < (dirList S).get i - δ)
    (hshort : ∀ w ∈ spikeEndpoints S,
      Complex.arg w = (dirList S).get i → ‖w‖ < Real.exp u)
    (hshortπ : ∀ w ∈ spikeEndpoints S,
      Complex.arg w = Real.pi → ‖w‖ < Real.exp u)
    (hub : u ≤ B)
    (hBigB : ∀ w ∈ spikeEndpoints S, ‖w‖ < Real.exp B) :
    cellExpr (Submission.E2bCore.pull h) u B
      ((dirList S).get i - δ) ((dirList S).get i + δ) = 0 := by
  classical
  have hxseam : Real.pi < (dirList S).get i + δ := by
    rw [hxeq]
    linarith [hδ]
  have hsepi : ∀ θ ∈ dirSet S,
      θ ∈ Set.Icc ((dirList S).get i - δ) ((dirList S).get i + δ) →
        θ = (dirList S).get i := fun θ hθ hwin =>
    dirList_window_separated (S := S) (δ := δ) hsep i hθ hwin
  exact seam_window_zero_pi S hS0 hh δ u B hδ hsep i hlast hwrap0 hxeq hcl
    hshort hub
    (seam_arcB_1 S hS0 hh B hδ i hBigB)
    (seam_arcB_2 S hS0 hh B hδ i hBigB)
    (seam_arcU_1 S hS0 hh δ u hδ i hxseam hsepi hshort hshortπ hcl)
    (seam_arcU_2 S hS0 hh δ u hδ hδle i hlast hwrap0 hshortπ)

end Submission.E2bInst

end
