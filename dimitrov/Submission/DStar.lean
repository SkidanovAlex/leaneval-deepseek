import Mathlib
import Submission.E2bAssembly
import Submission.E2bInst
import Submission.E2bCells
import Submission.SeamCells
import Submission.SeamIntegrability
import Submission.SpineGaps
import Submission.SepLemma
import Submission.RadialFree
import Submission.DirCycle
import Submission.DirSet
import Submission.Fold
import Submission.E2bTelescope

/-!
# DStar: proof of the assembled E2b deformation over the star

This module proves `deformation_star` (below), the E2b deformation identity
for `h` holomorphic off the hedgehog `star S`:

    ∮_{C(0, e^B)} h  =  Σ_j I•arc(u_j, x_j−δ, x_j+δ) + Σ_j I•arc(A, x_j+δ, x_{j+1}−δ)
                        + Σ_j rad(A,u_j,x_j−δ) − Σ_j rad(A,u_j,x_j+δ)

(`x j := dirX S hlen0 j` the cyclic direction spine, `s := (dirList S).length`,
`x s = x 0 + 2π`).  The proof instantiates
`Submission.E2bAssembly.circle_eq_cap_sum_x` (VERIFIED: `circle_eq_cap_sum_x`
in `Submission/E2bAssembly.lean`, whose conclusion is exactly this RHS with
`x` and `s`), discharging its hypotheses:

* `hcl` (cyclic closure): `dirX_length S hlen0` + `dirX_of_lt` at `j=0`;
* `hBwin`/`hBgap` (arc integrability at radius `e^B` over the window/gap):
  the whole circle is star-free by `hBigB`
  (`Submission.RadialFree.arcB_integrable_any S hh B hBigB`, works for any
  real range — give it `(c := …)(d := …)` explicitly);
* radial integrability at the window edges `x_j − δ` and `x_j + δ`
  (`hRwinL/hRwinLB` at angle `x_j−δ`, `hRwinR/hRwinRB` at angle `x_j+δ`):
  via `Submission.RadialFree.radial_integrable_of_angle_free S hh (A) (B) θ
  hno`, where the `hno` (no direction equals the wrapped angle) is supplied
  by the helpers `no_dir_left_edge` / `no_dir_right_edge` /
  `no_dir_right_edge_seam` below (VERIFIED);
* `hwin` (per-window cell zero): non-seam windows via
  `Submission.E2bInst.hwin_nonseam_dirList` (works whenever the window
  `(x_j−δ, x_j+δ)` stays inside `(−π,π]`, i.e. `x_j + δ ≤ π`); the seam
  window of the LAST direction (when `π < x_j + δ`) via
  `Submission.E2bInst.hwin_seam_lt_pi_dirList` (if `x_j < π`) or
  `Submission.E2bInst.hwin_seam_pi_dirList` (if `x_j = π`);
* `hgap` (per-gap cell zero): interior gaps via
  `Submission.E2bInst.hgap_interior_dirList`; the wrap gap (last index) via
  `Submission.E2bInst.hgap_wrap_dirList` when `x + δ ≤ π` (feeding it the
  four arc-integrability facts `hBarc1/hBarc2` := `arcB_integrable_any`,
  `hAarc1/hAarc2` := arcs at radius `A` over the direction-free pieces —
  prove them with `arc_integrable_angle_free` below, whose `hno` follows
  because all directions are `≤ x < π` resp. `≥ x0 > (wrapped range)`),
  or via `gap_wrap_above_pi` below when `π < x + δ` (the `x = π` case,
  where the artificial π-split pieces of `hgap_wrap_dirList` are NOT
  star-free).

## INDEX-PROOF CONVERSIONS (important)

Several `Submission.E2bInst`/`Submission.SeamCells` hypotheses (`hδx0`,
`hwrap0`) are stated with an index proof of `0 < (dirList S).length` that is
*locally generated* from the last-index `i : Fin (dirList S).length`:

    ⟨0, by have h0 : 0 < (dirList S).length := by
             have : i.val < (dirList S).length := i.isLt; omega; exact h0⟩

`deformation_star`'s versions use `hlen0`.  The entries are the same value
(`Fin` equality by `Fin.ext rfl` — both have `.val = 0`), so convert with
`congrArg`:

    
lemma get0_eq (S) (p q : 0 < (dirList S).length) :
        (dirList S).get ⟨0, p⟩ = (dirList S).get ⟨0, q⟩

and `simpa [get0_eq S hlen0 q] using hδx0`.  Likewise, the last-dirList
entry appears in `deformation_star`'s `hwrap0` as
`(dirList S).get ⟨(dirList S).length − 1, by omega⟩` and in the E2bInst
seam/wrap statements as `(dirList S).get i` (`i.val = length − 1`): convert
with a `congrArg`-based equality.  Two `Fin`s with the same `.val` are equal
by `Fin.ext`; `(dirList S).get` applied to equal `Fin`s is equal by
`congrArg (fun e : Fin (dirList S).length => (dirList S).get e) (Fin.ext …)`.

## DISPATCH GUIDE for `hwin` (per `j < s`)

1. If `j + 1 < s` (non-last): `x_j + δ < x_{j+1} − δ < x_{j+1} ≤ π`
   (`hsep j (j+1-proof)` + `dirList_get_mem_Ioc`), so
   `hwin_nonseam_dirList` applies: `hcl` (−π < x_j − δ) from `hδx0`
   (δ < x_0 + π) + `x_j ≥ x_0` (all entries ≥ head;
   `Submission.SeamCells.dirList_head_le S hlen0`),
   `hdu` (x_j + δ ≤ π), `hub` := `hub j hj'`,
   `hshort` instantiated from `hshort j hj'` via `dirX_of_lt S hlen0 hj'`
   (dirX S hlen0 j = (dirList S).get ⟨j,hj'⟩);
2. If `j + 1 = s` (last): by_cases `x + δ ≤ π` (nonseam as above with
   `i := ⟨j,hj'⟩`) or `π < x + δ` (seam): by_cases `x = π`:
   `hwin_seam_pi_dirList`, else `hwin_seam_lt_pi_dirList` (with
   `hxlt : x < π` from `x ≤ π` and `x ≠ π`).

The E2bInst seam lemmas internally provide the seam arc integrabilities from
`hBigB`/`hshort`/`hshortπ` — only their own listed hypotheses are needed.

## DISPATCH GUIDE for `hgap` (per `j < s`)

1. If `j + 1 < s`: `hgap_interior_dirList S hS0 hh A B hδ hj hj1
   (hsep-clean j hj1)` (the `hsep` hypothesis there has a plain `⟨j,hj⟩`
   index; convert from `hsep`'s `⟨j, Nat.lt_trans (Nat.lt_succ_self j) hj1⟩`
   by `congrArg`+`Fin.ext`);
2. If `j + 1 = s` (wrap gap over `(x+δ, x0+2π−δ)`):
   * if `x + δ ≤ π`: `E2bInst.hgap_wrap_dirList` (needs `hBarc1/2`
     := `arcB_integrable_any`, `hAarc1/2` := direction-free arcs via
     `arc_integrable_angle_free`; also `i`, `hlast`, converted `hδx0`,
     `hwrap0`);
   * if `π < x + δ`: `gap_wrap_above_pi` below (no arc hypotheses needed —
     the whole cell shifts by −2π into the direction-free range
     `(x+δ−2π, x0−δ)`).

FINAL STEP: `exact circle_eq_cap_sum_x h s hs A B δ x u hcl hBwin hBgap
hRwinL hRwinLB hRwinR hRwinRB hwin hgap` (then the goal is closed by
definitional equality / `simpa [x, s]`).
-/

noncomputable section
open scoped Complex Real Interval BigOperators
open Complex
open MeasureTheory

namespace Submission.DStar

open Submission.DirCycle
open Submission.DirSet
open Submission.E2bAssembly
open Submission.E2bT
open Submission.RadialFree
open Submission.E2bCells
open Submission.Fold
open Submission.SpineGaps
open Submission.SepLemma
open Submission.E2bInst
open Submission.SeamCells

/-- `(dirList S).get` at index `0` does not depend on the positivity proof
(Fins at index 0 with any proofs are equal). -/
lemma get0_eq (S : Finset ℂ) (p q : 0 < (dirList S).length) :
    (dirList S).get ⟨0, p⟩ = (dirList S).get ⟨0, q⟩ := by
  apply congrArg (fun e : Fin (dirList S).length => (dirList S).get e)
  apply Fin.ext
  rfl

/-- An arc at radius `e^r` over an angular range `[c,d]` whose every point
(angle) is not a direction mod `2π` is star-free, hence integrable. -/
lemma arc_integrable_angle_free (S : Finset ℂ)
    {h : ℂ → ℂ} (hh : DifferentiableOn ℂ h (Submission.XTransfer.star S)ᶜ)
    (r : ℝ) {c d : ℝ}
    (hno : ∀ y : ℝ, y ∈ Set.uIcc c d →
      ∀ d0 ∈ dirSet S, d0 ≠ toIocMod Real.two_pi_pos (-Real.pi) y) :
    IntervalIntegrable (fun y : ℝ => Submission.E2bCore.pull h (r + y * Complex.I)) volume c d := by
  exact E2bCells.intervalIntegrable_pull_arc S hh r (by
    intro y hy
    exact exp_ray_not_mem_star_of_not_dir (S := S) (θ := y) (hno y hy) r)

/-- No direction equals the wrapped angle of the left window edge `x_j − δ`
(all entries above `x_0` by `hδx0`, window separation). -/
lemma no_dir_left_edge (S : Finset ℂ) (hlen0 : 0 < (dirList S).length)
    {δ : ℝ} (hδ : 0 < δ)
    (hsep : ∀ (j : ℕ) (hj : j + 1 < (dirList S).length),
      (dirList S).get ⟨j + 1, hj⟩ -
        (dirList S).get ⟨j, Nat.lt_trans (Nat.lt_succ_self j) hj⟩ > 2 * δ)
    (hδx0 : δ < (dirList S).get ⟨0, hlen0⟩ + Real.pi)
    {j : ℕ} (hj : j < (dirList S).length) :
    ∀ d0 ∈ dirSet S, d0 ≠ toIocMod Real.two_pi_pos (-Real.pi) (dirX S hlen0 j - δ) := by
  classical
  intro d0 hd0 hEq
  have hgt : -Real.pi < (dirList S).get ⟨j, hj⟩ - δ := by
    have hθ : (dirList S).get ⟨j, hj⟩ ∈ dirSet S :=
      (dirList_mem_iff S ((dirList S).get ⟨j, hj⟩)).mp (List.get_mem (dirList S) ⟨j, hj⟩)
    have hge : (dirList S).get ⟨0, hlen0⟩ ≤ (dirList S).get ⟨j, hj⟩ :=
      Submission.SeamCells.dirList_head_le S hlen0 hθ
    have h0 : -Real.pi < (dirList S).get ⟨0, hlen0⟩ - δ := by linarith [hδx0]
    linarith
  have hle : (dirList S).get ⟨j, hj⟩ - δ ≤ Real.pi := by
    have hx := (dirList_get_mem_Ioc S ⟨j, hj⟩).2
    linarith [hδ]
  have hT : toIocMod Real.two_pi_pos (-Real.pi) (dirX S hlen0 j - δ)
      = (dirList S).get ⟨j, hj⟩ - δ := by
    rw [dirX_of_lt S hlen0 hj]
    exact (toIocMod_eq_self Real.two_pi_pos (a := -Real.pi) (b := (dirList S).get ⟨j, hj⟩ - δ)).2
      (show (dirList S).get ⟨j, hj⟩ - δ ∈ Set.Ioc (-Real.pi) (-Real.pi + 2 * Real.pi)
        from ⟨hgt, by linarith⟩)
  have hEq' : d0 = (dirList S).get ⟨j, hj⟩ - δ := by
    rw [hT] at hEq
    exact hEq
  have hwin : (dirList S).get ⟨j, hj⟩ - δ ∈
      Set.Icc ((dirList S).get ⟨j, hj⟩ - δ) ((dirList S).get ⟨j, hj⟩ + δ) := by
    constructor <;> linarith [hδ]
  have hd' : (dirList S).get ⟨j, hj⟩ - δ ∈ dirSet S := by simpa [hEq'] using hd0
  have heq := dirList_window_separated (S := S) (δ := δ) hsep ⟨j, hj⟩ hd' hwin
  have : δ = 0 := by linarith
  exact False.elim (lt_irrefl δ (by linarith [hδ]))

/-- No direction equals the wrapped angle of the right window edge `x_j + δ`
in the non-seam case (`x_j + δ ≤ π`). -/
lemma no_dir_right_edge (S : Finset ℂ) (hlen0 : 0 < (dirList S).length)
    {δ : ℝ} (hδ : 0 < δ)
    (hsep : ∀ (j : ℕ) (hj : j + 1 < (dirList S).length),
      (dirList S).get ⟨j + 1, hj⟩ -
        (dirList S).get ⟨j, Nat.lt_trans (Nat.lt_succ_self j) hj⟩ > 2 * δ)
    {j : ℕ} (hj : j < (dirList S).length)
    (hdu : (dirList S).get ⟨j, hj⟩ + δ ≤ Real.pi) :
    ∀ d0 ∈ dirSet S, d0 ≠ toIocMod Real.two_pi_pos (-Real.pi) (dirX S hlen0 j + δ) := by
  classical
  intro d0 hd0 hEq
  have hgt : -Real.pi < (dirList S).get ⟨j, hj⟩ + δ := by
    have hx := (dirList_get_mem_Ioc S ⟨j, hj⟩).1
    linarith
  have hT : toIocMod Real.two_pi_pos (-Real.pi) (dirX S hlen0 j + δ)
      = (dirList S).get ⟨j, hj⟩ + δ := by
    rw [dirX_of_lt S hlen0 hj]
    exact (toIocMod_eq_self Real.two_pi_pos (a := -Real.pi) (b := (dirList S).get ⟨j, hj⟩ + δ)).2
      (show (dirList S).get ⟨j, hj⟩ + δ ∈ Set.Ioc (-Real.pi) (-Real.pi + 2 * Real.pi)
        from ⟨hgt, by linarith⟩)
  have hEq' : d0 = (dirList S).get ⟨j, hj⟩ + δ := by
    rw [hT] at hEq
    exact hEq
  have hwin : (dirList S).get ⟨j, hj⟩ + δ ∈
      Set.Icc ((dirList S).get ⟨j, hj⟩ - δ) ((dirList S).get ⟨j, hj⟩ + δ) := by
    constructor <;> linarith [hδ]
  have hd' : (dirList S).get ⟨j, hj⟩ + δ ∈ dirSet S := by simpa [hEq'] using hd0
  have heq := dirList_window_separated (S := S) (δ := δ) hsep ⟨j, hj⟩ hd' hwin
  have : δ = 0 := by linarith
  exact False.elim (lt_irrefl δ (by linarith [hδ]))

/-- No direction equals the wrapped angle of the right window edge of the
LAST direction in the seam case (`π < x + δ`): the wrapped value is below
`x_0`. -/
lemma no_dir_right_edge_seam (S : Finset ℂ) (hlen0 : 0 < (dirList S).length)
    {δ : ℝ} (hδ : 0 < δ) (hδle : δ ≤ Real.pi)
    (hwrap0 : 2 * Real.pi + (dirList S).get ⟨0, hlen0⟩ -
        (dirList S).get ⟨(dirList S).length - 1, by omega⟩ > 2 * δ)
    (hδx0 : δ < (dirList S).get ⟨0, hlen0⟩ + Real.pi)
    {j : ℕ} (hj : j < (dirList S).length) (hlast : j + 1 = (dirList S).length)
    (hseam : Real.pi < (dirList S).get ⟨j, hj⟩ + δ) :
    ∀ d0 ∈ dirSet S, d0 ≠ toIocMod Real.two_pi_pos (-Real.pi) (dirX S hlen0 j + δ) := by
  classical
  intro d0 hd0 hEq
  have hxl : (dirList S).get ⟨j, hj⟩ ≤ Real.pi := (dirList_get_mem_Ioc S ⟨j, hj⟩).2
  have hT : toIocMod Real.two_pi_pos (-Real.pi) (dirX S hlen0 j + δ)
      = (dirList S).get ⟨j, hj⟩ + δ - 2 * Real.pi := by
    rw [dirX_of_lt S hlen0 hj]
    rw [toIocMod_eq_iff]
    constructor
    · constructor
      · linarith
      · have h : -Real.pi + 2 * Real.pi = Real.pi := by ring
        rw [h]
        have hle2 : (dirList S).get ⟨j, hj⟩ + δ ≤ 3 * Real.pi := by linarith [hxl, hδle, Real.pi_pos]
        linarith
    · refine ⟨1, ?_⟩
      ring
  have hEq' : d0 = (dirList S).get ⟨j, hj⟩ + δ - 2 * Real.pi := by
    rw [hT] at hEq
    exact hEq
  have hge : (dirList S).get ⟨0, hlen0⟩ ≤ d0 := by
    exact Submission.SeamCells.dirList_head_le S hlen0 hd0
  have heq_last : (dirList S).get ⟨j, hj⟩ =
      (dirList S).get ⟨(dirList S).length - 1, by omega⟩ := by
    apply congrArg (fun e : Fin (dirList S).length => (dirList S).get e)
    apply Fin.ext
    dsimp
    omega
  have hwlt : (dirList S).get ⟨j, hj⟩ + δ - 2 * Real.pi < (dirList S).get ⟨0, hlen0⟩ := by
    have h1 : (dirList S).get ⟨j, hj⟩ + δ - 2 * Real.pi < (dirList S).get ⟨0, hlen0⟩ - δ := by
      linarith
    linarith [h1, hδ]
  linarith

/-- The wrap gap (`j = s−1`) when `π < x + δ`: the whole cell shifts by
`−2π` into the direction-free range `(x+δ−2π, x_0−δ)` and `gap_cell_zero`
applies (no seam-split arc integrability needed). -/
lemma gap_wrap_above_pi (S : Finset ℂ) (hS0 : ∀ z ∈ S, z ≠ 0)
    {h : ℂ → ℂ} (hh : DifferentiableOn ℂ h (Submission.XTransfer.star S)ᶜ)
    (A B : ℝ) {δ : ℝ} (hδ : 0 < δ)
    (i : Fin (dirList S).length) (hlast : i.val + 1 = (dirList S).length)
    (hlen0 : 0 < (dirList S).length)
    (hwrap0 : 2 * Real.pi + (dirList S).get ⟨0, hlen0⟩ - (dirList S).get i > 2 * δ)
    (hδx0 : δ < (dirList S).get ⟨0, hlen0⟩ + Real.pi)
    (hseam : Real.pi < (dirList S).get i + δ) :
    cellExpr (Submission.E2bCore.pull h) A B
      ((dirList S).get i + δ) ((dirList S).get ⟨0, hlen0⟩ + 2 * Real.pi - δ) = 0 := by
  classical
  let x0 : ℝ := (dirList S).get ⟨0, hlen0⟩
  let x : ℝ := (dirList S).get i
  let lo : ℝ := x + δ
  let hi : ℝ := x0 + 2 * Real.pi - δ
  have hx0le : x0 ≤ Real.pi := by
    dsimp [x0]
    exact (dirList_get_mem_Ioc S ⟨0, hlen0⟩).2
  have hxIoc : x ∈ Set.Ioc (-Real.pi) Real.pi := by
    dsimp [x]
    exact dirList_get_mem_Ioc S i
  have hdir_ge_x0 : ∀ θ ∈ dirSet S, x0 ≤ θ := by
    intro θ hθ
    dsimp [x0]
    exact dirList_head_le S hlen0 hθ
  have hhi_gt_lo : lo < hi := by
    dsimp [lo, hi]
    linarith [hwrap0]
  -- shifted range (lo − 2π, x0 − δ): direction-free and inside (−π, π]
  have hcl' : -Real.pi < lo - 2 * Real.pi := by
    dsimp [lo]
    linarith [hseam]
  have hdu' : x0 - δ ≤ Real.pi := by linarith [hδ, hx0le]
  have hcd' : lo - 2 * Real.pi < x0 - δ := by
    dsimp [lo]
    linarith [hwrap0]
  have hnoDir : ∀ θ ∈ dirSet S, θ ∉ Set.Icc (lo - 2 * Real.pi) (x0 - δ) := by
    intro θ hθ hwinθ
    have hge : x0 ≤ θ := hdir_ge_x0 θ hθ
    have hlo : θ ≤ x0 - δ := hwinθ.2
    linarith [hδ]
  have hno : ∀ z ∈ S,
      Complex.arg (z ^ 2) ∉ Set.Icc (lo - 2 * Real.pi) (x0 - δ) ∧
      Complex.arg (z ^ 4) ∉ Set.Icc (lo - 2 * Real.pi) (x0 - δ) :=
    endpoints_no_arg_of_dirSet_free (S := S) (c := lo - 2 * Real.pi) (d := x0 - δ) hnoDir
  have hzero' : cellExpr (Submission.E2bCore.pull h) A B (lo - 2 * Real.pi) (x0 - δ) = 0 := by
    change cellExpr (fun w : ℂ => h (Complex.exp w) * Complex.exp w) A B
      (lo - 2 * Real.pi) (x0 - δ) = 0
    exact Fold.gap_cell_zero hS0 hh A B hcd' hcl' hdu' hno
  -- shift the whole cell by +2π back
  have hs := Submission.E2bT.cellExpr_add_two_pi h A B (lo - 2 * Real.pi) (x0 - δ)
  have hc1 : (lo - 2 * Real.pi) + 2 * Real.pi = lo := by dsimp [lo]; ring
  have hc2 : (x0 - δ) + 2 * Real.pi = hi := by dsimp [hi, x0]; ring
  rw [hc1, hc2] at hs
  dsimp [lo, hi]
  exact hs.trans hzero'

/-- `(dirList S).get` at a common index `j` does not depend on the choice of
the index proof. -/
lemma dirList_get_ext (S : Finset ℂ) {j : ℕ} (p q : j < (dirList S).length) :
    (dirList S).get ⟨j, p⟩ = (dirList S).get ⟨j, q⟩ := by
  apply congrArg (fun e : Fin (dirList S).length => (dirList S).get e)
  apply Fin.ext
  rfl

/-- The last entry `(dirList S).get j` (`j` last) equals
`(dirList S).get ⟨length − 1, ·⟩` (rewrite-friendly orientation). -/
lemma dirList_get_j_last (S : Finset ℂ) {j : ℕ} (hj : j < (dirList S).length)
    (hlast : j + 1 = (dirList S).length) :
    (dirList S).get ⟨j, hj⟩ = (dirList S).get ⟨(dirList S).length - 1, by omega⟩ := by
  apply congrArg (fun e : Fin (dirList S).length => (dirList S).get e)
  apply Fin.ext
  dsimp
  omega

/-- The left edge of the `δ`-window around any direction stays above `−π`
(all directions are at least the head `x_0`, and `δ < x_0 + π`). -/
lemma window_left_gt_npi (S : Finset ℂ) (hlen0 : 0 < (dirList S).length)
    {δ : ℝ} (hδx0 : δ < (dirList S).get ⟨0, hlen0⟩ + Real.pi)
    {j : ℕ} (hj : j < (dirList S).length) :
    -Real.pi < (dirList S).get ⟨j, hj⟩ - δ := by
  have hθ : (dirList S).get ⟨j, hj⟩ ∈ dirSet S :=
    (dirList_mem_iff S ((dirList S).get ⟨j, hj⟩)).mp (List.get_mem (dirList S) ⟨j, hj⟩)
  have hge : (dirList S).get ⟨0, hlen0⟩ ≤ (dirList S).get ⟨j, hj⟩ :=
    Submission.SeamCells.dirList_head_le S hlen0 hθ
  linarith

/-- The upper edge of the `δ`-window around a direction that is followed by
another direction stays within `π` (separation `> 2δ` and `x_{j+1} ≤ π`). -/
lemma window_right_le_pi (S : Finset ℂ)
    {δ : ℝ} (hδ : 0 < δ)
    (hsep : ∀ (j : ℕ) (hj : j + 1 < (dirList S).length),
      (dirList S).get ⟨j + 1, hj⟩ -
        (dirList S).get ⟨j, Nat.lt_trans (Nat.lt_succ_self j) hj⟩ > 2 * δ)
    {j : ℕ} (hjS : j < (dirList S).length) (hj1 : j + 1 < (dirList S).length) :
    (dirList S).get ⟨j, hjS⟩ + δ ≤ Real.pi := by
  have hxjp : (dirList S).get ⟨j + 1, hj1⟩ ≤ Real.pi := (dirList_get_mem_Ioc S ⟨j + 1, hj1⟩).2
  have hsep' : (dirList S).get ⟨j + 1, hj1⟩ - (dirList S).get ⟨j, hjS⟩ > 2 * δ := by
    simpa [dirList_get_ext S (Nat.lt_trans (Nat.lt_succ_self j) hj1) hjS] using (hsep j hj1)
  linarith

/-- The separation bound in the `hjS`-indexed form (consecutive entries). -/
lemma dirList_sep_at (S : Finset ℂ)
    {δ : ℝ} (hsep : ∀ (j : ℕ) (hj : j + 1 < (dirList S).length),
      (dirList S).get ⟨j + 1, hj⟩ -
        (dirList S).get ⟨j, Nat.lt_trans (Nat.lt_succ_self j) hj⟩ > 2 * δ)
    {j : ℕ} (hjS : j < (dirList S).length) (hj1 : j + 1 < (dirList S).length) :
    (dirList S).get ⟨j + 1, hj1⟩ - (dirList S).get ⟨j, hjS⟩ > 2 * δ := by
  simpa [dirList_get_ext S (Nat.lt_trans (Nat.lt_succ_self j) hj1) hjS] using (hsep j hj1)

/-- **The assembled deformation over the star** (statement as in
`Submission.E2bAssembly.deformation_star`).  See the module docstring
for the full dispatch guide. -/
theorem deformation_star (S : Finset ℂ) (hS0 : ∀ z ∈ S, z ≠ 0)
    {h : ℂ → ℂ} (hh : DifferentiableOn ℂ h (Submission.XTransfer.star S)ᶜ)
    (A B δ : ℝ) (u : ℕ → ℝ)
    (hlen0 : 0 < (dirList S).length)
    (hδ : 0 < δ) (hδle : δ ≤ Real.pi)
    (hsep : ∀ (j : ℕ) (hj : j + 1 < (dirList S).length),
      (dirList S).get ⟨j + 1, hj⟩ -
        (dirList S).get ⟨j, Nat.lt_trans (Nat.lt_succ_self j) hj⟩ > 2 * δ)
    (hwrap0 : 2 * Real.pi + (dirList S).get ⟨0, hlen0⟩ -
        (dirList S).get ⟨(dirList S).length - 1, by omega⟩ > 2 * δ)
    (hδx0 : δ < (dirList S).get ⟨0, hlen0⟩ + Real.pi)
    (hBigB : ∀ w ∈ spikeEndpoints S, ‖w‖ < Real.exp B)
    (hshort : ∀ j : ℕ, j < (dirList S).length → ∀ w ∈ spikeEndpoints S,
      Complex.arg w = dirX S hlen0 j → ‖w‖ < Real.exp (u j))
    (hshortπ : ∀ w ∈ spikeEndpoints S, Complex.arg w = Real.pi →
      ‖w‖ < Real.exp (u ((dirList S).length - 1)))
    (hub : ∀ j : ℕ, j < (dirList S).length → u j ≤ B) :
    (∮ z in C((0 : ℂ), Real.exp B), h z) =
      (∑ j ∈ Finset.range (dirList S).length,
        Complex.I • arcInt (Submission.E2bCore.pull h) (u j)
          (dirX S hlen0 j - δ) (dirX S hlen0 j + δ))
        + (∑ j ∈ Finset.range (dirList S).length,
        Complex.I • arcInt (Submission.E2bCore.pull h) A
          (dirX S hlen0 j + δ) (dirX S hlen0 (j + 1) - δ))
        + (∑ j ∈ Finset.range (dirList S).length,
        radInt (Submission.E2bCore.pull h) A (u j) (dirX S hlen0 j - δ))
        - (∑ j ∈ Finset.range (dirList S).length,
        radInt (Submission.E2bCore.pull h) A (u j) (dirX S hlen0 j + δ)) := by
  classical
  -- cyclic closure of the direction spine
  have hcl : dirX S hlen0 (dirList S).length = dirX S hlen0 0 + 2 * Real.pi := by
    rw [dirX_length S hlen0]
    rw [dirX_of_lt S hlen0 hlen0]
  -- arcs at radius e^B over the windows and gaps (whole circle star-free)
  have hBwin : ∀ j : ℕ, j < (dirList S).length → IntervalIntegrable
      (fun y : ℝ => Submission.E2bCore.pull h (B + y * Complex.I)) volume
        (dirX S hlen0 j - δ) (dirX S hlen0 j + δ) := by
    intro j hj
    exact arcB_integrable_any S hh B (c := dirX S hlen0 j - δ) (d := dirX S hlen0 j + δ) hBigB
  have hBgap : ∀ j : ℕ, j < (dirList S).length → IntervalIntegrable
      (fun y : ℝ => Submission.E2bCore.pull h (B + y * Complex.I)) volume
        (dirX S hlen0 j + δ) (dirX S hlen0 (j + 1) - δ) := by
    intro j hj
    exact arcB_integrable_any S hh B (c := dirX S hlen0 j + δ)
      (d := dirX S hlen0 (j + 1) - δ) hBigB
  -- radials at the left window edge x_j − δ
  have hRwinL : ∀ j : ℕ, j < (dirList S).length → IntervalIntegrable
      (fun t : ℝ => Submission.E2bCore.pull h (t + (dirX S hlen0 j - δ : ℝ) * Complex.I)) volume
        A (u j) := by
    intro j hjS
    exact radial_integrable_of_angle_free S hh A (u j) (θ := dirX S hlen0 j - δ)
      (no_dir_left_edge S hlen0 hδ hsep hδx0 (j := j) hjS)
  have hRwinLB : ∀ j : ℕ, j < (dirList S).length → IntervalIntegrable
      (fun t : ℝ => Submission.E2bCore.pull h (t + (dirX S hlen0 j - δ : ℝ) * Complex.I)) volume
        (u j) B := by
    intro j hjS
    exact radial_integrable_of_angle_free S hh (u j) B (θ := dirX S hlen0 j - δ)
      (no_dir_left_edge S hlen0 hδ hsep hδx0 (j := j) hjS)
  -- right window edge x_j + δ is never a direction (per-index dispatch)
  have hradR : ∀ j : ℕ, j < (dirList S).length →
      ∀ d0 ∈ dirSet S, d0 ≠ toIocMod Real.two_pi_pos (-Real.pi) (dirX S hlen0 j + δ) := by
    intro j hjS
    by_cases hlt : j + 1 < (dirList S).length
    · exact no_dir_right_edge S hlen0 hδ hsep (j := j) hjS
        (window_right_le_pi S hδ hsep hjS hlt)
    · have hlast : j + 1 = (dirList S).length := by omega
      by_cases hdu0 : (dirList S).get ⟨j, hjS⟩ + δ ≤ Real.pi
      · exact no_dir_right_edge S hlen0 hδ hsep (j := j) hjS hdu0
      · have hseam0 : Real.pi < (dirList S).get ⟨j, hjS⟩ + δ := by linarith
        exact no_dir_right_edge_seam S hlen0 hδ hδle hwrap0 hδx0 (j := j) hjS hlast hseam0
  have hRwinR : ∀ j : ℕ, j < (dirList S).length → IntervalIntegrable
      (fun t : ℝ => Submission.E2bCore.pull h (t + (dirX S hlen0 j + δ : ℝ) * Complex.I)) volume
        A (u j) := by
    intro j hjS
    exact radial_integrable_of_angle_free S hh A (u j) (θ := dirX S hlen0 j + δ) (hradR j hjS)
  have hRwinRB : ∀ j : ℕ, j < (dirList S).length → IntervalIntegrable
      (fun t : ℝ => Submission.E2bCore.pull h (t + (dirX S hlen0 j + δ : ℝ) * Complex.I)) volume
        (u j) B := by
    intro j hjS
    exact radial_integrable_of_angle_free S hh (u j) B (θ := dirX S hlen0 j + δ) (hradR j hjS)
  -- per-window cell zeros
  have hwin : ∀ j : ℕ, j < (dirList S).length →
      cellExpr (Submission.E2bCore.pull h) (u j) B (dirX S hlen0 j - δ) (dirX S hlen0 j + δ) = 0 := by
    intro j hjS
    rw [dirX_of_lt S hlen0 hjS]
    have hcl0 : -Real.pi < (dirList S).get ⟨j, hjS⟩ - δ := window_left_gt_npi S hlen0 hδx0 hjS
    have hshortj : ∀ w ∈ spikeEndpoints S,
        Complex.arg w = (dirList S).get ⟨j, hjS⟩ → ‖w‖ < Real.exp (u j) := by
      simpa [dirX_of_lt S hlen0 hjS] using (hshort j hjS)
    have hubj : u j ≤ B := hub j hjS
    by_cases hlt : j + 1 < (dirList S).length
    · -- interior window: x_j + δ < x_{j+1} − δ < x_{j+1} ≤ π (non-seam)
      exact hwin_nonseam_dirList S hS0 hh δ (u j) B hδ hsep (j := j) hjS hshortj hcl0
        (window_right_le_pi S hδ hsep hjS hlt) hubj
    · -- last window: seam iff π < x_j + δ
      have hlast : j + 1 = (dirList S).length := by omega
      by_cases hdu0 : (dirList S).get ⟨j, hjS⟩ + δ ≤ Real.pi
      · exact hwin_nonseam_dirList S hS0 hh δ (u j) B hδ hsep (j := j) hjS hshortj hcl0 hdu0 hubj
      · have hseam0 : Real.pi < (dirList S).get ⟨j, hjS⟩ + δ := by linarith
        have hwrap0' : 2 * Real.pi + (dirList S).get ⟨0, hlen0⟩ -
            (dirList S).get ⟨j, hjS⟩ > 2 * δ := by
          rw [← dirList_get_j_last S hjS hlast] at hwrap0
          exact hwrap0
        have hshortπj : ∀ w ∈ spikeEndpoints S,
            Complex.arg w = Real.pi → ‖w‖ < Real.exp (u j) := by
          intro w hw harg
          have hjm1 : j = (dirList S).length - 1 := by omega
          have heq : u j = u ((dirList S).length - 1) := by rw [hjm1]
          rw [heq]
          exact hshortπ w hw harg
        by_cases hxpi : (dirList S).get ⟨j, hjS⟩ = Real.pi
        · exact hwin_seam_pi_dirList S hS0 hh δ (u j) B hδ hδle hsep ⟨j, hjS⟩ hlast hwrap0'
            hxpi hcl0 hshortj hshortπj hubj hBigB
        · have hxlt0 : (dirList S).get ⟨j, hjS⟩ < Real.pi :=
            lt_of_le_of_ne (dirList_get_mem_Ioc S ⟨j, hjS⟩).2 hxpi
          exact hwin_seam_lt_pi_dirList S hS0 hh δ (u j) B hδ hδle hsep ⟨j, hjS⟩ hlast hwrap0'
            hδx0 hxlt0 hseam0 hcl0 hshortj hshortπj hubj hBigB
  -- per-gap cell zeros
  have hgap : ∀ j : ℕ, j < (dirList S).length →
      cellExpr (Submission.E2bCore.pull h) A B (dirX S hlen0 j + δ) (dirX S hlen0 (j + 1) - δ) = 0 := by
    intro j hjS
    by_cases hlt : j + 1 < (dirList S).length
    · -- interior gap between consecutive directions
      rw [dirX_of_lt S hlen0 hjS]
      rw [dirX_of_lt S hlen0 hlt]
      exact hgap_interior_dirList S hS0 hh A B hδ (j := j) hjS hlt
        (dirList_sep_at S hsep hjS hlt)
    · -- wrap gap closing the spine over (x_last + δ, x_0 + 2π − δ)
      have hlast : j + 1 = (dirList S).length := by omega
      rw [dirX_of_lt S hlen0 hjS]
      rw [hlast, dirX_length S hlen0]
      by_cases hdu0 : (dirList S).get ⟨j, hjS⟩ + δ ≤ Real.pi
      · -- split at π (upper piece shifted by −2π)
        have hwrap0' : 2 * Real.pi + (dirList S).get ⟨0, hlen0⟩ -
            (dirList S).get ⟨j, hjS⟩ > 2 * δ := by
          rw [← dirList_get_j_last S hjS hlast] at hwrap0
          exact hwrap0
        have hBarc1 : IntervalIntegrable (fun y : ℝ =>
            Submission.E2bCore.pull h (B + y * Complex.I)) volume
              ((dirList S).get ⟨j, hjS⟩ + δ) Real.pi := by
          exact arcB_integrable_any S hh B (c := (dirList S).get ⟨j, hjS⟩ + δ) (d := Real.pi) hBigB
        have hBarc2 : IntervalIntegrable (fun y : ℝ =>
            Submission.E2bCore.pull h (B + y * Complex.I)) volume
              Real.pi ((dirList S).get ⟨0, hlen0⟩ + 2 * Real.pi - δ) := by
          exact arcB_integrable_any S hh B (c := Real.pi)
            (d := (dirList S).get ⟨0, hlen0⟩ + 2 * Real.pi - δ) hBigB
        have hnoA1 : ∀ y : ℝ, y ∈ Set.uIcc ((dirList S).get ⟨j, hjS⟩ + δ) Real.pi →
            ∀ d0 ∈ dirSet S, d0 ≠ toIocMod Real.two_pi_pos (-Real.pi) y := by
          intro y hy d0 hd0 hEq
          have hui : Set.uIcc ((dirList S).get ⟨j, hjS⟩ + δ) Real.pi =
              Set.Icc ((dirList S).get ⟨j, hjS⟩ + δ) Real.pi := Set.uIcc_of_le hdu0
          have hyi : y ∈ Set.Icc ((dirList S).get ⟨j, hjS⟩ + δ) Real.pi := by
            rw [← hui]
            exact hy
          have hxIoc := dirList_get_mem_Ioc S ⟨j, hjS⟩
          have hyioc : y ∈ Set.Ioc (-Real.pi) (-Real.pi + 2 * Real.pi) := by
            rw [show (-Real.pi + 2 * Real.pi : ℝ) = Real.pi by ring]
            constructor
            · have hxgt : -Real.pi < (dirList S).get ⟨j, hjS⟩ := hxIoc.1
              linarith [hyi.1, hxgt, hδ]
            · exact hyi.2
          have hT : toIocMod Real.two_pi_pos (-Real.pi) y = y := by
            exact (toIocMod_eq_self Real.two_pi_pos (a := -Real.pi) (b := y)).2 hyioc
          have hEq' : d0 = y := by
            rw [hT] at hEq
            exact hEq
          have hle : d0 ≤ (dirList S).get ⟨j, hjS⟩ :=
            Submission.SeamCells.dirList_last_ge S ⟨j, hjS⟩ hlast hd0
          have : d0 < y := by linarith [hle, hyi.1, hδ]
          exact (ne_of_lt this) hEq'
        have hAarc1 : IntervalIntegrable (fun y : ℝ =>
            Submission.E2bCore.pull h (A + y * Complex.I)) volume
              ((dirList S).get ⟨j, hjS⟩ + δ) Real.pi := by
          exact arc_integrable_angle_free S hh A (c := (dirList S).get ⟨j, hjS⟩ + δ)
            (d := Real.pi) hnoA1
        have hnoA2 : ∀ y : ℝ, y ∈ Set.uIcc Real.pi
            ((dirList S).get ⟨0, hlen0⟩ + 2 * Real.pi - δ) →
            ∀ d0 ∈ dirSet S, d0 ≠ toIocMod Real.two_pi_pos (-Real.pi) y := by
          intro y hy d0 hd0 hEq
          have horder : Real.pi ≤ (dirList S).get ⟨0, hlen0⟩ + 2 * Real.pi - δ := by
            linarith [hδx0]
          have hui : Set.uIcc Real.pi ((dirList S).get ⟨0, hlen0⟩ + 2 * Real.pi - δ) =
              Set.Icc Real.pi ((dirList S).get ⟨0, hlen0⟩ + 2 * Real.pi - δ) := Set.uIcc_of_le horder
          have hyi : y ∈ Set.Icc Real.pi ((dirList S).get ⟨0, hlen0⟩ + 2 * Real.pi - δ) := by
            rw [← hui]
            exact hy
          have hxl_lt : (dirList S).get ⟨j, hjS⟩ < Real.pi := by linarith [hdu0, hδ]
          have hle_last : d0 ≤ (dirList S).get ⟨j, hjS⟩ :=
            Submission.SeamCells.dirList_last_ge S ⟨j, hjS⟩ hlast hd0
          by_cases hyπ : y = Real.pi
          · -- y = π: wrapped value is π itself, and every direction is < π
            have hT : toIocMod Real.two_pi_pos (-Real.pi) Real.pi = Real.pi := by
              exact (toIocMod_eq_self Real.two_pi_pos (a := -Real.pi) (b := Real.pi)).2
                (by
                  rw [show (-Real.pi + 2 * Real.pi : ℝ) = Real.pi by ring]
                  exact ⟨by linarith [Real.pi_pos], le_rfl⟩)
            have hEq' : d0 = Real.pi := by
              rw [hyπ] at hEq
              rw [hT] at hEq
              exact hEq
            have : d0 < Real.pi := by linarith [hle_last, hxl_lt]
            exact (ne_of_lt this) hEq'
          · -- π < y: wrapped value is y − 2π ∈ (−π, x_0 − δ], below every direction
            have hygt : Real.pi < y := lt_of_le_of_ne hyi.1 (by exact fun h => hyπ h.symm)
            have hlo : -Real.pi < y - 2 * Real.pi := by linarith [hygt]
            have hhi : y - 2 * Real.pi ≤ Real.pi := by
              have hb : (dirList S).get ⟨0, hlen0⟩ ≤ Real.pi := (dirList_get_mem_Ioc S ⟨0, hlen0⟩).2
              linarith [hyi.2, hb, hδ]
            have hyioc : y - 2 * Real.pi ∈ Set.Ioc (-Real.pi) (-Real.pi + 2 * Real.pi) := by
              rw [show (-Real.pi + 2 * Real.pi : ℝ) = Real.pi by ring]
              exact ⟨hlo, hhi⟩
            have hT : toIocMod Real.two_pi_pos (-Real.pi) y = y - 2 * Real.pi := by
              rw [toIocMod_eq_iff Real.two_pi_pos (a := -Real.pi) (b := y) (c := y - 2 * Real.pi)]
              constructor
              · exact hyioc
              · refine ⟨1, ?_⟩
                ring
            have hEq' : d0 = y - 2 * Real.pi := by
              rw [hT] at hEq
              exact hEq
            have hge : (dirList S).get ⟨0, hlen0⟩ ≤ d0 :=
              Submission.SeamCells.dirList_head_le S hlen0 hd0
            have hbd : y - 2 * Real.pi < (dirList S).get ⟨0, hlen0⟩ := by
              have hbd0 : y - 2 * Real.pi ≤ (dirList S).get ⟨0, hlen0⟩ - δ := by linarith [hyi.2]
              linarith [hbd0, hδ]
            exact (ne_of_gt (by linarith [hbd, hge])) hEq'
        have hAarc2 : IntervalIntegrable (fun y : ℝ =>
            Submission.E2bCore.pull h (A + y * Complex.I)) volume
              Real.pi ((dirList S).get ⟨0, hlen0⟩ + 2 * Real.pi - δ) := by
          exact arc_integrable_angle_free S hh A (c := Real.pi)
            (d := (dirList S).get ⟨0, hlen0⟩ + 2 * Real.pi - δ) hnoA2
        exact hgap_wrap_dirList S hS0 hh A B hδ ⟨j, hjS⟩ hlast hδx0 hwrap0'
          hBarc1 hBarc2 hAarc1 hAarc2
      · -- the whole cell lies above π: shift by −2π into the direction-free range
        have hseam0 : Real.pi < (dirList S).get ⟨j, hjS⟩ + δ := by linarith
        have hwrap0' : 2 * Real.pi + (dirList S).get ⟨0, hlen0⟩ -
            (dirList S).get ⟨j, hjS⟩ > 2 * δ := by
          rw [← dirList_get_j_last S hjS hlast] at hwrap0
          exact hwrap0
        exact gap_wrap_above_pi S hS0 hh A B hδ ⟨j, hjS⟩ hlast hlen0 hwrap0' hδx0 hseam0
  -- assemble the deformation identity
  exact circle_eq_cap_sum_x h (dirList S).length (Nat.succ_le_of_lt hlen0) A B δ
    (dirX S hlen0) u hcl hBwin hBgap hRwinL hRwinLB hRwinR hRwinRB hwin hgap

end Submission.DStar
