import Mathlib
import Submission.TipCell
import Submission.SpineGaps
import Submission.Fold
import Submission.E2bCore
import Submission.DirCycle
import Submission.DirSet
import Submission.SepLemma

/-!
# E2b geometry instantiation: window and gap cell zeros for the hedgehog

The E2b deformation theorem `Submission.E2bT.circle_eq_cap_sum`
(`Submission/E2bGeneral.lean`, general-`s`, PROVED) consumes, for each
window cell `[u j, B] × (b(2j), b(2j+1))` and gap cell
`[A, B] × (b(2j+1), b(2j+2))`, the *per-cell zero* facts `hwin` and `hgap`
(`cellExpr (pull h) … = 0`, from the rectangle Cauchy identity).  This
module supplies them for the actual hedgehog `star S`:

1. `window_cell_zero` (NON-SEAM): for a direction `x ∈ (−π, π]` whose
   closed `δ`-window `[x−δ, x+δ]` still lies inside `(−π, π]`, if every
   spike endpoint `z²`, `z⁴` whose argument points into the window is
   shorter than `e^u` (so the exp-image of the cell rectangle is
   star-free, `Submission.TipCell.expRect_avoids_star_tip`), the
   above-the-tip cell `[u, B] × (x−δ, x+δ)` has zero boundary integral:
       `cellExpr (pull h) u B (x−δ) (x+δ) = 0`
   (this is `hwin` for non-seam directions; seam-crossing windows of the
   first/last directions are split at `±π` and glued via
   `Submission.E2bT.cellExpr_add_two_pi`/`cellExpr_sub_two_pi` +
   `cellExpr_add_adjacent` in a later module).

2. `gap_cell_zero` is already available end-to-end as
   `Submission.SpineGaps.gap_cell_between_dirList` (for any range strictly
   between consecutive `Submission.DirCycle.dirList` entries; such ranges
   are automatically inside `(−π, π]`); a re-exported convenience
   `gap_cell_between_dirList` in this namespace is provided.

3. Continuity/integrability boilerplate, collected once here:
   `continuousOn_pull_of_differentiableOn` (the pulled-back 1-form
   `w ↦ pull h w = h (exp w)·exp w` is continuous on the preimage of the
   complement of the hedgehog when `h` is differentiable off the hedgehog)
   and `intervalIntegrable_pull_arc` / `intervalIntegrable_pull_radial`
   (the arc/radial pieces of the cells are integrable whenever their
   exp-images avoid the hedgehog).  These discharge the `hBint`/`hRint`
   families of `circle_eq_cap_sum` in the application.

All `radInt`/`arcInt`/`cellExpr` are those of `Submission.Fold`
(definitionally equal to `Submission.E2bCore`'s copies); `pull` is
`Submission.E2bCore.pull`.  `h : ℂ → ℂ` is assumed differentiable on the
complement `(star S)ᶜ` (open since the hedgehog is closed), and every
`z ∈ S` nonzero (so all spike endpoints are nonzero).
-/

noncomputable section

open scoped Complex Real Interval
open Complex
open MeasureTheory

namespace Submission.E2bCells

open Submission.XTransfer
open Submission.DirSet
open Submission.Fold
open Submission.TipCell
open Submission.DirCycle

/-- **Non-seam above-the-tip window cell zero.**  Direction `x` with its
closed `δ`-window inside `(−π, π]`; every spike endpoint pointing into the
window is shorter than `e^u`.  Then the pulled-back boundary integral over
the cell `[[u, B]] ×ℂ [[x−δ, x+δ]]` vanishes for every `h` holomorphic off
the hedgehog.  (This is the `hwin` of `Submission.E2bT.circle_eq_cap_sum`
for the non-seam directions.) -/
theorem window_cell_zero (S : Finset ℂ) (hS0 : ∀ z ∈ S, z ≠ 0)
    {h : ℂ → ℂ} (hh : DifferentiableOn ℂ h (Submission.XTransfer.star S)ᶜ)
    (u B x δ : ℝ) (hub : u ≤ B) (hδ : 0 < δ)
    (hcl : -Real.pi < x - δ) (hdu : x + δ ≤ Real.pi)
    (htip : ∀ z ∈ S,
      (Complex.arg (z ^ 2) ∈ Set.Icc (x - δ) (x + δ) → ‖z ^ 2‖ < Real.exp u) ∧
      (Complex.arg (z ^ 4) ∈ Set.Icc (x - δ) (x + δ) → ‖z ^ 4‖ < Real.exp u)) :
    cellExpr (Submission.E2bCore.pull h) u B (x - δ) (x + δ) = 0 := by
  have hc : x - δ < x + δ := by linarith [hδ]
  exact Fold.pullback_cell_zero h u B (x - δ) (x + δ)
    (TipCell.tip_cell_boundary_integral_eq_zero (S := S) hS0 hh u B hub
      (c := x - δ) (d := x + δ) hc hcl hdu htip)

/-- Re-export of the gap-cell zero between consecutive directions
(`Submission.SpineGaps.gap_cell_between_dirList`), stated with
`pull h` for uniformity with `window_cell_zero`. -/
theorem gap_cell_between_dirList (S : Finset ℂ) (hS0 : ∀ z ∈ S, z ≠ 0)
    {h : ℂ → ℂ} (hh : DifferentiableOn ℂ h (Submission.XTransfer.star S)ᶜ)
    (a b : ℝ) (i : Fin (dirList S).length) (hi : i.val + 1 < (dirList S).length)
    {c d : ℝ} (hxc : (dirList S).get i < c) (hcd : c < d)
    (hdy : d < (dirList S).get ⟨i.val + 1, hi⟩) :
    cellExpr (Submission.E2bCore.pull h) a b c d = 0 := by
  change cellExpr (fun w : ℂ => h (Complex.exp w) * Complex.exp w) a b c d = 0
  exact SpineGaps.gap_cell_between_dirList S hS0 hh a b i hi hxc hcd hdy

/-- The exp-pullback of `h` is continuous on the preimage of the hedgehog
complement (composition of `h`-continuity on `(star S)ᶜ`, `exp` and
multiplication by `exp`). -/
lemma continuousOn_pull_of_differentiableOn (S : Finset ℂ)
    {h : ℂ → ℂ} (hh : DifferentiableOn ℂ h (Submission.XTransfer.star S)ᶜ) :
    ContinuousOn (fun w : ℂ => Submission.E2bCore.pull h w)
      {w : ℂ | Complex.exp w ∉ Submission.XTransfer.star S} := by
  have hPhi : ContinuousOn (fun z : ℂ => h z * z) (Submission.XTransfer.star S)ᶜ :=
    hh.continuousOn.mul continuousOn_id
  have hf : ContinuousOn (fun w : ℂ => Complex.exp w)
      {w : ℂ | Complex.exp w ∉ Submission.XTransfer.star S} := by
    intro w hw
    exact Complex.continuous_exp.continuousAt.continuousWithinAt
  have hmap : Set.MapsTo (fun w : ℂ => Complex.exp w)
      {w : ℂ | Complex.exp w ∉ Submission.XTransfer.star S}
      (Submission.XTransfer.star S)ᶜ := by
    intro w hw
    exact hw
  have hcomp : ContinuousOn (fun w : ℂ => h (Complex.exp w) * Complex.exp w)
      {w : ℂ | Complex.exp w ∉ Submission.XTransfer.star S} :=
    hPhi.comp hf hmap
  change ContinuousOn (fun w : ℂ => h (Complex.exp w) * Complex.exp w)
      {w : ℂ | Complex.exp w ∉ Submission.XTransfer.star S}
  exact hcomp

/-- **Arc integrability.**  The pulled-back integrand along a circle arc of
radius `e^r` (`y ↦ pull h (r + y·I)`) is integrable on `[c,d]` provided the
whole arc-image avoids the hedgehog. -/
lemma intervalIntegrable_pull_arc (S : Finset ℂ)
    {h : ℂ → ℂ} (hh : DifferentiableOn ℂ h (Submission.XTransfer.star S)ᶜ)
    (r : ℝ) {c d : ℝ}
    (hfree : ∀ y : ℝ, y ∈ Set.uIcc c d →
      Complex.exp (r + y * Complex.I) ∉ Submission.XTransfer.star S) :
    IntervalIntegrable (fun y : ℝ => Submission.E2bCore.pull h (r + y * Complex.I)) volume c d := by
  have hcont : ContinuousOn h (Submission.XTransfer.star S)ᶜ := hh.continuousOn
  let g : ℝ → ℂ := fun y => Complex.exp (r + y * Complex.I)
  have hg_maps : Set.MapsTo g (Set.uIcc c d) (Submission.XTransfer.star S)ᶜ := by
    intro y hy
    exact hfree y hy
  have hg_cont : ContinuousOn g (Set.uIcc c d) := by
    intro y hy
    exact (Complex.continuous_exp.continuousAt.comp (by
      -- y ↦ r + y * I continuous at y (as map ℝ → ℂ)
      fun_prop)).continuousWithinAt
  have hcomp : ContinuousOn (fun y : ℝ => h (g y)) (Set.uIcc c d) :=
    hcont.comp hg_cont hg_maps
  have hmul : ContinuousOn (fun y : ℝ => h (g y) * g y) (Set.uIcc c d) := hcomp.mul hg_cont
  have hconv : (fun y : ℝ => Submission.E2bCore.pull h (r + y * Complex.I))
      = fun y : ℝ => h (g y) * g y := by
    funext y
    rfl
  rw [hconv]
  exact ContinuousOn.intervalIntegrable hmul

/-- **Radial integrability.**  The pulled-back integrand along a radial
segment at angle `c` (`t ↦ pull h (t + c·I)`) is integrable on `[a,b]`
provided the whole segment-image avoids the hedgehog. -/
lemma intervalIntegrable_pull_radial (S : Finset ℂ)
    {h : ℂ → ℂ} (hh : DifferentiableOn ℂ h (Submission.XTransfer.star S)ᶜ)
    {a b : ℝ} (c : ℝ)
    (hfree : ∀ t : ℝ, t ∈ Set.uIcc a b →
      Complex.exp (t + c * Complex.I) ∉ Submission.XTransfer.star S) :
    IntervalIntegrable (fun t : ℝ => Submission.E2bCore.pull h (t + c * Complex.I)) volume a b := by
  have hcont : ContinuousOn h (Submission.XTransfer.star S)ᶜ := hh.continuousOn
  let g : ℝ → ℂ := fun t => Complex.exp (t + c * Complex.I)
  have hg_maps : Set.MapsTo g (Set.uIcc a b) (Submission.XTransfer.star S)ᶜ := by
    intro t ht
    exact hfree t ht
  have hg_cont : ContinuousOn g (Set.uIcc a b) := by
    intro t ht
    exact (Complex.continuous_exp.continuousAt.comp (by
      fun_prop)).continuousWithinAt
  have hcomp : ContinuousOn (fun t : ℝ => h (g t)) (Set.uIcc a b) :=
    hcont.comp hg_cont hg_maps
  have hmul : ContinuousOn (fun t : ℝ => h (g t) * g t) (Set.uIcc a b) := hcomp.mul hg_cont
  have hconv : (fun t : ℝ => Submission.E2bCore.pull h (t + c * Complex.I))
      = fun t : ℝ => h (g t) * g t := by
    funext t
    rfl
  rw [hconv]
  exact ContinuousOn.intervalIntegrable hmul


/-! ## Non-seam `hwin` instantiation over the direction list -/

/-- `z²` is a spike endpoint. -/
lemma spikeEndpoints_mem_sq (S : Finset ℂ) {z : ℂ} (hz : z ∈ S) :
    z ^ 2 ∈ spikeEndpoints S := by
  classical
  rw [spikeEndpoints, Finset.mem_union]
  exact Or.inl (Finset.mem_image.mpr ⟨z, hz, rfl⟩)

/-- `z⁴` is a spike endpoint. -/
lemma spikeEndpoints_mem_pow4 (S : Finset ℂ) {z : ℂ} (hz : z ∈ S) :
    z ^ 4 ∈ spikeEndpoints S := by
  classical
  rw [spikeEndpoints, Finset.mem_union]
  exact Or.inr (Finset.mem_image.mpr ⟨z, hz, rfl⟩)

/-- **Non-seam window `hwin` for a direction of the list.**  For the
direction `x := (dirList S).get i` whose `δ`-window contains no other
direction (`hsepi`, supplied by `Submission.SepLemma.dirList_window_
separated` from the consecutive-gap bounds) and stays inside `(−π, π]`
(`hcl`, `hdu`), if every spike along `x` is shorter than `e^u` (`hshort`)
then the above-the-tip window cell `[u, B] × (x−δ, x+δ)` has zero boundary
integral: this is the `hwin` hypothesis of
`Submission.E2bT.circle_eq_cap_sum` for a non-seam direction. -/
theorem nonseam_window_zero_dirList (S : Finset ℂ) (hS0 : ∀ z ∈ S, z ≠ 0)
    {h : ℂ → ℂ} (hh : DifferentiableOn ℂ h (Submission.XTransfer.star S)ᶜ)
    (δ u B : ℝ) (hδ : 0 < δ)
    (i : Fin (dirList S).length)
    (hsepi : ∀ θ ∈ dirSet S,
      θ ∈ Set.Icc ((dirList S).get i - δ) ((dirList S).get i + δ) →
        θ = (dirList S).get i)
    (hshort : ∀ w ∈ spikeEndpoints S,
      Complex.arg w = (dirList S).get i → ‖w‖ < Real.exp u)
    (hcl : -Real.pi < (dirList S).get i - δ)
    (hdu : (dirList S).get i + δ ≤ Real.pi)
    (hub : u ≤ B) :
    cellExpr (Submission.E2bCore.pull h) u B
      ((dirList S).get i - δ) ((dirList S).get i + δ) = 0 := by
  classical
  let x : ℝ := (dirList S).get i
  have htip : ∀ z ∈ S,
      (Complex.arg (z ^ 2) ∈ Set.Icc (x - δ) (x + δ) → ‖z ^ 2‖ < Real.exp u) ∧
      (Complex.arg (z ^ 4) ∈ Set.Icc (x - δ) (x + δ) → ‖z ^ 4‖ < Real.exp u) := by
    intro z hz
    constructor
    · intro harg
      have hargD : Complex.arg (z ^ 2) ∈ dirSet S := arg_sq_mem_dirSet hz
      have heq : Complex.arg (z ^ 2) = x := hsepi (Complex.arg (z ^ 2)) hargD (by simpa [x] using harg)
      exact hshort (z ^ 2) (spikeEndpoints_mem_sq S hz) heq
    · intro harg
      have hargD : Complex.arg (z ^ 4) ∈ dirSet S := arg_pow4_mem_dirSet hz
      have heq : Complex.arg (z ^ 4) = x := hsepi (Complex.arg (z ^ 4)) hargD (by simpa [x] using harg)
      exact hshort (z ^ 4) (spikeEndpoints_mem_pow4 S hz) heq
  have hcl' : -Real.pi < x - δ := by simpa [x] using hcl
  have hdu' : x + δ ≤ Real.pi := by simpa [x] using hdu
  exact window_cell_zero S hS0 hh u B x δ hub hδ hcl' hdu' htip


/-- **Non-seam window `hwin` from the consecutive-gap bounds.**  Same as
`nonseam_window_zero_dirList` but the direction-freeness of the window
(`hsepi`) is derived from the consecutive-gap bounds `hsep` (the output
shape of `Submission.E2bParam.exists_delta`) by
`Submission.SepLemma.dirList_window_separated`. -/
theorem nonseam_window_zero_of_sep (S : Finset ℂ) (hS0 : ∀ z ∈ S, z ≠ 0)
    {h : ℂ → ℂ} (hh : DifferentiableOn ℂ h (Submission.XTransfer.star S)ᶜ)
    (δ u B : ℝ) (hδ : 0 < δ)
    (hsep : ∀ (j : ℕ) (hj : j + 1 < (dirList S).length),
      (dirList S).get ⟨j + 1, hj⟩ -
        (dirList S).get ⟨j, Nat.lt_trans (Nat.lt_succ_self j) hj⟩ > 2 * δ)
    (i : Fin (dirList S).length)
    (hshort : ∀ w ∈ spikeEndpoints S,
      Complex.arg w = (dirList S).get i → ‖w‖ < Real.exp u)
    (hcl : -Real.pi < (dirList S).get i - δ)
    (hdu : (dirList S).get i + δ ≤ Real.pi)
    (hub : u ≤ B) :
    cellExpr (Submission.E2bCore.pull h) u B
      ((dirList S).get i - δ) ((dirList S).get i + δ) = 0 := by
  have hsepi : ∀ θ ∈ dirSet S,
      θ ∈ Set.Icc ((dirList S).get i - δ) ((dirList S).get i + δ) →
        θ = (dirList S).get i := fun θ hθ hwin =>
    SepLemma.dirList_window_separated (S := S) (δ := δ) hsep i hθ hwin
  exact nonseam_window_zero_dirList S hS0 hh δ u B hδ i hsepi hshort hcl hdu hub


/-- **Generalized above-the-tip window cell zero.**  For any angular range
`[c,d] ⊆ (−π, π]` that contains no direction other than `x` (`honly`) and
whose every spike (endpoint with argument `x`) is shorter than `e^u`
(`hshort`), the cell `[u, B] × (c, d)` has zero boundary integral.  (This
covers the non-seam windows (`c = x−δ, d = x+δ`) and the lower seam pieces
(`c = x−δ, d = π`) uniformly.) -/
theorem window_cell_zero_gen (S : Finset ℂ) (hS0 : ∀ z ∈ S, z ≠ 0)
    {h : ℂ → ℂ} (hh : DifferentiableOn ℂ h (Submission.XTransfer.star S)ᶜ)
    (u B : ℝ) (hub : u ≤ B) {x c d : ℝ} (hcd : c < d)
    (hcl : -Real.pi < c) (hdu : d ≤ Real.pi)
    (honly : ∀ θ ∈ dirSet S, θ ∈ Set.Icc c d → θ = x)
    (hshort : ∀ w ∈ spikeEndpoints S, Complex.arg w = x → ‖w‖ < Real.exp u) :
    cellExpr (Submission.E2bCore.pull h) u B c d = 0 := by
  have htip : ∀ z ∈ S,
      (Complex.arg (z ^ 2) ∈ Set.Icc c d → ‖z ^ 2‖ < Real.exp u) ∧
      (Complex.arg (z ^ 4) ∈ Set.Icc c d → ‖z ^ 4‖ < Real.exp u) := by
    intro z hz
    constructor
    · intro harg
      have hargD : Complex.arg (z ^ 2) ∈ dirSet S := arg_sq_mem_dirSet hz
      have heq : Complex.arg (z ^ 2) = x := honly (Complex.arg (z ^ 2)) hargD harg
      exact hshort (z ^ 2) (spikeEndpoints_mem_sq S hz) heq
    · intro harg
      have hargD : Complex.arg (z ^ 4) ∈ dirSet S := arg_pow4_mem_dirSet hz
      have heq : Complex.arg (z ^ 4) = x := honly (Complex.arg (z ^ 4)) hargD harg
      exact hshort (z ^ 4) (spikeEndpoints_mem_pow4 S hz) heq
  exact Fold.pullback_cell_zero h u B c d
    (TipCell.tip_cell_boundary_integral_eq_zero (S := S) hS0 hh u B hub
      (c := c) (d := d) hcd hcl hdu htip)

end Submission.E2bCells

end
