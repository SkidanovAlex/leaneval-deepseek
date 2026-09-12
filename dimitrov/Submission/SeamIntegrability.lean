import Mathlib
import Submission.E2bCells
import Submission.SeamCells
import Submission.DirCycle
import Submission.DirSet
import Submission.SpineGaps

/-!
# Arc integrability for the seam window (isolated delegation task)

`Submission.SeamCells.seam_window_zero_lt_pi` and
`seam_window_zero_pi` (the seam window zeros for the LAST direction
`x := (dirList S).get i` of the spike spine, whose `δ`-window crosses the
arg branch at `π`) consume four interval-integrability facts for the arcs
at the outer radius `e^B` and at the tip radius `e^u` over the two split
pieces `(x−δ, π)` and `(π, x+δ)`:

    seam_arcB_1 : IntervalIntegrable (fun y => pull h (B + y·I)) volume (x−δ) π
    seam_arcB_2 : IntervalIntegrable (fun y => pull h (B + y·I)) volume π (x+δ)
    seam_arcU_1 : IntervalIntegrable (fun y => pull h (u + y·I)) volume (x−δ) π
    seam_arcU_2 : IntervalIntegrable (fun y => pull h (u + y·I)) volume π (x+δ)

This module proves them (no unfinished proofs may remain; add helpers
freely; do not change the four public statements).

PROOF of each: instantiate `Submission.E2bCells.intervalIntegrable_pull_arc`
with the star-freeness of the arc-image `exp(u + y·I)` / `exp(B + y·I)`
for `y` in the range.  The star-freeness is geometric:

* **B-arcs** (`seam_arcB_1`, `seam_arcB_2`): the whole circle `|X| = e^B`
  avoids the hedgehog when `B` is above every spike tip (`hBigB`:
  `∀ w ∈ spikeEndpoints S, ‖w‖ < Real.exp B`): every star point has
  modulus `≤ ‖w‖ < e^B` for its endpoint `w` (use
  `Submission.XTransfer.mem_segment_zero_iff` and `norm_smul`), so the
  circle point `exp(B + y·I)` (modulus `e^B`, `Complex.norm_exp`) is not
  on the star.  This works for ANY real range `(c,d)`; prove a generic
  helper `arcB_integrable (c d : ℝ)` and specialize.

* **u-arc over the lower piece** (`seam_arcU_1` over `(x−δ, π)`): points
  `exp(u + y·I)` with `y ∈ (x−δ, π]` have argument `y` (interior
  `y > −π` guaranteed by `hcl`; `y = π` gives argument `π`).  No direction
  lies in `(x−δ, π)` other than possibly `x` itself (`hsepi` over the
  larger window), and every spike along `x` is shorter than `e^u`
  (`hshort`), so no star point lies at modulus `e^u` in this angular
  sector (`norm` bound as in `Submission.TipCell.expRect_avoids_star_tip`).

* **u-arc over the upper piece** (`seam_arcU_2` over `(π, x+δ)`): points
  have argument `y − 2π ∈ (−π, x+δ−2π)` (`Complex.arg_exp`); this range
  contains no direction because every direction is `≥ x₀` and the wrap
  bound `hwrap0` (`2π + x₀ − x > 2δ`) gives `x₀ > x + δ − 2π`
  (`dirList_head_le`).  So the arc is star-free regardless of `u`.

COMMON HYPOTHESES (shared by the four lemmas, mirroring
`Submission.SeamCells.seam_window_zero_lt_pi`/`seam_window_zero_pi`):
`S`, `hS0 : ∀ z ∈ S, z ≠ 0`, `h : ℂ → ℂ` differentiable off the hedgehog,
`δ u B : ℝ`, `hδ : 0 < δ`, the last index `i : Fin (dirList S).length`
with `hlast : i.val + 1 = (dirList S).length`, the first-direction bound
`hδx0 : δ < x₀ + π`, the wrap bound `hwrap0 : 2π + x₀ − x > 2δ`
(`x₀ := (dirList S).get ⟨0, hlen0⟩`, `x := (dirList S).get i`,
`hlen0 := (0 < length)` derived from `i`), the lower-window bound
`hcl : −π < x − δ`, the window separation `hsepi : ∀ θ ∈ dirSet S,
θ ∈ Icc (x−δ) (x+δ) → θ = x`, and the short-spike hypothesis
`hshort : ∀ w ∈ spikeEndpoints S, Complex.arg w = x → ‖w‖ < Real.exp u`.
For the B-arcs also `hBigB : ∀ w ∈ spikeEndpoints S, ‖w‖ < Real.exp B`.
-/

noncomputable section
open scoped Complex Real Interval BigOperators
open Complex
open MeasureTheory

namespace Submission.SeamIntegrability

open Submission.DirCycle
open Submission.DirSet
open Submission.E2bCells

open Submission.XTransfer

/-- A point on the segment `[0, c]` has norm at most `‖c‖`. -/
lemma norm_le_norm_of_mem_segment_zero (c X : ℂ) (hX : X ∈ segment ℝ 0 c) :
    ‖X‖ ≤ ‖c‖ := by
  rcases (mem_segment_zero_iff c X).mp hX with ⟨t, ht01, htX⟩
  calc
    ‖X‖ = ‖t • c‖ := by rw [htX]
    _ = t * ‖c‖ := by rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ht01.1]
    _ ≤ ‖c‖ := by exact mul_le_of_le_one_left (norm_nonneg c) ht01.2

/-- Every star point has norm strictly below `e^B` when `B` is above every
spike tip (`hBigB`). -/
lemma norm_lt_exp_of_mem_star (S : Finset ℂ) {B : ℝ}
    (hBigB : ∀ w ∈ spikeEndpoints S, ‖w‖ < Real.exp B) {X : ℂ} (hX : X ∈ star S) :
    ‖X‖ < Real.exp B := by
  classical
  rcases hX with ⟨z, hz, hseg⟩
  rcases hseg with h2 | h4
  · have hw : z ^ 2 ∈ spikeEndpoints S := spikeEndpoints_mem_sq S hz
    exact lt_of_le_of_lt (norm_le_norm_of_mem_segment_zero (z ^ 2) X h2) (hBigB (z ^ 2) hw)
  · have hw : z ^ 4 ∈ spikeEndpoints S := spikeEndpoints_mem_pow4 S hz
    exact lt_of_le_of_lt (norm_le_norm_of_mem_segment_zero (z ^ 4) X h4) (hBigB (z ^ 4) hw)

/-- The circle of radius `e^B` avoids the hedgehog when `B` is above every
spike tip: `exp (B + y·I) ∉ star S` for every real `y`. -/
lemma exp_circle_not_mem_star (S : Finset ℂ) {B : ℝ}
    (hBigB : ∀ w ∈ spikeEndpoints S, ‖w‖ < Real.exp B) :
    ∀ y : ℝ, Complex.exp (B + y * Complex.I) ∉ star S := by
  intro y hyx
  have hlt : ‖Complex.exp (B + y * Complex.I)‖ < Real.exp B :=
    norm_lt_exp_of_mem_star S hBigB hyx
  have heq : ‖Complex.exp (B + y * Complex.I)‖ = Real.exp B := by
    rw [Complex.norm_exp]
    simp
  linarith

/-- Generic B-arc integrability on any real range `(c, d)`. -/
lemma arcB_integrable (S : Finset ℂ) {h : ℂ → ℂ}
    (hh : DifferentiableOn ℂ h (Submission.XTransfer.star S)ᶜ)
    (B : ℝ) {c d : ℝ}
    (hBigB : ∀ w ∈ spikeEndpoints S, ‖w‖ < Real.exp B) :
    IntervalIntegrable (fun y : ℝ =>
      Submission.E2bCore.pull h (B + y * Complex.I)) volume c d := by
  exact intervalIntegrable_pull_arc S hh B (c := c) (d := d) (by
    intro y hy
    exact exp_circle_not_mem_star S hBigB y)

/-- B-arc over the lower seam piece. -/
theorem seam_arcB_1 (S : Finset ℂ) (hS0 : ∀ z ∈ S, z ≠ 0)
    {h : ℂ → ℂ} (hh : DifferentiableOn ℂ h (Submission.XTransfer.star S)ᶜ)
    (B : ℝ) {δ : ℝ} (hδ : 0 < δ)
    (i : Fin (dirList S).length)
    (hBigB : ∀ w ∈ spikeEndpoints S, ‖w‖ < Real.exp B) :
    IntervalIntegrable (fun y : ℝ =>
      Submission.E2bCore.pull h (B + y * Complex.I)) volume
        ((dirList S).get i - δ) Real.pi := by
  exact arcB_integrable S hh B (c := (dirList S).get i - δ) (d := Real.pi) hBigB

/-- B-arc over the upper seam piece. -/
theorem seam_arcB_2 (S : Finset ℂ) (hS0 : ∀ z ∈ S, z ≠ 0)
    {h : ℂ → ℂ} (hh : DifferentiableOn ℂ h (Submission.XTransfer.star S)ᶜ)
    (B : ℝ) {δ : ℝ} (hδ : 0 < δ)
    (i : Fin (dirList S).length)
    (hBigB : ∀ w ∈ spikeEndpoints S, ‖w‖ < Real.exp B) :
    IntervalIntegrable (fun y : ℝ =>
      Submission.E2bCore.pull h (B + y * Complex.I)) volume
        Real.pi ((dirList S).get i + δ) := by
  exact arcB_integrable S hh B (c := Real.pi) (d := (dirList S).get i + δ) hBigB

/-- Every direction of the hedgehog lies in `(−π, π]`. -/
lemma dirSet_mem_bounds (S : Finset ℂ) {θ : ℝ} (hθ : θ ∈ dirSet S) :
    -Real.pi < θ ∧ θ ≤ Real.pi := by
  classical
  rcases (Finset.mem_image.mp hθ) with ⟨c, hc, rfl⟩
  exact (Complex.arg_mem_Ioc c)

/-- A point `X ≠ 0` of modulus `e^u` whose argument is `a` is not on the
hedgehog when every spike endpoint of argument `a` is shorter than `e^u`. -/
lemma exp_ray_not_mem_star_of_short {S : Finset ℂ} {u a : ℝ}
    (hshort : ∀ w ∈ spikeEndpoints S, Complex.arg w = a → ‖w‖ < Real.exp u)
    (X : ℂ) (hXnorm : ‖X‖ = Real.exp u) (hargX : Complex.arg X = a)
    (hX0 : X ≠ 0) : X ∉ star S := by
  intro hXstar
  rcases hXstar with ⟨z, hz, hseg⟩
  rcases hseg with h2 | h4
  · have hw : z ^ 2 ∈ spikeEndpoints S := spikeEndpoints_mem_sq S hz
    have hargw : Complex.arg (z ^ 2) = a := by
      calc
        Complex.arg (z ^ 2) = Complex.arg X :=
          (Submission.StarGeom.arg_eq_of_mem_segment_zero_ne_zero h2 hX0).symm
        _ = a := hargX
    have hs := hshort (z ^ 2) hw hargw
    have hle : ‖X‖ ≤ ‖z ^ 2‖ := norm_le_norm_of_mem_segment_zero (z ^ 2) X h2
    linarith
  · have hw : z ^ 4 ∈ spikeEndpoints S := spikeEndpoints_mem_pow4 S hz
    have hargw : Complex.arg (z ^ 4) = a := by
      calc
        Complex.arg (z ^ 4) = Complex.arg X :=
          (Submission.StarGeom.arg_eq_of_mem_segment_zero_ne_zero h4 hX0).symm
        _ = a := hargX
    have hs := hshort (z ^ 4) hw hargw
    have hle : ‖X‖ ≤ ‖z ^ 4‖ := norm_le_norm_of_mem_segment_zero (z ^ 4) X h4
    linarith

/-- `exp (u + π·I)` avoids the hedgehog when every `π`-spike is shorter than
`e^u` (`hshortπ`). -/
lemma exp_pi_arc_not_mem_star {S : Finset ℂ} {u : ℝ}
    (hshortπ : ∀ w ∈ spikeEndpoints S, Complex.arg w = Real.pi → ‖w‖ < Real.exp u) :
    Complex.exp (u + Real.pi * Complex.I) ∉ star S := by
  have hXn : ‖Complex.exp (u + Real.pi * Complex.I)‖ = Real.exp u := by
    rw [Complex.norm_exp]
    simp
  have harg : Complex.arg (Complex.exp (u + Real.pi * Complex.I)) = Real.pi := by
    exact Submission.StarGeom.arg_exp_add_mul_I (x := u) (y := Real.pi)
      (by linarith [Real.pi_pos]) (le_refl Real.pi)
  exact exp_ray_not_mem_star_of_short hshortπ (Complex.exp (u + Real.pi * Complex.I))
    hXn harg (Complex.exp_ne_zero _)

/-- u-arc over the lower seam piece (window sector, short spikes).  The
window crosses the branch at `π` (`hseam`), so the whole lower piece
`(x−δ, π)` lies inside the window `(x−δ, x+δ)`; interior points have
argument in `(x−δ, π]` (only direction `x`, spikes short by `hshort`); the
endpoint `y = π` has argument `π` (spikes short by `hshortπ`). -/
theorem seam_arcU_1 (S : Finset ℂ) (hS0 : ∀ z ∈ S, z ≠ 0)
    {h : ℂ → ℂ} (hh : DifferentiableOn ℂ h (Submission.XTransfer.star S)ᶜ)
    (δ u : ℝ) (hδ : 0 < δ)
    (i : Fin (dirList S).length)
    (hseam : Real.pi < (dirList S).get i + δ)
    (hsepi : ∀ θ ∈ dirSet S,
      θ ∈ Set.Icc ((dirList S).get i - δ) ((dirList S).get i + δ) →
        θ = (dirList S).get i)
    (hshort : ∀ w ∈ spikeEndpoints S,
      Complex.arg w = (dirList S).get i → ‖w‖ < Real.exp u)
    (hshortπ : ∀ w ∈ spikeEndpoints S,
      Complex.arg w = Real.pi → ‖w‖ < Real.exp u)
    (hcl : -Real.pi < (dirList S).get i - δ) :
    IntervalIntegrable (fun y : ℝ =>
      Submission.E2bCore.pull h (u + y * Complex.I)) volume
        ((dirList S).get i - δ) Real.pi := by
  classical
  let x : ℝ := (dirList S).get i
  have hseam' : Real.pi < x + δ := by simpa [x] using hseam
  have hcl' : -Real.pi < x - δ := by simpa [x] using hcl
  have hx_dir : x ∈ dirSet S := by
    have hm : (dirList S).get i ∈ dirList S := List.get_mem (dirList S) i
    exact (dirList_mem_iff S x).mp (by simpa [x] using hm)
  have hx_le_pi : x ≤ Real.pi := (dirSet_mem_bounds S hx_dir).2
  have hcd : x - δ < Real.pi := by linarith [hδ, hx_le_pi]
  have hfree : ∀ y : ℝ, y ∈ Set.uIcc (x - δ) Real.pi →
      Complex.exp (u + y * Complex.I) ∉ star S := by
    intro y hy hws
    have hyi : y ∈ Set.Icc (x - δ) Real.pi := by
      have hu : Set.uIcc (x - δ) Real.pi = Set.Icc (x - δ) Real.pi :=
        Set.uIcc_of_le (le_of_lt hcd)
      simpa [hu] using hy
    have hyl : -Real.pi < y := lt_of_lt_of_le hcl' hyi.1
    have hargy : Complex.arg (Complex.exp (u + y * Complex.I)) = y :=
      Submission.StarGeom.arg_exp_add_mul_I hyl hyi.2
    have hexp0 : Complex.exp (u + y * Complex.I) ≠ 0 := Complex.exp_ne_zero _
    rcases hws with ⟨z, hz, hseg⟩
    rcases hseg with h2 | h4
    · have harg2 : Complex.arg (z ^ 2) = y := by
        calc
          Complex.arg (z ^ 2) = Complex.arg (Complex.exp (u + y * Complex.I)) :=
            (Submission.StarGeom.arg_eq_of_mem_segment_zero_ne_zero h2 hexp0).symm
          _ = y := hargy
      have hyD : y ∈ dirSet S := by
        simpa [harg2] using arg_sq_mem_dirSet hz
      have hseam_y : y ≤ x + δ := le_trans hyi.2 (le_of_lt hseam')
      have hyx : y = x := hsepi y hyD ⟨hyi.1, hseam_y⟩
      have hargx : Complex.arg (z ^ 2) = x := by rw [harg2, hyx]
      have hshortz : ‖z ^ 2‖ < Real.exp u :=
        hshort (z ^ 2) (spikeEndpoints_mem_sq S hz) hargx
      have hXn : ‖Complex.exp (u + y * Complex.I)‖ = Real.exp u := by
        rw [Complex.norm_exp]
        simp
      have hseg_le : ‖Complex.exp (u + y * Complex.I)‖ ≤ ‖z ^ 2‖ :=
        norm_le_norm_of_mem_segment_zero (z ^ 2) (Complex.exp (u + y * Complex.I)) h2
      linarith
    · have harg4 : Complex.arg (z ^ 4) = y := by
        calc
          Complex.arg (z ^ 4) = Complex.arg (Complex.exp (u + y * Complex.I)) :=
            (Submission.StarGeom.arg_eq_of_mem_segment_zero_ne_zero h4 hexp0).symm
          _ = y := hargy
      have hyD : y ∈ dirSet S := by
        simpa [harg4] using arg_pow4_mem_dirSet hz
      have hseam_y : y ≤ x + δ := le_trans hyi.2 (le_of_lt hseam')
      have hyx : y = x := hsepi y hyD ⟨hyi.1, hseam_y⟩
      have hargx : Complex.arg (z ^ 4) = x := by rw [harg4, hyx]
      have hshortz : ‖z ^ 4‖ < Real.exp u :=
        hshort (z ^ 4) (spikeEndpoints_mem_pow4 S hz) hargx
      have hXn : ‖Complex.exp (u + y * Complex.I)‖ = Real.exp u := by
        rw [Complex.norm_exp]
        simp
      have hseg_le : ‖Complex.exp (u + y * Complex.I)‖ ≤ ‖z ^ 4‖ :=
        norm_le_norm_of_mem_segment_zero (z ^ 4) (Complex.exp (u + y * Complex.I)) h4
      linarith
  simpa [x] using (intervalIntegrable_pull_arc S hh u (c := x - δ) (d := Real.pi) hfree)

/-- u-arc over the upper seam piece.  Points with `y ∈ (π, x+δ)` have
argument `y − 2π ∈ (−π, x+δ−2π)`; the wrap bound `hwrap0` keeps all
directions above that range, and the endpoint `y = π` (argument `π`) is
star-free because the `π`-spikes are short (`hshortπ`). -/
theorem seam_arcU_2 (S : Finset ℂ) (hS0 : ∀ z ∈ S, z ≠ 0)
    {h : ℂ → ℂ} (hh : DifferentiableOn ℂ h (Submission.XTransfer.star S)ᶜ)
    (δ u : ℝ) (hδ : 0 < δ) (hδle : δ ≤ Real.pi)
    (i : Fin (dirList S).length) (hlast : i.val + 1 = (dirList S).length)
    (hwrap0 : 2 * Real.pi + (dirList S).get ⟨0, by
        have h0 : 0 < (dirList S).length := by
          have : i.val < (dirList S).length := i.isLt
          omega
        exact h0⟩ - (dirList S).get i > 2 * δ)
    (hshortπ : ∀ w ∈ spikeEndpoints S,
      Complex.arg w = Real.pi → ‖w‖ < Real.exp u) :
    IntervalIntegrable (fun y : ℝ =>
      Submission.E2bCore.pull h (u + y * Complex.I)) volume
        Real.pi ((dirList S).get i + δ) := by
  classical
  let x : ℝ := (dirList S).get i
  have hx_dir : x ∈ dirSet S := by
    have hm : (dirList S).get i ∈ dirList S := List.get_mem (dirList S) i
    exact (dirList_mem_iff S x).mp (by simpa [x] using hm)
  have hxb := dirSet_mem_bounds S hx_dir
  have hx_gt_neg_pi : -Real.pi < x := hxb.1
  have hxle_pi : x ≤ Real.pi := hxb.2
  have hlen0 : 0 < (dirList S).length := by
    have : i.val < (dirList S).length := i.isLt
    omega
  let x0 : ℝ := (dirList S).get ⟨0, hlen0⟩
  have hwrap0' : 2 * Real.pi + x0 - x > 2 * δ := by
    have hw : (dirList S).get ⟨0, by
        have h0 : 0 < (dirList S).length := by
          have : i.val < (dirList S).length := i.isLt
          omega
        exact h0⟩ = (dirList S).get ⟨0, hlen0⟩ := by
      exact congrArg (fun e : Fin (dirList S).length => (dirList S).get e) (Fin.ext rfl)
    dsimp [x0, x]
    simpa [hw] using hwrap0
  have hx0_lt_shift : x + δ - 2 * Real.pi < x0 := by linarith [hwrap0', hδ]
  have hxdp_le2pi : x + δ ≤ 2 * Real.pi := by linarith [hxle_pi, hδle]
  have hxdp_gt_neg_pi : -Real.pi < x + δ := by linarith [hx_gt_neg_pi, hδ]
  have hfree : ∀ y : ℝ, y ∈ Set.uIcc Real.pi (x + δ) →
      Complex.exp (u + y * Complex.I) ∉ star S := by
    intro y hy hws
    by_cases hpi_le : Real.pi ≤ x + δ
    · have hyi : y ∈ Set.Icc Real.pi (x + δ) := by
        have hu : Set.uIcc Real.pi (x + δ) = Set.Icc Real.pi (x + δ) := Set.uIcc_of_le hpi_le
        simpa [hu] using hy
      have hy1 : Real.pi ≤ y := hyi.1
      have hy2 : y ≤ x + δ := hyi.2
      have hy2le : y ≤ 2 * Real.pi := le_trans hy2 hxdp_le2pi
      by_cases hypi : y = Real.pi
      · have hws' : Complex.exp (u + Real.pi * Complex.I) ∈ star S := by
          simpa [hypi] using hws
        exact exp_pi_arc_not_mem_star (S := S) (u := u) hshortπ hws'
      · have hygt : Real.pi < y := lt_of_le_of_ne hy1 (fun h => hypi h.symm)
        have hargy : Complex.arg (Complex.exp (u + y * Complex.I)) = y - 2 * Real.pi := by
          rw [Complex.arg_exp]
          have htoIoc : toIocMod Real.two_pi_pos (-Real.pi) y = y - 2 * Real.pi := by
            rw [toIocMod_eq_iff]
            constructor
            · constructor
              · linarith
              · have h : -Real.pi + 2 * Real.pi = Real.pi := by ring
                rw [h]
                linarith [hy2le, Real.pi_pos]
            · refine ⟨1, ?_⟩
              rw [one_zsmul]
              ring
          simpa using htoIoc
        have hexp0 : Complex.exp (u + y * Complex.I) ≠ 0 := Complex.exp_ne_zero _
        rcases hws with ⟨z, hz, hseg⟩
        rcases hseg with h2 | h4
        · have harg2 : Complex.arg (z ^ 2) = y - 2 * Real.pi := by
            calc
              Complex.arg (z ^ 2) = Complex.arg (Complex.exp (u + y * Complex.I)) :=
                (Submission.StarGeom.arg_eq_of_mem_segment_zero_ne_zero h2 hexp0).symm
              _ = y - 2 * Real.pi := hargy
          have hθ : y - 2 * Real.pi ∈ dirSet S := by
            simpa [harg2] using arg_sq_mem_dirSet hz
          have hmin : x0 ≤ y - 2 * Real.pi := by
            simpa [x0] using Submission.SeamCells.dirList_head_le S hlen0 hθ
          have hsmall : y - 2 * Real.pi < x0 := by linarith [hx0_lt_shift, hy2]
          linarith
        · have harg4 : Complex.arg (z ^ 4) = y - 2 * Real.pi := by
            calc
              Complex.arg (z ^ 4) = Complex.arg (Complex.exp (u + y * Complex.I)) :=
                (Submission.StarGeom.arg_eq_of_mem_segment_zero_ne_zero h4 hexp0).symm
              _ = y - 2 * Real.pi := hargy
          have hθ : y - 2 * Real.pi ∈ dirSet S := by
            simpa [harg4] using arg_pow4_mem_dirSet hz
          have hmin : x0 ≤ y - 2 * Real.pi := by
            simpa [x0] using Submission.SeamCells.dirList_head_le S hlen0 hθ
          have hsmall : y - 2 * Real.pi < x0 := by linarith [hx0_lt_shift, hy2]
          linarith
    · have hxdp : x + δ < Real.pi := lt_of_not_ge hpi_le
      have hyi : y ∈ Set.Icc (x + δ) Real.pi := by
        have hu : Set.uIcc Real.pi (x + δ) = Set.Icc (x + δ) Real.pi := by
          rw [Set.uIcc_comm]
          exact Set.uIcc_of_le (le_of_lt hxdp)
        simpa [hu] using hy
      have hy1 : x + δ ≤ y := hyi.1
      have hy2 : y ≤ Real.pi := hyi.2
      by_cases hypi : y = Real.pi
      · have hws' : Complex.exp (u + Real.pi * Complex.I) ∈ star S := by
          simpa [hypi] using hws
        exact exp_pi_arc_not_mem_star (S := S) (u := u) hshortπ hws'
      · have hyl : -Real.pi < y := by
          linarith [hxdp_gt_neg_pi, hy1]
        have hargy : Complex.arg (Complex.exp (u + y * Complex.I)) = y :=
          Submission.StarGeom.arg_exp_add_mul_I hyl hy2
        have hexp0 : Complex.exp (u + y * Complex.I) ≠ 0 := Complex.exp_ne_zero _
        rcases hws with ⟨z, hz, hseg⟩
        rcases hseg with h2 | h4
        · have harg2 : Complex.arg (z ^ 2) = y := by
            calc
              Complex.arg (z ^ 2) = Complex.arg (Complex.exp (u + y * Complex.I)) :=
                (Submission.StarGeom.arg_eq_of_mem_segment_zero_ne_zero h2 hexp0).symm
              _ = y := hargy
          have hθ : y ∈ dirSet S := by
            simpa [harg2] using arg_sq_mem_dirSet hz
          have hle_yx : y ≤ x := by
            simpa [x] using Submission.SeamCells.dirList_last_ge S i hlast hθ
          have hgt : x < y := by linarith [hy1, hδ]
          linarith
        · have harg4 : Complex.arg (z ^ 4) = y := by
            calc
              Complex.arg (z ^ 4) = Complex.arg (Complex.exp (u + y * Complex.I)) :=
                (Submission.StarGeom.arg_eq_of_mem_segment_zero_ne_zero h4 hexp0).symm
              _ = y := hargy
          have hθ : y ∈ dirSet S := by
            simpa [harg4] using arg_pow4_mem_dirSet hz
          have hle_yx : y ≤ x := by
            simpa [x] using Submission.SeamCells.dirList_last_ge S i hlast hθ
          have hgt : x < y := by linarith [hy1, hδ]
          linarith
  simpa [x] using (intervalIntegrable_pull_arc S hh u (c := Real.pi) (d := x + δ) hfree)

end Submission.SeamIntegrability

end
