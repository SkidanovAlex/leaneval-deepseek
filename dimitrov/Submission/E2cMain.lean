import Mathlib
import Submission.E2c
import Submission.E2cParam
import Submission.E2cGeom
import Submission.DStar
import Submission.BranchW
import Submission.Rays
import Submission.XTransfer
import Submission.PolyMoment
import Submission.E0Complex
import Submission.HankelDecay
import Submission.PolyaCore
import Submission.Dictionary
import Submission.Conjugates
import Submission.Minpoly
import Submission.Gnorm
import Submission.EngineAlg
import Submission.RadialFree
import Submission.SeamIntegrability
import Submission.TipCell
import Submission.StarGeom
import Submission.DirCycle
import Submission.DirSet
import Submission.E2bCore
import Submission.Fold

/-!
# E2c ASSEMBLY: `HedgehogBound (conjugateValues α)` ⟹ `EngineAlg.HankelInput α hα`

MAIN THEOREM of this file (E2c, mechanical wiring; E1 supplies the
`HedgehogBound` hypothesis from the Dubinin content):

    hankelDet_zero_of_hedgehogBound (α) (hα) (hα0) (hhb : HedgehogBound (conjugateValues α))
        : EngineAlg.HankelInput α hα

## DATA (all verified elsewhere)

Unpack in this order (see the respective module docstrings for details):

* `S := conjugateValues α : Finset ℂ` (`Submission.Conjugates`);
* `P := minpoly ℤ α : ℤ[X]` (`Submission.Minpoly`);
* `star S := Submission.XTransfer.star S = ⋃_{z∈S} ([0,z²] ∪ [0,z⁴])`;
* spike geometry: `spikeEndpoints S`, `dirSet S := (spikeEndpoints S).image Complex.arg`,
  `dirList S := (dirSet S).sort`, `dirX S hlen0 j := (dirList S).get ⟨j, …⟩`
  (`Submission.DirSet`, `Submission.DirCycle`; all verified);
* `hhb` unpacks to `⟨ε, hε, C, hC, θ, hθ0, hθ1, hp⟩` with
  `hp j : ∃ p, p.Monic ∧ p.natDegree = j ∧ ∀ X ∈ FatStar S ε, ‖p.eval X‖ ≤ C * θ ^ j`
  (`Submission.PolyaCore.HedgehogBound`, `FatStar S ε := {X | ∃Y∈star S, ‖X−Y‖≤ε}`);
* `Submission.BranchW.exists_holomorphic_branch α hα hα0` gives
  `⟨a, ha0, haConv, f, hfdiff, hfsq, hf0, htay⟩` where
  `a : ℕ→ℤ`, `a 0 = 1`, conv-square of `a` = coeffs of `Gpoly P`,
  `f` DifferentiableOn `cutPlane (rootFinset S)`, `f 0 = 1`,
  `htay : ∀ k, taylorCoeff f k = (a k : ℂ)`  (`Submission.SqrtTaylor.taylorCoeff`);
* `Submission.Rays.exists_ball_subset_cutPlane (rootFinset S) (rootFinset_ne_zero hS0)`
  gives `⟨ρ₀, hρ₀pos, hball⟩` with `Metric.ball 0 ρ₀ ⊆ cutPlane (rootFinset S)`;
* `g : ℂ → ℂ := fun X => if X = 0 then 0 else f (X⁻¹)` (exactly as in
  `Submission.BranchX.exists_laurent_branch`); one must re-prove for this `g`
  (following BranchX's internal proof, ~15 lines): `hgdiff : DifferentiableOn ℂ g (star S)ᶜ`
  (via `XTransfer.holomorphicOn_star_compl_of_holomorphicOn_cutPlane S hSne hfdiff`),
  and `hgsq : ∀ X ∈ (star S)ᶜ, g X ^ 2 = (Gpoly P).eval₂ (algebraMap ℤ ℂ) (X⁻¹)`;
* `S.Nonempty` (there is an embedding), `hS0 : ∀ z ∈ S, z ≠ 0`
  (`Submission.Dictionary.zero_not_mem_conjugateValues`), `hSne`,
  `hne : (dirSet S).Nonempty` and `hlen0 : 0 < (dirList S).length`
  (pattern: `E1Content.dirSet_conjugateValues_nonempty`, but re-derive here —
  do NOT import Submission.E1Content/Dubinin/SS1/Step3, they carry unfinished proofs);
* `hw0 : ∀ w ∈ spikeEndpoints S, w ≠ 0` (from `hS0` + `pow_ne_zero`);
* parameters (all verified in `Submission.E2cParam`, statements exact there):
  `u := uOf S hlen0 ε`, `A := AOf ε`, `R0 := (ρ₀)⁻¹`, `B := BOf S ε R0`,
  `δ` from `exists_delta_geo S hne hε hR0` (`hR0 : 0 < R0` from `hρ₀pos`).
  Verified consequences to use:
  `hδpos`, `δ ≤ 1` (hence `δ ≤ π`), `hδx0 : δ < (dirList S).get ⟨0,hlen0⟩ + π`,
  `hsep`, wrap-gap `> 2δ`, `2 * radBound S ε * δ ≤ ε/2` (`huδ_of_radBound` gives
  `2 * exp (u j) * δ ≤ ε/2` for each `j < length`),
  `exp_uOf` / `radius_pos`, `exp_uOf_sub_spikeLen_le_half` (hug),
  `short_of_uOf` (hshort: `‖w‖ < exp (u j)` for endpoints with `arg w = dirX S hlen0 j`),
  `AOf_le_uOf`, `exp_AOf_le_eps`, `exp_BOf`, `hBigB_of_BOf`, `uOf_le_BOf`,
  `R0_lt_exp_BOf`, `shortπ_last` (hshortπ), `dirX_mem_dirSet`, `dirSpikeLen_le_maxEndNorm`.

## MAIN OUTLINE (each step mechanical; do not import Step3/Dubinin/E1Content/SS*)

1. Choose `p : ℕ → ℂ[X]` from `hhb` by `Classical.choose`:
   `pmonic : ∀ j, (p j).Monic`, `pdeg : ∀ j, (p j).natDegree = j`,
   `pbd : ∀ j X, X ∈ FatStar S ε → ‖(p j).eval X‖ ≤ C * θ ^ j`.

2. (Moment-matrix = circle integral.)  For each `k ≥ 1`, `i j : Fin k`, with
   `h := fun X => g X * ((p i.val).eval X) * ((p j.val).eval X) * X⁻¹`, `hh :
   DifferentiableOn ℂ h (star S)ᶜ` (product of `hgdiff`, polynomials, `X ↦ X⁻¹`
   holomorphic off `0`, and `0 ∈ star S` via `XTransfer.zero_mem_star hSne`), and
   `ρ := exp B`:
   `cMomentMatrix k (fun n => (a n : ℂ)) (fun t : Fin k => p t.val) i j =
        (2*π*I)⁻¹ * ∮ z in C(0, ρ), g z * (p i.val).eval z * (p j.val).eval z * z⁻¹`
   by `PolyMoment.cMomentMatrix_eq_circleIntegral` with
   `hf := hfdiff.mono hball` (DifferentiableOn on `ball 0 ρ₀`), `ha := htay`,
   `hg` (the pointwise `g X = f (X⁻¹)`), `hρpos : 0 < exp B`,
   `hρ : ρ⁻¹ < ρ₀` from `R0_lt_exp_BOf` (R0 := ρ₀⁻¹).

3. (Deformation.)  Apply `DStar.deformation_star S hS0 hh A B δ u hlen0 hδ
   (le_trans hδle1 Real.pi…) hsep hwrap0 hδx0 hBigB hshort hshortπ hub` where
   `hsep`/`hwrap0` are the pieces of `exists_delta_geo` (translated to
   `dirX S hlen0 j` via `dirX_of_lt S hlen0 hj` and the `dirList_get_*`
   conversions), `hBigB := hBigB_of_BOf S hε hR0`, `hshort := short_of_uOf S
   hlen0 hε` (rw `dirX_of_lt`), `hshortπ := shortπ_last S hlen0 hε`, `hub :=
   uOf_le_BOf S hlen0 hε hR0`.  Result:
   `∮ z in C(0, exp B), h z = Σ_j I•arcInt (pull h) (u j) (dirX j − δ) (dirX j + δ)
     + Σ_j I•arcInt (pull h) A (dirX j + δ) (dirX (j+1) − δ)
     + Σ_j radInt (pull h) A (u j) (dirX j − δ)
     − Σ_j radInt (pull h) A (u j) (dirX j + δ)`
   (all sums over `j ∈ Finset.range (dirList S).length`).
   NB `dirX S hlen0 (j+1)` for `j+1 = length` is the cyclic value
   `dirX S hlen0 0 + 2π` (`dirX_length`); keep `j < length`.

4. (Pointwise bound on the deformed pieces.)  For `X := exp (t + i·θ)` on any
   RHS piece: `‖pull h (t + i·θ)‖ = ‖g X‖·‖(p i.val).eval X‖·‖(p j.val).eval X‖`
   (prove a helper: `pull_mul_inv_norm`), where
   * `‖g X‖ ≤ M := (1 + (house α)^4 / exp A) ^ S.card` via
     `Gnorm.norm_g_le α hα hα0 g hgsq hX` provided `hX : X ∈ (star S)ᶜ`
     and `exp A ≤ ‖X‖` (true on all pieces: `A ≤ t`);
   * `‖(p t').eval X‖ ≤ C·θ^t'` whenever `X ∈ FatStar S ε`
     (`E2cGeom.fatStar_of_rot_point` for window/radial points, at radius
     `r ∈ [0, exp (u j)]` with `|Δ| ≤ δ` — hypotheses `hug`, `huδ`, `hw0`,
     `dirX_mem_dirSet`; `E2cGeom.fatStar_gap_point` for gap points, radius
     `exp A ≤ ε` via `exp_AOf_le_eps`);
   * each RHS point is in the complement `(star S)ᶜ`:
     - radial sides (θ = dirX j ± δ): `RadialFree.exp_ray_not_mem_star_of_not_dir`
       with the `no_dir_*` facts from `DStar` (`no_dir_left_edge S hlen0 hδ hsep
       hδx0 (j := j) hjS`, `no_dir_right_edge`, `no_dir_right_edge_seam` — the
       `hradR`/`hno` pattern is proved in the DStar proof body, reuse it);
     - gap arcs (θ between consecutive directions, incl. the wrap gap):
       `exp_ray_not_mem_star_of_not_dir` + no-direction strictly between
       (use `DirCycle.no_dir_between_get`, the wrap-gap analysis from
       `SpineGaps.gap_cell_between_dirList`/`E2bParam.wrapGap_dirList_eq`:
       for the wrap gap, points with `θ > π` wrap below `x_0 − δ`);
     - window cap arcs (θ ∈ (dirX j − δ, dirX j + δ), radius `exp (u j)`):
       split by `by_cases` on whether `arg X` (= `toIocMod 2π (−π) θ`) lies in
       `dirSet S`; if not, `exp_ray_not_mem_star_of_not_dir`; if yes, it equals
       `dirX S hlen0 j` (only direction in the window, cyclically — use `hsep`,
       `hδx0`, the wrap gap, `hshort`), then `SeamIntegrability.
       exp_ray_not_mem_star_of_short` with `hshort j hjS` applied to the point
       (norms `‖X‖ = exp (u j)`).  (Alternative, may be simpler: use the
       `StarGeom.expRect_avoids_star`-family lemmas on w-rectangles, splitting
       seam windows at `π` as in `DStar`.)
   Net per-piece bound: `‖piece integral‖ ≤ (piece length)·M·C²·θ^(i.val+j.val)`.

5. (Total bound.)  `‖RHS‖ ≤ K₀·M·C²·θ^(i.val+j.val)` where
   `K₀ := Σ j < s, (2δ + ((dirX (j+1) − δ) − (dirX j + δ)) + 2·(u j − A))`
   (s := (dirList S).length; use `norm_sum_le`, the four summand families,
   `E2c.arcInt_norm_le`/`radInt_norm_le`-style bounds, `abs_sub_of_window`,
   `|d−c|` computations).  Hence with `K := K₀·M·C²` (positive, independent of
   `k,i,j`):
   `‖cMomentMatrix k (fun n => (a n : ℂ)) (fun t : Fin k => p t.val) i j‖ ≤ K·θ^(i.val+j.val)`
   for all `k ≥ 1`, `i j : Fin k` (factor `(2π)⁻¹ ≤ 1` — drop it or absorb it
   into `K`; `‖(2*π*I)⁻¹‖ = (2π)⁻¹`).

6. (Hankel decay.)  Apply
   `HankelDecay.hankelDet_eventually_zero_of_moment_bound a p pmonic pdeg hK hθ0 hθ1 hmom`
   with `hmom` from step 5 to obtain `⟨N, hN⟩`.

7. Output `⟨a, ha0, haConv, N, hN⟩ : EngineAlg.HankelInput α hα` (which is by
   definition exactly `∃ a, a 0 = 1 ∧ ConvSq P a ∧ ∃ K, ∀ k ≥ K, hankelDet a k = 0`).

## INVARIANTS / WARNINGS

* `dirX S hlen0 j` requires `j < (dirList S).length` for the `Fin` proof; the
  sums are over `j ∈ Finset.range s` and `dirX S hlen0 (j+1)` needs a
  positivity proof for `j+1` only when `j+1 < s` (use `dirX_of_lt`); for
  `j+1 = s` use the cyclic identity `dirX S hlen0 s = dirX S hlen0 0 + 2π`
  (`dirX_length S hlen0`), and prove a small wrapper `dirX_succ` doing the
  `by_cases j+1 < s / = s` split returning the right value.
* `intervalIntegral` over `a..b` is over the unoriented interval; the bound
  helpers `E2c.arcInt_norm_le`/`radInt_norm_le` take the pointwise bound on
  `y ∈ Ι c d` (uIoc) — read their statements in `Submission/E2c.lean` and
  match the interval endpoints; they require no integrability hypothesis.
* `hankelDet` is `Submission.Kronecker.hankelDet` (open in EngineAlg); the
  complex moment matrix is `Submission.E0Complex.cMomentMatrix`.
* Do NOT import any of `Submission.E1Content`, `Submission.Dubinin`,
  `Submission.SS1`, `Submission.SS2`, `Submission.SS3asm`, `Submission.SS3a`,
  `Submission.SS3core`, `Submission.Step3`, `Submission.AnalyticEngine`,
  `Submission.Engine` — they carry unfinished proofs.  Everything imported above is
  free of unfinished proofs.
-/

noncomputable section

open scoped Real Polynomial Topology BigOperators Interval
open Complex

namespace Submission.E2c

open Submission.PolyaCore
open Submission.Conjugates
open Submission.DirSet
open Submission.E2cGeom
open Submission.E2bCore

open Submission.DirCycle
open Submission.E2bAssembly
open Submission.DStar
open Submission.SepLemma
open Submission.SpineGaps
open Submission.SeamCells
open Submission.TipCell
open Submission.RadialFree
open Submission.E2bCells
open Submission.XTransfer
open scoped Complex Real Interval
open Complex

/-! # Geometric star-free lemmas for the deformed contour -/

/-- Window cap arcs at radius `e^u` over the `δ`-window of direction
`x_j := dirX S hlen0 j` avoid the hedgehog (nonseam or seam). -/
lemma window_cap_not_mem_star (S : Finset ℂ) (hS0 : ∀ z ∈ S, z ≠ 0)
    (hlen0 : 0 < (dirList S).length) {δ : ℝ} (hδ : 0 < δ) (hδle : δ ≤ Real.pi)
    (hsep : ∀ (j : ℕ) (hj : j + 1 < (dirList S).length),
      (dirList S).get ⟨j + 1, hj⟩ -
        (dirList S).get ⟨j, Nat.lt_trans (Nat.lt_succ_self j) hj⟩ > 2 * δ)
    (hδx0 : δ < (dirList S).get ⟨0, hlen0⟩ + Real.pi)
    (hwrap0 : 2 * Real.pi + (dirList S).get ⟨0, hlen0⟩ -
        (dirList S).get ⟨(dirList S).length - 1, by omega⟩ > 2 * δ)
    {u : ℝ} {j : ℕ} (hj : j < (dirList S).length)
    (hshort : ∀ w ∈ spikeEndpoints S, Complex.arg w = dirX S hlen0 j → ‖w‖ < Real.exp u) :
    ∀ y ∈ Set.Icc (dirX S hlen0 j - δ) (dirX S hlen0 j + δ),
      Complex.exp (u + y * Complex.I) ∉ star S := by
  classical
  have hxL : dirX S hlen0 j = (dirList S).get ⟨j, hj⟩ := dirX_of_lt S hlen0 hj
  have hsepi : ∀ θ ∈ dirSet S,
      θ ∈ Set.Icc ((dirList S).get ⟨j, hj⟩ - δ) ((dirList S).get ⟨j, hj⟩ + δ) →
        θ = (dirList S).get ⟨j, hj⟩ := by
    intro θ hθ hw
    exact dirList_window_separated (S := S) (δ := δ) hsep ⟨j, hj⟩ hθ hw
  have hcl : -Real.pi < (dirList S).get ⟨j, hj⟩ - δ := window_left_gt_npi S hlen0 hδx0 hj
  have hshortL : ∀ w ∈ spikeEndpoints S,
      Complex.arg w = (dirList S).get ⟨j, hj⟩ → ‖w‖ < Real.exp u := by
    simpa [hxL] using hshort
  have htip_gen : ∀ {c d : ℝ}, -Real.pi < c → d ≤ Real.pi →
      (∀ θ ∈ dirSet S, θ ∈ Set.Icc c d → θ = (dirList S).get ⟨j, hj⟩) →
      ∀ z ∈ S,
        (Complex.arg (z ^ 2) ∈ Set.Icc c d → ‖z ^ 2‖ < Real.exp u) ∧
        (Complex.arg (z ^ 4) ∈ Set.Icc c d → ‖z ^ 4‖ < Real.exp u) := by
    intro c d hcl0 hdu0 hsep0 z hz
    constructor
    · intro harg
      have hargD : Complex.arg (z ^ 2) ∈ dirSet S := arg_sq_mem_dirSet hz
      have heq : Complex.arg (z ^ 2) = (dirList S).get ⟨j, hj⟩ := hsep0 _ hargD harg
      exact hshortL (z ^ 2) (spikeEndpoints_mem_sq S hz) heq
    · intro harg
      have hargD : Complex.arg (z ^ 4) ∈ dirSet S := arg_pow4_mem_dirSet hz
      have heq : Complex.arg (z ^ 4) = (dirList S).get ⟨j, hj⟩ := hsep0 _ hargD harg
      exact hshortL (z ^ 4) (spikeEndpoints_mem_pow4 S hz) heq
  intro y hy
  by_cases hdu : (dirList S).get ⟨j, hj⟩ + δ ≤ Real.pi
  · have hc_d : (dirList S).get ⟨j, hj⟩ - δ < (dirList S).get ⟨j, hj⟩ + δ := by linarith
    have htip_win : ∀ z ∈ S,
        (Complex.arg (z ^ 2) ∈ Set.Icc ((dirList S).get ⟨j, hj⟩ - δ) ((dirList S).get ⟨j, hj⟩ + δ) →
            ‖z ^ 2‖ < Real.exp u) ∧
        (Complex.arg (z ^ 4) ∈ Set.Icc ((dirList S).get ⟨j, hj⟩ - δ) ((dirList S).get ⟨j, hj⟩ + δ) →
            ‖z ^ 4‖ < Real.exp u) := by
      exact htip_gen (c := (dirList S).get ⟨j, hj⟩ - δ) (d := (dirList S).get ⟨j, hj⟩ + δ) hcl hdu hsepi
    have hw : (u : ℂ) + (y : ℂ) * Complex.I ∈
        (Set.uIcc u u : Set ℝ) ×ℂ (Set.uIcc ((dirList S).get ⟨j, hj⟩ - δ)
          ((dirList S).get ⟨j, hj⟩ + δ)) := by
      rw [Complex.mem_reProdIm]
      constructor
      · simp
      · have huIoc : Set.uIcc ((dirList S).get ⟨j, hj⟩ - δ) ((dirList S).get ⟨j, hj⟩ + δ) =
            Set.Icc ((dirList S).get ⟨j, hj⟩ - δ) ((dirList S).get ⟨j, hj⟩ + δ) :=
          Set.uIcc_of_le (le_of_lt hc_d)
        rw [huIoc]
        simpa [hxL] using hy
    have hfree := expRect_avoids_star_tip (S := S) hS0
      (xmin := u) (xmax := u) (ymin := (dirList S).get ⟨j, hj⟩ - δ)
      (ymax := (dirList S).get ⟨j, hj⟩ + δ)
      (by rfl) hc_d hcl hdu htip_win
    have hne : Complex.exp ((u : ℂ) + (y : ℂ) * Complex.I) ∉ star S := hfree _ hw
    simpa using hne
  · have hseam : Real.pi < (dirList S).get ⟨j, hj⟩ + δ := by linarith
    have hlt_not : ¬ j + 1 < (dirList S).length := by
      intro hlt
      have hdu0 := window_right_le_pi S hδ hsep hj hlt
      linarith
    have hlast : j + 1 = (dirList S).length := by omega
    have hwrapX : 2 * Real.pi + (dirList S).get ⟨0, hlen0⟩ -
        (dirList S).get ⟨j, hj⟩ > 2 * δ := by
      rw [← dirList_get_j_last S hj hlast] at hwrap0
      exact hwrap0
    by_cases hypi : y ≤ Real.pi
    · have hcd : (dirList S).get ⟨j, hj⟩ - δ < Real.pi := by
        have hx := (dirList_get_mem_Ioc S ⟨j, hj⟩).2
        linarith
      have htip_low : ∀ z ∈ S,
          (Complex.arg (z ^ 2) ∈ Set.Icc ((dirList S).get ⟨j, hj⟩ - δ) Real.pi → ‖z ^ 2‖ < Real.exp u) ∧
          (Complex.arg (z ^ 4) ∈ Set.Icc ((dirList S).get ⟨j, hj⟩ - δ) Real.pi → ‖z ^ 4‖ < Real.exp u) := by
        refine htip_gen (c := (dirList S).get ⟨j, hj⟩ - δ) (d := Real.pi) hcl (le_rfl) ?_
        intro θ hθ hθi
        have hθw : θ ∈ Set.Icc ((dirList S).get ⟨j, hj⟩ - δ) ((dirList S).get ⟨j, hj⟩ + δ) := by
          constructor
          · exact hθi.1
          · linarith [hθi.2]
        exact hsepi θ hθ hθw
      have hw : (u : ℂ) + (y : ℂ) * Complex.I ∈
          (Set.uIcc u u : Set ℝ) ×ℂ (Set.uIcc ((dirList S).get ⟨j, hj⟩ - δ) Real.pi) := by
        rw [Complex.mem_reProdIm]
        constructor
        · simp
        · have hyL : y ∈ Set.Icc ((dirList S).get ⟨j, hj⟩ - δ) ((dirList S).get ⟨j, hj⟩ + δ) := by
            simpa [hxL] using hy
          have huIoc : Set.uIcc ((dirList S).get ⟨j, hj⟩ - δ) Real.pi =
              Set.Icc ((dirList S).get ⟨j, hj⟩ - δ) Real.pi := Set.uIcc_of_le (le_of_lt hcd)
          rw [huIoc]
          constructor
          · simpa using hyL.1
          · simpa using hypi
      have hfree := expRect_avoids_star_tip (S := S) hS0
        (xmin := u) (xmax := u) (ymin := (dirList S).get ⟨j, hj⟩ - δ) (ymax := Real.pi)
        (by rfl) hcd hcl (le_rfl) htip_low
      have hne : Complex.exp ((u : ℂ) + (y : ℂ) * Complex.I) ∉ star S := hfree _ hw
      simpa using hne
    · have hpi_lt : Real.pi < y := lt_of_not_ge hypi
      have hx_le_pi : (dirList S).get ⟨j, hj⟩ ≤ Real.pi := (dirList_get_mem_Ioc S ⟨j, hj⟩).2
      have hy_le : y ≤ (dirList S).get ⟨j, hj⟩ + δ := by simpa [hxL] using hy.2
      have hT : toIocMod Real.two_pi_pos (-Real.pi) y = y - 2 * Real.pi := by
        rw [toIocMod_eq_iff]
        constructor
        · constructor
          · linarith [hpi_lt]
          · have h : -Real.pi + 2 * Real.pi = Real.pi := by ring
            rw [h]
            have h2pi : (dirList S).get ⟨j, hj⟩ + δ ≤ 3 * Real.pi := by linarith [hx_le_pi, hδle, Real.pi_pos]
            linarith
        · refine ⟨1, ?_⟩
          rw [one_zsmul]
          ring
      have hno : ∀ d ∈ dirSet S, d ≠ toIocMod Real.two_pi_pos (-Real.pi) y := by
        intro d hd hEq
        rw [hT] at hEq
        have hge : (dirList S).get ⟨0, hlen0⟩ ≤ d := dirList_head_le S hlen0 hd
        have hsmall : y - 2 * Real.pi < (dirList S).get ⟨0, hlen0⟩ := by
          have h1 : (dirList S).get ⟨j, hj⟩ + δ - 2 * Real.pi < (dirList S).get ⟨0, hlen0⟩ := by
            linarith [hwrapX, hδ]
          linarith [hy_le]
        linarith
      have hne := exp_ray_not_mem_star_of_not_dir (S := S) (θ := y) hno u
      simpa using hne

/-- The radial ray at the left window edge `x_j − δ` avoids the hedgehog. -/
lemma radial_left_not_mem_star (S : Finset ℂ)
    (hlen0 : 0 < (dirList S).length) {δ : ℝ} (hδ : 0 < δ)
    (hsep : ∀ (j : ℕ) (hj : j + 1 < (dirList S).length),
      (dirList S).get ⟨j + 1, hj⟩ -
        (dirList S).get ⟨j, Nat.lt_trans (Nat.lt_succ_self j) hj⟩ > 2 * δ)
    (hδx0 : δ < (dirList S).get ⟨0, hlen0⟩ + Real.pi)
    {j : ℕ} (hj : j < (dirList S).length) :
    ∀ t : ℝ, Complex.exp (t + (dirX S hlen0 j - δ) * Complex.I) ∉ star S := by
  intro t
  simpa using (exp_ray_not_mem_star_of_not_dir (S := S) (θ := dirX S hlen0 j - δ)
    (no_dir_left_edge S hlen0 hδ hsep hδx0 (j := j) hj) t)

/-- The radial ray at the right window edge `x_j + δ` avoids the hedgehog
(nonseam or seam dispatch). -/
lemma radial_right_not_mem_star (S : Finset ℂ)
    (hlen0 : 0 < (dirList S).length) {δ : ℝ} (hδ : 0 < δ) (hδle : δ ≤ Real.pi)
    (hsep : ∀ (j : ℕ) (hj : j + 1 < (dirList S).length),
      (dirList S).get ⟨j + 1, hj⟩ -
        (dirList S).get ⟨j, Nat.lt_trans (Nat.lt_succ_self j) hj⟩ > 2 * δ)
    (hδx0 : δ < (dirList S).get ⟨0, hlen0⟩ + Real.pi)
    (hwrap0 : 2 * Real.pi + (dirList S).get ⟨0, hlen0⟩ -
        (dirList S).get ⟨(dirList S).length - 1, by omega⟩ > 2 * δ)
    {j : ℕ} (hj : j < (dirList S).length) :
    ∀ t : ℝ, Complex.exp (t + (dirX S hlen0 j + δ) * Complex.I) ∉ star S := by
  intro t
  by_cases hlt : j + 1 < (dirList S).length
  · simpa using (exp_ray_not_mem_star_of_not_dir (S := S) (θ := dirX S hlen0 j + δ)
      (no_dir_right_edge S hlen0 hδ hsep (j := j) hj (window_right_le_pi S hδ hsep hj hlt)) t)
  · have hlast : j + 1 = (dirList S).length := by omega
    by_cases hdu0 : (dirList S).get ⟨j, hj⟩ + δ ≤ Real.pi
    · simpa using (exp_ray_not_mem_star_of_not_dir (S := S) (θ := dirX S hlen0 j + δ)
        (no_dir_right_edge S hlen0 hδ hsep (j := j) hj hdu0) t)
    · have hseam0 : Real.pi < (dirList S).get ⟨j, hj⟩ + δ := by linarith
      simpa using (exp_ray_not_mem_star_of_not_dir (S := S) (θ := dirX S hlen0 j + δ)
        (no_dir_right_edge_seam S hlen0 hδ hδle hwrap0 hδx0 (j := j) hj hlast hseam0) t)

/-- Interior gap arcs (between consecutive directions): every point with
angle in `[x_j + δ, x_{j+1} − δ]` is direction-free, so its whole ray
avoids the hedgehog. -/
lemma gap_arc_interior_not_mem_star (S : Finset ℂ)
    (hlen0 : 0 < (dirList S).length) {δ : ℝ} (hδ : 0 < δ)
    {j : ℕ} (hj : j < (dirList S).length) (hlt : j + 1 < (dirList S).length) :
    ∀ y ∈ Set.Icc (dirX S hlen0 j + δ) (dirX S hlen0 (j + 1) - δ),
      ∀ r : ℝ, Complex.exp (r + y * Complex.I) ∉ star S := by
  classical
  intro y hy r
  have hxL : dirX S hlen0 j = (dirList S).get ⟨j, hj⟩ := dirX_of_lt S hlen0 hj
  have hxpL : dirX S hlen0 (j + 1) = (dirList S).get ⟨j + 1, hlt⟩ := dirX_of_lt S hlen0 hlt
  have hxj : (dirList S).get ⟨j, hj⟩ < y := by
    have hy1 : dirX S hlen0 j + δ ≤ y := hy.1
    linarith [hxL, hδ]
  have hyjp : y < (dirList S).get ⟨j + 1, hlt⟩ := by
    have hy2 : y ≤ dirX S hlen0 (j + 1) - δ := hy.2
    linarith [hxpL, hδ]
  have hyl : -Real.pi < y := by
    have hxI := dirList_get_mem_Ioc S ⟨j, hj⟩
    linarith [hxj, hxI.1]
  have hyu : y ≤ Real.pi := by
    have hxI := dirList_get_mem_Ioc S ⟨j + 1, hlt⟩
    linarith [hyjp, hxI.2]
  have hT : toIocMod Real.two_pi_pos (-Real.pi) y = y := by
    exact (toIocMod_eq_self Real.two_pi_pos (a := -Real.pi) (b := y)).2
      (show y ∈ Set.Ioc (-Real.pi) (-Real.pi + 2 * Real.pi) from ⟨hyl, by linarith⟩)
  have hno : ∀ d ∈ dirSet S, d ≠ toIocMod Real.two_pi_pos (-Real.pi) y := by
    intro d hd hEq
    rw [hT] at hEq
    have hmid : (dirList S).get ⟨j, hj⟩ < d ∧ d < (dirList S).get ⟨j + 1, hlt⟩ := by
      rw [hEq]
      exact ⟨hxj, hyjp⟩
    exact no_dir_between_get S ⟨j, hj⟩ hlt d hd hmid
  simpa using (exp_ray_not_mem_star_of_not_dir (S := S) (θ := y) hno r)

/-- The wrap gap arc (after the last direction, closing at `x_0 + 2π`):
every point with angle in `[x_j + δ, x_0 + 2π − δ]` is direction-free
(when wrapped into `(−π, π]`), so its ray avoids the hedgehog. -/
lemma gap_arc_wrap_not_mem_star (S : Finset ℂ)
    (hlen0 : 0 < (dirList S).length) {δ : ℝ} (hδ : 0 < δ)
    (hδx0 : δ < (dirList S).get ⟨0, hlen0⟩ + Real.pi)
    (hwrap0 : 2 * Real.pi + (dirList S).get ⟨0, hlen0⟩ -
        (dirList S).get ⟨(dirList S).length - 1, by omega⟩ > 2 * δ)
    {j : ℕ} (hj : j < (dirList S).length) (hlast : j + 1 = (dirList S).length) :
    ∀ y ∈ Set.Icc (dirX S hlen0 j + δ) (dirX S hlen0 (j + 1) - δ),
      ∀ r : ℝ, Complex.exp (r + y * Complex.I) ∉ star S := by
  classical
  intro y hy r
  have hxL : dirX S hlen0 j = (dirList S).get ⟨j, hj⟩ := dirX_of_lt S hlen0 hj
  have hxpL : dirX S hlen0 (j + 1) = (dirList S).get ⟨0, hlen0⟩ + 2 * Real.pi := by
    rw [hlast, dirX_length S hlen0]
  have hxj_le : dirX S hlen0 j + δ ≤ y := hy.1
  have hy_le : y ≤ dirX S hlen0 (j + 1) - δ := hy.2
  have hxj : (dirList S).get ⟨j, hj⟩ < y := by linarith [hxL, hδ]
  have hyl : -Real.pi < y := by
    have hxI := dirList_get_mem_Ioc S ⟨j, hj⟩
    linarith [hxj, hxI.1]
  have hwrapX : 2 * Real.pi + (dirList S).get ⟨0, hlen0⟩ -
      (dirList S).get ⟨j, hj⟩ > 2 * δ := by
    rw [← dirList_get_j_last S hj hlast] at hwrap0
    exact hwrap0
  by_cases hypi : y ≤ Real.pi
  · have hyu : y ≤ Real.pi := hypi
    have hT : toIocMod Real.two_pi_pos (-Real.pi) y = y := by
      exact (toIocMod_eq_self Real.two_pi_pos (a := -Real.pi) (b := y)).2
        (show y ∈ Set.Ioc (-Real.pi) (-Real.pi + 2 * Real.pi) from ⟨hyl, by linarith⟩)
    have hno : ∀ d ∈ dirSet S, d ≠ toIocMod Real.two_pi_pos (-Real.pi) y := by
      intro d hd hEq
      rw [hT] at hEq
      have hdle : d ≤ (dirList S).get ⟨j, hj⟩ := by
        rcases (List.mem_iff_get.mp ((dirList_mem_iff S d).mpr hd)) with ⟨k, rfl⟩
        have hk : k.val ≤ j := by
          by_contra hnot
          have hgt : j < k.val := lt_of_not_ge hnot
          have : k.val < (dirList S).length := k.isLt
          have hlastval : j + 1 = (dirList S).length := hlast
          omega
        exact dirList_get_mono S (i := k) (j := ⟨j, hj⟩) hk
      linarith [hEq, hxj]
    simpa using (exp_ray_not_mem_star_of_not_dir (S := S) (θ := y) hno r)
  · have hpi_lt : Real.pi < y := lt_of_not_ge hypi
    have hy_le2 : y ≤ (dirList S).get ⟨0, hlen0⟩ + 2 * Real.pi - δ := by
      rw [hxpL] at hy_le
      exact hy_le
    have hT : toIocMod Real.two_pi_pos (-Real.pi) y = y - 2 * Real.pi := by
      rw [toIocMod_eq_iff]
      constructor
      · constructor
        · linarith [hpi_lt]
        · have h : -Real.pi + 2 * Real.pi = Real.pi := by ring
          rw [h]
          have hb : (dirList S).get ⟨0, hlen0⟩ ≤ Real.pi := (dirList_get_mem_Ioc S ⟨0, hlen0⟩).2
          linarith [hy_le2, hδ]
      · refine ⟨1, ?_⟩
        rw [one_zsmul]
        ring
    have hno : ∀ d ∈ dirSet S, d ≠ toIocMod Real.two_pi_pos (-Real.pi) y := by
      intro d hd hEq
      rw [hT] at hEq
      have hge : (dirList S).get ⟨0, hlen0⟩ ≤ d := dirList_head_le S hlen0 hd
      have hsmall : y - 2 * Real.pi < (dirList S).get ⟨0, hlen0⟩ := by
        have h1 : (dirList S).get ⟨j, hj⟩ + δ - 2 * Real.pi < (dirList S).get ⟨0, hlen0⟩ := by
          linarith [hwrapX, hδ]
        linarith [hy_le2, hxL]
      linarith
    simpa using (exp_ray_not_mem_star_of_not_dir (S := S) (θ := y) hno r)

/-! # Pull-back norm identities and multiplication bounds -/

/-- Norm of the pulled-back integrand of `h X = g X · q₁ X · q₂ X · X⁻¹`
factors as the product of the norms of the three holomorphic factors. -/
lemma pull_h_norm (g : ℂ → ℂ) (q₁ q₂ : ℂ[X]) (w : ℂ) :
    ‖(g (Complex.exp w) * (q₁.eval (Complex.exp w)) * (q₂.eval (Complex.exp w)) *
          (Complex.exp w)⁻¹) * Complex.exp w‖ =
      ‖g (Complex.exp w)‖ * ‖(q₁.eval (Complex.exp w))‖ * ‖(q₂.eval (Complex.exp w))‖ := by
  have hx0 : Complex.exp w ≠ 0 := Complex.exp_ne_zero w
  have hEq : (g (Complex.exp w) * (q₁.eval (Complex.exp w)) * (q₂.eval (Complex.exp w)) *
          (Complex.exp w)⁻¹) * Complex.exp w
      = g (Complex.exp w) * (q₁.eval (Complex.exp w)) * (q₂.eval (Complex.exp w)) := by
    calc
      (g (Complex.exp w) * (q₁.eval (Complex.exp w)) * (q₂.eval (Complex.exp w)) *
            (Complex.exp w)⁻¹) * Complex.exp w
          = g (Complex.exp w) * (q₁.eval (Complex.exp w)) * (q₂.eval (Complex.exp w)) *
            ((Complex.exp w)⁻¹ * Complex.exp w) := by ring
      _ = g (Complex.exp w) * (q₁.eval (Complex.exp w)) * (q₂.eval (Complex.exp w)) * 1 := by
            rw [inv_mul_cancel₀ hx0]
      _ = g (Complex.exp w) * (q₁.eval (Complex.exp w)) * (q₂.eval (Complex.exp w)) := by ring
  rw [hEq]
  rw [norm_mul, norm_mul]

/-- Multiply the three pointwise bounds on the factors of the pulled-back
integrand. -/
lemma pull_h_mul_bound (g : ℂ → ℂ) (q₁ q₂ : ℂ[X]) {M C θ : ℝ} (hM : 0 ≤ M)
    (hC0 : 0 ≤ C) (hθ0 : 0 ≤ θ) {a b : ℕ} (w : ℂ)
    (hg : ‖g (Complex.exp w)‖ ≤ M)
    (h1 : ‖(q₁.eval (Complex.exp w))‖ ≤ C * θ ^ a)
    (h2 : ‖(q₂.eval (Complex.exp w))‖ ≤ C * θ ^ b) :
    ‖(g (Complex.exp w) * (q₁.eval (Complex.exp w)) * (q₂.eval (Complex.exp w)) *
        (Complex.exp w)⁻¹) * Complex.exp w‖
      ≤ M * C * C * θ ^ (a + b) := by
  have hA : 0 ≤ ‖g (Complex.exp w)‖ := norm_nonneg _
  have hB : 0 ≤ ‖(q₁.eval (Complex.exp w))‖ := norm_nonneg _
  have hC : 0 ≤ ‖(q₂.eval (Complex.exp w))‖ := norm_nonneg _
  have h1' : ‖(q₁.eval (Complex.exp w))‖ * ‖(q₂.eval (Complex.exp w))‖ ≤
      (C * θ ^ a) * (C * θ ^ b) := mul_le_mul h1 h2 hC (mul_nonneg hC0 (pow_nonneg hθ0 a))
  have h12 : 0 ≤ (C * θ ^ a) * (C * θ ^ b) := mul_nonneg (mul_nonneg hC0 (pow_nonneg hθ0 a))
      (mul_nonneg hC0 (pow_nonneg hθ0 b))
  have hrewr : M * ((C * θ ^ a) * (C * θ ^ b)) = M * C * C * θ ^ (a + b) := by
    calc
      M * ((C * θ ^ a) * (C * θ ^ b)) = M * (C * C * (θ ^ a * θ ^ b)) := by ring
      _ = M * (C * C * θ ^ (a + b)) := by rw [← pow_add]
      _ = M * C * C * θ ^ (a + b) := by ring
  calc
    ‖(g (Complex.exp w) * (q₁.eval (Complex.exp w)) * (q₂.eval (Complex.exp w)) *
        (Complex.exp w)⁻¹) * Complex.exp w‖
        = ‖g (Complex.exp w)‖ * ‖(q₁.eval (Complex.exp w))‖ * ‖(q₂.eval (Complex.exp w))‖ :=
          pull_h_norm g q₁ q₂ w
    _ = ‖g (Complex.exp w)‖ * (‖(q₁.eval (Complex.exp w))‖ * ‖(q₂.eval (Complex.exp w))‖) := by ring
    _ ≤ M * ((C * θ ^ a) * (C * θ ^ b)) := mul_le_mul hg h1' (mul_nonneg hB hC) hM
    _ = M * C * C * θ ^ (a + b) := hrewr


open Submission.GOnCutPlane
open Submission.Dictionary
open Submission.BranchW
open Submission.Rays
open Submission.Minpoly
open Submission.PolyMoment
open Submission.HankelDecay
open Submission.E0Complex
open Submission.E2cParam
open Submission.Gnorm

/-- Norm bound for the branch `g` on contour points of radius `≥ exp A`
(`A := AOf ε`): `‖g X‖ ≤ M` for `M := (1 + house⁴ / exp A)^card`. -/
lemma norm_g_le_expA {K : Type*} [Field K] [NumberField K]
    (α : K) (hα : IsIntegral ℤ α) (hα0 : α ≠ 0) (g : ℂ → ℂ)
    (hgsq : ∀ X ∈ (star (conjugateValues α))ᶜ,
      g X ^ 2 = (Gpoly (minpoly ℤ α)).eval₂ (algebraMap ℤ ℂ) (X⁻¹))
    {A : ℝ} {X : ℂ} (hX : X ∈ (star (conjugateValues α))ᶜ)
    (hXge : Real.exp A ≤ ‖X‖) :
    ‖g X‖ ≤ (1 + (NumberField.house α) ^ 4 / Real.exp A) ^ (conjugateValues α).card := by
  classical
  have hXne : X ≠ 0 := by
    intro hX0
    have hSne : (conjugateValues α).Nonempty := by
      dsimp [conjugateValues]
      exact Finset.image_nonempty.mpr Finset.univ_nonempty
    exact hX (by simpa [hX0] using (zero_mem_star (S := conjugateValues α) hSne))
  have hb := norm_g_le (α := α) hα hα0 g hgsq (X := X) hX
  have hH4 : 0 ≤ (NumberField.house α) ^ 4 := by positivity
  have hden0 : 0 < Real.exp A := Real.exp_pos A
  have hXpos : 0 < ‖X‖ := lt_of_lt_of_le hden0 hXge
  have hinv : ‖X‖⁻¹ ≤ (Real.exp A)⁻¹ := (inv_le_inv₀ hXpos hden0).mpr hXge
  have hdiv : (NumberField.house α) ^ 4 / ‖X‖ ≤ (NumberField.house α) ^ 4 / Real.exp A := by
    calc
      (NumberField.house α) ^ 4 / ‖X‖ = (NumberField.house α) ^ 4 * ‖X‖⁻¹ := by
        rw [div_eq_mul_inv]
      _ ≤ (NumberField.house α) ^ 4 * (Real.exp A)⁻¹ := by
        exact mul_le_mul_of_nonneg_left hinv hH4
      _ = (NumberField.house α) ^ 4 / Real.exp A := by rw [div_eq_mul_inv]
  have hbasele : 1 + (NumberField.house α) ^ 4 / ‖X‖ ≤
      1 + (NumberField.house α) ^ 4 / Real.exp A := by linarith
  have hbase0 : 0 ≤ 1 + (NumberField.house α) ^ 4 / ‖X‖ := by
    exact add_nonneg zero_le_one (div_nonneg hH4 (le_of_lt hXpos))
  calc
    ‖g X‖ ≤ (1 + (NumberField.house α) ^ 4 / ‖X‖) ^ (conjugateValues α).card := hb
    _ ≤ (1 + (NumberField.house α) ^ 4 / Real.exp A) ^ (conjugateValues α).card := by
      exact pow_le_pow_left₀ hbase0 hbasele (conjugateValues α).card

/-- **E2c main theorem.**  Polynomial control of the hedgehog over the
conjugates (E1 output) forces the formal square-root sequence of
`Gpoly (minpoly ℤ α)` to have eventually vanishing integer Hankel
determinants — the input of `EngineAlg.no_hankelInput`. -/
theorem hankelDet_zero_of_hedgehogBound {K : Type*} [Field K] [NumberField K]
    (α : K) (hα : IsIntegral ℤ α) (hα0 : α ≠ 0)
    (hhb : HedgehogBound (conjugateValues α)) :
    Submission.EngineAlg.HankelInput α hα := by
  classical
  let S : Finset ℂ := conjugateValues α
  let P : ℤ[X] := minpoly ℤ α
  have hS0 : ∀ z ∈ S, z ≠ 0 := by
    intro z hz hz0
    dsimp [S] at hz
    exact (zero_not_mem_conjugateValues (α := α) hα0) (by simpa [hz0] using hz)
  have hSne : S.Nonempty := by
    dsimp [S, conjugateValues]
    exact Finset.image_nonempty.mpr Finset.univ_nonempty
  have hne : (dirSet S).Nonempty := by
    rcases hSne with ⟨z, hz⟩
    exact ⟨Complex.arg (z ^ 2), arg_sq_mem_dirSet (S := S) hz⟩
  have hlen0 : 0 < (dirList S).length := by
    rw [dirList_length]
    exact Finset.card_pos.mpr hne
  have hw0 : ∀ w ∈ spikeEndpoints S, w ≠ 0 := by
    classical
    intro w hw
    by_contra hw0
    rw [spikeEndpoints, Finset.mem_union] at hw
    rcases hw with hw | hw
    · rcases Finset.mem_image.mp hw with ⟨z, hz, rfl⟩
      exact (pow_ne_zero 2 (hS0 z (by simpa [S] using hz))) hw0
    · rcases Finset.mem_image.mp hw with ⟨z, hz, rfl⟩
      exact (pow_ne_zero 4 (hS0 z (by simpa [S] using hz))) hw0
  rcases hhb with ⟨ε, hε, C, hC, θ, hθ0, hθ1, hp⟩
  let p : ℕ → ℂ[X] := fun j => Classical.choose (hp j)
  have hpm : ∀ j : ℕ, (p j).Monic := by
    intro j
    exact (Classical.choose_spec (hp j)).1
  have hpd : ∀ j : ℕ, (p j).natDegree = j := by
    intro j
    exact (Classical.choose_spec (hp j)).2.1
  have hpb : ∀ (j : ℕ) (X : ℂ), X ∈ FatStar S ε → ‖(p j).eval X‖ ≤ C * θ ^ j := by
    intro j X hX
    exact (Classical.choose_spec (hp j)).2.2 X hX
  rcases (exists_holomorphic_branch (K := K) (α := α) hα hα0) with
    ⟨a, ha0, haConv, f, hfdiff, hfsq, hf0, htay⟩
  let g : ℂ → ℂ := fun X => if X = 0 then 0 else f (X⁻¹)
  have hgpoint : ∀ X : ℂ, X ≠ 0 → g X = f (X⁻¹) := by
    intro X hX
    dsimp [g]
    simp [hX]
  have hgdiff : DifferentiableOn ℂ g (XTransfer.star S)ᶜ := by
    dsimp [g, S]
    exact holomorphicOn_star_compl_of_holomorphicOn_cutPlane (S := conjugateValues α) hSne hfdiff
  have hgsq : ∀ X ∈ (XTransfer.star S)ᶜ, g X ^ 2 = (Gpoly P).eval₂ (algebraMap ℤ ℂ) (X⁻¹) := by
    intro X hX
    have hXne : X ≠ 0 := by
      intro hX0
      exact hX (by simpa [hX0] using (zero_mem_star (S := S) hSne))
    have hw : X⁻¹ ∈ cutPlane (rootFinset S) :=
      (mem_star_compl_iff_inv_mem_cutPlane (S := S) hXne).1 hX
    calc
      g X ^ 2 = (f (X⁻¹)) ^ 2 := by
        dsimp [g]
        simp [hXne]
      _ = (Gpoly P).eval₂ (algebraMap ℤ ℂ) (X⁻¹) := by
        simpa [S] using (hfsq (X⁻¹) (by simpa [S] using hw))
  have hC0 : ∀ c ∈ rootFinset S, c ≠ 0 := by
    exact rootFinset_ne_zero (S := S) (by simpa [S] using hS0)
  rcases (exists_ball_subset_cutPlane (C := rootFinset S) hC0) with ⟨ρ₀, hρ₀pos, hball⟩
  let R0 : ℝ := (ρ₀)⁻¹
  have hR0 : 0 < R0 := by
    dsimp [R0]
    exact inv_pos.mpr hρ₀pos
  let u : ℕ → ℝ := uOf S hlen0 ε
  let A : ℝ := AOf ε
  let B : ℝ := BOf S ε R0
  rcases (exists_delta_geo S hne hε hR0) with ⟨δ, hδpos, hδle1, hδx0, hsep, hwrap0, hradb⟩
  have hδle : δ ≤ Real.pi := by
    have hpi : (1 : ℝ) ≤ Real.pi := by linarith [Real.pi_gt_three]
    linarith
  have hδ0 : 0 ≤ δ := le_of_lt hδpos
  have hshort_all : ∀ (j : ℕ) (hj : j < (dirList S).length) (w : ℂ),
      w ∈ spikeEndpoints S → Complex.arg w = dirX S hlen0 j → ‖w‖ < Real.exp (u j) := by
    intro j hj w hw harg
    simpa [u] using (short_of_uOf S hlen0 hε hj hw harg)
  have hshortπ_all : ∀ w ∈ spikeEndpoints S, Complex.arg w = Real.pi →
      ‖w‖ < Real.exp (u ((dirList S).length - 1)) := by
    intro w hw harg
    simpa [u] using (shortπ_last S hlen0 hε hw harg)
  have hBigB_all : ∀ w ∈ spikeEndpoints S, ‖w‖ < Real.exp B := by
    intro w hw
    simpa [B] using (hBigB_of_BOf S hε hR0 w hw)
  have hub_all : ∀ (j : ℕ) (hj : j < (dirList S).length), u j ≤ B := by
    intro j hj
    simpa [u, B] using (uOf_le_BOf S hlen0 hε hR0 hj)
  have hA_le_u : ∀ (j : ℕ) (hj : j < (dirList S).length), A ≤ u j := by
    intro j hj
    simpa [u, A] using (AOf_le_uOf S hlen0 hε hj)
  have hug_all : ∀ (j : ℕ) (hj : j < (dirList S).length),
      Real.exp (u j) - dirSpikeLen S (dirX S hlen0 j) ≤ ε / 2 := by
    intro j hj
    simpa [u] using (exp_uOf_sub_spikeLen_le_half S hlen0 hε j)
  have huδ_all : ∀ (j : ℕ) (hj : j < (dirList S).length),
      2 * Real.exp (u j) * δ ≤ ε / 2 := by
    intro j hj
    exact huδ_of_radBound S hlen0 hε hδ0 hradb hj
  have hxj_dir : ∀ (j : ℕ) (hj : j < (dirList S).length), dirX S hlen0 j ∈ dirSet S := by
    intro j hj
    exact dirX_mem_dirSet S hlen0 hj
  let M := (1 + (NumberField.house α) ^ 4 / Real.exp A) ^ S.card
  have hM0 : 0 ≤ M := by
    dsimp [M]
    exact pow_nonneg (by positivity : (0 : ℝ) ≤ 1 + (NumberField.house α) ^ 4 / Real.exp A) S.card
  let sN : ℕ := (dirList S).length
  let L := ∑ j ∈ Finset.range sN,
    (2 * δ + |(dirX S hlen0 (j + 1) - δ) - (dirX S hlen0 j + δ)| + 2 * (u j - A))
  have hL0 : 0 ≤ L := by
    dsimp [L]
    apply Finset.sum_nonneg
    intro j hj
    have huA : 0 ≤ u j - A := sub_nonneg.mpr (hA_le_u j (by simpa [sN] using hj))
    have habs : 0 ≤ |(dirX S hlen0 (j + 1) - δ) - (dirX S hlen0 j + δ)| := abs_nonneg _
    nlinarith [hδ0, huA, habs]
  -- moment matrix bound (analytic core)
  have hmom : ∀ k : ℕ, 1 ≤ k → ∀ i j : Fin k,
      ‖(cMomentMatrix k (fun n : ℕ => (a n : ℂ)) (fun t : Fin k => p t.val) i j)‖ ≤
        (‖((2 * π * Complex.I)⁻¹ : ℂ)‖ * L * M * C * C) * θ ^ (i.val + j.val) := by
    intro k hk i j
    let h : ℂ → ℂ := fun X => g X * (p i.val).eval X * (p j.val).eval X * X⁻¹
    have hinv_diff : DifferentiableOn ℂ (fun X : ℂ => X⁻¹) (XTransfer.star S)ᶜ := by
      intro X hX
      have hXne : X ≠ 0 := by
        intro hX0
        exact hX (by simpa [hX0] using (zero_mem_star (S := S) hSne))
      exact (differentiableAt_inv hXne).differentiableWithinAt
    have hh : DifferentiableOn ℂ h (XTransfer.star S)ᶜ := by
      dsimp [h]
      have h1 := hgdiff.mul ((Polynomial.differentiable (p i.val)).differentiableOn)
      have h2 := h1.mul ((Polynomial.differentiable (p j.val)).differentiableOn)
      exact h2.mul hinv_diff
    have hfBall : DifferentiableOn ℂ f (Metric.ball (0 : ℂ) ρ₀) := by
      simpa [S] using hfdiff.mono hball
    have hρpos : 0 < Real.exp B := Real.exp_pos B
    have hρ : (Real.exp B)⁻¹ < ρ₀ := by
      have h1 : (Real.exp B)⁻¹ < R0⁻¹ :=
        (inv_lt_inv₀ hρpos hR0).mpr (R0_lt_exp_BOf S hε hR0)
      have hinv : R0⁻¹ = ρ₀ := by
        dsimp [R0]
        exact inv_inv ρ₀
      rwa [hinv] at h1
    have hMom : cMomentMatrix k (fun n : ℕ => (a n : ℂ)) (fun t : Fin k => p t.val) i j =
        ((2 * π * Complex.I)⁻¹) * (∮ z in C((0 : ℂ), Real.exp B), h z) := by
      dsimp [h]
      exact PolyMoment.cMomentMatrix_eq_circleIntegral hfBall htay hgpoint hρpos hρ k
        (fun t : Fin k => p t.val) (fun i0 : Fin k => hpd i0.val) i j
    have hdef := DStar.deformation_star S hS0 hh A B δ u hlen0 hδpos hδle hsep hwrap0 hδx0
      hBigB_all hshort_all hshortπ_all hub_all
    -- pointwise bound on the pieces
    let P : ℝ := M * C * C * θ ^ (i.val + j.val)
    have hcap_pt : ∀ (jN : ℕ) (hj : jN < (dirList S).length),
        ∀ y ∈ Set.uIoc (dirX S hlen0 jN - δ) (dirX S hlen0 jN + δ),
          ‖pull h ((u jN) + y * Complex.I)‖ ≤ P := by
      intro jN hj y hyu
      let w : ℂ := (u jN : ℂ) + (y : ℂ) * Complex.I
      let X : ℂ := Complex.exp w
      have hwin0 : dirX S hlen0 jN - δ ≤ dirX S hlen0 jN + δ := by linarith [hδ0]
      have hycc : y ∈ Set.Icc (dirX S hlen0 jN - δ) (dirX S hlen0 jN + δ) := by
        have hyu0 : y ∈ Set.uIcc (dirX S hlen0 jN - δ) (dirX S hlen0 jN + δ) :=
          Set.uIoc_subset_uIcc hyu
        rwa [Set.uIcc_of_le hwin0] at hyu0
      have hstar0 : Complex.exp ((u jN) + y * Complex.I) ∉ XTransfer.star S :=
        window_cap_not_mem_star S hS0 hlen0 hδpos hδle hsep hδx0 hwrap0 (u := u jN) (j := jN) hj
          (hshort_all jN hj) y hycc
      have hstar : X ∉ XTransfer.star S := by
        simpa [X, w] using hstar0
      have hΔ : |y - dirX S hlen0 jN| ≤ δ := by
        have hy1 : dirX S hlen0 jN - δ ≤ y := hycc.1
        have hy2 : y ≤ dirX S hlen0 jN + δ := hycc.2
        have hneg : -δ ≤ y - dirX S hlen0 jN := by linarith
        have hpos : y - dirX S hlen0 jN ≤ δ := by linarith
        exact abs_le.mpr ⟨hneg, hpos⟩
      have hfat0 : (Real.exp (u jN) : ℂ) * Complex.exp (y * Complex.I) ∈ FatStar S ε := by
        have hf := E2cGeom.fatStar_of_rot_point S (hxj_dir jN hj) hε hδ0 hδle1 (hug_all jN hj)
          (huδ_all jN hj) hw0 (Real.exp_pos (u jN)).le le_rfl (Δ := y - dirX S hlen0 jN) hΔ
        have harg : (dirX S hlen0 jN + (y - dirX S hlen0 jN)) * Complex.I = y * Complex.I := by ring
        simpa [harg] using hf
      have hXeq : X = (Real.exp (u jN) : ℂ) * Complex.exp (y * Complex.I) := by
        dsimp [X, w]
        rw [Complex.exp_add, ← Complex.ofReal_exp]
      have hfat : X ∈ FatStar S ε := by
        rw [hXeq]
        exact hfat0
      have hgeX : Real.exp A ≤ ‖X‖ := by
        dsimp [X, w]
        rw [Complex.norm_exp]
        have hre : ((u jN : ℂ) + (y : ℂ) * Complex.I).re = u jN := by simp
        rw [hre]
        exact Real.exp_le_exp.mpr (hA_le_u jN hj)
      have hgX : ‖g X‖ ≤ M := by
        have hXc : X ∈ (star (conjugateValues α))ᶜ := by
          simpa [S] using hstar
        have hb := norm_g_le_expA (α := α) hα hα0 g hgsq (A := A) (X := X) hXc hgeX
        simpa [M, S] using hb
      have h1X : ‖(p i.val).eval X‖ ≤ C * θ ^ i.val := hpb i.val X hfat
      have h2X : ‖(p j.val).eval X‖ ≤ C * θ ^ j.val := hpb j.val X hfat
      have hbnd := pull_h_mul_bound g (p i.val) (p j.val) hM0 hC.le hθ0 (a := i.val) (b := j.val) w
        hgX h1X h2X
      simpa [pull, h, P, w] using hbnd
    have hrad_pt : ∀ (jN : ℕ) (hj : jN < (dirList S).length) (sgn : ℝ),
        (sgn = -δ ∨ sgn = δ) →
        ∀ t ∈ Set.uIoc A (u jN),
          ‖pull h (t + ((dirX S hlen0 jN + sgn : ℝ) : ℂ) * Complex.I)‖ ≤ P := by
      intro jN hj sgn hsgn t htu
      let w : ℂ := (t : ℂ) + ((dirX S hlen0 jN + sgn : ℝ) : ℂ) * Complex.I
      let X : ℂ := Complex.exp w
      have htucc : t ∈ Set.Icc A (u jN) := by
        have hu : Set.uIcc A (u jN) = Set.Icc A (u jN) := Set.uIcc_of_le (hA_le_u jN hj)
        have ht0 : t ∈ Set.uIcc A (u jN) := Set.uIoc_subset_uIcc htu
        rwa [hu] at ht0
      have htA : A ≤ t := htucc.1
      have htu' : t ≤ u jN := htucc.2
      have hstar : X ∉ XTransfer.star S := by
        rcases hsgn with hsgn | hsgn
        · have hsr : Complex.exp (t + (dirX S hlen0 jN - δ) * Complex.I) ∉ XTransfer.star S :=
            radial_left_not_mem_star S hlen0 hδpos hsep hδx0 (j := jN) hj t
          have hc1 : dirX S hlen0 jN + (-δ) = dirX S hlen0 jN - δ := by ring
          dsimp [X, w]
          simpa [hsgn, hc1] using hsr
        · have hsr : Complex.exp (t + (dirX S hlen0 jN + δ) * Complex.I) ∉ XTransfer.star S :=
            radial_right_not_mem_star S hlen0 hδpos hδle hsep hδx0 hwrap0 (j := jN) hj t
          dsimp [X, w]
          simpa [hsgn] using hsr
      have hΔ : |sgn| ≤ δ := by
        rcases hsgn with hsgn | hsgn
        · rw [hsgn]
          simpa [abs_of_nonneg hδ0]
        · rw [hsgn]
          simpa [abs_of_nonneg hδ0]
      have hfat0 : (Real.exp t : ℂ) * Complex.exp (((dirX S hlen0 jN : ℂ) + (sgn : ℂ)) * Complex.I) ∈ FatStar S ε := by
        have hf := E2cGeom.fatStar_of_rot_point S (hxj_dir jN hj) hε hδ0 hδle1 (hug_all jN hj)
          (huδ_all jN hj) hw0 (Real.exp_pos t).le (Real.exp_le_exp.mpr htu') (Δ := sgn) hΔ
        simpa using hf
      have hXeq : X = (Real.exp t : ℂ) * Complex.exp (((dirX S hlen0 jN : ℂ) + (sgn : ℂ)) * Complex.I) := by
        dsimp [X, w]
        rw [Complex.exp_add, ← Complex.ofReal_exp]
        simp
      have hfat : X ∈ FatStar S ε := by
        rw [hXeq]
        exact hfat0
      have hgeX : Real.exp A ≤ ‖X‖ := by
        dsimp [X, w]
        rw [Complex.norm_exp]
        have hre : ((t : ℂ) + ((dirX S hlen0 jN + sgn : ℝ) : ℂ) * Complex.I).re = t := by simp
        rw [hre]
        exact Real.exp_le_exp.mpr htA
      have hgX : ‖g X‖ ≤ M := by
        have hXc : X ∈ (star (conjugateValues α))ᶜ := by
          simpa [S] using hstar
        have hb := norm_g_le_expA (α := α) hα hα0 g hgsq (A := A) (X := X) hXc hgeX
        simpa [M, S] using hb
      have h1X : ‖(p i.val).eval X‖ ≤ C * θ ^ i.val := hpb i.val X hfat
      have h2X : ‖(p j.val).eval X‖ ≤ C * θ ^ j.val := hpb j.val X hfat
      have hbnd := pull_h_mul_bound g (p i.val) (p j.val) hM0 hC.le hθ0 (a := i.val) (b := j.val) w
        hgX h1X h2X
      simpa [pull, h, P, w] using hbnd
    have hgap_pt : ∀ (jN : ℕ) (hj : jN < (dirList S).length),
        ∀ y ∈ Set.uIoc (dirX S hlen0 jN + δ) (dirX S hlen0 (jN + 1) - δ),
          ‖pull h (A + y * Complex.I)‖ ≤ P := by
      intro jN hj y hyu
      let w : ℂ := (A : ℂ) + (y : ℂ) * Complex.I
      let X : ℂ := Complex.exp w
      by_cases hlt : jN + 1 < (dirList S).length
      · -- interior gap
        have hxL : dirX S hlen0 jN = (dirList S).get ⟨jN, hj⟩ := dirX_of_lt S hlen0 hj
        have hxpL : dirX S hlen0 (jN + 1) = (dirList S).get ⟨jN + 1, hlt⟩ := dirX_of_lt S hlen0 hlt
        have hgap_pos : (dirList S).get ⟨jN + 1, hlt⟩ - (dirList S).get ⟨jN, hj⟩ > 2 * δ :=
          dirList_sep_at S hsep hj hlt
        have hwin0 : dirX S hlen0 jN + δ ≤ dirX S hlen0 (jN + 1) - δ := by
          rw [hxL, hxpL]
          linarith [hgap_pos]
        have hycc : y ∈ Set.Icc (dirX S hlen0 jN + δ) (dirX S hlen0 (jN + 1) - δ) := by
          have hyu0 : y ∈ Set.uIcc (dirX S hlen0 jN + δ) (dirX S hlen0 (jN + 1) - δ) :=
            Set.uIoc_subset_uIcc hyu
          rwa [Set.uIcc_of_le hwin0] at hyu0
        have hstar0 : ∀ r : ℝ, Complex.exp (r + y * Complex.I) ∉ XTransfer.star S :=
          gap_arc_interior_not_mem_star S hlen0 hδpos hj hlt y hycc
        have hstar : X ∉ XTransfer.star S := by
          simpa [X, w] using (hstar0 A)
        have hfat0 : (Real.exp A : ℂ) * Complex.exp (y * Complex.I) ∈ FatStar S ε :=
          E2cGeom.fatStar_gap_point S hSne hε (exp_AOf_le_eps hε) y
        have hXeq : X = (Real.exp A : ℂ) * Complex.exp (y * Complex.I) := by
          dsimp [X, w]
          rw [Complex.exp_add, ← Complex.ofReal_exp]
        have hfat : X ∈ FatStar S ε := by
          rw [hXeq]
          exact hfat0
        have hgeX : Real.exp A ≤ ‖X‖ := by
          dsimp [X, w]
          rw [Complex.norm_exp]
          simp
        have hgX : ‖g X‖ ≤ M := by
          have hXc : X ∈ (star (conjugateValues α))ᶜ := by
            simpa [S] using hstar
          have hb := norm_g_le_expA (α := α) hα hα0 g hgsq (A := A) (X := X) hXc hgeX
          simpa [M, S] using hb
        have h1X : ‖(p i.val).eval X‖ ≤ C * θ ^ i.val := hpb i.val X hfat
        have h2X : ‖(p j.val).eval X‖ ≤ C * θ ^ j.val := hpb j.val X hfat
        have hbnd := pull_h_mul_bound g (p i.val) (p j.val) hM0 hC.le hθ0 (a := i.val) (b := j.val) w
          hgX h1X h2X
        simpa [pull, h, P, w] using hbnd
      · -- wrap gap
        have hlast : jN + 1 = (dirList S).length := by omega
        have hwrapW : 2 * Real.pi + (dirList S).get ⟨0, hlen0⟩ -
            (dirList S).get ⟨jN, hj⟩ > 2 * δ := by
          rw [← dirList_get_j_last S hj hlast] at hwrap0
          exact hwrap0
        have hwin0 : dirX S hlen0 jN + δ ≤ dirX S hlen0 (jN + 1) - δ := by
          rw [hlast, dirX_length S hlen0]
          have hxL : dirX S hlen0 jN = (dirList S).get ⟨jN, hj⟩ := dirX_of_lt S hlen0 hj
          rw [hxL]
          have hxb : (dirList S).get ⟨0, hlen0⟩ ≤ Real.pi := (dirList_get_mem_Ioc S ⟨0, hlen0⟩).2
          have hxl : (dirList S).get ⟨jN, hj⟩ > -Real.pi := (dirList_get_mem_Ioc S ⟨jN, hj⟩).1
          linarith [hwrapW]
        have hycc : y ∈ Set.Icc (dirX S hlen0 jN + δ) (dirX S hlen0 (jN + 1) - δ) := by
          have hyu0 : y ∈ Set.uIcc (dirX S hlen0 jN + δ) (dirX S hlen0 (jN + 1) - δ) :=
            Set.uIoc_subset_uIcc hyu
          rwa [Set.uIcc_of_le hwin0] at hyu0
        have hstar0 : ∀ r : ℝ, Complex.exp (r + y * Complex.I) ∉ XTransfer.star S :=
          gap_arc_wrap_not_mem_star S hlen0 hδpos hδx0 hwrap0 hj hlast y hycc
        have hstar : X ∉ XTransfer.star S := by
          simpa [X, w] using (hstar0 A)
        have hfat0 : (Real.exp A : ℂ) * Complex.exp (y * Complex.I) ∈ FatStar S ε :=
          E2cGeom.fatStar_gap_point S hSne hε (exp_AOf_le_eps hε) y
        have hXeq : X = (Real.exp A : ℂ) * Complex.exp (y * Complex.I) := by
          dsimp [X, w]
          rw [Complex.exp_add, ← Complex.ofReal_exp]
        have hfat : X ∈ FatStar S ε := by
          rw [hXeq]
          exact hfat0
        have hgeX : Real.exp A ≤ ‖X‖ := by
          dsimp [X, w]
          rw [Complex.norm_exp]
          simp
        have hgX : ‖g X‖ ≤ M := by
          have hXc : X ∈ (star (conjugateValues α))ᶜ := by
            simpa [S] using hstar
          have hb := norm_g_le_expA (α := α) hα hα0 g hgsq (A := A) (X := X) hXc hgeX
          simpa [M, S] using hb
        have h1X : ‖(p i.val).eval X‖ ≤ C * θ ^ i.val := hpb i.val X hfat
        have h2X : ‖(p j.val).eval X‖ ≤ C * θ ^ j.val := hpb j.val X hfat
        have hbnd := pull_h_mul_bound g (p i.val) (p j.val) hM0 hC.le hθ0 (a := i.val) (b := j.val) w
          hgX h1X h2X
        simpa [pull, h, P, w] using hbnd
    -- per-piece integral bounds
    have hlen_uA : ∀ (j : ℕ) (hj : j < sN), |u j - A| = u j - A := by
      intro j hj
      rw [abs_of_nonneg (sub_nonneg.mpr (hA_le_u j (by simpa [sN] using hj)))]
    have hbarc_cap : ∀ (j : ℕ) (hj : j < sN),
        ‖arcInt (pull h) (u j) (dirX S hlen0 j - δ) (dirX S hlen0 j + δ)‖ ≤ P * (2 * δ) := by
      intro j hj
      have hpt := hcap_pt j (by simpa [sN] using hj)
      have hb := arcInt_norm_le (pull h) (u j) (dirX S hlen0 j - δ) (dirX S hlen0 j + δ) P hpt
      have hlen : |(dirX S hlen0 j + δ) - (dirX S hlen0 j - δ)| = 2 * δ := by
        have hnonneg : 0 ≤ (dirX S hlen0 j + δ) - (dirX S hlen0 j - δ) := by linarith [hδ0]
        rw [abs_of_nonneg hnonneg]
        ring
      rwa [hlen] at hb
    have hbarc_gap : ∀ (j : ℕ) (hj : j < sN),
        ‖arcInt (pull h) A (dirX S hlen0 j + δ) (dirX S hlen0 (j + 1) - δ)‖ ≤
          P * |(dirX S hlen0 (j + 1) - δ) - (dirX S hlen0 j + δ)| := by
      intro j hj
      exact arcInt_norm_le (pull h) A (dirX S hlen0 j + δ) (dirX S hlen0 (j + 1) - δ) P
        (hgap_pt j (by simpa [sN] using hj))
    have hbrad : ∀ (j : ℕ) (hj : j < sN) (sgn : ℝ),
        (sgn = -δ ∨ sgn = δ) →
        ‖radInt (pull h) A (u j) (dirX S hlen0 j + sgn)‖ ≤ P * (u j - A) := by
      intro j hj sgn hsgn
      have hpt := hrad_pt j (by simpa [sN] using hj) sgn hsgn
      have hb := radInt_norm_le (pull h) A (u j) (dirX S hlen0 j + sgn) P hpt
      have hlen : |u j - A| = u j - A := hlen_uA j (by simpa [sN] using hj)
      rwa [hlen] at hb
    -- norm of the deformed contour ≤ P·L
    have hdef' : (∮ z in C((0 : ℂ), Real.exp B), h z) =
        (∑ j ∈ Finset.range sN, Complex.I • arcInt (pull h) (u j)
            (dirX S hlen0 j - δ) (dirX S hlen0 j + δ))
        + (∑ j ∈ Finset.range sN, Complex.I • arcInt (pull h) A
            (dirX S hlen0 j + δ) (dirX S hlen0 (j + 1) - δ))
        + (∑ j ∈ Finset.range sN, radInt (pull h) A (u j) (dirX S hlen0 j - δ))
        - (∑ j ∈ Finset.range sN, radInt (pull h) A (u j) (dirX S hlen0 j + δ)) := by
      dsimp [sN]
      exact hdef
    have hnorm_circle : ‖(∮ z in C((0 : ℂ), Real.exp B), h z)‖ ≤ P * L := by
      let S1 : ℂ := ∑ j ∈ Finset.range sN, Complex.I • arcInt (pull h) (u j)
          (dirX S hlen0 j - δ) (dirX S hlen0 j + δ)
      let S2 : ℂ := ∑ j ∈ Finset.range sN, Complex.I • arcInt (pull h) A
          (dirX S hlen0 j + δ) (dirX S hlen0 (j + 1) - δ)
      let S3 : ℂ := ∑ j ∈ Finset.range sN, radInt (pull h) A (u j) (dirX S hlen0 j - δ)
      let S4 : ℂ := ∑ j ∈ Finset.range sN, radInt (pull h) A (u j) (dirX S hlen0 j + δ)
      have hbS1 : ‖S1‖ ≤ ∑ j ∈ Finset.range sN, P * (2 * δ) := by
        dsimp [S1]
        calc
          ‖(∑ j ∈ Finset.range sN, Complex.I • arcInt (pull h) (u j)
              (dirX S hlen0 j - δ) (dirX S hlen0 j + δ))‖
              ≤ ∑ j ∈ Finset.range sN,
                  ‖Complex.I • arcInt (pull h) (u j) (dirX S hlen0 j - δ) (dirX S hlen0 j + δ)‖ :=
                norm_sum_le _ _
          _ = ∑ j ∈ Finset.range sN,
                  ‖arcInt (pull h) (u j) (dirX S hlen0 j - δ) (dirX S hlen0 j + δ)‖ := by
                apply Finset.sum_congr rfl
                intro j hj
                rw [norm_smul, Complex.norm_I, one_mul]
          _ ≤ ∑ j ∈ Finset.range sN, P * (2 * δ) := by
                apply Finset.sum_le_sum
                intro j hj
                exact hbarc_cap j (Finset.mem_range.mp hj)
      have hbS2 : ‖S2‖ ≤ ∑ j ∈ Finset.range sN,
            P * |(dirX S hlen0 (j + 1) - δ) - (dirX S hlen0 j + δ)| := by
        dsimp [S2]
        calc
          ‖(∑ j ∈ Finset.range sN, Complex.I • arcInt (pull h) A
              (dirX S hlen0 j + δ) (dirX S hlen0 (j + 1) - δ))‖
              ≤ ∑ j ∈ Finset.range sN,
                  ‖Complex.I • arcInt (pull h) A (dirX S hlen0 j + δ) (dirX S hlen0 (j + 1) - δ)‖ :=
                norm_sum_le _ _
          _ = ∑ j ∈ Finset.range sN,
                  ‖arcInt (pull h) A (dirX S hlen0 j + δ) (dirX S hlen0 (j + 1) - δ)‖ := by
                apply Finset.sum_congr rfl
                intro j hj
                rw [norm_smul, Complex.norm_I, one_mul]
          _ ≤ ∑ j ∈ Finset.range sN,
                P * |(dirX S hlen0 (j + 1) - δ) - (dirX S hlen0 j + δ)| := by
                apply Finset.sum_le_sum
                intro j hj
                exact hbarc_gap j (Finset.mem_range.mp hj)
      have hbS3 : ‖S3‖ ≤ ∑ j ∈ Finset.range sN, P * (u j - A) := by
        dsimp [S3]
        calc
          ‖(∑ j ∈ Finset.range sN, radInt (pull h) A (u j) (dirX S hlen0 j - δ))‖
              ≤ ∑ j ∈ Finset.range sN,
                  ‖radInt (pull h) A (u j) (dirX S hlen0 j - δ)‖ := norm_sum_le _ _
          _ ≤ ∑ j ∈ Finset.range sN, P * (u j - A) := by
                apply Finset.sum_le_sum
                intro j hj
                exact hbrad j (Finset.mem_range.mp hj) (-δ) (Or.inl rfl)
      have hbS4 : ‖S4‖ ≤ ∑ j ∈ Finset.range sN, P * (u j - A) := by
        dsimp [S4]
        calc
          ‖(∑ j ∈ Finset.range sN, radInt (pull h) A (u j) (dirX S hlen0 j + δ))‖
              ≤ ∑ j ∈ Finset.range sN,
                  ‖radInt (pull h) A (u j) (dirX S hlen0 j + δ)‖ := norm_sum_le _ _
          _ ≤ ∑ j ∈ Finset.range sN, P * (u j - A) := by
                apply Finset.sum_le_sum
                intro j hj
                exact hbrad j (Finset.mem_range.mp hj) δ (Or.inr rfl)
      have hsplit : ‖S1 + S2 + S3 - S4‖ ≤
          (∑ j ∈ Finset.range sN, P * (2 * δ)) +
          (∑ j ∈ Finset.range sN,
            P * |(dirX S hlen0 (j + 1) - δ) - (dirX S hlen0 j + δ)|) +
          (∑ j ∈ Finset.range sN, P * (u j - A)) +
          (∑ j ∈ Finset.range sN, P * (u j - A)) := by
        have h1 : ‖S1 + S2 + S3 - S4‖ ≤ ‖S1 + S2 + S3‖ + ‖S4‖ := norm_sub_le _ _
        have h2 : ‖S1 + S2 + S3‖ ≤ ‖S1 + S2‖ + ‖S3‖ := norm_add_le _ _
        have h3 : ‖S1 + S2‖ ≤ ‖S1‖ + ‖S2‖ := norm_add_le _ _
        have hh : ‖S1‖ + ‖S2‖ + ‖S3‖ + ‖S4‖ ≤
            (∑ j ∈ Finset.range sN, P * (2 * δ)) +
            (∑ j ∈ Finset.range sN,
              P * |(dirX S hlen0 (j + 1) - δ) - (dirX S hlen0 j + δ)|) +
            (∑ j ∈ Finset.range sN, P * (u j - A)) +
            (∑ j ∈ Finset.range sN, P * (u j - A)) := by
          have hA := hbS1
          have hB := hbS2
          have hC := hbS3
          have hD := hbS4
          linarith
        nlinarith
      have hsums : (∑ j ∈ Finset.range sN, P * (2 * δ)) +
          (∑ j ∈ Finset.range sN,
            P * |(dirX S hlen0 (j + 1) - δ) - (dirX S hlen0 j + δ)|) +
          (∑ j ∈ Finset.range sN, P * (u j - A)) +
          (∑ j ∈ Finset.range sN, P * (u j - A)) = P * L := by
        calc
          (∑ j ∈ Finset.range sN, P * (2 * δ)) +
              (∑ j ∈ Finset.range sN,
                P * |(dirX S hlen0 (j + 1) - δ) - (dirX S hlen0 j + δ)|) +
              (∑ j ∈ Finset.range sN, P * (u j - A)) +
              (∑ j ∈ Finset.range sN, P * (u j - A))
              = ∑ j ∈ Finset.range sN,
                  (P * (2 * δ) +
                    P * |(dirX S hlen0 (j + 1) - δ) - (dirX S hlen0 j + δ)| +
                    P * (u j - A) + P * (u j - A)) := by
                rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
          _ = P * L := by
                dsimp [L]
                rw [Finset.mul_sum]
                apply Finset.sum_congr rfl
                intro j hj
                ring
      have hdefs : (∮ z in C((0 : ℂ), Real.exp B), h z) = S1 + S2 + S3 - S4 := by
        dsimp [S1, S2, S3, S4, sN]
        exact hdef
      calc
        ‖(∮ z in C((0 : ℂ), Real.exp B), h z)‖ = ‖S1 + S2 + S3 - S4‖ := by rw [hdefs]
        _ ≤ (∑ j ∈ Finset.range sN, P * (2 * δ)) +
            (∑ j ∈ Finset.range sN,
              P * |(dirX S hlen0 (j + 1) - δ) - (dirX S hlen0 j + δ)|) +
            (∑ j ∈ Finset.range sN, P * (u j - A)) +
            (∑ j ∈ Finset.range sN, P * (u j - A)) := hsplit
        _ = P * L := hsums
    have hnormM : ‖(cMomentMatrix k (fun n : ℕ => (a n : ℂ)) (fun t : Fin k => p t.val) i j)‖ ≤
        ‖((2 * π * Complex.I)⁻¹ : ℂ)‖ * (P * L) := by
      rw [hMom]
      calc
        ‖((2 * π * Complex.I)⁻¹ : ℂ) * (∮ z in C((0 : ℂ), Real.exp B), h z)‖
            = ‖((2 * π * Complex.I)⁻¹ : ℂ)‖ * ‖(∮ z in C((0 : ℂ), Real.exp B), h z)‖ := norm_mul _ _
        _ ≤ ‖((2 * π * Complex.I)⁻¹ : ℂ)‖ * (P * L) :=
            mul_le_mul_of_nonneg_left hnorm_circle (norm_nonneg _)
    have hfinal : ‖(cMomentMatrix k (fun n : ℕ => (a n : ℂ)) (fun t : Fin k => p t.val) i j)‖ ≤
        (‖((2 * π * Complex.I)⁻¹ : ℂ)‖ * L * M * C * C) * θ ^ (i.val + j.val) := by
      calc
        ‖(cMomentMatrix k (fun n : ℕ => (a n : ℂ)) (fun t : Fin k => p t.val) i j)‖
            ≤ ‖((2 * π * Complex.I)⁻¹ : ℂ)‖ * (P * L) := hnormM
        _ = ‖((2 * π * Complex.I)⁻¹ : ℂ)‖ * (L * (M * C * C * θ ^ (i.val + j.val))) := by
              dsimp [P]
              ring
        _ = (‖((2 * π * Complex.I)⁻¹ : ℂ)‖ * L * M * C * C) * θ ^ (i.val + j.val) := by ring
    exact hfinal
  have hK0 : 0 ≤ ‖((2 * π * Complex.I)⁻¹ : ℂ)‖ * L * M * C * C := by
    have hC0 : 0 ≤ C := hC.le
    have hpos1 : 0 ≤ ‖((2 * π * Complex.I)⁻¹ : ℂ)‖ * L := mul_nonneg (norm_nonneg _) hL0
    have hpos2 : 0 ≤ ‖((2 * π * Complex.I)⁻¹ : ℂ)‖ * L * M := mul_nonneg hpos1 hM0
    have hpos3 : 0 ≤ ‖((2 * π * Complex.I)⁻¹ : ℂ)‖ * L * M * C := mul_nonneg hpos2 hC0
    exact mul_nonneg hpos3 hC0
  rcases (hankelDet_eventually_zero_of_moment_bound a p hpm hpd hK0 hθ0 hθ1 hmom) with ⟨N, hN⟩
  exact ⟨a, ha0, haConv, N, hN⟩

end Submission.E2c

end

