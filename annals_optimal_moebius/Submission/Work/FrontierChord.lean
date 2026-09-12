import Submission.Work.SectorFill
import Submission.Work.FrontierCluster

open OptimalMoebius Filter Topology
open scoped BigOperators Matrix Topology Metric

set_option autoImplicit false
set_option maxHeartbeats 800000
local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)
local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-!
# The degenerate frontier is locally a straight chord — (r2), chord form (FrontierChord)

`SectorFill.degenerate_frontier_half_disk` gives, at every degenerate
frontier point `e` of a flat component `C = flatComponent f p`, the
half-disk statement `C ∩ B(e,ρ) = {φ_w < 0} ∩ B(e,ρ)` with
`φ_w z := signedLineFunc e w z` (`w` unit).  This file upgrades that to
the exact **frontier** statement:

    `z ∈ frontier C  ↔  signedLineFunc e w z = 0`   (for `z ∈ B(e,ρ)`),

i.e. the frontier of `C` inside `B(e,ρ)` is EXACTLY the straight chord
through `e` in direction `w`, with `C` strictly on the `φ_w < 0` side.
This is Target (r2) of the flat-trapezoid analysis in its chord form —
the pointwise building block from which the side lines of `C` (and hence
the `FlatSideData` correspondence) are assembled.

Proof structure (pure topology from the green half-disk statement; no new
surface geometry):
* `⊆`: `z ∈ frontier C ∩ B` gives `z ∉ C` (C open, `interior C = C`) and
  `z ∈ closure C`; `φ z < 0` would put `z ∈ C` (the half-disk), while
  `0 < φ z` is impossible by continuity of `φ` (a small ball around `z`
  stays in `{φ > 0} ∩ B(e,ρ)`, yet `z ∈ closure C` puts `C`-points in
  every such ball, and those would need `φ < 0`).  Hence `φ z = 0`.
* `⊇`: `φ z = 0` (`z ∈ B(e,ρ)`): `z ∉ C` (else `φ z < 0`); for closure,
  move from `z` a small distance `t` in the direction
  `n := (−w₁, w₀)` perpendicular to `w` (unit, `det2 n w = −‖w‖² < 0`):
  `φ(z + t•n) = φ z + t·det2 n w < 0`, so with `0 < t < ε` and
  `t < ρ − dist z e` the point `z + t•n` lies in `C` (half-disk) within
  `ε` of `z`.

Build: `lake build Submission.Work.FrontierChord` rc=0, zero sorry.
-/

noncomputable section
namespace Submission.PaperBand

/-- The unit perpendicular to a unit vector `w`: `n := (−w₁, w₀)` has norm
1 and satisfies `det2 n w = −‖w‖² < 0`. -/
lemma norm_perp_rot {w : ℝ²} (hw₁ : ‖w‖ = 1) :
    ‖(!₂[-(w 1), w 0] : ℝ²)‖ = 1 := by
  have hnn2 : ‖(!₂[-(w 1), w 0] : ℝ²)‖ ^ 2 = 1 := by
    calc
      ‖(!₂[-(w 1), w 0] : ℝ²)‖ ^ 2 = (-(w 1)) ^ 2 + (w 0) ^ 2 := by
        rw [norm_sq_coord_sum]
        simp
      _ = (w 0) ^ 2 + (w 1) ^ 2 := by ring
      _ = 1 := by
        have h := norm_sq_coord_sum w
        have hw2 : ‖w‖ ^ 2 = 1 := by rw [hw₁]; norm_num
        nlinarith
  have hnn0 : 0 ≤ ‖(!₂[-(w 1), w 0] : ℝ²)‖ := norm_nonneg _
  apply le_antisymm
  · have hle : ‖(!₂[-(w 1), w 0] : ℝ²)‖ ^ 2 ≤ 1 ^ 2 := by simpa using hnn2.le
    exact (sq_le_sq₀ hnn0 (by norm_num)).mp hle
  · have hle : 1 ^ 2 ≤ ‖(!₂[-(w 1), w 0] : ℝ²)‖ ^ 2 := by
      rw [hnn2]
      norm_num
    exact (sq_le_sq₀ (by norm_num) hnn0).mp hle

/-- The rotated direction crosses to the negative side of the signed
functional: `det2 n w < 0` for `n := (−w₁, w₀)`, `‖w‖ = 1`. -/
lemma det2_perp_rot_neg {w : ℝ²} (hw₁ : ‖w‖ = 1) :
    det2 (!₂[-(w 1), w 0] : ℝ²) w < 0 := by
  have hw : (w 0) ^ 2 + (w 1) ^ 2 = 1 := by
    have h := norm_sq_coord_sum w
    have hw2 : ‖w‖ ^ 2 = 1 := by rw [hw₁]; norm_num
    nlinarith
  dsimp [det2]
  simp
  nlinarith

/-- **Degenerate frontier is locally a straight chord** (Target (r2),
chord form): at a degenerate frontier point `e` of the flat component
`C = flatComponent f p` there is a unit direction `w` and `ρ > 0` such
that, inside `B(e,ρ)` (contained in the strip interior), a point lies on
the frontier of `C` iff it lies on the straight line through `e` in
direction `w`: `z ∈ frontier C ↔ signedLineFunc e w z = 0`.  Combined
with `degenerate_frontier_half_disk` (`C ∩ B(e,ρ) = {φ_w < 0} ∩ B(e,ρ)`)
this says: near `e` the component `C` is exactly one open half of the
ball cut by the straight chord through `e` in direction `w`. -/
theorem degenerate_frontier_straight_chord {a : ℝ} {f : ℝ² → ℝ³}
    (hf : IsMoebiusEmbedding a f) (ha : 0 < a) {p e : ℝ²} (heS : e ∈ stripInterior)
    (heF : e ∈ frontier (flatComponent f p)) :
    ∃ w : ℝ², ∃ ρ : ℝ, ‖w‖ = 1 ∧ 0 < ρ ∧ Metric.ball e ρ ⊆ stripInterior ∧
      (∀ z : ℝ², z ∈ Metric.ball e ρ →
        (z ∈ frontier (flatComponent f p) ↔ signedLineFunc e w z = 0)) := by
  rcases degenerate_frontier_half_disk hf ha heS heF with ⟨w, ρ, hw₁, hρ, hballS, hiff⟩
  refine ⟨w, ρ, hw₁, hρ, hballS, ?_⟩
  intro z hzball
  have hopen : IsOpen (flatComponent f p) := isOpen_flatComponent f p
  have hinteq : interior (flatComponent f p) = flatComponent f p := hopen.interior_eq
  constructor
  · -- z ∈ frontier C  →  φ z = 0
    intro hzF
    change z ∈ closure (flatComponent f p) ∧ z ∉ interior (flatComponent f p) at hzF
    have hzC : z ∉ flatComponent f p := by
      intro hzin
      apply hzF.2
      rwa [hinteq]
    have hzcl : z ∈ closure (flatComponent f p) := hzF.1
    by_contra hφne
    rcases lt_or_gt_of_ne hφne with hφlt | hφgt
    · exact hzC ((hiff z hzball).mpr hφlt)
    · exfalso
      -- 0 < φ z contradicts z ∈ closure C (C-points in every ball would have φ < 0)
      have hcont : ContinuousAt (fun x : ℝ² => signedLineFunc e w x) z :=
        (continuous_signedLineFunc e w).continuousAt
      have hevpos : ∀ᶠ x in 𝓝 z, 0 < signedLineFunc e w x := by
        change (fun x : ℝ² => signedLineFunc e w x) ⁻¹' Set.Ioi 0 ∈ 𝓝 z
        exact hcont.preimage_mem_nhds (isOpen_Ioi.mem_nhds
          (show (0 : ℝ) < signedLineFunc e w z from hφgt))
      rcases (Metric.eventually_nhds_iff.mp hevpos) with ⟨δ, hδ, hδpos⟩
      have hze : dist z e < ρ := (Metric.mem_ball.mp hzball)
      let ε₂ : ℝ := (ρ - dist z e) / 2
      have hε₂p : 0 < ε₂ := by dsimp [ε₂]; linarith
      let ε : ℝ := min δ ε₂
      have hεp : 0 < ε := lt_min hδ hε₂p
      have hzclε := (Metric.mem_closure_iff.mp hzcl) ε hεp
      rcases hzclε with ⟨c, hcC, hcz⟩
      have hcpos : 0 < signedLineFunc e w c := by
        apply hδpos
        have hczs : dist c z = dist z c := dist_comm c z
        rw [hczs]
        exact lt_of_lt_of_le hcz (min_le_left δ ε₂)
      have hce : dist c e < ρ := by
        have htria : dist c e ≤ dist c z + dist z e := dist_triangle c z e
        have hczs : dist c z = dist z c := dist_comm c z
        have hczle : dist c z < (ρ - dist z e) / 2 := by
          rw [hczs]
          exact lt_of_lt_of_le hcz (min_le_right δ ε₂)
        nlinarith
      have hcball : c ∈ Metric.ball e ρ := (Metric.mem_ball.mpr hce)
      have hcneg : signedLineFunc e w c < 0 := (hiff c hcball).1 hcC
      linarith
  · -- φ z = 0 → z ∈ frontier C
    intro hφ0
    constructor
    · -- z ∈ closure C
      rw [Metric.mem_closure_iff]
      intro ε hε
      have hze : dist z e < ρ := (Metric.mem_ball.mp hzball)
      let n : ℝ² := !₂[-(w 1), w 0]
      have hnn₁ : ‖n‖ = 1 := by
        dsimp [n]
        exact norm_perp_rot hw₁
      have hdetn : det2 n w < 0 := by
        dsimp [n]
        exact det2_perp_rot_neg hw₁
      let t : ℝ := min (ε / 2) ((ρ - dist z e) / 2)
      have htpos : 0 < t := by
        dsimp [t]
        exact lt_min (by linarith) (by linarith)
      let c : ℝ² := z + t • n
      have hdist : dist z c < ε := by
        dsimp [c]
        have hzcn : ‖z - (z + t • n)‖ = t * ‖n‖ := by
          rw [show z - (z + t • n) = -(t • n) by abel]
          rw [norm_neg]
          rw [norm_smul]
          rw [Real.norm_eq_abs]
          rw [abs_of_nonneg (le_of_lt htpos)]
        have hmain : ‖z - (z + t • n)‖ = t := by
          rw [hzcn, hnn₁]
          ring
        have hε₂ : t < ε := by
          dsimp [t]
          have hmin : min (ε / 2) ((ρ - dist z e) / 2) ≤ ε / 2 := min_le_left _ _
          have hhalf : ε / 2 < ε := by linarith
          exact lt_of_le_of_lt hmin hhalf
        rw [dist_eq_norm]
        rw [hmain]
        exact hε₂
      have hce : dist c e < ρ := by
        have htria : dist c e ≤ dist c z + dist z e := dist_triangle c z e
        have hcz : dist c z = t := by
          -- dist c z = ‖c - z‖ = ‖t n‖ = t
          dsimp [c]
          have hzcn : ‖(z + t • n) - z‖ = t * ‖n‖ := by
            rw [show (z + t • n) - z = t • n by abel]
            rw [norm_smul]
            rw [Real.norm_eq_abs]
            rw [abs_of_nonneg (le_of_lt htpos)]
          have hmain : ‖(z + t • n) - z‖ = t := by
            rw [hzcn, hnn₁]
            ring
          rw [dist_eq_norm]
          rw [hmain]
        have ht₂ : t ≤ (ρ - dist z e) / 2 := min_le_right (ε / 2) ((ρ - dist z e) / 2)
        nlinarith [htria, hcz, ht₂, hze]
      have hcball : c ∈ Metric.ball e ρ := (Metric.mem_ball.mpr hce)
      have hφc : signedLineFunc e w c < 0 := by
        have hlin := signedLineFunc_add_smul e w z n t
        have hφz0 : signedLineFunc e w z = 0 := hφ0
        have hdetmul : t * det2 n w < 0 := by
          exact mul_neg_of_pos_of_neg htpos hdetn
        rw [hlin, hφz0, zero_add]
        exact hdetmul
      have hcC : c ∈ flatComponent f p := (hiff c hcball).mpr hφc
      exact ⟨c, hcC, hdist⟩
    · -- z ∉ interior C (C is open)
      intro hzi
      have hzC : z ∈ flatComponent f p := by rwa [hinteq] at hzi
      have hneg : signedLineFunc e w z < 0 := (hiff z hzball).1 hzC
      linarith



/-- **The frontier is locally segment-closed**: with the chord data at a
degenerate frontier point `e` of the flat component `C` (unit `w`, radius
`ρ`, frontier = chord `{φ_w = 0}` inside `B(e,ρ)`), any other frontier
point `e'` within `B(e,ρ)` makes the whole straight segment `[e, e']` a
frontier set of `C`: the affine functional `φ_w` vanishes identically on
the segment (it vanishes at `e` and at `e'`), and every point of the
segment stays in `B(e,ρ)` (balls are convex).  This is the local building
block toward showing the frontier arcs of `C` are straight segments. -/
theorem frontier_segment_is_frontier {a : ℝ} {f : ℝ² → ℝ³}
    (hf : IsMoebiusEmbedding a f) (ha : 0 < a) {p e w : ℝ²} {ρ : ℝ}
    (heS : e ∈ stripInterior) (heF : e ∈ frontier (flatComponent f p))
    (hw₁ : ‖w‖ = 1) (hρ : 0 < ρ) (hballS : Metric.ball e ρ ⊆ stripInterior)
    (hchord : ∀ z : ℝ², z ∈ Metric.ball e ρ →
      (z ∈ frontier (flatComponent f p) ↔ signedLineFunc e w z = 0))
    {e' : ℝ²} (he'ball : e' ∈ Metric.ball e ρ)
    (he'F : e' ∈ frontier (flatComponent f p)) :
    ∀ t ∈ Set.Icc (0 : ℝ) 1, e + t • (e' - e) ∈ frontier (flatComponent f p) := by
  intro t ht
  have hte : t ≤ (1 : ℝ) := (Set.mem_Icc.mp ht).2
  have ht0 : 0 ≤ t := (Set.mem_Icc.mp ht).1
  -- φ_w vanishes at both ends, so on the whole segment
  have hφseg : signedLineFunc e w (e + t • (e' - e)) = 0 := by
    have hlin := signedLineFunc_affine_segment e w e e' t
    have hφe : signedLineFunc e w e = 0 := signedLineFunc_self e w
    have hφe' : signedLineFunc e w e' = 0 := (hchord e' he'ball).1 he'F
    rw [hlin, hφe, hφe', sub_zero, mul_zero, add_zero]
  -- the segment point stays inside the ball
  have hzball : e + t • (e' - e) ∈ Metric.ball e ρ := by
    have hdist : dist e (e + t • (e' - e)) < ρ := by
      have hn : ‖e - (e + t • (e' - e))‖ = t * ‖e' - e‖ := by
        rw [show e - (e + t • (e' - e)) = -(t • (e' - e)) by abel]
        rw [norm_neg]
        rw [norm_smul]
        rw [Real.norm_eq_abs]
        rw [abs_of_nonneg ht0]
      have hmain : ‖e - (e + t • (e' - e))‖ < ρ := by
        rw [hn]
        have hle : t * ‖e' - e‖ ≤ ‖e' - e‖ := by
          calc
            t * ‖e' - e‖ ≤ 1 * ‖e' - e‖ := mul_le_mul_of_nonneg_right hte (norm_nonneg _)
            _ = ‖e' - e‖ := by ring
        have hlt : ‖e' - e‖ < ρ := by
          have hmem : dist e' e < ρ := (Metric.mem_ball.mp he'ball)
          rwa [dist_eq_norm] at hmem
        exact lt_of_le_of_lt hle hlt
      rw [dist_eq_norm]
      exact hmain
    exact (Metric.mem_ball.mpr (by simpa [dist_comm] using hdist))
  exact (hchord (e + t • (e' - e)) hzball).mpr hφseg
end Submission.PaperBand
