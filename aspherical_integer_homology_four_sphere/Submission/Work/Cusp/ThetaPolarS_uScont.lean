/-
# The shifted perimeter lift `uS c` is continuous on the shifted wedges

`uS c p = c + Int.fract (u p - c)` is the lift of the circle-valued perimeter parameter `u` of
`Work.Cusp.Basic`/`Charts.lean` taking its values in `[c, c+1)`, and

`wedgeS c k = {p | 0 < nrm p ∧ Int.fract (u p - c) ∈ (k/4, (k+1)/4)}`

is the `c`-shifted `k`-th wedge of directions.  On it the lift has to be continuous: the two
functions it is built from, `u` and `Int.fract (· - c)`, each have exactly one jump, and the
jumps compensate.

More precisely there are two kinds of points of `wedgeS c k`.

* Points whose direction is not the corner `e = (1,1)`: here `u` is continuous
  (`Work.Cusp.u_continuousAt_off_corner`), and since `Int.fract (u p - c) > k/4 ≥ 0` the
  fractional part is continuous at `u p`; so `uS c = (c + Int.fract (· - c)) ∘ u` is continuous.

* Points on the ray through `e` (`bnd p = e`): here `u` jumps between `0` and `1` across the ray
  and `c + Int.fract (· - c)` jumps at the integers, and the two jumps compensate because
  `Int.fract (1 - c) = Int.fract (-c)`.  Concretely, near such a `p` the plane is covered by the
  two closed cones `S0 = {0 < p 0 ∧ |p 1| ≤ p 0}` (over the right edge of the square, where
  `u = (1 - p₁/p₀)/8`) and `S3 = {|p 0| ≤ p 1}` (over the top edge, where `u ≡ (7 + p₀/p₁)/8`
  modulo `1`); on `S0` the function `uS c` agrees with the continuous function
  `c + Int.fract ((1 - p₁/p₀)/8 - c)`, on `S3` with `c + Int.fract ((7 + p₀/p₁)/8 - c)`, and the
  two agree at the ray.  `tendsto_of_cover` (two closed pieces covering a neighbourhood, along
  both of which the *same* function `uS c` is the limit) then gives continuity.

(The statement proved here is the same one as `Work.Cusp.uS_continuousOn_wedgeS`, proved
independently in a sibling file of this chapter; the two proofs use different decompositions of
the plane at the corner ray.)
-/
import Mathlib
import Submission.Work.Cusp.Basic
import Submission.Work.Cusp.Charts
import Submission.Work.Cusp.smul_bnd
import Submission.Work.Cusp.u_continuousAt_off_corner

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open scoped Real InnerProductSpace Topology
open Filter

noncomputable section

namespace Work.Cusp

/-! ### Coordinates -/

/-- The coordinate projection `p ↦ p i` of `E2 = ℝ²` is continuous. -/
private lemma continuous_coord_E2 (i : Fin 2) : Continuous (fun p : E2 => p i) :=
  (continuous_apply i).comp (PiLp.continuous_ofLp 2 (fun _ : Fin 2 => ℝ))

/-- Coordinates of `bnd p = (nrm p)⁻¹ • p`. -/
private lemma bnd_apply (p : E2) (i : Fin 2) : bnd p i = (nrm p)⁻¹ * p i := by simp [bnd]

/-! ### The two edge functions of `uPerim` used at the corner ray -/

/-- The affine branch of `u` over the right edge of the square: on `{0 < p 0, |p 1| ≤ p 0}` the
direction of `p` is `(1, p₁/p₀)` and `u p = (1 - p₁/p₀)/8`. -/
private def gR : E2 → ℝ := fun p => (1 - p 1 / p 0) / 8

/-- The affine branch of `u` over the top edge of the square: on `{|p 0| < p 1}` the direction of
`p` is `(p₀/p₁, 1)` and `u p = (7 + p₀/p₁)/8`; on the whole cone `{|p 0| ≤ p 1}` the same expression
equals `u p` modulo the integer `1`. -/
private def gT : E2 → ℝ := fun p => (7 + p 0 / p 1) / 8

private lemma continuousAt_gR {p : E2} (h : p 0 ≠ 0) : ContinuousAt gR p := by
  have h1 : ContinuousAt (fun a : E2 => a 1 / a 0) p :=
    (continuous_coord_E2 1).continuousAt.div (continuous_coord_E2 0).continuousAt h
  have h2 : ContinuousAt (fun a : E2 => 1 - a 1 / a 0) p := continuousAt_const.sub h1
  show ContinuousAt (fun a : E2 => (1 - a 1 / a 0) / 8) p
  exact h2.div_const 8

private lemma continuousAt_gT {p : E2} (h : p 1 ≠ 0) : ContinuousAt gT p := by
  have h1 : ContinuousAt (fun a : E2 => a 0 / a 1) p :=
    (continuous_coord_E2 0).continuousAt.div (continuous_coord_E2 1).continuousAt h
  have h2 : ContinuousAt (fun a : E2 => 7 + a 0 / a 1) p := continuousAt_const.add h1
  show ContinuousAt (fun a : E2 => (7 + a 0 / a 1) / 8) p
  exact h2.div_const 8

/-! ### `u` on the two cones through the corner ray -/

/-- On the cone `{0 < p 0, |p 1| ≤ p 0}` (the cone over the right edge of the square) the
perimeter parameter is the right-edge branch `gR`. -/
private lemma u_eq_gR {p : E2} (h0 : 0 < p 0) (h1 : |p 1| ≤ p 0) : u p = gR p := by
  have hnrm : nrm p = p 0 := by
    simp only [nrm, abs_of_nonneg (le_of_lt h0)]
    exact max_eq_left h1
  have hb0 : bnd p 0 = 1 := by rw [bnd_apply, hnrm, inv_mul_cancel₀ (ne_of_gt h0)]
  have hb1 : bnd p 1 = p 1 / p 0 := by rw [bnd_apply, hnrm, div_eq_inv_mul]
  have hu : uPerim (bnd p) = (1 - bnd p 1) / 8 := by rw [uPerim, ite_eq_left hb0]
  rw [u, hu, hb1, gR]

/-- On the cone `{|p 0| < p 1}` (the cone over the interior of the top edge of the square) the
perimeter parameter is the top-edge branch `gT`. -/
private lemma u_eq_gT {p : E2} (h : |p 0| < p 1) : u p = gT p := by
  have hp1 : 0 < p 1 := lt_of_le_of_lt (abs_nonneg _) h
  have hle : |p 0| ≤ p 1 := le_of_lt h
  have hnrm : nrm p = p 1 := by
    simp only [nrm, abs_of_pos hp1]
    exact max_eq_right hle
  have hb1 : bnd p 1 = 1 := by rw [bnd_apply, hnrm, inv_mul_cancel₀ (ne_of_gt hp1)]
  have hb0 : bnd p 0 = p 0 / p 1 := by rw [bnd_apply, hnrm, div_eq_inv_mul]
  have hq1 : bnd p 1 ≠ -1 := by rw [hb1]; norm_num
  have hq0 : bnd p 0 ≠ 1 := by
    rw [hb0]; intro hh
    have hpe : p 0 = p 1 := (div_eq_one_iff_eq (ne_of_gt hp1)).mp hh
    rw [hpe, abs_of_pos hp1] at h
    exact lt_irrefl (p 1) h
  have hq0' : bnd p 0 ≠ -1 := by
    rw [hb0]; intro hh
    have hpe : p 0 = -1 * p 1 := (div_eq_iff (ne_of_gt hp1)).mp hh
    have habs : |p 0| = p 1 := by
      rw [hpe, show (-1 : ℝ) * p 1 = -(p 1) by ring, abs_neg, abs_of_pos hp1]
    linarith [(abs_lt.mp h).2]
  rw [u, uPerim, ite_eq_right hq0, ite_eq_right hq1, ite_eq_right hq0', hb0, gT]

/-- On the whole cone `{|p 0| ≤ p 1}` the top-edge branch `gT` equals `u` modulo the integer `1`:
either `p` is in the open cone (`u p = gT p`) or `p` lies on the corner ray `p 0 = p 1 > 0`, where
`u p = 0` and `gT p = 1`. -/
private lemma u_eq_gT_or {p : E2} (h : |p 0| ≤ p 1) : u p = gT p ∨ u p = gT p - 1 := by
  by_cases h1 : p 1 = 0
  · -- `|p 0| ≤ 0`, so `p = 0` and `u 0 = 7/8 = gT 0`
    have hp0 : p 0 = 0 := abs_eq_zero.mp (le_antisymm (by rwa [h1] at h) (abs_nonneg _))
    have hp : p = 0 := by ext i; fin_cases i <;> simp [hp0, h1]
    left
    have hu : u p = 7 / 8 := by
      rw [hp, u, show bnd (0 : E2) = 0 by simp [bnd]]
      rw [uPerim]; norm_num
    rw [hu, hp, gT]; norm_num
  · have hp1 : 0 < p 1 := lt_of_le_of_ne (le_trans (abs_nonneg _) h) (Ne.symm h1)
    have hnrm : nrm p = p 1 := by
      simp only [nrm, abs_of_pos hp1]
      exact max_eq_right h
    have hb1 : bnd p 1 = 1 := by rw [bnd_apply, hnrm, inv_mul_cancel₀ (ne_of_gt hp1)]
    have hb0 : bnd p 0 = p 0 / p 1 := by rw [bnd_apply, hnrm, div_eq_inv_mul]
    have hq1 : bnd p 1 ≠ -1 := by rw [hb1]; norm_num
    by_cases hq0 : bnd p 0 = 1
    · -- the corner ray `p 0 = p 1`: `u p = 0` and `gT p = 1`
      right
      have hp0eq : p 0 = p 1 := (div_eq_one_iff_eq (ne_of_gt hp1)).mp (by rwa [hb0] at hq0)
      have hu : u p = 0 := by rw [u, uPerim, ite_eq_left hq0, hb1]; norm_num
      have hg : gT p = 1 := by rw [gT, hp0eq, div_self (ne_of_gt hp1)]; norm_num
      rw [hu, hg]; norm_num
    · by_cases hq0' : bnd p 0 = -1
      · -- the ray `p 0 = -p 1` with `p 1 > 0`: both branches give `3/4`
        left
        have hp0eq : p 0 = -p 1 := by
          have hh : p 0 = -1 * p 1 := (div_eq_iff (ne_of_gt hp1)).mp (by rwa [hb0] at hq0')
          linarith
        have hu : u p = (5 + bnd p 1) / 8 := by
          rw [u, uPerim, ite_eq_right hq0, ite_eq_right hq1, ite_eq_left hq0']
        have hg : gT p = 3 / 4 := by rw [gT, hp0eq]; field_simp; ring
        rw [hu, hb1, hg]; norm_num
      · -- the open cone
        left
        have hu : u p = (7 + bnd p 0) / 8 := by
          rw [u, uPerim, ite_eq_right hq0, ite_eq_right hq1, ite_eq_right hq0']
        rw [hu, hb0, gT]

/-- **The top-edge branch agrees with `uS c` modulo the fractional part** on the closed cone
`{|p 0| ≤ p 1}`. -/
private lemma uS_eq_gT (c : ℝ) {p : E2} (h : |p 0| ≤ p 1) :
    uS c p = c + Int.fract (gT p - c) := by
  rcases u_eq_gT_or h with h' | h'
  · rw [uS, h']
  · rw [uS, h']
    have : gT p - 1 - c = (gT p - c) + ((-1 : ℤ) : ℝ) := by push_cast; ring
    rw [this, Int.fract_add_intCast]

/-! ### The two closed pieces at the corner ray -/

/-- The cone over the right edge of the square. -/
private def S0 : Set E2 := {p | 0 < p 0 ∧ |p 1| ≤ p 0}

/-- The cone over the top edge of the square (closed, so it contains the corner ray). -/
private def S3 : Set E2 := {p | |p 0| ≤ p 1}

/-! ### Gluing two pieces covering a neighbourhood -/

/-- **Gluing lemma.**  If `f` tends to `y` along each of two pieces `s` and `t`, and `s ∪ t` is a
neighbourhood of `p`, then `f` tends to `y` at `p`.  (In particular `f` is continuous at `p` when
`y = f p`.) -/
private lemma tendsto_of_cover {f : E2 → ℝ} {p : E2} {y : ℝ} {s t : Set E2}
    (hcover : ∀ᶠ a in 𝓝 p, a ∈ s ∪ t)
    (hs : Tendsto f (𝓝[s] p) (𝓝 y)) (ht : Tendsto f (𝓝[t] p) (𝓝 y)) :
    Tendsto f (𝓝 p) (𝓝 y) := by
  intro V hV
  have hs' : f ⁻¹' V ∈ 𝓝[s] p := hs hV
  have ht' : f ⁻¹' V ∈ 𝓝[t] p := ht hV
  rw [Metric.mem_nhdsWithin_iff] at hs' ht'
  obtain ⟨ε₂, hε₂, h₂⟩ := hs'
  obtain ⟨ε₃, hε₃, h₃⟩ := ht'
  rw [Metric.eventually_nhds_iff] at hcover
  obtain ⟨ε₁, hε₁, hcov⟩ := hcover
  rw [Filter.mem_map, Metric.mem_nhds_iff]
  refine ⟨min ε₁ (min ε₂ ε₃), lt_min hε₁ (lt_min hε₂ hε₃), ?_⟩
  intro a ha
  have ha1 : dist a p < ε₁ := lt_of_lt_of_le ha (min_le_left _ _)
  have ha2 : dist a p < ε₂ :=
    lt_of_lt_of_le ha (le_trans (min_le_right _ _) (min_le_left _ _))
  have ha3 : dist a p < ε₃ :=
    lt_of_lt_of_le ha (le_trans (min_le_right _ _) (min_le_right _ _))
  rcases hcov ha1 with hmem | hmem
  · exact h₂ ⟨Metric.mem_ball.mpr ha2, hmem⟩
  · exact h₃ ⟨Metric.mem_ball.mpr ha3, hmem⟩

/-- Continuity at a non-integer point, transported through the shift by `c`. -/
private lemma continuousAt_fract_offset {c x : ℝ} (h : Int.fract (x - c) ≠ 0) :
    ContinuousAt (fun t : ℝ => c + Int.fract (t - c)) x := by
  have hx : ContinuousAt Int.fract (x - c) :=
    continuousAt_fract (fun hEq => h (by rw [hEq, Int.fract_intCast]))
  have hsub : ContinuousAt (fun t : ℝ => t - c) x :=
    continuousAt_id.sub continuousAt_const
  have hcomp : ContinuousAt (fun t : ℝ => Int.fract (t - c)) x :=
    Filter.Tendsto.comp hx hsub
  exact hcomp.const_add c

/-! ### The theorem -/

theorem ThetaPolarS_uScont (c : ℝ) (k : Fin 4) : ContinuousOn (uS c) (wedgeS c k) := by
  intro p hp
  rw [wedgeS] at hp
  obtain ⟨hnrm, hfrac⟩ := hp
  rw [Set.mem_Ioo] at hfrac
  have hpos : 0 < Int.fract (u p - c) := lt_of_le_of_lt (by positivity) hfrac.1
  have hne : Int.fract (u p - c) ≠ 0 := ne_of_gt hpos
  by_cases hb : bnd p = !₂[(1 : ℝ), (1 : ℝ)]
  · -- `p` lies on the corner ray through `(1,1)`: the two jumps compensate
    have hp0 : p 0 = nrm p := by
      have h := congrArg (fun x : E2 => x 0) (smul_bnd p).symm
      rw [hb] at h
      simpa [PiLp.smul_apply] using h
    have hp1 : p 1 = nrm p := by
      have h := congrArg (fun x : E2 => x 1) (smul_bnd p).symm
      rw [hb] at h
      simpa [PiLp.smul_apply] using h
    have hS0 : p ∈ S0 := ⟨by rw [hp0]; exact hnrm, by rw [hp1, hp0, abs_of_pos hnrm]⟩
    have hS3 : p ∈ S3 := by
      show |p 0| ≤ p 1
      rw [hp0, hp1, abs_of_pos hnrm]
    -- the fractional parts at the two branch values
    have hfrR : Int.fract (gR p - c) ≠ 0 := by
      have hgu : gR p = u p := (u_eq_gR hS0.1 hS0.2).symm
      rw [hgu]; exact hne
    have hfrT : Int.fract (gT p - c) ≠ 0 := by
      have hu0 : u p = 0 := by
        rw [u, hb, uPerim, ite_eq_left (by simp)]; norm_num
      have hg1 : gT p = 1 := by
        rw [gT, hp1, hp0, div_self (ne_of_gt hnrm)]; norm_num
      have : gT p - c = (u p - c) + ((1 : ℤ) : ℝ) := by rw [hg1, hu0]; push_cast; ring
      rw [this, Int.fract_add_intCast]; exact hne
    -- `uS c` agrees with the continuous functions of the two branches on the two pieces
    have hs : ContinuousWithinAt (uS c) S0 p := by
      have hcont : ContinuousWithinAt (fun a : E2 => c + Int.fract (gR a - c)) S0 p :=
        (continuousAt_fract_offset (x := gR p) hfrR).comp_continuousWithinAt
          (continuousAt_gR (ne_of_gt hS0.1)).continuousWithinAt
      refine hcont.congr (fun y hy => ?_) ?_
      · simp only [uS]
        rw [u_eq_gR hy.1 hy.2]
      · simp only [uS]
        rw [u_eq_gR hS0.1 hS0.2]
    have ht : ContinuousWithinAt (uS c) S3 p := by
      have hcont : ContinuousWithinAt (fun a : E2 => c + Int.fract (gT a - c)) S3 p :=
        (continuousAt_fract_offset (x := gT p) hfrT).comp_continuousWithinAt
          (continuousAt_gT (ne_of_gt (by rw [hp1]; exact hnrm))).continuousWithinAt
      refine hcont.congr (fun y hy => ?_) ?_
      · exact uS_eq_gT c hy
      · exact uS_eq_gT c hS3
    -- the two pieces cover a neighbourhood of `p`
    have hcover : ∀ᶠ a in 𝓝 p, a ∈ S0 ∪ S3 := by
      have h1 : ∀ᶠ a in 𝓝 p, 0 < a 0 :=
        (isOpen_lt continuous_const (continuous_coord_E2 0)).mem_nhds (by
          show 0 < p 0
          rw [hp0]; exact hnrm)
      have h2 : ∀ᶠ a in 𝓝 p, 0 < a 1 :=
        (isOpen_lt continuous_const (continuous_coord_E2 1)).mem_nhds (by
          show 0 < p 1
          rw [hp1]; exact hnrm)
      refine (h1.and h2).mono (fun a ha => ?_)
      obtain ⟨ha0, ha1⟩ := ha
      rcases le_total (a 1) (a 0) with hh | hh
      · left
        exact ⟨ha0, by rw [abs_of_pos ha1]; exact hh⟩
      · right
        show |a 0| ≤ a 1
        rw [abs_of_pos ha0]
        exact hh
    have hcont : ContinuousAt (uS c) p := tendsto_of_cover hcover hs ht
    exact hcont.continuousWithinAt
  · -- off the corner ray, `u` is continuous and so is the fractional part at `u p`
    have hu : ContinuousAt u p := u_continuousAt_off_corner hnrm hb
    have hg : ContinuousAt (fun t : ℝ => c + Int.fract (t - c)) (u p) :=
      continuousAt_fract_offset (x := u p) hne
    have hcomp : ContinuousAt (fun q : E2 => c + Int.fract (u q - c)) p := hg.comp hu
    have huc : ContinuousAt (uS c) p := hcomp
    exact huc.continuousWithinAt

end Work.Cusp
