/-
# Continuity of the shifted perimeter lift `uS c` on the shifted wedges

`uS c p = c + Int.fract (u p - c)` is the unique lift of the circle-valued perimeter parameter
`u p` (see `Work.Cusp.Basic`, `Work.Cusp.Charts`) taking values in `[c, c+1)`.  Its jumps are
exactly the directions on which `u p - c ∈ ℤ`.

`wedgeS c k = {p | 0 < nrm p ∧ Int.fract (u p - c) ∈ (k/4, (k+1)/4)}` is the `c`-shifted `k`-th
wedge of directions; on it the lift lies in the open interval `(c + k/4, c + (k+1)/4)` of length
`1/4`, and it is continuous.  This file proves that.

There are two kinds of points of `wedgeS c k` to handle.

* Points whose direction is not the corner `e = (1,1)`: here `u` is continuous
  (`Work.Cusp.u_continuousAt_off_corner`, whose only discontinuity besides the origin is the ray
  through `e`), and since `Int.fract (u p - c) > k/4 ≥ 0` the fractional part is continuous at
  `u p`, so `uS c = (c + Int.fract (· - c)) ∘ u` is continuous at `p`.

* Points on the ray through the corner `e` (`bnd p = e`, i.e. `u p = 0`): here `u` jumps between
  `0` and `1` across the ray, and `c + Int.fract (· - c)` jumps at the integers; the two jumps
  compensate, because `Int.fract (1 - c) = Int.fract (-c)`.  Away from the corner the direction is
  on one of the two edges and `u` is close to `0` (right edge) or to `1` (top edge) — this is
  `Work.Cusp.uPerim_corner_approx` — so `uS c q → c + Int.fract (-c) = uS c p`.

Note that on the ray through `e` the value of `Int.fract (u p - c) = Int.fract (-c)` is `0` when
`c ∈ ℤ`; those points are then *not* in `wedgeS c k`, consistently with the discontinuity of `uS c`
there.
-/
import Mathlib
import Submission.Work.Cusp.Basic
import Submission.Work.Cusp.Charts
import Submission.Work.Cusp.nrm_continuous
import Submission.Work.Cusp.nrm_bnd
import Submission.Work.Cusp.uPerim_mem
import Submission.Work.Cusp.bndOfU_uPerim
import Submission.Work.Cusp.uPerim_corner_approx
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

/-- The radial projection `bnd p = (nrm p)⁻¹ • p` is continuous at every point of positive sup
norm. -/
private lemma bnd_continuousAt {p : E2} (hp : 0 < nrm p) : ContinuousAt bnd p := by
  have hne : nrm p ≠ 0 := ne_of_gt hp
  have h1 : ContinuousAt (fun q : E2 => (nrm q)⁻¹) p := nrm_continuous.continuousAt.inv₀ hne
  show ContinuousAt (fun q : E2 => (nrm q)⁻¹ • q) p
  exact h1.smul continuousAt_id

/-- `Int.fract` is locally `η`-close at a non-integer point `x`: there is `δ > 0` such that
`|fract y - fract x| < η` for `|y - x| < δ`. -/
private lemma fract_continuousAt_eps {x : ℝ} (hx : x ≠ ⌊x⌋) {η : ℝ} (hη : 0 < η) :
    ∃ δ > 0, ∀ y : ℝ, |y - x| < δ → |Int.fract y - Int.fract x| < η := by
  have hc : ContinuousAt Int.fract x := continuousAt_fract hx
  have hmem : {y : ℝ | dist (Int.fract y) (Int.fract x) < η} ∈ 𝓝 x :=
    (Metric.tendsto_nhds.mp hc) η hη
  obtain ⟨δ, hδpos, hδ⟩ := Metric.mem_nhds_iff.mp hmem
  refine ⟨δ, hδpos, fun y hy => ?_⟩
  have hyb : y ∈ Metric.ball x δ := by rwa [Metric.mem_ball, Real.dist_eq]
  have h := hδ hyb
  rwa [Set.mem_ofPred_eq, Real.dist_eq] at h

/-- **Continuity of `uS c` at a point of the corner ray `bnd p = (1,1)`.**  There `u p = 0`, and
the value of `uS c` is `c + Int.fract (-c)`; the hypothesis `0 < Int.fract (u p - c)` excludes the
case `c ∈ ℤ`, in which the compensating jumps of `u` and of `Int.fract (· - c)` would not occur
(and such points are not in any `wedgeS c k`). -/
private lemma uS_continuousAt_corner (c : ℝ) {p : E2} (hp : 0 < nrm p)
    (hb : bnd p = !₂[(1:ℝ),(1:ℝ)]) (hf : 0 < Int.fract (u p - c)) :
    ContinuousAt (uS c) p := by
  have hu0 : u p = 0 := by rw [u, hb]; unfold uPerim; norm_num
  have hfrac : Int.fract (-c) ≠ 0 := by
    have h := hf
    rw [hu0, zero_sub] at h
    exact ne_of_gt h
  have hpos : 0 < Int.fract (-c) :=
    lt_of_le_of_ne (Int.fract_nonneg (-c)) (Ne.symm hfrac)
  have hnegc : (-c) ≠ ⌊-c⌋ := (Int.fract_pos).mp hpos
  have h1cfrac : Int.fract (1 - c) = Int.fract (-c) := by
    rw [show (1:ℝ) - c = 1 + (-c) by ring, Int.fract_one_add]
  have hpos1 : 0 < Int.fract (1 - c) := by rw [h1cfrac]; exact hpos
  have h1c : (1 - c) ≠ ⌊1 - c⌋ := (Int.fract_pos).mp hpos1
  have huSp : uS c p = c + Int.fract (-c) := by rw [uS, hu0, zero_sub]
  change Tendsto (uS c) (𝓝 p) (𝓝 (uS c p))
  rw [huSp, Metric.tendsto_nhds]
  intro η hη
  obtain ⟨δ1, hδ1pos, hδ1⟩ := fract_continuousAt_eps hnegc hη
  obtain ⟨δ2, hδ2pos, hδ2⟩ := fract_continuousAt_eps h1c hη
  have hε'pos : 0 < min δ1 δ2 := lt_min hδ1pos hδ2pos
  obtain ⟨δ', hδ'pos, hδ'⟩ := uPerim_corner_approx (min δ1 δ2) hε'pos
  have hcoord0 : Continuous (fun x : E2 => x 0) :=
    (continuous_apply 0).comp (PiLp.continuous_ofLp 2 (fun _ : Fin 2 => ℝ))
  have hcoord1 : Continuous (fun x : E2 => x 1) :=
    (continuous_apply 1).comp (PiLp.continuous_ofLp 2 (fun _ : Fin 2 => ℝ))
  have hbnd0 : Tendsto (fun q : E2 => (bnd q) 0) (𝓝 p) (𝓝 (1:ℝ)) := by
    have h := hcoord0.continuousAt.tendsto.comp (bnd_continuousAt hp)
    change Tendsto (fun q : E2 => (bnd q) 0) (𝓝 p) (𝓝 ((bnd p) 0)) at h
    rw [show (bnd p) 0 = 1 by rw [hb]; rfl] at h
    exact h
  have hbnd1 : Tendsto (fun q : E2 => (bnd q) 1) (𝓝 p) (𝓝 (1:ℝ)) := by
    have h := hcoord1.continuousAt.tendsto.comp (bnd_continuousAt hp)
    change Tendsto (fun q : E2 => (bnd q) 1) (𝓝 p) (𝓝 ((bnd p) 1)) at h
    rw [show (bnd p) 1 = 1 by rw [hb]; rfl] at h
    exact h
  have hnrmpos : ∀ᶠ q : E2 in 𝓝 p, 0 < nrm q :=
    (nrm_continuous.tendsto p).eventually (eventually_gt_nhds hp)
  have hq0 : ∀ᶠ q : E2 in 𝓝 p, |(bnd q) 0 - 1| < δ' :=
    ((Metric.tendsto_nhds.mp hbnd0) δ' hδ'pos).mono
      (fun q hq => by rwa [Real.dist_eq] at hq)
  have hq1 : ∀ᶠ q : E2 in 𝓝 p, |(bnd q) 1 - 1| < δ' :=
    ((Metric.tendsto_nhds.mp hbnd1) δ' hδ'pos).mono
      (fun q hq => by rwa [Real.dist_eq] at hq)
  filter_upwards [hq0, hq1, hnrmpos] with q hqq0 hqq1 hqpos
  have hqne : q ≠ 0 := fun h => by rw [h] at hqpos; simp [nrm] at hqpos
  have hbndq : nrm (bnd q) = 1 := nrm_bnd hqne
  have hdisj := hδ' (bnd q) hbndq hqq0 hqq1
  have huq : u q = uPerim (bnd q) := rfl
  have huq_nonneg : 0 ≤ u q := by rw [huq]; exact (uPerim_mem hbndq).1
  have huq_lt1 : u q < 1 := by rw [huq]; exact (uPerim_mem hbndq).2
  rcases hdisj with hlt | hgt
  · -- the direction is close to the right edge: `u` is close to `0`
    have h1 : |(u q - c) - (-c)| < δ1 := by
      rw [show (u q - c) - (-c) = u q by ring, abs_of_nonneg huq_nonneg]
      exact lt_of_lt_of_le (by rw [huq]; exact hlt) (min_le_left δ1 δ2)
    have hkey := hδ1 (u q - c) h1
    rw [Real.dist_eq, uS,
      show c + Int.fract (u q - c) - (c + Int.fract (-c))
        = Int.fract (u q - c) - Int.fract (-c) by ring]
    exact hkey
  · -- the direction is close to the top edge: `u` is close to `1`
    have hgt' : 1 - min δ1 δ2 < u q := by rw [huq]; exact hgt
    have h2 : |(u q - c) - (1 - c)| < δ2 := by
      rw [show (u q - c) - (1 - c) = u q - 1 by ring, abs_of_nonpos (by linarith)]
      linarith [hgt', min_le_right δ1 δ2]
    have hkey := hδ2 (u q - c) h2
    rw [Real.dist_eq, uS,
      show c + Int.fract (u q - c) - (c + Int.fract (-c))
        = Int.fract (u q - c) - Int.fract (-c) by ring]
    rw [h1cfrac] at hkey
    exact hkey

/-- **The shifted perimeter lift `uS c` is continuous on each shifted wedge `wedgeS c k`.** -/
theorem uS_continuousOn_wedgeS (c : ℝ) (k : Fin 4) : ContinuousOn (uS c) (wedgeS c k) := by
  intro p0 hp0
  rw [wedgeS] at hp0
  obtain ⟨hnrm, hfrac⟩ := hp0
  rw [Set.mem_Ioo] at hfrac
  have hfrac_pos : 0 < Int.fract (u p0 - c) := lt_of_le_of_lt (by positivity) hfrac.1
  by_cases hb : bnd p0 = !₂[(1:ℝ),(1:ℝ)]
  · -- the direction is the corner `(1,1)`: the two jumps compensate
    exact (uS_continuousAt_corner c hnrm hb hfrac_pos).continuousWithinAt
  · -- off the corner ray `u` is continuous, and `Int.fract (· - c)` is continuous at `u p0`
    have hu : ContinuousAt u p0 := u_continuousAt_off_corner hnrm hb
    have hg : ContinuousAt (fun x : ℝ => c + Int.fract (x - c)) (u p0) := by
      have hx : u p0 - c ≠ ⌊u p0 - c⌋ := (Int.fract_pos).mp hfrac_pos
      have h1 : ContinuousAt (fun x : ℝ => x - c) (u p0) :=
        continuousAt_id.sub continuousAt_const
      have h2 : ContinuousAt (fun x : ℝ => Int.fract (x - c)) (u p0) :=
        ContinuousAt.comp (f := fun x : ℝ => x - c) (continuousAt_fract hx) h1
      exact continuousAt_const.add h2
    exact (hg.comp hu).continuousWithinAt

end Work.Cusp
