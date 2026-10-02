import Mathlib
import Submission.Work.GATE.Defs
import Submission.Work.GATE.Segment.seg_tongues
import Submission.Work.GATE.Segment.exists_segment_near
import Submission.Work.GATE.Segment.blowup_at_endpoint
import Submission.Work.GATE.Segment.crossing_two_tongues

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open Classical Filter Set
open scoped Topology

set_option autoImplicit false
set_option linter.unusedVariables false

noncomputable section

namespace Work.GATE.Segment

open LeanEval.ComplexAnalysis (Mandelbar)

/-! ## Elementary distance formulae on a straight segment

For `y p : ℂ` and `t : ℝ`, the point `y + t (p - y)` lies on the straight line through `y` and
`p`, and its distance to `y` respectively to `p` is `|t| · dist y p` respectively
`|1 - t| · dist y p`.  These are the two estimates by which the *interior* of the segment
`y → p` is located inside the ball around `y` of radius `dist y p`. -/

theorem dist_seg_left (y p : ℂ) (t : ℝ) :
    dist y (y + ((t : ℝ) : ℂ) * (p - y)) = |t| * dist y p := by
  have hpp : dist y p = ‖p - y‖ := by rw [dist_eq_norm, norm_sub_rev]
  have hYeq : y + ((t : ℝ) : ℂ) * (p - y) - y = ((t : ℝ) : ℂ) * (p - y) := by ring
  rw [hpp, dist_eq_norm, norm_sub_rev, hYeq, norm_mul, Complex.norm_real, Real.norm_eq_abs]

theorem dist_seg_right (y p : ℂ) (t : ℝ) :
    dist (y + ((t : ℝ) : ℂ) * (p - y)) p = |1 - t| * dist y p := by
  have hpp : dist y p = ‖p - y‖ := by rw [dist_eq_norm, norm_sub_rev]
  have hsub : y + ((t : ℝ) : ℂ) * (p - y) - p = (((t - 1 : ℝ)) : ℂ) * (p - y) := by
    push_cast; ring
  rw [hpp, dist_eq_norm, hsub, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_sub_comm]

/-- **A point of the complement at distance `dist y p` from `y` is a frontier point.**  If the
open ball about `y` of radius `dist y p` is contained in the open set `Nm` and `p ∉ Nm`, then `p`
is a *frontier* point of `Nm`: the points `y + (1 - s)(p - y)`, `s ∈ (0, 1)`, lie in that ball and
converge to `p` as `s → 0`. -/
theorem mem_frontier_of_forall_lt {Nm : Set ℂ} (hOpen : IsOpen Nm) {y p : ℂ} (hp : p ∉ Nm)
    (hpos : 0 < dist y p) (hnear : ∀ z : ℂ, dist y z < dist y p → z ∈ Nm) :
    p ∈ frontier Nm := by
  rw [hOpen.frontier_eq]
  refine ⟨?_, hp⟩
  rw [Metric.mem_closure_iff]
  intro ε hε
  have hden : 0 < dist y p + ε := by linarith
  set s : ℝ := ε / (dist y p + ε) with hsdef
  have hspos : 0 < s := by rw [hsdef]; exact div_pos hε hden
  have hslt : s < 1 := by
    rw [hsdef, div_lt_one hden]
    linarith
  refine ⟨y + ((1 - s : ℝ) : ℂ) * (p - y), hnear _ ?_, ?_⟩
  · rw [dist_seg_left, abs_of_pos (by linarith : (0 : ℝ) < 1 - s)]
    calc (1 - s) * dist y p < 1 * dist y p := mul_lt_mul_of_pos_right (by linarith) hpos
      _ = dist y p := one_mul _
  · have hs1 : (1 : ℝ) - (1 - s) = s := by ring
    rw [dist_comm, dist_seg_right, hs1, abs_of_pos hspos]
    calc s * dist y p = (ε / (dist y p + ε)) * dist y p := by rw [hsdef]
      _ < ε := by
        rw [div_mul_eq_mul_div, div_lt_iff₀ hden]
        nlinarith [hε, hpos]

/-- **The parabolic segment of §2.1 of the design.**  At every scale `r > 0` there is a straight
segment from a point `y ∈ Nm` to a point `p ∈ frontier Nm ∩ ball c₀ r` whose *interior* (the
half-open segment `y + [0,1) (p - y)`, which contains `y` itself) lies in `Nm ∩ ball c₀ r`, and
which carries a parameter of the `b`-tongue and a parameter of the `ι b`-tongue, both escaping.

The construction is the one of `seg_tongues`, but with the segment *closed* at the frontier point
`p`: `p` is the frontier point nearest to `y`, so the open ball about `y` of radius `dist y p`
lies in `Nm`, while the phase `Re trans` blows up like `-∞` at `p ∈ frontier Nm`; continuity of
the transit coordinate along the segment then forces it to cross both leak lattices. -/
theorem seg_tongues_parabolic {c₀ : ℂ} {Nm : Set ℂ} (hOpen : IsOpen Nm)
    (hfront : c₀ ∈ frontier Nm) (TD : Work.GATE.TransitData c₀ Nm) {r : ℝ} (hr : 0 < r) :
    ∃ y p : ℂ, p ∈ frontier Nm ∩ Metric.ball c₀ r ∧
      (∀ μ ∈ Set.Ico (0 : ℝ) 1,
        y + ((μ : ℝ) : ℂ) * (p - y) ∈ Nm ∩ Metric.ball c₀ r) ∧
      ∃ e₁ ∈ segment ℝ y p, ∃ e₂ ∈ segment ℝ y p,
        e₁ ∉ LeanEval.ComplexAnalysis.Mandelbar ∧
        e₂ ∉ LeanEval.ComplexAnalysis.Mandelbar ∧
        Work.GATE.bTongue TD.trans TD.xLeak TD.r₀ e₁ ∧
        Work.GATE.iotaTongue TD.trans TD.xLeak TD.r₀ e₂ := by
  have hR : 0 < min TD.ρ r := lt_min TD.hρ hr
  obtain ⟨y, p, _hyNm, hpnot, hpos, hnear, hpball, hsegball, hsegNm⟩ :=
    exists_segment_near (r := min TD.ρ r) hOpen hfront hR
  -- (1) `p` is a frontier point
  have hpfron : p ∈ frontier Nm := mem_frontier_of_forall_lt hOpen hpnot hpos hnear
  -- (2) all points of the segment lie in the domain of the transit data
  have hleρ : min TD.ρ r / 2 ≤ TD.ρ := by
    have := min_le_left TD.ρ r
    linarith [TD.hρ]
  have hler : min TD.ρ r / 2 ≤ r := by
    have := min_le_right TD.ρ r
    linarith [hr]
  have hpballρ : p ∈ Metric.ball c₀ TD.ρ := Metric.ball_subset_ball hleρ hpball
  have hseg_ρ : ∀ μ ∈ Set.Ico (0 : ℝ) 1,
      y + ((μ : ℝ) : ℂ) * (p - y) ∈ Nm ∩ Metric.ball c₀ TD.ρ := by
    intro μ hμ
    exact ⟨hsegNm μ hμ, Metric.ball_subset_ball hleρ (hsegball μ ⟨hμ.1, le_of_lt hμ.2⟩)⟩
  -- (3) the phase blows up at `p`, so some point of the segment has `Re trans < (trans y).re - 2`
  obtain ⟨μ₀, hμ₀, hμ₀'⟩ := blowup_at_endpoint (M := (TD.trans y).re - 2)
    (TD.blowup p ⟨hpfron, hpballρ⟩) hsegNm
  have hμ₀_le : μ₀ ≤ 1 := le_of_lt hμ₀.2
  -- (4) the transit coordinate is continuous along the segment up to that point
  have hmaps : MapsTo (fun μ : ℝ => y + ((μ : ℝ) : ℂ) * (p - y)) (Set.Icc (0 : ℝ) μ₀)
      (Nm ∩ Metric.ball c₀ TD.ρ) :=
    fun μ hμ => hseg_ρ μ ⟨hμ.1, lt_of_le_of_lt hμ.2 hμ₀.2⟩
  have hcont : Continuous fun μ : ℝ => y + ((μ : ℝ) : ℂ) * (p - y) :=
    continuous_const.add (Complex.continuous_ofReal.mul continuous_const)
  have hFcont : ContinuousOn
      (fun μ : ℝ => (TD.trans (y + ((μ : ℝ) : ℂ) * (p - y))).re) (Set.Icc (0 : ℝ) μ₀) :=
    Complex.continuous_re.comp_continuousOn (TD.cont.comp hcont.continuousOn hmaps)
  have hF0 : (fun μ : ℝ => (TD.trans (y + ((μ : ℝ) : ℂ) * (p - y))).re) 0
      = (TD.trans y).re := by simp
  -- (5) the two lattice crossings
  have hμ₀pos : 0 < μ₀ := by
    by_contra hcon
    have hcon' : μ₀ ≤ 0 := le_of_not_gt hcon
    have h0 : μ₀ = 0 := le_antisymm hcon' hμ₀.1
    rw [h0] at hμ₀'
    simp at hμ₀'
    linarith
  obtain ⟨μ₁, hμ₁, μ₂, hμ₂, k, l, hk, hl⟩ :=
    crossing_lattice (f := fun μ : ℝ => (TD.trans (y + ((μ : ℝ) : ℂ) * (p - y))).re)
      (a := 0) (b := μ₀) (A₀ := (TD.trans y).re) (x := TD.xLeak) hμ₀pos hFcont hF0
      (by simpa using hμ₀')
  have hμ₁lt : μ₁ < 1 := lt_of_le_of_lt hμ₁.2 hμ₀.2
  have hμ₂lt : μ₂ < 1 := lt_of_le_of_lt hμ₂.2 hμ₀.2
  have hμ₁Icc : μ₁ ∈ Set.Icc (0 : ℝ) 1 := ⟨hμ₁.1, le_of_lt hμ₁lt⟩
  have hμ₂Icc : μ₂ ∈ Set.Icc (0 : ℝ) 1 := ⟨hμ₂.1, le_of_lt hμ₂lt⟩
  have he₁mem : y + ((μ₁ : ℝ) : ℂ) * (p - y) ∈ Nm ∩ Metric.ball c₀ TD.ρ :=
    hseg_ρ μ₁ ⟨hμ₁.1, hμ₁lt⟩
  have he₂mem : y + ((μ₂ : ℝ) : ℂ) * (p - y) ∈ Nm ∩ Metric.ball c₀ TD.ρ :=
    hseg_ρ μ₂ ⟨hμ₂.1, hμ₂lt⟩
  have hk' : (TD.trans (y + ((μ₁ : ℝ) : ℂ) * (p - y))).re = TD.xLeak + (k : ℝ) := by
    simpa using hk
  have hl' : (TD.trans (y + ((μ₂ : ℝ) : ℂ) * (p - y))).re = TD.xLeak + 1 / 2 + (l : ℝ) := by
    simpa using hl
  have hb₁ : Work.GATE.bTongue TD.trans TD.xLeak TD.r₀ (y + ((μ₁ : ℝ) : ℂ) * (p - y)) :=
    Work.GATE.bTongue_of_re_eq hk'
      (lt_of_le_of_lt (TD.height _ he₁mem) (by linarith [TD.hr₀]))
  have hi₂ : Work.GATE.iotaTongue TD.trans TD.xLeak TD.r₀ (y + ((μ₂ : ℝ) : ℂ) * (p - y)) :=
    Work.GATE.iotaTongue_of_re_eq hl'
      (lt_of_le_of_lt (TD.height _ he₂mem) (by linarith [TD.hr₀]))
  have he₁M : (y + ((μ₁ : ℝ) : ℂ) * (p - y)) ∉ Mandelbar := TD.escape_b _ he₁mem hb₁
  have he₂M : (y + ((μ₂ : ℝ) : ℂ) * (p - y)) ∉ Mandelbar := TD.escape_iota _ he₂mem hi₂
  -- (6) the two escape parameters lie on the segment
  have hseg_split : ∀ μ ∈ Set.Icc (0 : ℝ) 1, y + ((μ : ℝ) : ℂ) * (p - y) ∈ segment ℝ y p := by
    intro μ hμ
    rw [segment_eq_image']
    exact ⟨μ, hμ, by simp [Complex.real_smul]⟩
  -- (7) assemble
  refine ⟨y, p, ⟨hpfron, Metric.ball_subset_ball hler hpball⟩, ?_,
    y + ((μ₁ : ℝ) : ℂ) * (p - y), hseg_split μ₁ hμ₁Icc,
    y + ((μ₂ : ℝ) : ℂ) * (p - y), hseg_split μ₂ hμ₂Icc,
    he₁M, he₂M, hb₁, hi₂⟩
  intro μ hμ
  exact ⟨hsegNm μ hμ, Metric.ball_subset_ball hler (hsegball μ ⟨hμ.1, le_of_lt hμ.2⟩)⟩

end Work.GATE.Segment
