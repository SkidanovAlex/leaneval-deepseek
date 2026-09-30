import Mathlib
import Submission.Work.ThomBordism.TwoSet.SpreadDefs

/-!
# Continuity of the spreading retraction

The flow coefficient `clamp01 (τ ν / r)` is discontinuous where `r = 0`, but the displacement
`flowCoef · (x - clampCell c hN x)` is not: it is bounded by `cellDist c x / N`, which tends to `0`
as `r(x) → 0`.  This is what makes `spreadPt`, and hence `spreadMap`, continuous.
-/

open scoped Topology unitInterval

namespace Work.ThomBordism.TwoSet

variable {j N : ℕ}

theorem cellDistCoord_eq_of_le {c : CellIdx j N} {i : Fin j} {x : IC j} (hN : 1 ≤ N)
    (h : (x i : ℝ) ≤ (c.lo i : ℝ) / (N:ℝ)) :
    cellDistCoord c i x = (c.lo i : ℝ) - (N:ℝ) * (x i : ℝ) := by
  have hNpos : (0:ℝ) < N := by exact_mod_cast hN
  have hle : ((c.lo i : ℝ)) / N ≤ ((c.hi i : ℝ)) / N :=
    div_le_div_of_nonneg_right (by exact_mod_cast c.hle i) (le_of_lt hNpos)
  have h1 : 0 ≤ (c.lo i : ℝ) - (N:ℝ) * (x i : ℝ) := by
    have := (le_div_iff₀ hNpos).mp h
    linarith
  have h2 : (N:ℝ) * (x i : ℝ) - (c.hi i : ℝ) ≤ 0 := by
    have h3 := (le_div_iff₀ hNpos).mp (le_trans h hle)
    linarith
  rw [cellDistCoord, max_eq_left (le_trans h2 h1), max_eq_right h1]

theorem cellDistCoord_eq_of_ge {c : CellIdx j N} {i : Fin j} {x : IC j} (hN : 1 ≤ N)
    (h : (c.hi i : ℝ) / (N:ℝ) ≤ (x i : ℝ)) :
    cellDistCoord c i x = (N:ℝ) * (x i : ℝ) - (c.hi i : ℝ) := by
  have hNpos : (0:ℝ) < N := by exact_mod_cast hN
  have hle : ((c.lo i : ℝ)) / N ≤ ((c.hi i : ℝ)) / N :=
    div_le_div_of_nonneg_right (by exact_mod_cast c.hle i) (le_of_lt hNpos)
  have h1 : (c.lo i : ℝ) - (N:ℝ) * (x i : ℝ) ≤ 0 := by
    have h3 := (div_le_iff₀ hNpos).mp (le_trans hle h)
    linarith
  have h2 : 0 ≤ (N:ℝ) * (x i : ℝ) - (c.hi i : ℝ) := by
    have := (div_le_iff₀ hNpos).mp h
    linarith
  rw [cellDistCoord, max_eq_right (le_trans h1 h2), max_eq_right h2]

theorem mul_abs_sub_clamp_le_cellDist (c : CellIdx j N) (hN : 1 ≤ N) (i : Fin j) (x : IC j) :
    (N:ℝ) * |(x i : ℝ) - ((clampCell c hN x) i : ℝ)| ≤ cellDist c x := by
  have hNpos : (0:ℝ) < N := by exact_mod_cast hN
  have hle : ((c.lo i : ℝ)) / N ≤ ((c.hi i : ℝ)) / N :=
    div_le_div_of_nonneg_right (by exact_mod_cast c.hle i) (le_of_lt hNpos)
  rcases le_or_gt ((x i : ℝ)) ((c.lo i : ℝ) / N) with h | h
  · have hcd := cellDistCoord_eq_of_le (c := c) (i := i) (x := x) hN h
    have hcl : ((clampCell c hN x) i : ℝ) = (c.lo i : ℝ) / N := by
      rw [clampCell_val, clampR, min_eq_right (le_trans h hle), max_eq_left h]
    rw [hcl]
    rw [abs_of_nonpos (by linarith : (x i : ℝ) - (c.lo i : ℝ) / N ≤ 0)]
    have hval : (N:ℝ) * -((x i : ℝ) - (c.lo i : ℝ) / N)
        = (c.lo i : ℝ) - (N:ℝ) * (x i : ℝ) := by field_simp; ring
    rw [hval, ← hcd]
    exact cellDistCoord_le_cellDist c i x
  · rcases le_or_gt ((c.hi i : ℝ) / N) ((x i : ℝ)) with h2 | h2
    · have hcd := cellDistCoord_eq_of_ge (c := c) (i := i) (x := x) hN h2
      have hcl : ((clampCell c hN x) i : ℝ) = (c.hi i : ℝ) / N := by
        rw [clampCell_val, clampR, min_eq_left h2, max_eq_right hle]
      rw [hcl]
      rw [abs_of_nonneg (by linarith : (0:ℝ) ≤ (x i : ℝ) - (c.hi i : ℝ) / N)]
      have hval : (N:ℝ) * ((x i : ℝ) - (c.hi i : ℝ) / N)
          = (N:ℝ) * (x i : ℝ) - (c.hi i : ℝ) := by field_simp
      rw [hval, ← hcd]
      exact cellDistCoord_le_cellDist c i x
    · have hcl : ((clampCell c hN x) i : ℝ) = (x i : ℝ) := by
        rw [clampCell_val, clampR, min_eq_right h2.le, max_eq_right h.le]
      rw [hcl, sub_self, abs_zero, mul_zero]
      exact cellDist_nonneg c x

theorem dist_clampCell_le (c : CellIdx j N) (hN : 1 ≤ N) (x : IC j) :
    dist x (clampCell c hN x) ≤ cellDist c x / N := by
  have hNpos : (0:ℝ) < N := by exact_mod_cast hN
  rw [dist_pi_le_iff (div_nonneg (cellDist_nonneg c x) (le_of_lt hNpos))]
  intro i
  rw [Subtype.dist_eq, Real.dist_eq, le_div_iff₀ hNpos, mul_comm]
  exact mul_abs_sub_clamp_le_cellDist c hN i x

theorem abs_flowCoef_mul_le (c : CellIdx j N) (hN : 1 ≤ N) (i : Fin j) (x : IC j) (τ : I) :
    |flowCoef c x τ * ((x i : ℝ) - ((clampCell c hN x) i : ℝ))| ≤ cellDist c x / N := by
  rw [abs_mul]
  calc |flowCoef c x τ| * |(x i : ℝ) - ((clampCell c hN x) i : ℝ)|
      ≤ 1 * (cellDist c x / N) := by
        refine mul_le_mul ?_ ?_ (abs_nonneg _) (by norm_num)
        · rw [abs_of_nonneg (flowCoef_nonneg c x τ)]; exact flowCoef_le_one c x τ
        · have h := mul_abs_sub_clamp_le_cellDist c hN i x
          rw [le_div_iff₀ (by exact_mod_cast hN), mul_comm]
          exact h
    _ = cellDist c x / N := one_mul _

theorem continuousAt_flowCoef (c : CellIdx j N) {p : IC j × I} (h : rOf c p.1 ≠ 0) :
    ContinuousAt (fun q : IC j × I => flowCoef c q.1 q.2) p := by
  have h1 : ContinuousAt (fun q : IC j × I => ((q.2 : I) : ℝ) * nuOf c q.1 / rOf c q.1) p :=
    (((continuous_subtype_val.comp continuous_snd).continuousAt).mul
      (((continuous_nuOf c).continuousAt).comp continuous_fst.continuousAt)).div
      (((continuous_rOf c).continuousAt).comp continuous_fst.continuousAt) h
  exact continuous_clamp01.continuousAt.comp h1

theorem continuous_displacement (c : CellIdx j N) (hN : 1 ≤ N) (i : Fin j) :
    Continuous fun p : IC j × I => (p.1 i : ℝ) - ((clampCell c hN p.1) i : ℝ) :=
  (continuous_subtype_val.comp ((continuous_apply i).comp continuous_fst)).sub
    (continuous_subtype_val.comp ((continuous_apply i).comp
      ((clampCell c hN).continuous.comp continuous_fst)))

/-- **Continuity of the flow displacement.** -/
theorem continuous_flowCoef_mul (c : CellIdx j N) (hN : 1 ≤ N) (i : Fin j) :
    Continuous fun p : IC j × I =>
      flowCoef c p.1 p.2 * ((p.1 i : ℝ) - ((clampCell c hN p.1) i : ℝ)) := by
  rw [continuous_iff_continuousAt]
  intro p₀
  rcases eq_or_ne (rOf c p₀.1) 0 with h | h
  · -- at `r = 0`: the displacement vanishes and bounds the product
    have hcd : cellDist c p₀.1 = 0 :=
      (cellDist_eq_zero_iff hN c p₀.1).mpr ((rOf_eq_zero_iff hN c p₀.1).mp h)
    have hvan : (p₀.1 i : ℝ) - ((clampCell c hN p₀.1) i : ℝ) = 0 := by
      rw [clampCell_eq_self c hN ((rOf_eq_zero_iff hN c p₀.1).mp h)]; ring
    rw [Metric.continuousAt_iff]
    intro ε hε
    have hcont := (continuous_displacement c hN i).continuousAt (x := p₀)
    rw [Metric.continuousAt_iff] at hcont
    obtain ⟨δ, hδ, hball⟩ := hcont (ε/2) (by linarith)
    refine ⟨δ, hδ, fun p hp => ?_⟩
    have h1 : |(p.1 i : ℝ) - ((clampCell c hN p.1) i : ℝ)| < ε/2 := by
      have := hball hp
      rw [Real.dist_eq, hvan, sub_zero] at this
      exact this
    have h2 : |flowCoef c p.1 p.2| ≤ 1 := by
      rw [abs_of_nonneg (flowCoef_nonneg c p.1 p.2)]; exact flowCoef_le_one c p.1 p.2
    have h3 : flowCoef c p₀.1 p₀.2 * ((p₀.1 i : ℝ) - ((clampCell c hN p₀.1) i : ℝ)) = 0 := by
      rw [hvan, mul_zero]
    rw [Real.dist_eq, h3, sub_zero, abs_mul]
    calc |flowCoef c p.1 p.2| * |(p.1 i : ℝ) - ((clampCell c hN p.1) i : ℝ)|
        ≤ 1 * |(p.1 i : ℝ) - ((clampCell c hN p.1) i : ℝ)| :=
          mul_le_mul_of_nonneg_right h2 (abs_nonneg _)
      _ < ε := by rw [one_mul]; linarith
  · have hc : ContinuousAt (fun q : IC j × I => flowCoef c q.1 q.2) p₀ :=
      continuousAt_flowCoef c h
    exact hc.mul (continuous_displacement c hN i).continuousAt

theorem continuous_spreadPt_coord (c : CellIdx j N) (hN : 1 ≤ N) (i : Fin j) :
    Continuous fun p : IC j × I => ((spreadPt c hN p.1 p.2) i : ℝ) := by
  have h : (fun p : IC j × I => ((spreadPt c hN p.1 p.2) i : ℝ))
      = fun p : IC j × I =>
          (p.1 i : ℝ) - flowCoef c p.1 p.2 * ((p.1 i : ℝ) - ((clampCell c hN p.1) i : ℝ)) := by
    funext p
    rw [spreadPt, segMap]
    ring
  rw [h]
  exact (continuous_subtype_val.comp ((continuous_apply i).comp continuous_fst)).sub
    (continuous_flowCoef_mul c hN i)

theorem continuous_spreadPt (c : CellIdx j N) (hN : 1 ≤ N) :
    Continuous fun p : IC j × I => spreadPt c hN p.1 p.2 :=
  continuous_pi fun i => Continuous.subtype_mk (continuous_spreadPt_coord c hN i) _

theorem continuous_pushI (c : CellIdx j N) :
    Continuous fun p : IC j × I => pushI c p.1 p.2 := by
  refine Continuous.subtype_mk ?_ _
  have h1 : Continuous fun p : IC j × I => ((p.2 : I) : ℝ) * nuOf c p.1 :=
    (continuous_subtype_val.comp continuous_snd).mul ((continuous_nuOf c).comp continuous_fst)
  have h2 : Continuous fun p : IC j × I => rOf c p.1 :=
    (continuous_rOf c).comp continuous_fst
  exact continuous_const.max (h1.sub h2)

theorem continuous_spreadMap (c : CellIdx j N) (hN : 1 ≤ N) :
    Continuous fun p : IC j × I => spreadMap c hN p.1 p.2 :=
  (continuous_spreadPt c hN).prodMk (continuous_pushI c)

end Work.ThomBordism.TwoSet
