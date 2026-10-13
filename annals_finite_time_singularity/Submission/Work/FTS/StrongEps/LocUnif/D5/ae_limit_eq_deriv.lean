import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.IntervalIntegral.LebesgueDifferentiationThm
import Mathlib.MeasureTheory.Order.Group.Lattice
import Mathlib.Order.CompletePartialOrder
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.StrongEps.LocUnif.D5.ae_ident_aux

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# Identification of an a.e. limit with the derivative of a uniform limit (1-D engine)

This file isolates the one-dimensional "ACL" argument used to identify the a.e. limit of the
level-5 slots with the corresponding mixed derivative of the limit function.
-/

noncomputable section

open scoped Real Topology ENNReal
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.LocUnif.D5

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

/-! ## The clamped limit and the "bad" set of rational difference quotients -/

/-- The composition of `Llim` with the projection onto the box `[a,b] × [c,d]`; it is globally
continuous as soon as `Llim` is continuous on the box, and it agrees with `Llim` there. -/
def Lclamp {a b c d : ℝ} (hab : a ≤ b) (hcd : c ≤ d) (Llim : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ :=
  fun z θ => Llim (Set.projIcc a b hab z) (Set.projIcc c d hcd θ)

/-- The set of points of the box at which the rational difference quotients of the clamped limit
are *not* close to `w`.  This is the set whose nullity is produced by Fubini; it is measurable
without any measurability assumption on `Llim` itself, thanks to the clamping. -/
def BadSet {a b c d : ℝ} (Lc : ℝ → ℝ → ℝ) (w : ℝ × ℝ → ℝ) : Set (ℝ × ℝ) :=
  {p | p ∈ Set.Icc a b ×ˢ Set.Icc c d ∧ ∃ k : ℕ, ∀ m : ℕ, ∃ h : ℚ,
      0 < |(h : ℝ)| ∧ |(h : ℝ)| < 1 / (m + 1) ∧ p.1 + (h : ℝ) ∈ Set.Icc a b ∧
      1 / (k + 1) < |(Lc (p.1 + (h : ℝ)) p.2 - Lc p.1 p.2) / (h : ℝ) - w p|}

theorem badSet_measurable {a b c d : ℝ} {Lc : ℝ → ℝ → ℝ} {w : ℝ × ℝ → ℝ}
    (hLc : Continuous (Function.uncurry Lc)) (hw : Measurable w) :
    MeasurableSet (BadSet (a := a) (b := b) (c := c) (d := d) Lc w) := by
  rw [BadSet]
  have hbox : MeasurableSet {p : ℝ × ℝ | p ∈ Set.Icc a b ×ˢ Set.Icc c d} :=
    measurableSet_Icc.prod measurableSet_Icc
  have hstep : ∀ (k m : ℕ) (h : ℚ), MeasurableSet {p : ℝ × ℝ | 0 < |(h : ℝ)| ∧
      |(h : ℝ)| < 1 / ((m : ℝ) + 1) ∧ p.1 + (h : ℝ) ∈ Set.Icc a b ∧
      1 / ((k : ℝ) + 1) < |(Lc (p.1 + (h : ℝ)) p.2 - Lc p.1 p.2) / (h : ℝ) - w p|} := by
    intro k m h
    have hshift : MeasurableSet {p : ℝ × ℝ | p.1 + (h : ℝ) ∈ Set.Icc a b} :=
      measurableSet_Icc.preimage (by fun_prop)
    have hval : MeasurableSet {p : ℝ × ℝ |
        1 / ((k : ℝ) + 1) < |(Lc (p.1 + (h : ℝ)) p.2 - Lc p.1 p.2) / (h : ℝ) - w p|} := by
      refine measurableSet_lt measurable_const ?_
      have h1 : Continuous fun p : ℝ × ℝ => Lc (p.1 + (h : ℝ)) p.2 :=
        hLc.comp ((continuous_fst.add continuous_const).prodMk continuous_snd)
      have h2 : Continuous fun p : ℝ × ℝ => Lc p.1 p.2 :=
        hLc.comp (continuous_fst.prodMk continuous_snd)
      have hm1 : Measurable fun p : ℝ × ℝ =>
          (Lc (p.1 + (h : ℝ)) p.2 - Lc p.1 p.2) / (h : ℝ) := ((h1.sub h2).div_const _).measurable
      exact (hm1.sub hw).abs
    have hconst1 : MeasurableSet {p : ℝ × ℝ | 0 < |(h : ℝ)|} := by
      by_cases hh : 0 < |(h : ℝ)| <;> simp [hh]
    have hconst2 : MeasurableSet {p : ℝ × ℝ | |(h : ℝ)| < 1 / ((m : ℝ) + 1)} := by
      by_cases hh : |(h : ℝ)| < 1 / ((m : ℝ) + 1) <;> simp [hh]
    exact hconst1.inter (hconst2.inter (hshift.inter hval))
  rw [show {p : ℝ × ℝ | p ∈ Set.Icc a b ×ˢ Set.Icc c d ∧ ∃ k : ℕ, ∀ m : ℕ, ∃ h : ℚ,
        0 < |(h : ℝ)| ∧ |(h : ℝ)| < 1 / ((m : ℝ) + 1) ∧ p.1 + (h : ℝ) ∈ Set.Icc a b ∧
        1 / ((k : ℝ) + 1) < |(Lc (p.1 + (h : ℝ)) p.2 - Lc p.1 p.2) / (h : ℝ) - w p|}
      = {p : ℝ × ℝ | p ∈ Set.Icc a b ×ˢ Set.Icc c d} ∩
        (⋃ k : ℕ, ⋂ m : ℕ, ⋃ h : ℚ, {p : ℝ × ℝ | 0 < |(h : ℝ)| ∧
          |(h : ℝ)| < 1 / ((m : ℝ) + 1) ∧ p.1 + (h : ℝ) ∈ Set.Icc a b ∧
          1 / ((k : ℝ) + 1) < |(Lc (p.1 + (h : ℝ)) p.2 - Lc p.1 p.2) / (h : ℝ) - w p|}) from by
    ext p
    simp only [Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_iUnion, Set.mem_iInter]]
  exact hbox.inter (MeasurableSet.iUnion fun k => MeasurableSet.iInter fun m =>
    MeasurableSet.iUnion fun h => hstep k m h)

/-! ## The two directions of the characterisation -/

/-- **Reverse direction**: at a point `z` where the primitive of `w(·,θ)` is differentiable with
derivative `w (z,θ)`, the rational difference quotients satisfy the quantitative bounds, so
`(z,θ)` is not in the bad set. -/
theorem notMemBad_of_good {a b c d : ℝ} (hab : a < b) (hcd : c < d)
    {Lc : ℝ → ℝ → ℝ} {Llim : ℝ → ℝ → ℝ} {w : ℝ × ℝ → ℝ}
    (hLc_eq : ∀ z ∈ Set.Icc a b, ∀ θ ∈ Set.Icc c d, Lc z θ = Llim z θ)
    {θ : ℝ} (hθI : θ ∈ Set.Icc c d) {z : ℝ} (hzIoo : z ∈ Set.Ioo a b)
    (hidz : ∀ z' ∈ Set.Icc a b, Llim z' θ - Llim z θ = ∫ u in z..z', w (u, θ))
    (hgood : ∀ c' ∈ Set.uIcc a b, HasDerivAt (fun x => ∫ t in c'..x, w (t, θ)) (w (z, θ)) z)
    (hint : IntegrableOn (fun z => w (z, θ)) (Set.Icc a b) volume) :
    (z, θ) ∉ BadSet (a := a) (b := b) (c := c) (d := d) Lc w := by
  intro hzbad
  obtain ⟨hzbox, k, hk⟩ := hzbad
  have hzab : z ∈ Set.Icc a b := ⟨le_of_lt hzIoo.1, le_of_lt hzIoo.2⟩
  have haab : a ∈ Set.Icc a b := Set.left_mem_Icc.mpr (le_of_lt hab)
  obtain ⟨δ, hδpos, hδ⟩ :=
    exists_delta_hasDerivAt (hgood a (Set.left_mem_uIcc))
      (by positivity : (0 : ℝ) < 1 / ((k : ℝ) + 1))
  obtain ⟨m, hm⟩ : ∃ m : ℕ, 1 / ((m : ℝ) + 1) ≤ δ := by
    obtain ⟨m, hm⟩ := exists_nat_gt (1 / δ)
    refine ⟨m, ?_⟩
    rw [div_le_iff₀ (by positivity : (0 : ℝ) < (m : ℝ) + 1)]
    rw [div_lt_iff₀ hδpos] at hm
    linarith
  obtain ⟨h, hh1, hh2, hh3, hh4⟩ := hk m
  have hzhmem : z + (h : ℝ) ∈ Set.Icc a b := hh3
  have hi1 : IntervalIntegrable (fun t => w (t, θ)) volume a (z + (h : ℝ)) :=
    (hint.mono_set (by
      rw [Set.uIcc_of_le hzhmem.1]
      exact Set.Icc_subset_Icc_right hzhmem.2)).intervalIntegrable
  have hi2 : IntervalIntegrable (fun t => w (t, θ)) volume a z :=
    (hint.mono_set (by
      rw [Set.uIcc_of_le hzab.1]
      exact Set.Icc_subset_Icc_right hzab.2)).intervalIntegrable
  have hq : (Lc (z + (h : ℝ)) θ - Lc z θ) / (h : ℝ)
      = (((fun x => ∫ t in a..x, w (t, θ)) (z + (h : ℝ)))
          - ((fun x => ∫ t in a..x, w (t, θ)) z)) / (h : ℝ) := by
    have h1 : Lc (z + (h : ℝ)) θ - Lc z θ = ∫ u in z..(z + (h : ℝ)), w (u, θ) := by
      rw [hLc_eq (z + (h : ℝ)) hzhmem θ hθI, hLc_eq z hzab θ hθI,
        ← hidz (z + (h : ℝ)) hzhmem]
    have h2 : ((fun x => ∫ t in a..x, w (t, θ)) (z + (h : ℝ)))
        - ((fun x => ∫ t in a..x, w (t, θ)) z) = ∫ u in z..(z + (h : ℝ)), w (u, θ) :=
      intervalIntegral.integral_interval_sub_left hi1 hi2
    rw [h1, h2]
  have hh1' : 0 < |z + (h : ℝ) - z| := by simpa using hh1
  have hh2' : |z + (h : ℝ) - z| < δ := by
    have : |(h : ℝ)| < 1 / ((m : ℝ) + 1) := hh2
    simp only [add_sub_cancel_left]
    exact lt_of_lt_of_le this hm
  have hbound := hδ (z + (h : ℝ)) hh1' hh2'
  simp only [add_sub_cancel_left] at hbound
  rw [hq] at hh4
  exact absurd hh4 (not_lt.mpr hbound.le)

/-- **Forward direction**: if the rational difference quotients of the clamped limit satisfy the
quantitative bounds (all `k`, on a small interval of steps), then the honest difference quotients
of `Llim (·,θ)` at `z` converge to `w (z,θ)`, so the derivative exists and equals `w (z,θ)`. -/
theorem hasDerivAt_of_notMemBad {a b c d : ℝ} (hab : a < b) (hcd : c < d)
    {Lc : ℝ → ℝ → ℝ} {Llim : ℝ → ℝ → ℝ} {w : ℝ × ℝ → ℝ}
    (hLc_cont : Continuous (Function.uncurry Lc))
    (hLc_eq : ∀ z ∈ Set.Icc a b, ∀ θ ∈ Set.Icc c d, Lc z θ = Llim z θ)
    {θ : ℝ} (hθI : θ ∈ Set.Icc c d) {z : ℝ} (hzIoo : z ∈ Set.Ioo a b)
    (hidz : ∀ z' ∈ Set.Icc a b, Llim z' θ - Llim z θ = ∫ u in z..z', w (u, θ))
    (hint : IntegrableOn (fun z => w (z, θ)) (Set.Icc a b) volume)
    (hnb : (z, θ) ∉ BadSet (a := a) (b := b) (c := c) (d := d) Lc w) :
    HasDerivAt (fun z' => Llim z' θ) (w (z, θ)) z := by
  have hzab : z ∈ Set.Icc a b := ⟨le_of_lt hzIoo.1, le_of_lt hzIoo.2⟩
  -- the quantitative statement extracted from `¬Bad`
  have hQ : ∀ k : ℕ, ∃ m : ℕ, ∀ h : ℚ, 0 < |(h : ℝ)| → |(h : ℝ)| < 1 / ((m : ℝ) + 1) →
      z + (h : ℝ) ∈ Set.Icc a b →
      |(Lc (z + (h : ℝ)) θ - Lc z θ) / (h : ℝ) - w (z, θ)| ≤ 1 / ((k : ℝ) + 1) := by
    intro k
    by_contra hcon
    push Not at hcon
    exact hnb ⟨⟨hzab, hθI⟩, k, fun m => hcon m⟩
  -- the `ε`-`δ` statement for the difference quotients
  have hεδ : ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ y : ℝ, 0 < |y - z| → |y - z| < δ →
      |(Llim y θ - Llim z θ) / (y - z) - w (z, θ)| < ε := by
    intro ε hε
    obtain ⟨k, hk⟩ : ∃ k : ℕ, 1 / ((k : ℝ) + 1) < ε := by
      obtain ⟨k, hk⟩ := exists_nat_gt (1 / ε)
      refine ⟨k, ?_⟩
      rw [div_lt_iff₀ (by positivity : (0 : ℝ) < (k : ℝ) + 1)]
      rw [div_lt_iff₀ hε] at hk
      linarith
    obtain ⟨m, hm⟩ := hQ k
    obtain ⟨δc, hδcpos, hδc1, hδc2, hδc3⟩ : ∃ δc : ℝ, 0 < δc ∧ δc ≤ 1 / ((m : ℝ) + 1) ∧
        δc ≤ z - a ∧ δc ≤ b - z :=
      ⟨min (1 / ((m : ℝ) + 1)) (min (z - a) (b - z)),
        lt_min (by positivity) (lt_min (by linarith [hzIoo.1]) (by linarith [hzIoo.2])),
        min_le_left _ _, le_trans (min_le_right _ _) (min_le_left _ _),
        le_trans (min_le_right _ _) (min_le_right _ _)⟩
    have hcont1 : Continuous fun t : ℝ => Lc (z + t) θ :=
      hLc_cont.comp ((continuous_const.add continuous_id).prodMk continuous_const)
    have hcont_pos : ContinuousOn (fun t : ℝ => (Lc (z + t) θ - Lc z θ) / t - w (z, θ))
        (Set.Ioo (0 : ℝ) δc) := by
      have hnum : ContinuousOn (fun t : ℝ => Lc (z + t) θ - Lc z θ) (Set.Ioo (0 : ℝ) δc) :=
        (hcont1.sub continuous_const).continuousOn
      exact (hnum.div continuousOn_id (fun t ht => ne_of_gt ht.1)).sub continuousOn_const
    have hcont_neg : ContinuousOn (fun t : ℝ => (Lc (z + t) θ - Lc z θ) / t - w (z, θ))
        (Set.Ioo (-δc) 0) := by
      have hnum : ContinuousOn (fun t : ℝ => Lc (z + t) θ - Lc z θ) (Set.Ioo (-δc) 0) :=
        (hcont1.sub continuous_const).continuousOn
      exact (hnum.div continuousOn_id (fun t ht => ne_of_lt ht.2)).sub continuousOn_const
    -- the rational bounds on either half-interval
    have hrat : ∀ t : ℚ, (t : ℝ) ∈ Set.Ioo (-δc) 0 ∪ Set.Ioo (0 : ℝ) δc →
        |(Lc (z + (t : ℝ)) θ - Lc z θ) / (t : ℝ) - w (z, θ)| ≤ 1 / ((k : ℝ) + 1) := by
      intro t ht
      have htabs : |(t : ℝ)| < δc := by
        rcases ht with ht | ht
        · rw [abs_of_neg ht.2]; linarith [ht.1]
        · rw [abs_of_pos ht.1]; exact ht.2
      have ht0 : 0 < |(t : ℝ)| := abs_pos.mpr (by
        rcases ht with ht | ht
        · exact ne_of_lt ht.2
        · exact ne_of_gt ht.1)
      have htz : z + (t : ℝ) ∈ Set.Icc a b := by
        rcases ht with ht | ht
        · -- the negative side
          refine ⟨by linarith [ht.1, hδc2], by linarith [hzIoo.2, ht.2]⟩
        · -- the positive side
          refine ⟨by linarith [hzIoo.1, ht.1], by linarith [ht.2, hδc3]⟩
      exact hm t ht0 (lt_of_lt_of_le htabs hδc1) htz
    have hbound_pos : ∀ t ∈ Set.Ioo (0 : ℝ) δc,
        |(Lc (z + t) θ - Lc z θ) / t - w (z, θ)| ≤ 1 / ((k : ℝ) + 1) :=
      abs_le_of_forall_rat_of_continuousOn isOpen_Ioo hcont_pos (fun q hq => hrat q (Or.inr hq))
    have hbound_neg : ∀ t ∈ Set.Ioo (-δc) 0,
        |(Lc (z + t) θ - Lc z θ) / t - w (z, θ)| ≤ 1 / ((k : ℝ) + 1) :=
      abs_le_of_forall_rat_of_continuousOn isOpen_Ioo hcont_neg (fun q hq => hrat q (Or.inl hq))
    refine ⟨δc, hδcpos, fun y hy hyδ => ?_⟩
    have hyne : y - z ≠ 0 := by
      intro h0
      rw [h0, abs_zero] at hy
      exact absurd hy (lt_irrefl 0)
    have hyab : y ∈ Set.Icc a b := by
      rcases lt_or_gt_of_ne hyne with hneg | hpos
      · rw [abs_of_neg hneg] at hyδ
        exact ⟨by linarith [hδc2], by linarith [hzIoo.2, hneg]⟩
      · rw [abs_of_pos hpos] at hyδ
        exact ⟨by linarith [hzIoo.1, hpos], by linarith [hδc3]⟩
    have hbound : |(Lc y θ - Lc z θ) / (y - z) - w (z, θ)| ≤ 1 / ((k : ℝ) + 1) := by
      rcases lt_or_gt_of_ne hyne with hneg | hpos
      · have hmem : y - z ∈ Set.Ioo (-δc) 0 := by
          refine ⟨?_, hneg⟩
          rw [abs_of_neg hneg] at hyδ; linarith
        have := hbound_neg (y - z) hmem
        rwa [show z + (y - z) = y from by ring] at this
      · have hmem : y - z ∈ Set.Ioo (0 : ℝ) δc := by
          refine ⟨hpos, ?_⟩
          rw [abs_of_pos hpos] at hyδ; exact hyδ
        have := hbound_pos (y - z) hmem
        rwa [show z + (y - z) = y from by ring] at this
    -- convert to the primitive's difference quotient
    have hb2 : |(Llim y θ - Llim z θ) / (y - z) - w (z, θ)| ≤ 1 / ((k : ℝ) + 1) := by
      rw [← hLc_eq y hyab θ hθI, ← hLc_eq z hzab θ hθI]
      exact hbound
    have hi1 : IntervalIntegrable (fun t => w (t, θ)) volume a y :=
      (hint.mono_set (by
        rw [Set.uIcc_of_le hyab.1]
        exact Set.Icc_subset_Icc_right hyab.2)).intervalIntegrable
    have hi2 : IntervalIntegrable (fun t => w (t, θ)) volume a z :=
      (hint.mono_set (by
        rw [Set.uIcc_of_le hzab.1]
        exact Set.Icc_subset_Icc_right hzab.2)).intervalIntegrable
    rw [hidz y hyab, ← intervalIntegral.integral_interval_sub_left hi1 hi2] at hb2 ⊢
    exact lt_of_le_of_lt hb2 hk
  -- conclude
  rw [hasDerivAt_iff_tendsto_slope, Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨δ, hδpos, hδ⟩ := hεδ ε hε
  rw [eventually_nhdsWithin_iff]
  refine Filter.eventually_of_mem (Metric.ball_mem_nhds z hδpos) fun y hy hyne => ?_
  simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at hyne
  have hyδ : |y - z| < δ := by simpa [Metric.mem_ball, Real.dist_eq] using hy
  have hy0 : 0 < |y - z| := by
    rw [abs_pos]
    intro h0
    exact hyne (sub_eq_zero.mp h0)
  have h := hδ y hy0 hyδ
  rw [slope_def_field, Real.dist_eq]
  simpa [abs_sub_comm] using h



/-! ## The main identification statement -/

theorem ae_limit_eq_deriv {a b a₀ b₀ c d : ℝ} (ha₀ : 0 < a₀) (ha₀a : a₀ < a) (hab : a < b)
    (hbb₀ : b < b₀) (hcd : c < d)
    {L : ℕ → ℝ → ℝ → ℝ} {Llim : ℝ → ℝ → ℝ} {W : ℕ → ℝ × ℝ → ℝ} {w : ℝ × ℝ → ℝ}
    (hcont : ∀ n, ContinuousOn (fun p : ℝ × ℝ => L n p.1 p.2) (Set.Icc a₀ b₀ ×ˢ Set.Icc c d))
    (hslice : ∀ n, ∀ θ ∈ Set.Icc c d, ContDiffOn ℝ 1 (fun z => L n z θ) (Set.Ioo a₀ b₀))
    (hW : ∀ n, ∀ p ∈ Set.Icc a b ×ˢ Set.Icc c d, W n p = Work.Spaces.pz (L n) p.1 p.2)
    (hconv : TendstoUniformlyOn (fun n (p : ℝ × ℝ) => L n p.1 p.2) (fun p => Llim p.1 p.2)
      Filter.atTop (Set.Icc a₀ b₀ ×ˢ Set.Icc c d))
    (hwmeas : Measurable w)
    (hint : ∀ᵐ θ ∂(volume.restrict (Set.Icc c d)), ∀ z ∈ Set.Icc a b, ∀ z₀ ∈ Set.Icc a b,
      Filter.Tendsto (fun k => ∫ u in z..z₀, W k (u, θ)) Filter.atTop
        (nhds (∫ u in z..z₀, w (u, θ))))
    (hwint : ∀ᵐ θ ∂(volume.restrict (Set.Icc c d)),
      IntegrableOn (fun z => w (z, θ)) (Set.Icc a b) volume) :
    ∀ᵐ p ∂(volume.restrict (Set.Icc a b ×ˢ Set.Icc c d)),
      w p = Work.Spaces.pz Llim p.1 p.2 := by
  classical
  have hab' : a ≤ b := le_of_lt hab
  have hcd' : c ≤ d := le_of_lt hcd
  have hmemR : ∀ z ∈ Set.Icc a b, ∀ θ ∈ Set.Icc c d, (z, θ) ∈ Set.Icc a b ×ˢ Set.Icc c d :=
    fun z hz θ hθ => Set.mem_prod.mpr ⟨hz, hθ⟩
  have hmemR₀ : ∀ z ∈ Set.Icc a b, ∀ θ ∈ Set.Icc c d,
      (z, θ) ∈ Set.Icc a₀ b₀ ×ˢ Set.Icc c d := fun z hz θ hθ => Set.mem_prod.mpr
    ⟨⟨by linarith [hz.1, ha₀a], by linarith [hz.2, hbb₀]⟩, hθ⟩
  have hIccab : ∀ z ∈ Set.Icc a b, z ∈ Set.Ioo a₀ b₀ := fun z hz =>
    ⟨by linarith [hz.1, ha₀a], by linarith [hz.2, hbb₀]⟩
  have hboxsub : Set.Icc a b ×ˢ Set.Icc c d ⊆ Set.Icc a₀ b₀ ×ˢ Set.Icc c d := by
    intro p hp
    exact hmemR₀ p.1 hp.1 p.2 hp.2
  -- continuity of `Llim` on the box, and of the clamped version
  have hlimcont : ContinuousOn (Function.uncurry Llim) (Set.Icc a₀ b₀ ×ˢ Set.Icc c d) :=
    hconv.continuousOn (Filter.Eventually.of_forall hcont).frequently
  have hlimcont' : ContinuousOn (Function.uncurry Llim) (Set.Icc a b ×ˢ Set.Icc c d) :=
    hlimcont.mono hboxsub
  set Lc : ℝ → ℝ → ℝ := Lclamp hab' hcd' Llim with hLcdef
  have hLc_eq : ∀ z ∈ Set.Icc a b, ∀ θ ∈ Set.Icc c d, Lc z θ = Llim z θ := by
    intro z hz θ hθ
    rw [hLcdef]
    simp only [Lclamp, Set.projIcc_of_mem hab' hz, Set.projIcc_of_mem hcd' hθ, Subtype.coe_mk]
  have hLccont : Continuous (Function.uncurry Lc) := by
    have h1a : Continuous fun p : ℝ × ℝ => ((Set.projIcc a b hab' p.1 : Set.Icc a b) : ℝ) :=
      continuous_subtype_val.comp
        ((continuous_projIcc (a := a) (b := b) (h := hab')).comp continuous_fst)
    have h1b : Continuous fun p : ℝ × ℝ => ((Set.projIcc c d hcd' p.2 : Set.Icc c d) : ℝ) :=
      continuous_subtype_val.comp
        ((continuous_projIcc (a := c) (b := d) (h := hcd')).comp continuous_snd)
    have h1 : Continuous fun p : ℝ × ℝ =>
        (((Set.projIcc a b hab' p.1 : Set.Icc a b) : ℝ),
         ((Set.projIcc c d hcd' p.2 : Set.Icc c d) : ℝ)) := h1a.prodMk h1b
    have h2 : ∀ p : ℝ × ℝ,
        (((Set.projIcc a b hab' p.1 : Set.Icc a b) : ℝ),
         ((Set.projIcc c d hcd' p.2 : Set.Icc c d) : ℝ)) ∈ Set.Icc a b ×ˢ Set.Icc c d :=
      fun p => Set.mem_prod.mpr ⟨(Set.projIcc a b hab' p.1).2, (Set.projIcc c d hcd' p.2).2⟩
    have h4 : Function.uncurry Lc = (Function.uncurry Llim) ∘
        fun p : ℝ × ℝ =>
          (((Set.projIcc a b hab' p.1 : Set.Icc a b) : ℝ),
           ((Set.projIcc c d hcd' p.2 : Set.Icc c d) : ℝ)) := by
      funext p
      simp only [Function.uncurry, Function.comp_apply, hLcdef, Lclamp]
    rw [h4]
    exact hlimcont'.comp_continuous h1 h2
  -- the identity for a.e. angle
  have hid : ∀ᵐ θ ∂(volume.restrict (Set.Icc c d)), ∀ z ∈ Set.Icc a b, ∀ z₀ ∈ Set.Icc a b,
      Llim z₀ θ - Llim z θ = ∫ u in z..z₀, w (u, θ) := by
    filter_upwards [ae_restrict_mem measurableSet_Icc, hint] with θ hθI hθ
    intro z hz z₀ hz₀
    have hFTC : ∀ k : ℕ, (∫ u in z..z₀, W k (u, θ)) = L k z₀ θ - L k z θ := by
      intro k
      have hsub : Set.uIcc z z₀ ⊆ Set.Icc a b := by
        rcases le_total z z₀ with hle | hle
        · rw [Set.uIcc_of_le hle]; exact Set.Icc_subset_Icc hz.1 hz₀.2
        · rw [Set.uIcc_of_ge hle]; exact Set.Icc_subset_Icc hz₀.1 hz.2
      have hderiv : ∀ u ∈ Set.uIcc z z₀, HasDerivAt (fun z' => L k z' θ) (W k (u, θ)) u := by
        intro u hu
        have huab : u ∈ Set.Icc a b := hsub hu
        have hd : HasDerivAt (fun z' => L k z' θ) (Work.Spaces.pz (L k) u θ) u :=
          (((hslice k θ hθI).differentiableOn (by simp)).differentiableAt
            (isOpen_Ioo.mem_nhds (hIccab u huab))).hasDerivAt
        have hWk : W k (u, θ) = Work.Spaces.pz (L k) u θ := by
          simpa using hW k (u, θ) (hmemR u huab θ hθI)
        rw [← hWk] at hd
        exact hd
      have hii : IntervalIntegrable (fun u => W k (u, θ)) volume z z₀ := by
        have hcont' : ContinuousOn (fun u => Work.Spaces.pz (L k) u θ) (Set.uIcc z z₀) :=
          ((hslice k θ hθI).continuousOn_deriv_of_isOpen isOpen_Ioo le_rfl).mono
            (fun u hu => hIccab u (hsub hu))
        have hloc : IntegrableOn (fun u => W k (u, θ)) (Set.uIcc z z₀) volume :=
          (hcont'.integrableOn_compact isCompact_uIcc).congr_fun
            (fun u hu => (hW k (u, θ) (hmemR u (hsub hu) θ hθI)).symm) measurableSet_uIcc
        exact hloc.intervalIntegrable
      rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hii]
    have h2 : Filter.Tendsto (fun k => L k z₀ θ - L k z θ) Filter.atTop
        (nhds (Llim z₀ θ - Llim z θ)) := by
      have hA : Filter.Tendsto (fun k => L k z₀ θ) Filter.atTop (nhds (Llim z₀ θ)) := by
        simpa using hconv.tendsto_at (hmemR₀ z₀ hz₀ θ hθI)
      have hB : Filter.Tendsto (fun k => L k z θ) Filter.atTop (nhds (Llim z θ)) := by
        simpa using hconv.tendsto_at (hmemR₀ z hz θ hθI)
      exact hA.sub hB
    have h2' : Filter.Tendsto (fun k => ∫ u in z..z₀, W k (u, θ)) Filter.atTop
        (nhds (Llim z₀ θ - Llim z θ)) :=
      h2.congr' (Filter.Eventually.of_forall fun k => (hFTC k).symm)
    exact tendsto_nhds_unique h2' (hθ z hz z₀ hz₀)
  -- the Lebesgue differentiation theorem, for a.e. angle
  have hLDT : ∀ᵐ θ ∂(volume.restrict (Set.Icc c d)), ∀ᵐ z ∂volume,
      z ∈ Set.uIcc a b → ∀ c' ∈ Set.uIcc a b,
        HasDerivAt (fun x => ∫ t in c'..x, w (t, θ)) (w (z, θ)) z := by
    filter_upwards [hwint] with θ hθ
    exact IntervalIntegrable.ae_hasDerivAt_integral
      ((hθ.mono_set (le_of_eq (Set.uIcc_of_le hab'))).intervalIntegrable)
  -- the set of good angles
  set Θ : Set ℝ := {θ | θ ∈ Set.Icc c d ∧
    (∀ z ∈ Set.Icc a b, ∀ z₀ ∈ Set.Icc a b, Llim z₀ θ - Llim z θ = ∫ u in z..z₀, w (u, θ)) ∧
    IntegrableOn (fun z => w (z, θ)) (Set.Icc a b) volume ∧
    (∀ᵐ z ∂volume, z ∈ Set.uIcc a b → ∀ c' ∈ Set.uIcc a b,
      HasDerivAt (fun x => ∫ t in c'..x, w (t, θ)) (w (z, θ)) z)} with hΘdef
  have hmemΘ : ∀ᵐ θ ∂(volume.restrict (Set.Icc c d)), θ ∈ Θ := by
    filter_upwards [ae_restrict_mem measurableSet_Icc, hid, hwint, hLDT] with θ h1 h2 h3 h4
    exact ⟨h1, h2, h3, h4⟩
  have hΘnull : (volume.restrict (Set.Icc c d)) Θᶜ = 0 := MeasureTheory.ae_iff.mp hmemΘ
  -- the "bad" set is measurable
  have hBadmeas : MeasurableSet (BadSet (a := a) (b := b) (c := c) (d := d) Lc w) :=
    badSet_measurable hLccont hwmeas
  -- its sections are a.e. null
  have hsec : ∀ θ ∈ Θ,
      (volume.restrict (Set.Icc a b)) {z | (z, θ) ∈ BadSet (a := a) (b := b) (c := c) (d := d) Lc w}
        = 0 := by
    intro θ hθ
    obtain ⟨hθI, hθid, hθint, hθLDT⟩ := hθ
    have hnull : volume {z : ℝ | z ∈ Set.uIcc a b ∧
        ¬ (∀ c' ∈ Set.uIcc a b, HasDerivAt (fun x => ∫ t in c'..x, w (t, θ)) (w (z, θ)) z)}
        = 0 := by
      refine measure_mono_null ?_ (MeasureTheory.ae_iff.mp hθLDT)
      intro z hz
      simp only [Set.mem_setOf_eq] at hz ⊢
      exact fun h => hz.2 (h hz.1)
    have hnull2 : volume ({a, b} : Set ℝ) = 0 :=
      ((Set.finite_singleton b).insert a).measure_zero volume
    have hsub2 : {z | (z, θ) ∈ BadSet (a := a) (b := b) (c := c) (d := d) Lc w} ⊆
        ({a, b} : Set ℝ) ∪ {z : ℝ | z ∈ Set.uIcc a b ∧
          ¬ (∀ c' ∈ Set.uIcc a b, HasDerivAt (fun x => ∫ t in c'..x, w (t, θ)) (w (z, θ)) z)} := by
      intro z hz
      by_cases hzab : z ∈ ({a, b} : Set ℝ)
      · exact Or.inl hzab
      right
      simp only [Set.mem_setOf_eq] at hz ⊢
      have hzI : z ∈ Set.Icc a b := hz.1.1
      refine ⟨by rw [Set.uIcc_of_le hab']; exact hzI, fun hgood => ?_⟩
      have hzIoo : z ∈ Set.Ioo a b :=
        ⟨lt_of_le_of_ne hzI.1 (by intro h0; exact hzab (by simp [h0])),
          lt_of_le_of_ne hzI.2 (by intro h0; exact hzab (by simp [h0]))⟩
      exact absurd hz (notMemBad_of_good hab hcd hLc_eq hθI hzIoo
        (fun z' hz' => hθid z hzI z' hz') hgood hθint)
    refine le_antisymm ?_ bot_le
    calc (volume.restrict (Set.Icc a b))
          {z | (z, θ) ∈ BadSet (a := a) (b := b) (c := c) (d := d) Lc w}
        ≤ (volume.restrict (Set.Icc a b)) (({a, b} : Set ℝ) ∪ {z : ℝ | z ∈ Set.uIcc a b ∧
            ¬ (∀ c' ∈ Set.uIcc a b, HasDerivAt (fun x => ∫ t in c'..x, w (t, θ)) (w (z, θ)) z)}) :=
          measure_mono hsub2
      _ ≤ volume (({a, b} : Set ℝ) ∪ {z : ℝ | z ∈ Set.uIcc a b ∧
            ¬ (∀ c' ∈ Set.uIcc a b, HasDerivAt (fun x => ∫ t in c'..x, w (t, θ)) (w (z, θ)) z)}) :=
          Measure.restrict_apply_le _ _
      _ = 0 := measure_union_null hnull2 hnull
  -- the bad set is null (Fubini)
  have hBadnull : (volume.restrict (Set.Icc a b ×ˢ Set.Icc c d))
      (BadSet (a := a) (b := b) (c := c) (d := d) Lc w) = 0 := by
    have hμν : (volume.restrict (Set.Icc a b)).prod (volume.restrict (Set.Icc c d))
        = volume.restrict (Set.Icc a b ×ˢ Set.Icc c d) := by
      rw [Measure.prod_restrict, ← Measure.volume_eq_prod ℝ ℝ]
    rw [← hμν]
    have hsm : MeasurableSet (Prod.swap ⁻¹'
        BadSet (a := a) (b := b) (c := c) (d := d) Lc w) :=
      hBadmeas.preimage measurable_swap
    have hsec' : (fun θ => (volume.restrict (Set.Icc a b))
        (Prod.mk θ ⁻¹' (Prod.swap ⁻¹' BadSet (a := a) (b := b) (c := c) (d := d) Lc w)))
        =ᵐ[volume.restrict (Set.Icc c d)] 0 := by
      rw [Filter.EventuallyEq, MeasureTheory.ae_iff]
      refine measure_mono_null ?_ hΘnull
      intro θ hθ
      simp only [Pi.zero_apply, Set.mem_setOf_eq] at hθ ⊢
      exact fun hΘmem => hθ (hsec θ hΘmem)
    have hmain := Measure.measure_prod_null_of_ae_null (μ := volume.restrict (Set.Icc c d))
      (ν := volume.restrict (Set.Icc a b)) hsm hsec'
    have hfab : (volume.restrict (Set.Icc a b)).prod (volume.restrict (Set.Icc c d))
        (BadSet (a := a) (b := b) (c := c) (d := d) Lc w)
        = (volume.restrict (Set.Icc c d)).prod (volume.restrict (Set.Icc a b))
          (Prod.swap ⁻¹' BadSet (a := a) (b := b) (c := c) (d := d) Lc w) := by
      rw [← Measure.map_apply measurable_swap hBadmeas,
        (Measure.measurePreserving_swap (μ := volume.restrict (Set.Icc c d))
          (ν := volume.restrict (Set.Icc a b))).map_eq]
    rw [hfab]
    exact hmain
  -- the final a.e. statement
  rw [MeasureTheory.ae_iff]
  have hμν : (volume.restrict (Set.Icc a b ×ˢ Set.Icc c d))
      = (volume.restrict (Set.Icc a b)).prod (volume.restrict (Set.Icc c d)) := by
    rw [Measure.prod_restrict, ← Measure.volume_eq_prod ℝ ℝ]
  have hpiece0 : (volume.restrict (Set.Icc a b ×ˢ Set.Icc c d))
      {p : ℝ × ℝ | p ∉ Set.Icc a b ×ˢ Set.Icc c d} = 0 := by
    have hmeas : MeasurableSet {p : ℝ × ℝ | p ∉ Set.Icc a b ×ˢ Set.Icc c d} :=
      (measurableSet_Icc.prod measurableSet_Icc).compl
    rw [Measure.restrict_apply hmeas]
    have h0 : {p : ℝ × ℝ | p ∉ Set.Icc a b ×ˢ Set.Icc c d} ∩ (Set.Icc a b ×ˢ Set.Icc c d)
        = (∅ : Set (ℝ × ℝ)) := by
      ext p; simp only [Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false,
        not_and]; exact fun h1 h2 => h1 h2
    rw [h0, measure_empty]
  have hpiece2 : (volume.restrict (Set.Icc a b ×ˢ Set.Icc c d)) {p : ℝ × ℝ | p.2 ∉ Θ} = 0 := by
    rw [hμν, show {p : ℝ × ℝ | p.2 ∉ Θ} = Set.univ ×ˢ Θᶜ from by
      ext p; simp]
    rw [Measure.prod_prod, hΘnull, mul_zero]
  have hpiece3 : (volume.restrict (Set.Icc a b ×ˢ Set.Icc c d))
      {p : ℝ × ℝ | p.1 ∈ ({a, b} : Set ℝ)} = 0 := by
    rw [hμν, show {p : ℝ × ℝ | p.1 ∈ ({a, b} : Set ℝ)} = ({a, b} : Set ℝ) ×ˢ Set.univ from by
      ext p; simp]
    rw [Measure.prod_prod]
    have h0 : (volume.restrict (Set.Icc a b)) ({a, b} : Set ℝ) = 0 :=
      le_antisymm ((Measure.restrict_apply_le (Set.Icc a b) ({a, b} : Set ℝ)).trans
        (le_of_eq (((Set.finite_singleton b).insert a).measure_zero volume))) bot_le
    rw [h0, zero_mul]
  refine measure_mono_null ?_ (measure_union_null hpiece0 (measure_union_null hBadnull
    (measure_union_null hpiece2 hpiece3)))
  intro p hp
  by_cases hbox : p ∈ Set.Icc a b ×ˢ Set.Icc c d
  · by_cases h2 : p.2 ∉ Θ
    · exact Or.inr (Or.inr (Or.inl h2))
    · push Not at h2
      by_cases h3 : p.1 ∈ ({a, b} : Set ℝ)
      · exact Or.inr (Or.inr (Or.inr h3))
      · refine Or.inr (Or.inl ?_)
        by_contra hnb
        have hp1I : p.1 ∈ Set.Icc a b := hbox.1
        have hp1Ioo : p.1 ∈ Set.Ioo a b :=
          ⟨lt_of_le_of_ne hp1I.1 (by intro h0; exact h3 (by simp [h0])),
            lt_of_le_of_ne hp1I.2 (by intro h0; exact h3 (by simp [h0]))⟩
        obtain ⟨hθI, hθid, hθint, -⟩ := h2
        have hder := hasDerivAt_of_notMemBad hab hcd hLccont hLc_eq hθI hp1Ioo
          (fun z' hz' => hθid p.1 hp1I z' hz') hθint hnb
        have hdw : Work.Spaces.pz Llim p.1 p.2 = w p := by
          rw [show Work.Spaces.pz Llim p.1 p.2
            = deriv (fun z' => Llim z' p.2) p.1 from rfl]
          exact hder.deriv
        exact hp hdw.symm
  · exact Or.inl hbox

end Work.FTS.StrongEps.LocUnif.D5
