import Mathlib
import Submission.Work.WilE7.SelDefs

open Filter Topology

namespace Work.WilE7

/-! ### Auxiliary facts about `Real.tanh` -/

/-- `Real.tanh` written with `exp (-(2 x))`, the form in which its limits at `±∞` are visible. -/
lemma erF_tanh_eq_exp_neg (x : ℝ) :
    Real.tanh x = (1 - Real.exp (-(2 * x))) / (1 + Real.exp (-(2 * x))) := by
  rw [Real.tanh_eq]
  have e1 : Real.exp x * Real.exp (-x) = 1 := by rw [← Real.exp_add]; norm_num
  have e2 : Real.exp (-x) * Real.exp (-x) = Real.exp (-(2 * x)) := by
    rw [← Real.exp_add]; ring_nf
  have h3 : Real.exp x * Real.exp (-(2 * x)) = Real.exp (-x) := by
    rw [← e2, ← mul_assoc, e1, one_mul]
  rw [div_eq_div_iff (by positivity) (by positivity)]
  linear_combination (norm := ring_nf) 2 * h3

lemma erF_continuous_tanh : Continuous Real.tanh := by
  rw [show Real.tanh = fun x => Real.sinh x / Real.cosh x from
    funext Real.tanh_eq_sinh_div_cosh]
  exact Real.continuous_sinh.div Real.continuous_cosh fun x => (Real.cosh_pos x).ne'

/-- `tanh x → 1` as `x → +∞`. -/
lemma erF_tendsto_tanh_atTop : Tendsto Real.tanh atTop (𝓝 1) := by
  have hneg : Tendsto (fun x : ℝ => -(2 * x)) atTop atBot :=
    tendsto_neg_atTop_atBot.comp
      ((tendsto_const_mul_atTop_of_pos (f := id) (show (0 : ℝ) < 2 by norm_num)).mpr tendsto_id)
  have hz : Tendsto (fun x : ℝ => Real.exp (-(2 * x))) atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp hneg
  have hcont : ContinuousAt (fun y : ℝ => (1 - y) / (1 + y)) 0 :=
    (continuousAt_const.sub continuousAt_id).div (continuousAt_const.add continuousAt_id)
      (by norm_num)
  have hratio : Tendsto (fun x : ℝ => (1 - Real.exp (-(2 * x))) / (1 + Real.exp (-(2 * x))))
      atTop (𝓝 1) := by
    have hc := hcont.tendsto.comp hz
    rw [show ((fun y : ℝ => (1 - y) / (1 + y)) ∘ fun x : ℝ => Real.exp (-(2 * x)))
        = (fun x : ℝ => (1 - Real.exp (-(2 * x))) / (1 + Real.exp (-(2 * x)))) from by
      funext x; simp] at hc
    simpa using hc
  rw [show Real.tanh = fun x : ℝ => (1 - Real.exp (-(2 * x))) / (1 + Real.exp (-(2 * x))) from
    funext erF_tanh_eq_exp_neg]
  exact hratio

/-- `tanh x → -1` as `x → -∞`, deduced from the limit at `+∞` and oddness. -/
lemma erF_tendsto_tanh_atBot : Tendsto Real.tanh atBot (𝓝 (-1)) := by
  have h : Tendsto (fun x : ℝ => Real.tanh (-x)) atBot (𝓝 1) :=
    erF_tendsto_tanh_atTop.comp tendsto_neg_atBot_atTop
  have h2 : Tendsto (fun x : ℝ => -Real.tanh x) atBot (𝓝 1) := by
    simpa only [Real.tanh_neg] using h
  simpa using h2.neg

/-! ### Continuity of `erF` at the three kinds of points -/

/-- `erF` tends to `-1` at `⊥`; this is `tanh x → -1` for `x → -∞`. -/
lemma erF_tendsto_atBot : Tendsto erF (𝓝 (⊥ : EReal)) (𝓝 (-1)) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  rw [Filter.eventually_iff, EReal.mem_nhds_bot_iff]
  have ht := (Metric.tendsto_nhds.mp erF_tendsto_tanh_atBot) ε hε
  rw [eventually_atBot] at ht
  obtain ⟨y, hy⟩ := ht
  refine ⟨y, fun x hx => ?_⟩
  induction x using EReal.rec with
  | bot => simpa using hε
  | coe t => simpa using hy t (le_of_lt (EReal.coe_lt_coe_iff.mp hx))
  | top => exact absurd hx (not_lt.mpr (le_top : (y : EReal) ≤ ⊤))

/-- `erF` tends to `1` at `⊤`; this is `tanh x → 1` for `x → +∞`. -/
lemma erF_tendsto_atTop : Tendsto erF (𝓝 (⊤ : EReal)) (𝓝 1) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  rw [Filter.eventually_iff, EReal.mem_nhds_top_iff]
  have ht := (Metric.tendsto_nhds.mp erF_tendsto_tanh_atTop) ε hε
  rw [eventually_atTop] at ht
  obtain ⟨y, hy⟩ := ht
  refine ⟨y, fun x hx => ?_⟩
  induction x using EReal.rec with
  | bot => exact absurd hx (not_lt.mpr (bot_le : (⊥ : EReal) ≤ y))
  | coe t => simpa using hy t (le_of_lt (EReal.coe_lt_coe_iff.mp hx))
  | top => simpa using hε

/-- `erF` is continuous at the finite point `a`, by continuity of `tanh` and the fact that the
inclusion `ℝ → EReal` is an open embedding. -/
lemma erF_continuousAt_coe (a : ℝ) : ContinuousAt erF (a : EReal) := by
  have hcont : Continuous fun x : ℝ => erF (x : EReal) := by
    simpa only [erF_coe] using erF_continuous_tanh
  rw [ContinuousAt, EReal.nhds_coe, Filter.tendsto_map'_iff]
  exact hcont.continuousAt

/-- `erF` (defined by `⊥ ↦ -1`, `⊤ ↦ 1`, and `x ↦ Real.tanh x` on the finite part, see
`Submission/Work/WilE7/SelDefs.lean`, namespace `Work.WilE7`) is continuous, for the order
topology on `EReal` and the usual topology on `ℝ`.  Equivalently: `erF` is an order isomorphism
of `EReal` onto `[-1,1]`, so continuity at `⊤` says `tanh x → 1` as `x → +∞`, at `⊥` it says
`tanh x → -1` as `x → -∞`, and at finite points it is continuity of `Real.tanh`. -/
theorem erF_continuous : Continuous Work.WilE7.erF := by
  rw [continuous_iff_continuousAt]
  intro x
  induction x using EReal.rec with
  | bot =>
    change Tendsto erF (nhds (⊥ : EReal)) (nhds (-1))
    exact erF_tendsto_atBot
  | coe a => exact erF_continuousAt_coe a
  | top =>
    change Tendsto erF (nhds (⊤ : EReal)) (nhds 1)
    exact erF_tendsto_atTop

end Work.WilE7
