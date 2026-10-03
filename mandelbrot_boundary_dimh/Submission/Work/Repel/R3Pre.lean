import Mathlib
import Submission.Work.Interfaces.Parabolic
import Submission.Work.Repel.repel3_helpers
import Submission.Work.Repel.repel3_aux
import Submission.Work.Repel.setup_exists_v4
import Submission.Work.Repel.chain_setup_v4
import Submission.Work.Repel.boxes_v3
import Submission.Work.Repel.R3Arith
import Submission.Work.Repel.target_control
import Submission.Work.Repel.locally_inj_of_deriv_ne_zero
import Submission.Work.Repel.exists_piExp_eq_of_ball
import Submission.Work.Repel.returns_to_ifs
import Submission.Work.L62.chain

/-!
# REPEL / §6: the prelude (blocks A, B, C of the assembly)

All the data of §6 that does **not** depend on `a₁, a₂, β`: the §6 setup `Setup`, the chain data
`ChainSetup` of Lemma 6.2, the fixed constants, the two `PertStatement` calls at level 0 and level 1,
and the scale `η, η₁` together with every threshold fact.

It is a *structure* on purpose: the later stages (`R3Level0`, `R3Level1`, `repel3`) then carry a
**single** hypothesis in their context instead of a hundred.
-/

namespace Work.Repel

open MandelDim Complex Set Metric Filter Topology
open LeanEval.Dynamics.MandelbrotBoundary
open scoped _root_.Topology

noncomputable section

set_option linter.unusedVariables false

/-- `Hfit ≤ η³` may be multiplied out: this is the form consumed by `Work.Repel.fit_arith`.
Small context on purpose (the assembly calls it inside a very large local context). -/
theorem fit_threshold {Hfit η C₀ Cb C₁' : ℝ} (hC₀ : 0 < C₀ + 1) (hCb : 0 < Cb) (hC₁ : 0 < C₁')
    (hH : Hfit = 256 / (320 * (C₀ + 1) * (10 ^ 12 * Cb ^ 2 * (C₁' + 1) ^ 2)))
    (hη : Hfit ≤ η ^ 3) :
    256 ≤ η ^ 3 * (320 * (C₀ + 1) * (10 ^ 12 * Cb ^ 2 * (C₁' + 1) ^ 2)) := by
  have hD : 0 < 320 * (C₀ + 1) * (10 ^ 12 * Cb ^ 2 * (C₁' + 1) ^ 2) := by
    exact mul_pos (by linarith) (mul_pos (mul_pos (by norm_num) (pow_pos hCb 2)) (pow_pos (by linarith : 0 < C₁' + 1) 2))
  have hmul := mul_le_mul_of_nonneg_right hη (le_of_lt hD)
  rw [hH, div_mul_cancel₀ 256 (ne_of_gt hD)] at hmul
  exact hmul

/-- The `a₁a₂β`-independent part of the §6 assembly. -/
structure R3Base where
  ε : ℝ
  hε : 0 < ε
  b : ℝ
  hb : 0 < b
  S : Setup
  CS : ChainSetup S b
  wt₀ : ℂ
  hwt₀Dφ : wt₀ ∈ S.d₀.Dφ
  hφwt₀ : S.d₀.φ wt₀ = 0
  hderwt : deriv S.d₀.φ wt₀ ≠ 0
  hζaDφ : S.ζa ∈ S.d₁.Dφ
  hζaderiv : deriv S.d₁.φ S.ζa ≠ 0
  hζbDφ : S.ζb ∈ S.d₁.Dφ
  hζbderiv : deriv S.d₁.φ S.ζb ≠ 0
  hζaφ : S.d₁.φ S.ζa = S.s₀ * MandelDim.piExp wt₀
  hζbφ : S.d₁.φ S.ζb = S.s₀ * MandelDim.piExp wt₀
  hs₀pos : 0 < ‖S.s₀‖
  r₀ : ℝ
  hr₀pos : 0 < r₀
  hr₀le200 : r₀ ≤ 1 / 200
  hr₀sub : Metric.closedBall wt₀ (2 * r₀) ⊆ S.d₀.Dφ
  hr₀sub' : Metric.closedBall wt₀ r₀ ⊆ S.d₀.Dφ
  hr₀inj : Set.InjOn S.d₀.φ (Metric.ball wt₀ r₀)
  hK₀'c : IsCompact (Metric.closedBall wt₀ (2 * r₀))
  hderivlow₀ : ∀ z ∈ Metric.ball wt₀ r₀, ‖deriv S.d₀.φ wt₀‖ * 2 / 3 ≤ ‖deriv S.d₀.φ z‖
  g₀ : ℝ
  hg₀def : g₀ = ‖deriv S.d₀.φ wt₀‖
  hg₀pos : 0 < g₀
  σL : ℝ
  hσLdef : σL = g₀ * r₀ / 256
  hσLpos : 0 < σL
  Bd : ℝ
  hBd : ∀ z ∈ Metric.closedBall wt₀ r₀, ‖S.d₀.φ z‖ ≤ Bd
  δb : ℝ
  hδbdef : δb = 1 / (16 * Real.pi)
  δ₁b : ℝ
  hδ₁bdef : δ₁b = r₀ / 2 * Real.pi * ‖MandelDim.piExp wt₀‖ * ‖S.s₀‖ / 16
  hδ₁bpos : 0 < δ₁b
  m₁ : ℝ
  hm₁def : m₁ = min ‖deriv S.d₁.φ S.ζa‖ ‖deriv S.d₁.φ S.ζb‖
  hm₁pos : 0 < m₁
  εa' : ℝ
  εb' : ℝ
  hεa'pos : 0 < εa'
  hεb'pos : 0 < εb'
  hsuba : Metric.closedBall S.ζa (2 * (εa' / 4)) ⊆ S.d₁.Dφ
  hsubb : Metric.closedBall S.ζb (2 * (εb' / 4)) ⊆ S.d₁.Dφ
  hCSρa : CS.ρ ≤ εa' / 4
  hCSρb : CS.ρ ≤ εb' / 4
  ρmax : ℝ
  hCSρle : CS.ρ ≤ ρmax
  Da : ℝ
  Db : ℝ
  hDa : ∀ z ∈ Metric.closedBall S.ζa (εa' / 4), ‖deriv S.d₁.φ z‖ ≤ Da
  hDb : ∀ z ∈ Metric.closedBall S.ζb (εb' / 4), ‖deriv S.d₁.φ z‖ ≤ Db
  D₁ : ℝ
  hD₁def : D₁ = max Da Db
  hD₁pos : 0 < D₁
  hDlim : ∀ z ∈ Metric.closedBall S.ζa CS.ρ, ‖deriv S.d₁.φ z‖ ≤ D₁
  hsubA : Metric.closedBall S.ζa CS.ρ ⊆ S.d₁.Dφ
  hsubB : Metric.closedBall S.ζb CS.ρ ⊆ S.d₁.Dφ
  hderivlowA : ∀ z ∈ Metric.ball S.ζa CS.ρ, ‖deriv S.d₁.φ S.ζa‖ * 2 / 3 ≤ ‖deriv S.d₁.φ z‖
  hderivlowB : ∀ z ∈ Metric.ball S.ζb CS.ρ, ‖deriv S.d₁.φ S.ζb‖ * 2 / 3 ≤ ‖deriv S.d₁.φ z‖
  hnormA : ∀ z ∈ Metric.ball S.ζa CS.ρ, ‖S.d₁.φ z‖ ≤ 2 * ‖S.d₁.φ S.ζa‖ + 1
  hnormB : ∀ z ∈ Metric.ball S.ζb CS.ρ, ‖S.d₁.φ z‖ ≤ 2 * ‖S.d₁.φ S.ζb‖ + 1
  hCSball : Metric.closedBall S.ζa (2 * CS.ρ) ∪ Metric.closedBall S.ζb (2 * CS.ρ) ⊆ S.d₁.Dφ
  hCSρ1 : CS.ρ ≤ 1 / 2
  hCSρD : CS.ρ * D₁ ≤ r₀ / 2 * Real.pi * ‖MandelDim.piExp wt₀‖ * ‖S.s₀‖ / 8
  K₂' : Set ℂ
  hK₂'c : IsCompact K₂'
  hK₂'suba : Metric.closedBall S.ζa (4 * CS.ρ) ⊆ K₂'
  hK₂'subb : Metric.closedBall S.ζb (4 * CS.ρ) ⊆ K₂'
  hK₂'Dφ : K₂' ⊆ S.d₁.Dφ
  hinj2ρA : Set.InjOn S.d₁.φ (Metric.closedBall S.ζa (2 * CS.ρ))
  hinj2ρB : Set.InjOn S.d₁.φ (Metric.closedBall S.ζb (2 * CS.ρ))
  Bd₁ : ℝ
  hBd₁ : ∀ z ∈ K₂', ‖S.d₁.φ z‖ ≤ Bd₁
  preM₀ : ℝ
  hpreM₀def : preM₀ = max (Bd + δb) 1 / (r₀ / 2)
  hpreM₀pos : 0 < preM₀
  preM₁ : ℝ
  hpreM₁def : preM₁ = max (Bd₁ + δ₁b) 1 / CS.ρ
  hpreM₁pos : 0 < preM₁
  Cb : ℝ
  hCbdef : Cb = max 1 (2 * (preM₀ * preM₁) / (‖S.s₀‖ * (2 * Real.pi * ‖MandelDim.piExp wt₀‖)))
  hCbpos : 0 < Cb
  hCbge : 2 * (preM₀ * preM₁) / (‖S.s₀‖ * (2 * Real.pi * ‖MandelDim.piExp wt₀‖)) ≤ Cb
  Hfit : ℝ
  hHfitdef : Hfit = 256 / (320 * (CS.C₀ + 1) * (10 ^ 12 * Cb ^ 2 * (CS.C₁' + 1) ^ 2))
  B₁ : ℝ
  hB₁def : B₁ = 2 * ‖S.d₁.φ S.ζa‖ + 1 + δ₁b
  hB₁pos : 0 < B₁
  cb : ℝ
  hcbdef : cb = g₀ * m₁ / (16 * Real.pi * B₁)
  hcbpos : 0 < cb
  Hfitlo : ℝ
  hHfitlodef : Hfitlo = (5 / 4) / ((CS.C₀ + 1) * CS.C₁ ^ 2 * cb ^ 2)
  δ₁ : ℝ
  hδ₁def : δ₁ = min (min (CS.δ / 2)
      (CS.ρ * min (‖deriv S.d₁.φ S.ζa‖) (‖deriv S.d₁.φ S.ζb‖) / 256))
      (r₀ / 2 * Real.pi * ‖MandelDim.piExp wt₀‖ * ‖S.s₀‖ / 16)
  hδ₁pos : 0 < δ₁
  hδ₁CS : δ₁ ≤ CS.δ / 2
  hδ₁der : δ₁ ≤ CS.ρ * min (‖deriv S.d₁.φ S.ζa‖) (‖deriv S.d₁.φ S.ζb‖) / 256
  hδ₁π : δ₁ ≤ r₀ / 2 * Real.pi * ‖MandelDim.piExp wt₀‖ * ‖S.s₀‖ / 16
  hδ₁ltCS : δ₁ < CS.δ

set_option maxHeartbeats 2500000 in
theorem r3_base (hParab : ParabStatement) (hPert : PertStatement) (hHorn : HornStatement)
    (hL61 : L61Statement) (hL62 : L62Statement) (hF0 : F0FactsStatement)
    (ε : ℝ) (hε : 0 < ε) (b : ℝ) (hb : 0 < b) :
    ∃ B : R3Base, B.ε = ε ∧ B.b = b := by
  obtain ⟨S, hζaDφ, hζaderiv, hζbDφ, hζbderiv, wt₀, hwt₀Dφ, hφwt₀, hderwt, hζaφ, hζbφ⟩ :=
    setup_exists_v4 hParab hHorn hL61 hF0
  have hs₀pos : 0 < ‖S.s₀‖ := norm_pos_iff.mpr S.hne
  -- ## The level-0 target data around `wt₀`
  have hwt_nhds : S.d₀.Dφ ∈ 𝓝 wt₀ := S.d₀.Dφ_open.mem_nhds hwt₀Dφ
  obtain ⟨εw, hεwpos, hεwsub⟩ := Metric.mem_nhds_iff.mp hwt_nhds
  obtain ⟨r₁, hr₁pos, hr₁inj⟩ := locally_inj_of_deriv_ne_zero
    (S.d₀.φ_holo.analyticAt hwt_nhds) hderwt
  -- v8: a disc on which `‖(d₀.φ)'‖` does not drop below `(2/3)‖(d₀.φ)'(wt₀)‖`
  obtain ⟨r₁d, hr₁dpos, -, hr₁dbd⟩ := deriv_lower_half S.d₀.Dφ_open S.d₀.φ_holo hwt₀Dφ
  set r₀ : ℝ := min (min (min r₁ r₁d) (εw / 4)) (1 / 200) with hr₀def
  have hr₀pos : 0 < r₀ := lt_min (lt_min (lt_min hr₁pos hr₁dpos) (by linarith)) (by norm_num)
  have hr₀le200 : r₀ ≤ 1 / 200 := min_le_right _ _
  have hr₀le_r₁ : r₀ ≤ r₁ :=
    le_trans (min_le_left _ _) (le_trans (min_le_left _ _) (min_le_left _ _))
  have hr₀le_r₁d : r₀ ≤ r₁d :=
    le_trans (min_le_left _ _) (le_trans (min_le_left _ _) (min_le_right _ _))
  have hr₀le_w : r₀ ≤ εw / 4 := le_trans (min_le_left _ _) (min_le_right _ _)
  have hr₀sub : Metric.closedBall wt₀ (2 * r₀) ⊆ S.d₀.Dφ := by
    intro z hz
    apply hεwsub
    rw [Metric.mem_ball, dist_eq_norm]
    rw [Metric.mem_closedBall, dist_eq_norm] at hz
    linarith
  have hr₀sub' : Metric.closedBall wt₀ r₀ ⊆ S.d₀.Dφ :=
    (Metric.closedBall_subset_closedBall (by linarith)).trans hr₀sub
  have hr₀inj : Set.InjOn S.d₀.φ (Metric.ball wt₀ r₀) :=
    hr₁inj.mono (Metric.ball_subset_ball hr₀le_r₁)
  have hK₀'c : IsCompact (Metric.closedBall wt₀ (2 * r₀)) := isCompact_closedBall _ _
  have hdwtpos : 0 < ‖deriv S.d₀.φ wt₀‖ := norm_pos_iff.mpr hderwt
  set g₀ : ℝ := ‖deriv S.d₀.φ wt₀‖ with hg₀def
  have hg₀pos : 0 < g₀ := hdwtpos
  set σL : ℝ := g₀ * r₀ / 256 with hσLdef
  have hσLpos : 0 < σL := by rw [hσLdef]; exact div_pos (mul_pos hg₀pos hr₀pos) (by norm_num)
  -- ## A fixed neighbourhood of the two level-1 starting points, and derivative bounds
  obtain ⟨εa', hεa'pos, hεa'sub⟩ := Metric.mem_nhds_iff.mp (S.d₁.Dφ_open.mem_nhds hζaDφ)
  obtain ⟨εb', hεb'pos, hεb'sub⟩ := Metric.mem_nhds_iff.mp (S.d₁.Dφ_open.mem_nhds hζbDφ)
  have hRa : (0:ℝ) < εa' / 4 := by linarith
  have hRb : (0:ℝ) < εb' / 4 := by linarith
  have hsuba : Metric.closedBall S.ζa (2 * (εa' / 4)) ⊆ S.d₁.Dφ := by
    intro z hz
    apply hεa'sub
    rw [Metric.mem_ball, dist_eq_norm]
    rw [Metric.mem_closedBall, dist_eq_norm] at hz
    linarith
  have hsubb : Metric.closedBall S.ζb (2 * (εb' / 4)) ⊆ S.d₁.Dφ := by
    intro z hz
    apply hεb'sub
    rw [Metric.mem_ball, dist_eq_norm]
    rw [Metric.mem_closedBall, dist_eq_norm] at hz
    linarith
  obtain ⟨r₂a, hr₂apos, hr₂ainj⟩ := locally_inj_of_deriv_ne_zero
    (S.d₁.φ_holo.analyticAt (S.d₁.Dφ_open.mem_nhds hζaDφ)) hζaderiv
  obtain ⟨r₂b, hr₂bpos, hr₂binj⟩ := locally_inj_of_deriv_ne_zero
    (S.d₁.φ_holo.analyticAt (S.d₁.Dφ_open.mem_nhds hζbDφ)) hζbderiv
  obtain ⟨Da, hDa0, hDa⟩ := deriv_bound_on_ball (g := S.d₁.φ) S.d₁.φ_holo hRa hsuba
  obtain ⟨Db, hDb0, hDb⟩ := deriv_bound_on_ball (g := S.d₁.φ) S.d₁.φ_holo hRb hsubb
  set D₁ : ℝ := max Da Db with hD₁def
  have hD₁pos : 0 < D₁ := lt_of_lt_of_le hDa0 (le_max_left _ _)
  have hπwt : 0 < ‖MandelDim.piExp wt₀‖ := norm_pos_iff.mpr (Work.Horn.MandelDim.piExp_ne_zero wt₀)
  have hρ₀pos : 0 < r₀ / 2 := by linarith
  -- ## The chain, with `ρ` small
  -- v8: the two discs on which the level-1 derivatives do not drift by more than 3/2 resp. 2
  obtain ⟨rLa, hrLapos, -, hrLabd⟩ := deriv_lower_half S.d₁.Dφ_open S.d₁.φ_holo hζaDφ
  obtain ⟨rLb, hrLbpos, -, hrLbbd⟩ := deriv_lower_half S.d₁.Dφ_open S.d₁.φ_holo hζbDφ
  obtain ⟨rUa, hrUapos, -, hrUabd⟩ := norm_upper_double S.d₁.Dφ_open S.d₁.φ_holo hζaDφ
  obtain ⟨rUb, hrUbpos, -, hrUbbd⟩ := norm_upper_double S.d₁.Dφ_open S.d₁.φ_holo hζbDφ
  set ρL : ℝ := min (min rLa rLb) (min rUa rUb) with hρLdef
  have hρLpos : 0 < ρL := lt_min (lt_min hrLapos hrLbpos) (lt_min hrUapos hrUbpos)
  have hρLla : ρL ≤ rLa := le_trans (min_le_left _ _) (min_le_left _ _)
  have hρLlb : ρL ≤ rLb := le_trans (min_le_left _ _) (min_le_right _ _)
  have hρLua : ρL ≤ rUa := le_trans (min_le_right _ _) (min_le_left _ _)
  have hρLub : ρL ≤ rUb := le_trans (min_le_right _ _) (min_le_right _ _)
  set ρmax : ℝ := min (min (min (min (εa' / 8) (εb' / 8)) (min (r₂a / 4) (r₂b / 4)))
      (min (min (1 / 2) (r₀ / 2 * Real.pi * ‖MandelDim.piExp wt₀‖ * ‖S.s₀‖ / (8 * (D₁ + 1))))
        (50 * Real.pi * r₀ * ‖S.s₀‖ * ‖MandelDim.piExp wt₀‖ / D₁))) ρL
    with hρmaxdef
  have hρmaxpos : 0 < ρmax := by
    rw [hρmaxdef]
    exact lt_min (lt_min (lt_min (lt_min (by linarith) (by linarith))
      (lt_min (by linarith) (by linarith)))
      (lt_min (lt_min (by norm_num)
        (div_pos (mul_pos (mul_pos (mul_pos hρ₀pos Real.pi_pos) hπwt) hs₀pos)
          (by positivity)))
        (div_pos (mul_pos (mul_pos (mul_pos (mul_pos (by norm_num : (0 : ℝ) < 50) Real.pi_pos)
          hr₀pos) hs₀pos) hπwt) hD₁pos))) hρLpos
  have hρmax_le_a : ρmax ≤ εa' / 8 := by
    rw [hρmaxdef]
    exact le_trans (min_le_left _ _)
      (le_trans (min_le_left _ _) (le_trans (min_le_left _ _) (min_le_left _ _)))
  have hρmax_le_b : ρmax ≤ εb' / 8 := by
    rw [hρmaxdef]
    exact le_trans (min_le_left _ _)
      (le_trans (min_le_left _ _) (le_trans (min_le_left _ _) (min_le_right _ _)))
  have hρmax_le_2a : ρmax ≤ r₂a / 4 := by
    rw [hρmaxdef]
    exact le_trans (min_le_left _ _)
      (le_trans (min_le_left _ _) (le_trans (min_le_right _ _) (min_le_left _ _)))
  have hρmax_le_2b : ρmax ≤ r₂b / 4 := by
    rw [hρmaxdef]
    exact le_trans (min_le_left _ _)
      (le_trans (min_le_left _ _) (le_trans (min_le_right _ _) (min_le_right _ _)))
  have hρmax_le_half : ρmax ≤ 1 / 2 := by
    rw [hρmaxdef]
    exact le_trans (min_le_left _ _)
      (le_trans (min_le_right _ _) (le_trans (min_le_left _ _) (min_le_left _ _)))
  have hρmax_le_D : ρmax ≤ r₀ / 2 * Real.pi * ‖MandelDim.piExp wt₀‖ * ‖S.s₀‖ / (8 * (D₁ + 1)) := by
    rw [hρmaxdef]
    exact le_trans (min_le_left _ _)
      (le_trans (min_le_right _ _) (le_trans (min_le_left _ _) (min_le_right _ _)))
  have hρmax_le_m : ρmax ≤ 50 * Real.pi * r₀ * ‖S.s₀‖ * ‖MandelDim.piExp wt₀‖ / D₁ := by
    rw [hρmaxdef]
    exact le_trans (min_le_left _ _) (le_trans (min_le_right _ _) (min_le_right _ _))
  have hρmax_le_L : ρmax ≤ ρL := by rw [hρmaxdef]; exact min_le_right _ _
  obtain ⟨CS, hCSρle, hCSball⟩ := chain_setup_v4 hL62 S b hb hζaDφ hζbDφ ρmax hρmaxpos
  have hCSρL : CS.ρ ≤ ρL := le_trans hCSρle hρmax_le_L
  have hCSρ1 : CS.ρ ≤ 1 / 2 := le_trans hCSρle hρmax_le_half
  have hCSρa : CS.ρ ≤ εa' / 4 := by linarith [hCSρle, hρmax_le_a]
  have hCSρb : CS.ρ ≤ εb' / 4 := by linarith [hCSρle, hρmax_le_b]
  have hCSρ2a : CS.ρ ≤ r₂a := by linarith [hCSρle, hρmax_le_2a]
  have hCSρ2b : CS.ρ ≤ r₂b := by linarith [hCSρle, hρmax_le_2b]
  have hCSρ2a' : 2 * CS.ρ < r₂a := by linarith [hCSρle, hρmax_le_2a]
  have hCSρ2b' : 2 * CS.ρ < r₂b := by linarith [hCSρle, hρmax_le_2b]
  have hCSρla : CS.ρ ≤ rLa := le_trans hCSρL hρLla
  have hCSρlb : CS.ρ ≤ rLb := le_trans hCSρL hρLlb
  have hCSρua : CS.ρ ≤ rUa := le_trans hCSρL hρLua
  have hCSρub : CS.ρ ≤ rUb := le_trans hCSρL hρLub
  have hCSρD : CS.ρ * D₁ ≤ r₀ / 2 * Real.pi * ‖MandelDim.piExp wt₀‖ * ‖S.s₀‖ / 8 := by
    have h1 : CS.ρ ≤ r₀ / 2 * Real.pi * ‖MandelDim.piExp wt₀‖ * ‖S.s₀‖ / (8 * (D₁ + 1)) :=
      le_trans hCSρle hρmax_le_D
    have h2 : CS.ρ * D₁ ≤ CS.ρ * (D₁ + 1) := by nlinarith [le_of_lt CS.hρ, hD₁pos]
    have h3 : CS.ρ * (D₁ + 1) ≤ r₀ / 2 * Real.pi * ‖MandelDim.piExp wt₀‖ * ‖S.s₀‖ / 8 := by
      have hpos : (0:ℝ) < 8 * (D₁ + 1) := by positivity
      have h4 : CS.ρ * (8 * (D₁ + 1)) ≤ r₀ / 2 * Real.pi * ‖MandelDim.piExp wt₀‖ * ‖S.s₀‖ := by
        rw [le_div_iff₀ hpos] at h1
        linarith [h1]
      linarith [h4]
    linarith [h2, h3]
  -- ## The level-1 target compact, the target-side constant `Cb` and the fit threshold
  -- (everything here is `η`- and `a₁a₂β`-independent: it is computed *before* `η` is chosen,
  --  which is what makes the `dim_arith` constant available at the time `Γ` is produced)
  set K₂' : Set ℂ := Metric.closedBall S.ζa (4 * CS.ρ) ∪ Metric.closedBall S.ζb (4 * CS.ρ)
    with hK₂'def
  have hK₂'c : IsCompact K₂' := by
    rw [hK₂'def]
    exact (isCompact_closedBall _ _).union (isCompact_closedBall _ _)
  have hK₂'Dφ : K₂' ⊆ S.d₁.Dφ := by
    rw [hK₂'def]
    intro z hz
    rcases hz with hz | hz
    · exact hsuba (Metric.closedBall_subset_closedBall (by linarith [hCSρle, hρmax_le_a]) hz)
    · exact hsubb (Metric.closedBall_subset_closedBall (by linarith [hCSρle, hρmax_le_b]) hz)
  -- bounds for the two unperturbed Fatou coordinates on the target compacts
  obtain ⟨Bd, hBd⟩ := (isCompact_closedBall wt₀ r₀).exists_bound_of_continuousOn
    (S.d₀.φ_holo.continuousOn.mono hr₀sub')
  obtain ⟨Bd₁, hBd₁⟩ := hK₂'c.exists_bound_of_continuousOn
    (S.d₁.φ_holo.continuousOn.mono hK₂'Dφ)
  set δb : ℝ := 1 / (16 * Real.pi) with hδbdef
  set δ₁b : ℝ := r₀ / 2 * Real.pi * ‖MandelDim.piExp wt₀‖ * ‖S.s₀‖ / 16 with hδ₁bdef
  set preM₀ : ℝ := max (Bd + δb) 1 / (r₀ / 2) with hpreM₀def
  set preM₁ : ℝ := max (Bd₁ + δ₁b) 1 / CS.ρ with hpreM₁def
  have hpreM₀pos : 0 < preM₀ := by
    rw [hpreM₀def]
    exact div_pos (lt_of_lt_of_le one_pos (le_max_right _ _)) (by linarith)
  have hpreM₁pos : 0 < preM₁ := by
    rw [hpreM₁def]
    exact div_pos (lt_of_lt_of_le one_pos (le_max_right _ _)) CS.hρ
  set Cb : ℝ := max 1 (2 * (preM₀ * preM₁) / (‖S.s₀‖ * (2 * Real.pi * ‖MandelDim.piExp wt₀‖)))
    with hCbdef
  have hCbpos : 0 < Cb := lt_of_lt_of_le one_pos (le_max_left _ _)
  have hCbge : 2 * (preM₀ * preM₁) / (‖S.s₀‖ * (2 * Real.pi * ‖MandelDim.piExp wt₀‖)) ≤ Cb :=
    le_max_right _ _
  set Hfit : ℝ := 256 / (320 * (CS.C₀ + 1) * (10 ^ 12 * Cb ^ 2 * (CS.C₁' + 1) ^ 2))
    with hHfitdef
  -- v8: the constant `cb` of the LOWER bound `hcblo` on the target-side factor, and the
  -- threshold `Hfitlo` of `hfitlo` (everything `η`-independent)
  set m₁ : ℝ := min ‖deriv S.d₁.φ S.ζa‖ ‖deriv S.d₁.φ S.ζb‖ with hm₁def
  have hm₁pos : 0 < m₁ := lt_min (norm_pos_iff.mpr hζaderiv) (norm_pos_iff.mpr hζbderiv)
  set B₁ : ℝ := 2 * ‖S.d₁.φ S.ζa‖ + 1 + δ₁b with hB₁def
  have hδ₁bpos : 0 < δ₁b := by rw [hδ₁bdef]; positivity
  have hB₁pos : 0 < B₁ := by rw [hB₁def]; linarith [norm_nonneg (S.d₁.φ S.ζa), hδ₁bpos]
  set cb : ℝ := g₀ * m₁ / (16 * Real.pi * B₁) with hcbdef
  have hcbpos : 0 < cb := by
    rw [hcbdef]
    exact div_pos (mul_pos hg₀pos hm₁pos) (by positivity)
  set Hfitlo : ℝ := (5 / 4) / ((CS.C₀ + 1) * CS.C₁ ^ 2 * cb ^ 2) with hHfitlodef
  
  -- ## The level-1 perturbation scale
  have hδ₁pos : 0 < min (‖deriv S.d₁.φ S.ζa‖) (‖deriv S.d₁.φ S.ζb‖) :=
    lt_min (norm_pos_iff.mpr hζaderiv) (norm_pos_iff.mpr hζbderiv)
  set δ₁ : ℝ := min (min (CS.δ / 2)
      (CS.ρ * min (‖deriv S.d₁.φ S.ζa‖) (‖deriv S.d₁.φ S.ζb‖) / 256))
      (r₀ / 2 * Real.pi * ‖MandelDim.piExp wt₀‖ * ‖S.s₀‖ / 16) with hδ₁def
  have hδ₁pos' : 0 < δ₁ := by
    rw [hδ₁def]
    exact lt_min (lt_min (by linarith [CS.hδ])
      (div_pos (mul_pos CS.hρ hδ₁pos) (by norm_num))) (by positivity)
  have hδ₁CS : δ₁ ≤ CS.δ / 2 := le_trans (min_le_left _ _) (min_le_left _ _)
  have hδ₁der : δ₁ ≤ CS.ρ * min (‖deriv S.d₁.φ S.ζa‖) (‖deriv S.d₁.φ S.ζb‖) / 256 :=
    le_trans (min_le_left _ _) (min_le_right _ _)
  have hδ₁π : δ₁ ≤ r₀ / 2 * Real.pi * ‖MandelDim.piExp wt₀‖ * ‖S.s₀‖ / 16 := min_le_right _ _
  have hδ₁ltCS : δ₁ < CS.δ := by linarith [hδ₁CS, CS.hδ]
  refine ⟨{ ε := ε, hε := hε, b := b, hb := hb, S := S, CS := CS, wt₀ := wt₀, hwt₀Dφ := hwt₀Dφ, hφwt₀ := hφwt₀, hderwt := hderwt, hζaDφ := hζaDφ, hζaderiv := hζaderiv, hζbDφ := hζbDφ, hζbderiv := hζbderiv, hζaφ := hζaφ, hζbφ := hζbφ, hs₀pos := hs₀pos, r₀ := r₀, hr₀pos := hr₀pos, hr₀le200 := hr₀le200, hr₀sub := hr₀sub, hr₀sub' := hr₀sub', hr₀inj := hr₀inj, hK₀'c := hK₀'c, hderivlow₀ := ?_, g₀ := g₀, hg₀def := hg₀def, hg₀pos := hg₀pos, σL := σL, hσLdef := hσLdef, hσLpos := hσLpos, Bd := Bd, hBd := hBd, δb := δb, hδbdef := hδbdef, δ₁b := δ₁b, hδ₁bdef := hδ₁bdef, hδ₁bpos := hδ₁bpos, m₁ := m₁, hm₁def := hm₁def, hm₁pos := hm₁pos, εa' := εa', εb' := εb', hεa'pos := hεa'pos, hεb'pos := hεb'pos, hsuba := hsuba, hsubb := hsubb, hCSρa := hCSρa, hCSρb := hCSρb, ρmax := ρmax, hCSρle := hCSρle, Da := Da, Db := Db, hDa := hDa, hDb := hDb, D₁ := D₁, hD₁def := hD₁def, hD₁pos := hD₁pos, hDlim := ?_, hsubA := ?_, hsubB := ?_, hderivlowA := ?_, hderivlowB := ?_, hnormA := ?_, hnormB := ?_, hCSball := hCSball, hCSρ1 := hCSρ1, hCSρD := hCSρD, K₂' := K₂', hK₂'c := hK₂'c, hK₂'suba := ?_, hK₂'subb := ?_, hK₂'Dφ := hK₂'Dφ, hinj2ρA := ?_, hinj2ρB := ?_, Bd₁ := Bd₁, hBd₁ := hBd₁, preM₀ := preM₀, hpreM₀def := hpreM₀def, hpreM₀pos := hpreM₀pos, preM₁ := preM₁, hpreM₁def := hpreM₁def, hpreM₁pos := hpreM₁pos, Cb := Cb, hCbdef := hCbdef, hCbpos := hCbpos, hCbge := hCbge, Hfit := Hfit, hHfitdef := hHfitdef, B₁ := B₁, hB₁def := hB₁def, hB₁pos := hB₁pos, cb := cb, hcbdef := hcbdef, hcbpos := hcbpos, Hfitlo := Hfitlo, hHfitlodef := hHfitlodef, δ₁ := δ₁, hδ₁def := hδ₁def, hδ₁pos := hδ₁pos', hδ₁CS := hδ₁CS, hδ₁der := hδ₁der, hδ₁π := hδ₁π, hδ₁ltCS := hδ₁ltCS }, rfl, rfl⟩
  · exact fun z hz => hr₁dbd z (Metric.ball_subset_ball hr₀le_r₁d hz)
  · intro z hz
    exact le_trans (hDa z (Metric.closedBall_subset_closedBall hCSρa hz)) (le_max_left _ _)
  · exact (Metric.closedBall_subset_closedBall (by linarith [hCSρa])).trans hsuba
  · exact (Metric.closedBall_subset_closedBall (by linarith [hCSρb])).trans hsubb
  · exact fun z hz => hrLabd z (Metric.ball_subset_ball hCSρla hz)
  · exact fun z hz => hrLbbd z (Metric.ball_subset_ball hCSρlb hz)
  · exact fun z hz => hrUabd z (Metric.ball_subset_ball hCSρua hz)
  · exact fun z hz => hrUbbd z (Metric.ball_subset_ball hCSρub hz)
  · rw [hK₂'def]; exact Set.subset_union_left
  · rw [hK₂'def]; exact Set.subset_union_right
  · exact hr₂ainj.mono (Metric.closedBall_subset_ball hCSρ2a')
  · exact hr₂binj.mono (Metric.closedBall_subset_ball hCSρ2b')
end
structure R3Pre extends R3Base where
  ηL0 : ℝ
  hηL0pos : 0 < ηL0
  ηL1 : ℝ
  hηL1pos : 0 < ηL1
  Na : ℕ
  hNa : ∀ a₁ : ℕ, Na ≤ a₁ → ∀ a₂ : ℕ, 4 ≤ a₂ → ∀ β : ℂ,
      0 ≤ β.re → β.re < 1 → |β.im| ≤ b →
      InF1 (alphaOf a₁ a₂ β) ∧
      ‖alphaOf a₁ a₂ β‖ ≤ 4 / (a₁ : ℝ) ∧
      ‖(1 : ℂ) / ((a₂ : ℂ) + β)‖ ≤ 2 / (a₂ : ℝ) ∧
      |((1 : ℂ) / ((a₂ : ℂ) + β)).re| ≤ 1 / 2 ∧
      ‖Complex.exp (2 * Real.pi * I * (1 / ((a₂ : ℂ) + β))) - 1‖ ≤ 32 / (a₂ : ℝ) ∧
      ‖(a₁ : ℂ) - 1 / ((a₂ : ℂ) + β)‖ ≥ (a₁ : ℝ) / 2 ∧
      alphaOf a₁ a₂ β ≠ 0
  Γ : ℝ
  Cconst : ℝ
  γc : ℝ
  hγcdef : γc = 1 / (320 * (max CS.C₀ 0 + 1) * ‖S.s₀‖ ^ 2)
  hγcpos : 0 < γc
  hCconstdef : Cconst = 10 ^ 6 * Cb * (|CS.C₁'| + 1) / ‖S.s₀‖ + 2
  hΓ : ∀ η N K : ℝ, Γ ≤ η →
      γc * η * (Real.exp (2 * Real.pi * η)) ^ 2 ≤ N →
      K ≤ Cconst * η ^ 2 * Real.exp (2 * Real.pi * η) → 1 < K →
      2 - ε ≤ Real.log N / Real.log K
  y₀ : ℝ
  hy₀def : y₀ = S.d₀.η₀ + 1
  hy₀ : S.d₀.η₀ < y₀
  η : ℝ
  hηpos : 0 < η
  hη100 : 100 ≤ η
  hηHfit : Hfit ≤ η
  hηHfitlo : Hfitlo ≤ η
  hηL0le : ηL0 ≤ η
  hΓle : Γ ≤ η
  hηy : 8 * y₀ / 7 ≤ η
  hηwt : ‖wt₀‖ + r₀ / 2 ≤ 2 * η
  hσLbig : 4 / η ≤ σL
  hζa_le : |S.ζa.im| ≤ η / 4
  hζb_le : |S.ζb.im| ≤ η / 4
  hDflat : ∀ z ∈ Dflat η, y₀ ≤ |z.im|
  η₁ : ℝ
  hη₁def : η₁ = Real.exp (2 * Real.pi * η) / ‖S.s₀‖
  hη₁mul : η₁ * ‖S.s₀‖ = Real.exp (2 * Real.pi * η)
  hη₁pos : 0 < η₁
  hL1le : ηL1 ≤ η₁
  hsize : 64 * (CS.C₀ + 1) ≤ η₁
  hηlt : η < η₁
  hη₁big : 2 * (max ‖S.ζa‖ ‖S.ζb‖ + CS.ρ) ≤ η₁
  hfitlo : 4 * (η * η₁ ^ 2 / (320 * (CS.C₀ + 1))) ≤ (CS.C₁ * cb * η ^ 2 * η₁ / 10) ^ 2
  hηtgt : 10 ^ 7 * Real.pi * ‖S.s₀ * MandelDim.piExp wt₀‖ / (g₀ * m₁ * CS.ρ) ≤ η
  L₁ : Set ℂ
  hL₁c : IsCompact L₁
  hL₁sub : L₁ ⊆ Dg0germ S.d₀ S.hd₀
  δ₁₀ : ℝ
  hδ₁₀pos : 0 < δ₁₀
  hL1uniq : ∀ (f : ℂ → ℂ) (Df : Set ℂ),
      NearOn (g0germ S.d₀) f Df L₁ δ₁₀ → f 0 = 0 → InF1 (rotOf f) →
      Nonempty (PertData S.d₁ f Df η₁ CS.y₁ CS.K₂ K₂' δ₁)
  K : Set ℂ
  hKc : IsCompact K
  hKsub : K ⊆ S.d₀.DE
  hcover : ∀ ζ ∈ L₁, ζ ≠ 0 →
      Complex.log (ζ / S.s₀) / (2 * Real.pi * I) ∈ K ∪ {w : ℂ | y₀ ≤ |w.im|}
  B : ℝ
  hB0 : 0 ≤ B
  hB : ∀ ζ ∈ L₁, ζ ≠ 0 →
      ‖MandelDim.piExp (S.d₀.E (Complex.log (ζ / S.s₀) / (2 * Real.pi * I)))‖ ≤ B
  cB : ℝ
  hcBdef : cB = ‖S.s₀‖ * B
  hcB0 : 0 ≤ cB
  δ : ℝ
  hδdef : δ = min (min (min (1 / (16 * Real.pi)) (δ₁₀ / (4096 * (cB + 1))))
      (g₀ * r₀ / 256))
      (m₁ * CS.ρ * g₀ / (10 ^ 8 * Real.pi * ‖S.s₀ * MandelDim.piExp wt₀‖))
  hδpos : 0 < δ
  hδle : δ ≤ 1 / (16 * Real.pi)
  hδbd : δ ≤ δ₁₀ / (4096 * (cB + 1))
  hδcap : δ ≤ g₀ * r₀ / 256
  hδsmall : 10 ^ 8 * Real.pi * δ * ‖S.s₀ * MandelDim.piExp wt₀‖ ≤ g₀ * m₁ * CS.ρ
  L₀ : Set ℂ
  hL₀c : IsCompact L₀
  δ₀₀ : ℝ
  hδ₀₀pos : 0 < δ₀₀
  hL0uniq : ∀ (f : ℂ → ℂ) (Df : Set ℂ),
      NearOn f0 f Df L₀ δ₀₀ → f 0 = 0 → InF1 (rotOf f) →
      Nonempty (PertData S.d₀ f Df η y₀ K (Metric.closedBall wt₀ (2 * r₀)) δ)
  M₀ : ℝ
  hM₀0 : 0 ≤ M₀
  hM₀ : ∀ z ∈ L₀, ‖z‖ ≤ M₀
  N₁ : ℕ
  N₂ : ℕ
  hNa_le : Na ≤ N₁
  h32_le : 32 ≤ N₁
  hM_le : Nat.ceil (16 * Real.pi * M₀ / δ₀₀ + 1) ≤ N₁
  h201_le : Nat.ceil (201 * (η + 1)) ≤ N₁
  h4_le : 4 ≤ N₂
  hb_le : Nat.ceil (b + 1) ≤ N₂
  hcB_le : Nat.ceil (768 * cB / δ₁₀ + 1) ≤ N₂
  h17_le : Nat.ceil (17 * Real.exp (2 * Real.pi * η) + b + 1) ≤ N₂
  hN₂η : Nat.ceil (8 * η₁ + 1) ≤ N₂

set_option maxHeartbeats 2500000 in
theorem r3_pre (hParab : ParabStatement) (hPert : PertStatement) (hHorn : HornStatement)
    (hL61 : L61Statement) (hL62 : L62Statement) (hF0 : F0FactsStatement)
    (Bpre : R3Base) :
    ∃ B : R3Pre, B.ε = Bpre.ε ∧ B.b = Bpre.b := by
-- ## Thresholds and the scale `η`
  have hF0in : InF0 f0 univ := hF0.1
  obtain ⟨ηL0, hηL0pos, hL0stmt⟩ := hPert f0 univ Bpre.S.d₀ hF0in.1
  obtain ⟨ηL1, hηL1pos, hL1stmt⟩ :=
    hPert (g0germ Bpre.S.d₀) (Dg0germ Bpre.S.d₀ Bpre.S.hd₀) Bpre.S.d₁ (isParabolicGerm_g0germ Bpre.S.d₀ Bpre.S.hd₀)
  have hγ : (0 : ℝ) < 1 / (320 * (max Bpre.CS.C₀ 0 + 1) * ‖Bpre.S.s₀‖ ^ 2) := by
    have h1 : (0 : ℝ) < 320 * (max Bpre.CS.C₀ 0 + 1) * ‖Bpre.S.s₀‖ ^ 2 := by
      have h2 : (0 : ℝ) < 320 * (max Bpre.CS.C₀ 0 + 1) := by positivity
      have h4 : 0 < ‖Bpre.S.s₀‖ := Bpre.hs₀pos
      exact mul_pos h2 (by positivity)
    exact one_div_pos.mpr h1
  have hCpos : (0 : ℝ) < 10 ^ 6 * Bpre.Cb * (|Bpre.CS.C₁'| + 1) / ‖Bpre.S.s₀‖ + 2 := by
    have h1 : (0 : ℝ) ≤ 10 ^ 6 * Bpre.Cb * (|Bpre.CS.C₁'| + 1) / ‖Bpre.S.s₀‖ :=
      div_nonneg (mul_nonneg (mul_nonneg (by norm_num) (le_of_lt Bpre.hCbpos))
        (by linarith [abs_nonneg Bpre.CS.C₁'])) (norm_nonneg _)
    linarith
  obtain ⟨Γ, hΓ⟩ := dim_arith Bpre.ε (10 ^ 6 * Bpre.Cb * (|Bpre.CS.C₁'| + 1) / ‖Bpre.S.s₀‖ + 2)
    (1 / (320 * (max Bpre.CS.C₀ 0 + 1) * ‖Bpre.S.s₀‖ ^ 2)) Bpre.hε hCpos hγ
  set Cconst : ℝ := 10 ^ 6 * Bpre.Cb * (|Bpre.CS.C₁'| + 1) / ‖Bpre.S.s₀‖ + 2 with hCconstdef
  set γc : ℝ := 1 / (320 * (max Bpre.CS.C₀ 0 + 1) * ‖Bpre.S.s₀‖ ^ 2) with hγcdef
  have hγcpos : 0 < γc := by rw [hγcdef]; positivity
  have hΓ' : ∀ η N K : ℝ, Γ ≤ η →
      γc * η * (Real.exp (2 * Real.pi * η)) ^ 2 ≤ N →
      K ≤ Cconst * η ^ 2 * Real.exp (2 * Real.pi * η) → 1 < K →
      2 - Bpre.ε ≤ Real.log N / Real.log K := by
    rw [hCconstdef, hγcdef]
    exact hΓ
  obtain ⟨Be1, hBe1⟩ := exists_exp_ge_const (ηL1 * ‖Bpre.S.s₀‖)
  obtain ⟨Be2, hBe2⟩ := exists_exp_ge_const (64 * (Bpre.CS.C₀ + 1) * ‖Bpre.S.s₀‖)
  obtain ⟨Be3, hBe3⟩ := exists_exp_ge_const ((max (‖Bpre.S.ζa‖ + Bpre.CS.ρ) (‖Bpre.S.ζb‖ + Bpre.CS.ρ)) * ‖Bpre.S.s₀‖ / 2)
  obtain ⟨Be4, hBe4⟩ := exists_exp_ge_const (2 * (max ‖Bpre.S.ζa‖ ‖Bpre.S.ζb‖ + Bpre.ρmax) * ‖Bpre.S.s₀‖)
  obtain ⟨Bl1, hBl1⟩ := exists_eta_mul_lt_exp ‖Bpre.S.s₀‖
  set y₀ : ℝ := Bpre.S.d₀.η₀ + 1 with hy₀def
  have hy₀ : Bpre.S.d₀.η₀ < y₀ := by rw [hy₀def]; linarith
  have hnn : ∀ x : ℝ, 0 ≤ max x 0 := fun x => le_max_right x 0
  have hP1 : (0 : ℝ) ≤ max ηL0 0 := hnn ηL0
  have hP2 : (0 : ℝ) ≤ max Γ 0 := hnn Γ
  have hP3 : (0 : ℝ) ≤ max (4 / Bpre.σL) 0 := hnn _
  have hP4 : (0 : ℝ) ≤ max (8 * y₀ / 7) 0 := hnn _
  have hP5 : (0 : ℝ) ≤ max Be1 0 := hnn Be1
  have hP6 : (0 : ℝ) ≤ max Be2 0 := hnn Be2
  have hP7 : (0 : ℝ) ≤ max Be3 0 := hnn Be3
  have hP8 : (0 : ℝ) ≤ max Bl1 0 := hnn Bl1
  have hP9 : (0 : ℝ) ≤ max (4 * (|Bpre.S.ζa.im| + |Bpre.S.ζb.im| + 1)) 0 := hnn _
  have hP10 : (0 : ℝ) ≤ max (‖Bpre.wt₀‖ + Bpre.r₀ / 2) 0 := hnn _
  have hP11 : (0 : ℝ) ≤ max Bpre.Hfit 0 := hnn _
  have hP12 : (0 : ℝ) ≤ max Bpre.Hfitlo 0 := hnn _
  have hP13 : (0 : ℝ) ≤ max Be4 0 := hnn _
  have hP14 : (0 : ℝ) ≤ max (4 / Bpre.σL) 0 := hnn _
  have hP15 : (0 : ℝ) ≤ max ((‖Bpre.wt₀‖ + Bpre.r₀ / 2) / 2) 0 := hnn _
  have hP16 : (0 : ℝ) ≤ max (10 ^ 7 * Real.pi * ‖Bpre.S.s₀ * MandelDim.piExp Bpre.wt₀‖ / (Bpre.g₀ * Bpre.m₁ * Bpre.CS.ρ)) 0 := hnn _
  set η : ℝ := (max ηL0 0 + 1) + (max Γ 0 + 1) + (max (4 / Bpre.σL) 0 + 1)
      + (max (8 * y₀ / 7) 0 + 1) + (max Be1 0 + 1) + (max Be2 0 + 1) + (max Be3 0 + 1)
      + (max Bl1 0 + 1) + (max (4 * (|Bpre.S.ζa.im| + |Bpre.S.ζb.im| + 1)) 0 + 1)
      + (max (‖Bpre.wt₀‖ + Bpre.r₀ / 2) 0 + 1) + (max Bpre.Hfit 0 + 1) + (max Bpre.Hfitlo 0 + 1) + (max Be4 0 + 1) + (max (4 / Bpre.σL) 0 + 1)
      + (max ((‖Bpre.wt₀‖ + Bpre.r₀ / 2) / 2) 0 + 1)
      + (max (10 ^ 7 * Real.pi * ‖Bpre.S.s₀ * MandelDim.piExp Bpre.wt₀‖ / (Bpre.g₀ * Bpre.m₁ * Bpre.CS.ρ)) 0 + 1) + 101
    with hηdef
  have hηL0le : ηL0 ≤ η := by rw [hηdef]; linarith only [le_max_left ηL0 0, hP1, hP2, hP3, hP4, hP5, hP6, hP7, hP8, hP9, hP10, hP11, hP12, hP13, hP14, hP15, hP16]
  have hΓle : Γ ≤ η := by rw [hηdef]; linarith only [le_max_left Γ 0, hP1, hP2, hP3, hP4, hP5, hP6, hP7, hP8, hP9, hP10, hP11, hP12, hP13, hP14, hP15, hP16]
  have hησ : 4 / Bpre.σL ≤ η := by rw [hηdef]; linarith only [le_max_left (4 / Bpre.σL) 0, hP1, hP2, hP3, hP4, hP5, hP6, hP7, hP8, hP9, hP10, hP11, hP12, hP13, hP14, hP15, hP16]
  have hηy : 8 * y₀ / 7 ≤ η := by rw [hηdef]; linarith only [le_max_left (8 * y₀ / 7) 0, hP1, hP2, hP3, hP4, hP5, hP6, hP7, hP8, hP9, hP10, hP11, hP12, hP13, hP14, hP15, hP16]
  have hηBe1 : Be1 ≤ η := by rw [hηdef]; linarith only [le_max_left Be1 0, hP1, hP2, hP3, hP4, hP5, hP6, hP7, hP8, hP9, hP10, hP11, hP12, hP13, hP14, hP15, hP16]
  have hηBe2 : Be2 ≤ η := by rw [hηdef]; linarith only [le_max_left Be2 0, hP1, hP2, hP3, hP4, hP5, hP6, hP7, hP8, hP9, hP10, hP11, hP12, hP13, hP14, hP15, hP16]
  have hηBe3 : Be3 ≤ η := by rw [hηdef]; linarith only [le_max_left Be3 0, hP1, hP2, hP3, hP4, hP5, hP6, hP7, hP8, hP9, hP10, hP11, hP12, hP13, hP14, hP15, hP16]
  have hηBe4 : Be4 ≤ η := by
    rw [hηdef]
    linarith only [le_max_left Be4 0, hP1, hP2, hP3, hP4, hP5, hP6, hP7, hP8, hP9, hP10, hP11,
      hP12, hP13, hP14, hP15, hP16]
  have hηBl1 : Bl1 ≤ η := by rw [hηdef]; linarith only [le_max_left Bl1 0, hP1, hP2, hP3, hP4, hP5, hP6, hP7, hP8, hP9, hP10, hP11, hP12, hP13, hP14, hP15, hP16]
  have hηζ : 4 * (|Bpre.S.ζa.im| + |Bpre.S.ζb.im| + 1) ≤ η := by
    rw [hηdef]; linarith only [le_max_left (4 * (|Bpre.S.ζa.im| + |Bpre.S.ζb.im| + 1)) 0, hP1, hP2, hP3, hP4, hP5, hP6, hP7, hP8, hP9, hP10, hP11, hP12, hP13, hP14, hP15, hP16]
  have hηwt : ‖Bpre.wt₀‖ + Bpre.r₀ / 2 ≤ η := by
    rw [hηdef]; linarith only [le_max_left (‖Bpre.wt₀‖ + Bpre.r₀ / 2) 0, hP1, hP2, hP3, hP4, hP5, hP6, hP7, hP8, hP9, hP10, hP11, hP12, hP13, hP14, hP15, hP16]
  have hηHfit : Bpre.Hfit ≤ η := by
    rw [hηdef]
    linarith only [le_max_left Bpre.Hfit 0, hP1, hP2, hP3, hP4, hP5, hP6, hP7, hP8, hP9, hP10, hP11, hP12, hP13, hP14, hP15, hP16]
  have hηHfitlo : Bpre.Hfitlo ≤ η := by
    rw [hηdef]
    linarith only [le_max_left Bpre.Hfitlo 0, hP1, hP2, hP3, hP4, hP5, hP6, hP7, hP8, hP9, hP10, hP11,
      hP12, hP13, hP14, hP15, hP16]
  have hη100 : (100 : ℝ) ≤ η := by rw [hηdef]; linarith only [hP1, hP2, hP3, hP4, hP5, hP6, hP7, hP8, hP9, hP10, hP11, hP12, hP13, hP14, hP15, hP16]
  have hηpos : (0 : ℝ) < η := by linarith
  have hηwt2 : ‖Bpre.wt₀‖ + Bpre.r₀ / 2 ≤ 2 * η := by linarith [hηwt]
  have hηT : 10 ^ 7 * Real.pi * ‖Bpre.S.s₀ * MandelDim.piExp Bpre.wt₀‖ / (Bpre.g₀ * Bpre.m₁ * Bpre.CS.ρ) ≤ η := by
    rw [hηdef]
    linarith only [le_max_left (10 ^ 7 * Real.pi * ‖Bpre.S.s₀ * MandelDim.piExp Bpre.wt₀‖ / (Bpre.g₀ * Bpre.m₁ * Bpre.CS.ρ)) 0, hP1, hP2, hP3, hP4, hP5, hP6, hP7, hP8, hP9, hP10,
      hP11, hP12, hP13, hP14, hP15, hP16]
  have hσLbig : 4 / η ≤ Bpre.σL := by
    rw [div_le_iff₀ hηpos]
    have h := (div_le_iff₀ Bpre.hσLpos).mp hησ
    linarith
  set η₁ : ℝ := Real.exp (2 * Real.pi * η) / ‖Bpre.S.s₀‖ with hη₁def
  have hη₁mul : η₁ * ‖Bpre.S.s₀‖ = Real.exp (2 * Real.pi * η) := by
    rw [hη₁def]; exact div_mul_cancel₀ _ (ne_of_gt Bpre.hs₀pos)
  have hη₁big : 2 * (max ‖Bpre.S.ζa‖ ‖Bpre.S.ζb‖ + Bpre.CS.ρ) ≤ η₁ := by
    have h1 : 2 * (max ‖Bpre.S.ζa‖ ‖Bpre.S.ζb‖ + Bpre.ρmax) * ‖Bpre.S.s₀‖ ≤ Real.exp (2 * Real.pi * η) :=
      le_trans (le_max_left _ _) (hBe4 η hηBe4)
    have h2 : 2 * (max ‖Bpre.S.ζa‖ ‖Bpre.S.ζb‖ + Bpre.CS.ρ) * ‖Bpre.S.s₀‖ ≤
        2 * (max ‖Bpre.S.ζa‖ ‖Bpre.S.ζb‖ + Bpre.ρmax) * ‖Bpre.S.s₀‖ := by
      have hle : max ‖Bpre.S.ζa‖ ‖Bpre.S.ζb‖ + Bpre.CS.ρ ≤ max ‖Bpre.S.ζa‖ ‖Bpre.S.ζb‖ + Bpre.ρmax :=
        by linarith [Bpre.hCSρle]
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hle (by norm_num)) (le_of_lt Bpre.hs₀pos)
    have h3 : 2 * (max ‖Bpre.S.ζa‖ ‖Bpre.S.ζb‖ + Bpre.CS.ρ) * ‖Bpre.S.s₀‖ ≤ η₁ * ‖Bpre.S.s₀‖ := by
      rw [hη₁mul]
      exact le_trans h2 h1
    exact le_of_mul_le_mul_right h3 Bpre.hs₀pos
  have hη₁pos : 0 < η₁ := by rw [hη₁def]; exact div_pos (Real.exp_pos _) Bpre.hs₀pos
  have hL1le : ηL1 ≤ η₁ := by
    have h1 : ηL1 * ‖Bpre.S.s₀‖ ≤ Real.exp (2 * Real.pi * η) :=
      le_trans (le_max_left _ _) (hBe1 η hηBe1)
    have h2 : ηL1 * ‖Bpre.S.s₀‖ ≤ η₁ * ‖Bpre.S.s₀‖ := by rw [hη₁mul]; exact h1
    exact le_of_mul_le_mul_right h2 Bpre.hs₀pos
  have hsize : 64 * (Bpre.CS.C₀ + 1) ≤ η₁ := by
    have h1 : 64 * (Bpre.CS.C₀ + 1) * ‖Bpre.S.s₀‖ ≤ Real.exp (2 * Real.pi * η) :=
      le_trans (le_max_left _ _) (hBe2 η hηBe2)
    have h2 : 64 * (Bpre.CS.C₀ + 1) * ‖Bpre.S.s₀‖ ≤ η₁ * ‖Bpre.S.s₀‖ := by rw [hη₁mul]; exact h1
    exact le_of_mul_le_mul_right h2 Bpre.hs₀pos
  have hfitlo : 4 * (η * η₁ ^ 2 / (320 * (Bpre.CS.C₀ + 1))) ≤
      (Bpre.CS.C₁ * Bpre.cb * η ^ 2 * η₁ / 10) ^ 2 := by
    by_cases hC₀gt : 0 < Bpre.CS.C₀ + 1
    · exact fitlo_arith hηpos hη₁pos hC₀gt Bpre.CS.hC₁ Bpre.hcbpos
        (fitlo_key hC₀gt Bpre.CS.hC₁ Bpre.hcbpos Bpre.hHfitlodef
          (le_trans hηHfitlo (eta_le_cube (by linarith [hη100]))))
    · have hle : Bpre.CS.C₀ + 1 ≤ 0 := le_of_not_gt hC₀gt
      have h1 : 4 * (η * η₁ ^ 2 / (320 * (Bpre.CS.C₀ + 1))) ≤ 0 := by
        rw [show 4 * (η * η₁ ^ 2 / (320 * (Bpre.CS.C₀ + 1)))
            = 4 * η * η₁ ^ 2 / (320 * (Bpre.CS.C₀ + 1)) by ring]
        exact div_nonpos_of_nonneg_of_nonpos (by positivity) (by nlinarith [hle])
      have h2 : (0 : ℝ) ≤ (Bpre.CS.C₁ * Bpre.cb * η ^ 2 * η₁ / 10) ^ 2 := sq_nonneg _
      linarith
  have hζa_le : |Bpre.S.ζa.im| ≤ η / 4 := by
    have h1 : |Bpre.S.ζa.im| ≤ |Bpre.S.ζa.im| + |Bpre.S.ζb.im| + 1 := by linarith [abs_nonneg Bpre.S.ζb.im]
    linarith [hηζ]
  have hζb_le : |Bpre.S.ζb.im| ≤ η / 4 := by
    have h1 : |Bpre.S.ζb.im| ≤ |Bpre.S.ζa.im| + |Bpre.S.ζb.im| + 1 := by linarith [abs_nonneg Bpre.S.ζa.im]
    linarith [hηζ]
  have hηlt : η < η₁ := by
    have h1 : η * ‖Bpre.S.s₀‖ < Real.exp (2 * Real.pi * η) := hBl1 η hηBl1
    rw [hη₁def, lt_div_iff₀ Bpre.hs₀pos]
    exact h1
  have hDflat : ∀ z ∈ Dflat η, y₀ ≤ |z.im| := by
    intro z hz0
    have hz : z ∈ Metric.closedBall (Complex.I * (η : ℂ)) (|η| / 8) := hz0
    rw [Metric.mem_closedBall, dist_eq_norm] at hz
    rw [abs_of_pos hηpos] at hz
    have him0 : (z - Complex.I * (η : ℂ)).im = z.im - η := by
      simp only [Complex.sub_im, Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re,
        Complex.ofReal_im, mul_zero, zero_mul, zero_add, one_mul]
    have h1 : |(z - Complex.I * (η : ℂ)).im| ≤ ‖z - Complex.I * (η : ℂ)‖ :=
      Complex.abs_im_le_norm _
    rw [him0] at h1
    have him : |z.im - η| ≤ η / 8 := le_trans h1 hz
    have h2 : η - η / 8 ≤ z.im := by
      have := abs_le.mp him
      linarith [this.1]
    have h3 : (0 : ℝ) < z.im := by linarith [h2, hηpos]
    rw [abs_of_pos h3]
    have h4 : y₀ ≤ 7 * η / 8 := by linarith [hηy]
    linarith
  
-- ## The level-1 PertStatement
  obtain ⟨L₁, hL₁c, hL₁sub, δ₁₀, hδ₁₀pos, hL1uniq⟩ :=
    hL1stmt η₁ hL1le Bpre.CS.y₁ Bpre.CS.hy₁ Bpre.CS.K₂ Bpre.K₂'
      Bpre.CS.hK₂c Bpre.CS.hK₂sub Bpre.hK₂'c Bpre.hK₂'Dφ Bpre.δ₁ Bpre.hδ₁pos
  -- the level-0 horn compact covering the principal lifts of `L₁`
  have hLcover : ∀ ζ ∈ L₁, ζ ≠ 0 → ζ / Bpre.S.s₀ ∈ piExp '' (Bpre.S.hd₀.Bu ∪ Bpre.S.hd₀.Bl) := by
    intro ζ hζ hζne
    have h := hL₁sub hζ
    change ζ ∈ (fun ζ => s0 Bpre.S.d₀ * ζ) '' (insert 0 (piExp '' (Bpre.S.hd₀.Bu ∪ Bpre.S.hd₀.Bl))) at h
    obtain ⟨z, hz, hzζ⟩ := h
    have hzval : ζ / Bpre.S.s₀ = z := by
      rw [← hzζ]
      show s0 Bpre.S.d₀ * z / Bpre.S.s₀ = z
      rw [← Bpre.S.hs₀]
      exact mul_div_cancel_left₀ z Bpre.S.hne
    rw [Set.mem_insert_iff] at hz
    rcases hz with hz0 | hz
    · exact absurd (by rw [← hzζ, hz0]; simp) hζne
    · obtain ⟨u, hu, huz⟩ := hz
      exact ⟨u, hu, by rw [hzval, huz]⟩
  obtain ⟨K, hKc, hKsub, hcover⟩ :=
    lift_cover Bpre.S.d₀ Bpre.S.hd₀ Bpre.S.s₀ Bpre.S.hne L₁ hL₁c hLcover (Bpre.S.d₀.η₀ + 1)
  obtain ⟨B, hB0, hB⟩ := exists_bound_piExp_E Bpre.S.d₀ Bpre.S.hne hL₁c hKc hKsub (by linarith) hcover
  set cB : ℝ := ‖Bpre.S.s₀‖ * B with hcBdef
  have hcB0 : 0 ≤ cB := mul_nonneg (norm_nonneg _) hB0
  -- ## The level-0 closeness
  set δ : ℝ := min (min (min (1 / (16 * Real.pi)) (δ₁₀ / (4096 * (cB + 1))))
      (Bpre.g₀ * Bpre.r₀ / 256))
      (Bpre.m₁ * Bpre.CS.ρ * Bpre.g₀ / (10 ^ 8 * Real.pi * ‖Bpre.S.s₀ * MandelDim.piExp Bpre.wt₀‖))
    with hδdef
  have hDpos : 0 < ‖Bpre.S.s₀ * MandelDim.piExp Bpre.wt₀‖ := by
    rw [norm_pos_iff]
    exact mul_ne_zero (norm_ne_zero_iff.mp (ne_of_gt Bpre.hs₀pos)) (Complex.exp_ne_zero _)
  have hδpos : 0 < δ := by
    rw [hδdef]
    exact lt_min (lt_min (lt_min (by positivity) (div_pos hδ₁₀pos (by linarith [hcB0])))
      (div_pos (mul_pos Bpre.hg₀pos Bpre.hr₀pos) (by norm_num)))
      (div_pos (mul_pos (mul_pos Bpre.hm₁pos Bpre.CS.hρ) Bpre.hg₀pos)
        (mul_pos (mul_pos (by norm_num) Real.pi_pos) hDpos))
  have hδle : δ ≤ 1 / (16 * Real.pi) :=
    le_trans (min_le_left _ _) (le_trans (min_le_left _ _) (min_le_left _ _))
  have hδbd : δ ≤ δ₁₀ / (4096 * (cB + 1)) :=
    le_trans (min_le_left _ _) (le_trans (min_le_left _ _) (min_le_right _ _))
  have hδcap : δ ≤ Bpre.g₀ * Bpre.r₀ / 256 :=
    le_trans (min_le_left _ _) (min_le_right _ _)
  have hδsmall : 10 ^ 8 * Real.pi * δ * ‖Bpre.S.s₀ * MandelDim.piExp Bpre.wt₀‖ ≤
      Bpre.g₀ * Bpre.m₁ * Bpre.CS.ρ := by
    have hdiv : δ ≤ Bpre.m₁ * Bpre.CS.ρ * Bpre.g₀ /
        (10 ^ 8 * Real.pi * ‖Bpre.S.s₀ * MandelDim.piExp Bpre.wt₀‖) := min_le_right _ _
    have hB : 0 < 10 ^ 8 * Real.pi * ‖Bpre.S.s₀ * MandelDim.piExp Bpre.wt₀‖ :=
      mul_pos (mul_pos (by norm_num) Real.pi_pos) hDpos
    have h2 := mul_le_mul_of_nonneg_right hdiv (le_of_lt hB)
    rw [div_mul_cancel₀ _ (ne_of_gt hB)] at h2
    have h3 : 10 ^ 8 * Real.pi * δ * ‖Bpre.S.s₀ * MandelDim.piExp Bpre.wt₀‖ =
        δ * (10 ^ 8 * Real.pi * ‖Bpre.S.s₀ * MandelDim.piExp Bpre.wt₀‖) := by ring
    have h4 : Bpre.g₀ * Bpre.m₁ * Bpre.CS.ρ = Bpre.m₁ * Bpre.CS.ρ * Bpre.g₀ := by ring
    rw [h3, h4]
    exact h2
  -- ## The level-0 PertStatement
  obtain ⟨L₀, hL₀c, -, δ₀₀, hδ₀₀pos, hL0uniq⟩ :=
    hL0stmt η hηL0le y₀ hy₀ K (Metric.closedBall Bpre.wt₀ (2 * Bpre.r₀)) hKc hKsub
      Bpre.hK₀'c Bpre.hr₀sub δ hδpos
  obtain ⟨M₀, hM₀0, hM₀⟩ := exists_bound_norm_on_compact hL₀c
  -- ## The thresholds for `a₁` and `a₂`
  obtain ⟨Na, hNa⟩ := alphaOf_bounds Bpre.b (le_of_lt Bpre.hb)
  set N₁ : ℕ := max (max Na 32)
    (max (Nat.ceil (16 * Real.pi * M₀ / δ₀₀ + 1))
      (max (Nat.ceil (201 * (η + 1))) (Nat.ceil (η + 1)))) with hN₁def
  set N₂ : ℕ := max (max (max 4 (max (Nat.ceil (Bpre.b + 1)) (Nat.ceil (768 * cB / δ₁₀ + 1))))
    (Nat.ceil (17 * Real.exp (2 * Real.pi * η) + Bpre.b + 1))) (Nat.ceil (8 * η₁ + 1)) with hN₂def
  have hNa_le : Na ≤ N₁ := by
    rw [hN₁def]
    exact le_trans (le_max_left Na 32) (le_max_left (max Na 32) _)
  have h32_le : 32 ≤ N₁ := by
    rw [hN₁def]
    exact le_trans (le_max_right Na 32) (le_max_left (max Na 32) _)
  have hM_le : Nat.ceil (16 * Real.pi * M₀ / δ₀₀ + 1) ≤ N₁ := by
    rw [hN₁def]
    exact le_trans (le_max_left _ _) (le_max_right (max Na 32) _)
  have h201_le : Nat.ceil (201 * (η + 1)) ≤ N₁ := by
    rw [hN₁def]
    exact le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) (le_max_right _ _)
  have h4_le : 4 ≤ N₂ := by
    rw [hN₂def]
    exact le_trans (le_max_left 4 _) (le_trans (le_max_left _ _) (le_max_left _ _))
  have hb_le : Nat.ceil (Bpre.b + 1) ≤ N₂ := by
    rw [hN₂def]
    exact le_trans (le_trans (le_max_left _ _) (le_max_right _ _))
      (le_trans (le_max_left _ _) (le_max_left _ _))
  have hcB_le : Nat.ceil (768 * cB / δ₁₀ + 1) ≤ N₂ := by
    rw [hN₂def]
    exact le_trans (le_trans (le_max_right _ _) (le_max_right _ _))
      (le_trans (le_max_left _ _) (le_max_left _ _))
  have h17_le : Nat.ceil (17 * Real.exp (2 * Real.pi * η) + Bpre.b + 1) ≤ N₂ := by
    rw [hN₂def]
    exact le_trans (le_max_right _ _) (le_max_left _ _)
  have hη₁_le : Nat.ceil (8 * η₁ + 1) ≤ N₂ := by
    rw [hN₂def]
    exact le_max_right _ _
  have hηwt2 : ‖Bpre.wt₀‖ + Bpre.r₀ / 2 ≤ 2 * η := by linarith [hηwt]
  refine ⟨{ toR3Base := Bpre, ηL0 := ηL0, hηL0pos := hηL0pos, ηL1 := ηL1, hηL1pos := hηL1pos, Na := Na, hNa := hNa, Γ := Γ, Cconst := Cconst, γc := γc, hγcdef := hγcdef, hγcpos := hγcpos, hCconstdef := hCconstdef, hΓ := hΓ', y₀ := y₀, hy₀def := hy₀def, hy₀ := hy₀, η := η, hηpos := hηpos, hη100 := hη100, hηHfit := hηHfit, hηHfitlo := hηHfitlo, hηL0le := hηL0le, hΓle := hΓle, hηy := hηy, hηwt := hηwt2, hσLbig := hσLbig, hζa_le := hζa_le, hζb_le := hζb_le, hDflat := hDflat, η₁ := η₁, hη₁def := hη₁def, hη₁mul := hη₁mul, hη₁pos := hη₁pos, hL1le := hL1le, hsize := hsize, hηlt := hηlt, hη₁big := hη₁big, hfitlo := hfitlo, hηtgt := hηT, L₁ := L₁, hL₁c := hL₁c, hL₁sub := hL₁sub, δ₁₀ := δ₁₀, hδ₁₀pos := hδ₁₀pos, hL1uniq := hL1uniq, K := K, hKc := hKc, hKsub := hKsub, hcover := hcover, B := B, hB0 := hB0, hB := hB, cB := cB, hcBdef := hcBdef, hcB0 := hcB0, δ := δ, hδdef := hδdef, hδpos := hδpos, hδle := hδle, hδbd := hδbd, hδcap := hδcap, hδsmall := hδsmall, L₀ := L₀, hL₀c := hL₀c, δ₀₀ := δ₀₀, hδ₀₀pos := hδ₀₀pos, hL0uniq := hL0uniq, M₀ := M₀, hM₀0 := hM₀0, hM₀ := hM₀, N₁ := N₁, N₂ := N₂, hNa_le := hNa_le, h32_le := h32_le, hM_le := hM_le, h201_le := h201_le, h4_le := h4_le, hb_le := hb_le, hcB_le := hcB_le, h17_le := h17_le, hN₂η := hη₁_le }, rfl, rfl⟩

/-- The prelude: assemble `R3Base` and then `R3Pre`. -/
theorem r3_prelude (hParab : ParabStatement) (hPert : PertStatement) (hHorn : HornStatement)
    (hL61 : L61Statement) (hL62 : L62Statement) (hF0 : F0FactsStatement)
    (ε : ℝ) (hε : 0 < ε) (b : ℝ) (hb : 0 < b) :
    ∃ B : R3Pre, B.ε = ε ∧ B.b = b := by
  obtain ⟨B₁, h₁⟩ := r3_base hParab hPert hHorn hL61 hL62 hF0 ε hε b hb
  obtain ⟨B₂, h₂⟩ := r3_pre hParab hPert hHorn hL61 hL62 hF0 B₁
  exact ⟨B₂, by rw [h₂.1, h₁.1], by rw [h₂.2, h₁.2]⟩


end Work.Repel
