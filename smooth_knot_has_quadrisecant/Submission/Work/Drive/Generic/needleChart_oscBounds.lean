import Mathlib
import Submission.Work.Drive.AB.pinSetup
import Submission.Work.Drive.sweepChamferClean

namespace Work.Drive.Generic

open LeanEval.KnotTheory.Quadrisecant


/-! ## Helper estimates -/

private lemma chartE_norm_le (r : ℝ → Space) {d : BandArcData} (D : SweepData d)
    (lam δ₁ δ₂ ε : ℝ) (v : Space) : ‖chartE r D lam δ₁ δ₂ ε v‖ ≤ 1 := by
  rw [chartE, norm_smul]
  rcases eq_or_lt_of_le (norm_nonneg (chartUp r D lam δ₁ δ₂ ε v)) with h0 | h0
  · rw [← h0]; simp
  · rw [Real.norm_eq_abs, abs_of_pos (inv_pos.mpr h0), inv_mul_cancel₀ (ne_of_gt h0)]

private lemma exists_lift_bound {d : BandArcData} (D : SweepData d) :
    ∃ A : ℝ, 1 ≤ A ∧ ∀ x : ℝ, |taR D x| ≤ A ∧ |tbR D x| ≤ A := by
  obtain ⟨A₀, hA₀⟩ := (isCompact_univ (X := ↥unitInterval)).exists_bound_of_continuousOn
    D.cont_ta.continuousOn
  obtain ⟨A₁, hA₁⟩ := (isCompact_univ (X := ↥unitInterval)).exists_bound_of_continuousOn
    D.cont_tb.continuousOn
  refine ⟨max 1 (max A₀ A₁), le_max_left _ _, fun x => ⟨?_, ?_⟩⟩
  · have h : |taR D x| ≤ A₀ := by
      have h' := hA₀ (clampI x) (Set.mem_univ _)
      simpa [taR, Real.norm_eq_abs] using h'
    exact h.trans (le_trans (le_max_left A₀ A₁) (le_max_right 1 (max A₀ A₁)))
  · have h : |tbR D x| ≤ A₁ := by
      have h' := hA₁ (clampI x) (Set.mem_univ _)
      simpa [tbR, Real.norm_eq_abs] using h'
    exact h.trans (le_trans (le_max_right A₀ A₁) (le_max_right 1 (max A₀ A₁)))

private lemma chord_sub_arc_eq {r : ℝ → Space} {d : BandArcData} (D : SweepData d) (s ξ : ℝ) :
    sweepChord' r D s ξ - sweepArc' r D s ξ
      = (1 - ξ) • (r (taR D s) - r (taR D s + ξ * sweepW' D s))
        + ξ • (r (tbR D s) - r (taR D s + ξ * sweepW' D s)) := by
  simp only [sweepChord', sweepArc', sweepW']
  rw [show taR D s + ξ * (tbR D s - taR D s) = (1 - ξ) * taR D s + ξ * tbR D s by ring]
  module

private lemma chord_sub_arc_norm_le {r : ℝ → Space} {d : BandArcData} (D : SweepData d)
    {M : ℝ} (hM : ∀ x y : ℝ, ‖r x - r y‖ ≤ M * |x - y|)
    {ξ : ℝ} (hξ0 : 0 ≤ ξ) (hξ1 : ξ ≤ 1) (s : ℝ) :
    ‖sweepChord' r D s ξ - sweepArc' r D s ξ‖
      ≤ 2 * M * ξ * (1 - ξ) * |sweepW' D s| := by
  rw [chord_sub_arc_eq]
  have hta : |taR D s - (taR D s + ξ * sweepW' D s)| = ξ * |sweepW' D s| := by
    rw [show taR D s - (taR D s + ξ * sweepW' D s) = -(ξ * sweepW' D s) by ring, abs_neg,
      abs_mul, abs_of_nonneg hξ0]
  have htb : |tbR D s - (taR D s + ξ * sweepW' D s)| = (1 - ξ) * |sweepW' D s| := by
    rw [show tbR D s - (taR D s + ξ * sweepW' D s) = (1 - ξ) * sweepW' D s by
      rw [sweepW']; ring, abs_mul, abs_of_nonneg (by linarith)]
  calc ‖(1 - ξ) • (r (taR D s) - r (taR D s + ξ * sweepW' D s))
        + ξ • (r (tbR D s) - r (taR D s + ξ * sweepW' D s))‖
      ≤ ‖(1 - ξ) • (r (taR D s) - r (taR D s + ξ * sweepW' D s))‖
        + ‖ξ • (r (tbR D s) - r (taR D s + ξ * sweepW' D s))‖ := norm_add_le _ _
    _ = (1 - ξ) * ‖r (taR D s) - r (taR D s + ξ * sweepW' D s)‖
        + ξ * ‖r (tbR D s) - r (taR D s + ξ * sweepW' D s)‖ := by
        rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
          abs_of_nonneg (by linarith), abs_of_nonneg hξ0]
    _ ≤ (1 - ξ) * (M * (ξ * |sweepW' D s|)) + ξ * (M * ((1 - ξ) * |sweepW' D s|)) := by
        refine add_le_add ?_ ?_
        · exact mul_le_mul_of_nonneg_left
            (by simpa only [hta] using hM (taR D s) (taR D s + ξ * sweepW' D s)) (by linarith)
        · exact mul_le_mul_of_nonneg_left
            (by simpa only [htb] using hM (tbR D s) (taR D s + ξ * sweepW' D s)) hξ0
    _ = 2 * M * ξ * (1 - ξ) * |sweepW' D s| := by ring

/-- **The velocity of the chamfered loop is bounded, uniformly in the chamfer `lam ∈ (0,1/4]`.**

`A` bounds the clamped lifts `taR`, `tbR`; `M` is a Lipschitz constant for the curve; `L` bounds
the speed on the range of the arc parameter.  The bound is the crude piecewise estimate of the four
branches of `chamferVel`: the two chamfer branches carry the factor `1/lam` but their numerator is a
chord of length `O(lam * A)`, the chord branch's `1/(1/2 - lam)` is bounded by `4` for
`lam ≤ 1/4`, and the arc branch is bounded by the speed. -/
private lemma chamferVel_norm_le {r : ℝ → Space} {d : BandArcData} (D : SweepData d)
    {A M L : ℝ} (hA0 : 0 ≤ A) (hM0 : 0 ≤ M) (hL0 : 0 ≤ L)
    (hlift : ∀ x : ℝ, |taR D x| ≤ A ∧ |tbR D x| ≤ A)
    (hlip : ∀ x y : ℝ, ‖r x - r y‖ ≤ M * |x - y|)
    (hvel : ∀ x : ℝ, |x| ≤ 5 * A → ‖velocity r x‖ ≤ L)
    {lam : ℝ} (h0 : 0 < lam) (h4 : lam ≤ 1 / 4) (s t : ℝ) :
    ‖chamferVel r D lam s t‖ ≤ 8 * A * (L + M) / period := by
  have hper : 0 < period := period_pos
  have hw : |sweepW' D s| ≤ 2 * A := by
    have h := hlift s
    calc |sweepW' D s| = |tbR D s - taR D s| := by rw [sweepW']
      _ ≤ |tbR D s| + |taR D s| := abs_sub _ _
      _ ≤ A + A := add_le_add h.2 h.1
      _ = 2 * A := by ring
  have hstep1 : 4 * A * L / period ≤ 8 * A * (L + M) / period := by
    refine div_le_div_of_nonneg_right ?_ hper.le
    nlinarith [hA0, hL0, hM0]
  have hstep2 : 8 * A * M / period ≤ 8 * A * (L + M) / period := by
    refine div_le_div_of_nonneg_right ?_ hper.le
    nlinarith [hA0, hL0, hM0]
  have hdel4 : ∀ ξ : ℝ, 0 ≤ ξ → ξ ≤ 1 →
      ‖sweepChord' r D s ξ - sweepArc' r D s ξ‖ ≤ 2 * M * ξ * (1 - ξ) * (2 * A) := by
    intro ξ hξ0 hξ1
    refine (chord_sub_arc_norm_le D hlip hξ0 hξ1 s).trans ?_
    exact mul_le_mul_of_nonneg_left hw
      (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hM0) hξ0) (by linarith))
  have hcoefC : ‖(2 / lam) * (1 / period)‖ = 2 / (lam * period) := by
    rw [Real.norm_eq_abs, abs_of_pos (by positivity)]; ring
  have hdiv : 2 / (lam * period) * (4 * lam * M * A) = 8 * A * M / period := by
    have hl : lam ≠ 0 := ne_of_gt h0
    have hp : period ≠ 0 := ne_of_gt hper
    field_simp
    ring
  rw [chamferVel_eq_ite]
  split_ifs with h1 h2 h3
  · rw [chamferVelArc, norm_smul]
    have harg : ‖velocity r (taR D s + (lam + (1 - 2 * lam) * (2 * sweepParam t)) * sweepW' D s)‖ ≤ L := by
      refine hvel _ ?_
      have hu := sweepParam_mem t
      have hco : |lam + (1 - 2 * lam) * (2 * sweepParam t)| ≤ 2 := by
        rw [abs_le]; constructor <;> nlinarith [h0, h4, hu.1, hu.2.le]
      calc |taR D s + (lam + (1 - 2 * lam) * (2 * sweepParam t)) * sweepW' D s|
          ≤ |taR D s| + |(lam + (1 - 2 * lam) * (2 * sweepParam t)) * sweepW' D s| :=
            abs_add_le _ _
        _ ≤ A + 2 * (2 * A) := by
            refine add_le_add (hlift s).1 ?_
            rw [abs_mul]
            exact mul_le_mul hco hw (abs_nonneg _) (by norm_num)
        _ = 5 * A := by ring
    have hcoef : ‖((1 - 2 * lam) * (2 / period)) * sweepW' D s‖ ≤ 2 * (2 * A) / period := by
      have hle1 : |(1 : ℝ) - 2 * lam| ≤ 1 := by
        rw [abs_le]; constructor <;> linarith
      calc ‖((1 - 2 * lam) * (2 / period)) * sweepW' D s‖
          = |(1 - 2 * lam)| * |2 / period| * |sweepW' D s| := by
            rw [Real.norm_eq_abs, abs_mul, abs_mul]
        _ = |(1 - 2 * lam)| * (2 / period) * |sweepW' D s| := by
            rw [abs_of_pos (by positivity : (0 : ℝ) < 2 / period)]
        _ ≤ 1 * (2 / period) * (2 * A) := by
            refine mul_le_mul (mul_le_mul hle1 le_rfl (by positivity) (by norm_num)) hw
              (abs_nonneg _) (by positivity)
        _ = 2 * (2 * A) / period := by ring
    calc ‖((1 - 2 * lam) * (2 / period)) * sweepW' D s‖
          * ‖velocity r (taR D s + (lam + (1 - 2 * lam) * (2 * sweepParam t)) * sweepW' D s)‖
        ≤ (2 * (2 * A) / period) * L := mul_le_mul hcoef harg (norm_nonneg _) (by positivity)
      _ = 4 * A * L / period := by ring
      _ ≤ 8 * A * (L + M) / period := hstep1
  · rw [chamferVelChamfer₁, norm_smul, hcoefC]
    have hdel : ‖sweepChord' r D s (1 - lam) - sweepArc' r D s (1 - lam)‖ ≤ 4 * lam * M * A := by
      refine (hdel4 (1 - lam) (by linarith) (by linarith)).trans ?_
      rw [show (1 : ℝ) - (1 - lam) = lam by ring]
      have h : 0 ≤ 4 * lam * lam * M * A := by positivity
      nlinarith [h]
    calc 2 / (lam * period) * ‖sweepChord' r D s (1 - lam) - sweepArc' r D s (1 - lam)‖
        ≤ 2 / (lam * period) * (4 * lam * M * A) :=
          mul_le_mul_of_nonneg_left hdel (by positivity)
      _ = 8 * A * M / period := hdiv
      _ ≤ 8 * A * (L + M) / period := hstep2
  · rw [chamferVelChord, norm_smul]
    have hcoef : ‖-((1 - 2 * lam) / ((1 / 2 - lam) * period))‖ ≤ 4 / period := by
      have hd : (0 : ℝ) < (1 / 2 - lam) * period := by
        have : (0 : ℝ) < 1 / 2 - lam := by linarith
        positivity
      have hq : (0 : ℝ) ≤ (1 - 2 * lam) / ((1 / 2 - lam) * period) :=
        div_nonneg (by linarith) hd.le
      rw [norm_neg, Real.norm_eq_abs, abs_of_nonneg hq]
      refine (div_le_div_of_nonneg_right (by linarith : 1 - 2 * lam ≤ 1) hd.le).trans ?_
      refine (one_div_le_one_div_of_le (by positivity : (0 : ℝ) < (1 / 4) * period) ?_).trans ?_
      · nlinarith [h4, hper]
      · exact le_of_eq (by
          rw [div_eq_div_iff (by positivity : ((1:ℝ)/4) * period ≠ 0) (ne_of_gt hper)]
          ring)
    have hdiff : ‖r (tbR D s) - r (taR D s)‖ ≤ M * (2 * A) :=
      (hlip _ _).trans (mul_le_mul_of_nonneg_left hw hM0)
    calc ‖-((1 - 2 * lam) / ((1 / 2 - lam) * period))‖ * ‖r (tbR D s) - r (taR D s)‖
        ≤ (4 / period) * (M * (2 * A)) := mul_le_mul hcoef hdiff (norm_nonneg _) (by positivity)
      _ = 8 * A * M / period := by ring
      _ ≤ 8 * A * (L + M) / period := hstep2
  · rw [chamferVelChamfer₂, norm_smul, hcoefC]
    have hdel : ‖sweepArc' r D s lam - sweepChord' r D s lam‖ ≤ 4 * lam * M * A := by
      rw [norm_sub_rev]
      refine (hdel4 lam h0.le (by linarith)).trans ?_
      have h : 0 ≤ 4 * lam * lam * M * A := by positivity
      nlinarith [h]
    calc 2 / (lam * period) * ‖sweepArc' r D s lam - sweepChord' r D s lam‖
        ≤ 2 / (lam * period) * (4 * lam * M * A) :=
          mul_le_mul_of_nonneg_left hdel (by positivity)
      _ = 8 * A * M / period := hdiv
      _ ≤ 8 * A * (L + M) / period := hstep2

/-- **Joint oscillation of the chamfered loop.**  The two uniform-continuity moduli of the loop
(in the loop parameter and in the sweep parameter, both uniform in `lam ∈ (0,1/4]`) combine into a
single modulus for the *joint* modulus of continuity: the difference of two loop points is at most
the sum of the two moduli. -/
private lemma sweepLoopChamfer_joint_osc {r : ℝ → Space} {d : BandArcData} (D : SweepData d)
    (hloop : LoopProfileModulus' r D) (hsweep : LoopSweepModulus' r D) :
    ∀ η : ℝ, 0 < η → ∃ θ : ℝ, 0 < θ ∧
      ∀ (lam : ℝ), 0 < lam → lam ≤ 1 / 4 → ∀ (σ σ' : ℝ), |σ - σ'| ≤ θ →
        ∀ (t t' : ℝ), |t - t'| ≤ θ →
          ‖sweepLoopChamfer r D lam σ' t' - sweepLoopChamfer r D lam σ t‖ ≤ η := by
  intro η hη
  have ht : LoopTModulus' r D := sweepLoopChamfer_t_modulus' D hloop
  obtain ⟨T, hT0, hT⟩ := ht (η / 2) (by linarith)
  obtain ⟨S, hS0, hS⟩ := hsweep (η / 2) (by linarith)
  refine ⟨min T S, lt_min hT0 hS0, ?_⟩
  intro lam h0 h4 σ σ' hσ t t' ht'
  have h1 : ‖sweepLoopChamfer r D lam σ' t' - sweepLoopChamfer r D lam σ t'‖ ≤ η / 2 := by
    have hmem : sweepParam t' ∈ Set.Icc (0 : ℝ) 1 :=
      ⟨(sweepParam_mem t').1, (sweepParam_mem t').2.le⟩
    have h := hS lam h0 h4 σ σ' (sweepParam t') hmem (hσ.trans (min_le_right _ _))
    simpa only [sweepLoopChamfer_eq_profile r D h0 (by linarith : lam < 1) σ' t',
      sweepLoopChamfer_eq_profile r D h0 (by linarith : lam < 1) σ t'] using h
  have h2 : ‖sweepLoopChamfer r D lam σ t' - sweepLoopChamfer r D lam σ t‖ ≤ η / 2 :=
    hT lam h0 h4 σ t t' (ht'.trans (min_le_left _ _))
  calc ‖sweepLoopChamfer r D lam σ' t' - sweepLoopChamfer r D lam σ t‖
      ≤ ‖sweepLoopChamfer r D lam σ' t' - sweepLoopChamfer r D lam σ t'‖
        + ‖sweepLoopChamfer r D lam σ t' - sweepLoopChamfer r D lam σ t‖ :=
        norm_sub_le_trans' _ _ _
    _ ≤ η / 2 + η / 2 := add_le_add h1 h2
    _ = η := by ring

theorem needleChart_oscBounds {r : ℝ → Space} (hr : IsSmoothKnot r)
    {d : BandArcData} (D : Work.Drive.SweepData d) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε ≤ ε₀ → ∀ κ : ℝ, 0 < κ → ∃ Λ : ℝ, 0 < Λ ∧
      ∀ (lam δ₁ δ₂ : ℝ), 0 < lam → lam ≤ Λ → lam < 1 / 2 → 0 < δ₁ → δ₁ ≤ Λ →
        0 < δ₂ → δ₂ ≤ Λ → δ₂ ≤ ε / 2 →
      ∀ (v : Space), ‖v‖ = 1 →
        Work.Drive.chordEndB r D δ₂ ε - Work.Drive.chordEndA r D δ₂ ε
          = ‖Work.Drive.chordEndB r D δ₂ ε - Work.Drive.chordEndA r D δ₂ ε‖ • v →
        ∃ (A B A' B' : ℝ), 0 ≤ A ∧ 0 ≤ B ∧ 0 ≤ A' ∧ 0 ≤ B' ∧
          2 * (A * B') + 2 * (B * A') < κ ∧
          (∀ t : ℝ, ∀ u : ℝ, u ∈ Set.Icc (-1 : ℝ) 1 → ∀ v₁ : ℝ, v₁ ∈ Set.Icc (-1 : ℝ) 1 →
            ∀ u' : ℝ, u' ∈ Set.Icc (-1 : ℝ) 1 → ∀ v₂ : ℝ, v₂ ∈ Set.Icc (-1 : ℝ) 1 →
            |inner ℝ (Work.Drive.sweepLoopChamfer r D lam (ε - δ₂ * v₁)
                  (t + period / 4 - δ₁ * u) - Work.Drive.chartC r D lam δ₁ δ₂ ε v)
                (Work.Drive.chartE r D lam δ₁ δ₂ ε v)
              - inner ℝ (Work.Drive.sweepLoopChamfer r D lam (ε - δ₂ * v₂)
                  (t + period / 4 - δ₁ * u') - Work.Drive.chartC r D lam δ₁ δ₂ ε v)
                (Work.Drive.chartE r D lam δ₁ δ₂ ε v)| ≤ A) ∧
          (∀ t : ℝ, ∀ u : ℝ, u ∈ Set.Icc (-1 : ℝ) 1 → ∀ v₁ : ℝ, v₁ ∈ Set.Icc (-1 : ℝ) 1 →
            ∀ u' : ℝ, u' ∈ Set.Icc (-1 : ℝ) 1 → ∀ v₂ : ℝ, v₂ ∈ Set.Icc (-1 : ℝ) 1 →
            |inner ℝ (Work.Drive.sweepLoopChamfer r D lam (ε - δ₂ * v₁)
                  (t + period / 4 - δ₁ * u) - Work.Drive.chartC r D lam δ₁ δ₂ ε v) v
              - inner ℝ (Work.Drive.sweepLoopChamfer r D lam (ε - δ₂ * v₂)
                  (t + period / 4 - δ₁ * u') - Work.Drive.chartC r D lam δ₁ δ₂ ε v) v| ≤ B) ∧
          (∀ t : ℝ, ∀ u : ℝ, u ∈ Set.Icc (-1 : ℝ) 1 → ∀ v₁ : ℝ, v₁ ∈ Set.Icc (-1 : ℝ) 1 →
            ∀ u' : ℝ, u' ∈ Set.Icc (-1 : ℝ) 1 → ∀ v₂ : ℝ, v₂ ∈ Set.Icc (-1 : ℝ) 1 →
            |inner ℝ (Work.Drive.chamferVel r D lam (ε - δ₂ * v₁)
                  (t + period / 4 - δ₁ * u))
                (Work.Drive.chartE r D lam δ₁ δ₂ ε v)
              - inner ℝ (Work.Drive.chamferVel r D lam (ε - δ₂ * v₂)
                  (t + period / 4 - δ₁ * u'))
                (Work.Drive.chartE r D lam δ₁ δ₂ ε v)| ≤ A') ∧
          (∀ t : ℝ, ∀ u : ℝ, u ∈ Set.Icc (-1 : ℝ) 1 → ∀ v₁ : ℝ, v₁ ∈ Set.Icc (-1 : ℝ) 1 →
            ∀ u' : ℝ, u' ∈ Set.Icc (-1 : ℝ) 1 → ∀ v₂ : ℝ, v₂ ∈ Set.Icc (-1 : ℝ) 1 →
            |inner ℝ (Work.Drive.chamferVel r D lam (ε - δ₂ * v₁)
                  (t + period / 4 - δ₁ * u)) v
              - inner ℝ (Work.Drive.chamferVel r D lam (ε - δ₂ * v₂)
                  (t + period / 4 - δ₁ * u')) v| ≤ B') := by
  have hcont : Continuous r := hr.smooth.continuous
  have hloop : LoopProfileModulus' r D := sweepLoopProfile_uniformCont_loop D hcont
  have hsweep : LoopSweepModulus' r D := sweepLoopProfile_uniformCont_sweep D hcont
  obtain ⟨A, hA1, hAli⟩ := exists_lift_bound D
  have hA0 : 0 ≤ A := le_trans zero_le_one hA1
  obtain ⟨M, hMpos, hlip⟩ := Work.Drive.exists_knot_lipschitz hr
  have hM0 : 0 ≤ M := hMpos.le
  obtain ⟨L, hL⟩ := IsCompact.exists_bound_of_continuousOn
    (isCompact_Icc (a := -(5 * A)) (b := 5 * A))
    (hr.smooth.continuous_deriv le_top).continuousOn
  have hL0 : 0 ≤ L := le_trans (norm_nonneg (deriv r 0)) (hL 0 ⟨by linarith, by linarith⟩)
  have hvel : ∀ x : ℝ, |x| ≤ 5 * A → ‖velocity r x‖ ≤ L := by
    intro x hx
    exact hL x (by rw [Set.mem_Icc]; exact abs_le.mp hx)
  set C : ℝ := 8 * A * (L + M) / period with hCdef
  have hC0 : 0 ≤ C := by
    rw [hCdef]
    exact div_nonneg (mul_nonneg (mul_nonneg (by norm_num) hA0) (by linarith)) period_pos.le
  refine ⟨1, one_pos, fun ε hε hεle κ hκ => ?_⟩
  set η : ℝ := κ / (8 * (C + 1)) with hηdef
  have hη0 : 0 < η := by rw [hηdef]; positivity
  have hkey : 8 * C * η < κ := by
    have hC1 : (0 : ℝ) < C + 1 := by linarith
    rw [hηdef, show 8 * C * (κ / (8 * (C + 1))) = (C / (C + 1)) * κ by field_simp]
    have hlt : C / (C + 1) < 1 := by
      rw [div_lt_one hC1]; linarith
    simpa using mul_lt_mul_of_pos_right hlt hκ
  obtain ⟨θ, hθ0, hθ⟩ := sweepLoopChamfer_joint_osc D hloop hsweep η hη0
  refine ⟨min (1 / 4) (θ / 2), lt_min (by norm_num) (by linarith), ?_⟩
  intro lam δ₁ δ₂ h0 hΛ hhalf hδ₁ hδ₁Λ hδ₂ hδ₂Λ hδ₂ε v hv hchord
  have h4 : lam ≤ 1 / 4 := le_trans hΛ (min_le_left _ _)
  have hθ₁ : 2 * δ₁ ≤ θ := by
    have h := le_trans hδ₁Λ (min_le_right (1 / 4 : ℝ) (θ / 2)); linarith
  have hθ₂ : 2 * δ₂ ≤ θ := by
    have h := le_trans hδ₂Λ (min_le_right (1 / 4 : ℝ) (θ / 2)); linarith
  have hCv : ∀ σ t : ℝ, ‖chamferVel r D lam σ t‖ ≤ C := fun σ t =>
    chamferVel_norm_le D hA0 hM0 hL0 hAli hlip hvel h0 h4 σ t
  have hprod : 2 * (η * (2 * C)) + 2 * (η * (2 * C)) < κ := by
    have heq : 2 * (η * (2 * C)) + 2 * (η * (2 * C)) = 8 * C * η := by ring
    rw [heq]; exact hkey
  refine ⟨η, η, 2 * C, 2 * C, hη0.le, hη0.le, by linarith, by linarith, hprod, ?_, ?_, ?_, ?_⟩
  · intro t u hu v₁ hv₁ u' hu' v₂ hv₂
    have hσ : |(ε - δ₂ * v₂) - (ε - δ₂ * v₁)| ≤ θ := by
      rw [show ε - δ₂ * v₂ - (ε - δ₂ * v₁) = δ₂ * (v₁ - v₂) by ring, abs_mul,
        abs_of_pos hδ₂]
      have hv' : |v₁ - v₂| ≤ 2 := by
        rw [abs_le]; constructor <;> linarith [hv₁.1, hv₁.2, hv₂.1, hv₂.2]
      nlinarith [hv', hδ₂, hθ₂]
    have hs : |(t + period / 4 - δ₁ * u') - (t + period / 4 - δ₁ * u)| ≤ θ := by
      rw [show t + period / 4 - δ₁ * u' - (t + period / 4 - δ₁ * u) = δ₁ * (u - u') by ring,
        abs_mul, abs_of_pos hδ₁]
      have hu' : |u - u'| ≤ 2 := by
        rw [abs_le]; constructor <;> linarith [hu.1, hu.2, hu'.1, hu'.2]
      nlinarith [hu', hδ₁, hθ₁]
    have hdiff := hθ lam h0 h4 (ε - δ₂ * v₂) (ε - δ₂ * v₁) hσ
      (t + period / 4 - δ₁ * u') (t + period / 4 - δ₁ * u) hs
    have hid : inner ℝ (sweepLoopChamfer r D lam (ε - δ₂ * v₁) (t + period / 4 - δ₁ * u)
            - chartC r D lam δ₁ δ₂ ε v) (chartE r D lam δ₁ δ₂ ε v)
        - inner ℝ (sweepLoopChamfer r D lam (ε - δ₂ * v₂) (t + period / 4 - δ₁ * u')
            - chartC r D lam δ₁ δ₂ ε v) (chartE r D lam δ₁ δ₂ ε v)
        = inner ℝ (sweepLoopChamfer r D lam (ε - δ₂ * v₁) (t + period / 4 - δ₁ * u)
            - sweepLoopChamfer r D lam (ε - δ₂ * v₂) (t + period / 4 - δ₁ * u'))
          (chartE r D lam δ₁ δ₂ ε v) := by
      simp only [inner_sub_left]
      ring
    rw [hid]
    calc |inner ℝ (sweepLoopChamfer r D lam (ε - δ₂ * v₁) (t + period / 4 - δ₁ * u)
            - sweepLoopChamfer r D lam (ε - δ₂ * v₂) (t + period / 4 - δ₁ * u'))
          (chartE r D lam δ₁ δ₂ ε v)|
        ≤ ‖sweepLoopChamfer r D lam (ε - δ₂ * v₁) (t + period / 4 - δ₁ * u)
            - sweepLoopChamfer r D lam (ε - δ₂ * v₂) (t + period / 4 - δ₁ * u')‖
          * ‖chartE r D lam δ₁ δ₂ ε v‖ := by
          simpa only [Real.norm_eq_abs] using
            norm_inner_le_norm (𝕜 := ℝ) (sweepLoopChamfer r D lam (ε - δ₂ * v₁)
                (t + period / 4 - δ₁ * u)
              - sweepLoopChamfer r D lam (ε - δ₂ * v₂) (t + period / 4 - δ₁ * u'))
              (chartE r D lam δ₁ δ₂ ε v)
      _ ≤ η * 1 := mul_le_mul hdiff (chartE_norm_le r D lam δ₁ δ₂ ε v) (norm_nonneg _) hη0.le
      _ = η := by ring
  · intro t u hu v₁ hv₁ u' hu' v₂ hv₂
    have hσ : |(ε - δ₂ * v₂) - (ε - δ₂ * v₁)| ≤ θ := by
      rw [show ε - δ₂ * v₂ - (ε - δ₂ * v₁) = δ₂ * (v₁ - v₂) by ring, abs_mul,
        abs_of_pos hδ₂]
      have hv' : |v₁ - v₂| ≤ 2 := by
        rw [abs_le]; constructor <;> linarith [hv₁.1, hv₁.2, hv₂.1, hv₂.2]
      nlinarith [hv', hδ₂, hθ₂]
    have hs : |(t + period / 4 - δ₁ * u') - (t + period / 4 - δ₁ * u)| ≤ θ := by
      rw [show t + period / 4 - δ₁ * u' - (t + period / 4 - δ₁ * u) = δ₁ * (u - u') by ring,
        abs_mul, abs_of_pos hδ₁]
      have hu' : |u - u'| ≤ 2 := by
        rw [abs_le]; constructor <;> linarith [hu.1, hu.2, hu'.1, hu'.2]
      nlinarith [hu', hδ₁, hθ₁]
    have hdiff := hθ lam h0 h4 (ε - δ₂ * v₂) (ε - δ₂ * v₁) hσ
      (t + period / 4 - δ₁ * u') (t + period / 4 - δ₁ * u) hs
    have hid : inner ℝ (sweepLoopChamfer r D lam (ε - δ₂ * v₁) (t + period / 4 - δ₁ * u)
            - chartC r D lam δ₁ δ₂ ε v) v
        - inner ℝ (sweepLoopChamfer r D lam (ε - δ₂ * v₂) (t + period / 4 - δ₁ * u')
            - chartC r D lam δ₁ δ₂ ε v) v
        = inner ℝ (sweepLoopChamfer r D lam (ε - δ₂ * v₁) (t + period / 4 - δ₁ * u)
            - sweepLoopChamfer r D lam (ε - δ₂ * v₂) (t + period / 4 - δ₁ * u')) v := by
      simp only [inner_sub_left]
      ring
    rw [hid]
    calc |inner ℝ (sweepLoopChamfer r D lam (ε - δ₂ * v₁) (t + period / 4 - δ₁ * u)
            - sweepLoopChamfer r D lam (ε - δ₂ * v₂) (t + period / 4 - δ₁ * u')) v|
        ≤ ‖sweepLoopChamfer r D lam (ε - δ₂ * v₁) (t + period / 4 - δ₁ * u)
            - sweepLoopChamfer r D lam (ε - δ₂ * v₂) (t + period / 4 - δ₁ * u')‖ * ‖v‖ := by
          simpa only [Real.norm_eq_abs] using
            norm_inner_le_norm (𝕜 := ℝ) (sweepLoopChamfer r D lam (ε - δ₂ * v₁)
                (t + period / 4 - δ₁ * u)
              - sweepLoopChamfer r D lam (ε - δ₂ * v₂) (t + period / 4 - δ₁ * u')) v
      _ ≤ η * 1 := mul_le_mul hdiff (le_of_eq hv) (norm_nonneg _) hη0.le
      _ = η := by ring
  · intro t u hu v₁ hv₁ u' hu' v₂ hv₂
    have hV1 := hCv (ε - δ₂ * v₁) (t + period / 4 - δ₁ * u)
    have hV2 := hCv (ε - δ₂ * v₂) (t + period / 4 - δ₁ * u')
    have hid : inner ℝ (chamferVel r D lam (ε - δ₂ * v₁) (t + period / 4 - δ₁ * u))
            (chartE r D lam δ₁ δ₂ ε v)
        - inner ℝ (chamferVel r D lam (ε - δ₂ * v₂) (t + period / 4 - δ₁ * u'))
            (chartE r D lam δ₁ δ₂ ε v)
        = inner ℝ (chamferVel r D lam (ε - δ₂ * v₁) (t + period / 4 - δ₁ * u)
            - chamferVel r D lam (ε - δ₂ * v₂) (t + period / 4 - δ₁ * u'))
          (chartE r D lam δ₁ δ₂ ε v) := by
      rw [inner_sub_left]
    rw [hid]
    calc |inner ℝ (chamferVel r D lam (ε - δ₂ * v₁) (t + period / 4 - δ₁ * u)
            - chamferVel r D lam (ε - δ₂ * v₂) (t + period / 4 - δ₁ * u'))
          (chartE r D lam δ₁ δ₂ ε v)|
        ≤ ‖chamferVel r D lam (ε - δ₂ * v₁) (t + period / 4 - δ₁ * u)
            - chamferVel r D lam (ε - δ₂ * v₂) (t + period / 4 - δ₁ * u')‖
          * ‖chartE r D lam δ₁ δ₂ ε v‖ := by
          simpa only [Real.norm_eq_abs] using
            norm_inner_le_norm (𝕜 := ℝ) (chamferVel r D lam (ε - δ₂ * v₁) (t + period / 4 - δ₁ * u)
              - chamferVel r D lam (ε - δ₂ * v₂) (t + period / 4 - δ₁ * u'))
              (chartE r D lam δ₁ δ₂ ε v)
      _ ≤ (2 * C) * 1 := by
          refine mul_le_mul ?_ (chartE_norm_le r D lam δ₁ δ₂ ε v) (norm_nonneg _) (by linarith)
          calc ‖chamferVel r D lam (ε - δ₂ * v₁) (t + period / 4 - δ₁ * u)
                - chamferVel r D lam (ε - δ₂ * v₂) (t + period / 4 - δ₁ * u')‖
              ≤ ‖chamferVel r D lam (ε - δ₂ * v₁) (t + period / 4 - δ₁ * u)‖
                + ‖chamferVel r D lam (ε - δ₂ * v₂) (t + period / 4 - δ₁ * u')‖ :=
                norm_sub_le _ _
            _ ≤ C + C := add_le_add hV1 hV2
            _ = 2 * C := by ring
      _ = 2 * C := by ring
  · intro t u hu v₁ hv₁ u' hu' v₂ hv₂
    have hV1 := hCv (ε - δ₂ * v₁) (t + period / 4 - δ₁ * u)
    have hV2 := hCv (ε - δ₂ * v₂) (t + period / 4 - δ₁ * u')
    have hid : inner ℝ (chamferVel r D lam (ε - δ₂ * v₁) (t + period / 4 - δ₁ * u)) v
        - inner ℝ (chamferVel r D lam (ε - δ₂ * v₂) (t + period / 4 - δ₁ * u')) v
        = inner ℝ (chamferVel r D lam (ε - δ₂ * v₁) (t + period / 4 - δ₁ * u)
            - chamferVel r D lam (ε - δ₂ * v₂) (t + period / 4 - δ₁ * u')) v := by
      rw [inner_sub_left]
    rw [hid]
    calc |inner ℝ (chamferVel r D lam (ε - δ₂ * v₁) (t + period / 4 - δ₁ * u)
            - chamferVel r D lam (ε - δ₂ * v₂) (t + period / 4 - δ₁ * u')) v|
        ≤ ‖chamferVel r D lam (ε - δ₂ * v₁) (t + period / 4 - δ₁ * u)
            - chamferVel r D lam (ε - δ₂ * v₂) (t + period / 4 - δ₁ * u')‖ * ‖v‖ := by
          simpa only [Real.norm_eq_abs] using
            norm_inner_le_norm (𝕜 := ℝ) (chamferVel r D lam (ε - δ₂ * v₁) (t + period / 4 - δ₁ * u)
              - chamferVel r D lam (ε - δ₂ * v₂) (t + period / 4 - δ₁ * u')) v
      _ ≤ (2 * C) * 1 := mul_le_mul
          (by
            calc ‖chamferVel r D lam (ε - δ₂ * v₁) (t + period / 4 - δ₁ * u)
                  - chamferVel r D lam (ε - δ₂ * v₂) (t + period / 4 - δ₁ * u')‖
                ≤ ‖chamferVel r D lam (ε - δ₂ * v₁) (t + period / 4 - δ₁ * u)‖
                  + ‖chamferVel r D lam (ε - δ₂ * v₂) (t + period / 4 - δ₁ * u')‖ :=
                  norm_sub_le _ _
              _ ≤ C + C := add_le_add hV1 hV2
              _ = 2 * C := by ring)
          (le_of_eq hv) (norm_nonneg _) (by linarith)
      _ = 2 * C := by ring


end Work.Drive.Generic
