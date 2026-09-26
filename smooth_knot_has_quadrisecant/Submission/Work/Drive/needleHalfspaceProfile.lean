import Mathlib
import Submission.Work.Drive.needleFam_inner_eq_devAvg
import Submission.Work.Drive.needleDevDefs
import Submission.Work.Drive.sweepBlurFacts
import Submission.Work.Drive.chordSweepSmooth
import Submission.Work.Drive.chordSweepDefs
import Submission.Work.Drive.arcZoneWindow
import Submission.Work.Drive.needleArcZoneMono

/-!
# The needle's profile: the half-space route

This module isolates the *provable* half of the needle's one-sidedness (the crux
`Work.Drive.needleArcHeightPos` behind `needleStarShapedData.lean`).

The needle `N = needleFam r D lam δ₁ δ₂ ε` is, in the arc zone of the loop parameter, the double
average of the *loops'* deviations `loopDev (ε - δ₂ v) (arcFrac lam δ₁ t u)` from their own chords
(`Work.Drive.needleFam_inner_eq_devAvg`).  Consequently a direction `e` which is orthogonal to the
needle's chord and *positive on every loop's deviation*

    `∀ v u ∈ [-1,1], 0 < ⟪loopDev (ε - δ₂ v) (arcFrac lam δ₁ t u), e⟫`

makes the needle's own profile positive (`needleFam_inner_pos_of_pointwise`).

The Green representation of the deviation (`Work.Drive.dev_green`) gives such a direction from a
*definite sign of the second derivative*: if a unit `e` has `⟪e, r''(x)⟫ ≤ 0` along the whole
retained arc, with strict negativity somewhere, then `0 < ⟪e, loopDev σ ξ⟫` for every interior
fraction (`loopDev_pos_of_halfspace`).  Such an `e` exists whenever the collapsed end `ρ = ta 0` is
*not an inflection* of the knot (`exists_secondDeriv_halfspace`).

The remaining case — `r''(ρ) ∥ r'(ρ)`, i.e. `ρ` an inflection of the trace — is *not* covered by a
half-space condition: in that case `Π_û r''(a_σ) = O(s²)` and the leading term of the profile is the
*second-order* bracket `s_σ/2 + (1+ξ)W_σ/6`, whose sign is governed by the relative size of the
`a`-branch displacement `s_σ` and the arc width `W_σ`.  That case has to use `havoid` at the level of
the second-order bracket; see `NOTES_needleStarShaped_data.md`.
-/

noncomputable section
namespace Work.Drive

set_option maxHeartbeats 1600000

open LeanEval.KnotTheory.Quadrisecant MeasureTheory
open scoped Real Topology intervalIntegral

/-- The loop's deviation `loopDev` is the deviation `dev` of `needleDevDefs`. -/
lemma loopDev_eq_dev (r : ℝ → Space) {d : BandArcData} (D : SweepData d) (σ ξ : ℝ) :
    loopDev r D σ ξ = dev r D σ ξ := rfl

/-- **The loop's deviation is one-sided against a definite acceleration.**
If a unit `e` has `⟪e, r''⟫ ≤ 0` along the whole retained arc at parameter `σ`, and `< 0`
somewhere in the interior, then the deviation of the retained arc from its chord has positive
`e`-component at every interior fraction. -/
theorem loopDev_pos_of_halfspace {r : ℝ → Space} (hr : IsSmoothKnot r) {d : BandArcData}
    (D : SweepData d) {σ : ℝ} {e : Space} (hW : 0 < sweepW' D σ)
    (hle : ∀ u ∈ Set.Icc (0:ℝ) 1,
      inner ℝ e (deriv (velocity r) (taR D σ + u * sweepW' D σ)) ≤ 0)
    (hlt : ∃ u ∈ Set.Ioo (0:ℝ) 1,
      inner ℝ e (deriv (velocity r) (taR D σ + u * sweepW' D σ)) < 0)
    {ξ : ℝ} (hξ : ξ ∈ Set.Ioo (0:ℝ) 1) :
    0 < inner ℝ e (loopDev r D σ ξ) := by
  rw [loopDev_eq_dev]
  exact needleDev_inner_pos hr D hW hle hlt hξ

/-! ## Needle level: the double average -/

/-- The integral of a bump-weighted strictly positive continuous function on `[-1,1]` is positive. -/
lemma devAvg_pos {f : ℝ → ℝ} (hcont : ContinuousOn f (Set.Icc (-1:ℝ) 1))
    (hpos : ∀ u ∈ Set.Icc (-1:ℝ) 1, 0 < f u) :
    0 < ∫ u in (-1:ℝ)..1, sweepBump u * f u := by
  refine intervalIntegral.integral_pos (by norm_num)
    (sweepBump_continuous.continuousOn.mul hcont) (fun u hu => ?_) ⟨0, by norm_num, ?_⟩
  · exact mul_nonneg (sweepBump_nonneg u) (hpos u ⟨hu.1.le, hu.2⟩).le
  · exact mul_pos (sweepBump_pos (by norm_num) (by norm_num)) (hpos 0 (by norm_num))

/-- **The needle's profile is positive from a pointwise-positive loop deviation.**
If for every `(v,u) ∈ [-1,1]²` the deviation of the loop at `ε - δ₂ v` has positive `e`-component at
the fraction `arcFrac lam δ₁ t u`, and `e` is orthogonal to the needle's chord
`chordEndB - chordEndA`, then the needle's deviation from its chord at parameter `t` has positive
`e`-component. -/
theorem needleFam_inner_pos_of_pointwise {r : ℝ → Space} (hr : Continuous r) {d : BandArcData}
    (D : SweepData d) {lam δ₁ δ₂ ε t : ℝ} (hlam1 : lam < 1 / 2) (hδ₁ : 0 < δ₁)
    (hδ : δ₁ < period / 2)
    (hzone : ∀ u : ℝ, u ∈ Set.Icc (-1:ℝ) 1 → sweepParam (t - δ₁ * u) ≤ 1 / 2)
    {e : Space}
    (hpos : ∀ v : ℝ, v ∈ Set.Icc (-1:ℝ) 1 → ∀ u : ℝ, u ∈ Set.Icc (-1:ℝ) 1 →
      0 < inner ℝ (loopDev r D (ε - δ₂ * v) (arcFrac lam δ₁ t u)) e)
    (horth : inner ℝ (chordEndB r D δ₂ ε - chordEndA r D δ₂ ε) e = 0) :
    0 < inner ℝ (needleFam r D lam δ₁ δ₂ ε t - chordEndA r D δ₂ ε) e := by
  -- the affine proxy for the arc fraction (continuous, and equal to `arcFrac` on `[-1,1]`)
  set ξ : ℝ → ℝ := fun u => lam + (1 - 2 * lam) * (2 * (sweepParam t - δ₁ * u / period)) with hξ
  have hξcont : Continuous ξ := by rw [hξ]; fun_prop
  have hξeq : ∀ u ∈ Set.Icc (-1:ℝ) 1, arcFrac lam δ₁ t u = ξ u :=
    fun u hu => arcFrac_eq_affine hδ₁ hδ hu hzone
  -- the parametric inner integrand
  set F : ℝ → ℝ → ℝ := fun v u => sweepBump u *
      inner ℝ (loopDev r D (ε - δ₂ * v) (ξ u)) e with hFdef
  have hFcont : Continuous (Function.uncurry F) := by
    rw [hFdef]
    have h1 : Continuous (fun p : ℝ × ℝ => taR D (ε - δ₂ * p.1)) :=
      (arcWin_taR_continuous D).comp (by fun_prop)
    have h2 : Continuous (fun p : ℝ × ℝ => tbR D (ε - δ₂ * p.1)) :=
      (arcWin_tbR_continuous D).comp (by fun_prop)
    have h3 : Continuous (fun p : ℝ × ℝ => sweepW' D (ε - δ₂ * p.1)) :=
      (arcWin_sweepW'_continuous D).comp (by fun_prop)
    have h4 : Continuous (fun p : ℝ × ℝ =>
        r (taR D (ε - δ₂ * p.1) + ξ p.2 * sweepW' D (ε - δ₂ * p.1))) :=
      hr.comp (h1.add ((hξcont.comp continuous_snd).mul h3))
    have h5 : Continuous (fun p : ℝ × ℝ =>
        (1 - ξ p.2) • r (taR D (ε - δ₂ * p.1)) + (ξ p.2) • r (tbR D (ε - δ₂ * p.1))) :=
      (((continuous_const.sub (hξcont.comp continuous_snd)).smul (hr.comp h1)).add
        ((hξcont.comp continuous_snd).smul (hr.comp h2)))
    have h6 : Continuous (fun p : ℝ × ℝ =>
        inner ℝ (loopDev r D (ε - δ₂ * p.1) (ξ p.2)) e) := by
      rw [show (fun p : ℝ × ℝ => inner ℝ (loopDev r D (ε - δ₂ * p.1) (ξ p.2)) e)
        = (fun p : ℝ × ℝ => inner ℝ
          (r (taR D (ε - δ₂ * p.1) + ξ p.2 * sweepW' D (ε - δ₂ * p.1)) -
            ((1 - ξ p.2) • r (taR D (ε - δ₂ * p.1)) + (ξ p.2) • r (tbR D (ε - δ₂ * p.1)))) e)
        from rfl]
      exact (h4.sub h5).inner continuous_const
    exact (sweepBump_continuous.comp continuous_snd).mul h6
  have hFval : ∀ v : ℝ, (∫ u in (-1:ℝ)..1, sweepBump u *
        inner ℝ (loopDev r D (ε - δ₂ * v) (arcFrac lam δ₁ t u)) e)
      = ∫ u in (-1:ℝ)..1, F v u := by
    intro v
    refine intervalIntegral.integral_congr (fun u hu => ?_)
    rw [Set.uIcc_of_le (by norm_num : (-1:ℝ) ≤ 1)] at hu
    rw [hFdef, hξeq u hu]
  have hinner : ∀ v ∈ Set.Icc (-1:ℝ) 1, 0 < ∫ u in (-1:ℝ)..1, F v u := by
    intro v hv
    have hcontv : ContinuousOn
        (fun u : ℝ => inner ℝ (loopDev r D (ε - δ₂ * v) (ξ u)) e) (Set.Icc (-1:ℝ) 1) := by
      have h1 : Continuous (fun u : ℝ => taR D (ε - δ₂ * v)) := continuous_const
      have h2 : Continuous (fun u : ℝ => tbR D (ε - δ₂ * v)) := continuous_const
      have h3 : Continuous (fun u : ℝ => sweepW' D (ε - δ₂ * v)) := continuous_const
      have h4 : Continuous (fun u : ℝ =>
          r (taR D (ε - δ₂ * v) + ξ u * sweepW' D (ε - δ₂ * v))) :=
        hr.comp (h1.add (hξcont.mul h3))
      have h5 : Continuous (fun u : ℝ =>
          (1 - ξ u) • r (taR D (ε - δ₂ * v)) + (ξ u) • r (tbR D (ε - δ₂ * v))) :=
        ((continuous_const.sub hξcont).smul (hr.comp h1)).add (hξcont.smul (hr.comp h2))
      rw [show (fun u : ℝ => inner ℝ (loopDev r D (ε - δ₂ * v) (ξ u)) e)
        = (fun u : ℝ => inner ℝ
          (r (taR D (ε - δ₂ * v) + ξ u * sweepW' D (ε - δ₂ * v)) -
            ((1 - ξ u) • r (taR D (ε - δ₂ * v)) + (ξ u) • r (tbR D (ε - δ₂ * v)))) e)
        from rfl]
      exact ((h4.sub h5).inner continuous_const).continuousOn
    have hgoal : 0 < ∫ u in (-1:ℝ)..1, sweepBump u *
        inner ℝ (loopDev r D (ε - δ₂ * v) (ξ u)) e := by
      refine devAvg_pos hcontv (fun u hu => ?_)
      simpa only [hξeq u hu] using hpos v hv u hu
    simpa only [hFdef] using hgoal
  rw [needleFam_inner_eq_devAvg hr D hlam1 hzone, horth, mul_zero, add_zero]
  simp only [hFval]
  have hcont2 : ContinuousOn (fun v : ℝ => ∫ u in (-1:ℝ)..1, F v u) (Set.Icc (-1:ℝ) 1) :=
    ((intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' hFcont _ _)).continuousOn
  have hgoal2 : 0 < ∫ v in (-1:ℝ)..1, sweepBump v *
      ((fun v : ℝ => ∫ u in (-1:ℝ)..1, F v u) v) :=
    devAvg_pos hcont2 hinner
  simpa only using hgoal2

/-! ## Existence of the half-space direction at a non-inflection -/

/-- **A definite second-derivative half-space at a non-inflection.**
If the collapsed end `ρ` is *not an inflection* of the knot — that is, there is a unit `e₀`
orthogonal to `r'(ρ)` with `⟪e₀, r''(ρ)⟫ > 0` — then there is `δ > 0` such that for every unit `û`
within `δ` of the unit tangent at `ρ`, and every pair `α ≤ β` inside `[ρ-δ, ρ+δ]`, there is a unit
`e` with `⟪e, û⟫ = 0` and `⟪e, r''(x)⟫ < 0` all along `[α,β]`. -/
theorem exists_secondDeriv_halfspace {r : ℝ → Space} (hr : IsSmoothKnot r) {ρ : ℝ}
    (hT : deriv r ρ ≠ 0)
    (hne : ∃ e₀ : Space, ‖e₀‖ = 1 ∧ inner ℝ e₀ (deriv r ρ) = 0 ∧
      0 < inner ℝ e₀ (deriv (deriv r) ρ)) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ û : Space, ‖û‖ = 1 → ‖û - (‖deriv r ρ‖⁻¹ • deriv r ρ)‖ ≤ δ →
      ∀ α β : ℝ, |α - ρ| ≤ δ → |β - ρ| ≤ δ →
        ∃ e : Space, ‖e‖ = 1 ∧ inner ℝ e û = 0 ∧
          ∀ x : ℝ, α ≤ x → x ≤ β → inner ℝ e (deriv (deriv r) x) < 0 := by
  obtain ⟨e₀, he₀n, he₀orth, he₀pos⟩ := hne
  set c0 : ℝ := inner ℝ e₀ (deriv (deriv r) ρ) with hc0def
  have hc0pos : 0 < c0 := he₀pos
  set z : Space := deriv (deriv r) ρ with hzdef
  set T : Space := ‖deriv r ρ‖⁻¹ • deriv r ρ with hTdef
  have hTe₀ : inner ℝ e₀ T = 0 := by
    rw [hTdef, inner_smul_right, he₀orth, mul_zero]
  have hTnorm : ‖T‖ = 1 := by rw [hTdef]; exact norm_smul_inv_norm hT
  -- continuity of the acceleration at `ρ`
  have hcont : Continuous (deriv (deriv r)) := by
    have h2 : iteratedDeriv 2 r = deriv (deriv r) := by
      rw [show (2:ℕ) = 1 + 1 from rfl, iteratedDeriv_succ', iteratedDeriv_one]
    rw [← h2]
    exact hr.smooth.continuous_iteratedDeriv 2 le_top
  obtain ⟨δ₁, hδ₁pos, hδ₁⟩ := Metric.continuousAt_iff.mp
    (show ContinuousAt (deriv (deriv r)) ρ from hcont.continuousAt) (c0 / 8)
    (by linarith [hc0pos])
  set K : ℝ := ‖z‖ + 1 with hKdef
  have hKpos : 0 < K := by rw [hKdef]; positivity
  have hKge : ‖z‖ ≤ K := by rw [hKdef]; linarith
  have hδ₂pos : 0 < c0 / (8 * K) := by positivity
  refine ⟨min (δ₁ / 2) (min (c0 / (8 * K)) 1),
    lt_min (by linarith) (lt_min hδ₂pos one_pos), ?_⟩
  intro û hûn hûclose α β hα hβ
  have hδle₁ : min (δ₁ / 2) (min (c0 / (8 * K)) 1) < δ₁ :=
    lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hδle₂ : min (δ₁ / 2) (min (c0 / (8 * K)) 1) ≤ c0 / (8 * K) :=
    le_trans (min_le_right _ _) (min_le_left _ _)
  set v : Space := z - inner ℝ z û • û with hvdef
  set w : Space := z - inner ℝ z T • T with hwdef
  -- `w` has length at least `c0`
  have hwge : c0 ≤ ‖w‖ := by
    have heq : c0 = inner ℝ e₀ w := by
      rw [hc0def, hzdef, hwdef, inner_sub_right, inner_smul_right, hTe₀, mul_zero, sub_zero]
    rw [heq]
    calc inner ℝ e₀ w ≤ ‖e₀‖ * ‖w‖ := real_inner_le_norm _ _
      _ = ‖w‖ := by rw [he₀n, one_mul]
  -- `v - w` is small
  have hvwh : v - w = inner ℝ z T • (T - û) + inner ℝ z (T - û) • û := by
    rw [hvdef, hwdef, inner_sub_right]
    module
  have hb1 : ‖inner ℝ z T • (T - û)‖ ≤ ‖z‖ * ‖T - û‖ := by
    rw [norm_smul, Real.norm_eq_abs]
    refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
    calc |inner ℝ z T| ≤ ‖z‖ * ‖T‖ := abs_real_inner_le_norm _ _
      _ = ‖z‖ := by rw [hTnorm, mul_one]
  have hb2 : ‖inner ℝ z (T - û) • û‖ ≤ ‖z‖ * ‖T - û‖ := by
    rw [norm_smul, Real.norm_eq_abs, hûn, mul_one]
    exact abs_real_inner_le_norm _ _
  have hvwd : ‖v - w‖ ≤ 2 * ‖z‖ * ‖T - û‖ := by
    rw [hvwh]
    calc ‖inner ℝ z T • (T - û) + inner ℝ z (T - û) • û‖
        ≤ ‖inner ℝ z T • (T - û)‖ + ‖inner ℝ z (T - û) • û‖ := norm_add_le _ _
      _ ≤ ‖z‖ * ‖T - û‖ + ‖z‖ * ‖T - û‖ := add_le_add hb1 hb2
      _ = 2 * ‖z‖ * ‖T - û‖ := by ring
  have hclose : ‖T - û‖ ≤ c0 / (8 * K) := by
    have h1 : ‖T - û‖ = ‖û - T‖ := norm_sub_rev _ _
    rw [h1, hTdef]
    exact le_trans hûclose hδle₂
  have hvwd' : ‖v - w‖ ≤ 2 * ‖z‖ * (c0 / (8 * K)) :=
    le_trans hvwd (mul_le_mul_of_nonneg_left hclose (by positivity))
  have hzK : ‖z‖ * (c0 / (8 * K)) ≤ K * (c0 / (8 * K)) :=
    mul_le_mul_of_nonneg_right hKge (by positivity)
  have hfinal : 2 * (K * (c0 / (8 * K))) = c0 / 4 := by
    field_simp
    ring
  have hvwle : ‖v - w‖ ≤ c0 / 4 := by
    nlinarith [hvwd', hzK, hKpos, hc0pos]
  have hvge : c0 / 2 ≤ ‖v‖ := by
    have h3 : ‖w‖ ≤ ‖v‖ + ‖v - w‖ := by
      have h := norm_sub_le v (v - w)
      have h4 : v - (v - w) = w := by abel
      rwa [h4] at h
    linarith [h3, hwge, hvwle, hc0pos]
  have hvne : v ≠ 0 := by
    intro hv0
    have h0 : ‖v‖ = 0 := by rw [hv0]; simp
    linarith [hvge, hc0pos, h0]
  refine ⟨-(‖v‖⁻¹) • v, ?_, ?_, ?_⟩
  · rw [norm_smul, Real.norm_eq_abs, abs_neg, abs_inv, abs_of_nonneg (norm_nonneg v)]
    exact inv_mul_cancel₀ (norm_ne_zero_iff.mpr hvne)
  · have hvû : inner ℝ v û = 0 := by
      rw [hvdef, inner_sub_left, inner_smul_left, RCLike.conj_to_real,
        real_inner_self_eq_norm_sq, hûn]
      ring
    rw [inner_smul_left, RCLike.conj_to_real, hvû, mul_zero]
  · intro x hxα hxβ
    have hxρ : |x - ρ| ≤ min (δ₁ / 2) (min (c0 / (8 * K)) 1) := by
      rcases le_total ρ x with h | h
      · rw [abs_of_nonneg (by linarith)]
        have h1 : x - ρ ≤ β - ρ := by linarith
        have h2 : β - ρ ≤ |β - ρ| := le_abs_self _
        linarith [h1, h2, hβ]
      · rw [abs_of_nonpos (by linarith)]
        have h1 : ρ - x ≤ ρ - α := by linarith
        have h2 : ρ - α ≤ |ρ - α| := le_abs_self _
        have h3 : |ρ - α| = |α - ρ| := abs_sub_comm _ _
        linarith [h1, h2, h3, hα]
    have hxδ₁ : dist x ρ < δ₁ := by
      rw [Real.dist_eq]
      linarith [hxρ, hδle₁]
    have hd : ‖deriv (deriv r) x - deriv (deriv r) ρ‖ ≤ c0 / 8 := by
      have h := hδ₁ hxδ₁
      rw [dist_eq_norm] at h
      linarith [h]
    set d : Space := deriv (deriv r) x - deriv (deriv r) ρ with hddef
    have hdv : ‖d‖ ≤ c0 / 8 := by rw [hddef]; exact hd
    have hvu : inner ℝ v û = 0 := by
      rw [hvdef, inner_sub_left, inner_smul_left, RCLike.conj_to_real,
        real_inner_self_eq_norm_sq, hûn]
      ring
    have hvρ : inner ℝ v (deriv (deriv r) ρ) = ‖v‖ * ‖v‖ := by
      have hzv : deriv (deriv r) ρ = v + inner ℝ z û • û := by rw [hvdef, hzdef]; abel
      rw [hzv, inner_add_right, inner_smul_right, hvu, mul_zero, add_zero,
        real_inner_self_eq_norm_sq, pow_two]
    have hxsplit : deriv (deriv r) x = deriv (deriv r) ρ + d := by rw [hddef]; abel
    have hsplit : inner ℝ v (deriv (deriv r) x)
        = inner ℝ v (deriv (deriv r) ρ) + inner ℝ v d := by
      rw [hxsplit, inner_add_right]
    have hb := (abs_le.mp (abs_real_inner_le_norm v d)).1
    have hkey : ‖v‖ * ‖v‖ - ‖v‖ * ‖d‖ ≤ inner ℝ v (deriv (deriv r) x) := by
      rw [hsplit, hvρ]
      linarith [hb]
    have hpos : 0 < inner ℝ v (deriv (deriv r) x) := by
      have hv1 : c0 / 2 ≤ ‖v‖ := hvge
      have hnn : 0 ≤ ‖v‖ := norm_nonneg v
      have hm : ‖v‖ * ‖d‖ ≤ ‖v‖ * (c0 / 8) := mul_le_mul_of_nonneg_left hdv hnn
      have hstep : ‖v‖ * (c0 / 8) ≤ ‖v‖ * ‖v‖ / 2 := by nlinarith [hv1, hnn, hc0pos]
      have hvv : 0 < ‖v‖ * ‖v‖ := by nlinarith [hv1, hc0pos]
      nlinarith [hkey, hm, hstep, hvv]
    rw [inner_smul_left, RCLike.conj_to_real]
    have hc : 0 < (‖v‖)⁻¹ * inner ℝ v (deriv (deriv r) x) :=
      mul_pos (inv_pos.mpr (norm_pos_iff.mpr hvne)) hpos
    ring_nf
    linarith [hc]

end Work.Drive
