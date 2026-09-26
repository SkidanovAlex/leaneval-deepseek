import Mathlib
import Submission.Work.Drive.Generic.nclmPkg
import Submission.Work.Drive.Generic.nclmBasic
import Submission.Work.Drive.Generic.nclmDev
import Submission.Work.Drive.Generic.nclmWindow
import Submission.Work.Drive.H2.chartE_accel_neg
import Submission.Work.Drive.H2.chartUp_norm_bound
import Submission.Work.Drive.H2.baseHeight_lower
import Submission.Work.Drive.AB.chordEndNormLower
import Submission.Work.Drive.AB.windowDataSmall

/-!
# The chamfer package of the needle's chart data

`Work.Drive.Generic.nclmPkgChamfer` is one of the four packages into which the chart data
`Work.Drive.Generic.nclmDataC` is split (see `nclmPkg.lean`).  It consists of

* the **acceleration clause**: the chart "up" direction `chartE` is *negative* along the acceleration
  of every retained arc of the window (`⟪r'' x, chartE⟫ ≤ -cE`);
* the two **deviation clauses**: the deviation `loopDev σ ξ` of the arc from its chord, against
  `chartE`, is at least `λ(1-λ)/2 · w(σ)² · cE` at the two chamfer fractions `ξ = λ`, `1 - λ`, while
  its `v`-component is bounded by `λ(1-λ)/2 · w(σ)² · cK`;
* the **bookkeeping**: `2 ‖chartUp‖ cK ≤ ℓ cE / 8`, where `ℓ` is the chord length.

All three are immediate from the estimates already in the library:

* the acceleration clause is `Work.Drive.H2.chartE_accel_neg`;
* the signed deviation clause is `Work.Drive.Generic.nclm_dev_scalar_ge` (with `y = chartE` and the
  lower bound `c = cE` on `⟪r'' , chartE⟫` supplied by the acceleration clause), and the absolute
  one is `Work.Drive.Generic.nclm_dev_scalar_le` (with `y = v` and `B = K`, a global bound on the
  acceleration);
* the bookkeeping combines the *upper* bound `‖chartUp‖ ≤ w(ε)² K`
  (`Work.Drive.H2.chartUp_norm_bound`) with the *lower* bound `cC · w(ε)/2 ≤ ℓ`
  (`Work.Drive.chordEndNormLower`, together with the window comparison `w(σ) ≥ w(ε)/2` of
  `Work.Drive.Generic.nclm_window_eps`): both scale as a power of the width `w(ε) = sweepW' D ε`,
  so a single smallness threshold `ε₀` on the width makes `2 ‖chartUp‖ K ≤ ℓ cE/8` true.  The
  vanishing of the width at the collapsed end is the helper `sweepW'_le_of_small` below.
-/

namespace Work.Drive.Generic

open LeanEval.KnotTheory.Quadrisecant MeasureTheory
open scoped Real Topology intervalIntegral

variable {r : ℝ → Space} {d : BandArcData}

/-- **The width of the band arc collapses at the left end.**  For every `S > 0` there is
`ε₀ > 0` with `sweepW' D ε ≤ S` for every `ε ∈ (0, ε₀]`.  This is the continuity of `sweepW'` at
`0` together with `sweepW' D 0 = 0` (the two lifts agree at the collapsed end). -/
lemma sweepW'_le_of_small {d : BandArcData} (D : Work.Drive.SweepData d) {S : ℝ}
    (hS : 0 < S) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε ≤ ε₀ → Work.Drive.sweepW' D ε ≤ S := by
  have hcont : ContinuousAt (fun x : ℝ => Work.Drive.sweepW' D x) 0 :=
    (Work.Drive.continuous_sweepW' D).continuousAt
  have hzero : Work.Drive.sweepW' D 0 = 0 := by
    rw [Work.Drive.sweepW', Work.Drive.tbR_zero_eq_taR_zero D, sub_self]
  obtain ⟨δ, hδ0, hδ⟩ := Metric.continuousAt_iff.mp hcont S hS
  refine ⟨δ / 2, by positivity, ?_⟩
  intro ε hε0 hεδ
  have hdist : dist ε (0 : ℝ) < δ := by
    rw [Real.dist_eq, sub_zero, abs_of_pos hε0]
    linarith
  have h := hδ hdist
  rw [hzero, Real.dist_eq, sub_zero] at h
  exact le_of_lt (lt_of_abs_lt h)

theorem nclm_clauseChamfer {r : ℝ → LeanEval.KnotTheory.Quadrisecant.Space}
    (hr : LeanEval.KnotTheory.Quadrisecant.IsSmoothKnot r)
    (hinfl : ∀ t : ℝ, LinearIndependent ℝ ![deriv r t, deriv (deriv r) t])
    {d : LeanEval.KnotTheory.Quadrisecant.BandArcData} (D : Work.Drive.SweepData d) :
    Work.Drive.Generic.nclmPkgChamfer r D := by
  -- the acceleration clause, with its ε-threshold and its constant
  obtain ⟨cE, hcE0, εA, hεA0, _hεA12, Hacc⟩ := Work.Drive.H2.chartE_accel_neg hr hinfl D
  -- a global bound for the acceleration
  obtain ⟨K, hK1, hKb⟩ := Work.Drive.H2.H2_accel_bound hr
  have hK0 : (0 : ℝ) < K := lt_of_lt_of_le zero_lt_one hK1
  -- a lower bound for the length of the blurred chord
  obtain ⟨εC, cC, hεC0, hcC0, Hchord⟩ := Work.Drive.chordEndNormLower hr D
  -- smallness of the width
  obtain ⟨εS, hεS0, hεS⟩ :=
    sweepW'_le_of_small (d := d) D (S := cC * cE / (64 * K ^ 2)) (by positivity)
  refine ⟨min (min (min εA εC) εS) (1 / 2),
    lt_min (lt_min (lt_min hεA0 hεC0) hεS0) (by norm_num), ?_⟩
  intro ε hε0 hεε₀
  have hεA : ε ≤ εA :=
    le_trans hεε₀ (le_trans (min_le_left _ _)
      (le_trans (min_le_left _ _) (min_le_left _ _)))
  have hεC : ε ≤ εC :=
    le_trans hεε₀ (le_trans (min_le_left _ _)
      (le_trans (min_le_left _ _) (min_le_right _ _)))
  have hεS' : ε ≤ εS := le_trans hεε₀ (le_trans (min_le_left _ _) (min_le_right _ _))
  have hε12 : ε ≤ 1 / 2 := le_trans hεε₀ (min_le_right _ _)
  have hε1 : ε < 1 := by linarith
  have hWpos : 0 < Work.Drive.sweepW' D ε := Work.Drive.wds_sweepW'_pos D hε0 hε1
  obtain ⟨Λw, hΛw0, hΛw⟩ := nclm_window_eps D hε0 hε1
  obtain ⟨Λa, hΛa0, _hΛa14, hAcc⟩ := Hacc ε hε0 hεA
  have hper : (0 : ℝ) < period := period_pos
  refine ⟨cE, K, min (min Λw Λa) (min (period / 16) (1 / 4)), hcE0, hK0.le,
    lt_min (lt_min hΛw0 hΛa0) (lt_min (by linarith) (by norm_num)), ?_⟩
  intro lam δ₁ δ₂ hlam0 hlamΛ hlam2 hδ₁0 hδ₁Λ hδ₂0 hδ₂Λ hδ₂ε v hv hcv
  -- unpack the threshold
  have hWlam : lam ≤ Λw := le_trans hlamΛ (le_trans (min_le_left _ _) (min_le_left _ _))
  have hAlam : lam ≤ Λa := le_trans hlamΛ (le_trans (min_le_left _ _) (min_le_right _ _))
  have hWδ₁ : δ₁ ≤ Λw := le_trans hδ₁Λ (le_trans (min_le_left _ _) (min_le_left _ _))
  have hAδ₁ : δ₁ ≤ Λa := le_trans hδ₁Λ (le_trans (min_le_left _ _) (min_le_right _ _))
  have hWδ₂ : δ₂ ≤ Λw := le_trans hδ₂Λ (le_trans (min_le_left _ _) (min_le_left _ _))
  have hAδ₂ : δ₂ ≤ Λa := le_trans hδ₂Λ (le_trans (min_le_left _ _) (min_le_right _ _))
  have h16δ₁ : δ₁ ≤ period / 16 :=
    le_trans hδ₁Λ (le_trans (min_le_right _ _) (min_le_left _ _))
  have hδ₁4 : δ₁ ≤ period / 4 := by linarith
  -- the window comparisons of the width
  have hWlow : ∀ σ : ℝ, ε - δ₂ ≤ σ → σ ≤ ε + δ₂ →
      Work.Drive.sweepW' D ε / 2 ≤ Work.Drive.sweepW' D σ :=
    fun σ h1 h2 => (hΛw δ₂ σ hδ₂0 hWδ₂ hδ₂ε h1 h2).1
  have hWup : ∀ σ : ℝ, ε - δ₂ ≤ σ → σ ≤ ε + δ₂ →
      Work.Drive.sweepW' D σ ≤ 2 * Work.Drive.sweepW' D ε :=
    fun σ h1 h2 => (hΛw δ₂ σ hδ₂0 hWδ₂ hδ₂ε h1 h2).2.1
  have hmem : ∀ u ∈ Set.Icc (-1 : ℝ) 1,
      ε - δ₂ ≤ ε - δ₂ * u ∧ ε - δ₂ * u ≤ ε + δ₂ := by
    intro u hu
    constructor <;> nlinarith [hu.1, hu.2, hδ₂0]
  -- `iteratedDeriv 2 r = deriv (deriv r)`
  have hiter : iteratedDeriv 2 r = deriv (deriv r) := by
    rw [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ', iteratedDeriv_one]
  -- the acceleration clause
  have haccC : ∀ σ : ℝ, ε - δ₂ ≤ σ → σ ≤ ε + δ₂ →
      ∀ x ∈ Set.Icc (Work.Drive.taR D σ) (Work.Drive.tbR D σ),
        inner ℝ (deriv (deriv r) x) (Work.Drive.chartE r D lam δ₁ δ₂ ε v) ≤ -cE := by
    intro σ h1 h2 x hx
    have h := hAcc lam δ₁ δ₂ hlam0 hAlam hδ₁0 hAδ₁ hδ₂0 hAδ₂ hδ₂ε v hv hcv σ h1 h2
      x hx.1 hx.2
    rwa [hiter] at h
  -- the deviation clauses
  have hdevC : ∀ σ : ℝ, ε - δ₂ ≤ σ → σ ≤ ε + δ₂ →
      lam * (1 - lam) / 2 * (Work.Drive.sweepW' D σ) ^ 2 * cE
            ≤ inner ℝ (Work.Drive.loopDev r D σ (1 - lam))
              (Work.Drive.chartE r D lam δ₁ δ₂ ε v) ∧
      lam * (1 - lam) / 2 * (Work.Drive.sweepW' D σ) ^ 2 * cE
            ≤ inner ℝ (Work.Drive.loopDev r D σ lam)
              (Work.Drive.chartE r D lam δ₁ δ₂ ε v) ∧
      |inner ℝ (Work.Drive.loopDev r D σ (1 - lam)) v|
            ≤ lam * (1 - lam) / 2 * (Work.Drive.sweepW' D σ) ^ 2 * K ∧
      |inner ℝ (Work.Drive.loopDev r D σ lam) v|
            ≤ lam * (1 - lam) / 2 * (Work.Drive.sweepW' D σ) ^ 2 * K := by
    intro σ h1 h2
    have hwσ : 0 < Work.Drive.sweepW' D σ := lt_of_lt_of_le (by linarith) (hWlow σ h1 h2)
    have hξ1 : (1 - lam) ∈ Set.Icc (0 : ℝ) 1 := ⟨by linarith, by linarith⟩
    have hξ0 : lam ∈ Set.Icc (0 : ℝ) 1 := ⟨hlam0.le, by linarith⟩
    have hE : ∀ x ∈ Set.Icc (Work.Drive.taR D σ) (Work.Drive.tbR D σ),
        inner ℝ (deriv (deriv r) x) (Work.Drive.chartE r D lam δ₁ δ₂ ε v) ≤ -cE :=
      fun x hx => haccC σ h1 h2 x hx
    have hV : ∀ x ∈ Set.Icc (Work.Drive.taR D σ) (Work.Drive.tbR D σ),
        |inner ℝ (deriv (deriv r) x) v| ≤ K := by
      intro x hx
      calc |inner ℝ (deriv (deriv r) x) v| ≤ ‖deriv (deriv r) x‖ * ‖v‖ :=
            abs_real_inner_le_norm _ _
        _ = ‖deriv (deriv r) x‖ := by rw [hv, mul_one]
        _ ≤ K := hKb x
    have hA := nclm_dev_scalar_ge (D := D) (r := r) hr
      (y := Work.Drive.chartE r D lam δ₁ δ₂ ε v) (c := cE) hwσ hξ1 hE
    have hB := nclm_dev_scalar_ge (D := D) (r := r) hr
      (y := Work.Drive.chartE r D lam δ₁ δ₂ ε v) (c := cE) hwσ hξ0 hE
    have hC := nclm_dev_scalar_le (D := D) (r := r) hr (y := v) (B := K) hwσ hξ1 hV
    have hD := nclm_dev_scalar_le (D := D) (r := r) hr (y := v) (B := K) hwσ hξ0 hV
    refine ⟨?_, hB, ?_, hD⟩
    · have he : lam * (1 - lam) / 2 * (Work.Drive.sweepW' D σ) ^ 2 * cE
          = ((1 - lam) * (1 - (1 - lam)) / 2) * (Work.Drive.sweepW' D σ) ^ 2 * cE := by
        ring
      rw [he]; exact hA
    · have he : lam * (1 - lam) / 2 * (Work.Drive.sweepW' D σ) ^ 2 * K
          = ((1 - lam) * (1 - (1 - lam)) / 2) * (Work.Drive.sweepW' D σ) ^ 2 * K := by
        ring
      rw [he]; exact hC
  -- the bookkeeping
  have hcu : ‖Work.Drive.chartUp r D lam δ₁ δ₂ ε v‖
      ≤ (Work.Drive.sweepW' D ε) ^ 2 * K :=
    Work.Drive.H2.chartUp_norm_bound (r := r) (D := D) (W := Work.Drive.sweepW' D ε) hr
      hK0.le hWpos.le hlam0.le hlam2 hδ₁0 hδ₁4 hδ₂0 hδ₂ε hε0 hε12 hv hKb hWup hcv
  have hInt : Work.Drive.sweepW' D ε / 2
      ≤ ∫ u in (-1 : ℝ)..1, Work.Drive.sweepBump u * Work.Drive.sweepW' D (ε - δ₂ * u) :=
    bumpAvg_ge ((Work.Drive.continuous_sweepW' D).comp (by fun_prop)).continuousOn
      (fun u hu => hWlow (ε - δ₂ * u) (hmem u hu).1 (hmem u hu).2)
  have hchord := Hchord δ₂ ε hδ₂0 hδ₂ε hε0 hεC
  have hℓ : cC * (Work.Drive.sweepW' D ε / 2)
      ≤ ‖Work.Drive.chordEndB r D δ₂ ε - Work.Drive.chordEndA r D δ₂ ε‖ :=
    le_trans (mul_le_mul_of_nonneg_left hInt hcC0.le) hchord
  have hWb : Work.Drive.sweepW' D ε * (64 * K ^ 2) ≤ cC * cE :=
    (le_div_iff₀ (by positivity : (0 : ℝ) < 64 * K ^ 2)).mp (hεS ε hε0 hεS')
  have hstep : 32 * (Work.Drive.sweepW' D ε) ^ 2 * K ^ 2
      ≤ cC * cE * Work.Drive.sweepW' D ε := by
    have h := mul_le_mul_of_nonneg_right hWb hWpos.le
    nlinarith [h, sq_nonneg (Work.Drive.sweepW' D ε * K)]
  have hbrC : 4 * (‖Work.Drive.chartUp r D lam δ₁ δ₂ ε v‖ / 2) * K
      ≤ ‖Work.Drive.chordEndB r D δ₂ ε - Work.Drive.chordEndA r D δ₂ ε‖ * cE / 8 := by
    have h1 : 4 * (‖Work.Drive.chartUp r D lam δ₁ δ₂ ε v‖ / 2) * K
        ≤ 2 * ((Work.Drive.sweepW' D ε) ^ 2 * K) * K := by
      have hh := mul_le_mul_of_nonneg_right hcu hK0.le
      linarith
    have h2 : 2 * ((Work.Drive.sweepW' D ε) ^ 2 * K) * K
        ≤ cC * Work.Drive.sweepW' D ε * cE / 16 := by
      linarith [hstep]
    have h3 : cC * Work.Drive.sweepW' D ε * cE / 16
        ≤ ‖Work.Drive.chordEndB r D δ₂ ε - Work.Drive.chordEndA r D δ₂ ε‖ * cE / 8 := by
      have hh := mul_le_mul_of_nonneg_right hℓ (by positivity : (0 : ℝ) ≤ cE / 8)
      linarith
    linarith
  exact ⟨haccC, hdevC, hbrC⟩

end Work.Drive.Generic
