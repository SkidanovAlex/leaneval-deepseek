import Mathlib
import Submission.Work.Drive.AB.pinSetup
import Submission.Work.Drive.AB.windowDataSmall
import Submission.Work.Drive.AB.needleHalfspaceProfile
import Submission.Work.Drive.H2.baseHeight_lower

/-!
# The acceleration of the needle's retained arcs against the chart's "up" direction

`Work.Drive.chartE r D lam δ₁ δ₂ ε v` is the unit "up" vector of the needle's chart: the direction
of `chartUp`, the offset of the needle's base point from the line of its chord.  Geometrically
`chartUp` is (up to the factor `w²/8`) the *opposite* of the transverse part of the acceleration of
the retained arc — the sagitta of the arc points away from the centre of curvature — so the
component of the acceleration along `chartE` is *negative*, uniformly in the box and along the arc.

This module proves that statement with an explicit constant and explicit thresholds:

* `loopDev_inner_meanValue` — the deviation `loopDev σ ξ` against an arbitrary direction, in
  mean-value (signed) form: there is an *interior* point `ζ` of the retained arc with
  `⟪loopDev σ ξ, y⟫ = -(ξ (1-ξ)/2) w² ⟪r'' ζ, y⟫` (`w = sweepW' D σ`);
* `perp_inner_ge` — the elementary linear algebra: pairing `A` with the `v`-perpendicular part of
  `Q` is at least `κ²/32` when `A` is close to `Q`, `Q` has a definite component along a unit `e`
  and a bounded component along the unit `v`;
* `chartUp_inner_arcFracQ` — the double-`sweepBump`-average identity for `chartUp` in the
  `arcFracQ` parametrisation (the form in which the pointwise bounds are applied);
* `chartUp_bounds` — the two bounds on `chartUp` used below: a lower bound for its component against
  `-e₀` (which also gives `chartUp ≠ 0`) and an upper bound for its norm;
* `chartE_accel_neg` — the target.
-/

namespace Work.Drive.H2

open LeanEval.KnotTheory.Quadrisecant MeasureTheory
open scoped Real Topology intervalIntegral

noncomputable section

/-! ## The mean-value form of the deviation against a fixed direction -/

/-- **The deviation `loopDev σ ξ` against an arbitrary direction, in signed mean-value form.**
For `ξ ∈ [0,1]` there is an interior point `ζ` of the retained arc with

    ⟪loopDev σ ξ, y⟫ = -(ξ (1-ξ) / 2) * W(σ)² * ⟪r'' ζ, y⟫ .

(The point here is the *sign*: the second derivative is taken at a single interior point, so a
definite lower bound for `⟪r'' ζ, y⟫` along the arc gives an upper bound for `⟪loopDev σ ξ, y⟫`.) -/
lemma loopDev_inner_meanValue {r : ℝ → Space} (hr : IsSmoothKnot r) {d : BandArcData}
    (D : SweepData d) {σ ξ : ℝ} (hw : 0 < sweepW' D σ) (hξ : ξ ∈ Set.Icc (0 : ℝ) 1)
    (y : Space) :
    ∃ ζ ∈ Set.Ioo (taR D σ) (tbR D σ),
      inner ℝ (loopDev r D σ ξ) y
        = -((ξ * (1 - ξ) / 2) * (sweepW' D σ) ^ 2 * inner ℝ (deriv (deriv r) ζ) y) := by
  have hf : ContDiff ℝ 2 (fun t : ℝ => inner ℝ (r t) y) := by
    have h1 : ContDiff ℝ 2 r := hr.smooth.of_le le_top
    exact ContDiff.inner ℝ h1 contDiff_const
  have hba : taR D σ < taR D σ + sweepW' D σ := by linarith
  obtain ⟨ζ, hζ, hζeq⟩ := Work.Generic.interp_error_meanValue
    (a := taR D σ) (b := taR D σ + sweepW' D σ) (ξ := ξ)
    (f := fun t : ℝ => inner ℝ (r t) y) hba hξ hf
  have hdev : inner ℝ (loopDev r D σ ξ) y
      = inner ℝ (r (taR D σ + ξ * sweepW' D σ)) y
        - ((1 - ξ) * inner ℝ (r (taR D σ)) y
            + ξ * inner ℝ (r (taR D σ + sweepW' D σ)) y) := by
    have h1 : loopDev r D σ ξ = r (taR D σ + ξ * sweepW' D σ)
        - ((1 - ξ) • r (taR D σ) + ξ • r (tbR D σ)) := rfl
    have h2 : taR D σ + sweepW' D σ = tbR D σ := by rw [sweepW']; ring
    rw [h1, h2, inner_sub_left, inner_add_left, inner_smul_left, inner_smul_left,
      RCLike.conj_to_real, RCLike.conj_to_real]
  refine ⟨ζ, ?_, ?_⟩
  · have h2 : taR D σ + sweepW' D σ = tbR D σ := by rw [sweepW']; ring
    rw [h2] at hζ
    exact hζ
  · rw [hdev]
    have h := hζeq
    rw [show taR D σ + ξ * (taR D σ + sweepW' D σ - taR D σ) = taR D σ + ξ * sweepW' D σ
        from by ring,
      show taR D σ + sweepW' D σ - taR D σ = sweepW' D σ from by ring,
      Generic.nclm_deriv2_inner hr y ζ] at h
    exact h

/-! ## Pairing the acceleration with the perpendicular part of the acceleration -/

/-- **Elementary linear algebra of the transverse part.**  Let `v`, `e` be unit vectors, `Q` with
`κ/2 ≤ ⟪Q,e⟫` and `|⟪Q,v⟫| ≤ K`, and `|⟪v,e⟫| ≤ sg` with `sg * K ≤ κ/4`.  If `A` is within `κ/16`
of `Q`, then the pairing of `A` with the `v`-perpendicular part of `Q` is at least `κ²/32`.

Indeed `⟪Q, Q - ⟪Q,v⟫ v⟫ = ‖Q - ⟪Q,v⟫ v‖²` and the perpendicular part has `e`-component at least
`κ/2 - sg K ≥ κ/4`, whence the pairing is at least `(κ/4)(κ/4 - κ/16) = 3κ²/64`. -/
lemma perp_inner_ge {A Q e v : Space} {κ K sg : ℝ} (hκ : 0 < κ) (hv : ‖v‖ = 1) (he : ‖e‖ = 1)
    (hQe : κ / 2 ≤ inner ℝ Q e) (hQv : |inner ℝ Q v| ≤ K) (hve : |inner ℝ v e| ≤ sg)
    (hK : 0 ≤ K) (hsgK : sg * K ≤ κ / 4) (hAQ : ‖A - Q‖ ≤ κ / 16) :
    κ ^ 2 / 32 ≤ inner ℝ A (Q - (inner ℝ Q v) • v) := by
  set q : Space := Q - (inner ℝ Q v) • v with hq
  have hQq : inner ℝ Q q = ‖q‖ ^ 2 := by
    rw [hq]
    exact inner_self_sub_smul Q v hv
  have hqe : κ / 4 ≤ inner ℝ q e := by
    have h1 : inner ℝ q e = inner ℝ Q e - inner ℝ Q v * inner ℝ v e := by
      rw [hq, inner_sub_left, real_inner_smul_left]
    have h2 : inner ℝ Q v * inner ℝ v e ≤ K * sg := by
      calc inner ℝ Q v * inner ℝ v e ≤ |inner ℝ Q v * inner ℝ v e| := le_abs_self _
        _ = |inner ℝ Q v| * |inner ℝ v e| := abs_mul _ _
        _ ≤ K * sg := mul_le_mul hQv hve (abs_nonneg _) hK
    rw [h1]
    linarith
  have hqnorm : κ / 4 ≤ ‖q‖ := by
    calc κ / 4 ≤ inner ℝ q e := hqe
      _ ≤ ‖q‖ * ‖e‖ := real_inner_le_norm q e
      _ = ‖q‖ := by rw [he, mul_one]
  have hkey : ‖q‖ * (‖q‖ - ‖A - Q‖) ≤ inner ℝ A q := by
    have hsplit : inner ℝ A q = inner ℝ (A - Q) q + inner ℝ Q q := by
      conv_lhs => rw [show A = (A - Q) + Q from by abel]
      rw [inner_add_left]
    have h2 : -(‖A - Q‖ * ‖q‖) ≤ inner ℝ (A - Q) q :=
      neg_le_of_abs_le (abs_real_inner_le_norm (A - Q) q)
    rw [hsplit, hQq]
    nlinarith [h2, hqnorm, norm_nonneg q, norm_nonneg (A - Q), hκ]
  have hstep : ‖q‖ * (κ / 4 - κ / 16) ≤ ‖q‖ * (‖q‖ - ‖A - Q‖) := by
    refine mul_le_mul_of_nonneg_left ?_ (by linarith)
    linarith
  have hfinal : κ ^ 2 / 32 ≤ ‖q‖ * (κ / 4 - κ / 16) := by
    nlinarith [hqnorm, hκ]
  linarith [hstep, hkey, hfinal]

/-! ## The chart vector against an arbitrary direction, in the `arcFracQ` chart -/

/-- **The double-average identity for `chartUp` in the `arcFracQ` chart.**  The `σ`-blur variable
`u` of the arc fraction is the affine surrogate `arcFracQ` (which agrees with `arcFrac` on the
smoothing window), so that the pointwise estimates on `arcFracQ` apply inside the integral. -/
lemma chartUp_inner_arcFracQ {r : ℝ → Space} (hr : IsSmoothKnot r) {d : BandArcData}
    (D : SweepData d) {lam δ₁ δ₂ ε : ℝ} {v : Space} (hlam1 : lam < 1 / 2)
    (hδ₁0 : 0 < δ₁) (hδ₁4 : δ₁ ≤ period / 4) (hv : ‖v‖ = 1)
    (hb : chordEndB r D δ₂ ε - chordEndA r D δ₂ ε
            = ‖chordEndB r D δ₂ ε - chordEndA r D δ₂ ε‖ • v) (y : Space) :
    inner ℝ (chartUp r D lam δ₁ δ₂ ε v) y
      = Generic.bumpAvg₂ (fun v' u =>
          inner ℝ (loopDev r D (ε - δ₂ * v') (Generic.arcFracQ lam δ₁ u)) y
            - inner ℝ v y * inner ℝ (loopDev r D (ε - δ₂ * v') (Generic.arcFracQ lam δ₁ u)) v) := by
  rw [Generic.nclm_chartUp_inner hr.continuous D hlam1 hδ₁0 hδ₁4 hv hb y]
  unfold Generic.bumpAvg₂
  refine intervalIntegral.integral_congr (fun v' _ => ?_)
  congr 1
  refine intervalIntegral.integral_congr (fun u hu => ?_)
  rw [Set.uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 1)] at hu
  simp only [Generic.arcFrac_quarter_eq hδ₁0 hδ₁4 hu]

/-! ## The two bounds on the chart vector -/

/-- **The two bounds on `chartUp`.**  Under the pointwise deviation bounds (which the caller reads
off `nclm_dev_scalar_ge` / `nclm_dev_scalar_le`) and the window comparisons of the retained width:

* the component of `chartUp` against `-e₀` is at least `W² κ / 256` (in particular `chartUp ≠ 0`);
* the norm of `chartUp` is at most `W² K / 2`. -/
theorem chartUp_bounds {r : ℝ → Space} (hr : IsSmoothKnot r) {d : BandArcData} (D : SweepData d)
    {lam δ₁ δ₂ ε W κ K sg : ℝ} {v : Space}
    (hv : ‖v‖ = 1)
    (hb : chordEndB r D δ₂ ε - chordEndA r D δ₂ ε
            = ‖chordEndB r D δ₂ ε - chordEndA r D δ₂ ε‖ • v)
    (hlam1 : lam < 1 / 2) (hδ₁0 : 0 < δ₁) (hδ₁4 : δ₁ ≤ period / 4)
    (hδ₂0 : 0 < δ₂) (hW : 0 < W) (hκ : 0 < κ) (hK : 0 ≤ K) (hsgK : sg * K ≤ κ / 4)
    (hacc : ∀ σ : ℝ, ε - δ₂ ≤ σ → σ ≤ ε + δ₂ →
      ∀ x ∈ Set.Icc (taR D σ) (tbR D σ),
        κ / 2 ≤ inner ℝ (Generic.nclmE0 r D) (deriv (deriv r) x))
    (hKb : ∀ x : ℝ, ‖deriv (deriv r) x‖ ≤ K)
    (hdve : |inner ℝ v (Generic.nclmE0 r D)| ≤ sg)
    (hξlo : ∀ u ∈ Set.Icc (-1 : ℝ) 1,
      (1 / 16 : ℝ) ≤ Generic.arcFracQ lam δ₁ u * (1 - Generic.arcFracQ lam δ₁ u) / 2)
    (hξhi : ∀ u ∈ Set.Icc (-1 : ℝ) 1,
      Generic.arcFracQ lam δ₁ u * (1 - Generic.arcFracQ lam δ₁ u) / 2 ≤ (1 / 8 : ℝ))
    (hξmem : ∀ u ∈ Set.Icc (-1 : ℝ) 1, Generic.arcFracQ lam δ₁ u ∈ Set.Icc (0 : ℝ) 1)
    (hwslo : ∀ σ : ℝ, ε - δ₂ ≤ σ → σ ≤ ε + δ₂ → W / 2 ≤ sweepW' D σ)
    (hwshi : ∀ σ : ℝ, ε - δ₂ ≤ σ → σ ≤ ε + δ₂ → sweepW' D σ ≤ 2 * W) :
    W ^ 2 * κ / 256 ≤ inner ℝ (chartUp r D lam δ₁ δ₂ ε v) (-(Generic.nclmE0 r D))
      ∧ ‖chartUp r D lam δ₁ δ₂ ε v‖ ≤ W ^ 2 * K / 2 := by
  have hσmem : ∀ v' ∈ Set.Icc (-1 : ℝ) 1,
      ε - δ₂ ≤ ε - δ₂ * v' ∧ ε - δ₂ * v' ≤ ε + δ₂ := by
    intro v' hv'
    constructor
    · nlinarith [hv'.2, hδ₂0]
    · nlinarith [hv'.1, hδ₂0]
  have hwpos : ∀ v' ∈ Set.Icc (-1 : ℝ) 1, 0 < sweepW' D (ε - δ₂ * v') := by
    intro v' hv'
    obtain ⟨h1, h2⟩ := hσmem v' hv'
    exact lt_of_lt_of_le (by positivity) (hwslo _ h1 h2)
  have hvw : inner ℝ v (chartUp r D lam δ₁ δ₂ ε v) = 0 := by
    rw [real_inner_comm]
    exact inner_chartUp_v r D lam δ₁ δ₂ ε hv
  have hcont_gen : ∀ y : Space, Continuous (Function.uncurry (fun v' u : ℝ =>
      inner ℝ (loopDev r D (ε - δ₂ * v') (Generic.arcFracQ lam δ₁ u)) y
        - inner ℝ v y * inner ℝ (loopDev r D (ε - δ₂ * v') (Generic.arcFracQ lam δ₁ u)) v)) := by
    intro y
    have hL := Generic.continuous_loopDevQ hr.continuous D lam δ₁ δ₂ ε
    exact (hL.inner continuous_const).sub (continuous_const.mul (hL.inner continuous_const))
  constructor
  · rw [chartUp_inner_arcFracQ hr D hlam1 hδ₁0 hδ₁4 hv hb (-(Generic.nclmE0 r D))]
    refine Generic.bumpAvg₂_ge' (hcont_gen (-(Generic.nclmE0 r D))) (C := W ^ 2 * κ / 256) ?_
    intro v' hv' u hu
    obtain ⟨hσ1, hσ2⟩ := hσmem v' hv'
    have hσp := hwpos v' hv'
    have hξm := hξmem u hu
    have hdev1 : (Generic.arcFracQ lam δ₁ u * (1 - Generic.arcFracQ lam δ₁ u) / 2)
          * (sweepW' D (ε - δ₂ * v')) ^ 2 * (κ / 2)
        ≤ inner ℝ (loopDev r D (ε - δ₂ * v') (Generic.arcFracQ lam δ₁ u))
            (-(Generic.nclmE0 r D)) :=
      Generic.nclm_dev_scalar_ge (D := D) (r := r) hr (y := -(Generic.nclmE0 r D)) (c := κ / 2)
        hσp hξm (fun x hx => by
          have h := hacc (ε - δ₂ * v') hσ1 hσ2 x hx
          rw [inner_neg_right, real_inner_comm]
          linarith)
    have hdev2 : |inner ℝ (loopDev r D (ε - δ₂ * v') (Generic.arcFracQ lam δ₁ u)) v|
        ≤ (Generic.arcFracQ lam δ₁ u * (1 - Generic.arcFracQ lam δ₁ u) / 2)
          * (sweepW' D (ε - δ₂ * v')) ^ 2 * K :=
      Generic.nclm_dev_scalar_le (D := D) (r := r) hr (y := v) (B := K) hσp hξm (fun x hx => by
        calc |inner ℝ (deriv (deriv r) x) v| ≤ ‖deriv (deriv r) x‖ * ‖v‖ :=
              abs_real_inner_le_norm _ _
          _ = ‖deriv (deriv r) x‖ := by rw [hv, mul_one]
          _ ≤ K := hKb x)
    set P : ℝ := (Generic.arcFracQ lam δ₁ u * (1 - Generic.arcFracQ lam δ₁ u) / 2)
      * (sweepW' D (ε - δ₂ * v')) ^ 2 with hPdef
    have hPpos : 0 < P := by
      have h1 := hξlo u hu
      have h2 : 0 < (sweepW' D (ε - δ₂ * v')) ^ 2 := pow_pos hσp 2
      rw [hPdef]
      positivity
    have hPlo : W ^ 2 / 64 ≤ P := by
      have h1 := hξlo u hu
      have h2 := hwslo (ε - δ₂ * v') hσ1 hσ2
      have h3 : (W / 2) ^ 2 ≤ (sweepW' D (ε - δ₂ * v')) ^ 2 := by
        have h4 : (0 : ℝ) ≤ W / 2 := by linarith
        simpa [pow_two] using mul_self_le_mul_self h4 h2
      rw [hPdef]
      nlinarith [h1, h3, h2, hW]
    have hPnn : 0 ≤ P := le_of_lt hPpos
    have hbd : inner ℝ v (-(Generic.nclmE0 r D)) ≤ sg := by
      have h1 : |inner ℝ v (-(Generic.nclmE0 r D))| ≤ sg := by
        rw [inner_neg_right, abs_neg]
        exact hdve
      exact le_trans (le_abs_self _) h1
    have hbd2 : -(sg * K * P) ≤ -inner ℝ v (-(Generic.nclmE0 r D))
        * inner ℝ (loopDev r D (ε - δ₂ * v') (Generic.arcFracQ lam δ₁ u)) v := by
      have h2 : inner ℝ v (-(Generic.nclmE0 r D))
          * inner ℝ (loopDev r D (ε - δ₂ * v') (Generic.arcFracQ lam δ₁ u)) v ≤ sg * (P * K) := by
        have h3 : |inner ℝ v (-(Generic.nclmE0 r D))| ≤ sg := by
          rw [inner_neg_right, abs_neg]
          exact hdve
        rw [hPdef] at hdev2
        calc inner ℝ v (-(Generic.nclmE0 r D))
              * inner ℝ (loopDev r D (ε - δ₂ * v') (Generic.arcFracQ lam δ₁ u)) v
            ≤ |inner ℝ v (-(Generic.nclmE0 r D))
                * inner ℝ (loopDev r D (ε - δ₂ * v') (Generic.arcFracQ lam δ₁ u)) v| :=
                le_abs_self _
          _ = |inner ℝ v (-(Generic.nclmE0 r D))|
                * |inner ℝ (loopDev r D (ε - δ₂ * v') (Generic.arcFracQ lam δ₁ u)) v| :=
                abs_mul _ _
          _ ≤ sg * (P * K) := mul_le_mul h3 hdev2 (abs_nonneg _) (le_trans (abs_nonneg _) h3)
      nlinarith [h2]
    have hkey : W ^ 2 * κ / 256 ≤ inner ℝ (loopDev r D (ε - δ₂ * v') (Generic.arcFracQ lam δ₁ u))
            (-(Generic.nclmE0 r D))
          - inner ℝ v (-(Generic.nclmE0 r D))
            * inner ℝ (loopDev r D (ε - δ₂ * v') (Generic.arcFracQ lam δ₁ u)) v := by
      rw [hPdef] at hdev1
      have hsk : sg * K * P ≤ (κ / 4) * P := mul_le_mul_of_nonneg_right hsgK hPnn
      nlinarith [hdev1, hbd2, hsk, hPlo, hPpos, hκ]
    exact hkey
  · have hself : ‖chartUp r D lam δ₁ δ₂ ε v‖ ^ 2
        = Generic.bumpAvg₂ (fun v' u =>
            inner ℝ (loopDev r D (ε - δ₂ * v') (Generic.arcFracQ lam δ₁ u))
                (chartUp r D lam δ₁ δ₂ ε v)
              - inner ℝ v (chartUp r D lam δ₁ δ₂ ε v)
                * inner ℝ (loopDev r D (ε - δ₂ * v') (Generic.arcFracQ lam δ₁ u)) v) := by
      rw [← real_inner_self_eq_norm_sq]
      exact chartUp_inner_arcFracQ hr D hlam1 hδ₁0 hδ₁4 hv hb (chartUp r D lam δ₁ δ₂ ε v)
    have hpt : ∀ v' ∈ Set.Icc (-1 : ℝ) 1, ∀ u ∈ Set.Icc (-1 : ℝ) 1,
        |inner ℝ (loopDev r D (ε - δ₂ * v') (Generic.arcFracQ lam δ₁ u))
              (chartUp r D lam δ₁ δ₂ ε v)
            - inner ℝ v (chartUp r D lam δ₁ δ₂ ε v)
              * inner ℝ (loopDev r D (ε - δ₂ * v') (Generic.arcFracQ lam δ₁ u)) v|
          ≤ W ^ 2 * K / 2 * ‖chartUp r D lam δ₁ δ₂ ε v‖ := by
      intro v' hv' u hu
      rw [hvw, zero_mul, sub_zero]
      obtain ⟨hσ1, hσ2⟩ := hσmem v' hv'
      have hσp := hwpos v' hv'
      have hξm := hξmem u hu
      have hdev := Generic.nclm_dev_scalar_le (D := D) (r := r) hr
        (y := chartUp r D lam δ₁ δ₂ ε v) (B := K * ‖chartUp r D lam δ₁ δ₂ ε v‖) hσp hξm
        (fun x hx => by
          calc |inner ℝ (deriv (deriv r) x) (chartUp r D lam δ₁ δ₂ ε v)|
              ≤ ‖deriv (deriv r) x‖ * ‖chartUp r D lam δ₁ δ₂ ε v‖ := abs_real_inner_le_norm _ _
            _ ≤ K * ‖chartUp r D lam δ₁ δ₂ ε v‖ :=
                mul_le_mul_of_nonneg_right (hKb x) (norm_nonneg _))
      calc |inner ℝ (loopDev r D (ε - δ₂ * v') (Generic.arcFracQ lam δ₁ u))
            (chartUp r D lam δ₁ δ₂ ε v)|
          ≤ (Generic.arcFracQ lam δ₁ u * (1 - Generic.arcFracQ lam δ₁ u) / 2)
              * (sweepW' D (ε - δ₂ * v')) ^ 2 * (K * ‖chartUp r D lam δ₁ δ₂ ε v‖) := hdev
        _ ≤ W ^ 2 * K / 2 * ‖chartUp r D lam δ₁ δ₂ ε v‖ := by
            have h1 := hξhi u hu
            have h2 := hwshi (ε - δ₂ * v') hσ1 hσ2
            have h3 : (sweepW' D (ε - δ₂ * v')) ^ 2 ≤ (2 * W) ^ 2 := by
              have h4 : (0 : ℝ) ≤ sweepW' D (ε - δ₂ * v') := le_of_lt hσp
              simpa [pow_two] using mul_self_le_mul_self h4 h2
            have h5 : (0 : ℝ) ≤ ‖chartUp r D lam δ₁ δ₂ ε v‖ := norm_nonneg _
            have hPnn : (0 : ℝ) ≤ Generic.arcFracQ lam δ₁ u * (1 - Generic.arcFracQ lam δ₁ u) / 2 := by
              linarith [hξlo u hu]
            have h6 : Generic.arcFracQ lam δ₁ u * (1 - Generic.arcFracQ lam δ₁ u) / 2
                * (sweepW' D (ε - δ₂ * v')) ^ 2 ≤ W ^ 2 / 2 := by
              have h4 : (0 : ℝ) ≤ (sweepW' D (ε - δ₂ * v')) ^ 2 := sq_nonneg _
              calc Generic.arcFracQ lam δ₁ u * (1 - Generic.arcFracQ lam δ₁ u) / 2
                    * (sweepW' D (ε - δ₂ * v')) ^ 2
                  ≤ (1 / 8) * (4 * W ^ 2) := mul_le_mul h1 (by nlinarith [h3]) h4 (by norm_num)
                _ = W ^ 2 / 2 := by ring
            have h7 : (0 : ℝ) ≤ K * ‖chartUp r D lam δ₁ δ₂ ε v‖ := mul_nonneg hK h5
            calc Generic.arcFracQ lam δ₁ u * (1 - Generic.arcFracQ lam δ₁ u) / 2
                  * (sweepW' D (ε - δ₂ * v')) ^ 2 * (K * ‖chartUp r D lam δ₁ δ₂ ε v‖)
                ≤ (W ^ 2 / 2) * (K * ‖chartUp r D lam δ₁ δ₂ ε v‖) :=
                  mul_le_mul_of_nonneg_right h6 h7
              _ = W ^ 2 * K / 2 * ‖chartUp r D lam δ₁ δ₂ ε v‖ := by ring
    have hsq : ‖chartUp r D lam δ₁ δ₂ ε v‖ ^ 2
        ≤ W ^ 2 * K / 2 * ‖chartUp r D lam δ₁ δ₂ ε v‖ := by
      have h := Generic.bumpAvg₂_abs_le' (hcont_gen (chartUp r D lam δ₁ δ₂ ε v)) hpt
      rw [← hself] at h
      rwa [abs_of_nonneg (sq_nonneg _)] at h
    rcases eq_or_lt_of_le (norm_nonneg (chartUp r D lam δ₁ δ₂ ε v)) with h0 | hpos
    · rw [← h0]
      positivity
    · have h1 : ‖chartUp r D lam δ₁ δ₂ ε v‖ * ‖chartUp r D lam δ₁ δ₂ ε v‖
          ≤ W ^ 2 * K / 2 * ‖chartUp r D lam δ₁ δ₂ ε v‖ := by
        rwa [pow_two] at hsq
      exact le_of_mul_le_mul_right h1 hpos


/-! ## The target -/

set_option maxHeartbeats 1000000 in
theorem chartE_accel_neg {r : ℝ → LeanEval.KnotTheory.Quadrisecant.Space}
    (hr : LeanEval.KnotTheory.Quadrisecant.IsSmoothKnot r)
    (hinfl : ∀ t : ℝ, LinearIndependent ℝ ![deriv r t, deriv (deriv r) t])
    {d : LeanEval.KnotTheory.Quadrisecant.BandArcData} (D : Work.Drive.SweepData d) :
    ∃ c : ℝ, 0 < c ∧ ∃ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ ≤ 1 / 2 ∧ ∀ ε : ℝ, 0 < ε → ε ≤ ε₀ →
      ∃ Λ : ℝ, 0 < Λ ∧ Λ ≤ 1 / 4 ∧
        ∀ lam δ₁ δ₂ : ℝ, 0 < lam → lam ≤ Λ → 0 < δ₁ → δ₁ ≤ Λ →
          0 < δ₂ → δ₂ ≤ Λ → δ₂ ≤ ε / 2 →
        ∀ v : LeanEval.KnotTheory.Quadrisecant.Space, ‖v‖ = 1 →
          Work.Drive.chordEndB r D δ₂ ε - Work.Drive.chordEndA r D δ₂ ε
            = ‖Work.Drive.chordEndB r D δ₂ ε - Work.Drive.chordEndA r D δ₂ ε‖ • v →
        ∀ σ : ℝ, ε - δ₂ ≤ σ → σ ≤ ε + δ₂ →
        ∀ x : ℝ, Work.Drive.taR D σ ≤ x → x ≤ Work.Drive.tbR D σ →
          inner ℝ (iteratedDeriv 2 r x) (Work.Drive.chartE r D lam δ₁ δ₂ ε v) ≤ -c := by
  -- a global bound for the acceleration and a Lipschitz constant for it
  obtain ⟨K, hK1, hKb⟩ := H2_accel_bound hr
  have hK0 : 0 < K := lt_of_lt_of_le zero_lt_one hK1
  obtain ⟨CL, hCL0, hCL⟩ := Generic.nclm_lipschitz_r'' hr
  -- the transverse frame at the collapsed end
  set e₀ : Space := Generic.nclmE0 r D with he₀
  set T : Space := Generic.nclmT r D with hT
  set κ : ℝ := inner ℝ e₀ (deriv (deriv r) (taR D 0)) with hκ
  have hκpos : 0 < κ := by
    rw [hκ, he₀, real_inner_comm]
    show 0 < inner ℝ (deriv (deriv r) (Generic.nclmRho D)) (Generic.nclmE0 r D)
    rw [Generic.nclm_inner_r''_E0 hr hinfl D]
    exact norm_pos_iff.mpr (Generic.nclmW_ne_zero hr hinfl D)
  -- the smallness radius of the chord direction
  set sg : ℝ := min (min 1 (κ / (64 * K))) (κ / (64 * CL)) with hsg
  have hsg0 : 0 < sg := by
    rw [hsg]
    exact lt_min (lt_min one_pos (by positivity)) (by positivity)
  have hsgK : sg * K ≤ κ / 64 := by
    have h : sg ≤ κ / (64 * K) := le_trans (min_le_left _ _) (min_le_right _ _)
    calc sg * K ≤ (κ / (64 * K)) * K := mul_le_mul_of_nonneg_right h hK0.le
      _ = κ / 64 := by field_simp
  have hsgCL : sg * CL ≤ κ / 64 := by
    have h : sg ≤ κ / (64 * CL) := min_le_right _ _
    calc sg * CL ≤ (κ / (64 * CL)) * CL := mul_le_mul_of_nonneg_right h hCL0.le
      _ = κ / 64 := by field_simp
  -- the two window thresholds
  obtain ⟨εA, hεA0, hεA12, hAcc⟩ :=
    Generic.nclm_acc (r := r) hr D (e₀ := e₀) (by rw [← hκ]; exact hκpos)
  obtain ⟨εw, hεw0, hεw1, hwin⟩ := windowDataSmall (r := r) hr D sg hsg0
  refine ⟨κ ^ 2 / (1024 * K), by positivity, min (min εA εw) (1 / 2), ?_, ?_, ?_⟩
  · exact lt_min (lt_min hεA0 hεw0) (by norm_num)
  · exact le_trans (min_le_right _ _) (by norm_num)
  · intro ε hε0 hεle
    have hεA : ε ≤ εA := le_trans hεle (le_trans (min_le_left _ _) (min_le_left _ _))
    have hεw : ε ≤ εw := le_trans hεle (le_trans (min_le_left _ _) (min_le_right _ _))
    have hε12 : ε ≤ 1 / 2 := le_trans hεle (min_le_right _ _)
    have hε1' : ε < 1 := by linarith
    have hWpos : 0 < sweepW' D ε := wds_sweepW'_pos D hε0 hε1'
    obtain ⟨Λw, hΛw0, hΛw⟩ := Generic.nclm_window_eps D hε0 hε1'
    refine ⟨min (1 / 4) Λw, lt_min (by norm_num) hΛw0, min_le_left _ _, ?_⟩
    intro lam δ₁ δ₂ hlam0 hlamΛ hδ₁0 hδ₁Λ hδ₂0 hδ₂Λ hδ₂ε
    have hlam14 : lam ≤ 1 / 4 := le_trans hlamΛ (min_le_left _ _)
    have hδ₁14 : δ₁ ≤ 1 / 4 := le_trans hδ₁Λ (min_le_left _ _)
    have hδ₂Λw : δ₂ ≤ Λw := le_trans hδ₂Λ (min_le_right _ _)
    have hlam12 : lam < 1 / 2 := by linarith
    have hπ4 : (1 : ℝ) / 4 ≤ period / 4 := by rw [period]; nlinarith [Real.pi_gt_three]
    have hπ16 : (1 : ℝ) / 4 ≤ period / 16 := by rw [period]; nlinarith [Real.pi_gt_three]
    have hδ₁4 : δ₁ ≤ period / 4 := by linarith
    have hδ₁16 : δ₁ ≤ period / 16 := by linarith
    have hwslo : ∀ σ : ℝ, ε - δ₂ ≤ σ → σ ≤ ε + δ₂ → sweepW' D ε / 2 ≤ sweepW' D σ :=
      fun σ h1 h2 => (hΛw δ₂ σ hδ₂0 hδ₂Λw hδ₂ε h1 h2).1
    have hwshi : ∀ σ : ℝ, ε - δ₂ ≤ σ → σ ≤ ε + δ₂ → sweepW' D σ ≤ 2 * sweepW' D ε :=
      fun σ h1 h2 => (hΛw δ₂ σ hδ₂0 hδ₂Λw hδ₂ε h1 h2).2.1
    obtain ⟨hclose, hCne, hdir⟩ := hwin δ₂ ε hδ₂0 hδ₂ε hε0 hεw
    -- the arc-fraction bounds
    have hξmem : ∀ u ∈ Set.Icc (-1 : ℝ) 1,
        Generic.arcFracQ lam δ₁ u ∈ Set.Icc (0 : ℝ) 1 := by
      intro u hu
      obtain ⟨h1, h2⟩ := Generic.arcFracQ_mem hlam0.le (by linarith) hδ₁0 hδ₁16 hu
      exact ⟨by linarith, by linarith⟩
    have hξlo : ∀ u ∈ Set.Icc (-1 : ℝ) 1,
        (1 / 16 : ℝ) ≤ Generic.arcFracQ lam δ₁ u * (1 - Generic.arcFracQ lam δ₁ u) / 2 := by
      intro u hu
      obtain ⟨h1, h2⟩ := Generic.arcFracQ_mem hlam0.le (by linarith) hδ₁0 hδ₁16 hu
      have hkey : (3 : ℝ) / 16 ≤ Generic.arcFracQ lam δ₁ u * (1 - Generic.arcFracQ lam δ₁ u) := by
        nlinarith [mul_nonneg (show (0:ℝ) ≤ Generic.arcFracQ lam δ₁ u - 1 / 4 by linarith)
          (show (0:ℝ) ≤ 3 / 4 - Generic.arcFracQ lam δ₁ u by linarith)]
      linarith
    have hξhi : ∀ u ∈ Set.Icc (-1 : ℝ) 1,
        Generic.arcFracQ lam δ₁ u * (1 - Generic.arcFracQ lam δ₁ u) / 2 ≤ (1 / 8 : ℝ) := by
      intro u hu
      have hkey : Generic.arcFracQ lam δ₁ u * (1 - Generic.arcFracQ lam δ₁ u) ≤ (1 : ℝ) / 4 := by
        nlinarith [sq_nonneg (Generic.arcFracQ lam δ₁ u - 1 / 2)]
      linarith
    -- the definite transverse acceleration on the window's arcs
    have hacc : ∀ σ : ℝ, ε - δ₂ ≤ σ → σ ≤ ε + δ₂ →
        ∀ x ∈ Set.Icc (taR D σ) (tbR D σ),
          κ / 2 ≤ inner ℝ e₀ (deriv (deriv r) x) := by
      intro σ h1 h2 x hx
      have h := hAcc δ₂ ε σ x hδ₂0 hδ₂ε hε0 hεA h1 h2 hx
      simpa only [← hκ] using h
    intro v hv hcv σ hσlo hσhi x hxlo hxhi
    have hx : x ∈ Set.Icc (taR D σ) (tbR D σ) := ⟨hxlo, hxhi⟩
    -- `v` is the unit chord direction, hence close to the tangent at the collapsed end
    have hCne' : chordEndB r D δ₂ ε - chordEndA r D δ₂ ε ≠ 0 := sub_ne_zero.mpr hCne
    have hvunit : v = ‖chordEndB r D δ₂ ε - chordEndA r D δ₂ ε‖⁻¹ •
        (chordEndB r D δ₂ ε - chordEndA r D δ₂ ε) := by
      have h2 : ‖chordEndB r D δ₂ ε - chordEndA r D δ₂ ε‖ ≠ 0 :=
        norm_ne_zero_iff.mpr hCne'
      have hgen : ∀ y : Space, y = ‖chordEndB r D δ₂ ε - chordEndA r D δ₂ ε‖ • v →
          ‖chordEndB r D δ₂ ε - chordEndA r D δ₂ ε‖⁻¹ • y = v := fun y hy => by
        rw [hy, smul_smul, inv_mul_cancel₀ h2, one_smul]
      exact (hgen _ hcv).symm
    have hTn : T = (‖deriv r (taR D 0)‖)⁻¹ • deriv r (taR D 0) := rfl
    have hdirv : ‖v - T‖ ≤ sg := by
      rw [hvunit, hTn]
      exact hdir
    have hE0T : inner ℝ T e₀ = 0 := by
      rw [hT, he₀, real_inner_comm]
      exact Generic.nclm_inner_E0_T hr hinfl D
    have hdve : |inner ℝ v e₀| ≤ sg := by
      have h1 : inner ℝ v e₀ = inner ℝ (v - T) e₀ := by rw [inner_sub_left, hE0T, sub_zero]
      rw [h1]
      calc |inner ℝ (v - T) e₀| ≤ ‖v - T‖ * ‖e₀‖ := abs_real_inner_le_norm _ _
        _ = ‖v - T‖ := by rw [he₀, Generic.nclmE0_norm hr hinfl D, mul_one]
        _ ≤ sg := hdirv
    -- `x` as a fraction of the retained arc, and the closeness of everything to the collapsed end
    have hWσpos : 0 < sweepW' D σ := lt_of_lt_of_le (by positivity) (hwslo σ hσlo hσhi)
    have hwtb : taR D σ + sweepW' D σ = tbR D σ := by rw [sweepW']; ring
    set ξx : ℝ := (x - taR D σ) / sweepW' D σ with hξx
    have hξx0 : 0 ≤ ξx := by rw [hξx]; exact div_nonneg (by linarith) hWσpos.le
    have hξx1 : ξx ≤ 1 := by rw [hξx, div_le_one hWσpos]; linarith
    have hxeq : x = taR D σ + ξx * sweepW' D σ := by rw [hξx]; field_simp; ring
    have hxclose : |x - taR D 0| ≤ sg := by
      rw [hxeq]
      exact hclose σ hσlo hσhi ξx hξx0 hξx1
    -- the two chart bounds
    obtain ⟨hchart_ge, hchart_le⟩ := chartUp_bounds (r := r) hr D (v := v) (hv := hv) (hb := hcv)
      (hlam1 := hlam12) (hδ₁0 := hδ₁0) (hδ₁4 := hδ₁4) (hδ₂0 := hδ₂0) (hW := hWpos)
      (hκ := hκpos) (hK := hK0.le) (hsgK := by linarith [hsgK]) (hacc := hacc) (hKb := hKb)
      (hdve := hdve) (hξlo := hξlo) (hξhi := hξhi) (hξmem := hξmem) (hwslo := hwslo)
      (hwshi := hwshi)
    -- the perpendicular part of the acceleration at `x`
    have hvw' : inner ℝ (chartUp r D lam δ₁ δ₂ ε v) v = 0 :=
      inner_chartUp_v r D lam δ₁ δ₂ ε hv
    set q : Space := deriv (deriv r) x - (inner ℝ (deriv (deriv r) x) v) • v with hq
    have hqv : inner ℝ v q = 0 := by
      have h1 : inner ℝ v q = inner ℝ v (deriv (deriv r) x)
          - inner ℝ (deriv (deriv r) x) v * inner ℝ v v := by
        rw [hq, inner_sub_right, real_inner_smul_right]
      have h2 : inner ℝ v v = 1 := by rw [real_inner_self_eq_norm_sq, hv]; norm_num
      rw [h1, h2, mul_one, real_inner_comm]
      ring
    have hσmem2 : ∀ v' ∈ Set.Icc (-1 : ℝ) 1,
        ε - δ₂ ≤ ε - δ₂ * v' ∧ ε - δ₂ * v' ≤ ε + δ₂ := by
      intro v' hv'
      constructor
      · nlinarith [hv'.2, hδ₂0]
      · nlinarith [hv'.1, hδ₂0]
    have hwpos2 : ∀ v' ∈ Set.Icc (-1 : ℝ) 1, 0 < sweepW' D (ε - δ₂ * v') := by
      intro v' hv'
      obtain ⟨h1, h2⟩ := hσmem2 v' hv'
      exact lt_of_lt_of_le (by positivity) (hwslo _ h1 h2)
    -- the numerator bound: `⟪r''x, chartUp⟫ ≤ -W²κ²/2048`
    have hnum : inner ℝ (deriv (deriv r) x) (chartUp r D lam δ₁ δ₂ ε v)
        ≤ -((sweepW' D ε) ^ 2 * κ ^ 2 / 2048) := by
      have hid := chartUp_inner_arcFracQ (r := r) hr D (v := v) hlam12 hδ₁0 hδ₁4 hv hcv q
      have hcont : Continuous (Function.uncurry (fun v' u : ℝ =>
          inner ℝ (loopDev r D (ε - δ₂ * v') (Generic.arcFracQ lam δ₁ u)) q
            - inner ℝ v q
              * inner ℝ (loopDev r D (ε - δ₂ * v') (Generic.arcFracQ lam δ₁ u)) v)) := by
        have hL := Generic.continuous_loopDevQ hr.continuous D lam δ₁ δ₂ ε
        exact (hL.inner continuous_const).sub (continuous_const.mul (hL.inner continuous_const))
      have hpt : ∀ v' ∈ Set.Icc (-1 : ℝ) 1, ∀ u ∈ Set.Icc (-1 : ℝ) 1,
          inner ℝ (loopDev r D (ε - δ₂ * v') (Generic.arcFracQ lam δ₁ u)) q
            - inner ℝ v q * inner ℝ (loopDev r D (ε - δ₂ * v') (Generic.arcFracQ lam δ₁ u)) v
          ≤ -((sweepW' D ε) ^ 2 * κ ^ 2 / 2048) := by
        intro v' hv' u hu
        rw [hqv, zero_mul, sub_zero]
        obtain ⟨hσ1, hσ2⟩ := hσmem2 v' hv'
        have hσp := hwpos2 v' hv'
        have hξm := hξmem u hu
        obtain ⟨ζ, hζ, hζeq⟩ := loopDev_inner_meanValue (r := r) hr D hσp hξm q
        have hperp : κ ^ 2 / 32 ≤ inner ℝ (deriv (deriv r) ζ) q := by
          have hmain := perp_inner_ge (A := deriv (deriv r) ζ) (Q := deriv (deriv r) x)
            (e := e₀) (v := v) (κ := κ) (K := K) (sg := sg) hκpos hv
            (Generic.nclmE0_norm hr hinfl D) ?_ ?_ hdve hK0.le (by linarith [hsgK]) ?_
          · rw [← hq] at hmain
            exact hmain
          · have h := hacc σ hσlo hσhi x hx
            rw [real_inner_comm]
            exact h
          · calc |inner ℝ (deriv (deriv r) x) v|
                ≤ ‖deriv (deriv r) x‖ * ‖v‖ := abs_real_inner_le_norm _ _
              _ = ‖deriv (deriv r) x‖ := by rw [hv, mul_one]
              _ ≤ K := hKb x
          · have hζclose : |ζ - taR D 0| ≤ sg := by
              obtain ⟨hζ1, hζ2⟩ := hζ
              have hwtb' : taR D (ε - δ₂ * v') + sweepW' D (ε - δ₂ * v')
                  = tbR D (ε - δ₂ * v') := by rw [sweepW']; ring
              set ξz : ℝ := (ζ - taR D (ε - δ₂ * v')) / sweepW' D (ε - δ₂ * v') with hξz
              have hz0 : 0 ≤ ξz := by
                rw [hξz]
                exact div_nonneg (by linarith [hζ1]) (le_of_lt hσp)
              have hz1 : ξz ≤ 1 := by
                rw [hξz, div_le_one hσp]
                linarith [hζ2, hwtb']
              have hzeq : ζ = taR D (ε - δ₂ * v') + ξz * sweepW' D (ε - δ₂ * v') := by
                rw [hξz]; field_simp; ring
              rw [hzeq]
              exact hclose (ε - δ₂ * v') hσ1 hσ2 ξz hz0 hz1
            have hxd : |ζ - x| ≤ 2 * sg := by
              have h2 : |ζ - x| = |(ζ - taR D 0) - (x - taR D 0)| := by ring_nf
              rw [h2]
              calc |(ζ - taR D 0) - (x - taR D 0)| ≤ |ζ - taR D 0| + |x - taR D 0| := abs_sub _ _
                _ ≤ sg + sg := add_le_add hζclose hxclose
                _ = 2 * sg := by ring
            calc ‖deriv (deriv r) ζ - deriv (deriv r) x‖ ≤ CL * |ζ - x| := hCL ζ x
              _ ≤ CL * (2 * sg) := mul_le_mul_of_nonneg_left hxd hCL0.le
              _ = 2 * (sg * CL) := by ring
              _ ≤ 2 * (κ / 64) := by linarith [hsgCL]
              _ = κ / 32 := by ring
              _ ≤ κ / 16 := by linarith [hκpos]
        have hPlo : (sweepW' D ε) ^ 2 / 64
            ≤ (Generic.arcFracQ lam δ₁ u * (1 - Generic.arcFracQ lam δ₁ u) / 2)
              * (sweepW' D (ε - δ₂ * v')) ^ 2 := by
          have h1 := hξlo u hu
          have h2 := hwslo (ε - δ₂ * v') hσ1 hσ2
          have h3 : (sweepW' D ε / 2) ^ 2 ≤ (sweepW' D (ε - δ₂ * v')) ^ 2 := by
            have h4 : (0 : ℝ) ≤ sweepW' D ε / 2 := by linarith
            simpa [pow_two] using mul_self_le_mul_self h4 h2
          have h5 : (0 : ℝ) ≤ Generic.arcFracQ lam δ₁ u * (1 - Generic.arcFracQ lam δ₁ u) / 2 := by
            linarith [hξlo u hu]
          calc (sweepW' D ε) ^ 2 / 64 = (1 / 16) * (sweepW' D ε / 2) ^ 2 := by ring
            _ ≤ (Generic.arcFracQ lam δ₁ u * (1 - Generic.arcFracQ lam δ₁ u) / 2)
                * (sweepW' D (ε - δ₂ * v')) ^ 2 :=
                mul_le_mul h1 h3 (by positivity) h5
        calc inner ℝ (loopDev r D (ε - δ₂ * v') (Generic.arcFracQ lam δ₁ u)) q
            = -((Generic.arcFracQ lam δ₁ u * (1 - Generic.arcFracQ lam δ₁ u) / 2)
                * (sweepW' D (ε - δ₂ * v')) ^ 2 * inner ℝ (deriv (deriv r) ζ) q) := hζeq
          _ ≤ -((sweepW' D ε) ^ 2 / 64 * (κ ^ 2 / 32)) := by
              have hPnn : (0 : ℝ) ≤ (Generic.arcFracQ lam δ₁ u
                  * (1 - Generic.arcFracQ lam δ₁ u) / 2) * (sweepW' D (ε - δ₂ * v')) ^ 2 := by
                have h5 : (0 : ℝ) ≤ Generic.arcFracQ lam δ₁ u
                    * (1 - Generic.arcFracQ lam δ₁ u) / 2 := by linarith [hξlo u hu]
                positivity
              nlinarith [hperp, hPlo, hPnn]
          _ = -((sweepW' D ε) ^ 2 * κ ^ 2 / 2048) := by ring
      have hle := Generic.bumpAvg₂_le' hcont hpt
      have h2 : inner ℝ (chartUp r D lam δ₁ δ₂ ε v) q
          ≤ -((sweepW' D ε) ^ 2 * κ ^ 2 / 2048) := by
        rw [hid]
        exact hle
      have h3 : inner ℝ (deriv (deriv r) x) (chartUp r D lam δ₁ δ₂ ε v)
          = inner ℝ (chartUp r D lam δ₁ δ₂ ε v) q := by
        rw [hq, inner_sub_right, real_inner_smul_right, hvw', mul_zero, sub_zero, real_inner_comm]
      rw [h3]
      exact h2
    -- the final combination with the norm bound
    have hfinal : inner ℝ (deriv (deriv r) x) (chartE r D lam δ₁ δ₂ ε v)
        ≤ -(κ ^ 2 / (1024 * K)) := by
      have hNpos : 0 < ‖chartUp r D lam δ₁ δ₂ ε v‖ := by
        have h1 : (0 : ℝ) < (sweepW' D ε) ^ 2 * κ / 256 := by positivity
        have h2 : 0 < inner ℝ (chartUp r D lam δ₁ δ₂ ε v) (-(Generic.nclmE0 r D)) :=
          lt_of_lt_of_le h1 hchart_ge
        have h3 : inner ℝ (chartUp r D lam δ₁ δ₂ ε v) (-(Generic.nclmE0 r D))
            ≤ ‖chartUp r D lam δ₁ δ₂ ε v‖ := by
          calc inner ℝ (chartUp r D lam δ₁ δ₂ ε v) (-(Generic.nclmE0 r D))
              ≤ ‖chartUp r D lam δ₁ δ₂ ε v‖ * ‖-(Generic.nclmE0 r D)‖ := real_inner_le_norm _ _
            _ = ‖chartUp r D lam δ₁ δ₂ ε v‖ := by
                rw [norm_neg, Generic.nclmE0_norm hr hinfl D, mul_one]
        linarith
      have hstep : inner ℝ (deriv (deriv r) x) (chartUp r D lam δ₁ δ₂ ε v)
          ≤ -(κ ^ 2 / (1024 * K)) * ‖chartUp r D lam δ₁ δ₂ ε v‖ := by
        have hcnonpos : -(κ ^ 2 / (1024 * K)) ≤ 0 := by
          have hc0 : (0 : ℝ) ≤ κ ^ 2 / (1024 * K) := by positivity
          linarith
        have h2 : -(κ ^ 2 / (1024 * K)) * ((sweepW' D ε) ^ 2 * K / 2)
            ≤ -(κ ^ 2 / (1024 * K)) * ‖chartUp r D lam δ₁ δ₂ ε v‖ :=
          mul_le_mul_of_nonpos_left hchart_le hcnonpos
        have h3 : -(κ ^ 2 / (1024 * K)) * ((sweepW' D ε) ^ 2 * K / 2)
            = -((sweepW' D ε) ^ 2 * κ ^ 2 / 2048) := by
          field_simp
          ring
        linarith [hnum, h2, h3]
      calc inner ℝ (deriv (deriv r) x) (chartE r D lam δ₁ δ₂ ε v)
          = (‖chartUp r D lam δ₁ δ₂ ε v‖)⁻¹
              * inner ℝ (deriv (deriv r) x) (chartUp r D lam δ₁ δ₂ ε v) := by
            rw [chartE, real_inner_smul_right]
        _ ≤ (‖chartUp r D lam δ₁ δ₂ ε v‖)⁻¹
              * (-(κ ^ 2 / (1024 * K)) * ‖chartUp r D lam δ₁ δ₂ ε v‖) :=
            mul_le_mul_of_nonneg_left hstep (le_of_lt (inv_pos.mpr hNpos))
        _ = -(κ ^ 2 / (1024 * K)) := by
            field_simp
    have hiter : iteratedDeriv 2 r = deriv (deriv r) := by
      rw [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ', iteratedDeriv_one]
    rw [hiter]
    exact hfinal

end

end Work.Drive.H2
