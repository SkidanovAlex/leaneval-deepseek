import Mathlib
import Submission.Work.Drive.AB.pinSetup
import Submission.Work.Drive.AB.windowDataSmall
import Submission.Work.Drive.AB.needleHalfspaceProfile
import Submission.Work.Drive.AB.needleFam_inner_eq_devAvg
import Submission.Work.Drive.Generic.nclm_blur_close_scale
import Submission.Work.Drive.H2.baseHeight_lower
import Submission.Work.Drive.H2.chordZoneClosed
import Submission.Work.Drive.H2.basePoint_v_coord
import Submission.Work.Drive.H2.chartUp_norm_bound

/-!
# The chart coordinates of the two chamfers of the needle's loop

`Work.Drive.H2.chamfer_pos_data` is the *geometric data* of the two chamfer (leg) branches of the
per-loop margin `Work.Drive.ChartLoopMargin`: for every small box `(lam, δ₁, δ₂)`, every `σ` in the
blur window and every unit `v` along the needle's chord, the loop point on the head chamfer lies at
chord coordinate at least `(1/4)(1/2 - lam) ℓ` (and on the tail chamfer at most its negative, with
`ℓ = ‖chordEndB - chordEndA‖`), while its `chartE`-coordinate is `O(W²)` with `W = sweepW' D ε`.

The proof is a bookkeeping estimate around three proved facts:

* `Work.Drive.H2.basePoint_v_coord` — the needle's base point has chord coordinate `ℓ/2 + O(W²)`;
* `Work.Drive.H2.chartUp_norm_bound` — `‖chartUp‖ ≤ W² K`;
* `Work.Drive.Generic.nclm_dev_scalar_le` — the retained arc's deviation from its chord is
  `O(ξ(1-ξ) W² K)` against every direction,

combined in `Work.Drive.H2.sweep_chart_bounds` (the chart coordinates of the arc and of its chord at
a general fraction `ξ`), the branch decomposition of `sweepLoopChamfer`, and the lower bound
`c_L W ≤ ℓ` of `Work.Drive.H2.chordLen_lower` (which dominates all the `O(W²)` errors for small `ε`).
-/

set_option maxHeartbeats 4000000

namespace Work.Drive.H2

open LeanEval.KnotTheory.Quadrisecant MeasureTheory
open scoped Real Topology intervalIntegral

noncomputable section

variable {r : ℝ → Space} {d : BandArcData} {D : SweepData d}

/-! ## Chart frame facts -/

lemma chartUp_inner_v {r : ℝ → Space} {d : BandArcData} {D : SweepData d}
    {lam δ₁ δ₂ ε : ℝ} {v : Space} (hv : ‖v‖ = 1) :
    inner ℝ (chartUp r D lam δ₁ δ₂ ε v) v = 0 := by
  have hv1 : inner ℝ v v = 1 := by rw [real_inner_self_eq_norm_sq, hv]; norm_num
  simp only [chartUp, nCoord, inner_sub_left, real_inner_smul_left, hv1]
  ring

lemma chartE_inner_v {r : ℝ → Space} {d : BandArcData} {D : SweepData d}
    {lam δ₁ δ₂ ε : ℝ} {v : Space} (hv : ‖v‖ = 1) :
    inner ℝ (chartE r D lam δ₁ δ₂ ε v) v = 0 := by
  rw [chartE, real_inner_smul_left,
    chartUp_inner_v (r := r) (D := D) (lam := lam) (δ₁ := δ₁) (δ₂ := δ₂) (ε := ε) hv,
    mul_zero]

lemma chartE_norm_le_one (r : ℝ → Space) {d : BandArcData} (D : SweepData d)
    (lam δ₁ δ₂ ε : ℝ) (v : Space) : ‖chartE r D lam δ₁ δ₂ ε v‖ ≤ 1 := by
  rw [chartE, norm_smul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (norm_nonneg _))]
  rcases eq_or_ne (chartUp r D lam δ₁ δ₂ ε v) 0 with h | h
  · rw [h, norm_zero, inv_zero, zero_mul]; norm_num
  · rw [inv_mul_cancel₀ (norm_ne_zero_iff.mpr h)]

lemma chartE_norm_sq_mul (r : ℝ → Space) {d : BandArcData} (D : SweepData d)
    (lam δ₁ δ₂ ε : ℝ) (v : Space) :
    (‖chartUp r D lam δ₁ δ₂ ε v‖ / 2) * ‖chartE r D lam δ₁ δ₂ ε v‖ ^ 2
      = ‖chartUp r D lam δ₁ δ₂ ε v‖ / 2 := by
  rw [chartE, norm_smul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (norm_nonneg _))]
  rcases eq_or_ne (chartUp r D lam δ₁ δ₂ ε v) 0 with h | h
  · rw [h, norm_zero, inv_zero, zero_mul, zero_pow (by norm_num : (2:ℕ) ≠ 0), mul_zero]
    norm_num
  · rw [inv_mul_cancel₀ (norm_ne_zero_iff.mpr h), one_pow, mul_one]

lemma chartC_sub_inner_v {r : ℝ → Space} {d : BandArcData} {D : SweepData d}
    {lam δ₁ δ₂ ε : ℝ} {v : Space} (hv : ‖v‖ = 1) :
    inner ℝ (chartC r D lam δ₁ δ₂ ε v - chordEndA r D δ₂ ε) v
      = inner ℝ (shiftedNeedle r D lam δ₁ δ₂ ε 0 - chordEndA r D δ₂ ε) v := by
  have hv1 : inner ℝ v v = 1 := by rw [real_inner_self_eq_norm_sq, hv]; norm_num
  have hdecomp : chartC r D lam δ₁ δ₂ ε v - chordEndA r D δ₂ ε
      = (nCoord r D lam δ₁ δ₂ ε v 0) • v
        + (‖chartUp r D lam δ₁ δ₂ ε v‖ / 2) • chartE r D lam δ₁ δ₂ ε v := by
    rw [chartC]; abel
  rw [hdecomp, inner_add_left, real_inner_smul_left, real_inner_smul_left, hv1,
    chartE_inner_v (r := r) (D := D) (lam := lam) (δ₁ := δ₁) (δ₂ := δ₂) (ε := ε) hv,
    mul_one, mul_zero, add_zero, nCoord]

lemma chartC_sub_inner_chartE {r : ℝ → Space} {d : BandArcData} {D : SweepData d}
    {lam δ₁ δ₂ ε : ℝ} {v : Space} (hv : ‖v‖ = 1) :
    inner ℝ (chartC r D lam δ₁ δ₂ ε v - chordEndA r D δ₂ ε) (chartE r D lam δ₁ δ₂ ε v)
      = ‖chartUp r D lam δ₁ δ₂ ε v‖ / 2 := by
  have hdecomp : chartC r D lam δ₁ δ₂ ε v - chordEndA r D δ₂ ε
      = (nCoord r D lam δ₁ δ₂ ε v 0) • v
        + (‖chartUp r D lam δ₁ δ₂ ε v‖ / 2) • chartE r D lam δ₁ δ₂ ε v := by
    rw [chartC]; abel
  have hve : inner ℝ v (chartE r D lam δ₁ δ₂ ε v) = 0 := by
    rw [real_inner_comm]
    exact chartE_inner_v (r := r) (D := D) (lam := lam) (δ₁ := δ₁) (δ₂ := δ₂) (ε := ε) hv
  rw [hdecomp, inner_add_left, real_inner_smul_left, real_inner_smul_left, hve, mul_zero,
    zero_add, real_inner_self_eq_norm_sq, chartE_norm_sq_mul]

/-! ## The chart coordinates of the arc and the chord -/

/-- `|a + b + c - d| ≤ |a| + |b| + |c| + |d|`. -/
lemma abs_add_sub_le_four (a b c dd : ℝ) : |a + b + c - dd| ≤ |a| + |b| + |c| + |dd| := by
  have h1 : a + b + c - dd = (a + b + c) + (-dd) := by ring
  rw [h1]
  calc |a + b + c + -dd| ≤ |a + b + c| + |-dd| := abs_add_le _ _
    _ ≤ (|a + b| + |c|) + |dd| := by rw [abs_neg]; gcongr; exact abs_add_le _ _
    _ ≤ ((|a| + |b|) + |c|) + |dd| := by gcongr; exact abs_add_le _ _
    _ = |a| + |b| + |c| + |dd| := by ring

/-- `|a + b - c| ≤ |a| + |b| + |c|`. -/
lemma abs_add_sub_le_three (a b c : ℝ) : |a + b - c| ≤ |a| + |b| + |c| := by
  have h1 : a + b - c = (a + b) + (-c) := by ring
  rw [h1]
  calc |a + b + -c| ≤ |a + b| + |-c| := abs_add_le _ _
    _ ≤ (|a| + |b|) + |c| := by rw [abs_neg]; gcongr; exact abs_add_le _ _
    _ = |a| + |b| + |c| := by ring

/-- **The chart coordinates of the retained arc and of its chord.**  With `W` a bound for the
retained width (through the caller's hypothesis `sweepW' D σ ≤ 2 * W`), `K` a bound for the
acceleration, and the window data supplied as hypotheses, the `v`-coordinate of the arc (resp. the
chord) at fraction `ξ`, relative to the chart centre `chartC`, is `(ξ - 1/2) * ℓ` up to `2 W² K`,
and its `chartE`-coordinate is bounded by `2 W² K`. -/
theorem sweep_chart_bounds {r : ℝ → Space} {d : BandArcData} {D : SweepData d}
    {lam δ₁ δ₂ ε σ ξ K W : ℝ} {v : Space}
    (hv : ‖v‖ = 1) (hK : 0 ≤ K) (hW : 0 ≤ W) (hξ : ξ ∈ Set.Icc (0 : ℝ) 1)
    (hCv : chordEndB r D δ₂ ε - chordEndA r D δ₂ ε
        = ‖chordEndB r D δ₂ ε - chordEndA r D δ₂ ε‖ • v)
    (hWc : ‖(r (tbR D σ) - r (taR D σ)) - (chordEndB r D δ₂ ε - chordEndA r D δ₂ ε)‖
        ≤ W ^ 2 * K / 8)
    (hAc : ‖r (taR D σ) - chordEndA r D δ₂ ε‖ ≤ W ^ 2 * K / 8)
    (hbase : |inner ℝ (shiftedNeedle r D lam δ₁ δ₂ ε 0 - chordEndA r D δ₂ ε) v
        - ‖chordEndB r D δ₂ ε - chordEndA r D δ₂ ε‖ / 2| ≤ W ^ 2 * K / 2)
    (hup : ‖chartUp r D lam δ₁ δ₂ ε v‖ ≤ W ^ 2 * K)
    (hdevv : |inner ℝ (loopDev r D σ ξ) v| ≤ W ^ 2 * K / 2)
    (hdeve : |inner ℝ (loopDev r D σ ξ) (chartE r D lam δ₁ δ₂ ε v)| ≤ W ^ 2 * K / 2) :
    |inner ℝ (sweepArc' r D σ ξ - chartC r D lam δ₁ δ₂ ε v) v
        - (ξ - 1 / 2) * ‖chordEndB r D δ₂ ε - chordEndA r D δ₂ ε‖| ≤ 2 * W ^ 2 * K ∧
    |inner ℝ (sweepArc' r D σ ξ - chartC r D lam δ₁ δ₂ ε v) (chartE r D lam δ₁ δ₂ ε v)|
        ≤ 2 * W ^ 2 * K ∧
    |inner ℝ (sweepChord' r D σ ξ - chartC r D lam δ₁ δ₂ ε v) v
        - (ξ - 1 / 2) * ‖chordEndB r D δ₂ ε - chordEndA r D δ₂ ε‖| ≤ 2 * W ^ 2 * K ∧
    |inner ℝ (sweepChord' r D σ ξ - chartC r D lam δ₁ δ₂ ε v) (chartE r D lam δ₁ δ₂ ε v)|
        ≤ 2 * W ^ 2 * K := by
  have hv1 : inner ℝ v v = 1 := by rw [real_inner_self_eq_norm_sq, hv]; norm_num
  have hCbv : inner ℝ (chordEndB r D δ₂ ε - chordEndA r D δ₂ ε) v
      = ‖chordEndB r D δ₂ ε - chordEndA r D δ₂ ε‖ := by
    rw [hCv, real_inner_smul_left, hv1, mul_one, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (norm_nonneg _), hv, mul_one]
  have hev : inner ℝ (chartE r D lam δ₁ δ₂ ε v) v = 0 :=
    chartE_inner_v (r := r) (D := D) (lam := lam) (δ₁ := δ₁) (δ₂ := δ₂) (ε := ε) hv
  have hve : inner ℝ v (chartE r D lam δ₁ δ₂ ε v) = 0 := by
    rw [real_inner_comm]; exact hev
  have hCbe : inner ℝ (chordEndB r D δ₂ ε - chordEndA r D δ₂ ε) (chartE r D lam δ₁ δ₂ ε v) = 0 := by
    rw [hCv, real_inner_smul_left, hve, mul_zero]
  have hW8 : 0 ≤ W ^ 2 * K / 8 := by positivity
  have hW2 : 0 ≤ W ^ 2 * K / 2 := by positivity
  have hWfull : 0 ≤ W ^ 2 * K := by positivity
  -- the four elementary pairings
  have hPv : |inner ℝ (r (taR D σ) - chordEndA r D δ₂ ε) v| ≤ W ^ 2 * K / 8 := by
    refine le_trans (abs_real_inner_le_norm _ _) ?_
    rw [hv, mul_one]; exact hAc
  have hPe : |inner ℝ (r (taR D σ) - chordEndA r D δ₂ ε) (chartE r D lam δ₁ δ₂ ε v)|
      ≤ W ^ 2 * K / 8 := by
    refine le_trans (abs_real_inner_le_norm _ _) ?_
    calc ‖r (taR D σ) - chordEndA r D δ₂ ε‖ * ‖chartE r D lam δ₁ δ₂ ε v‖
        ≤ (W ^ 2 * K / 8) * 1 :=
          mul_le_mul hAc (chartE_norm_le_one r D lam δ₁ δ₂ ε v) (norm_nonneg _) (by positivity)
      _ = W ^ 2 * K / 8 := by ring
  have hQv : |inner ℝ (r (tbR D σ) - r (taR D σ)) v
      - ‖chordEndB r D δ₂ ε - chordEndA r D δ₂ ε‖| ≤ W ^ 2 * K / 8 := by
    have h1 : inner ℝ (r (tbR D σ) - r (taR D σ)) v
        - ‖chordEndB r D δ₂ ε - chordEndA r D δ₂ ε‖
        = inner ℝ ((r (tbR D σ) - r (taR D σ)) - (chordEndB r D δ₂ ε - chordEndA r D δ₂ ε)) v := by
      simp only [inner_sub_left, hCbv]
    rw [h1]
    refine le_trans (abs_real_inner_le_norm _ _) ?_
    rw [hv, mul_one]; exact hWc
  have hQe : |inner ℝ (r (tbR D σ) - r (taR D σ)) (chartE r D lam δ₁ δ₂ ε v)|
      ≤ W ^ 2 * K / 8 := by
    have h1 : inner ℝ (r (tbR D σ) - r (taR D σ)) (chartE r D lam δ₁ δ₂ ε v)
        = inner ℝ ((r (tbR D σ) - r (taR D σ)) - (chordEndB r D δ₂ ε - chordEndA r D δ₂ ε))
            (chartE r D lam δ₁ δ₂ ε v) := by
      simp only [inner_sub_left, hCbe, sub_zero]
    rw [h1]
    refine le_trans (abs_real_inner_le_norm _ _) ?_
    calc ‖(r (tbR D σ) - r (taR D σ)) - (chordEndB r D δ₂ ε - chordEndA r D δ₂ ε)‖
          * ‖chartE r D lam δ₁ δ₂ ε v‖
        ≤ (W ^ 2 * K / 8) * 1 :=
          mul_le_mul hWc (chartE_norm_le_one r D lam δ₁ δ₂ ε v) (norm_nonneg _) (by positivity)
      _ = W ^ 2 * K / 8 := by ring
  -- the vector decomposition of the arc point relative to the chart centre
  have hch : sweepChord' r D σ ξ
      = r (taR D σ) + ξ • (r (tbR D σ) - r (taR D σ)) := by
    rw [sweepChord', sub_smul, one_smul, smul_sub]; abel
  have hVeq : sweepArc' r D σ ξ - chartC r D lam δ₁ δ₂ ε v
      = loopDev r D σ ξ + (r (taR D σ) - chordEndA r D δ₂ ε)
        + ξ • (r (tbR D σ) - r (taR D σ))
        - (nCoord r D lam δ₁ δ₂ ε v 0) • v
        - (‖chartUp r D lam δ₁ δ₂ ε v‖ / 2) • chartE r D lam δ₁ δ₂ ε v := by
    have hdev : sweepArc' r D σ ξ = loopDev r D σ ξ + sweepChord' r D σ ξ := by
      rw [loopDev, sweepChord', sweepArc']; abel
    rw [hdev, hch, chartC]
    abel
  have hVeqC : sweepChord' r D σ ξ - chartC r D lam δ₁ δ₂ ε v
      = (r (taR D σ) - chordEndA r D δ₂ ε) + ξ • (r (tbR D σ) - r (taR D σ))
        - (nCoord r D lam δ₁ δ₂ ε v 0) • v
        - (‖chartUp r D lam δ₁ δ₂ ε v‖ / 2) • chartE r D lam δ₁ δ₂ ε v := by
    rw [hch, chartC]
    abel
  -- the scalar identities
  have hident : inner ℝ (sweepArc' r D σ ξ - chartC r D lam δ₁ δ₂ ε v) v
        - (ξ - 1 / 2) * ‖chordEndB r D δ₂ ε - chordEndA r D δ₂ ε‖
      = ξ * (inner ℝ (r (tbR D σ) - r (taR D σ)) v
            - ‖chordEndB r D δ₂ ε - chordEndA r D δ₂ ε‖)
        + inner ℝ (loopDev r D σ ξ) v
        + inner ℝ (r (taR D σ) - chordEndA r D δ₂ ε) v
        - (inner ℝ (shiftedNeedle r D lam δ₁ δ₂ ε 0 - chordEndA r D δ₂ ε) v
            - ‖chordEndB r D δ₂ ε - chordEndA r D δ₂ ε‖ / 2) := by
    simp only [hVeq, inner_sub_left, inner_add_left, real_inner_smul_left, hv1, hev, mul_one,
      mul_zero, sub_zero, nCoord]
    ring
  have hidentC : inner ℝ (sweepChord' r D σ ξ - chartC r D lam δ₁ δ₂ ε v) v
        - (ξ - 1 / 2) * ‖chordEndB r D δ₂ ε - chordEndA r D δ₂ ε‖
      = ξ * (inner ℝ (r (tbR D σ) - r (taR D σ)) v
            - ‖chordEndB r D δ₂ ε - chordEndA r D δ₂ ε‖)
        + inner ℝ (r (taR D σ) - chordEndA r D δ₂ ε) v
        - (inner ℝ (shiftedNeedle r D lam δ₁ δ₂ ε 0 - chordEndA r D δ₂ ε) v
            - ‖chordEndB r D δ₂ ε - chordEndA r D δ₂ ε‖ / 2) := by
    simp only [hVeqC, inner_sub_left, inner_add_left, real_inner_smul_left, hv1, hev, mul_one,
      mul_zero, sub_zero, nCoord]
    ring
  have hidentE : inner ℝ (sweepArc' r D σ ξ - chartC r D lam δ₁ δ₂ ε v)
        (chartE r D lam δ₁ δ₂ ε v)
      = inner ℝ (loopDev r D σ ξ) (chartE r D lam δ₁ δ₂ ε v)
        + inner ℝ (r (taR D σ) - chordEndA r D δ₂ ε) (chartE r D lam δ₁ δ₂ ε v)
        + ξ * inner ℝ (r (tbR D σ) - r (taR D σ)) (chartE r D lam δ₁ δ₂ ε v)
        - ‖chartUp r D lam δ₁ δ₂ ε v‖ / 2 := by
    simp only [hVeq, inner_sub_left, inner_add_left, real_inner_smul_left, hve, mul_zero, sub_zero,
      real_inner_self_eq_norm_sq, chartE_norm_sq_mul]
  have hidentEC : inner ℝ (sweepChord' r D σ ξ - chartC r D lam δ₁ δ₂ ε v)
        (chartE r D lam δ₁ δ₂ ε v)
      = inner ℝ (r (taR D σ) - chordEndA r D δ₂ ε) (chartE r D lam δ₁ δ₂ ε v)
        + ξ * inner ℝ (r (tbR D σ) - r (taR D σ)) (chartE r D lam δ₁ δ₂ ε v)
        - ‖chartUp r D lam δ₁ δ₂ ε v‖ / 2 := by
    simp only [hVeqC, inner_sub_left, inner_add_left, real_inner_smul_left, hve, mul_zero, sub_zero,
      real_inner_self_eq_norm_sq, chartE_norm_sq_mul]
  have hξabs : |ξ| ≤ 1 := by rw [abs_of_nonneg hξ.1]; exact hξ.2
  have hξQ : |ξ * (inner ℝ (r (tbR D σ) - r (taR D σ)) v
      - ‖chordEndB r D δ₂ ε - chordEndA r D δ₂ ε‖)| ≤ W ^ 2 * K / 8 := by
    rw [abs_mul]
    exact (mul_le_mul hξabs hQv (abs_nonneg _) (by norm_num)).trans_eq (one_mul _)
  have hξQe : |ξ * inner ℝ (r (tbR D σ) - r (taR D σ)) (chartE r D lam δ₁ δ₂ ε v)|
      ≤ W ^ 2 * K / 8 := by
    rw [abs_mul]
    exact (mul_le_mul hξabs hQe (abs_nonneg _) (by norm_num)).trans_eq (one_mul _)
  have hup2 : |‖chartUp r D lam δ₁ δ₂ ε v‖ / 2| ≤ W ^ 2 * K / 2 := by
    rw [abs_of_nonneg (by positivity)]
    linarith [hup]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hident]
    refine (abs_add_sub_le_four _ _ _ _).trans ?_
    have h4 : |inner ℝ (shiftedNeedle r D lam δ₁ δ₂ ε 0 - chordEndA r D δ₂ ε) v
        - ‖chordEndB r D δ₂ ε - chordEndA r D δ₂ ε‖ / 2| ≤ W ^ 2 * K / 2 := hbase
    linarith [hξQ, hdevv, hPv, h4]
  · rw [hidentE]
    refine (abs_add_sub_le_four _ _ _ _).trans ?_
    linarith [hξQe, hdeve, hPe, hup2]
  · rw [hidentC]
    refine (abs_add_sub_le_three _ _ _).trans ?_
    have h4 : |inner ℝ (shiftedNeedle r D lam δ₁ δ₂ ε 0 - chordEndA r D δ₂ ε) v
        - ‖chordEndB r D δ₂ ε - chordEndA r D δ₂ ε‖ / 2| ≤ W ^ 2 * K / 2 := hbase
    linarith [hξQ, hPv, h4]
  · rw [hidentEC]
    refine (abs_add_sub_le_three _ _ _).trans ?_
    linarith [hξQe, hPe, hup2]

/-! ## The target -/

theorem chamfer_pos_data {r : ℝ → LeanEval.KnotTheory.Quadrisecant.Space}
    (hr : LeanEval.KnotTheory.Quadrisecant.IsSmoothKnot r)
    (hinfl : ∀ t : ℝ, LinearIndependent ℝ ![deriv r t, deriv (deriv r) t])
    {d : LeanEval.KnotTheory.Quadrisecant.BandArcData} (D : Work.Drive.SweepData d) :
    ∃ C : ℝ, 0 < C ∧ ∃ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ ≤ 1 / 2 ∧ ∀ ε : ℝ, 0 < ε → ε ≤ ε₀ →
      ∃ Λ : ℝ, 0 < Λ ∧ Λ ≤ 1 / 4 ∧
        ∀ lam δ₁ δ₂ : ℝ, 0 < lam → lam ≤ Λ → lam < 1 / 2 → 0 < δ₁ → δ₁ ≤ Λ →
          0 < δ₂ → δ₂ ≤ Λ → δ₂ ≤ ε / 2 →
        ∀ v : LeanEval.KnotTheory.Quadrisecant.Space, ‖v‖ = 1 →
          Work.Drive.chordEndB r D δ₂ ε - Work.Drive.chordEndA r D δ₂ ε
            = ‖Work.Drive.chordEndB r D δ₂ ε - Work.Drive.chordEndA r D δ₂ ε‖ • v →
        ∀ σ : ℝ, ε - δ₂ ≤ σ → σ ≤ ε + δ₂ →
          (∀ t : ℝ, 1 / 2 < Work.Drive.sweepParam t →
            Work.Drive.sweepParam t ≤ 1 / 2 + lam / 2 →
            (1 / 4) * (1 / 2 - lam)
                * ‖Work.Drive.chordEndB r D δ₂ ε - Work.Drive.chordEndA r D δ₂ ε‖
              ≤ inner ℝ (Work.Drive.sweepLoopChamfer r D lam σ t
                    - Work.Drive.chartC r D lam δ₁ δ₂ ε v) v ∧
            |inner ℝ (Work.Drive.sweepLoopChamfer r D lam σ t
                  - Work.Drive.chartC r D lam δ₁ δ₂ ε v)
                (Work.Drive.chartE r D lam δ₁ δ₂ ε v)|
              ≤ C * (Work.Drive.sweepW' D ε) ^ 2) ∧
          (∀ t : ℝ, 1 - lam / 2 < Work.Drive.sweepParam t →
            inner ℝ (Work.Drive.sweepLoopChamfer r D lam σ t
                  - Work.Drive.chartC r D lam δ₁ δ₂ ε v) v
              ≤ -(1 / 4) * (1 / 2 - lam)
                * ‖Work.Drive.chordEndB r D δ₂ ε - Work.Drive.chordEndA r D δ₂ ε‖ ∧
            |inner ℝ (Work.Drive.sweepLoopChamfer r D lam σ t
                  - Work.Drive.chartC r D lam δ₁ δ₂ ε v)
                (Work.Drive.chartE r D lam δ₁ δ₂ ε v)|
              ≤ C * (Work.Drive.sweepW' D ε) ^ 2) := by
  obtain ⟨K, hK1, hKb⟩ := H2_accel_bound hr
  have hK0 : 0 < K := lt_of_lt_of_le zero_lt_one hK1
  obtain ⟨εL, hεL0, hεL1, cL, hcL0, hcL⟩ := chordLen_lower (r := r) (D := D) hr
  obtain ⟨εB, hεB0, hεB⟩ := Generic.nclm_blur_close_scale hr D (K / 8) (by linarith)
  set η : ℝ := min 1 (cL / (32 * K)) with hη
  have hη0 : 0 < η := lt_min one_pos (by positivity)
  have hηc : η ≤ cL / (32 * K) := min_le_right _ _
  obtain ⟨εW, hεW0, hεW1, hεW⟩ := windowDataSmall hr D (η / 2) (by positivity)
  set E0 : ℝ := min (min (min εL εW) εB) (1 / 4) with hE0
  have hE0L : E0 ≤ εL := le_trans (min_le_left _ _) (le_trans (min_le_left _ _) (min_le_left _ _))
  have hE0W : E0 ≤ εW := le_trans (min_le_left _ _) (le_trans (min_le_left _ _) (min_le_right _ _))
  have hE0B : E0 ≤ εB := le_trans (min_le_left _ _) (min_le_right _ _)
  have hE014 : E0 ≤ 1 / 4 := min_le_right _ _
  refine ⟨3 * K, by positivity, E0, lt_min (lt_min (lt_min hεL0 hεW0) hεB0) (by norm_num),
    by linarith, ?_⟩
  intro ε hε0 hεE0
  have hεL' : ε ≤ εL := le_trans hεE0 hE0L
  have hεW' : ε ≤ εW := le_trans hεE0 hE0W
  have hεB' : ε ≤ εB := le_trans hεE0 hE0B
  have hε14 : ε ≤ 1 / 4 := le_trans hεE0 hE014
  have hε12 : ε ≤ 1 / 2 := by linarith
  have hε1 : ε < 1 := by linarith
  have hWpos : 0 < sweepW' D ε := wds_sweepW'_pos D hε0 hε1
  have hWsmall : sweepW' D ε ≤ η := by
    obtain ⟨hwin, -, -⟩ := hεW (ε / 2) ε (by linarith) le_rfl hε0 hεW'
    have h0 := hwin ε (by linarith) (by linarith) 0 (by norm_num) (by norm_num)
    have h1 := hwin ε (by linarith) (by linarith) 1 (by norm_num) (by norm_num)
    simp only [zero_mul, one_mul, add_zero] at h0 h1
    have htb : taR D ε + sweepW' D ε = tbR D ε := by rw [sweepW']; ring
    rw [htb] at h1
    have ha : -(η / 2) ≤ taR D ε - taR D 0 := (abs_le.mp h0).1
    have hb : tbR D ε - taR D 0 ≤ η / 2 := (abs_le.mp h1).2
    have hkey : sweepW' D ε = (tbR D ε - taR D 0) - (taR D ε - taR D 0) := by rw [sweepW']; ring
    rw [hkey]; linarith
  obtain ⟨Λc, hΛc0, hΛc⟩ := hεB ε hε0 hεB'
  obtain ⟨Λw, hΛw0, hΛw⟩ := Generic.nclm_window_eps (D := D) hε0 hε1
  obtain ⟨ΛL, hΛL0, hΛLε, hΛL⟩ := hcL ε hε0 hεL'
  set Λ : ℝ := min (min (min (min Λc Λw) ΛL) (period / 16)) (1 / 4) with hΛ
  have hΛc_le : Λ ≤ Λc :=
    le_trans (min_le_left _ _) (le_trans (min_le_left _ _) (le_trans (min_le_left _ _) (min_le_left _ _)))
  have hΛw_le : Λ ≤ Λw :=
    le_trans (min_le_left _ _) (le_trans (min_le_left _ _) (le_trans (min_le_left _ _) (min_le_right _ _)))
  have hΛL_le : Λ ≤ ΛL :=
    le_trans (min_le_left _ _) (le_trans (min_le_left _ _) (min_le_right _ _))
  have hΛp_le : Λ ≤ period / 16 := le_trans (min_le_left _ _) (min_le_right _ _)
  have hΛ14 : Λ ≤ 1 / 4 := min_le_right _ _
  refine ⟨Λ, ?_, hΛ14, ?_⟩
  · rw [hΛ]
    exact lt_min (lt_min (lt_min (lt_min hΛc0 hΛw0) hΛL0) (by linarith [period_pos])) (by norm_num)
  intro lam δ₁ δ₂ hlam0 hlamΛ hlam12 hδ₁0 hδ₁Λ hδ₂0 hδ₂Λ hδ₂ε
  have hδ₂Λc : δ₂ ≤ Λc := le_trans hδ₂Λ hΛc_le
  have hδ₂Λw : δ₂ ≤ Λw := le_trans hδ₂Λ hΛw_le
  have hδ₂ΛL : δ₂ ≤ ΛL := le_trans hδ₂Λ hΛL_le
  have hδ₁16 : δ₁ ≤ period / 16 := le_trans hδ₁Λ hΛp_le
  have hδ₁4 : δ₁ ≤ period / 4 := by linarith [period_pos]
  have hlam0le : 0 ≤ lam := hlam0.le
  have hlam14 : lam ≤ 1 / 4 := le_trans hlamΛ hΛ14
  have hWσ2 : ∀ σ' : ℝ, ε - δ₂ ≤ σ' → σ' ≤ ε + δ₂ → sweepW' D σ' ≤ 2 * sweepW' D ε :=
    fun σ' h1 h2 => (hΛw δ₂ σ' hδ₂0 hδ₂Λw hδ₂ε h1 h2).2.1
  intro v hv hvC
  set Cb : Space := chordEndB r D δ₂ ε - chordEndA r D δ₂ ε with hCb
  set ℓ : ℝ := ‖Cb‖ with hℓ
  have hℓc : cL * sweepW' D ε ≤ ℓ := by
    rw [hℓ, hCb]; exact hΛL δ₂ hδ₂0 hδ₂ΛL
  have hℓge : 32 * K * (sweepW' D ε) ^ 2 ≤ ℓ := by
    have h2 : 32 * K * sweepW' D ε ≤ cL := by
      have h3 : sweepW' D ε ≤ cL / (32 * K) := le_trans hWsmall hηc
      rw [le_div_iff₀ (by positivity : (0 : ℝ) < 32 * K)] at h3
      linarith
    calc 32 * K * (sweepW' D ε) ^ 2 = (32 * K * sweepW' D ε) * sweepW' D ε := by ring
      _ ≤ cL * sweepW' D ε := mul_le_mul_of_nonneg_right h2 hWpos.le
      _ ≤ ℓ := hℓc
  have hstep : 2 * (sweepW' D ε) ^ 2 * K ≤ (3 / 4) * (1 / 2 - lam) * ℓ := by
    have h1 : 2 * (sweepW' D ε) ^ 2 * K ≤ (1 / 16) * ℓ := by nlinarith [hℓge]
    have h2 : (1 / 16 : ℝ) * ℓ ≤ (3 / 4) * (1 / 2 - lam) * ℓ := by
      have h3 : (1 / 16 : ℝ) ≤ (3 / 4) * (1 / 2 - lam) := by linarith
      exact mul_le_mul_of_nonneg_right h3 (norm_nonneg _)
    linarith [h1, h2]
  have hbase := basePoint_v_coord (r := r) (D := D) hr hK0.le hWpos.le hlam0le hlam12 hδ₁0
    hδ₁4 hδ₂0 hδ₂ε hε0 hε12 hv hKb hWσ2 hvC
  have hup := chartUp_norm_bound (r := r) (D := D) hr hK0.le hWpos.le hlam0le hlam12 hδ₁0
    hδ₁4 hδ₂0 hδ₂ε hε0 hε12 hv hKb hWσ2 hvC
  intro σ hσlo hσhi
  have hWσpos : 0 < sweepW' D σ := Generic.nclm_window_wpos D hδ₂0 hδ₂ε hε0 hε12 hσlo hσhi
  obtain ⟨hclA, -, hclC, -⟩ := hΛc δ₂ σ hδ₂0 hδ₂Λc hδ₂ε hσlo hσhi
  have hAc : ‖r (taR D σ) - chordEndA r D δ₂ ε‖ ≤ (sweepW' D ε) ^ 2 * K / 8 :=
    hclA.trans (le_of_eq (by ring))
  have hWc : ‖(r (tbR D σ) - r (taR D σ)) - Cb‖ ≤ (sweepW' D ε) ^ 2 * K / 8 := by
    rw [hCb]; exact hclC.trans (le_of_eq (by ring))
  have hdevv : ∀ ξ ∈ Set.Icc (0 : ℝ) 1,
      |inner ℝ (loopDev r D σ ξ) v| ≤ (sweepW' D ε) ^ 2 * K / 2 := by
    intro ξ hξ
    have h1 := Generic.nclm_dev_scalar_le (D := D) hr hWσpos hξ (y := v) (B := K) (fun x hx => by
      calc |inner ℝ (deriv (deriv r) x) v| ≤ ‖deriv (deriv r) x‖ * ‖v‖ := abs_real_inner_le_norm _ _
        _ = ‖deriv (deriv r) x‖ := by rw [hv, mul_one]
        _ ≤ K := hKb x)
    have hfac : ξ * (1 - ξ) / 2 ≤ 1 / 8 := by nlinarith [sq_nonneg (ξ - 1 / 2)]
    have hWs : (sweepW' D σ) ^ 2 ≤ 4 * (sweepW' D ε) ^ 2 := by nlinarith [hWσ2 σ hσlo hσhi, hWpos.le]
    calc |inner ℝ (loopDev r D σ ξ) v|
        ≤ ξ * (1 - ξ) / 2 * (sweepW' D σ) ^ 2 * K := h1
      _ ≤ (1 / 8) * (4 * (sweepW' D ε) ^ 2) * K := by gcongr
      _ = (sweepW' D ε) ^ 2 * K / 2 := by ring
  have hdeve : ∀ ξ ∈ Set.Icc (0 : ℝ) 1,
      |inner ℝ (loopDev r D σ ξ) (chartE r D lam δ₁ δ₂ ε v)| ≤ (sweepW' D ε) ^ 2 * K / 2 := by
    intro ξ hξ
    have h1 := Generic.nclm_dev_scalar_le (D := D) hr hWσpos hξ (y := chartE r D lam δ₁ δ₂ ε v) (B := K)
      (fun x hx => by
        calc |inner ℝ (deriv (deriv r) x) (chartE r D lam δ₁ δ₂ ε v)|
            ≤ ‖deriv (deriv r) x‖ * ‖chartE r D lam δ₁ δ₂ ε v‖ := abs_real_inner_le_norm _ _
          _ ≤ K * 1 := mul_le_mul (hKb x) (chartE_norm_le_one r D lam δ₁ δ₂ ε v) (norm_nonneg _) hK0.le
          _ = K := mul_one K)
    have hfac : ξ * (1 - ξ) / 2 ≤ 1 / 8 := by nlinarith [sq_nonneg (ξ - 1 / 2)]
    have hWs : (sweepW' D σ) ^ 2 ≤ 4 * (sweepW' D ε) ^ 2 := by nlinarith [hWσ2 σ hσlo hσhi, hWpos.le]
    calc |inner ℝ (loopDev r D σ ξ) (chartE r D lam δ₁ δ₂ ε v)|
        ≤ ξ * (1 - ξ) / 2 * (sweepW' D σ) ^ 2 * K := h1
      _ ≤ (1 / 8) * (4 * (sweepW' D ε) ^ 2) * K := by gcongr
      _ = (sweepW' D ε) ^ 2 * K / 2 := by ring
  refine ⟨?_, ?_⟩
  · intro t ht1 ht2
    set sf : ℝ := (2 * sweepParam t - 1) / lam with hsf
    have hs0 : 0 ≤ sf := by rw [hsf]; exact div_nonneg (by linarith) hlam0.le
    have hs1 : sf ≤ 1 := by rw [hsf, div_le_one hlam0]; linarith
    have hΓ : sweepLoopChamfer r D lam σ t
        = (1 - sf) • sweepArc' r D σ (1 - lam) + sf • sweepChord' r D σ (1 - lam) := by
      rw [sweepLoopChamfer, if_neg (by linarith), if_pos ht2, ← hsf]
    have hξ1 : (1 - lam) ∈ Set.Icc (0 : ℝ) 1 := ⟨by linarith, by linarith⟩
    obtain ⟨hAv, hAe, hCvv, hCe⟩ := sweep_chart_bounds (r := r) (D := D) (lam := lam) (δ₁ := δ₁)
      (δ₂ := δ₂) (ε := ε) (σ := σ) (ξ := 1 - lam) (K := K) (W := sweepW' D ε) hv hK0.le hWpos.le
      hξ1 hvC hWc hAc hbase hup (hdevv (1 - lam) hξ1) (hdeve (1 - lam) hξ1)
    have hlin : inner ℝ (sweepLoopChamfer r D lam σ t - chartC r D lam δ₁ δ₂ ε v) v
        = (1 - sf) * inner ℝ (sweepArc' r D σ (1 - lam) - chartC r D lam δ₁ δ₂ ε v) v
          + sf * inner ℝ (sweepChord' r D σ (1 - lam) - chartC r D lam δ₁ δ₂ ε v) v := by
      rw [hΓ]
      simp only [inner_sub_left, inner_add_left, real_inner_smul_left]
      ring
    have hlinE : inner ℝ (sweepLoopChamfer r D lam σ t - chartC r D lam δ₁ δ₂ ε v)
          (chartE r D lam δ₁ δ₂ ε v)
        = (1 - sf) * inner ℝ (sweepArc' r D σ (1 - lam) - chartC r D lam δ₁ δ₂ ε v)
              (chartE r D lam δ₁ δ₂ ε v)
          + sf * inner ℝ (sweepChord' r D σ (1 - lam) - chartC r D lam δ₁ δ₂ ε v)
              (chartE r D lam δ₁ δ₂ ε v) := by
      rw [hΓ]
      simp only [inner_sub_left, inner_add_left, real_inner_smul_left]
      ring
    refine ⟨?_, ?_⟩
    · rw [hlin]
      have hA' : (1 / 2 - lam) * ℓ - 2 * (sweepW' D ε) ^ 2 * K
          ≤ inner ℝ (sweepArc' r D σ (1 - lam) - chartC r D lam δ₁ δ₂ ε v) v := by
        have h := (abs_le.mp hAv).1
        rw [← hCb, ← hℓ] at h
        have h2 : (1 - lam - 1 / 2) * ℓ = (1 / 2 - lam) * ℓ := by ring
        rw [h2] at h
        linarith
      have hC' : (1 / 2 - lam) * ℓ - 2 * (sweepW' D ε) ^ 2 * K
          ≤ inner ℝ (sweepChord' r D σ (1 - lam) - chartC r D lam δ₁ δ₂ ε v) v := by
        have h := (abs_le.mp hCvv).1
        rw [← hCb, ← hℓ] at h
        have h2 : (1 - lam - 1 / 2) * ℓ = (1 / 2 - lam) * ℓ := by ring
        rw [h2] at h
        linarith
      have h1 := mul_le_mul_of_nonneg_left hA' (by linarith : (0 : ℝ) ≤ 1 - sf)
      have h2 := mul_le_mul_of_nonneg_left hC' hs0
      have h3 : (1 - sf) * ((1 / 2 - lam) * ℓ - 2 * (sweepW' D ε) ^ 2 * K)
            + sf * ((1 / 2 - lam) * ℓ - 2 * (sweepW' D ε) ^ 2 * K)
          = (1 / 2 - lam) * ℓ - 2 * (sweepW' D ε) ^ 2 * K := by ring
      have hgoal : (1 / 4) * (1 / 2 - lam) * ℓ
          ≤ (1 / 2 - lam) * ℓ - 2 * (sweepW' D ε) ^ 2 * K := by linarith [hstep]
      linarith [h1, h2, h3, hgoal]
    · rw [hlinE]
      have htri : |(1 - sf) * inner ℝ (sweepArc' r D σ (1 - lam) - chartC r D lam δ₁ δ₂ ε v)
              (chartE r D lam δ₁ δ₂ ε v)
            + sf * inner ℝ (sweepChord' r D σ (1 - lam) - chartC r D lam δ₁ δ₂ ε v)
              (chartE r D lam δ₁ δ₂ ε v)|
          ≤ 3 * K * (sweepW' D ε) ^ 2 := by
        have h1 : |(1 - sf) * inner ℝ (sweepArc' r D σ (1 - lam) - chartC r D lam δ₁ δ₂ ε v)
              (chartE r D lam δ₁ δ₂ ε v)
            + sf * inner ℝ (sweepChord' r D σ (1 - lam) - chartC r D lam δ₁ δ₂ ε v)
              (chartE r D lam δ₁ δ₂ ε v)|
            ≤ |(1 - sf) * inner ℝ (sweepArc' r D σ (1 - lam) - chartC r D lam δ₁ δ₂ ε v)
                (chartE r D lam δ₁ δ₂ ε v)|
              + |sf * inner ℝ (sweepChord' r D σ (1 - lam) - chartC r D lam δ₁ δ₂ ε v)
                (chartE r D lam δ₁ δ₂ ε v)| := abs_add_le _ _
        have h2 : |(1 - sf) * inner ℝ (sweepArc' r D σ (1 - lam) - chartC r D lam δ₁ δ₂ ε v)
              (chartE r D lam δ₁ δ₂ ε v)|
            ≤ (1 - sf) * (2 * (sweepW' D ε) ^ 2 * K) := by
          rw [abs_mul, abs_of_nonneg (by linarith : (0 : ℝ) ≤ 1 - sf)]
          exact mul_le_mul_of_nonneg_left hAe (by linarith)
        have h3 : |sf * inner ℝ (sweepChord' r D σ (1 - lam) - chartC r D lam δ₁ δ₂ ε v)
              (chartE r D lam δ₁ δ₂ ε v)|
            ≤ sf * (2 * (sweepW' D ε) ^ 2 * K) := by
          rw [abs_mul, abs_of_nonneg hs0]
          exact mul_le_mul_of_nonneg_left hCe hs0
        have h4 : (1 - sf) * (2 * (sweepW' D ε) ^ 2 * K) + sf * (2 * (sweepW' D ε) ^ 2 * K)
            = 2 * (sweepW' D ε) ^ 2 * K := by ring
        have h5 : 2 * (sweepW' D ε) ^ 2 * K ≤ 3 * K * (sweepW' D ε) ^ 2 := by
          nlinarith [sq_nonneg (sweepW' D ε), hK0.le]
        linarith [h1, h2, h3, h4, h5]
      exact htri
  · intro t ht
    set sf : ℝ := (sweepParam t - (1 - lam / 2)) / (lam / 2) with hsf
    have hl2pos : 0 < lam / 2 := by linarith
    have hs0 : 0 ≤ sf := by rw [hsf]; exact div_nonneg (by linarith) hl2pos.le
    have hs1 : sf ≤ 1 := by
      rw [hsf, div_le_one hl2pos]
      have := (sweepParam_mem t).2
      linarith
    have hΓ : sweepLoopChamfer r D lam σ t
        = (1 - sf) • sweepChord' r D σ lam + sf • sweepArc' r D σ lam := by
      rw [sweepLoopChamfer, if_neg (by linarith), if_neg (by linarith), if_neg (by linarith), ← hsf]
    have hξl : lam ∈ Set.Icc (0 : ℝ) 1 := ⟨hlam0.le, by linarith⟩
    obtain ⟨hAv, hAe, hCvv, hCe⟩ := sweep_chart_bounds (r := r) (D := D) (lam := lam) (δ₁ := δ₁)
      (δ₂ := δ₂) (ε := ε) (σ := σ) (ξ := lam) (K := K) (W := sweepW' D ε) hv hK0.le hWpos.le
      hξl hvC hWc hAc hbase hup (hdevv lam hξl) (hdeve lam hξl)
    have hlin : inner ℝ (sweepLoopChamfer r D lam σ t - chartC r D lam δ₁ δ₂ ε v) v
        = (1 - sf) * inner ℝ (sweepChord' r D σ lam - chartC r D lam δ₁ δ₂ ε v) v
          + sf * inner ℝ (sweepArc' r D σ lam - chartC r D lam δ₁ δ₂ ε v) v := by
      rw [hΓ]
      simp only [inner_sub_left, inner_add_left, real_inner_smul_left]
      ring
    have hlinE : inner ℝ (sweepLoopChamfer r D lam σ t - chartC r D lam δ₁ δ₂ ε v)
          (chartE r D lam δ₁ δ₂ ε v)
        = (1 - sf) * inner ℝ (sweepChord' r D σ lam - chartC r D lam δ₁ δ₂ ε v)
              (chartE r D lam δ₁ δ₂ ε v)
          + sf * inner ℝ (sweepArc' r D σ lam - chartC r D lam δ₁ δ₂ ε v)
              (chartE r D lam δ₁ δ₂ ε v) := by
      rw [hΓ]
      simp only [inner_sub_left, inner_add_left, real_inner_smul_left]
      ring
    refine ⟨?_, ?_⟩
    · rw [hlin]
      have hA' : inner ℝ (sweepArc' r D σ lam - chartC r D lam δ₁ δ₂ ε v) v
          ≤ (lam - 1 / 2) * ℓ + 2 * (sweepW' D ε) ^ 2 * K := by
        have h := (abs_le.mp hAv).2
        rw [← hCb, ← hℓ] at h
        linarith
      have hC' : inner ℝ (sweepChord' r D σ lam - chartC r D lam δ₁ δ₂ ε v) v
          ≤ (lam - 1 / 2) * ℓ + 2 * (sweepW' D ε) ^ 2 * K := by
        have h := (abs_le.mp hCvv).2
        rw [← hCb, ← hℓ] at h
        linarith
      have h1 := mul_le_mul_of_nonneg_left hA' hs0
      have h2 := mul_le_mul_of_nonneg_left hC' (by linarith : (0 : ℝ) ≤ 1 - sf)
      have h3 : (1 - sf) * ((lam - 1 / 2) * ℓ + 2 * (sweepW' D ε) ^ 2 * K)
            + sf * ((lam - 1 / 2) * ℓ + 2 * (sweepW' D ε) ^ 2 * K)
          = (lam - 1 / 2) * ℓ + 2 * (sweepW' D ε) ^ 2 * K := by ring
      have hgoal : (lam - 1 / 2) * ℓ + 2 * (sweepW' D ε) ^ 2 * K
          ≤ -(1 / 4) * (1 / 2 - lam) * ℓ := by linarith [hstep]
      linarith [h1, h2, h3, hgoal]
    · rw [hlinE]
      have htri : |(1 - sf) * inner ℝ (sweepChord' r D σ lam - chartC r D lam δ₁ δ₂ ε v)
              (chartE r D lam δ₁ δ₂ ε v)
            + sf * inner ℝ (sweepArc' r D σ lam - chartC r D lam δ₁ δ₂ ε v)
              (chartE r D lam δ₁ δ₂ ε v)|
          ≤ 3 * K * (sweepW' D ε) ^ 2 := by
        have h1 : |(1 - sf) * inner ℝ (sweepChord' r D σ lam - chartC r D lam δ₁ δ₂ ε v)
              (chartE r D lam δ₁ δ₂ ε v)
            + sf * inner ℝ (sweepArc' r D σ lam - chartC r D lam δ₁ δ₂ ε v)
              (chartE r D lam δ₁ δ₂ ε v)|
            ≤ |(1 - sf) * inner ℝ (sweepChord' r D σ lam - chartC r D lam δ₁ δ₂ ε v)
                (chartE r D lam δ₁ δ₂ ε v)|
              + |sf * inner ℝ (sweepArc' r D σ lam - chartC r D lam δ₁ δ₂ ε v)
                (chartE r D lam δ₁ δ₂ ε v)| := abs_add_le _ _
        have h2 : |(1 - sf) * inner ℝ (sweepChord' r D σ lam - chartC r D lam δ₁ δ₂ ε v)
              (chartE r D lam δ₁ δ₂ ε v)|
            ≤ (1 - sf) * (2 * (sweepW' D ε) ^ 2 * K) := by
          rw [abs_mul, abs_of_nonneg (by linarith : (0 : ℝ) ≤ 1 - sf)]
          exact mul_le_mul_of_nonneg_left hCe (by linarith)
        have h3 : |sf * inner ℝ (sweepArc' r D σ lam - chartC r D lam δ₁ δ₂ ε v)
              (chartE r D lam δ₁ δ₂ ε v)|
            ≤ sf * (2 * (sweepW' D ε) ^ 2 * K) := by
          rw [abs_mul, abs_of_nonneg hs0]
          exact mul_le_mul_of_nonneg_left hAe hs0
        have h4 : (1 - sf) * (2 * (sweepW' D ε) ^ 2 * K) + sf * (2 * (sweepW' D ε) ^ 2 * K)
            = 2 * (sweepW' D ε) ^ 2 * K := by ring
        have h5 : 2 * (sweepW' D ε) ^ 2 * K ≤ 3 * K * (sweepW' D ε) ^ 2 := by
          nlinarith [sq_nonneg (sweepW' D ε), hK0.le]
        linarith [h1, h2, h3, h4, h5]
      exact htri

end

end Work.Drive.H2
