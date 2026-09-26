import Mathlib
import Submission.Work.Drive.Generic.nclmBasic
import Submission.Work.Drive.Generic.nclmE0

/-!
# The chart data of the needle's loops

This module collects the quantitative estimates on the chart coordinates of the needle's loops that
the per-loop margin of `Work.Drive.Generic.needleChartLoop_margin` consumes.

The chart is the one of `Work.Drive.chartC` / `Work.Drive.chartE`: the origin is the chart centre,
the abscissa is `v` (the needle's unit chord direction) and the ordinate is `chartE` (the unit "up"
direction, perpendicular to `v`).  For a retained arc at sweep parameter `σ`, the two coordinates of
its point at fraction `ξ` relative to the centre are the functions

* `Work.Drive.Generic.nclmAX r D lam δ₁ δ₂ ε σ v` (abscissa, written `X̃` below),
* `Work.Drive.Generic.nclmAH r D lam δ₁ δ₂ ε σ v` (ordinate, written `H̃` below).

The estimates are:

* `nclm_devw` — the three weakened deviation bounds (`ξ (1-ξ)/2 ≤ 1/8`);
* `nclm_chartUp_bounds` — the three component bounds of `chartUp` (against `e₀`, `b₀`, `T₀`), read
  off the double-average identity `nclm_chartUp_inner`;
* `nclm_chartE_align` — the alignment of `chartE` with `-e₀` that they imply;
* `nclm_accE_bound` — the resulting one-sided bound on the acceleration along `chartE`.

The remaining estimates (positions of the arc's ends, the chord, and the increments of `X̃`) live in
`nclmPos.lean`.
-/

noncomputable section
namespace Work.Drive.Generic

open LeanEval.KnotTheory.Quadrisecant MeasureTheory
open scoped Real Topology intervalIntegral

variable {r : ℝ → Space} {d : BandArcData}

/-- **The three weakened deviation bounds.**  On a retained arc whose accelerations against the
frame directions `-e₀`, `b₀`, `v` are bounded by `cy`, `cb`, `cv`, the corresponding deviations are
bounded by `(ξ (1-ξ)/2) w²` times those constants. -/
theorem nclm_devw {r : ℝ → Space} (hr : IsSmoothKnot r) {d : BandArcData} (D : Work.Drive.SweepData d)
    {σ : ℝ} (hw : 0 < Work.Drive.sweepW' D σ)
    {cy cb cv : ℝ} {v : Space}
    (hy : ∀ x ∈ Set.Icc (Work.Drive.taR D σ) (Work.Drive.tbR D σ),
      inner ℝ (deriv (deriv r) x) (-(nclmE0 r D)) ≤ -cy)
    (hb : ∀ x ∈ Set.Icc (Work.Drive.taR D σ) (Work.Drive.tbR D σ),
      |inner ℝ (deriv (deriv r) x) (nclmB0 r D)| ≤ cb)
    (hv : ∀ x ∈ Set.Icc (Work.Drive.taR D σ) (Work.Drive.tbR D σ),
      |inner ℝ (deriv (deriv r) x) v| ≤ cv)
    {ξ : ℝ} (hξ : ξ ∈ Set.Icc (0 : ℝ) 1) :
    (ξ * (1 - ξ) / 2) * (Work.Drive.sweepW' D σ) ^ 2 * cy
        ≤ inner ℝ (Work.Drive.loopDev r D σ ξ) (-(nclmE0 r D)) ∧
    |inner ℝ (Work.Drive.loopDev r D σ ξ) (nclmB0 r D)|
        ≤ (ξ * (1 - ξ) / 2) * (Work.Drive.sweepW' D σ) ^ 2 * cb ∧
    |inner ℝ (Work.Drive.loopDev r D σ ξ) v|
        ≤ (ξ * (1 - ξ) / 2) * (Work.Drive.sweepW' D σ) ^ 2 * cv :=
  ⟨nclm_dev_scalar_ge D hr hw hξ hy, nclm_dev_scalar_le D hr hw hξ hb,
    nclm_dev_scalar_le D hr hw hξ hv⟩


/-! ## The affine surrogate of the arc fraction -/

/-- The affine surrogate of the arc fraction of the blurred middle: globally continuous, and equal to
`arcFrac lam δ₁ (period / 4)` on the smoothing window `[-1,1]` (see `arcFrac_quarter`). -/
noncomputable def arcFracQ (lam δ₁ u : ℝ) : ℝ := 1 / 2 - (1 - 2 * lam) * (2 * δ₁ / period) * u

lemma arcFrac_quarter_eq {lam δ₁ u : ℝ} (hδ₁0 : 0 < δ₁) (hδ₁4 : δ₁ ≤ period / 4)
    (hu : u ∈ Set.Icc (-1 : ℝ) 1) :
    Work.Drive.arcFrac lam δ₁ (period / 4) u = arcFracQ lam δ₁ u := by
  rw [arcFrac_quarter hδ₁0 hδ₁4 hu, arcFracQ]

lemma arcFracQ_mem {lam δ₁ u : ℝ} (hlam0 : 0 ≤ lam) (hlam1 : lam ≤ 1)
    (hδ₁0 : 0 < δ₁) (hδ₁16 : δ₁ ≤ period / 16) (hu : u ∈ Set.Icc (-1 : ℝ) 1) :
    arcFracQ lam δ₁ u ∈ Set.Icc (1 / 4 : ℝ) (3 / 4) := by
  have hp : 0 < period := period_pos
  have hθ : |(1 - 2 * lam) * (2 * δ₁ / period) * u| ≤ 1 / 4 := by
    have h2 : |(1 : ℝ) - 2 * lam| ≤ 1 := by
      rw [abs_le]; constructor <;> linarith
    have h3 : |2 * δ₁ / period| ≤ 1 / 8 := by
      rw [abs_of_nonneg (by positivity), div_le_iff₀ hp]
      linarith
    have h4 : |u| ≤ 1 := by rw [abs_le]; exact hu
    calc |(1 - 2 * lam) * (2 * δ₁ / period) * u|
        = |1 - 2 * lam| * |2 * δ₁ / period| * |u| := by rw [abs_mul, abs_mul]
      _ ≤ 1 * (1 / 8) * 1 :=
          mul_le_mul (mul_le_mul h2 h3 (abs_nonneg _) zero_le_one) h4 (abs_nonneg _)
            (by norm_num)
      _ = 1 / 8 := by norm_num
    linarith
  have h5 : arcFracQ lam δ₁ u - 1 / 2 = -((1 - 2 * lam) * (2 * δ₁ / period) * u) := by
    rw [arcFracQ]; ring
  have h6 : |arcFracQ lam δ₁ u - 1 / 2| ≤ 1 / 4 := by rw [h5, abs_neg]; exact hθ
  rw [Set.mem_Icc]
  exact ⟨by linarith [abs_le.mp h6 |>.1], by linarith [abs_le.mp h6 |>.2]⟩


/-! ## Continuity of the double-average integrand -/

/-- The integrand of the chart identity is jointly continuous (on the affine surrogate `arcFracQ`). -/
lemma continuous_loopDevQ {r : ℝ → Space} (hr : Continuous r) {d : BandArcData}
    (D : Work.Drive.SweepData d) (lam δ₁ δ₂ ε : ℝ) :
    Continuous (fun p : ℝ × ℝ =>
      Work.Drive.loopDev r D (ε - δ₂ * p.1) (arcFracQ lam δ₁ p.2)) := by
  have hσ : Continuous (fun p : ℝ × ℝ => ε - δ₂ * p.1) :=
    continuous_const.sub (continuous_const.mul continuous_fst)
  have hξ : Continuous (fun p : ℝ × ℝ => arcFracQ lam δ₁ p.2) := by
    change Continuous (fun p : ℝ × ℝ =>
      1 / 2 - ((1 - 2 * lam) * (2 * δ₁ / period)) * p.2)
    exact continuous_const.sub (continuous_const.mul continuous_snd)
  have hta : Continuous (fun p : ℝ × ℝ => Work.Drive.taR D (ε - δ₂ * p.1)) :=
    (arcWin_taR_continuous D).comp hσ
  have htb : Continuous (fun p : ℝ × ℝ => Work.Drive.tbR D (ε - δ₂ * p.1)) :=
    (arcWin_tbR_continuous D).comp hσ
  have hw : Continuous (fun p : ℝ × ℝ => Work.Drive.sweepW' D (ε - δ₂ * p.1)) :=
    (arcWin_sweepW'_continuous D).comp hσ
  have h1 : Continuous (fun p : ℝ × ℝ => r (Work.Drive.taR D (ε - δ₂ * p.1)
      + arcFracQ lam δ₁ p.2 * Work.Drive.sweepW' D (ε - δ₂ * p.1))) :=
    hr.comp (hta.add (hξ.mul hw))
  have h2 : Continuous (fun p : ℝ × ℝ =>
      (1 - arcFracQ lam δ₁ p.2) • r (Work.Drive.taR D (ε - δ₂ * p.1))
        + (arcFracQ lam δ₁ p.2) • r (Work.Drive.tbR D (ε - δ₂ * p.1))) :=
    ((continuous_const.sub hξ).smul (hr.comp hta)).add (hξ.smul (hr.comp htb))
  exact h1.sub h2

/-- **The component bounds of `chartUp`.**  The three estimates (against `-e₀`, against `b₀`, and
the norm) read off the double-average identity `nclm_chartUp_inner`. -/
theorem nclm_chartUp_bounds {r : ℝ → Space} (hr : IsSmoothKnot r) {d : BandArcData}
    (D : Work.Drive.SweepData d) {lam δ₁ δ₂ ε W c K Kn dve dvb : ℝ} {v : Space}
    (hv : ‖v‖ = 1)
    (hid : ∀ y : Space, inner ℝ (Work.Drive.chartUp r D lam δ₁ δ₂ ε v) y
        = bumpAvg₂ (fun v' u =>
            inner ℝ (Work.Drive.loopDev r D (ε - δ₂ * v') (arcFracQ lam δ₁ u)) y
              - inner ℝ v y * inner ℝ (Work.Drive.loopDev r D (ε - δ₂ * v')
                  (arcFracQ lam δ₁ u)) v))
    (hlam0 : 0 ≤ lam) (hlam1 : lam ≤ 1) (hδ₁0 : 0 < δ₁) (hδ₁16 : δ₁ ≤ period / 16)
    (hδ₂0 : 0 ≤ δ₂)
    (hwpos : ∀ σ, ε - δ₂ ≤ σ → σ ≤ ε + δ₂ → 0 ≤ Work.Drive.sweepW' D σ)
    (hW : 0 < W) (hc : 0 ≤ c) (hK : 0 ≤ K) (hKn : 0 ≤ Kn)
    (hwslo : ∀ σ, ε - δ₂ ≤ σ → σ ≤ ε + δ₂ → W / 2 ≤ Work.Drive.sweepW' D σ)
    (hwshi : ∀ σ, ε - δ₂ ≤ σ → σ ≤ ε + δ₂ → Work.Drive.sweepW' D σ ≤ 2 * W)
    (hdev : ∀ σ, ε - δ₂ ≤ σ → σ ≤ ε + δ₂ → ∀ ξ ∈ Set.Icc (0 : ℝ) 1,
        (ξ * (1 - ξ) / 2) * (Work.Drive.sweepW' D σ) ^ 2 * c
            ≤ inner ℝ (Work.Drive.loopDev r D σ ξ) (-(nclmE0 r D)) ∧
        |inner ℝ (Work.Drive.loopDev r D σ ξ) (nclmB0 r D)|
            ≤ (ξ * (1 - ξ) / 2) * (Work.Drive.sweepW' D σ) ^ 2 * K ∧
        |inner ℝ (Work.Drive.loopDev r D σ ξ) v|
            ≤ (ξ * (1 - ξ) / 2) * (Work.Drive.sweepW' D σ) ^ 2 * K ∧
        ‖Work.Drive.loopDev r D σ ξ‖
            ≤ (ξ * (1 - ξ) / 2) * (Work.Drive.sweepW' D σ) ^ 2 * Kn)
    (hdve : |inner ℝ v (nclmE0 r D)| ≤ dve)
    (hdvb : |inner ℝ v (nclmB0 r D)| ≤ dvb) :
    W ^ 2 * c / 64 - W ^ 2 * dve * K / 2
        ≤ inner ℝ (Work.Drive.chartUp r D lam δ₁ δ₂ ε v) (-(nclmE0 r D)) ∧
    |inner ℝ (Work.Drive.chartUp r D lam δ₁ δ₂ ε v) (nclmB0 r D)|
        ≤ W ^ 2 * K * (1 + dvb) / 2 ∧
    ‖Work.Drive.chartUp r D lam δ₁ δ₂ ε v‖ ≤ W ^ 2 * (Kn + K) / 2 := by
  have hcontL := continuous_loopDevQ hr.continuous D lam δ₁ δ₂ ε
  have hcont : ∀ y : Space, Continuous (Function.uncurry (fun v' u : ℝ =>
      inner ℝ (Work.Drive.loopDev r D (ε - δ₂ * v') (arcFracQ lam δ₁ u)) y
        - inner ℝ v y * inner ℝ (Work.Drive.loopDev r D (ε - δ₂ * v')
            (arcFracQ lam δ₁ u)) v)) := by
    intro y
    show Continuous (fun p : ℝ × ℝ =>
      inner ℝ (Work.Drive.loopDev r D (ε - δ₂ * p.1) (arcFracQ lam δ₁ p.2)) y
        - inner ℝ v y * inner ℝ (Work.Drive.loopDev r D (ε - δ₂ * p.1)
            (arcFracQ lam δ₁ p.2)) v)
    exact (hcontL.inner continuous_const).sub
      (continuous_const.mul (hcontL.inner continuous_const))
  -- the arc fraction stays in `[1/4,3/4]`, hence `φ (1-φ)/2 ∈ [1/16, 1/8]`
  have hφlo : ∀ u ∈ Set.Icc (-1 : ℝ) 1,
      (1 / 16 : ℝ) ≤ arcFracQ lam δ₁ u * (1 - arcFracQ lam δ₁ u) / 2 := by
    intro u hu
    obtain ⟨h1, h2⟩ := arcFracQ_mem hlam0 hlam1 hδ₁0 hδ₁16 hu
    have hkey : (3 : ℝ) / 16 ≤ arcFracQ lam δ₁ u * (1 - arcFracQ lam δ₁ u) := by
      nlinarith [mul_nonneg (show (0:ℝ) ≤ arcFracQ lam δ₁ u - 1 / 4 by linarith)
        (show (0:ℝ) ≤ 3 / 4 - arcFracQ lam δ₁ u by linarith)]
    linarith
  have hφhi : ∀ u ∈ Set.Icc (-1 : ℝ) 1,
      arcFracQ lam δ₁ u * (1 - arcFracQ lam δ₁ u) / 2 ≤ (1 / 8 : ℝ) := by
    intro u hu
    have hkey : arcFracQ lam δ₁ u * (1 - arcFracQ lam δ₁ u) ≤ (1 : ℝ) / 4 := by
      nlinarith [sq_nonneg (arcFracQ lam δ₁ u - 1 / 2)]
    linarith
  have hφnn : ∀ u ∈ Set.Icc (-1 : ℝ) 1,
      (0 : ℝ) ≤ arcFracQ lam δ₁ u * (1 - arcFracQ lam δ₁ u) / 2 := by
    intro u hu
    linarith [hφlo u hu]
  have hφmem : ∀ u ∈ Set.Icc (-1 : ℝ) 1, arcFracQ lam δ₁ u ∈ Set.Icc (0 : ℝ) 1 := by
    intro u hu
    obtain ⟨h1, h2⟩ := arcFracQ_mem hlam0 hlam1 hδ₁0 hδ₁16 hu
    exact ⟨by linarith, by linarith⟩
  have hσmem : ∀ v' ∈ Set.Icc (-1 : ℝ) 1,
      ε - δ₂ ≤ ε - δ₂ * v' ∧ ε - δ₂ * v' ≤ ε + δ₂ := by
    intro v' hv'
    constructor
    · nlinarith [hv'.2, hδ₂0]
    · nlinarith [hv'.1, hδ₂0]
  have hsqlo : ∀ σ, ε - δ₂ ≤ σ → σ ≤ ε + δ₂ → W ^ 2 / 4 ≤ (Work.Drive.sweepW' D σ) ^ 2 := by
    intro σ h1 h2
    have h := hwslo σ h1 h2
    have h2' := mul_self_le_mul_self (show (0:ℝ) ≤ W / 2 by linarith) h
    nlinarith [h2']
  have hsqhi : ∀ σ, ε - δ₂ ≤ σ → σ ≤ ε + δ₂ → (Work.Drive.sweepW' D σ) ^ 2 ≤ 4 * W ^ 2 := by
    intro σ h1 h2
    have h := hwshi σ h1 h2
    have hp := hwpos σ h1 h2
    have h2' := mul_self_le_mul_self hp h
    nlinarith [h2']
  -- the product of the fraction factor and the squared width, in the window
  have hPQle : ∀ v' ∈ Set.Icc (-1 : ℝ) 1, ∀ u ∈ Set.Icc (-1 : ℝ) 1,
      arcFracQ lam δ₁ u * (1 - arcFracQ lam δ₁ u) / 2
        * (Work.Drive.sweepW' D (ε - δ₂ * v')) ^ 2 ≤ W ^ 2 / 2 := by
    intro v' hv' u hu
    obtain ⟨hσ1, hσ2⟩ := hσmem v' hv'
    have hPle := hφhi u hu
    have hQle := hsqhi (ε - δ₂ * v') hσ1 hσ2
    have hPnn := hφnn u hu
    have hQnn : (0:ℝ) ≤ (Work.Drive.sweepW' D (ε - δ₂ * v')) ^ 2 := sq_nonneg _
    calc arcFracQ lam δ₁ u * (1 - arcFracQ lam δ₁ u) / 2
          * (Work.Drive.sweepW' D (ε - δ₂ * v')) ^ 2
        ≤ (1 / 8) * (4 * W ^ 2) := mul_le_mul hPle hQle hQnn (by norm_num)
      _ = W ^ 2 / 2 := by ring
  have hPQge : ∀ v' ∈ Set.Icc (-1 : ℝ) 1, ∀ u ∈ Set.Icc (-1 : ℝ) 1,
      W ^ 2 / 64 ≤ arcFracQ lam δ₁ u * (1 - arcFracQ lam δ₁ u) / 2
        * (Work.Drive.sweepW' D (ε - δ₂ * v')) ^ 2 := by
    intro v' hv' u hu
    obtain ⟨hσ1, hσ2⟩ := hσmem v' hv'
    have hPge := hφlo u hu
    have hQge := hsqlo (ε - δ₂ * v') hσ1 hσ2
    have hPnn := hφnn u hu
    have hQnn : (0:ℝ) ≤ (Work.Drive.sweepW' D (ε - δ₂ * v')) ^ 2 := sq_nonneg _
    calc W ^ 2 / 64 = (1 / 16 : ℝ) * (W ^ 2 / 4) := by ring
      _ ≤ (arcFracQ lam δ₁ u * (1 - arcFracQ lam δ₁ u) / 2)
            * (Work.Drive.sweepW' D (ε - δ₂ * v')) ^ 2 := by
          refine mul_le_mul hPge hQge (by positivity) hPnn
  have hdevE : ∀ v' ∈ Set.Icc (-1 : ℝ) 1, ∀ u ∈ Set.Icc (-1 : ℝ) 1,
      W ^ 2 / 64 * c ≤ inner ℝ (Work.Drive.loopDev r D (ε - δ₂ * v') (arcFracQ lam δ₁ u))
        (-(nclmE0 r D)) := by
    intro v' hv' u hu
    obtain ⟨hσ1, hσ2⟩ := hσmem v' hv'
    obtain ⟨he, hb, hv2, hn⟩ := hdev (ε - δ₂ * v') hσ1 hσ2 (arcFracQ lam δ₁ u) (hφmem u hu)
    calc W ^ 2 / 64 * c ≤ (arcFracQ lam δ₁ u * (1 - arcFracQ lam δ₁ u) / 2
            * (Work.Drive.sweepW' D (ε - δ₂ * v')) ^ 2) * c :=
          mul_le_mul_of_nonneg_right (hPQge v' hv' u hu) hc
      _ ≤ _ := he
  have hdevB : ∀ v' ∈ Set.Icc (-1 : ℝ) 1, ∀ u ∈ Set.Icc (-1 : ℝ) 1,
      |inner ℝ (Work.Drive.loopDev r D (ε - δ₂ * v') (arcFracQ lam δ₁ u)) (nclmB0 r D)|
        ≤ W ^ 2 / 2 * K := by
    intro v' hv' u hu
    obtain ⟨hσ1, hσ2⟩ := hσmem v' hv'
    obtain ⟨he, hb, hv2, hn⟩ := hdev (ε - δ₂ * v') hσ1 hσ2 (arcFracQ lam δ₁ u) (hφmem u hu)
    calc |inner ℝ (Work.Drive.loopDev r D (ε - δ₂ * v') (arcFracQ lam δ₁ u)) (nclmB0 r D)|
        ≤ (arcFracQ lam δ₁ u * (1 - arcFracQ lam δ₁ u) / 2
            * (Work.Drive.sweepW' D (ε - δ₂ * v')) ^ 2) * K := hb
      _ ≤ W ^ 2 / 2 * K := mul_le_mul_of_nonneg_right (hPQle v' hv' u hu) hK
  have hdevV : ∀ v' ∈ Set.Icc (-1 : ℝ) 1, ∀ u ∈ Set.Icc (-1 : ℝ) 1,
      |inner ℝ (Work.Drive.loopDev r D (ε - δ₂ * v') (arcFracQ lam δ₁ u)) v|
        ≤ W ^ 2 / 2 * K := by
    intro v' hv' u hu
    obtain ⟨hσ1, hσ2⟩ := hσmem v' hv'
    obtain ⟨he, hb, hv2, hn⟩ := hdev (ε - δ₂ * v') hσ1 hσ2 (arcFracQ lam δ₁ u) (hφmem u hu)
    calc |inner ℝ (Work.Drive.loopDev r D (ε - δ₂ * v') (arcFracQ lam δ₁ u)) v|
        ≤ (arcFracQ lam δ₁ u * (1 - arcFracQ lam δ₁ u) / 2
            * (Work.Drive.sweepW' D (ε - δ₂ * v')) ^ 2) * K := hv2
      _ ≤ W ^ 2 / 2 * K := mul_le_mul_of_nonneg_right (hPQle v' hv' u hu) hK
  have hdevN : ∀ v' ∈ Set.Icc (-1 : ℝ) 1, ∀ u ∈ Set.Icc (-1 : ℝ) 1,
      ‖Work.Drive.loopDev r D (ε - δ₂ * v') (arcFracQ lam δ₁ u)‖ ≤ W ^ 2 / 2 * Kn := by
    intro v' hv' u hu
    obtain ⟨hσ1, hσ2⟩ := hσmem v' hv'
    obtain ⟨he, hb, hv2, hn⟩ := hdev (ε - δ₂ * v') hσ1 hσ2 (arcFracQ lam δ₁ u) (hφmem u hu)
    calc ‖Work.Drive.loopDev r D (ε - δ₂ * v') (arcFracQ lam δ₁ u)‖
        ≤ (arcFracQ lam δ₁ u * (1 - arcFracQ lam δ₁ u) / 2
            * (Work.Drive.sweepW' D (ε - δ₂ * v')) ^ 2) * Kn := hn
      _ ≤ W ^ 2 / 2 * Kn := mul_le_mul_of_nonneg_right (hPQle v' hv' u hu) hKn
  have hdve0 : (0:ℝ) ≤ dve := le_trans (abs_nonneg _) hdve
  have hdvb0 : (0:ℝ) ≤ dvb := le_trans (abs_nonneg _) hdvb
  have hWnn : (0:ℝ) ≤ W ^ 2 := sq_nonneg W
  have hK2 : (0:ℝ) ≤ W ^ 2 / 2 * K := by positivity
  refine ⟨?_, ?_, ?_⟩
  · rw [hid (-(nclmE0 r D))]
    refine bumpAvg₂_ge' (hcont (-(nclmE0 r D))) (C := W ^ 2 * c / 64 - W ^ 2 * dve * K / 2) ?_
    intro v' hv' u hu
    have h1 := hdevE v' hv' u hu
    have h2 := hdevV v' hv' u hu
    have h3 : inner ℝ v (-(nclmE0 r D)) = -inner ℝ v (nclmE0 r D) := inner_neg_right v _
    have h7 : |inner ℝ v (nclmE0 r D) * inner ℝ (Work.Drive.loopDev r D (ε - δ₂ * v')
        (arcFracQ lam δ₁ u)) v| ≤ dve * (W ^ 2 / 2 * K) := by
      rw [abs_mul]
      exact mul_le_mul hdve h2 (abs_nonneg _) hdve0
    have h8 : -(dve * (W ^ 2 / 2 * K)) ≤ inner ℝ v (nclmE0 r D)
        * inner ℝ (Work.Drive.loopDev r D (ε - δ₂ * v') (arcFracQ lam δ₁ u)) v :=
      neg_le_of_abs_le h7
    have h9 : W ^ 2 * c / 64 - W ^ 2 * dve * K / 2
        = W ^ 2 * c / 64 - dve * (W ^ 2 / 2 * K) := by ring
    rw [h3, h9]
    linarith [h1, h8]
  · rw [hid (nclmB0 r D)]
    refine bumpAvg₂_abs_le' (hcont (nclmB0 r D)) (C := W ^ 2 * K * (1 + dvb) / 2) ?_
    intro v' hv' u hu
    have h1 := hdevB v' hv' u hu
    have hv2 := hdevV v' hv' u hu
    have h2 : |inner ℝ v (nclmB0 r D) * inner ℝ (Work.Drive.loopDev r D (ε - δ₂ * v')
        (arcFracQ lam δ₁ u)) v| ≤ dvb * (W ^ 2 / 2 * K) := by
      rw [abs_mul]
      exact mul_le_mul hdvb hv2 (abs_nonneg _) hdvb0
    calc |inner ℝ (Work.Drive.loopDev r D (ε - δ₂ * v') (arcFracQ lam δ₁ u)) (nclmB0 r D)
          - inner ℝ v (nclmB0 r D) * inner ℝ (Work.Drive.loopDev r D (ε - δ₂ * v')
              (arcFracQ lam δ₁ u)) v|
        ≤ |inner ℝ (Work.Drive.loopDev r D (ε - δ₂ * v') (arcFracQ lam δ₁ u)) (nclmB0 r D)|
          + |inner ℝ v (nclmB0 r D) * inner ℝ (Work.Drive.loopDev r D (ε - δ₂ * v')
              (arcFracQ lam δ₁ u)) v| := abs_sub_le_add _ _
      _ ≤ W ^ 2 / 2 * K + dvb * (W ^ 2 / 2 * K) := add_le_add h1 h2
      _ = W ^ 2 * K * (1 + dvb) / 2 := by ring
  · have hpt : ∀ v' ∈ Set.Icc (-1 : ℝ) 1, ∀ u ∈ Set.Icc (-1 : ℝ) 1,
        |inner ℝ (Work.Drive.loopDev r D (ε - δ₂ * v') (arcFracQ lam δ₁ u))
            (Work.Drive.chartUp r D lam δ₁ δ₂ ε v)
          - inner ℝ v (Work.Drive.chartUp r D lam δ₁ δ₂ ε v)
            * inner ℝ (Work.Drive.loopDev r D (ε - δ₂ * v') (arcFracQ lam δ₁ u)) v|
          ≤ W ^ 2 / 2 * (Kn + K) * ‖Work.Drive.chartUp r D lam δ₁ δ₂ ε v‖ := by
      intro v' hv' u hu
      have h1 := hdevN v' hv' u hu
      have hv2 := hdevV v' hv' u hu
      have hvle : |inner ℝ v (Work.Drive.chartUp r D lam δ₁ δ₂ ε v)| ≤
          ‖Work.Drive.chartUp r D lam δ₁ δ₂ ε v‖ := by
        calc |inner ℝ v (Work.Drive.chartUp r D lam δ₁ δ₂ ε v)|
            ≤ ‖v‖ * ‖Work.Drive.chartUp r D lam δ₁ δ₂ ε v‖ := abs_real_inner_le_norm _ _
          _ = _ := by rw [hv, one_mul]
      have hnorm0 : (0:ℝ) ≤ ‖Work.Drive.chartUp r D lam δ₁ δ₂ ε v‖ := norm_nonneg _
      have hb1 : |inner ℝ (Work.Drive.loopDev r D (ε - δ₂ * v') (arcFracQ lam δ₁ u))
          (Work.Drive.chartUp r D lam δ₁ δ₂ ε v)|
          ≤ W ^ 2 / 2 * Kn * ‖Work.Drive.chartUp r D lam δ₁ δ₂ ε v‖ := by
        calc |inner ℝ (Work.Drive.loopDev r D (ε - δ₂ * v') (arcFracQ lam δ₁ u))
              (Work.Drive.chartUp r D lam δ₁ δ₂ ε v)|
            ≤ ‖Work.Drive.loopDev r D (ε - δ₂ * v') (arcFracQ lam δ₁ u)‖
                * ‖Work.Drive.chartUp r D lam δ₁ δ₂ ε v‖ := abs_real_inner_le_norm _ _
          _ ≤ (W ^ 2 / 2 * Kn) * ‖Work.Drive.chartUp r D lam δ₁ δ₂ ε v‖ :=
              mul_le_mul_of_nonneg_right h1 hnorm0
      have hb2 : |inner ℝ v (Work.Drive.chartUp r D lam δ₁ δ₂ ε v)
          * inner ℝ (Work.Drive.loopDev r D (ε - δ₂ * v') (arcFracQ lam δ₁ u)) v|
          ≤ W ^ 2 / 2 * K * ‖Work.Drive.chartUp r D lam δ₁ δ₂ ε v‖ := by
        rw [abs_mul]
        calc |inner ℝ v (Work.Drive.chartUp r D lam δ₁ δ₂ ε v)|
              * |inner ℝ (Work.Drive.loopDev r D (ε - δ₂ * v') (arcFracQ lam δ₁ u)) v|
            ≤ ‖Work.Drive.chartUp r D lam δ₁ δ₂ ε v‖ * (W ^ 2 / 2 * K) :=
              mul_le_mul hvle hv2 (abs_nonneg _) hnorm0
          _ = W ^ 2 / 2 * K * ‖Work.Drive.chartUp r D lam δ₁ δ₂ ε v‖ := by ring
      calc |inner ℝ (Work.Drive.loopDev r D (ε - δ₂ * v') (arcFracQ lam δ₁ u))
            (Work.Drive.chartUp r D lam δ₁ δ₂ ε v)
          - inner ℝ v (Work.Drive.chartUp r D lam δ₁ δ₂ ε v)
            * inner ℝ (Work.Drive.loopDev r D (ε - δ₂ * v') (arcFracQ lam δ₁ u)) v|
          ≤ |inner ℝ (Work.Drive.loopDev r D (ε - δ₂ * v') (arcFracQ lam δ₁ u))
              (Work.Drive.chartUp r D lam δ₁ δ₂ ε v)|
            + |inner ℝ v (Work.Drive.chartUp r D lam δ₁ δ₂ ε v)
              * inner ℝ (Work.Drive.loopDev r D (ε - δ₂ * v') (arcFracQ lam δ₁ u)) v| :=
            abs_sub_le_add _ _
        _ ≤ (W ^ 2 / 2 * Kn) * ‖Work.Drive.chartUp r D lam δ₁ δ₂ ε v‖
              + (W ^ 2 / 2 * K) * ‖Work.Drive.chartUp r D lam δ₁ δ₂ ε v‖ :=
            add_le_add hb1 hb2
        _ = W ^ 2 / 2 * (Kn + K) * ‖Work.Drive.chartUp r D lam δ₁ δ₂ ε v‖ := by ring
    have h := bumpAvg₂_abs_le' (hcont (Work.Drive.chartUp r D lam δ₁ δ₂ ε v))
      (C := W ^ 2 / 2 * (Kn + K) * ‖Work.Drive.chartUp r D lam δ₁ δ₂ ε v‖) hpt
    have h' : |inner ℝ (Work.Drive.chartUp r D lam δ₁ δ₂ ε v)
        (Work.Drive.chartUp r D lam δ₁ δ₂ ε v)|
        ≤ W ^ 2 / 2 * (Kn + K) * ‖Work.Drive.chartUp r D lam δ₁ δ₂ ε v‖ := by
      rw [hid]; exact h
    rw [real_inner_self_eq_norm_sq, abs_of_nonneg (sq_nonneg _)] at h'
    have h2 : (0:ℝ) ≤ W ^ 2 / 2 * (Kn + K) := by positivity
    nlinarith [h', h2, norm_nonneg (Work.Drive.chartUp r D lam δ₁ δ₂ ε v)]

end Work.Drive.Generic
