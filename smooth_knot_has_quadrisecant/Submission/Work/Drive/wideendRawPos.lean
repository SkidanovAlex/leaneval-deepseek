import Mathlib
import Submission.Work.Drive.sweepFamWideTolDefs
import Submission.Work.Drive.chamferVelBranch

/-!
# The raw value estimate at the wide end of the chord sweep

`Work.Drive.wideendRawPos`: the *unsmoothed* chamfered chord sweep
`Work.Drive.sweepLoopChamfer r D lam sig` is, after the matched reparametrisation
`Work.Drive.wideSigma`, quadratically close to the knot `r` at the wide end.

The content is the following second-order cancellation.  Writing

* `a = taR D sig`, `w = sweepW' D sig`, `d = period - w` (the "gap"), `lam` for the chamfer
  fraction and `u = sweepParam τ` for the loop fraction,

the loop point and the matched knot point are linked by the *same* affine interpolation: in each
of the four zones of `sweepLoopChamfer` the difference `loop - r (wideSigma …)` is a sum of at
most two terms of the form

`(1 - t) • r x + t • r y - r ((1 - t) * x + t * y)`,

whose size is controlled by `M₂` (the Lipschitz constant of the velocity) times the *square* of
the parameter gap between `x` and `y`.  The first-order terms cancel automatically because the
matched phase `wideSigma` advances exactly like the affine interpolation of the loop point.

## Main result

* `Work.Drive.wideendRawPos` — with constant `2 * M₂ + 1`.
-/

namespace Work.Drive

open LeanEval.KnotTheory.Quadrisecant
open scoped Real Topology unitInterval intervalIntegral

noncomputable section

/-! ## Periodicity helpers -/

/-- Shifting the argument of a `period`-periodic curve by an integer number of periods. -/
lemma wideRaw_int_shift {f : ℝ → Space} (hper : Function.Periodic f period) (x : ℝ) (k : ℤ) :
    f (x + (k : ℝ) * period) = f x := by
  have h := hper.sub_int_mul_eq (-k) (x := x)
  rw [Int.cast_neg, neg_mul] at h
  rw [show x - -((k : ℝ) * period) = x + (k : ℝ) * period by ring] at h
  exact h

/-- Shifting the argument of a `period`-periodic curve by one period. -/
lemma wideRaw_period_shift {f : ℝ → Space} (hper : Function.Periodic f period) {x y : ℝ}
    (h : x = y + period) : f x = f y := by
  rw [h]; exact hper y

/-- **The matched phase is the matched fraction up to a whole number of periods.** -/
lemma wideRaw_r_wideSigma {r : ℝ → Space} (hper : Function.Periodic r period)
    (a w d lam τ : ℝ) :
    r (wideSigma a w d lam τ) = r (wideSfrac a w d lam (sweepParam τ)) := by
  have hk : τ - sweepParam τ * period = ((⌊τ / period⌋ : ℤ) : ℝ) * period := by
    rw [sweepParam, sub_mul, div_mul_cancel₀ τ (ne_of_gt period_pos)]
    ring
  rw [wideSigma]
  rw [show τ + (wideSfrac a w d lam (sweepParam τ) - sweepParam τ * period)
      = wideSfrac a w d lam (sweepParam τ) + ((⌊τ / period⌋ : ℤ) : ℝ) * period by
    linarith [hk]]
  exact wideRaw_int_shift hper _ _

/-! ## The first-order difference quotient of a curve

For a `C¹` curve `r` and reals `p q` we write `wideRawVelInt r p q` for the *average velocity over the
segment* `[p, q]`, so that `r q - r p = (q - p) • wideRawVelInt r p q` exactly (fundamental theorem of
calculus).  The Lipschitz bound on the velocity then controls how far `wideRawVelInt r p q` is from the
velocity at a point. -/

/-- The average velocity of `r` over the parameter segment `[p,q]`. -/
def wideRawVelInt (r : ℝ → Space) (p q : ℝ) : Space :=
  ∫ s in (0 : ℝ)..1, velocity r (p + s * (q - p))

/-- **Fundamental theorem of calculus in difference-quotient form.** -/
lemma velInt_sub_eq {r : ℝ → Space} (hdr : Differentiable ℝ r)
    (hvelcont : Continuous (velocity r)) (p q : ℝ) :
    r q - r p = (q - p) • wideRawVelInt r p q := by
  have hderiv : ∀ s ∈ Set.uIcc (0 : ℝ) 1,
      HasDerivAt (fun s : ℝ => r (p + s * (q - p)))
        ((q - p) • velocity r (p + s * (q - p))) s := by
    intro s _
    have hinner : HasDerivAt (fun s : ℝ => p + s * (q - p)) (q - p) s := by
      have h1 : HasDerivAt (fun s : ℝ => s * (q - p)) (q - p) s := by
        simpa using (hasDerivAt_id s).mul_const (q - p)
      simpa using h1.const_add p
    exact (hdr (p + s * (q - p))).hasDerivAt.scomp s hinner
  have hcont : Continuous (fun s : ℝ => velocity r (p + s * (q - p))) :=
    hvelcont.comp (continuous_const.add (continuous_id.mul_const _))
  have hint : IntervalIntegrable (fun s : ℝ => (q - p) • velocity r (p + s * (q - p)))
      MeasureTheory.volume (0 : ℝ) 1 :=
    Continuous.intervalIntegrable (Continuous.smul
      (continuous_const : Continuous fun _ : ℝ => (q - p)) hcont) _ _
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
  rw [intervalIntegral.integral_smul,
    show p + 1 * (q - p) = q by ring, show p + 0 * (q - p) = p by ring] at h
  exact h.symm

/-- The average velocity over a segment is close to the velocity at any point, by the Lipschitz
bound of the velocity. -/
lemma velInt_close {r : ℝ → Space} (hvelcont : Continuous (velocity r)) {M₂ : ℝ}
    (hM2 : ∀ x y : ℝ, ‖velocity r x - velocity r y‖ ≤ M₂ * |x - y|) (hM2nn : 0 ≤ M₂)
    (p q z : ℝ) :
    ‖wideRawVelInt r p q - velocity r z‖ ≤ M₂ * max |p - z| |q - z| := by
  have hcont : Continuous (fun s : ℝ => velocity r (p + s * (q - p)) - velocity r z) :=
    (hvelcont.comp (continuous_const.add (continuous_id.mul_const _))).sub continuous_const
  have hint2 : IntervalIntegrable (fun s : ℝ => velocity r (p + s * (q - p)))
      MeasureTheory.volume (0 : ℝ) 1 :=
    Continuous.intervalIntegrable
      (hvelcont.comp (continuous_const.add (continuous_id.mul_const _))) _ _
  have hint3 : IntervalIntegrable (fun _ : ℝ => velocity r z) MeasureTheory.volume (0 : ℝ) 1 :=
    Continuous.intervalIntegrable continuous_const _ _
  have hsub : wideRawVelInt r p q - velocity r z
      = ∫ s in (0 : ℝ)..1, (velocity r (p + s * (q - p)) - velocity r z) := by
    rw [wideRawVelInt, intervalIntegral.integral_sub hint2 hint3, intervalIntegral.integral_const]
    simp
  rw [hsub]
  have hC : ∀ s ∈ Set.uIoc (0 : ℝ) 1,
      ‖velocity r (p + s * (q - p)) - velocity r z‖ ≤ M₂ * max |p - z| |q - z| := by
    intro s hs
    have hs' : s ∈ Set.Icc (0 : ℝ) 1 := by
      rw [Set.uIoc_of_le zero_le_one] at hs; exact ⟨hs.1.le, hs.2⟩
    have hs0 : 0 ≤ s := hs'.1
    have h1s : 0 ≤ 1 - s := by linarith [hs'.2]
    have h1 : ‖p + s * (q - p) - z‖ ≤ max |p - z| |q - z| := by
      rw [show p + s * (q - p) - z = (1 - s) * (p - z) + s * (q - z) by ring]
      have hn : ‖(1 - s) * (p - z) + s * (q - z)‖ ≤ (1 - s) * |p - z| + s * |q - z| := by
        calc ‖(1 - s) * (p - z) + s * (q - z)‖
            ≤ ‖(1 - s) * (p - z)‖ + ‖s * (q - z)‖ := norm_add_le _ _
          _ = (1 - s) * |p - z| + s * |q - z| := by
              simp only [norm_mul, Real.norm_eq_abs, abs_of_nonneg h1s, abs_of_nonneg hs0]
      have hle1 : (1 - s) * |p - z| ≤ (1 - s) * max |p - z| |q - z| :=
        mul_le_mul_of_nonneg_left (le_max_left _ _) h1s
      have hle2 : s * |q - z| ≤ s * max |p - z| |q - z| :=
        mul_le_mul_of_nonneg_left (le_max_right _ _) hs0
      have hMs : (1 - s) * max |p - z| |q - z| + s * max |p - z| |q - z|
          = max |p - z| |q - z| := by ring
      linarith [hn, hle1, hle2, hMs]
    calc ‖velocity r (p + s * (q - p)) - velocity r z‖
        ≤ M₂ * |p + s * (q - p) - z| := hM2 _ _
      _ ≤ M₂ * max |p - z| |q - z| := mul_le_mul_of_nonneg_left h1 hM2nn
  calc ‖∫ s in (0 : ℝ)..1, (velocity r (p + s * (q - p)) - velocity r z)‖
      ≤ (M₂ * max |p - z| |q - z|) * |1 - 0| :=
        intervalIntegral.norm_integral_le_of_norm_le_const hC
    _ = M₂ * max |p - z| |q - z| := by rw [sub_zero, abs_one, mul_one]

/-! ## The chord deviation -/

/-- **The deviation of the chord of `r x`, `r y` from the curve at the matching parameter.** -/
def wideRawChordDev (r : ℝ → Space) (x y t : ℝ) : Space :=
  (1 - t) • r x + t • r y - r ((1 - t) * x + t * y)

/-- The chord deviation, expressed through the average velocities. -/
lemma chordDev_eq_smul {r : ℝ → Space} (hdr : Differentiable ℝ r)
    (hvelcont : Continuous (velocity r)) (x y t : ℝ) :
    wideRawChordDev r x y t
      = (t * (1 - t) * (y - x)) •
          (wideRawVelInt r ((1 - t) * x + t * y) y - wideRawVelInt r ((1 - t) * x + t * y) x) := by
  set p := (1 - t) * x + t * y with hp
  have hsplit : wideRawChordDev r x y t = (1 - t) • (r x - r p) + t • (r y - r p) := by
    rw [wideRawChordDev]; module
  rw [hsplit, velInt_sub_eq hdr hvelcont p x, velInt_sub_eq hdr hvelcont p y]
  rw [show x - p = -(t * (y - x)) by rw [hp]; ring,
      show y - p = (1 - t) * (y - x) by rw [hp]; ring]
  module

/-- **The quadratic chord-deviation bound.**  For `t ∈ [0,1]` the chord of the points `r x`, `r y`
at fraction `t` is within `M₂ (y - x)²` of the curve at the matching parameter. -/
lemma norm_chordDev_le {r : ℝ → Space} (hdr : Differentiable ℝ r)
    (hvelcont : Continuous (velocity r)) {M₂ : ℝ}
    (hM2 : ∀ x y : ℝ, ‖velocity r x - velocity r y‖ ≤ M₂ * |x - y|) (hM2nn : 0 ≤ M₂)
    {x y t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    ‖wideRawChordDev r x y t‖ ≤ M₂ * (y - x) ^ 2 := by
  set p := (1 - t) * x + t * y with hp
  rw [chordDev_eq_smul hdr hvelcont, norm_smul, Real.norm_eq_abs]
  have h1 : ‖wideRawVelInt r p y - wideRawVelInt r p x‖ ≤ M₂ * |y - x| := by
    have ha : ‖wideRawVelInt r p y - velocity r p‖ ≤ M₂ * ((1 - t) * |y - x|) := by
      have h := velInt_close hvelcont hM2 hM2nn p y p
      rw [sub_self, abs_zero, max_eq_right (abs_nonneg _)] at h
      rwa [show |y - p| = (1 - t) * |y - x| by
        rw [show y - p = (1 - t) * (y - x) by rw [hp]; ring, abs_mul,
          abs_of_nonneg (by linarith)]] at h
    have hb : ‖wideRawVelInt r p x - velocity r p‖ ≤ M₂ * (t * |y - x|) := by
      have h := velInt_close hvelcont hM2 hM2nn p x p
      rw [sub_self, abs_zero, max_eq_right (abs_nonneg _)] at h
      rwa [show |x - p| = t * |y - x| by
        rw [show x - p = -(t * (y - x)) by rw [hp]; ring, abs_neg, abs_mul,
          abs_of_nonneg ht0]] at h
    have htri : ‖wideRawVelInt r p y - wideRawVelInt r p x‖
        ≤ ‖wideRawVelInt r p y - velocity r p‖ + ‖wideRawVelInt r p x - velocity r p‖ := by
      have h := norm_add_le (wideRawVelInt r p y - velocity r p) (velocity r p - wideRawVelInt r p x)
      rw [show (wideRawVelInt r p y - velocity r p) + (velocity r p - wideRawVelInt r p x)
            = wideRawVelInt r p y - wideRawVelInt r p x by abel,
          norm_sub_rev (velocity r p) (wideRawVelInt r p x)] at h
      exact h
    calc ‖wideRawVelInt r p y - wideRawVelInt r p x‖
        ≤ ‖wideRawVelInt r p y - velocity r p‖ + ‖wideRawVelInt r p x - velocity r p‖ := htri
      _ ≤ M₂ * ((1 - t) * |y - x|) + M₂ * (t * |y - x|) := add_le_add ha hb
      _ = M₂ * |y - x| := by ring
  have h5 : |t * (1 - t) * (y - x)| = t * (1 - t) * |y - x| := by
    rw [abs_mul, abs_mul, abs_of_nonneg ht0, abs_of_nonneg (by linarith)]
  rw [h5]
  have h6 : t * (1 - t) * |y - x| * (M₂ * |y - x|) ≤ M₂ * (y - x) ^ 2 := by
    have hs : t * (1 - t) ≤ 1 := by nlinarith
    have habs : |y - x| * |y - x| = (y - x) ^ 2 := by rw [← sq_abs]; ring
    have hM : (t * (1 - t)) * M₂ ≤ 1 * M₂ := mul_le_mul_of_nonneg_right hs hM2nn
    calc t * (1 - t) * |y - x| * (M₂ * |y - x|)
        = ((t * (1 - t)) * M₂) * (|y - x| * |y - x|) := by ring
      _ = ((t * (1 - t)) * M₂) * (y - x) ^ 2 := by rw [habs]
      _ ≤ (1 * M₂) * (y - x) ^ 2 := mul_le_mul_of_nonneg_right hM (sq_nonneg _)
      _ = M₂ * (y - x) ^ 2 := by ring
  calc t * (1 - t) * |y - x| * ‖wideRawVelInt r p y - wideRawVelInt r p x‖
      ≤ t * (1 - t) * |y - x| * (M₂ * |y - x|) :=
        mul_le_mul_of_nonneg_left h1 (by positivity)
    _ ≤ M₂ * (y - x) ^ 2 := h6

/-! ## The four zones -/

/-- **Bounds for the width of the retained arc.** -/
lemma wideRaw_sweepW'_bounds {d0 : BandArcData} (D : SweepData d0) (sig : ℝ) :
    0 ≤ sweepW' D sig ∧ sweepW' D sig ≤ period := by
  rcases le_or_gt sig 0 with h | h
  · have hcl : clampI sig = (0 : I) := by
      apply Subtype.ext
      show min 1 (max 0 sig) = ((0 : I) : ℝ)
      rw [max_eq_left h, min_eq_right zero_le_one]
      norm_num
    have h1 : taR D sig = D.ta 0 := by simp only [taR, hcl]
    have h2 : tbR D sig = D.tb 0 := by simp only [tbR, hcl]
    rw [sweepW', h1, h2, D.left_eq, sub_self]
    exact ⟨le_rfl, period_pos.le⟩
  rcases lt_or_ge sig 1 with h1 | h1
  · have hmem : sig ∈ Set.Ioo (0 : ℝ) 1 := ⟨h, h1⟩
    have hle : sig ∈ Set.Icc (0 : ℝ) 1 := ⟨h.le, h1.le⟩
    have hcl : clampI sig = (⟨sig, hle⟩ : I) := by
      apply Subtype.ext
      show min 1 (max 0 sig) = sig
      rw [max_eq_right hle.1, min_eq_right hle.2]
    have hw : sweepW' D sig = sweepW D ⟨sig, hle⟩ := by
      simp only [sweepW', sweepW, taR, tbR, hcl]
    rw [hw]
    exact ⟨(sweepW_pos_lt D ⟨sig, hle⟩ hmem).1.le, (sweepW_pos_lt D ⟨sig, hle⟩ hmem).2.le⟩
  · have hcl : clampI sig = (1 : I) := by
      apply Subtype.ext
      show min 1 (max 0 sig) = ((1 : I) : ℝ)
      rw [max_eq_right (le_trans zero_le_one h1), min_eq_left h1]
      norm_num
    have h1' : taR D sig = D.ta 1 := by simp only [taR, hcl]
    have h2' : tbR D sig = D.tb 1 := by simp only [tbR, hcl]
    rw [sweepW', h1', h2', D.right_eq, add_sub_cancel_left]
    exact ⟨period_pos.le, le_rfl⟩

/-- **Zone 1 (the arc).**  Here the loop point *is* the matched knot point. -/
private lemma wideRaw_zone1 {r : ℝ → Space} {d0 : BandArcData} (D : SweepData d0) {M₂ : ℝ}
    (hM2nn : 0 ≤ M₂) {lam sig τ : ℝ} (hu : sweepParam τ ≤ 1 / 2) :
    ‖sweepLoopChamfer r D lam sig τ -
      r (wideSfrac (taR D sig) (sweepW' D sig) (period - sweepW' D sig) lam (sweepParam τ))‖
      ≤ M₂ * ((lam * period) ^ 2 + (period - sweepW' D sig) ^ 2) := by
  have hloop : sweepLoopChamfer r D lam sig τ -
      r (wideSfrac (taR D sig) (sweepW' D sig) (period - sweepW' D sig) lam (sweepParam τ))
      = 0 := by
    rw [show wideSfrac (taR D sig) (sweepW' D sig) (period - sweepW' D sig) lam (sweepParam τ)
        = taR D sig + (lam + (1 - 2 * lam) * (2 * sweepParam τ)) * sweepW' D sig by
      rw [wideSfrac_arc hu]]
    rw [sweepLoopChamfer, if_pos hu]
    simp only [sweepArc']
    rw [sub_self]
  rw [hloop, norm_zero]
  exact mul_nonneg hM2nn (add_nonneg (sq_nonneg _) (sq_nonneg _))

/-- **Zone 2 (the first chamfer).** -/
private lemma wideRaw_zone2 {r : ℝ → Space} {d0 : BandArcData} (D : SweepData d0) {M₂ : ℝ}
    (hdr : Differentiable ℝ r) (hvelcont : Continuous (velocity r))
    (hM2 : ∀ x y : ℝ, ‖velocity r x - velocity r y‖ ≤ M₂ * |x - y|) (hM2nn : 0 ≤ M₂)
    (hper : Function.Periodic r period)
    {lam sig τ : ℝ} (hlam0 : 0 < lam) (hlam : lam ≤ 1 / 4)
    (hu1 : ¬ sweepParam τ ≤ 1 / 2) (hu2 : sweepParam τ ≤ 1 / 2 + lam / 2) :
    ‖sweepLoopChamfer r D lam sig τ -
      r (wideSfrac (taR D sig) (sweepW' D sig) (period - sweepW' D sig) lam (sweepParam τ))‖
      ≤ M₂ * ((lam * period) ^ 2 + (period - sweepW' D sig) ^ 2) := by
  set u := sweepParam τ with hu
  set dd := period - sweepW' D sig with hdd
  set a := taR D sig with ha
  set rho := (2 * u - 1) / lam with hrho
  set y := a - (1 - lam) * dd with hy
  have hwdd : sweepW' D sig = period - dd := by rw [hdd]; ring
  have htb' : r (tbR D sig) = r (a - dd) := by
    have harg : tbR D sig = (a - dd) + period := by
      rw [hdd, ha, sweepW']
      ring
    rw [harg]
    exact hper _
  have harc : r (a + (1 - lam) * (period - dd)) = r (y - lam * period) := by
    have harg : a + (1 - lam) * (period - dd) = (y - lam * period) + period := by
      rw [hy]; ring
    rw [harg]
    exact hper _
  have hL : sweepLoopChamfer r D lam sig τ
      = (1 - rho) • r (y - lam * period) + rho • (lam • r a + (1 - lam) • r (a - dd)) := by
    rw [sweepLoopChamfer, if_neg hu1, if_pos hu2]
    simp only [sweepArc', sweepChord']
    rw [show taR D sig = a from ha.symm,
        show (2 * u - 1) / lam = rho from hrho.symm,
        show (1 : ℝ) - (1 - lam) = lam by ring]
    rw [hwdd, harc, htb']
  have hR : r (wideSfrac (taR D sig) (sweepW' D sig) (period - sweepW' D sig) lam
        (sweepParam τ)) = r (y - (1 - rho) * lam * period) := by
    rw [wideSfrac_chamfer₁ hu1 hu2, hwdd, show taR D sig = a from ha.symm]
    exact wideRaw_period_shift hper (show a + (1 - lam) * (period - dd) + (2 * u - 1) * period
        = (y - (1 - rho) * lam * period) + period by
      rw [hrho, hy]; field_simp; ring)
  have hkey : sweepLoopChamfer r D lam sig τ -
      r (wideSfrac (taR D sig) (sweepW' D sig) (period - sweepW' D sig) lam (sweepParam τ))
      = wideRawChordDev r (y - lam * period) y rho + rho • wideRawChordDev r (a - dd) a lam := by
    rw [hL, hR]
    simp only [wideRawChordDev]
    rw [show (1 - rho) * (y - lam * period) + rho * y = y - (1 - rho) * lam * period by ring,
        show (1 - lam) * (a - dd) + lam * a = y by rw [hy]; ring]
    module
  have hrho0 : 0 ≤ rho := by
    rw [hrho]
    exact div_nonneg (by linarith [not_le.mp hu1]) hlam0.le
  have hrho1 : rho ≤ 1 := by
    rw [hrho, div_le_one hlam0]
    linarith [hu2]
  rw [hkey]
  have hb1 : ‖wideRawChordDev r (y - lam * period) y rho‖ ≤ M₂ * (lam * period) ^ 2 := by
    have h := norm_chordDev_le hdr hvelcont hM2 hM2nn (x := y - lam * period) (y := y) hrho0 hrho1
    rwa [show y - (y - lam * period) = lam * period by ring] at h
  have hb2 : ‖rho • wideRawChordDev r (a - dd) a lam‖ ≤ rho * (M₂ * dd ^ 2) := by
    rw [norm_smul, Real.norm_of_nonneg hrho0]
    refine mul_le_mul_of_nonneg_left ?_ hrho0
    have h := norm_chordDev_le hdr hvelcont hM2 hM2nn (x := a - dd) (y := a) hlam0.le (by linarith)
    rwa [show a - (a - dd) = dd by ring] at h
  calc ‖wideRawChordDev r (y - lam * period) y rho + rho • wideRawChordDev r (a - dd) a lam‖
      ≤ ‖wideRawChordDev r (y - lam * period) y rho‖ + ‖rho • wideRawChordDev r (a - dd) a lam‖ :=
        norm_add_le _ _
    _ ≤ M₂ * (lam * period) ^ 2 + rho * (M₂ * dd ^ 2) := add_le_add hb1 hb2
    _ ≤ M₂ * ((lam * period) ^ 2 + (period - sweepW' D sig) ^ 2) := by
        rw [← hdd]
        have hrhoM : rho * (M₂ * dd ^ 2) ≤ M₂ * dd ^ 2 := by
          have hm := mul_le_mul_of_nonneg_right hrho1 (mul_nonneg hM2nn (sq_nonneg dd))
          simpa using hm
        nlinarith [hrhoM, hM2nn, sq_nonneg dd, sq_nonneg (lam * period)]

/-- **Zone 3 (the chord).** -/
private lemma wideRaw_zone3 {r : ℝ → Space} {d0 : BandArcData} (D : SweepData d0) {M₂ : ℝ}
    (hdr : Differentiable ℝ r) (hvelcont : Continuous (velocity r))
    (hM2 : ∀ x y : ℝ, ‖velocity r x - velocity r y‖ ≤ M₂ * |x - y|) (hM2nn : 0 ≤ M₂)
    (hper : Function.Periodic r period)
    {lam sig τ : ℝ} (hlam0 : 0 < lam) (hlam : lam ≤ 1 / 4)
    (hu1 : ¬ sweepParam τ ≤ 1 / 2) (hu2 : ¬ sweepParam τ ≤ 1 / 2 + lam / 2)
    (hu3 : sweepParam τ ≤ 1 - lam / 2) :
    ‖sweepLoopChamfer r D lam sig τ -
      r (wideSfrac (taR D sig) (sweepW' D sig) (period - sweepW' D sig) lam (sweepParam τ))‖
      ≤ M₂ * ((lam * period) ^ 2 + (period - sweepW' D sig) ^ 2) := by
  set u := sweepParam τ with hu
  set dd := period - sweepW' D sig with hdd
  set a := taR D sig with ha
  set th := (u - (1 / 2 + lam / 2)) / (1 / 2 - lam) with hth
  set xi := (1 - lam) - th * (1 - 2 * lam) with hxi
  have hden : 0 < 1 / 2 - lam := by linarith
  have hu1' : 1 / 2 < u := by rw [hu]; exact not_le.mp hu1
  have hu2' : 1 / 2 + lam / 2 < u := by rw [hu]; exact not_le.mp hu2
  have hu3' : u ≤ 1 - lam / 2 := by rw [hu]; exact hu3
  have hwdd : sweepW' D sig = period - dd := by rw [hdd]; ring
  have hth0 : 0 ≤ th := by
    rw [hth]
    exact div_nonneg (by linarith [hu2']) hden.le
  have hth1 : th ≤ 1 := by
    rw [hth, div_le_iff₀ hden]
    linarith [hu3']
  have hxi0 : 0 ≤ xi := by
    rw [hxi]
    nlinarith [hth1, hlam]
  have hxi1 : xi ≤ 1 := by
    rw [hxi]
    nlinarith [hth0, hlam0]
  have htb' : r (tbR D sig) = r (a - dd) := by
    have harg : tbR D sig = (a - dd) + period := by
      rw [hdd, ha, sweepW']
      ring
    rw [harg]
    exact hper _
  have hL : sweepLoopChamfer r D lam sig τ = (1 - xi) • r a + xi • r (a - dd) := by
    rw [sweepLoopChamfer, if_neg hu1, if_neg hu2, if_pos hu3]
    simp only [sweepChord']
    rw [show taR D sig = a from ha.symm,
        show (1 - lam) - ((u - (1 / 2 + lam / 2)) / (1 / 2 - lam)) * (1 - 2 * lam)
          = xi from hxi.symm,
        htb']
  have hR : r (wideSfrac (taR D sig) (sweepW' D sig) (period - sweepW' D sig) lam
        (sweepParam τ)) = r (a - dd * xi) := by
    rw [wideSfrac_chord hu1 hu2 hu3, hdd.symm, hwdd, show taR D sig = a from ha.symm]
    exact wideRaw_period_shift hper (show a + (period - dd) + lam * dd
          + (1 - 2 * lam) * dd * ((u - (1 / 2 + lam / 2)) / (1 / 2 - lam))
        = (a - dd * xi) + period by
      rw [hxi, ← hth]; ring)
  have hkey : sweepLoopChamfer r D lam sig τ -
      r (wideSfrac (taR D sig) (sweepW' D sig) (period - sweepW' D sig) lam (sweepParam τ))
      = wideRawChordDev r (a - dd) a (1 - xi) := by
    rw [hL, hR]
    simp only [wideRawChordDev]
    rw [show (1 - (1 - xi)) * (a - dd) + (1 - xi) * a = a - dd * xi by ring]
    module
  rw [hkey]
  have h := norm_chordDev_le hdr hvelcont hM2 hM2nn (x := a - dd) (y := a) (t := 1 - xi)
    (by linarith) (by linarith)
  rw [show a - (a - dd) = dd by ring] at h
  refine h.trans ?_
  nlinarith [hM2nn, sq_nonneg dd, sq_nonneg (lam * period)]

/-- **Zone 4 (the second chamfer).** -/
private lemma wideRaw_zone4 {r : ℝ → Space} {d0 : BandArcData} (D : SweepData d0) {M₂ : ℝ}
    (hdr : Differentiable ℝ r) (hvelcont : Continuous (velocity r))
    (hM2 : ∀ x y : ℝ, ‖velocity r x - velocity r y‖ ≤ M₂ * |x - y|) (hM2nn : 0 ≤ M₂)
    (hper : Function.Periodic r period)
    {lam sig τ : ℝ} (hlam0 : 0 < lam) (hlam : lam ≤ 1 / 4)
    (hu1 : ¬ sweepParam τ ≤ 1 / 2) (hu2 : ¬ sweepParam τ ≤ 1 / 2 + lam / 2)
    (hu3 : ¬ sweepParam τ ≤ 1 - lam / 2) :
    ‖sweepLoopChamfer r D lam sig τ -
      r (wideSfrac (taR D sig) (sweepW' D sig) (period - sweepW' D sig) lam (sweepParam τ))‖
      ≤ M₂ * ((lam * period) ^ 2 + (period - sweepW' D sig) ^ 2) := by
  set u := sweepParam τ with hu
  set dd := period - sweepW' D sig with hdd
  set a := taR D sig with ha
  set t4 := (u - (1 - lam / 2)) / (lam / 2) with ht4
  set eta := 1 - t4 with heta
  set z := a - lam * dd with hz
  have hl2 : 0 < lam / 2 := by linarith
  have hu1' : 1 / 2 < u := by rw [hu]; exact not_le.mp hu1
  have hu2' : 1 / 2 + lam / 2 < u := by rw [hu]; exact not_le.mp hu2
  have hu3' : 1 - lam / 2 < u := by rw [hu]; exact not_le.mp hu3
  have hu4 : u < 1 := (sweepParam_mem τ).2
  have hwdd : sweepW' D sig = period - dd := by rw [hdd]; ring
  have ht40 : 0 ≤ t4 := by
    rw [ht4]
    exact div_nonneg (by linarith [hu3']) hl2.le
  have ht41 : t4 ≤ 1 := by
    rw [ht4, div_le_one hl2]
    linarith [hu4]
  have heta0 : 0 ≤ eta := by rw [heta]; linarith
  have heta1 : eta ≤ 1 := by rw [heta]; linarith
  have htb' : r (tbR D sig) = r (a - dd) := by
    have harg : tbR D sig = (a - dd) + period := by
      rw [hdd, ha, sweepW']
      ring
    rw [harg]
    exact hper _
  have hzc : r (a + lam * (period - dd)) = r (z + lam * period) := by
    have harg : a + lam * (period - dd) = z + lam * period := by rw [hz]; ring
    rw [harg]
  have hL : sweepLoopChamfer r D lam sig τ
      = eta • ((1 - lam) • r a + lam • r (a - dd)) + (1 - eta) • r (z + lam * period) := by
    rw [sweepLoopChamfer, if_neg hu1, if_neg hu2, if_neg hu3]
    simp only [sweepArc', sweepChord']
    rw [show taR D sig = a from ha.symm,
        show (1 : ℝ) - (u - (1 - lam / 2)) / (lam / 2) = eta from heta.symm,
        show (u - (1 - lam / 2)) / (lam / 2) = t4 from ht4.symm,
        hwdd]
    rw [show t4 = 1 - eta by rw [heta]; ring]
    rw [hzc, htb']
  have hR : r (wideSfrac (taR D sig) (sweepW' D sig) (period - sweepW' D sig) lam
        (sweepParam τ)) = r (z + (1 - eta) * lam * period) := by
    rw [wideSfrac_chamfer₂ hu1 hu2 hu3, hdd.symm, hwdd, show taR D sig = a from ha.symm]
    exact wideRaw_period_shift hper (show a + (period - dd) + (1 - lam) * dd
          + (2 * u - 2 + lam) * period = (z + (1 - eta) * lam * period) + period by
      rw [hz, heta, ht4]; field_simp; ring)
  have hkey : sweepLoopChamfer r D lam sig τ -
      r (wideSfrac (taR D sig) (sweepW' D sig) (period - sweepW' D sig) lam (sweepParam τ))
      = eta • wideRawChordDev r a (a - dd) lam + wideRawChordDev r (z + lam * period) z eta := by
    rw [hL, hR]
    simp only [wideRawChordDev]
    rw [show (1 - lam) * a + lam * (a - dd) = z by rw [hz]; ring,
        show (1 - eta) * (z + lam * period) + eta * z = z + (1 - eta) * lam * period by ring]
    module
  rw [hkey]
  have hb1 : ‖eta • wideRawChordDev r a (a - dd) lam‖ ≤ M₂ * dd ^ 2 := by
    rw [norm_smul, Real.norm_of_nonneg heta0]
    have h := norm_chordDev_le hdr hvelcont hM2 hM2nn (x := a) (y := a - dd) (t := lam)
      hlam0.le (by linarith)
    rw [show a - dd - a = -dd by ring, neg_sq] at h
    calc eta * ‖wideRawChordDev r a (a - dd) lam‖ ≤ eta * (M₂ * dd ^ 2) :=
          mul_le_mul_of_nonneg_left h heta0
      _ ≤ 1 * (M₂ * dd ^ 2) :=
          mul_le_mul_of_nonneg_right heta1 (mul_nonneg hM2nn (sq_nonneg dd))
      _ = M₂ * dd ^ 2 := by ring
  have hb2 : ‖wideRawChordDev r (z + lam * period) z eta‖ ≤ M₂ * (lam * period) ^ 2 := by
    have h := norm_chordDev_le hdr hvelcont hM2 hM2nn (x := z + lam * period) (y := z) (t := eta)
      heta0 heta1
    rwa [show z - (z + lam * period) = -(lam * period) by ring, neg_sq] at h
  calc ‖eta • wideRawChordDev r a (a - dd) lam + wideRawChordDev r (z + lam * period) z eta‖
      ≤ ‖eta • wideRawChordDev r a (a - dd) lam‖ + ‖wideRawChordDev r (z + lam * period) z eta‖ :=
        norm_add_le _ _
    _ ≤ M₂ * dd ^ 2 + M₂ * (lam * period) ^ 2 := add_le_add hb1 hb2
    _ ≤ M₂ * ((lam * period) ^ 2 + (period - sweepW' D sig) ^ 2) := by
        rw [← hdd]
        nlinarith [hM2nn, sq_nonneg dd, sq_nonneg (lam * period)]

/-! ## The main theorem -/

theorem wideendRawPos {r : ℝ → LeanEval.KnotTheory.Quadrisecant.Space}
    (hr : LeanEval.KnotTheory.Quadrisecant.IsSmoothKnot r)
    {d : LeanEval.KnotTheory.Quadrisecant.BandArcData} (D : Work.Drive.SweepData d)
    {M₁ M₂ : ℝ}
    (hM₁ : ∀ t : ℝ, ‖LeanEval.KnotTheory.Quadrisecant.velocity r t‖ ≤ M₁)
    (hM₂ : ∀ x y : ℝ, ‖LeanEval.KnotTheory.Quadrisecant.velocity r x -
      LeanEval.KnotTheory.Quadrisecant.velocity r y‖ ≤ M₂ * |x - y|) :
    ∃ C : ℝ, 0 < C ∧ ∀ (sig lam τ : ℝ), 0 < lam → lam ≤ 1 / 4 → sig ≤ 1 →
      ‖Work.Drive.sweepLoopChamfer r D lam sig τ -
        r (Work.Drive.wideSigma (Work.Drive.taR D sig) (Work.Drive.sweepW' D sig)
          (LeanEval.KnotTheory.Quadrisecant.period - Work.Drive.sweepW' D sig) lam τ)‖
        ≤ C * (lam * LeanEval.KnotTheory.Quadrisecant.period
            + (LeanEval.KnotTheory.Quadrisecant.period - Work.Drive.sweepW' D sig)) ^ 2 := by
  by_cases hM2nn : 0 ≤ M₂
  · refine ⟨2 * M₂ + 1, by linarith, ?_⟩
    intro sig lam τ hlam0 hlam1 hsig
    have hdr : Differentiable ℝ r := hr.smooth.differentiable (by simp)
    have hvelcont : Continuous (velocity r) := hr.smooth.continuous_deriv le_top
    have hdd0 : 0 ≤ period - sweepW' D sig := by
      have := (wideRaw_sweepW'_bounds D sig).2; linarith
    have hpp : 0 ≤ lam * period := mul_nonneg hlam0.le period_pos.le
    have hred : r (wideSigma (taR D sig) (sweepW' D sig) (period - sweepW' D sig) lam τ)
        = r (wideSfrac (taR D sig) (sweepW' D sig) (period - sweepW' D sig) lam
            (sweepParam τ)) :=
      wideRaw_r_wideSigma hr.periodic _ _ _ _ _
    rw [hred]
    have hfin : M₂ * ((lam * period) ^ 2 + (period - sweepW' D sig) ^ 2)
        ≤ (2 * M₂ + 1) * (lam * period + (period - sweepW' D sig)) ^ 2 := by
      have hsq : (lam * period) ^ 2 + (period - sweepW' D sig) ^ 2
          ≤ (lam * period + (period - sweepW' D sig)) ^ 2 := by nlinarith [hpp, hdd0]
      have h1 : M₂ * ((lam * period) ^ 2 + (period - sweepW' D sig) ^ 2)
          ≤ M₂ * (lam * period + (period - sweepW' D sig)) ^ 2 :=
        mul_le_mul_of_nonneg_left hsq hM2nn
      nlinarith [h1, sq_nonneg (lam * period + (period - sweepW' D sig))]
    by_cases h1 : sweepParam τ ≤ 1 / 2
    · exact (wideRaw_zone1 D hM2nn h1).trans hfin
    · by_cases h2 : sweepParam τ ≤ 1 / 2 + lam / 2
      · exact (wideRaw_zone2 D hdr hvelcont hM₂ hM2nn hr.periodic hlam0 hlam1 h1 h2).trans hfin
      · by_cases h3 : sweepParam τ ≤ 1 - lam / 2
        · exact (wideRaw_zone3 D hdr hvelcont hM₂ hM2nn hr.periodic hlam0 hlam1 h1 h2 h3).trans hfin
        · exact (wideRaw_zone4 D hdr hvelcont hM₂ hM2nn hr.periodic hlam0 hlam1 h1 h2 h3).trans hfin
  · exfalso
    have h := hM₂ 0 1
    norm_num at h
    linarith [norm_nonneg (velocity r 0 - velocity r 1)]

end

end Work.Drive
