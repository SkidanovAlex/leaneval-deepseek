import Mathlib
import Submission.Work.Drive.chordSweepSmooth
import Submission.Work.Drive.sweepWideEndDefs
import Submission.Work.Drive.chamferVelBranch
import Submission.Work.Drive.sweepFamWideTolDefs
import Submission.Work.Drive.sweepTopMatchingDefs

/-!
# The raw velocity bound of the top of the sweep, with explicit constant

`Work.Drive.sweepMatchRawVel`: for every Lipschitz constant `M₂` of the knot velocity, the raw
velocity `chamferVel` of the chamfered sweep loop differs from the matched knot velocity
`wideRho (...) lam (sweepParam τ) • velocity r (topSigma ...)` by at most
`M₂ (1 + period) (lam + (period - sweepW' D σ))` times that same matched rate.

This is the sharp-constant version of `Work.Drive.wideendRawVel` (whose conclusion is an
existential over the constant).  The loop parameter splits into four zones; on the arc zone the
two sides are *literally equal* (`Work.Drive.smv_arc`) and on the chord zone the natural
constant `2` already suffices (`Work.Drive.smv_chord`).  The two chamfer zones are re-estimated
here: the constructions of `werv_chamfer₁`/`werv_chamfer₂` lose a factor `4` there, which is
fatal for the constant `M₂ (1 + period)` asked for.  On each chamfer the two one-sided chord
differences are compared with the matched velocity at the *reduced* matched parameter, and the
*sum of the chord lengths* is the only thing that must be booked, giving
`2 M₂ (lam period + 2 lam d + d)`.
-/

noncomputable section
namespace Work.Drive

open LeanEval.KnotTheory.Quadrisecant
open scoped Real Topology

set_option maxHeartbeats 4000000

/-! ## The velocity is the slope of a chord through a nearby point -/

/-- The fundamental theorem of calculus along the knot. -/
lemma smv_int_velocity {r : ℝ → Space} (hr : IsSmoothKnot r) {a b : ℝ} (hab : a ≤ b) :
    ∫ y in a..b, velocity r y = r b - r a := by
  have hvcont : Continuous (velocity r) := hr.smooth.continuous_deriv le_top
  refine intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hab
    hr.smooth.continuous.continuousOn ?_ ?_
  · intro x hx
    exact (hr.smooth.differentiable (by simp) x).hasDerivAt
  · exact hvcont.intervalIntegrable _ _

/-- **The velocity of a curve is the slope of any chord through a nearby point.**  If `V` is
`M`-Lipschitz and `r` is an antiderivative of `V`, then for `p ≤ q` and any `c` whose distance
to both `p` and `q` is at most `D`,
`‖(r q - r p) - (q - p) • V c‖ ≤ M (q - p) D`. -/
lemma smv_chord_vel_bound {r : ℝ → Space} (hr : IsSmoothKnot r) {M : ℝ}
    (hlip : ∀ x y : ℝ, ‖velocity r x - velocity r y‖ ≤ M * |x - y|) (hM0 : 0 ≤ M)
    {p q c D : ℝ} (hpq : p ≤ q) (hD0 : 0 ≤ D) (hcp : |c - p| ≤ D) (hcq : |c - q| ≤ D) :
    ‖(r q - r p) - (q - p) • velocity r c‖ ≤ M * (q - p) * D := by
  have hvcont : Continuous (velocity r) := hr.smooth.continuous_deriv le_top
  have hInt : (r q - r p) - (q - p) • velocity r c
      = ∫ s in p..q, (velocity r s - velocity r c) := by
    rw [intervalIntegral.integral_sub (hvcont.intervalIntegrable _ _)
      (continuous_const.intervalIntegrable _ _), smv_int_velocity hr hpq,
      intervalIntegral.integral_const]
  rw [hInt]
  have hbound : ‖∫ s in p..q, (velocity r s - velocity r c)‖ ≤ (M * D) * |q - p| := by
    refine intervalIntegral.norm_integral_le_of_norm_le_const ?_
    intro x hx
    rw [Set.uIoc_of_le hpq] at hx
    have h1 : |x - c| ≤ D := by
      rw [abs_le]
      exact ⟨by linarith [(abs_le.mp hcp).2, le_of_lt hx.1],
             by linarith [(abs_le.mp hcq).1, hx.2]⟩
    calc ‖velocity r x - velocity r c‖ ≤ M * |x - c| := hlip x c
      _ ≤ M * D := mul_le_mul_of_nonneg_left h1 hM0
  calc ‖∫ s in p..q, (velocity r s - velocity r c)‖ ≤ (M * D) * |q - p| := hbound
    _ = M * (q - p) * D := by rw [abs_of_nonneg (sub_nonneg.mpr hpq)]; ring

/-! ## Periodicity of the velocity and the width of the retained arc -/

/-- The velocity of a `period`-periodic curve is `period`-periodic. -/
lemma smv_velocity_periodic {r : ℝ → Space} (hr : IsSmoothKnot r) :
    Function.Periodic (velocity r) period := by
  intro x
  show deriv r (x + period) = deriv r x
  have h2 : (fun y : ℝ => r (y + period)) = r := funext hr.periodic
  have h3 := deriv_comp_add_const r period x
  rw [h2] at h3
  exact h3.symm

lemma smv_clampI_eq_zero {x : ℝ} (h : x ≤ 0) : clampI x = (0 : ↑unitInterval) := by
  apply Subtype.ext
  show min 1 (max 0 x) = 0
  rw [max_eq_left h, min_eq_right zero_le_one]

lemma smv_clampI_eq_one {x : ℝ} (h : 1 ≤ x) : clampI x = (1 : ↑unitInterval) := by
  apply Subtype.ext
  show min 1 (max 0 x) = 1
  rw [max_eq_right (le_trans zero_le_one h), min_eq_left h]

lemma smv_clampI_eq_self {x : ℝ} (h : x ∈ Set.Icc (0 : ℝ) 1) :
    clampI x = (⟨x, h⟩ : ↑unitInterval) := by
  apply Subtype.ext
  show min 1 (max 0 x) = x
  rw [max_eq_right h.1, min_eq_right h.2]

lemma smv_sweepW'_eq_zero_of_nonpos {d : BandArcData} (D : SweepData d) {sig : ℝ}
    (h : sig ≤ 0) : sweepW' D sig = 0 := by
  have h1 : clampI sig = (0 : ↑unitInterval) := smv_clampI_eq_zero h
  have h2 : taR D sig = D.ta 0 := by simp only [taR, h1]
  have h3 : tbR D sig = D.tb 0 := by simp only [tbR, h1]
  simp only [sweepW', h2, h3, ← D.left_eq, sub_self]

lemma smv_sweepW'_eq_period_of_one_le {d : BandArcData} (D : SweepData d) {sig : ℝ}
    (h : 1 ≤ sig) : sweepW' D sig = period := by
  have h1 : clampI sig = (1 : ↑unitInterval) := smv_clampI_eq_one h
  have h2 : taR D sig = D.ta 1 := by simp only [taR, h1]
  have h3 : tbR D sig = D.tb 1 := by simp only [tbR, h1]
  rw [sweepW', h2, h3, D.right_eq]
  ring

/-- **The width of the retained arc** lies in `[0, period]`. -/
lemma smv_sweepW'_nonneg_le {d : BandArcData} (D : SweepData d) (sig : ℝ) :
    0 ≤ sweepW' D sig ∧ sweepW' D sig ≤ period := by
  by_cases h0 : sig ≤ 0
  · rw [smv_sweepW'_eq_zero_of_nonpos D h0]; exact ⟨le_rfl, period_pos.le⟩
  rw [not_le] at h0
  by_cases h1 : sig < 1
  · have hmem : sig ∈ Set.Ioo (0 : ℝ) 1 := ⟨h0, h1⟩
    have hle : sig ∈ Set.Icc (0 : ℝ) 1 := ⟨h0.le, h1.le⟩
    have hw : sweepW' D sig = sweepW D ⟨sig, hle⟩ := by
      simp only [sweepW', sweepW, taR, tbR, smv_clampI_eq_self hle]
    rw [hw]
    exact ⟨(sweepW_pos_lt D ⟨sig, hle⟩ hmem).1.le, (sweepW_pos_lt D ⟨sig, hle⟩ hmem).2.le⟩
  · rw [not_lt] at h1
    rw [smv_sweepW'_eq_period_of_one_le D h1]; exact ⟨period_pos.le, le_rfl⟩

/-- The matched knot parameter of the top of the sweep, reduced modulo the period: its velocity
is the velocity of `wideSfrac` at the loop fraction. -/
lemma smv_velocity_topSigma_eq_wideSfrac {r : ℝ → Space} (hr : IsSmoothKnot r)
    {d : BandArcData} (D : SweepData d) (lam σ t : ℝ) :
    velocity r (topSigma D lam σ t)
      = velocity r (wideSfrac (taR D σ) (sweepW' D σ) (period - sweepW' D σ) lam
          (sweepParam t)) := by
  rw [topSigma_eq_wideSfrac]
  exact (smv_velocity_periodic hr).int_mul ⌊t / period⌋ _

/-! ## The matched knot velocity of the two chamfer zones -/

/-- The velocity of the matched point on the first chamfer zone. -/
lemma smv_vel_topSigma_c1 {r : ℝ → Space} (hr : IsSmoothKnot r) {d : BandArcData}
    (D : SweepData d) {lam σ τ : ℝ} (h1 : ¬ sweepParam τ ≤ 1 / 2)
    (h2 : sweepParam τ ≤ 1 / 2 + lam / 2) :
    velocity r (topSigma D lam σ τ)
      = velocity r (taR D σ + (1 - lam) * sweepW' D σ + (2 * sweepParam τ - 1) * period) := by
  rw [smv_velocity_topSigma_eq_wideSfrac hr D lam σ τ, wideSfrac_chamfer₁ h1 h2]

/-- The velocity of the matched point on the second chamfer zone. -/
lemma smv_vel_topSigma_c2 {r : ℝ → Space} (hr : IsSmoothKnot r) {d : BandArcData}
    (D : SweepData d) {lam σ τ : ℝ} (h1 : ¬ sweepParam τ ≤ 1 / 2)
    (h2 : ¬ sweepParam τ ≤ 1 / 2 + lam / 2) (h3 : ¬ sweepParam τ ≤ 1 - lam / 2) :
    velocity r (topSigma D lam σ τ)
      = velocity r (taR D σ + sweepW' D σ + (1 - lam) * (period - sweepW' D σ)
          + (2 * sweepParam τ - 2 + lam) * period) := by
  rw [smv_velocity_topSigma_eq_wideSfrac hr D lam σ τ, wideSfrac_chamfer₂ h1 h2 h3]

/-! ## The abstract chord estimates of the two chamfer zones (sharp form) -/

/-- **First-chamfer chord estimate.**  With `φ ∈ [0, lam]` and `w + d = period`,
`lam • r a + (1 - lam) • r (a+w) - r (a + (1-lam) w)` differs from
`lam * period • velocity r (a + (1-lam) w + φ * period)` by at most
`M (lam w (lam period) + lam d (lam period + d))`. -/
lemma smv_cham1_aux {r : ℝ → Space} (hr : IsSmoothKnot r) {M : ℝ}
    (hlip : ∀ x y : ℝ, ‖velocity r x - velocity r y‖ ≤ M * |x - y|) (hM0 : 0 ≤ M)
    {a w d lam φ : ℝ} (hlam0 : 0 < lam) (hφ0 : 0 ≤ φ) (hφl : φ ≤ lam)
    (hwd : w + d = period) (hw0 : 0 ≤ w) (hd0 : 0 ≤ d) :
    ‖(lam • r a + (1 - lam) • r (a + w) - r (a + (1 - lam) * w))
        - (lam * period) • velocity r (a + (1 - lam) * w + φ * period)‖
      ≤ M * (lam * w * (lam * period) + lam * d * (lam * period + d)) := by
  have hP : (0 : ℝ) < period := period_pos
  have hwP : w ≤ period := by linarith
  have hLP : (0 : ℝ) ≤ lam * period := by positivity
  have hD1 : (0 : ℝ) ≤ lam * period + d := by linarith
  set B : ℝ := a + (1 - lam) * w with hB
  set S : ℝ := a + (1 - lam) * w + φ * period with hS
  have hBle : B ≤ a + w := by rw [hB]; nlinarith [hw0, hlam0]
  have hBA : (a + w) - B = lam * w := by rw [hB]; ring
  -- distances from the matched point `S`
  have hSBl : |S - B| ≤ lam * period := by
    rw [hS, hB]
    rw [show a + (1 - lam) * w + φ * period - (a + (1 - lam) * w) = φ * period by ring]
    rw [abs_of_nonneg (mul_nonneg hφ0 hP.le)]
    exact mul_le_mul_of_nonneg_right hφl hP.le
  have hSw : |S - (a + w)| ≤ lam * period := by
    rw [hS]
    have hrw : a + (1 - lam) * w + φ * period - (a + w) = φ * period - lam * w := by ring
    rw [hrw, abs_le]
    have h1 : (0 : ℝ) ≤ φ * period := mul_nonneg hφ0 hP.le
    have h2 : lam * w ≤ lam * period := mul_le_mul_of_nonneg_left hwP hlam0.le
    have h3 : φ * period ≤ lam * period := mul_le_mul_of_nonneg_right hφl hP.le
    have h4 : (0 : ℝ) ≤ lam * w := mul_nonneg hlam0.le hw0
    constructor <;> linarith
  have hSwd : |S - (a + w + d)| ≤ lam * period + d := by
    rw [hS]
    have hrw : a + (1 - lam) * w + φ * period - (a + w + d) = φ * period - lam * w - d := by ring
    rw [hrw, abs_le]
    have h1 : (0 : ℝ) ≤ φ * period := mul_nonneg hφ0 hP.le
    have h2 : lam * w ≤ lam * period := mul_le_mul_of_nonneg_left hwP hlam0.le
    have h3 : φ * period ≤ lam * period := mul_le_mul_of_nonneg_right hφl hP.le
    have h4 : (0 : ℝ) ≤ lam * w := mul_nonneg hlam0.le hw0
    constructor <;> linarith
  -- the two chord estimates
  have hT1 : ‖(r (a + w) - r B) - (lam * w) • velocity r S‖ ≤ M * (lam * w) * (lam * period) := by
    have h := smv_chord_vel_bound hr hlip hM0 hBle hLP hSBl hSw
    rwa [hBA] at h
  have hT2 : ‖(r (a + w + d) - r (a + w)) - d • velocity r S‖
      ≤ M * d * (lam * period + d) := by
    have hle : a + w ≤ a + w + d := by linarith
    have h := smv_chord_vel_bound hr hlip hM0 hle hD1
      (le_trans hSw (by linarith)) hSwd
    have hq : (a + w + d) - (a + w) = d := by ring
    rwa [hq] at h
  -- the identity
  have hper : r (a + w + d) = r a := by
    rw [show a + w + d = a + period by rw [← hwd]; ring]
    exact hr.periodic a
  have hid : (lam • r a + (1 - lam) • r (a + w) - r B) - (lam * period) • velocity r S
      = ((r (a + w) - r B) - (lam * w) • velocity r S)
        + lam • ((r (a + w + d) - r (a + w)) - d • velocity r S) := by
    rw [hper, hB, hS]
    rw [show lam * period = lam * w + lam * d by rw [← hwd]; ring]
    module
  have hsum : ‖((r (a + w) - r B) - (lam * w) • velocity r S)
        + lam • ((r (a + w + d) - r (a + w)) - d • velocity r S)‖
      ≤ M * (lam * w) * (lam * period) + lam * (M * d * (lam * period + d)) := by
    have hsm : ‖lam • ((r (a + w + d) - r (a + w)) - d • velocity r S)‖
        ≤ lam * (M * d * (lam * period + d)) := by
      rw [norm_smul, Real.norm_of_nonneg hlam0.le]
      exact mul_le_mul_of_nonneg_left hT2 hlam0.le
    exact (norm_add_le _ _).trans (add_le_add hT1 hsm)
  rw [hid]
  refine hsum.trans (le_of_eq ?_)
  ring

/-- **Second-chamfer chord estimate.**  With `ψ ∈ [0, lam]`, `lam < 1` and `w + d = period`,
`r (a + lam w) - ((1-lam) r a + lam r (a+w))` differs from
`lam * period • velocity r (a + w + (1-lam) d + ψ * period)` by at most
`M ((1-lam) (lam w) (lam period) + lam (lam w + d) (lam period + d))`. -/
lemma smv_cham2_aux {r : ℝ → Space} (hr : IsSmoothKnot r) {M : ℝ}
    (hlip : ∀ x y : ℝ, ‖velocity r x - velocity r y‖ ≤ M * |x - y|) (hM0 : 0 ≤ M)
    {a w d lam ψ : ℝ} (hlam0 : 0 < lam) (hlam1 : lam < 1) (hψ0 : 0 ≤ ψ) (hψl : ψ ≤ lam)
    (hwd : w + d = period) (hw0 : 0 ≤ w) (hd0 : 0 ≤ d) :
    ‖(r (a + lam * w) - ((1 - lam) • r a + lam • r (a + w)))
        - (lam * period) • velocity r (a + w + (1 - lam) * d + ψ * period)‖
      ≤ M * ((1 - lam) * (lam * w) * (lam * period)
          + lam * (lam * w + d) * (lam * period + d)) := by
  have hP : (0 : ℝ) < period := period_pos
  have hwP : w ≤ period := by linarith
  have hLP : (0 : ℝ) ≤ lam * period := by positivity
  have hD2 : (0 : ℝ) ≤ lam * period + d := by linarith
  have hlam1' : (0 : ℝ) ≤ 1 - lam := by linarith
  have hper : r (a + w) = r (a - d) := by
    have h : a + w = a - d + period := by linarith
    rw [h, hr.periodic (a - d)]
  set S : ℝ := a + w + (1 - lam) * d + ψ * period with hS
  have hSc : S - period = a - lam * d + ψ * period := by
    rw [hS]
    rw [show w = period - d by linarith]
    ring
  have hvS : velocity r S = velocity r (S - period) := by
    have h := smv_velocity_periodic hr (S - period)
    rwa [sub_add_cancel] at h
  -- distances from the reduced matched point `S - period`
  have hca : |(S - period) - a| ≤ lam * period := by
    rw [hSc, abs_le]
    have h1 : (0 : ℝ) ≤ ψ * period := mul_nonneg hψ0 hP.le
    have h2 : ψ * period ≤ lam * period := mul_le_mul_of_nonneg_right hψl hP.le
    have h3 : (0 : ℝ) ≤ lam * d := mul_nonneg hlam0.le hd0
    have h4 : lam * d ≤ lam * period := mul_le_mul_of_nonneg_left (by linarith) hlam0.le
    constructor <;> linarith
  have hcb : |(S - period) - (a + lam * w)| ≤ lam * period := by
    rw [hSc]
    have hrw : a - lam * d + ψ * period - (a + lam * w) = ψ * period - lam * w - lam * d := by ring
    rw [hrw, abs_le]
    have h1 : (0 : ℝ) ≤ ψ * period := mul_nonneg hψ0 hP.le
    have h2 : ψ * period ≤ lam * period := mul_le_mul_of_nonneg_right hψl hP.le
    have h3 : (0 : ℝ) ≤ lam * w := mul_nonneg hlam0.le hw0
    have h4 : (0 : ℝ) ≤ lam * d := mul_nonneg hlam0.le hd0
    have h5 : lam * w + lam * d = lam * period := by rw [← mul_add, hwd]
    constructor <;> linarith
  have hcc : |(S - period) - (a - d)| ≤ lam * period + d := by
    rw [hSc]
    have hrw : a - lam * d + ψ * period - (a - d) = ψ * period + d * (1 - lam) := by ring
    rw [hrw, abs_le]
    have h1 : (0 : ℝ) ≤ ψ * period := mul_nonneg hψ0 hP.le
    have h2 : ψ * period ≤ lam * period := mul_le_mul_of_nonneg_right hψl hP.le
    have h3 : (0 : ℝ) ≤ d * (1 - lam) := mul_nonneg hd0 hlam1'
    have h4 : d * (1 - lam) ≤ d := by nlinarith [hd0, hlam1']
    constructor <;> linarith
  -- the two chord estimates
  have hE1 : ‖(r (a + lam * w) - r a) - (lam * w) • velocity r S‖
      ≤ M * (lam * w) * (lam * period) := by
    rw [hvS]
    have hle : a ≤ a + lam * w := by nlinarith [hlam0, hw0]
    have h := smv_chord_vel_bound hr hlip hM0 hle hLP hca hcb
    have hq : (a + lam * w) - a = lam * w := by ring
    rwa [hq] at h
  have hE2 : ‖(r (a + lam * w) - r (a - d)) - (lam * w + d) • velocity r S‖
      ≤ M * (lam * w + d) * (lam * period + d) := by
    rw [hvS]
    have hle : a - d ≤ a + lam * w := by nlinarith [hlam0, hw0, hd0]
    have h := smv_chord_vel_bound hr hlip hM0 hle hD2 hcc
      (le_trans hcb (by linarith))
    have hq : (a + lam * w) - (a - d) = lam * w + d := by ring
    rwa [hq] at h
  -- the identity
  have hid : (r (a + lam * w) - ((1 - lam) • r a + lam • r (a + w)))
        - (lam * period) • velocity r S
      = (1 - lam) • ((r (a + lam * w) - r a) - (lam * w) • velocity r S)
        + lam • ((r (a + lam * w) - r (a - d)) - (lam * w + d) • velocity r S) := by
    rw [hper]
    rw [show lam * period = lam * w + lam * d by rw [← hwd]; ring]
    module
  have hsum : ‖(1 - lam) • ((r (a + lam * w) - r a) - (lam * w) • velocity r S)
        + lam • ((r (a + lam * w) - r (a - d)) - (lam * w + d) • velocity r S)‖
      ≤ (1 - lam) * (M * (lam * w) * (lam * period))
        + lam * (M * (lam * w + d) * (lam * period + d)) := by
    have h1 : ‖(1 - lam) • ((r (a + lam * w) - r a) - (lam * w) • velocity r S)‖
        ≤ (1 - lam) * (M * (lam * w) * (lam * period)) := by
      rw [norm_smul, Real.norm_of_nonneg hlam1']
      exact mul_le_mul_of_nonneg_left hE1 hlam1'
    have h2 : ‖lam • ((r (a + lam * w) - r (a - d)) - (lam * w + d) • velocity r S)‖
        ≤ lam * (M * (lam * w + d) * (lam * period + d)) := by
      rw [norm_smul, Real.norm_of_nonneg hlam0.le]
      exact mul_le_mul_of_nonneg_left hE2 hlam0.le
    exact (norm_add_le _ _).trans (add_le_add h1 h2)
  rw [hid]
  refine hsum.trans (le_of_eq ?_)
  ring

/-! ## Arithmetic -/

/-- The final arithmetic step of the two chamfer zones: the sharp error
`2 M (lam period + 2 lam d + d)` is still dominated by `M (1 + period) (lam + d) · 2`. -/
lemma smv_arith_cham {M lam w dd : ℝ} (hM0 : 0 ≤ M) (hlam0 : 0 < lam) (hlam1 : lam ≤ 1 / 2)
    (hw0 : 0 ≤ w) (hwP : w ≤ period) (hdd0 : 0 ≤ dd) (hddP : dd ≤ period) :
    2 * M * (lam * period + 2 * lam * dd + dd) ≤ M * (1 + period) * (lam + dd) * 2 := by
  have hP : (0 : ℝ) < period := period_pos
  have hP1 : (1 : ℝ) ≤ period := by rw [period]; linarith [Real.pi_gt_three]
  have hle : lam * period + 2 * lam * dd + dd ≤ (1 + period) * (lam + dd) := by
    have hx : (0 : ℝ) ≤ dd * (period - 2 * lam) :=
      mul_nonneg hdd0 (by linarith)
    nlinarith [hx, hlam0]
  calc 2 * M * (lam * period + 2 * lam * dd + dd)
      ≤ 2 * M * ((1 + period) * (lam + dd)) :=
        mul_le_mul_of_nonneg_left hle (by linarith : (0:ℝ) ≤ 2 * M)
    _ = M * (1 + period) * (lam + dd) * 2 := by ring

/-- The two chamfer expressions are dominated by the common sharp bound. -/
lemma smv_arith_Y {lam w dd : ℝ} (hlam0 : 0 < lam) (hw0 : 0 ≤ w) (hwP : w ≤ period)
    (hdd0 : 0 ≤ dd) (hddP : dd ≤ period) :
    lam * w * (lam * period) + lam * dd * (lam * period + dd)
      ≤ (lam * period + 2 * lam * dd + dd) * (lam * period) := by
  have hP : (0 : ℝ) < period := period_pos
  have h1 : lam * lam * period * w ≤ lam * lam * period * period :=
    mul_le_mul_of_nonneg_left hwP (by positivity : (0:ℝ) ≤ lam * lam * period)
  have h3 : lam * dd * dd ≤ lam * dd * period :=
    mul_le_mul_of_nonneg_left hddP (by positivity : (0:ℝ) ≤ lam * dd)
  have hpos : (0 : ℝ) ≤ lam * lam * dd * period := by positivity
  nlinarith [h1, h3, hpos]

/-- The second-chamfer expression is dominated by the common sharp bound. -/
lemma smv_arith_Y2 {lam w dd : ℝ} (hlam0 : 0 < lam) (hlam1 : lam ≤ 1)
    (hw0 : 0 ≤ w) (hwP : w ≤ period) (hdd0 : 0 ≤ dd) (hddP : dd ≤ period) :
    (1 - lam) * (lam * w) * (lam * period) + lam * (lam * w + dd) * (lam * period + dd)
      ≤ (lam * period + 2 * lam * dd + dd) * (lam * period) := by
  have hP : (0 : ℝ) < period := period_pos
  have h1 : lam * lam * period * w ≤ lam * lam * period * period :=
    mul_le_mul_of_nonneg_left hwP (by positivity : (0:ℝ) ≤ lam * lam * period)
  have h2 : lam * lam * dd * w ≤ lam * lam * dd * period :=
    mul_le_mul_of_nonneg_left hwP (by positivity : (0:ℝ) ≤ lam * lam * dd)
  have h3 : lam * dd * dd ≤ lam * dd * period :=
    mul_le_mul_of_nonneg_left hddP (by positivity : (0:ℝ) ≤ lam * dd)
  have hpos : (0 : ℝ) ≤ lam * lam * dd * period := by positivity
  nlinarith [h1, h2, h3, hpos]

/-! ## The four zone estimates -/

/-- **First chamfer zone**: sharp estimate. -/
lemma smv_cham1 {r : ℝ → Space} (hr : IsSmoothKnot r) {M : ℝ} (hM0 : 0 ≤ M)
    (hlip : ∀ x y : ℝ, ‖velocity r x - velocity r y‖ ≤ M * |x - y|)
    {d : BandArcData} (D : SweepData d) {lam σ t : ℝ} (hlam0 : 0 < lam) (hlam1 : lam < 1 / 2)
    (hu1 : ¬ sweepParam t ≤ 1 / 2) (hu2 : sweepParam t ≤ 1 / 2 + lam / 2) :
    ‖chamferVel r D lam σ t - (2 : ℝ) • velocity r (topSigma D lam σ t)‖
      ≤ 2 * M * (lam * period + 2 * lam * (period - sweepW' D σ) + (period - sweepW' D σ)) := by
  have hP : (0 : ℝ) < period := period_pos
  obtain ⟨hw0, hwP⟩ := smv_sweepW'_nonneg_le D σ
  have hdd0 : 0 ≤ period - sweepW' D σ := by linarith
  have hddP : period - sweepW' D σ ≤ period := by linarith
  have hwd : sweepW' D σ + (period - sweepW' D σ) = period := by ring
  have htb : tbR D σ = taR D σ + sweepW' D σ := by rw [sweepW']; ring
  have hφ0 : 0 ≤ 2 * sweepParam t - 1 := by have := not_le.mp hu1; linarith
  have hφl : 2 * sweepParam t - 1 ≤ lam := by linarith
  have hlamP : lam * period ≠ 0 := by positivity
  -- the raw chord difference, converted to the auxiliary shape
  have hV : (1 - (1 - lam)) • r (taR D σ) + (1 - lam) • r (tbR D σ)
        - r (taR D σ + (1 - lam) * sweepW' D σ)
      = lam • r (taR D σ) + (1 - lam) • r (taR D σ + sweepW' D σ)
        - r (taR D σ + (1 - lam) * sweepW' D σ) := by
    rw [htb]
    module
  have hcv : chamferVel r D lam σ t
      = (2 / (lam * period)) • (lam • r (taR D σ) + (1 - lam) • r (taR D σ + sweepW' D σ)
          - r (taR D σ + (1 - lam) * sweepW' D σ)) := by
    rw [chamferVel_eq_ite, if_neg hu1, if_pos hu2, chamferVelChamfer₁]
    simp only [sweepChord', sweepArc']
    rw [show (2 / lam) * (1 / period) = 2 / (lam * period) by field_simp, hV]
  have hvel : velocity r (topSigma D lam σ t)
      = velocity r (taR D σ + (1 - lam) * sweepW' D σ + (2 * sweepParam t - 1) * period) :=
    smv_vel_topSigma_c1 hr D hu1 hu2
  have haux := smv_cham1_aux (r := r) hr hlip hM0 (a := taR D σ) (w := sweepW' D σ)
    (d := period - sweepW' D σ) (lam := lam) (φ := 2 * sweepParam t - 1)
    hlam0 hφ0 hφl hwd hw0 hdd0
  have hsc : (2 / (lam * period)) * (lam * period) = 2 := by field_simp
  have h2v : (2 : ℝ) • velocity r (taR D σ + (1 - lam) * sweepW' D σ
        + (2 * sweepParam t - 1) * period)
      = (2 / (lam * period)) • ((lam * period) • velocity r (taR D σ + (1 - lam) * sweepW' D σ
        + (2 * sweepParam t - 1) * period)) := by
    rw [smul_smul, hsc]
  rw [hcv, hvel, h2v, ← smul_sub, norm_smul, Real.norm_of_nonneg (by positivity)]
  have hY := smv_arith_Y (lam := lam) (w := sweepW' D σ) (dd := period - sweepW' D σ)
    hlam0 hw0 hwP hdd0 hddP
  calc (2 / (lam * period)) * ‖(lam • r (taR D σ) + (1 - lam) • r (taR D σ + sweepW' D σ)
          - r (taR D σ + (1 - lam) * sweepW' D σ))
        - (lam * period) • velocity r (taR D σ + (1 - lam) * sweepW' D σ
            + (2 * sweepParam t - 1) * period)‖
      ≤ (2 / (lam * period)) * (M * (lam * sweepW' D σ * (lam * period)
          + lam * (period - sweepW' D σ) * (lam * period + (period - sweepW' D σ)))) :=
        mul_le_mul_of_nonneg_left haux (by positivity)
    _ ≤ (2 / (lam * period)) * (M * ((lam * period + 2 * lam * (period - sweepW' D σ)
          + (period - sweepW' D σ)) * (lam * period))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hY hM0) (by positivity)
    _ = 2 * M * (lam * period + 2 * lam * (period - sweepW' D σ) + (period - sweepW' D σ)) := by
        rw [show (2 / (lam * period)) * (M * ((lam * period + 2 * lam * (period - sweepW' D σ)
              + (period - sweepW' D σ)) * (lam * period)))
            = ((2 / (lam * period)) * (lam * period)) * (M * (lam * period
              + 2 * lam * (period - sweepW' D σ) + (period - sweepW' D σ))) by ring,
          hsc]
        ring

/-- **Second chamfer zone**: sharp estimate. -/
lemma smv_cham2 {r : ℝ → Space} (hr : IsSmoothKnot r) {M : ℝ} (hM0 : 0 ≤ M)
    (hlip : ∀ x y : ℝ, ‖velocity r x - velocity r y‖ ≤ M * |x - y|)
    {d : BandArcData} (D : SweepData d) {lam σ t : ℝ} (hlam0 : 0 < lam) (hlam1 : lam < 1 / 2)
    (hu1 : ¬ sweepParam t ≤ 1 / 2) (hu2 : ¬ sweepParam t ≤ 1 / 2 + lam / 2)
    (hu3 : ¬ sweepParam t ≤ 1 - lam / 2) :
    ‖chamferVel r D lam σ t - (2 : ℝ) • velocity r (topSigma D lam σ t)‖
      ≤ 2 * M * (lam * period + 2 * lam * (period - sweepW' D σ) + (period - sweepW' D σ)) := by
  have hP : (0 : ℝ) < period := period_pos
  obtain ⟨hw0, hwP⟩ := smv_sweepW'_nonneg_le D σ
  have hdd0 : 0 ≤ period - sweepW' D σ := by linarith
  have hddP : period - sweepW' D σ ≤ period := by linarith
  have hwd : sweepW' D σ + (period - sweepW' D σ) = period := by ring
  have htb : tbR D σ = taR D σ + sweepW' D σ := by rw [sweepW']; ring
  have hψ0 : 0 ≤ 2 * sweepParam t - 2 + lam := by have := not_le.mp hu3; linarith
  have hu4 : sweepParam t < 1 := (sweepParam_mem t).2
  have hψl : 2 * sweepParam t - 2 + lam ≤ lam := by linarith
  have hlamP : lam * period ≠ 0 := by positivity
  have hV : r (taR D σ + lam * sweepW' D σ) - ((1 - lam) • r (taR D σ) + lam • r (tbR D σ))
      = r (taR D σ + lam * sweepW' D σ)
        - ((1 - lam) • r (taR D σ) + lam • r (taR D σ + sweepW' D σ)) := by
    rw [htb]
  have hcv : chamferVel r D lam σ t
      = (2 / (lam * period)) • (r (taR D σ + lam * sweepW' D σ)
          - ((1 - lam) • r (taR D σ) + lam • r (taR D σ + sweepW' D σ))) := by
    rw [chamferVel_eq_ite, if_neg hu1, if_neg hu2, if_neg hu3, chamferVelChamfer₂]
    simp only [sweepChord', sweepArc']
    rw [show (2 / lam) * (1 / period) = 2 / (lam * period) by field_simp, hV]
  have hvel : velocity r (topSigma D lam σ t)
      = velocity r (taR D σ + sweepW' D σ + (1 - lam) * (period - sweepW' D σ)
          + (2 * sweepParam t - 2 + lam) * period) :=
    smv_vel_topSigma_c2 hr D hu1 hu2 hu3
  have haux := smv_cham2_aux (r := r) hr hlip hM0 (a := taR D σ) (w := sweepW' D σ)
    (d := period - sweepW' D σ) (lam := lam) (ψ := 2 * sweepParam t - 2 + lam)
    hlam0 (by linarith) hψ0 hψl hwd hw0 hdd0
  have hsc : (2 / (lam * period)) * (lam * period) = 2 := by field_simp
  have h2v : (2 : ℝ) • velocity r (taR D σ + sweepW' D σ + (1 - lam) * (period - sweepW' D σ)
        + (2 * sweepParam t - 2 + lam) * period)
      = (2 / (lam * period)) • ((lam * period) • velocity r (taR D σ + sweepW' D σ
        + (1 - lam) * (period - sweepW' D σ) + (2 * sweepParam t - 2 + lam) * period)) := by
    rw [smul_smul, hsc]
  rw [hcv, hvel, h2v, ← smul_sub, norm_smul, Real.norm_of_nonneg (by positivity)]
  have hY := smv_arith_Y2 (lam := lam) (w := sweepW' D σ) (dd := period - sweepW' D σ)
    hlam0 (by linarith) hw0 hwP hdd0 hddP
  calc (2 / (lam * period)) * ‖(r (taR D σ + lam * sweepW' D σ)
          - ((1 - lam) • r (taR D σ) + lam • r (taR D σ + sweepW' D σ)))
        - (lam * period) • velocity r (taR D σ + sweepW' D σ
            + (1 - lam) * (period - sweepW' D σ) + (2 * sweepParam t - 2 + lam) * period)‖
      ≤ (2 / (lam * period)) * (M * ((1 - lam) * (lam * sweepW' D σ) * (lam * period)
          + lam * (lam * sweepW' D σ + (period - sweepW' D σ))
              * (lam * period + (period - sweepW' D σ)))) :=
        mul_le_mul_of_nonneg_left haux (by positivity)
    _ ≤ (2 / (lam * period)) * (M * ((lam * period + 2 * lam * (period - sweepW' D σ)
          + (period - sweepW' D σ)) * (lam * period))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hY hM0) (by positivity)
    _ = 2 * M * (lam * period + 2 * lam * (period - sweepW' D σ) + (period - sweepW' D σ)) := by
        rw [show (2 / (lam * period)) * (M * ((lam * period + 2 * lam * (period - sweepW' D σ)
              + (period - sweepW' D σ)) * (lam * period)))
            = ((2 / (lam * period)) * (lam * period)) * (M * (lam * period
              + 2 * lam * (period - sweepW' D σ) + (period - sweepW' D σ))) by ring,
          hsc]
        ring

/-! ## The arc and chord zone estimates -/

/-- The velocity of the matched point on the arc zone. -/
lemma smv_vel_topSigma_arc {r : ℝ → Space} (hr : IsSmoothKnot r) {d : BandArcData}
    (D : SweepData d) {lam σ τ : ℝ} (h1 : sweepParam τ ≤ 1 / 2) :
    velocity r (topSigma D lam σ τ)
      = velocity r (taR D σ + (lam + (1 - 2 * lam) * (2 * sweepParam τ)) * sweepW' D σ) := by
  rw [smv_velocity_topSigma_eq_wideSfrac hr D lam σ τ, wideSfrac_arc h1]

/-- The velocity of the matched point on the chord zone, reduced modulo the period. -/
lemma smv_vel_topSigma_chord {r : ℝ → Space} (hr : IsSmoothKnot r) {d : BandArcData}
    (D : SweepData d) {lam σ τ : ℝ} (h1 : ¬ sweepParam τ ≤ 1 / 2)
    (h2 : ¬ sweepParam τ ≤ 1 / 2 + lam / 2) (h3 : sweepParam τ ≤ 1 - lam / 2) :
    velocity r (topSigma D lam σ τ)
      = velocity r (taR D σ + sweepW' D σ + lam * (period - sweepW' D σ)
          + (1 - 2 * lam) * (period - sweepW' D σ)
              * ((sweepParam τ - (1 / 2 + lam / 2)) / (1 / 2 - lam)) - period) := by
  rw [smv_velocity_topSigma_eq_wideSfrac hr D lam σ τ, wideSfrac_chord h1 h2 h3]
  have h := smv_velocity_periodic hr (taR D σ + sweepW' D σ + lam * (period - sweepW' D σ)
      + (1 - 2 * lam) * (period - sweepW' D σ)
          * ((sweepParam τ - (1 / 2 + lam / 2)) / (1 / 2 - lam)) - period)
  rwa [sub_add_cancel] at h

/-- **Arc zone**: the chamfer velocity *is* the matched knot velocity. -/
lemma smv_arc {r : ℝ → Space} (hr : IsSmoothKnot r) {d : BandArcData} (D : SweepData d)
    {lam σ τ : ℝ} (h1 : sweepParam τ ≤ 1 / 2) :
    chamferVel r D lam σ τ
      = wideRho (sweepW' D σ) (period - sweepW' D σ) lam (sweepParam τ)
          • velocity r (topSigma D lam σ τ) := by
  rw [chamferVel_eq_ite, if_pos h1, chamferVelArc, wideRho_arc h1, smv_vel_topSigma_arc hr D h1]
  congr 1
  ring

/-- **Chord zone**: sharp estimate; `wideRho` is `2 d / period` there. -/
lemma smv_chord {r : ℝ → Space} (hr : IsSmoothKnot r) {M : ℝ} (hM0 : 0 ≤ M)
    (hlip : ∀ x y : ℝ, ‖velocity r x - velocity r y‖ ≤ M * |x - y|)
    {d : BandArcData} (D : SweepData d) {lam σ t : ℝ} (hlam0 : 0 < lam) (hlam1 : lam < 1 / 2)
    (hu1 : ¬ sweepParam t ≤ 1 / 2) (hu2 : ¬ sweepParam t ≤ 1 / 2 + lam / 2)
    (hu3 : sweepParam t ≤ 1 - lam / 2) :
    ‖chamferVel r D lam σ t
        - wideRho (sweepW' D σ) (period - sweepW' D σ) lam (sweepParam t)
          • velocity r (topSigma D lam σ t)‖
      ≤ M * (1 + period) * (lam + (period - sweepW' D σ))
          * wideRho (sweepW' D σ) (period - sweepW' D σ) lam (sweepParam t) := by
  have hP : (0 : ℝ) < period := period_pos
  obtain ⟨hw0, hwP⟩ := smv_sweepW'_nonneg_le D σ
  have hdd0 : 0 ≤ period - sweepW' D σ := by linarith
  have hu := sweepParam_mem t
  have hu1' : 1 / 2 < sweepParam t := not_le.mp hu1
  have hhalf : (0 : ℝ) < 1 / 2 - lam := by linarith
  have htb : tbR D σ = taR D σ + sweepW' D σ := by rw [sweepW']; ring
  -- the loop fraction of the chord zone
  have hξ0 : 0 ≤ (sweepParam t - (1 / 2 + lam / 2)) / (1 / 2 - lam) :=
    div_nonneg (by linarith [not_le.mp hu2]) hhalf.le
  have hξ1 : (sweepParam t - (1 / 2 + lam / 2)) / (1 / 2 - lam) ≤ 1 := by
    rw [div_le_one hhalf]; linarith
  -- the reduced matched point
  set c : ℝ := taR D σ + sweepW' D σ + lam * (period - sweepW' D σ)
      + (1 - 2 * lam) * (period - sweepW' D σ)
          * ((sweepParam t - (1 / 2 + lam / 2)) / (1 / 2 - lam)) - period with hc
  have hvel : velocity r (topSigma D lam σ t) = velocity r c :=
    smv_vel_topSigma_chord hr D hu1 hu2 hu3
  -- the two distance bounds to the reduced matched point
  have hca : |c - taR D σ| ≤ period - sweepW' D σ := by
    rw [hc]
    have hrew : taR D σ + sweepW' D σ + lam * (period - sweepW' D σ)
          + (1 - 2 * lam) * (period - sweepW' D σ)
              * ((sweepParam t - (1 / 2 + lam / 2)) / (1 / 2 - lam)) - period - taR D σ
        = (period - sweepW' D σ)
            * (lam - 1 + (1 - 2 * lam)
              * ((sweepParam t - (1 / 2 + lam / 2)) / (1 / 2 - lam))) := by ring
    rw [hrew, abs_mul, abs_of_nonneg hdd0]
    have hb : |lam - 1 + (1 - 2 * lam)
        * ((sweepParam t - (1 / 2 + lam / 2)) / (1 / 2 - lam))| ≤ 1 := by
      rw [abs_le]
      constructor
      · have h1 : 0 ≤ (1 - 2 * lam)
            * ((sweepParam t - (1 / 2 + lam / 2)) / (1 / 2 - lam)) :=
          mul_nonneg (by linarith) hξ0
        linarith
      · have h1 : (1 - 2 * lam) * ((sweepParam t - (1 / 2 + lam / 2)) / (1 / 2 - lam))
            ≤ 1 - 2 * lam := mul_le_of_le_one_right (by linarith) hξ1
        linarith
    exact mul_le_of_le_one_right hdd0 hb
  have hcb : |c - (taR D σ - (period - sweepW' D σ))| ≤ period - sweepW' D σ := by
    rw [hc]
    have hrew : taR D σ + sweepW' D σ + lam * (period - sweepW' D σ)
          + (1 - 2 * lam) * (period - sweepW' D σ)
              * ((sweepParam t - (1 / 2 + lam / 2)) / (1 / 2 - lam)) - period
          - (taR D σ - (period - sweepW' D σ))
        = (period - sweepW' D σ)
            * (lam + (1 - 2 * lam)
              * ((sweepParam t - (1 / 2 + lam / 2)) / (1 / 2 - lam))) := by ring
    rw [hrew, abs_mul, abs_of_nonneg hdd0]
    have hb : |lam + (1 - 2 * lam)
        * ((sweepParam t - (1 / 2 + lam / 2)) / (1 / 2 - lam))| ≤ 1 := by
      rw [abs_of_nonneg (by
        have h1 : 0 ≤ (1 - 2 * lam)
            * ((sweepParam t - (1 / 2 + lam / 2)) / (1 / 2 - lam)) :=
          mul_nonneg (by linarith) hξ0
        linarith)]
      have h1 : (1 - 2 * lam) * ((sweepParam t - (1 / 2 + lam / 2)) / (1 / 2 - lam))
          ≤ 1 - 2 * lam := mul_le_of_le_one_right (by linarith) hξ1
      linarith
    exact mul_le_of_le_one_right hdd0 hb
  -- the chord estimate at the reduced matched point
  have hcorr : ‖(r (taR D σ) - r (taR D σ - (period - sweepW' D σ)))
        - (period - sweepW' D σ) • velocity r c‖ ≤ M * (period - sweepW' D σ) ^ 2 := by
    have hpq : taR D σ - (period - sweepW' D σ) ≤ taR D σ := by linarith
    have h := smv_chord_vel_bound hr hlip hM0 hpq hdd0 hcb hca
    have hq : taR D σ - (taR D σ - (period - sweepW' D σ)) = period - sweepW' D σ := by ring
    rw [hq] at h
    simpa only [pow_two, mul_assoc] using h
  -- the chamfer velocity in chord form
  have hper : r (tbR D σ) = r (taR D σ - (period - sweepW' D σ)) := by
    rw [htb]
    have h : taR D σ + sweepW' D σ = taR D σ - (period - sweepW' D σ) + period := by ring
    rw [h]
    exact hr.periodic _
  have hcv : chamferVel r D lam σ t
      = (2 / period) • (r (taR D σ) - r (taR D σ - (period - sweepW' D σ))) := by
    rw [chamferVel_eq_ite, if_neg hu1, if_neg hu2, if_pos hu3, chamferVelChord]
    have hscalar : -((1 - 2 * lam) / ((1 / 2 - lam) * period)) = -(2 / period) := by
      rw [show (1 : ℝ) - 2 * lam = 2 * (1 / 2 - lam) by ring,
          show 2 * (1 / 2 - lam) = (1 / 2 - lam) * 2 by ring,
          mul_div_mul_left _ _ (by linarith : (1 : ℝ) / 2 - lam ≠ 0)]
    rw [hscalar, hper, neg_smul, ← smul_neg, neg_sub]
  have hρ : wideRho (sweepW' D σ) (period - sweepW' D σ) lam (sweepParam t)
      = 2 * (period - sweepW' D σ) / period := by
    rw [wideRho_chord hu1 hu2 hu3, show (1 : ℝ) - 2 * lam = 2 * (1 / 2 - lam) by ring]
    rw [show 2 * (1 / 2 - lam) * (period - sweepW' D σ) / (period * (1 / 2 - lam))
        = 2 * (period - sweepW' D σ) / period by
      rw [show 2 * (1 / 2 - lam) * (period - sweepW' D σ)
            = (1 / 2 - lam) * (2 * (period - sweepW' D σ)) by ring,
          show period * (1 / 2 - lam) = (1 / 2 - lam) * period by ring,
          mul_div_mul_left _ _ (by linarith : (1 : ℝ) / 2 - lam ≠ 0)]]
  have hmain : ‖chamferVel r D lam σ t
        - wideRho (sweepW' D σ) (period - sweepW' D σ) lam (sweepParam t)
          • velocity r (topSigma D lam σ t)‖
      ≤ (2 / period) * (M * (period - sweepW' D σ) ^ 2) := by
    rw [hcv, hvel, hρ]
    rw [show (2 * (period - sweepW' D σ) / period) • velocity r c
        = (2 / period) • ((period - sweepW' D σ) • velocity r c) by
      rw [smul_smul]
      congr 1
      rw [div_mul_eq_mul_div]]
    rw [← smul_sub]
    rw [norm_smul, Real.norm_of_nonneg (by positivity)]
    exact mul_le_mul_of_nonneg_left hcorr (by positivity)
  refine hmain.trans ?_
  rw [hρ]
  have hle : period - sweepW' D σ ≤ (1 + period) * (lam + (period - sweepW' D σ)) := by
    nlinarith [hP, hlam0, hdd0]
  have hMdd : (0 : ℝ) ≤ 2 * M * (period - sweepW' D σ) :=
    mul_nonneg (mul_nonneg (by norm_num) hM0) hdd0
  have hkey := mul_le_mul_of_nonneg_left hle hMdd
  calc (2 / period) * (M * (period - sweepW' D σ) ^ 2)
      = (2 * M * (period - sweepW' D σ) * (period - sweepW' D σ)) / period := by ring
    _ ≤ (2 * M * (period - sweepW' D σ) * ((1 + period) * (lam + (period - sweepW' D σ))))
          / period := div_le_div_of_nonneg_right hkey (le_of_lt hP)
    _ = M * (1 + period) * (lam + (period - sweepW' D σ))
          * (2 * (period - sweepW' D σ) / period) := by ring

/-! ## The theorem -/

theorem sweepMatchRawVel {r : ℝ → LeanEval.KnotTheory.Quadrisecant.Space}
    (hr : LeanEval.KnotTheory.Quadrisecant.IsSmoothKnot r) {M₂ : ℝ} (hM₂0 : 0 ≤ M₂)
    (hM₂ : ∀ x y : ℝ,
      ‖LeanEval.KnotTheory.Quadrisecant.velocity r x - LeanEval.KnotTheory.Quadrisecant.velocity r y‖
        ≤ M₂ * |x - y|)
    {d : LeanEval.KnotTheory.Quadrisecant.BandArcData} (D : Work.Drive.SweepData d)
    {θ : ℝ} (hθ : 0 < θ) (hθp : θ ≤ LeanEval.KnotTheory.Quadrisecant.period) :
    ∀ (σ lam τ : ℝ), 1 / 2 ≤ σ → σ < 1 → 0 < lam → lam < 1 / 2 →
      LeanEval.KnotTheory.Quadrisecant.period - Work.Drive.sweepW' D σ ≤ θ * lam →
      ‖Work.Drive.chamferVel r D lam σ τ -
          Work.Drive.wideRho (Work.Drive.sweepW' D σ)
            (LeanEval.KnotTheory.Quadrisecant.period - Work.Drive.sweepW' D σ) lam
            (Work.Drive.sweepParam τ) •
          LeanEval.KnotTheory.Quadrisecant.velocity r (Work.Drive.topSigma D lam σ τ)‖
        ≤ M₂ * (1 + LeanEval.KnotTheory.Quadrisecant.period) *
            (lam + (LeanEval.KnotTheory.Quadrisecant.period - Work.Drive.sweepW' D σ)) *
          Work.Drive.wideRho (Work.Drive.sweepW' D σ)
            (LeanEval.KnotTheory.Quadrisecant.period - Work.Drive.sweepW' D σ) lam
            (Work.Drive.sweepParam τ) := by
  intro σ lam τ hσ0 hσ1 hlam0 hlam1 hdθ
  obtain ⟨hw0, hwP⟩ := smv_sweepW'_nonneg_le D σ
  have hdd0 : 0 ≤ period - sweepW' D σ := by linarith
  have hddP : period - sweepW' D σ ≤ period := by linarith
  have hρ0 : 0 ≤ M₂ * (1 + period) * (lam + (period - sweepW' D σ)) :=
    mul_nonneg (mul_nonneg hM₂0 (by linarith [period_pos])) (by linarith)
  by_cases h1 : sweepParam τ ≤ 1 / 2
  · rw [smv_arc hr D h1, sub_self, norm_zero]
    refine mul_nonneg hρ0 ?_
    rw [wideRho_arc h1]
    exact mul_nonneg (by linarith)
      (div_nonneg (mul_nonneg (by norm_num) hw0) (le_of_lt period_pos))
  · by_cases h2 : sweepParam τ ≤ 1 / 2 + lam / 2
    · rw [wideRho_chamfer₁ h1 h2]
      exact (smv_cham1 hr hM₂0 hM₂ D hlam0 hlam1 h1 h2).trans
        (smv_arith_cham hM₂0 hlam0 (le_of_lt hlam1) hw0 hwP hdd0 hddP)
    · by_cases h3 : sweepParam τ ≤ 1 - lam / 2
      · exact smv_chord hr hM₂0 hM₂ D hlam0 hlam1 h1 h2 h3
      · rw [wideRho_chamfer₂ h1 h2 h3]
        exact (smv_cham2 hr hM₂0 hM₂ D hlam0 hlam1 h1 h2 h3).trans
          (smv_arith_cham hM₂0 hlam0 (le_of_lt hlam1) hw0 hwP hdd0 hddP)

end Work.Drive
