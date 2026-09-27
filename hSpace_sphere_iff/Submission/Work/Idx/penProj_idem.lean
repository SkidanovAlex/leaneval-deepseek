import Mathlib
import Submission.Work.KT.Idx.PenDefs
import Submission.Work.KT.Fund.circleIntegral_inv_sub_eq_zero_rev

namespace Work.Idx

open Matrix MeasureTheory intervalIntegral
open scoped Topology Interval
open Work.KT.Idx

noncomputable section

variable {R : Type*} [NormedRing R] [NormedAlgebra ℂ R] [CompleteSpace R]

/-! ## The resolvent identity of the pencil `z ↦ z • A + B`

Everything below is stated for an arbitrary complex Banach algebra `R`, so that it applies to
`Matrix (Fin N) (Fin N) C(X, ℂ)` with the `L∞` operator norm. -/

/-- **Resolvent identity of the pencil.** For `z`, `w` at which the pencil `z ↦ z • A + B` is a
unit, `(z - w) • ((zA+B)⁻¹ A (wA+B)⁻¹) = (wA+B)⁻¹ - (zA+B)⁻¹`. -/
theorem penRes_mul (A B : R) {z w : ℂ}
    (hz : IsUnit (z • A + B)) (hw : IsUnit (w • A + B)) :
    (z - w) • (pRes A B z * A * pRes A B w) = pRes A B w - pRes A B z := by
  change (z - w) • (Ring.inverse (z • A + B) * A * Ring.inverse (w • A + B)) =
    Ring.inverse (w • A + B) - Ring.inverse (z • A + B)
  have hsub : (z • A + B) - (w • A + B) = (z - w) • A := by
    rw [add_sub_add_right_eq_sub, ← sub_smul]
  have e1 : Ring.inverse (z • A + B) * (z • A + B) * Ring.inverse (w • A + B) =
      Ring.inverse (w • A + B) := by
    rw [Ring.inverse_mul_cancel _ hz, one_mul]
  have e2 : Ring.inverse (z • A + B) * (w • A + B) * Ring.inverse (w • A + B) =
      Ring.inverse (z • A + B) := by
    rw [mul_assoc, Ring.mul_inverse_cancel _ hw, mul_one]
  have h1 : Ring.inverse (z • A + B) * ((z • A + B) - (w • A + B)) *
      Ring.inverse (w • A + B) = Ring.inverse (w • A + B) - Ring.inverse (z • A + B) := by
    rw [mul_sub, sub_mul, e1, e2]
  rw [← h1, hsub, ← smul_mul_assoc, ← mul_smul_comm]

/-- The same identity multiplied by `A` on the right, i.e. for the integrand `(zA+B)⁻¹ A`. -/
theorem penResA_mul (A B : R) {z w : ℂ}
    (hz : IsUnit (z • A + B)) (hw : IsUnit (w • A + B)) :
    (z - w) • (pResA A B z * pResA A B w) = pResA A B w - pResA A B z := by
  have h := congrArg (fun t : R => t * A) (penRes_mul A B hz hw)
  simp only [pResA, smul_mul_assoc, sub_mul] at h ⊢
  simpa only [mul_assoc] using h

/-- The resolvent identity in the form in which it enters the two-circle computation:
`(zA+B)⁻¹ A (wA+B)⁻¹ A = (z - w)⁻¹ • ((wA+B)⁻¹ A - (zA+B)⁻¹ A)` for `z ≠ w`. -/
theorem penResA_eq (A B : R) {z w : ℂ} (hzw : w ≠ z)
    (hz : IsUnit (z • A + B)) (hw : IsUnit (w • A + B)) :
    pResA A B z * pResA A B w = (z - w)⁻¹ • (pResA A B w - pResA A B z) := by
  have h := penResA_mul A B hz hw
  have hz' : z - w ≠ 0 := sub_ne_zero.mpr (Ne.symm hzw)
  calc pResA A B z * pResA A B w
      = (z - w)⁻¹ • ((z - w) • (pResA A B z * pResA A B w)) := by
        rw [smul_smul, inv_mul_cancel₀ hz', one_smul]
    _ = (z - w)⁻¹ • (pResA A B w - pResA A B z) := by rw [h]

/-- The pencil resolvent is continuous on a circle on which the pencil is invertible. -/
theorem penRes_continuousOn_sphere (A B : R) {r : ℝ}
    (hunit : ∀ z ∈ Metric.sphere (0:ℂ) r, IsUnit (z • A + B)) :
    ContinuousOn (pResA A B) (Metric.sphere (0:ℂ) r) := by
  have hunits : ContinuousOn Ring.inverse {x : R | IsUnit x} := fun x hx => by
    simpa only [IsUnit.unit_spec hx] using
      (NormedRing.inverse_continuousAt hx.unit).continuousWithinAt
  have hlin : Continuous fun z : ℂ => z • A + B :=
    (continuous_id.smul continuous_const).add continuous_const
  have h1 : ContinuousOn (fun z : ℂ => Ring.inverse (z • A + B)) (Metric.sphere (0:ℂ) r) :=
    hunits.comp hlin.continuousOn hunit
  exact h1.mul continuousOn_const

/-- Circle integrability of the pencil integrand on a circle of invertibility. -/
theorem penResA_circleIntegrable (A B : R) {r : ℝ} (hr : 0 ≤ r)
    (hunit : ∀ z ∈ Metric.sphere (0:ℂ) r, IsUnit (z • A + B)) :
    CircleIntegrable (pResA A B) 0 r :=
  (penRes_continuousOn_sphere A B hunit).circleIntegrable hr

/-! ## The gap around the unit circle -/

/-- **The pencil gap.** If the pencil `z ↦ z • A + B` is invertible on the whole unit circle, then
it is invertible on an annulus `1 - ε ≤ ‖z‖ ≤ 1 + ε` around it.

Proof: the set `U = {z | z • A + B is a unit}` is open (the units of a Banach algebra are open and
`z ↦ z • A + B` is continuous) and contains the compact unit circle, so it contains a whole
thickening of the circle. -/
theorem pen_gap (A B : R) (hunit : ∀ z : ℂ, ‖z‖ = 1 → IsUnit (z • A + B)) :
    ∃ ε : ℝ, 0 < ε ∧ ε < 1 ∧
      ∀ z : ℂ, 1 - ε ≤ ‖z‖ → ‖z‖ ≤ 1 + ε → IsUnit (z • A + B) := by
  have hcont : Continuous fun z : ℂ => z • A + B :=
    (continuous_id.smul continuous_const).add continuous_const
  have hopen : IsOpen {z : ℂ | IsUnit (z • A + B)} := Units.isOpen.preimage hcont
  have hS : Metric.sphere (0:ℂ) 1 ⊆ {z : ℂ | IsUnit (z • A + B)} := fun z hz =>
    hunit z (by simpa [dist_eq_norm] using Metric.mem_sphere.mp hz)
  obtain ⟨δ, hδ0, hδ⟩ := (isCompact_sphere (0:ℂ) 1).exists_thickening_subset_open hopen hS
  refine ⟨min (δ / 2) (1 / 2), lt_min (by linarith) (by norm_num),
    lt_of_le_of_lt (min_le_right _ _) (by norm_num), ?_⟩
  intro z hzl hzr
  have hεδ : min (δ / 2) (1 / 2) < δ := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hzpos : 0 < ‖z‖ := by
    have h1 : min (δ / 2) (1 / 2) ≤ 1 / 2 := min_le_right _ _
    linarith
  have hmem : (‖z‖)⁻¹ • z ∈ Metric.sphere (0:ℂ) 1 := by
    rw [Metric.mem_sphere, dist_eq_norm, sub_zero, norm_smul, Real.norm_eq_abs, abs_inv,
      abs_of_nonneg (norm_nonneg z), inv_mul_cancel₀ (ne_of_gt hzpos)]
  have hdist : dist z ((‖z‖)⁻¹ • z) < δ := by
    have hzsub : z - (‖z‖)⁻¹ • z = (1 - (‖z‖)⁻¹) • z := by rw [sub_smul, one_smul]
    have hkey : |1 - (‖z‖)⁻¹| * ‖z‖ = |‖z‖ - 1| := by
      nth_rewrite 2 [← abs_of_nonneg (norm_nonneg z)]
      rw [← abs_mul, sub_mul, one_mul, inv_mul_cancel₀ (ne_of_gt hzpos)]
    rw [dist_eq_norm, hzsub, norm_smul, Real.norm_eq_abs, hkey, abs_lt]
    constructor <;> linarith [hzl, hzr, hεδ]
  exact hδ (Metric.mem_thickening_iff.mpr ⟨_, hmem, hdist⟩)


/-! ## Deformation invariance of the pencil circle integral -/

/-- **Deformation invariance.** If the pencil is invertible on the closed annulus
`r ≤ ‖z‖ ≤ R'` then the integrals of `(zA+B)⁻¹ A` over the two boundary circles agree. This is
Cauchy's theorem on an annulus. -/
theorem pen_deform (A B : R) {r R' : ℝ} (hr : 0 < r) (hrR : r ≤ R')
    (hunit : ∀ z : ℂ, r ≤ ‖z‖ → ‖z‖ ≤ R' → IsUnit (z • A + B)) :
    (∮ z in C(0, R'), pResA A B z) = ∮ z in C(0, r), pResA A B z := by
  have hcont : Continuous fun z : ℂ => z • A + B :=
    (continuous_id.smul continuous_const).add continuous_const
  have hunits : ContinuousOn Ring.inverse {x : R | IsUnit x} := fun x hx => by
    simpa only [IsUnit.unit_spec hx] using
      (NormedRing.inverse_continuousAt hx.unit).continuousWithinAt
  -- the closed annulus lies in the set of invertibility
  have hmem : ∀ z ∈ (Metric.closedBall (0:ℂ) R' \ Metric.ball (0:ℂ) r),
      IsUnit (z • A + B) := by
    intro z hz
    have hge : r ≤ ‖z‖ := by
      have h2 : ¬ (dist z 0 < r) := by
        simpa [Metric.mem_ball, dist_zero_right] using hz.2
      simpa [dist_zero_right] using not_lt.mp h2
    have hle : ‖z‖ ≤ R' := by
      have h1 : dist z 0 ≤ R' := by simpa [Metric.mem_closedBall, dist_zero_right] using hz.1
      simpa [dist_zero_right] using h1
    exact hunit z hge hle
  have hcontOn : ContinuousOn (pResA A B)
      (Metric.closedBall (0:ℂ) R' \ Metric.ball (0:ℂ) r) :=
    ((hunits.comp hcont.continuousOn hmem)).mul continuousOn_const
  have hdiff : ∀ z ∈ (Metric.ball (0:ℂ) R' \ Metric.closedBall (0:ℂ) r),
      DifferentiableAt ℂ (pResA A B) z := by
    intro z hz
    have hge : r ≤ ‖z‖ := by
      have h2 : ¬ (dist z 0 ≤ r) := by
        simpa [Metric.mem_closedBall, dist_zero_right] using hz.2
      have h3 : r < dist z 0 := not_le.mp h2
      simpa [dist_zero_right] using h3.le
    have hle : ‖z‖ ≤ R' := by
      have h1 : dist z 0 < R' := by simpa [Metric.mem_ball, dist_zero_right] using hz.1
      simpa [dist_zero_right] using h1.le
    have hg : DifferentiableAt ℂ (fun y : ℂ => y • A + B) z :=
      (differentiableAt_id.smul_const A).add_const B
    exact (hg.inverse (hunit z hge hle)).mul_const A
  exact Complex.circleIntegral_eq_of_differentiable_on_annulus_off_countable hr hrR
    Set.countable_empty hcontOn (fun z hz => hdiff z hz.1)

/-! ## Fubini for the pencil kernel -/

/-- Fubini for the iterated circle integral of the kernel `(z - w)⁻¹ • (wA+B)⁻¹ A`. -/
theorem pen_swap (A B : R) {r R' : ℝ} (hr : 0 < r) (hR : 0 < R') (hrR : r < R')
    (hunit : ∀ z : ℂ, r ≤ ‖z‖ → ‖z‖ ≤ R' → IsUnit (z • A + B)) :
    (∮ z in C(0, R'), ∮ w in C(0, r), (z - w)⁻¹ • pResA A B w) =
      ∮ w in C(0, r), ∮ z in C(0, R'), (z - w)⁻¹ • pResA A B w := by
  refine Work.KT.Fund.circleIntegral_swap (fun z w : ℂ => (z - w)⁻¹ • pResA A B w)
    hR.le hr.le ?_
  have hne : ∀ p ∈ (Metric.sphere (0:ℂ) R' ×ˢ Metric.sphere (0:ℂ) r), p.1 - p.2 ≠ 0 := by
    intro p hp hcon
    obtain ⟨hp1, hp2⟩ := Set.mem_prod.mp hp
    have h1 : ‖p.1‖ = R' := by simpa [dist_eq_norm] using Metric.mem_sphere.mp hp1
    have h2 : ‖p.2‖ = r := by simpa [dist_eq_norm] using Metric.mem_sphere.mp hp2
    have : R' = r := by rw [← h1, sub_eq_zero.mp hcon, h2]
    exact absurd this (ne_of_gt hrR)
  have h1 : ContinuousOn (fun p : ℂ × ℂ => (p.1 - p.2)⁻¹)
      (Metric.sphere (0:ℂ) R' ×ˢ Metric.sphere (0:ℂ) r) :=
    (continuous_fst.sub continuous_snd).continuousOn.inv₀ hne
  have h2 : ContinuousOn (fun p : ℂ × ℂ => pResA A B p.2)
      (Metric.sphere (0:ℂ) R' ×ˢ Metric.sphere (0:ℂ) r) := by
    refine (penRes_continuousOn_sphere A B ?_).comp continuous_snd.continuousOn
      (fun p hp => (Set.mem_prod.mp hp).2)
    intro w hw
    have h2 : ‖w‖ = r := by simpa [dist_eq_norm] using Metric.mem_sphere.mp hw
    exact hunit w (by rw [h2]) (by rw [h2]; exact hrR.le)
  rw [show Function.uncurry (fun z w : ℂ => (z - w)⁻¹ • pResA A B w)
      = (fun p : ℂ × ℂ => (p.1 - p.2)⁻¹ • pResA A B p.2) from rfl]
  exact h1.smul h2

/-! ## The two-circle computation -/

/-- The product of two circle integrals as a double integral. -/
theorem pCirc_mul_pCirc (A B : R) {r R' : ℝ} (hr : 0 ≤ r) (hR : 0 ≤ R')
    (hintr : CircleIntegrable (pResA A B) 0 r)
    (hintR : CircleIntegrable (pResA A B) 0 R') :
    pCirc A B R' * pCirc A B r =
      ∮ z in C(0, R'), ∮ w in C(0, r), pResA A B z * pResA A B w := by
  rw [pCirc, pCirc, ← Work.KT.Fund.circleIntegral_mul_const (∮ w in C(0, r), pResA A B w)
    (pResA A B) 0 R' hintR]
  refine circleIntegral.integral_congr hR (fun z _ => ?_)
  exact (Work.KT.Fund.circleIntegral_const_mul (pResA A B z) (pResA A B) 0 r hintr).symm

/-- **Idempotency of the pencil projection** for an arbitrary complex Banach algebra `R`. -/
theorem penProj_idem_gen (A B : R) (hunit : ∀ z : ℂ, ‖z‖ = 1 → IsUnit (z • A + B)) :
    penProj A B * penProj A B = penProj A B := by
  obtain ⟨ε, hε0, hε1, hann⟩ := pen_gap A B hunit
  set r : ℝ := 1 - ε / 2 with hr
  set R' : ℝ := 1 + ε / 2 with hR
  have hr0 : 0 < r := by rw [hr]; linarith
  have hr1 : r < 1 := by rw [hr]; linarith
  have hR1 : 1 < R' := by rw [hR]; linarith
  have hrR : r < R' := lt_trans hr1 hR1
  have hann' : ∀ z : ℂ, r ≤ ‖z‖ → ‖z‖ ≤ R' → IsUnit (z • A + B) := by
    intro z h1 h2
    exact hann z (by rw [hr] at h1; linarith) (by rw [hR] at h2; linarith)
  have memR : ∀ z : ℂ, z ∈ Metric.sphere (0:ℂ) R' → ‖z‖ = R' := fun z hz =>
    by simpa [dist_eq_norm] using Metric.mem_sphere.mp hz
  have memr : ∀ z : ℂ, z ∈ Metric.sphere (0:ℂ) r → ‖z‖ = r := fun z hz =>
    by simpa [dist_eq_norm] using Metric.mem_sphere.mp hz
  -- deformation invariance: the integral does not depend on the radius in the annulus
  have hd1 : pCirc A B 1 = pCirc A B r :=
    pen_deform A B (r := r) (R' := 1) hr0 (le_of_lt hr1)
      (fun z h1 h2 => hann' z h1 (le_trans h2 (le_of_lt hR1)))
  have hd2 : pCirc A B 1 = pCirc A B R' :=
    (pen_deform A B (r := 1) (R' := R') zero_lt_one (le_of_lt hR1)
      (fun z h1 h2 => hann' z (le_trans (le_of_lt hr1) h1) h2)).symm
  have hpr : penProj A B = (2 * Real.pi * Complex.I)⁻¹ • pCirc A B r := by rw [penProj, hd1]
  have hPR : penProj A B = (2 * Real.pi * Complex.I)⁻¹ • pCirc A B R' := by rw [penProj, hd2]
  have hcR : CircleIntegrable (pResA A B) 0 R' :=
    penResA_circleIntegrable A B (le_of_lt (lt_trans hr0 hrR))
      (fun z hz => hann' z (by rw [memR z hz]; exact hrR.le) (by rw [memR z hz]))
  have hcr : CircleIntegrable (pResA A B) 0 r :=
    penResA_circleIntegrable A B hr0.le
      (fun z hz => hann' z (by rw [memr z hz]) (by rw [memr z hz]; exact hrR.le))
  -- the resolvent identity, pointwise on the two circles
  have hpt : ∀ z ∈ Metric.sphere (0:ℂ) R', ∀ w ∈ Metric.sphere (0:ℂ) r,
      pResA A B z * pResA A B w = (z - w)⁻¹ • (pResA A B w - pResA A B z) := by
    intro z hz w hw
    have hzR : ‖z‖ = R' := memR z hz
    have hwr : ‖w‖ = r := memr w hw
    have hzw : w ≠ z := by
      intro h
      have : R' = r := by rw [← hzR, ← h, hwr]
      exact absurd this (ne_of_gt hrR)
    exact penResA_eq A B hzw (hann' z (by rw [hzR]; exact hrR.le) (by rw [hzR]))
      (hann' w (by rw [hwr]) (by rw [hwr]; exact hrR.le))
  -- the singularity `z = w` lies outside the `w`-circle, so the second term drops out
  have hzero : ∀ z ∈ Metric.sphere (0:ℂ) R', (∮ w in C(0, r), (z - w)⁻¹) = 0 := by
    intro z hz
    exact Work.KT.Fund.circleIntegral_inv_sub_eq_zero_rev hr0 (by rw [memR z hz]; exact hrR)
  have hinner : ∀ z ∈ Metric.sphere (0:ℂ) R',
      (∮ w in C(0, r), pResA A B z * pResA A B w)
        = (∮ w in C(0, r), (z - w)⁻¹ • pResA A B w) := by
    intro z hz
    have hne : ∀ w ∈ Metric.sphere (0:ℂ) r, z - w ≠ 0 := by
      intro w hw hcon
      have hwr : ‖w‖ = r := memr w hw
      have : R' = r := by rw [← memR z hz, sub_eq_zero.mp hcon, hwr]
      exact absurd this (ne_of_gt hrR)
    have hcont_res : ContinuousOn (fun w : ℂ => (z - w)⁻¹) (Metric.sphere (0:ℂ) r) :=
      (continuousOn_const.sub continuousOn_id).inv₀ hne
    have hint1 : CircleIntegrable (fun w : ℂ => (z - w)⁻¹ • pResA A B w) 0 r :=
      (hcont_res.smul (penRes_continuousOn_sphere A B (fun w hw =>
        hann' w (by rw [memr w hw]) (by rw [memr w hw]; exact hrR.le)))).circleIntegrable hr0.le
    have hint2 : CircleIntegrable (fun w : ℂ => (z - w)⁻¹ • pResA A B z) 0 r :=
      (hcont_res.smul continuousOn_const).circleIntegrable hr0.le
    rw [circleIntegral.integral_congr hr0.le (fun w hw => by rw [hpt z hz w hw, smul_sub])]
    rw [circleIntegral.integral_sub hint1 hint2]
    rw [circleIntegral.integral_smul_const (fun w => (z - w)⁻¹) (pResA A B z)]
    rw [hzero z hz, zero_smul, sub_zero]
  have houter : (∮ z in C(0, R'), ∮ w in C(0, r), pResA A B z * pResA A B w)
      = ∮ z in C(0, R'), ∮ w in C(0, r), (z - w)⁻¹ • pResA A B w :=
    circleIntegral.integral_congr (le_of_lt (lt_trans hr0 hrR)) (fun z hz => hinner z hz)
  -- the inner `z`-integral is now Cauchy's formula: `z = w` is inside the `z`-circle
  have hfill : ∀ w ∈ Metric.sphere (0:ℂ) r,
      (∮ z in C(0, R'), (z - w)⁻¹ • pResA A B w) =
        (2 * Real.pi * Complex.I) • pResA A B w := by
    intro w hw
    rw [circleIntegral.integral_smul_const (fun z => (z - w)⁻¹) (pResA A B w)]
    congr 1
    have hwr : ‖w‖ = r := memr w hw
    have hball : w ∈ Metric.ball (0:ℂ) R' := by
      rw [Metric.mem_ball, dist_zero_right, hwr]; exact hrR
    exact circleIntegral.integral_sub_inv_of_mem_ball hball
  have hswap := pen_swap A B (r := r) (R' := R') hr0 (lt_trans hr0 hrR) hrR hann'
  have htail : (∮ w in C(0, r), ∮ z in C(0, R'), (z - w)⁻¹ • pResA A B w)
      = (2 * Real.pi * Complex.I) • pCirc A B r := by
    rw [circleIntegral.integral_congr hr0.le (fun w hw => hfill w hw),
      circleIntegral.integral_smul]
    rfl
  have hU : (∮ z in C(0, R'), ∮ w in C(0, r), pResA A B z * pResA A B w)
      = (2 * Real.pi * Complex.I) • pCirc A B r := by
    rw [houter, hswap, htail]
  have hsq : penProj A B * penProj A B =
      ((2 * Real.pi * Complex.I)⁻¹ * (2 * Real.pi * Complex.I)⁻¹) •
        (pCirc A B R' * pCirc A B r) := by
    nth_rewrite 1 [hPR]
    nth_rewrite 1 [hpr]
    rw [smul_mul_smul]
  have hcc : ((2 * Real.pi * Complex.I)⁻¹ * (2 * Real.pi * Complex.I)⁻¹) *
      (2 * Real.pi * Complex.I) = (2 * Real.pi * Complex.I)⁻¹ := by
    rw [mul_assoc, inv_mul_cancel₀ Complex.two_pi_I_ne_zero, mul_one]
  calc penProj A B * penProj A B
      = ((2 * Real.pi * Complex.I)⁻¹ * (2 * Real.pi * Complex.I)⁻¹) •
          (pCirc A B R' * pCirc A B r) := hsq
    _ = ((2 * Real.pi * Complex.I)⁻¹ * (2 * Real.pi * Complex.I)⁻¹) •
          ((2 * Real.pi * Complex.I) • pCirc A B r) := by
        rw [pCirc_mul_pCirc A B (r := r) (R' := R') hr0.le (le_of_lt (lt_trans hr0 hrR)) hcr hcR,
          hU]
    _ = (2 * Real.pi * Complex.I)⁻¹ • pCirc A B r := by rw [smul_smul, hcc]
    _ = penProj A B := hpr.symm

/-- **Idempotency of the Riesz projection of a matrix pencil.** For a matrix pencil `z ↦ z • A + B`
over `C(X, ℂ)` that is invertible on the unit circle, the projection
`Work.KT.Idx.matPenProj X A B = (2πi)⁻¹ ∮_{|z|=1} (zA+B)⁻¹ A dz` is idempotent.  This is the
fundamental property of the index bundle of the Toeplitz family (Hatcher, *Vector Bundles and
K-Theory* §2.1, the projection `E₊` of Prop. 2.7). -/
theorem penProj_idem (X : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X]
    {N : ℕ} (A B : Matrix (Fin N) (Fin N) C(X, ℂ))
    (hunit : ∀ z : ℂ, ‖z‖ = 1 → IsUnit (z • A + B)) :
    Work.KT.Idx.matPenProj X A B * Work.KT.Idx.matPenProj X A B =
      Work.KT.Idx.matPenProj X A B := by
  have h := @penProj_idem_gen (Matrix (Fin N) (Fin N) C(X, ℂ)) Matrix.linftyOpNormedRing
    Matrix.linftyOpNormedAlgebra (Matrix.instCompleteSpace (Fin N) (Fin N) (C(X, ℂ))) A B hunit
  simpa only [Work.KT.Idx.matPenProj] using h

end

end Work.Idx
