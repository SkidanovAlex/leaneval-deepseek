/-
# `Work.LWP.BiotSavart.nearField_bound` — the near-field bound for the Biot–Savart operator

For a vorticity `ω` bounded by `M ≥ 0` and supported in the closed ball of radius `R ≥ 0`
about the origin, the Newtonian-potential Biot–Savart field is bounded by `C · M · R`
*everywhere*, with no restriction on `‖x‖`:

  `‖biotSavart ω x‖ ≤ C · M · R`.

Far from the origin this is `Work.LWP.BiotSavart.farField_decay_const`
(`‖biotSavart ω x‖ ≤ (4/3) M R³/‖x‖²` for `2R ≤ ‖x‖`).  Near the origin the kernel singularity
is integrated against the *finite radius* of the support: with `‖x‖ ≤ 2R`, the support is
contained in the ball of radius `3R` about `x`, and for `‖y‖ ≤ R`

  `‖(‖x-y‖³)⁻¹ • (ω y × (x-y))‖ ≤ M ‖x-y‖⁻²`,

so `‖biotSavart ω x‖ ≤ (4π)⁻¹ M ∫_{‖y‖≤R} ‖x-y‖⁻² dy ≤ (4π)⁻¹ M · 4π·3R = 3 M R`.

The constant `3` is taken for the theorem: it dominates the near-field estimate and also the
far-field one (`(4/3) M R³/‖x‖² ≤ M R/3` for `2R ≤ ‖x‖`).
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.LinearAlgebra.CrossProduct
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Submission.Work.LWP.Defs
import Submission.Work.LWP.BiotSavart.integrand_norm_le
import Submission.Work.LWP.BiotSavart.farField_decay_const

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open FiniteTimeSingularity MeasureTheory WithLp
open scoped Matrix ENNReal

namespace Work.LWP.BiotSavart

/-- The Biot–Savart integrand of `biotSavart` at `(x,y)`: `(‖x-y‖³)⁻¹ • (ω y × (x-y))`, as an
element of `ℝ³`; `biotSavart ω x = (4π)⁻¹ • ∫ y, bsIntegrand ω x y`. -/
noncomputable def bsIntegrand (ω : R3 → R3) (x y : R3) : R3 :=
  WithLp.toLp 2 ((‖x - y‖ ^ (3 : ℕ))⁻¹ • crossProduct (ω y) (x - y))

lemma biotSavart_eq_integral (ω : R3 → R3) (x : R3) :
    biotSavart ω x = (4 * Real.pi)⁻¹ • ∫ y, bsIntegrand ω x y := rfl

/-- **Pointwise bound on the Biot–Savart integrand** (no hypothesis on the size of `y`):
`‖(‖x-y‖³)⁻¹ • (ω y × (x-y))‖ ≤ M ‖x-y‖⁻²` whenever `‖ω y‖ ≤ M`. -/
lemma bsIntegrand_norm_le {ω : R3 → R3} {M : ℝ} (hM : 0 ≤ M)
    (hω : ∀ y, ‖ω y‖ ≤ M) (x y : R3) :
    ‖bsIntegrand ω x y‖ ≤ M * ((‖x - y‖ ^ (2 : ℕ))⁻¹) := by
  have ha : (0 : ℝ) ≤ ‖x - y‖ := norm_nonneg _
  have hcross : ‖WithLp.toLp 2 (crossProduct (ω y) (x - y))‖ ≤ M * ‖x - y‖ :=
    le_trans (norm_toLp_crossProduct_le (ω y) (x - y))
      (mul_le_mul_of_nonneg_right (hω y) ha)
  have hkey : (‖x - y‖ ^ (3 : ℕ))⁻¹ * ‖x - y‖ ≤ (‖x - y‖ ^ (2 : ℕ))⁻¹ := by
    rcases eq_or_lt_of_le ha with h | h
    · rw [← h]; norm_num
    · have heq : (‖x - y‖ ^ (3 : ℕ))⁻¹ * ‖x - y‖ = (‖x - y‖ ^ (2 : ℕ))⁻¹ := by
        rw [show ‖x - y‖ ^ (3 : ℕ) = ‖x - y‖ ^ (2 : ℕ) * ‖x - y‖ by ring, mul_inv]
        field_simp
      rw [heq]
  rw [bsIntegrand, WithLp.toLp_smul, norm_smul,
    Real.norm_of_nonneg (inv_nonneg.mpr (by positivity))]
  calc (‖x - y‖ ^ (3 : ℕ))⁻¹ * ‖WithLp.toLp 2 (crossProduct (ω y) (x - y))‖
      ≤ (‖x - y‖ ^ (3 : ℕ))⁻¹ * (M * ‖x - y‖) :=
        mul_le_mul_of_nonneg_left hcross (inv_nonneg.mpr (by positivity))
    _ = M * ((‖x - y‖ ^ (3 : ℕ))⁻¹ * ‖x - y‖) := by ring
    _ ≤ M * (‖x - y‖ ^ (2 : ℕ))⁻¹ := mul_le_mul_of_nonneg_left hkey hM

/-- The integral of `‖z‖⁻²` over the closed ball of radius `r ≥ 0` about the origin of `ℝ³` is
`4πr` — the Jacobian `4πs²` of the spherical shell of radius `s` cancels the `s⁻²` of the
integrand exactly, so the borderline `r`-integrable case is finite.  The proof radially reduces
the integral with `MeasureTheory.integral_fun_norm_addHaar` (`Module.finrank ℝ R3 = 3`) and then
evaluates the resulting one-dimensional integral `∫ y in Ioi 0, y² · f y = r`. -/
lemma inv_sq_lintegral_closedBall_le (r : ℝ) (hr : 0 ≤ r) :
    ∫⁻ z in Metric.closedBall (0 : R3) r, ENNReal.ofReal ((‖z‖ ^ (2 : ℕ))⁻¹)
      ≤ ENNReal.ofReal (4 * Real.pi * r) := by
  classical
  let f : ℝ → ℝ := fun s => if s ≤ r then (s ^ 2)⁻¹ else 0
  have hf_nn : ∀ s, 0 ≤ f s := by
    intro s
    by_cases h : s ≤ r
    · simp only [f, if_pos h]; positivity
    · simp only [f, if_neg h]; exact le_refl 0
  have hcongr1 : ∀ y ∈ Set.Ioi (0 : ℝ), y ^ (2 : ℕ) * f y
      = (Set.Ioc (0 : ℝ) r).indicator (fun _ => (1 : ℝ)) y := by
    intro y hy
    have hypos : (0 : ℝ) < y := hy
    by_cases h : y ≤ r
    · rw [Set.indicator_of_mem (show y ∈ Set.Ioc (0 : ℝ) r from ⟨hypos, h⟩)]
      change y ^ 2 * (if y ≤ r then (y ^ 2)⁻¹ else 0) = (1 : ℝ)
      rw [if_pos h]
      field_simp
    · rw [Set.indicator_of_notMem (fun hh => h hh.2)]
      change y ^ 2 * (if y ≤ r then (y ^ 2)⁻¹ else 0) = (0 : ℝ)
      rw [if_neg h, mul_zero]
  have hI : ∫ y in Set.Ioi (0 : ℝ), y ^ (2 : ℕ) * f y = r := by
    rw [MeasureTheory.setIntegral_congr_fun measurableSet_Ioi hcongr1,
      MeasureTheory.setIntegral_indicator measurableSet_Ioc]
    have hset : Set.Ioi (0 : ℝ) ∩ Set.Ioc (0 : ℝ) r = Set.Ioc (0 : ℝ) r := by
      ext y; simp only [Set.mem_inter_iff, Set.mem_Ioi, Set.mem_Ioc]; tauto
    rw [hset, MeasureTheory.setIntegral_const, MeasureTheory.Measure.real, Real.volume_Ioc,
      ENNReal.toReal_ofReal (by linarith)]
    simp
  have hfr : Module.finrank ℝ R3 = 3 := by simp [Work.LWP.R3]
  have hvol : MeasureTheory.Measure.real MeasureTheory.volume (Metric.ball (0 : R3) 1)
      = Real.pi * 4 / 3 := by
    rw [MeasureTheory.Measure.real, EuclideanSpace.volume_ball_fin_three, ENNReal.toReal_mul,
      ENNReal.toReal_pow, ENNReal.toReal_ofReal (by norm_num : (0 : ℝ) ≤ 1),
      ENNReal.toReal_ofReal (by positivity : (0 : ℝ) ≤ Real.pi * 4 / 3)]
    norm_num
  have hbear : ∫ z : R3, f ‖z‖ = 4 * Real.pi * r := by
    rw [MeasureTheory.integral_fun_norm_addHaar (MeasureTheory.volume) f]
    simp only [hfr, Nat.reduceSub, smul_eq_mul]
    rw [hI, hvol]
    ring
  have hbase : IntegrableOn (fun _ : ℝ => (1 : ℝ)) (Set.Ioc (0 : ℝ) r) := by
    refine MeasureTheory.integrableOn_const ?_ ?_
    · rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top
    · simp
  have hind : Integrable ((Set.Ioc (0 : ℝ) r).indicator (fun _ => (1 : ℝ))) := by
    rw [MeasureTheory.integrable_indicator_iff measurableSet_Ioc]
    exact hbase
  have hIntOn : IntegrableOn (fun y : ℝ => y ^ (2 : ℕ) * f y) (Set.Ioi (0 : ℝ)) :=
    MeasureTheory.IntegrableOn.congr_fun hind.integrableOn
      (fun y hy => (hcongr1 y hy).symm) measurableSet_Ioi
  have hInt : Integrable (fun z : R3 => f ‖z‖) := by
    rw [MeasureTheory.integrable_fun_norm_addHaar (MeasureTheory.volume) (f := f)]
    simp only [hfr, Nat.reduceSub, smul_eq_mul]
    exact hIntOn
  have hlin : ∫⁻ z : R3, ENNReal.ofReal (f ‖z‖) < ⊤ := hInt.lintegral_lt_top
  have htoReal : (∫⁻ z : R3, ENNReal.ofReal (f ‖z‖)).toReal = 4 * Real.pi * r := by
    rw [← MeasureTheory.integral_eq_lintegral_of_nonneg_ae
      (Filter.Eventually.of_forall fun z => hf_nn ‖z‖) hInt.aestronglyMeasurable]
    exact hbear
  have hval : ∫⁻ z : R3, ENNReal.ofReal (f ‖z‖) = ENNReal.ofReal (4 * Real.pi * r) := by
    rw [← ENNReal.ofReal_toReal (a := ∫⁻ z : R3, ENNReal.ofReal (f ‖z‖)) hlin.ne, htoReal]
  have hpt : ∀ z : R3, ENNReal.ofReal (f ‖z‖)
      = (Metric.closedBall (0 : R3) r).indicator
          (fun z => ENNReal.ofReal ((‖z‖ ^ (2 : ℕ))⁻¹)) z := by
    intro z
    by_cases hz : z ∈ Metric.closedBall (0 : R3) r
    · rw [Set.indicator_of_mem hz]
      have hz' : ‖z‖ ≤ r := by simpa [Metric.mem_closedBall, dist_eq_norm] using hz
      simp only [f, if_pos hz']
    · rw [Set.indicator_of_notMem hz]
      have hz' : ¬ (‖z‖ ≤ r) := by
        intro h
        exact hz (by simpa [Metric.mem_closedBall, dist_eq_norm] using h)
      simp only [f, if_neg hz', ENNReal.ofReal_zero]
  have hred : ∫⁻ z in Metric.closedBall (0 : R3) r, ENNReal.ofReal ((‖z‖ ^ (2 : ℕ))⁻¹)
      = ∫⁻ z : R3, ENNReal.ofReal (f ‖z‖) := by
    rw [← MeasureTheory.lintegral_indicator (Metric.isClosed_closedBall.measurableSet)
      (fun z => ENNReal.ofReal ((‖z‖ ^ (2 : ℕ))⁻¹))]
    exact MeasureTheory.lintegral_congr (fun z => (hpt z).symm)
  rw [hred, hval]

/-- Translation invariance of the set integral over a closed ball: replacing the centre by a
translate and the variable by its difference from the centre does not change the integral. -/
lemma lintegral_closedBall_sub_eq (c : R3) (r : ℝ) (F : R3 → ℝ≥0∞) :
    ∫⁻ y in Metric.closedBall c r, F (y - c) = ∫⁻ z in Metric.closedBall (0 : R3) r, F z := by
  classical
  have hs : MeasurableSet (Metric.closedBall c r) := Metric.isClosed_closedBall.measurableSet
  have hs0 : MeasurableSet (Metric.closedBall (0 : R3) r) :=
    Metric.isClosed_closedBall.measurableSet
  have hmem : ∀ y : R3, y ∈ Metric.closedBall c r ↔ y - c ∈ Metric.closedBall (0 : R3) r := by
    intro y
    simp only [Metric.mem_closedBall, dist_eq_norm, sub_zero]
  rw [← MeasureTheory.lintegral_indicator hs (fun y => F (y - c))]
  have h1 : (fun y => (Metric.closedBall c r).indicator (fun y => F (y - c)) y)
      = fun y => (Metric.closedBall (0 : R3) r).indicator F (y - c) := by
    funext y
    rw [Set.indicator_apply, Set.indicator_apply]
    by_cases hy : y ∈ Metric.closedBall c r
    · simp [hy, (hmem y).mp hy]
    · have hy' : y - c ∉ Metric.closedBall (0 : R3) r := fun h => hy ((hmem y).mpr h)
      simp [hy, hy']
  rw [h1, MeasureTheory.lintegral_sub_right_eq_self
    (fun z => (Metric.closedBall (0 : R3) r).indicator F z) c]
  rw [MeasureTheory.lintegral_indicator hs0 F]

/-- The shifted version of `inv_sq_lintegral_closedBall_le_aux`: the singularity may sit at the
centre of the ball. -/
lemma inv_sq_lintegral_closedBall_shifted_le (c : R3) {r : ℝ} (hr : 0 ≤ r) :
    ∫⁻ y in Metric.closedBall c r, ENNReal.ofReal ((‖y - c‖ ^ (2 : ℕ))⁻¹)
      ≤ ENNReal.ofReal (4 * Real.pi * r) := by
  rw [lintegral_closedBall_sub_eq c r (fun z => ENNReal.ofReal ((‖z‖ ^ (2 : ℕ))⁻¹))]
  exact inv_sq_lintegral_closedBall_le r hr

/-- **The scalar near-field estimate**: for `‖x‖ ≤ 2R` the singular weight `‖x-y‖⁻²` has
integral at most `12πR = 4π·3R` over the ball of radius `R` about the origin, because that ball
is contained in the ball of radius `3R` about `x`. -/
lemma near_lintegral_scalar {R : ℝ} (hR : 0 ≤ R) {x : R3} (hx : ‖x‖ ≤ 2 * R) :
    ∫⁻ y in Metric.closedBall (0 : R3) R, ENNReal.ofReal ((‖x - y‖ ^ (2 : ℕ))⁻¹)
      ≤ ENNReal.ofReal (12 * Real.pi * R) := by
  have hsub : Metric.closedBall (0 : R3) R ⊆ Metric.closedBall x (3 * R) := by
    intro y hy
    simp only [Metric.mem_closedBall, dist_eq_norm, sub_zero] at hy
    simp only [Metric.mem_closedBall, dist_eq_norm]
    calc ‖y - x‖ = ‖x - y‖ := norm_sub_rev _ _
      _ ≤ ‖x‖ + ‖y‖ := norm_sub_le _ _
      _ ≤ 3 * R := by linarith
  calc ∫⁻ y in Metric.closedBall (0 : R3) R, ENNReal.ofReal ((‖x - y‖ ^ (2 : ℕ))⁻¹)
      ≤ ∫⁻ y in Metric.closedBall x (3 * R), ENNReal.ofReal ((‖x - y‖ ^ (2 : ℕ))⁻¹) :=
        lintegral_mono_set hsub
    _ = ∫⁻ y in Metric.closedBall x (3 * R), ENNReal.ofReal ((‖y - x‖ ^ (2 : ℕ))⁻¹) := by
        apply lintegral_congr
        intro y
        rw [norm_sub_rev]
    _ ≤ ENNReal.ofReal (4 * Real.pi * (3 * R)) :=
        inv_sq_lintegral_closedBall_shifted_le x (by linarith)
    _ = ENNReal.ofReal (12 * Real.pi * R) := by
        congr 1
        ring

/-- **Reduction of the vector-valued integrand to the scalar singular weight.**  Since `ω`
vanishes off the closed ball of radius `R`, the `ℝ³`-valued integrand of `biotSavart` is
dominated by `M` times the scalar weight `‖x-y‖⁻²` on that ball. -/
lemma lintegral_bsIntegrand_le {ω : R3 → R3} {R M : ℝ} (hM : 0 ≤ M)
    (hω : ∀ y, ‖ω y‖ ≤ M) (hsupp : ∀ y, ω y ≠ 0 → y ∈ Metric.closedBall 0 R)
    (x : R3)
    (hscal : ∫⁻ y in Metric.closedBall (0 : R3) R, ENNReal.ofReal ((‖x - y‖ ^ (2 : ℕ))⁻¹)
      ≤ ENNReal.ofReal (12 * Real.pi * R)) :
    ∫⁻ y, ENNReal.ofReal ‖bsIntegrand ω x y‖ ≤ ENNReal.ofReal (12 * Real.pi * M * R) := by
  classical
  have hsmeas : MeasurableSet (Metric.closedBall (0 : R3) R) :=
    Metric.isClosed_closedBall.measurableSet
  have hpoint : ∀ y, ENNReal.ofReal ‖bsIntegrand ω x y‖
      ≤ (Metric.closedBall (0 : R3) R).indicator
          (fun y => ENNReal.ofReal M * ENNReal.ofReal ((‖x - y‖ ^ (2 : ℕ))⁻¹)) y := by
    intro y
    by_cases hy : y ∈ Metric.closedBall (0 : R3) R
    · rw [Set.indicator_of_mem hy, ← ENNReal.ofReal_mul hM]
      exact ENNReal.ofReal_le_ofReal (bsIntegrand_norm_le hM hω x y)
    · rw [Set.indicator_of_notMem hy]
      have hωy : ω y = 0 := by
        by_contra hne
        exact hy (hsupp y hne)
      simp [bsIntegrand, hωy]
  have hsplit : (fun y => (Metric.closedBall (0 : R3) R).indicator
        (fun y => ENNReal.ofReal M * ENNReal.ofReal ((‖x - y‖ ^ (2 : ℕ))⁻¹)) y)
      = fun y => ENNReal.ofReal M * (Metric.closedBall (0 : R3) R).indicator
          (fun y => ENNReal.ofReal ((‖x - y‖ ^ (2 : ℕ))⁻¹)) y := by
    funext y
    by_cases hy : y ∈ Metric.closedBall (0 : R3) R <;>
      simp [Set.indicator_of_mem, Set.indicator_of_notMem, hy]
  calc ∫⁻ y, ENNReal.ofReal ‖bsIntegrand ω x y‖
      ≤ ∫⁻ y, (Metric.closedBall (0 : R3) R).indicator
          (fun y => ENNReal.ofReal M * ENNReal.ofReal ((‖x - y‖ ^ (2 : ℕ))⁻¹)) y :=
        lintegral_mono hpoint
    _ = ∫⁻ y, ENNReal.ofReal M * (Metric.closedBall (0 : R3) R).indicator
          (fun y => ENNReal.ofReal ((‖x - y‖ ^ (2 : ℕ))⁻¹)) y := by rw [hsplit]
    _ = ENNReal.ofReal M * ∫⁻ y, (Metric.closedBall (0 : R3) R).indicator
          (fun y => ENNReal.ofReal ((‖x - y‖ ^ (2 : ℕ))⁻¹)) y :=
        MeasureTheory.lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ = ENNReal.ofReal M * ∫⁻ y in Metric.closedBall (0 : R3) R,
          ENNReal.ofReal ((‖x - y‖ ^ (2 : ℕ))⁻¹) := by
        rw [MeasureTheory.lintegral_indicator hsmeas]
    _ ≤ ENNReal.ofReal M * ENNReal.ofReal (12 * Real.pi * R) :=
        mul_le_mul_right hscal _
    _ = ENNReal.ofReal (12 * Real.pi * M * R) := by
        rw [← ENNReal.ofReal_mul hM]
        congr 1
        ring

/-- **The near-field bound**: for `‖x‖ ≤ 2R`, `‖biotSavart ω x‖ ≤ 3 M R`. -/
lemma norm_biotSavart_near {ω : R3 → R3} {R M : ℝ} (hR : 0 ≤ R) (hM : 0 ≤ M)
    (hω : ∀ y, ‖ω y‖ ≤ M) (hsupp : ∀ y, ω y ≠ 0 → y ∈ Metric.closedBall 0 R)
    {x : R3} (hx : ‖x‖ ≤ 2 * R) :
    ‖biotSavart ω x‖ ≤ 3 * M * R := by
  rw [biotSavart_eq_integral, norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have h1 : ‖∫ y, bsIntegrand ω x y‖
      ≤ (∫⁻ y, ENNReal.ofReal ‖bsIntegrand ω x y‖).toReal :=
    norm_integral_le_lintegral_norm _
  have h2 : (∫⁻ y, ENNReal.ofReal ‖bsIntegrand ω x y‖).toReal ≤ 12 * Real.pi * M * R :=
    (ENNReal.toReal_mono ENNReal.ofReal_ne_top
      (lintegral_bsIntegrand_le hM hω hsupp x (near_lintegral_scalar hR hx))).trans_eq
      (ENNReal.toReal_ofReal (by positivity))
  calc (4 * Real.pi)⁻¹ * ‖∫ y, bsIntegrand ω x y‖
      ≤ (4 * Real.pi)⁻¹ * (12 * Real.pi * M * R) :=
        mul_le_mul_of_nonneg_left (h1.trans h2) (by positivity)
    _ = 3 * M * R := by
        field_simp
        ring

theorem nearField_bound {ω : R3 → R3} {R M : ℝ} (hR : 0 ≤ R) (hM : 0 ≤ M)
    (hω : ∀ y, ‖ω y‖ ≤ M) (hsupp : ∀ y, ω y ≠ 0 → y ∈ Metric.closedBall 0 R) :
    ∃ C : ℝ, 0 < C ∧ ∀ x : R3, ‖biotSavart ω x‖ ≤ C * M * R := by
  refine ⟨3, by norm_num, ?_⟩
  intro x
  by_cases hx : 2 * R ≤ ‖x‖
  · have h := farField_decay_const hR hM hω hsupp x hx
    rcases eq_or_lt_of_le hR with hR0 | hRpos
    · subst hR0
      simpa using h
    · have hxpos : 0 < ‖x‖ := lt_of_lt_of_le (by linarith) hx
      have hsq : 4 * R ^ 2 ≤ ‖x‖ ^ 2 := by nlinarith [norm_nonneg x]
      have hA : 0 ≤ 4 / 3 * M * R ^ 3 := by positivity
      have hdiv : 4 / 3 * M * R ^ 3 / ‖x‖ ^ 2 ≤ 4 / 3 * M * R ^ 3 / (4 * R ^ 2) :=
        div_le_div_of_nonneg_left hA (by positivity) hsq
      have hval : 4 / 3 * M * R ^ 3 / (4 * R ^ 2) = M * R / 3 := by
        field_simp
      have hfin : 4 / 3 * M * R ^ 3 / (4 * R ^ 2) ≤ 3 * M * R := by
        rw [hval]
        nlinarith [mul_nonneg hM hR]
      exact h.trans (hdiv.trans hfin)
  · exact norm_biotSavart_near hR hM hω hsupp (le_of_lt (lt_of_not_ge hx))

end Work.LWP.BiotSavart
