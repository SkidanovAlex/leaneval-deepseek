import Mathlib.Analysis.Fourier.AddCircleMulti
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
import Mathlib.Topology.UniformSpace.Uniformizable
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.Algebra.Order.Archimedean.Real.Hom
import Submission.Work.BoseFixR.Rb5Lin.ps3_fundamentalDomain
import Submission.Work.BoseFixR.Rb5Lin.ps3_latticeBall_finite
import Submission.Work.BoseFixR.Rb5Lin.ps3_mFourier_smul
import Submission.Work.BoseFixR.Rb5Lin.ps3_summableWeight
import Submission.Work.BoseFixR.Rb5Lin.ps3_torus_lift
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

-- Mathlib's torus Fourier theory (`Analysis.Fourier.AddCircleMulti`) is stated for the
-- probability Haar measure `AddCircle.haarAddCircle`, registered there as the local instance
-- `instMeasureSpaceUnitAddCircle`.  Registering it here makes `volume` on `UnitAddTorus (Fin 3)`
-- definitionally equal to the measure of that theory.
attribute [local instance] instMeasureSpaceUnitAddCircle

open MeasureTheory

namespace Work.BoseBoxFock

open Work.BoseFixR.Rb5Lin

noncomputable section

/-! ## 0. Elementary estimates -/

private lemma finrank_pi_fin3 : (Module.finrank ℝ (Fin 3 → ℝ) : ℝ) = 3 := by
  simp

/-- `x ↦ (1 + ‖x‖)⁻⁴` is integrable on `ℝ³`. -/
private lemma integrable_inv_weight :
    Integrable (fun x : Fin 3 → ℝ => ((1 + ‖x‖) ^ 4)⁻¹) := by
  have h := integrable_one_add_norm (E := Fin 3 → ℝ) (μ := volume) (r := (4 : ℝ)) (by
    rw [finrank_pi_fin3]; norm_num)
  refine h.congr ?_
  filter_upwards with x
  rw [Real.rpow_neg (le_of_lt (by positivity : (0 : ℝ) < 1 + ‖x‖))]
  simp

/-- From `(1 + ‖y‖)⁴ ‖g y‖ ≤ C` conclude `‖g y‖ ≤ C (1 + ‖y‖)⁻⁴`. -/
private lemma norm_le_weight {g : (Fin 3 → ℝ) → ℂ} {C : ℝ}
    (hgd : ∀ y : Fin 3 → ℝ, (1 + ‖y‖) ^ 4 * ‖g y‖ ≤ C) (y : Fin 3 → ℝ) :
    ‖g y‖ ≤ C * ((1 + ‖y‖) ^ 4)⁻¹ := by
  have h1 : ‖g y‖ * (1 + ‖y‖) ^ 4 ≤ C := by
    have h := hgd y
    rw [mul_comm] at h
    exact h
  have h2 : (0 : ℝ) < (1 + ‖y‖) ^ 4 := by positivity
  calc ‖g y‖ = (‖g y‖ * (1 + ‖y‖) ^ 4) * ((1 + ‖y‖) ^ 4)⁻¹ := by
        rw [mul_assoc, mul_inv_cancel₀ (ne_of_gt h2), mul_one]
    _ ≤ C * ((1 + ‖y‖) ^ 4)⁻¹ := mul_le_mul_of_nonneg_right h1 (by positivity)

/-- The lattice weight used for the domination. -/
private lemma weight_le_weight {A B : ℝ} (hA : 0 < A) (h : A ≤ B) :
    (B ^ 4)⁻¹ ≤ (A ^ 4)⁻¹ :=
  (inv_le_inv₀ (pow_pos (lt_of_lt_of_le hA h) 4) (pow_pos hA 4)).mpr
    (pow_le_pow_left₀ (le_of_lt hA) h 4)

/-- Uniform estimate on balls: for `‖z‖ ≤ R`, the translate `g (z + m)` is dominated by the
lattice weight shifted by `R`. -/
private lemma norm_translate_le {g : (Fin 3 → ℝ) → ℂ} {C : ℝ} (hC : 0 ≤ C)
    (hgd : ∀ y : Fin 3 → ℝ, (1 + ‖y‖) ^ 4 * ‖g y‖ ≤ C) {z : Fin 3 → ℝ} {R : ℝ}
    (hz : ‖z‖ ≤ R) (m : Fin 3 → ℤ) :
    ‖g (z + latPoint m)‖ ≤ C * ((1 + max 0 (‖latPoint m‖ - R)) ^ 4)⁻¹ := by
  refine (norm_le_weight hgd (z + latPoint m)).trans (mul_le_mul_of_nonneg_left ?_ hC)
  have h2 : ‖latPoint m‖ ≤ ‖z‖ + ‖z + latPoint m‖ := by
    have h := norm_sub_le (z + latPoint m) z
    rw [add_sub_cancel_left] at h
    linarith
  have h3 : max 0 (‖latPoint m‖ - R) ≤ ‖z + latPoint m‖ :=
    max_le (by positivity) (by linarith)
  have h1 : (1 : ℝ) + max 0 (‖latPoint m‖ - R) ≤ 1 + ‖z + latPoint m‖ := by linarith
  exact weight_le_weight (by have := le_max_left (0 : ℝ) (‖latPoint m‖ - R); linarith) h1

/-- The shifted lattice weight is dominated by the plain one. -/
private lemma shift_weight_le (b R : ℝ) (hb : 0 ≤ b) :
    ((1 + max 0 (b - R)) ^ 4)⁻¹ ≤ (1 + |R|) ^ 4 * ((1 + b) ^ 4)⁻¹ := by
  have h1 : (1 + b) ≤ (1 + |R|) * (1 + max 0 (b - R)) := by
    rcases le_total R b with hRb | hRb
    · have h2 : max 0 (b - R) = b - R := max_eq_right (by linarith)
      have h3 : (1 + b) ≤ (1 + |R|) * (1 + (b - R)) := by
        nlinarith [le_abs_self R, abs_nonneg R, hRb]
      rwa [h2]
    · have h2 : max 0 (b - R) = 0 := max_eq_left (by linarith)
      have h3 : 1 + b ≤ 1 + |R| := by linarith [le_abs_self R]
      simpa [h2] using h3
  have h2 : (1 + b) ^ 4 ≤ ((1 + |R|) * (1 + max 0 (b - R))) ^ 4 :=
    pow_le_pow_left₀ (by positivity) h1 4
  rw [mul_pow] at h2
  have h3 : (0 : ℝ) < (1 + b) ^ 4 := by positivity
  have h4 : (0 : ℝ) < (1 + max 0 (b - R)) ^ 4 := by positivity
  rw [← div_eq_mul_inv, le_div_iff₀ h3]
  calc ((1 + max 0 (b - R)) ^ 4)⁻¹ * (1 + b) ^ 4
      ≤ ((1 + max 0 (b - R)) ^ 4)⁻¹ * ((1 + |R|) ^ 4 * (1 + max 0 (b - R)) ^ 4) :=
        mul_le_mul_of_nonneg_left h2 (by positivity)
    _ = (1 + |R|) ^ 4 := by
        rw [mul_comm ((1 + |R|) ^ 4), ← mul_assoc, inv_mul_cancel₀ (ne_of_gt h4), one_mul]

/-- The shifted lattice weight is summable. -/
private lemma summableWeight_shift (R : ℝ) :
    Summable (fun m : Fin 3 → ℤ => ((1 + max 0 (‖latPoint m‖ - R)) ^ 4)⁻¹) := by
  refine Summable.of_nonneg_of_le (fun m => by positivity) (fun m => ?_)
    ((ps3_summableWeight).mul_left ((1 + |R|) ^ 4))
  exact shift_weight_le (‖latPoint m‖) R (norm_nonneg _)

/-! ## 1. The periodization and its continuity -/

/-- The periodization `F x = ∑' m ∈ ℤ³, g (x + m)`. -/
private def periodization (g : (Fin 3 → ℝ) → ℂ) : (Fin 3 → ℝ) → ℂ :=
  fun x => ∑' m : Fin 3 → ℤ, g (x + latPoint m)

/-- The periodization is invariant under the lattice. -/
private lemma periodization_periodic (g : (Fin 3 → ℝ) → ℂ) (x : Fin 3 → ℝ) (k : Fin 3 → ℤ) :
    periodization g (x + latPoint k) = periodization g x := by
  have h1 : ∀ m : Fin 3 → ℤ, g ((x + latPoint k) + latPoint m) = g (x + latPoint (m + k)) := by
    intro m
    congr 1
    ext i
    simp only [Pi.add_apply, latPoint_apply, Int.cast_add]
    ring
  simp only [periodization, h1]
  exact (Equiv.addRight k).tsum_eq (fun m : Fin 3 → ℤ => g (x + latPoint m))

/-- The periodization is continuous. -/
private lemma continuous_periodization {g : (Fin 3 → ℝ) → ℂ} {C : ℝ} (hC : 0 ≤ C)
    (hg : Continuous g) (hgd : ∀ y : Fin 3 → ℝ, (1 + ‖y‖) ^ 4 * ‖g y‖ ≤ C) :
    Continuous (periodization g) := by
  rw [continuous_iff_continuousAt]
  intro x
  have hsum : Summable (fun m : Fin 3 → ℤ =>
      ((1 + max 0 (‖latPoint m‖ - (‖x‖ + 1))) ^ 4)⁻¹) :=
    summableWeight_shift (‖x‖ + 1)
  have hcontOn : ContinuousOn (periodization g) (Metric.closedBall x 1) := by
    refine continuousOn_tsum (u := fun m : Fin 3 → ℤ =>
      C * ((1 + max 0 (‖latPoint m‖ - (‖x‖ + 1))) ^ 4)⁻¹) ?_ (hsum.mul_left C) ?_
    · intro m
      have h : Continuous (fun z : Fin 3 → ℝ => g (z + latPoint m)) :=
        hg.comp (continuous_id.add continuous_const)
      exact h.continuousOn
    · intro m z hz
      have hz' : ‖z‖ ≤ ‖x‖ + 1 := by
        have h2 : ‖z‖ - ‖x‖ ≤ ‖z - x‖ :=
          le_trans (le_abs_self _) (abs_norm_sub_norm_le z x)
        have hmem : ‖z - x‖ ≤ 1 := by
          simpa [Metric.mem_closedBall, dist_eq_norm] using hz
        linarith
      exact norm_translate_le hC hgd hz' m
  exact hcontOn.continuousAt (Metric.closedBall_mem_nhds x (by norm_num))

/-! ## 2. Auxiliary lemmas for the transfer to `EuclideanSpace` -/

/-- The Euclidean norm dominates the supremum norm. -/
private lemma norm_le_norm_toLp (y : Fin 3 → ℝ) :
    ‖y‖ ≤ ‖(WithLp.toLp 2 y : EuclideanSpace ℝ (Fin 3))‖ := by
  refine pi_norm_le_iff_of_nonneg (norm_nonneg _) |>.mpr fun i => ?_
  simpa using PiLp.norm_apply_le (p := 2) (β := fun _ : Fin 3 => ℝ)
    (WithLp.toLp 2 y : WithLp 2 (Fin 3 → ℝ)) i

/-- The box `(0,1]³` has volume one. -/
private lemma volume_box3 : (volume : Measure (Fin 3 → ℝ)) box3 = 1 := by
  have hvol : (volume : Measure (Fin 3 → ℝ))
      = Measure.pi (fun _ : Fin 3 => (volume : Measure ℝ)) := rfl
  rw [hvol, box3_eq_univ_pi, Measure.pi_pi]
  simp [Real.volume_Ioc]

/-- Points of the box have norm at most one. -/
private lemma norm_le_one_of_mem_box3 {x : Fin 3 → ℝ} (hx : x ∈ box3) : ‖x‖ ≤ 1 := by
  refine pi_norm_le_iff_of_nonneg (by norm_num) |>.mpr fun i => ?_
  have h := mem_box3.mp hx i
  rw [Real.norm_eq_abs]
  exact abs_le.mpr ⟨by linarith [h.1], by linarith [h.2]⟩

/-- Integrability from `(1 + ‖·‖)⁻⁴` decay. -/
private lemma integrable_of_decay {g : (Fin 3 → ℝ) → ℂ} {C : ℝ} (_hC : 0 ≤ C)
    (hg : AEStronglyMeasurable g volume)
    (hgd : ∀ y : Fin 3 → ℝ, ‖g y‖ ≤ C * ((1 + ‖y‖) ^ 4)⁻¹) : Integrable g := by
  have h1 : Integrable (fun y : Fin 3 → ℝ => C * ((1 + ‖y‖) ^ 4)⁻¹) :=
    integrable_inv_weight.const_mul C
  refine h1.mono' hg ?_
  filter_upwards with y
  exact hgd y

/-- The phase `x ↦ mFourier (-n) (q x)` is invariant under the lattice. -/
private lemma mFourier_neg_periodic (n : Fin 3 → ℤ) (x : Fin 3 → ℝ) (m : Fin 3 → ℤ) :
    (UnitAddTorus.mFourier (-n)) (fun i => ((x + latPoint m) i : UnitAddCircle))
      = (UnitAddTorus.mFourier (-n)) (fun i => (x i : UnitAddCircle)) := by
  congr 2
  funext i
  simp only [Pi.add_apply, latPoint_apply]
  rw [AddCircle.coe_add, show (((m i : ℝ) : UnitAddCircle)) = 0 from by
    rw [AddCircle.coe_eq_zero_iff]
    exact ⟨m i, by simp⟩, add_zero]

/-- `mFourier` takes values of norm at most one. -/
private lemma norm_mFourier_le_one (n : Fin 3 → ℤ) (x : Fin 3 → ℝ) :
    ‖(UnitAddTorus.mFourier n) (fun i => (x i : UnitAddCircle))‖ ≤ 1 := by
  have h := ContinuousMap.norm_coe_le_norm (UnitAddTorus.mFourier n)
    (fun i => (x i : UnitAddCircle))
  rw [UnitAddTorus.mFourier_norm] at h
  exact h

/-! ## 3. The Fourier coefficients of the periodization -/

/-- The `n`-th Fourier coefficient of the periodization is the Fourier integral. -/
private lemma fourierCoeff_periodization {g : (Fin 3 → ℝ) → ℂ} {C : ℝ} (hC : 0 ≤ C)
    (hg : Continuous g) (hgd : ∀ y : Fin 3 → ℝ, (1 + ‖y‖) ^ 4 * ‖g y‖ ≤ C)
    (G : C(UnitAddTorus (Fin 3), ℂ))
    (hG : ∀ x : Fin 3 → ℝ, G (fun i => (x i : UnitAddCircle)) = periodization g x)
    (n : Fin 3 → ℤ) :
    UnitAddTorus.mFourierCoeff (⇑G) n =
      ∫ x, g x * Complex.exp (-(2 * Real.pi * Complex.I * (∑ i, (x i : ℂ) * (n i : ℂ)))) := by
  have hphase : ∀ x : Fin 3 → ℝ,
      (UnitAddTorus.mFourier (-n)) (fun i => (x i : UnitAddCircle)) • periodization g x
      = ∑' m : Fin 3 → ℤ,
          (UnitAddTorus.mFourier (-n)) (fun i => (x i : UnitAddCircle)) • g (x + latPoint m) := by
    intro x
    simp only [periodization]
    rw [smul_eq_mul, ← tsum_mul_left]
    simp only [smul_eq_mul]
  -- Step 1: rewrite the coefficient as an integral over the fundamental box.
  have h1 : UnitAddTorus.mFourierCoeff (⇑G) n
      = ∫ x in box3,
          (UnitAddTorus.mFourier (-n)) (fun i => (x i : UnitAddCircle)) • periodization g x := by
    rw [UnitAddTorus.mFourierCoeff_eq_integral (⇑G) n (fun _ => (0 : ℝ))]
    simp only [hG]
    rfl
  -- Step 2: interchange the sum over the lattice with the integral.
  have h2 : (∫ x in box3,
        (UnitAddTorus.mFourier (-n)) (fun i => (x i : UnitAddCircle)) • periodization g x)
      = ∑' m : Fin 3 → ℤ, ∫ x in box3,
          (UnitAddTorus.mFourier (-n)) (fun i => (x i : UnitAddCircle)) • g (x + latPoint m) := by
    rw [show (fun x : Fin 3 → ℝ =>
          (UnitAddTorus.mFourier (-n)) (fun i => (x i : UnitAddCircle)) • periodization g x)
        = fun x => ∑' m : Fin 3 → ℤ,
          (UnitAddTorus.mFourier (-n)) (fun i => (x i : UnitAddCircle)) • g (x + latPoint m)
        from funext hphase]
    refine integral_tsum (μ := volume.restrict box3) ?_ ?_
    · intro m
      have hcont : Continuous (fun x : Fin 3 → ℝ =>
          (UnitAddTorus.mFourier (-n)) (fun i => (x i : UnitAddCircle)) • g (x + latPoint m)) := by
        fun_prop
      exact hcont.aestronglyMeasurable
    · -- domination of the sum of the integrals of the norms
      have hw : Summable (fun m : Fin 3 → ℤ =>
          C * ((1 + max 0 (‖latPoint m‖ - 1)) ^ 4)⁻¹) :=
        (summableWeight_shift 1).mul_left C
      have hnonneg : ∀ m : Fin 3 → ℤ, 0 ≤ C * ((1 + max 0 (‖latPoint m‖ - 1)) ^ 4)⁻¹ :=
        fun m => mul_nonneg hC (by positivity)
      have hbound : ∀ m : Fin 3 → ℤ, ∫⁻ x in box3,
          ‖(UnitAddTorus.mFourier (-n)) (fun i => (x i : UnitAddCircle)) •
            g (x + latPoint m)‖ₑ ≤
          ENNReal.ofReal (C * ((1 + max 0 (‖latPoint m‖ - 1)) ^ 4)⁻¹) := by
        intro m
        calc ∫⁻ x in box3,
              ‖(UnitAddTorus.mFourier (-n)) (fun i => (x i : UnitAddCircle)) •
                g (x + latPoint m)‖ₑ
            ≤ ∫⁻ _x in box3,
                ENNReal.ofReal (C * ((1 + max 0 (‖latPoint m‖ - 1)) ^ 4)⁻¹) := by
              refine lintegral_mono_ae ?_
              filter_upwards [ae_restrict_mem measurableSet_box3] with x hx
              rw [← ofReal_norm]
              refine ENNReal.ofReal_le_ofReal ?_
              calc ‖(UnitAddTorus.mFourier (-n)) (fun i => (x i : UnitAddCircle)) •
                    g (x + latPoint m)‖
                  = ‖(UnitAddTorus.mFourier (-n)) (fun i => (x i : UnitAddCircle))‖ *
                      ‖g (x + latPoint m)‖ := norm_smul _ _
                _ ≤ 1 * (C * ((1 + max 0 (‖latPoint m‖ - 1)) ^ 4)⁻¹) :=
                    mul_le_mul (norm_mFourier_le_one (-n) x)
                      (norm_translate_le hC hgd (norm_le_one_of_mem_box3 hx) m)
                      (norm_nonneg _) (by norm_num)
                _ = C * ((1 + max 0 (‖latPoint m‖ - 1)) ^ 4)⁻¹ := one_mul _
          _ = ENNReal.ofReal (C * ((1 + max 0 (‖latPoint m‖ - 1)) ^ 4)⁻¹) *
                (volume : Measure (Fin 3 → ℝ)) box3 := by
              rw [lintegral_const,
                show (volume.restrict box3) Set.univ = (volume : Measure (Fin 3 → ℝ)) box3 from by
                  rw [Measure.restrict_apply MeasurableSet.univ, Set.univ_inter]]
          _ = ENNReal.ofReal (C * ((1 + max 0 (‖latPoint m‖ - 1)) ^ 4)⁻¹) := by
              rw [volume_box3, mul_one]
      refine ne_top_of_le_ne_top ?_ (ENNReal.tsum_le_tsum hbound)
      rw [← ENNReal.ofReal_tsum_of_nonneg hnonneg hw]
      exact ENNReal.ofReal_ne_top
  -- Step 3: the fundamental domain identity.
  have h3 : (∑' m : Fin 3 → ℤ, ∫ x in box3,
        (UnitAddTorus.mFourier (-n)) (fun i => (x i : UnitAddCircle)) • g (x + latPoint m))
      = ∫ x, (UnitAddTorus.mFourier (-n)) (fun i => (x i : UnitAddCircle)) • g x := by
    have hint : Integrable (fun y : Fin 3 → ℝ =>
        (UnitAddTorus.mFourier (-n)) (fun i => (y i : UnitAddCircle)) • g y) := by
      refine integrable_of_decay hC ?_ ?_
      · have hcont : Continuous (fun y : Fin 3 → ℝ =>
            (UnitAddTorus.mFourier (-n)) (fun i => (y i : UnitAddCircle)) • g y) := by
          fun_prop
        exact hcont.aestronglyMeasurable
      · intro y
        calc ‖(UnitAddTorus.mFourier (-n)) (fun i => (y i : UnitAddCircle)) • g y‖
            = ‖(UnitAddTorus.mFourier (-n)) (fun i => (y i : UnitAddCircle))‖ * ‖g y‖ :=
              norm_smul _ _
          _ ≤ 1 * ‖g y‖ :=
              mul_le_mul_of_nonneg_right (norm_mFourier_le_one (-n) y) (norm_nonneg _)
          _ = ‖g y‖ := one_mul _
          _ ≤ C * ((1 + ‖y‖) ^ 4)⁻¹ := norm_le_weight hgd y
    rw [MeasureTheory.IsAddFundamentalDomain.integral_eq_tsum'' ps3_fundamentalDomain _ hint]
    refine tsum_congr fun m => ?_
    simp only [vadd_eq_add_latPoint]
    refine setIntegral_congr_fun measurableSet_box3 fun x _ => ?_
    rw [mFourier_neg_periodic n x m]
  -- Step 4: identify the phase with the exponential.
  have h4 : (∫ x, (UnitAddTorus.mFourier (-n)) (fun i => (x i : UnitAddCircle)) • g x)
      = ∫ x, g x * Complex.exp (-(2 * Real.pi * Complex.I * (∑ i, (x i : ℂ) * (n i : ℂ)))) := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    exact ps3_mFourier_smul n x (g x)
  rw [h1, h2, h3, h4]

/-! ## 4. Poisson summation on `ℝ³`, with summability of the Fourier coefficients assumed -/

/-- Change of variables: integrals over `EuclideanSpace ℝ (Fin 3)` against the Fourier
exponential. -/
private lemma integral_transfer (f : EuclideanSpace ℝ (Fin 3) → ℂ) (w : Fin 3 → ℝ) :
    (∫ x : EuclideanSpace ℝ (Fin 3), f x * Complex.exp (-(2 * Real.pi * Complex.I *
        (inner ℝ x (WithLp.toLp 2 w)))))
      = ∫ y : Fin 3 → ℝ, f (WithLp.toLp 2 y) * Complex.exp (-(2 * Real.pi * Complex.I *
        (∑ i, ((y i : ℂ) * (w i : ℂ))))) := by
  rw [← (PiLp.volume_preserving_toLp (Fin 3)).integral_comp
    (MeasurableEquiv.toLp 2 _).measurableEmbedding]
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  have hinner : ∀ y : Fin 3 → ℝ,
      ((inner ℝ (WithLp.toLp 2 y) (WithLp.toLp 2 w) : ℝ) : ℂ)
        = ∑ i, ((y i : ℂ) * (w i : ℂ)) := by
    intro y
    have h1 : (inner ℝ (WithLp.toLp 2 y) (WithLp.toLp 2 w) : ℝ) = ∑ i, y i * w i := by
      rw [PiLp.inner_apply]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp [RCLike.inner_apply, mul_comm]
    rw [h1, Complex.ofReal_sum]
    exact Finset.sum_congr rfl fun i _ => by push_cast; ring
  simp only [hinner]

/-- Poisson summation in the `Fin 3 → ℝ` coordinates, with the summability of the Fourier
coefficients as the convergence hypothesis. -/
private theorem poisson_R3 (g : (Fin 3 → ℝ) → ℂ) (hg : Continuous g)
    (hgdec : ∃ C : ℝ, ∀ y : Fin 3 → ℝ, (1 + ‖y‖) ^ 4 * ‖g y‖ ≤ C)
    (hFsum : Summable (fun n : Fin 3 → ℤ => ∫ x, g x * Complex.exp (-(2 * Real.pi * Complex.I *
      (∑ i, (x i : ℂ) * (latPoint n i : ℂ)))))) :
    (∑' m : Fin 3 → ℤ, g (latPoint m)) =
      ∑' m : Fin 3 → ℤ, ∫ x, g x * Complex.exp (-(2 * Real.pi * Complex.I *
        (∑ i, (x i : ℂ) * ((latPoint m) i : ℂ)))) := by
  obtain ⟨C, hC⟩ := hgdec
  have hCnn : 0 ≤ C := by
    have h2 : ‖g 0‖ ≤ C := by
      have := hC 0
      simpa using this
    linarith [norm_nonneg (g 0)]
  have hFcont : Continuous (periodization g) := continuous_periodization hCnn hg hC
  obtain ⟨G, hG⟩ := ps3_torus_lift ⟨periodization g, hFcont⟩
    (fun x m => periodization_periodic g x m)
  have hsum : Summable (fun n : Fin 3 → ℤ => UnitAddTorus.mFourierCoeff (⇑G) n) :=
    hFsum.congr fun n => (fourierCoeff_periodization hCnn hg hC G hG n).symm
  have hseries := UnitAddTorus.hasSum_mFourier_series_apply_of_summable (f := G) hsum
    (0 : UnitAddTorus (Fin 3))
  have hone : ∀ n : Fin 3 → ℤ, (UnitAddTorus.mFourier n) (0 : UnitAddTorus (Fin 3)) = 1 := by
    intro n
    rw [UnitAddTorus.mFourier]
    simp
  have hseries' : HasSum (fun n : Fin 3 → ℤ => UnitAddTorus.mFourierCoeff (⇑G) n) (G 0) := by
    simpa only [hone, smul_eq_mul, mul_one] using hseries
  have hG0 : G 0 = periodization g 0 := hG 0
  have hF0 : periodization g 0 = ∑' m : Fin 3 → ℤ, g (latPoint m) := by
    simp only [periodization, zero_add]
  rw [← hF0, ← hG0, ← hseries'.tsum_eq]
  exact tsum_congr fun n => fourierCoeff_periodization hCnn hg hC G hG n

/-! ## 5. Poisson summation in `EuclideanSpace ℝ (Fin 3)` -/

/-- **Poisson summation on `ℝ³` for the lattice `ℤ³`, with the summability of the Fourier
coefficients as the only convergence hypothesis** (the sibling
`Work.BoseFixR.Rb5Lin.poisson_summation_euclid3` instead assumes a rapid decay bound on the Fourier
transform).  `f` is continuous with `(1+‖x‖)⁴` decay, and the Fourier samples
`∫ x, f x · exp(-2πi⟪x, m⟫)` at the lattice `ℤ³` are summable. -/
theorem poissonEuclid3Summable (f : EuclideanSpace ℝ (Fin 3) → ℂ) (hf : Continuous f)
    (hfdec : ∃ C : ℝ, ∀ x : EuclideanSpace ℝ (Fin 3), (1 + ‖x‖) ^ 4 * ‖f x‖ ≤ C)
    (hFsum : Summable (fun m : Fin 3 → ℤ =>
      ∫ x : EuclideanSpace ℝ (Fin 3), f x * Complex.exp
        (-(2 * Real.pi * Complex.I * (inner ℝ x (WithLp.toLp 2 (fun i => (m i : ℝ)))))))) :
    (∑' m : Fin 3 → ℤ, f (WithLp.toLp 2 (fun i => (m i : ℝ))))
      = ∑' m : Fin 3 → ℤ, ∫ x : EuclideanSpace ℝ (Fin 3), f x * Complex.exp
        (-(2 * Real.pi * Complex.I * (inner ℝ x (WithLp.toLp 2 (fun i => (m i : ℝ)))))) := by
  set g : (Fin 3 → ℝ) → ℂ := fun y => f (WithLp.toLp 2 y) with hgdef
  have hg_cont : Continuous g := hf.comp (PiLp.continuous_toLp 2 fun _ : Fin 3 => ℝ)
  have hgdec : ∃ C : ℝ, ∀ y : Fin 3 → ℝ, (1 + ‖y‖) ^ 4 * ‖g y‖ ≤ C := by
    obtain ⟨C, hC⟩ := hfdec
    refine ⟨C, fun y => ?_⟩
    have h1 : (1 + ‖y‖) ^ 4
        ≤ (1 + ‖(WithLp.toLp 2 y : EuclideanSpace ℝ (Fin 3))‖) ^ 4 := by
      refine pow_le_pow_left₀ (by positivity) ?_ 4
      linarith [norm_le_norm_toLp y]
    have h2 : (1 + ‖y‖) ^ 4 * ‖g y‖ ≤ (1 + ‖(WithLp.toLp 2 y : EuclideanSpace ℝ (Fin 3))‖) ^ 4
        * ‖f (WithLp.toLp 2 y)‖ := by
      rw [hgdef]
      exact mul_le_mul_of_nonneg_right h1 (norm_nonneg _)
    exact h2.trans (hC (WithLp.toLp 2 y))
  have hFsum' : Summable (fun n : Fin 3 → ℤ =>
      ∫ x : Fin 3 → ℝ, g x * Complex.exp (-(2 * Real.pi * Complex.I *
        (∑ i, (x i : ℂ) * (latPoint n i : ℂ))))) := by
    refine hFsum.congr fun n => ?_
    have h := integral_transfer f (latPoint n)
    rw [show latPoint n = (fun i => (n i : ℝ)) from rfl] at h
    simpa only [hgdef, latPoint_apply] using h
  have hR3 := poisson_R3 g hg_cont hgdec hFsum'
  have hL : (∑' m : Fin 3 → ℤ, f (WithLp.toLp 2 (fun i => (m i : ℝ))))
      = ∑' m : Fin 3 → ℤ, g (latPoint m) :=
    tsum_congr fun m => by
      rw [hgdef]
      rfl
  have hR : (∑' m : Fin 3 → ℤ, ∫ x : EuclideanSpace ℝ (Fin 3),
        f x * Complex.exp (-(2 * Real.pi * Complex.I *
          (inner ℝ x (WithLp.toLp 2 (fun i => (m i : ℝ)))))))
      = ∑' m : Fin 3 → ℤ, ∫ x : Fin 3 → ℝ, g x * Complex.exp (-(2 * Real.pi * Complex.I *
          (∑ i, (x i : ℂ) * ((latPoint m) i : ℂ)))) := by
    refine tsum_congr fun m => ?_
    have h := integral_transfer f (latPoint m)
    rw [show latPoint m = (fun i => (m i : ℝ)) from rfl] at h
    simpa only [hgdef, latPoint_apply] using h
  rw [hL, hR]
  exact hR3

end

end Work.BoseBoxFock
