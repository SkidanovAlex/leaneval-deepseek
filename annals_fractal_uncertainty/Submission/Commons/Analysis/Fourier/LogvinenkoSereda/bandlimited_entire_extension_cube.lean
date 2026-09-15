import Mathlib.Algebra.Order.Archimedean.Real.Hom
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Analysis.Calculus.ContDiff.RestrictScalars
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.PicardGroup
import Mathlib.RingTheory.SimpleRing.Principal
import Submission.Commons.Analysis.Complex.analyticAt_of_differentiableOn_closedBall
import Submission.Commons.Analysis.Fourier.fourierInv_toLp_ae_eq_fourierInv

set_option maxHeartbeats 400000

namespace Commons.Analysis.Fourier.LogvinenkoSereda

open MeasureTheory Metric FourierTransform
open scoped BigOperators ENNReal

variable {d : ℕ}

/-- The band-limiting cube `{ξ | ∀ i, |ξ i| ≤ σ}` in `ℝᵈ`. -/
def bandCube (d : ℕ) (σ : ℝ) : Set (EuclideanSpace ℝ (Fin d)) :=
  {ξ | ∀ i : Fin d, |ξ i| ≤ σ}

/-- The phase `exp (2πi ∑ i, z i * ξ i)`. -/
noncomputable def phase (d : ℕ) (z : Fin d → ℂ) (ξ : EuclideanSpace ℝ (Fin d)) : ℂ :=
  Complex.exp (2 * Real.pi * Complex.I * (∑ i : Fin d, z i * (ξ i : ℂ)))

/-- The constant `2πi`. -/
noncomputable def iota : ℂ := 2 * Real.pi * Complex.I

/-- The `ℂ`-linear functional `u ↦ ∑ i, ξ i * u i`. -/
noncomputable def linξ (d : ℕ) (ξ : EuclideanSpace ℝ (Fin d)) : (Fin d → ℂ) →L[ℂ] ℂ :=
  ∑ i : Fin d, (ξ i : ℂ) • ContinuousLinearMap.proj i

lemma linξ_apply (ξ : EuclideanSpace ℝ (Fin d)) (u : Fin d → ℂ) :
    linξ d ξ u = ∑ i : Fin d, (ξ i : ℂ) * u i := by
  simp [linξ]

/-- The `ℂ`-linear derivative of the phase `z ↦ phase d z ξ` at `z`. -/
noncomputable def phaseCLM (d : ℕ) (z : Fin d → ℂ) (ξ : EuclideanSpace ℝ (Fin d)) :
    (Fin d → ℂ) →L[ℂ] ℂ :=
  (iota * phase d z ξ) • linξ d ξ

lemma norm_iota : ‖iota‖ = 2 * Real.pi := by
  rw [iota, norm_mul, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg Real.pi_nonneg]
  norm_num

lemma norm_linξ_le {σ : ℝ} (hσ : 0 ≤ σ) (ξ : EuclideanSpace ℝ (Fin d))
    (hξ : ξ ∈ bandCube d σ) : ‖linξ d ξ‖ ≤ (d : ℝ) * σ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg (Nat.cast_nonneg _) hσ) (fun u => ?_)
  rw [linξ_apply]
  calc ‖∑ i : Fin d, (ξ i : ℂ) * u i‖
      ≤ ∑ i : Fin d, ‖(ξ i : ℂ) * u i‖ := norm_sum_le _ _
    _ = ∑ i : Fin d, |ξ i| * ‖u i‖ := by
          apply Finset.sum_congr rfl
          intro i _
          rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    _ ≤ ∑ i : Fin d, σ * ‖u‖ := by
          apply Finset.sum_le_sum
          intro i _
          exact mul_le_mul (hξ i) (norm_le_pi_norm u i) (norm_nonneg _) hσ
    _ = (d : ℝ) * σ * ‖u‖ := by
          rw [Finset.sum_const, Finset.card_fin, nsmul_eq_mul]; ring

lemma norm_phase_le {σ : ℝ} (hσ : 0 ≤ σ) (z : Fin d → ℂ)
    (ξ : EuclideanSpace ℝ (Fin d)) (hξ : ξ ∈ bandCube d σ) :
    ‖phase d z ξ‖ ≤ Real.exp (2 * Real.pi * σ * d * ‖z‖) := by
  have hkey : 2 * Real.pi * Complex.I * (∑ i : Fin d, z i * (ξ i : ℂ))
      = iota * (∑ i : Fin d, z i * (ξ i : ℂ)) := by rw [iota]
  rw [phase, hkey]
  calc ‖Complex.exp (iota * (∑ i : Fin d, z i * (ξ i : ℂ)))‖
      = Real.exp ((iota * (∑ i : Fin d, z i * (ξ i : ℂ))).re) := Complex.norm_exp _
    _ ≤ Real.exp ‖iota * (∑ i : Fin d, z i * (ξ i : ℂ))‖ :=
        Real.exp_le_exp.mpr (Complex.re_le_norm _)
    _ = Real.exp (2 * Real.pi * ‖∑ i : Fin d, z i * (ξ i : ℂ)‖) := by
        rw [norm_mul, norm_iota]
    _ ≤ Real.exp (2 * Real.pi * σ * d * ‖z‖) := by
        apply Real.exp_le_exp.mpr
        have h2pi : (0:ℝ) ≤ 2 * Real.pi := by positivity
        calc 2 * Real.pi * ‖∑ i : Fin d, z i * (ξ i : ℂ)‖
            ≤ 2 * Real.pi * (∑ i : Fin d, ‖z i‖ * σ) := by
              apply mul_le_mul_of_nonneg_left _ h2pi
              calc ‖∑ i : Fin d, z i * (ξ i : ℂ)‖ ≤ ∑ i : Fin d, ‖z i * (ξ i : ℂ)‖ :=
                    norm_sum_le _ _
                _ = ∑ i : Fin d, ‖z i‖ * |ξ i| := by
                    apply Finset.sum_congr rfl
                    intro i _
                    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
                _ ≤ ∑ i : Fin d, ‖z i‖ * σ :=
                    Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (hξ i) (norm_nonneg _))
          _ = 2 * Real.pi * ((∑ i : Fin d, ‖z i‖) * σ) := by rw [Finset.sum_mul]
          _ ≤ 2 * Real.pi * (((d:ℝ) * ‖z‖) * σ) := by
              apply mul_le_mul_of_nonneg_left _ h2pi
              have h := Pi.sum_norm_apply_le_norm (f := z)
              rw [Fintype.card_fin, nsmul_eq_mul] at h
              exact mul_le_mul_of_nonneg_right h hσ
          _ = 2 * Real.pi * σ * d * ‖z‖ := by ring

lemma phase_eq_exp (z : Fin d → ℂ) (ξ : EuclideanSpace ℝ (Fin d)) :
    phase d z ξ = Complex.exp (iota * linξ d ξ z) := by
  rw [phase, linξ_apply, iota, Finset.mul_sum, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  ring

lemma norm_phaseCLM_le {σ : ℝ} (hσ : 0 ≤ σ) (z : Fin d → ℂ)
    (ξ : EuclideanSpace ℝ (Fin d)) (hξ : ξ ∈ bandCube d σ) :
    ‖phaseCLM d z ξ‖ ≤ (2 * Real.pi) * Real.exp (2 * Real.pi * σ * d * ‖z‖) * ((d:ℝ) * σ) := by
  rw [phaseCLM, norm_smul, norm_mul, norm_iota]
  exact mul_le_mul
    (mul_le_mul_of_nonneg_left (norm_phase_le hσ z ξ hξ) (by positivity))
    (norm_linξ_le hσ ξ hξ) (norm_nonneg _) (by positivity)

lemma hasFDerivAt_phase (z : Fin d → ℂ) (ξ : EuclideanSpace ℝ (Fin d)) :
    HasFDerivAt (fun w : Fin d → ℂ => phase d w ξ) (phaseCLM d z ξ) z := by
  have hL : HasFDerivAt (fun w : Fin d → ℂ => linξ d ξ w) (linξ d ξ) z :=
    ContinuousLinearMap.hasFDerivAt (linξ d ξ)
  have h1 : HasFDerivAt (fun w : Fin d → ℂ => iota • (linξ d ξ) w)
      (iota • linξ d ξ) z := hL.const_smul iota
  have h2 := h1.cexp
  have hfun : (fun w : Fin d → ℂ => Complex.exp (iota • (linξ d ξ) w))
      = fun w => phase d w ξ := by
    funext w; rw [phase_eq_exp w ξ]; simp [smul_eq_mul]
  have hder : Complex.exp (iota • (linξ d ξ) z) • (iota • linξ d ξ) = phaseCLM d z ξ := by
    rw [phaseCLM, phase_eq_exp z ξ]
    ext u
    simp only [ContinuousLinearMap.smul_apply, smul_eq_mul]
    ring
  rw [hfun, hder] at h2
  exact h2


section FT

/-- The Fourier--Laplace transform of a function on `ℝᵈ`. -/
noncomputable def FT (d : ℕ) (h : EuclideanSpace ℝ (Fin d) → ℂ) (z : Fin d → ℂ) : ℂ :=
  ∫ a, h a * phase d z a

lemma continuous_linξ : Continuous (fun a : EuclideanSpace ℝ (Fin d) => linξ d a) := by
  unfold linξ
  apply continuous_finsetSum
  intro i _
  exact (Complex.continuous_ofReal.comp
    (EuclideanSpace.proj i : EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ).continuous).smul continuous_const

lemma continuous_phase_fixed (z : Fin d → ℂ) :
    Continuous (fun a : EuclideanSpace ℝ (Fin d) => phase d z a) := by
  rw [show (fun a : EuclideanSpace ℝ (Fin d) => phase d z a)
      = fun a => Complex.exp (iota * linξ d a z) by
    funext a; exact phase_eq_exp z a]
  exact Complex.continuous_exp.comp
    (continuous_const.mul ((continuous_linξ (d := d)).clm_apply continuous_const))

lemma continuous_phaseCLM (z : Fin d → ℂ) :
    Continuous (fun a : EuclideanSpace ℝ (Fin d) => phaseCLM d z a) := by
  unfold phaseCLM
  exact (continuous_const.mul (continuous_phase_fixed z)).smul continuous_linξ

lemma integrable_mul_phase {σ : ℝ} (hσ : 0 ≤ σ) {h : EuclideanSpace ℝ (Fin d) → ℂ}
    (hh : Integrable h) (hsupp : ∀ᵐ a ∂(volume : Measure (EuclideanSpace ℝ (Fin d))),
      a ∉ bandCube d σ → h a = 0) (z : Fin d → ℂ) :
    Integrable (fun a => h a * phase d z a) := by
  refine (hh.norm.const_mul (Real.exp (2 * Real.pi * σ * d * ‖z‖))).mono' ?_ ?_
  · exact hh.aestronglyMeasurable.mul (continuous_phase_fixed z).aestronglyMeasurable
  · filter_upwards [hsupp] with a ha
    by_cases hmem : a ∈ bandCube d σ
    · rw [norm_mul]
      calc ‖h a‖ * ‖phase d z a‖ = ‖phase d z a‖ * ‖h a‖ := mul_comm _ _
        _ ≤ Real.exp (2 * Real.pi * σ * d * ‖z‖) * ‖h a‖ :=
            mul_le_mul_of_nonneg_right (norm_phase_le hσ z a hmem) (norm_nonneg (h a))
    · rw [ha hmem, zero_mul, norm_zero]; positivity

/-- The Fourier--Laplace transform is complex differentiable, and the derivative is the integral
of the derivative of the phase. -/
lemma hasFDerivAt_FT {σ : ℝ} (hσ : 0 ≤ σ) {H : EuclideanSpace ℝ (Fin d) → ℂ}
    (hH : Integrable H) (hsupp : ∀ᵐ a ∂(volume : Measure (EuclideanSpace ℝ (Fin d))),
      a ∉ bandCube d σ → H a = 0) (z : Fin d → ℂ) :
    HasFDerivAt (FT d H) (∫ a, H a • phaseCLM d z a) z := by
  have hball : ∀ x ∈ Metric.ball z 1, ‖x‖ ≤ ‖z‖ + 1 := by
    intro x hx
    have h1 : ‖x - z‖ < 1 := by
      rw [← dist_eq_norm]; exact Metric.mem_ball.mp hx
    calc ‖x‖ = ‖x - z + z‖ := by rw [sub_add_cancel]
      _ ≤ ‖x - z‖ + ‖z‖ := norm_add_le _ _
      _ ≤ ‖z‖ + 1 := by linarith
  refine hasFDerivAt_integral_of_dominated_of_fderiv_le
    (F := fun x a => H a * phase d x a) (F' := fun x a => H a • phaseCLM d x a)
    (s := Metric.ball z 1)
    (bound := fun a => (2 * Real.pi * ((d:ℝ) * σ) * Real.exp (2 * Real.pi * σ * d * (‖z‖ + 1)))
      * ‖H a‖)
    (Metric.ball_mem_nhds z one_pos) ?_ ?_ ?_ ?_ ?_ ?_
  · exact Filter.Eventually.of_forall fun x =>
      hH.aestronglyMeasurable.mul (continuous_phase_fixed x).aestronglyMeasurable
  · exact integrable_mul_phase hσ hH hsupp z
  · exact hH.aestronglyMeasurable.smul (continuous_phaseCLM z).aestronglyMeasurable
  · filter_upwards [hsupp] with a ha x hx
    by_cases hmem : a ∈ bandCube d σ
    · rw [norm_smul]
      have hC : ‖phaseCLM d x a‖ ≤ 2 * Real.pi * ((d:ℝ) * σ)
          * Real.exp (2 * Real.pi * σ * d * (‖z‖ + 1)) := by
        refine (norm_phaseCLM_le hσ x a hmem).trans ?_
        have hexp : Real.exp (2 * Real.pi * σ * d * ‖x‖)
            ≤ Real.exp (2 * Real.pi * σ * d * (‖z‖ + 1)) :=
          Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (hball x hx) (by positivity))
        calc (2 * Real.pi) * Real.exp (2 * Real.pi * σ * d * ‖x‖) * ((d:ℝ) * σ)
            ≤ (2 * Real.pi) * Real.exp (2 * Real.pi * σ * d * (‖z‖ + 1)) * ((d:ℝ) * σ) := by
              gcongr
          _ = 2 * Real.pi * ((d:ℝ) * σ) * Real.exp (2 * Real.pi * σ * d * (‖z‖ + 1)) := by ring
      calc ‖H a‖ * ‖phaseCLM d x a‖ = ‖phaseCLM d x a‖ * ‖H a‖ := mul_comm _ _
        _ ≤ (2 * Real.pi * ((d:ℝ) * σ) * Real.exp (2 * Real.pi * σ * d * (‖z‖ + 1))) * ‖H a‖ :=
            mul_le_mul_of_nonneg_right hC (norm_nonneg (H a))
    · simp [ha hmem]
  · exact hH.norm.const_mul _
  · exact Filter.Eventually.of_forall fun a x _ =>
      ((hasFDerivAt_phase x a).const_smul (H a)).congr_of_eventuallyEq
        (Filter.Eventually.of_forall fun w => by simp [smul_eq_mul])

end FT


section Analytic

variable (H : EuclideanSpace ℝ (Fin d) → ℂ) {σ : ℝ}

lemma differentiable_FT (hσ : 0 ≤ σ) (hH : Integrable H)
    (hsupp : ∀ᵐ a ∂(volume : Measure (EuclideanSpace ℝ (Fin d))), a ∉ bandCube d σ → H a = 0) :
    Differentiable ℂ (FT d H) :=
  fun z => (hasFDerivAt_FT hσ hH hsupp z).differentiableAt

lemma analyticAt_FT (hσ : 0 ≤ σ) (hH : Integrable H)
    (hsupp : ∀ᵐ a ∂(volume : Measure (EuclideanSpace ℝ (Fin d))), a ∉ bandCube d σ → H a = 0)
    (c : Fin d → ℂ) : AnalyticAt ℂ (FT d H) c :=
  Commons.Analysis.Complex.analyticAt_of_differentiableOn_closedBall one_pos
    (fun z _ => (hasFDerivAt_FT hσ hH hsupp z).differentiableAt.differentiableWithinAt)

lemma contDiff_complex_FT (hσ : 0 ≤ σ) (hH : Integrable H)
    (hsupp : ∀ᵐ a ∂(volume : Measure (EuclideanSpace ℝ (Fin d))), a ∉ bandCube d σ → H a = 0) :
    ContDiff ℂ ⊤ (FT d H) :=
  AnalyticOnNhd.contDiff (n := ⊤) (fun c _ => analyticAt_FT H hσ hH hsupp c)

lemma contDiff_real_FT (hσ : 0 ≤ σ) (hH : Integrable H)
    (hsupp : ∀ᵐ a ∂(volume : Measure (EuclideanSpace ℝ (Fin d))), a ∉ bandCube d σ → H a = 0) :
    ContDiff ℝ ⊤ (FT d H) :=
  (contDiff_complex_FT H hσ hH hsupp).restrict_scalars ℝ

end Analytic


section NormBound

lemma pi_single_expand {d : ℕ} (u : Fin d → ℂ) :
    u = ∑ k : Fin d, u k • (Pi.single k (1:ℂ)) := by
  funext k'
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [Finset.sum_eq_single k']
  · simp
  · intro b _ hb
    rw [Pi.single_eq_of_ne (Ne.symm hb)]; simp
  · intro h; exact absurd (Finset.mem_univ k') h

lemma expand_apply {d m : ℕ}
    (U : ContinuousMultilinearMap ℂ (fun _ : Fin m => (Fin d → ℂ)) ℂ)
    (v : Fin m → (Fin d → ℂ)) :
    U v = ∑ i : Fin m → Fin d, (∏ j : Fin m, v j (i j)) •
      U (fun j : Fin m => Pi.single (i j) (1:ℂ)) := by
  have hv : v = fun j => ∑ k : Fin d, v j k • (Pi.single k (1:ℂ)) := by
    funext j; exact pi_single_expand (v j)
  have hmap : U (fun j : Fin m => ∑ k : Fin d, v j k • (Pi.single k (1:ℂ)))
      = ∑ i : Fin m → Fin d, U (fun j : Fin m => v j (i j) • Pi.single (i j) (1:ℂ)) :=
    MultilinearMap.map_sum (f := U.toMultilinearMap) (g := fun j k => v j k • Pi.single k (1:ℂ))
  conv_lhs => rw [hv]
  rw [hmap]
  apply Finset.sum_congr rfl
  intro i _
  rw [show U (fun j : Fin m => v j (i j) • Pi.single (i j) (1:ℂ))
      = (∏ j : Fin m, v j (i j)) • U (fun j : Fin m => Pi.single (i j) (1:ℂ)) from
        MultilinearMap.map_smul_univ (f := U.toMultilinearMap) (c := fun j => v j (i j))
          (m := fun j => Pi.single (i j) (1:ℂ))]

/-- If an `ℝ`-multilinear map is the restriction of a `ℂ`-multilinear map then its operator norm
is bounded by the sum of the norms of its values on the standard basis tuples. -/
lemma norm_le_sum_apply_single {d m : ℕ}
    (T : ContinuousMultilinearMap ℝ (fun _ : Fin m => (Fin d → ℂ)) ℂ)
    (U : ContinuousMultilinearMap ℂ (fun _ : Fin m => (Fin d → ℂ)) ℂ)
    (h : ∀ v, T v = U v) :
    ‖T‖ ≤ ∑ i : Fin m → Fin d, ‖T (fun j : Fin m => Pi.single (i j) (1:ℂ))‖ := by
  refine ContinuousMultilinearMap.opNorm_le_bound (by positivity) (fun v => ?_)
  have hU : U v = ∑ i : Fin m → Fin d, (∏ j : Fin m, v j (i j)) •
      U (fun j : Fin m => Pi.single (i j) (1:ℂ)) := expand_apply U v
  calc ‖T v‖ = ‖U v‖ := by rw [h v]
    _ = ‖∑ i : Fin m → Fin d, (∏ j : Fin m, v j (i j)) •
          U (fun j : Fin m => Pi.single (i j) (1:ℂ))‖ := by rw [hU]
    _ ≤ ∑ i : Fin m → Fin d, ‖(∏ j : Fin m, v j (i j)) •
          U (fun j : Fin m => Pi.single (i j) (1:ℂ))‖ := norm_sum_le _ _
    _ ≤ ∑ i : Fin m → Fin d, (∏ j : Fin m, ‖v j‖) *
          ‖T (fun j : Fin m => Pi.single (i j) (1:ℂ))‖ := by
        apply Finset.sum_le_sum
        intro i _
        rw [norm_smul, norm_prod, ← h (fun j : Fin m => Pi.single (i j) (1:ℂ))]
        apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
        apply Finset.prod_le_prod (fun j _ => norm_nonneg _) (fun j _ => norm_le_pi_norm (v j) (i j))
    _ = (∏ j : Fin m, ‖v j‖) *
          ∑ i : Fin m → Fin d, ‖T (fun j : Fin m => Pi.single (i j) (1:ℂ))‖ := by
        rw [Finset.mul_sum]
    _ = (∑ i : Fin m → Fin d, ‖T (fun j : Fin m => Pi.single (i j) (1:ℂ))‖) *
          (∏ j : Fin m, ‖v j‖) := by
        rw [mul_comm]

end NormBound


section Support

lemma measurableSet_bandCube (d : ℕ) (σ : ℝ) : MeasurableSet (bandCube d σ) := by
  rw [show bandCube d σ = ⋂ i : Fin d, (EuclideanSpace.proj i) ⁻¹' Set.Icc (-σ) σ by
    ext ξ; simp [bandCube, abs_le]]
  exact MeasurableSet.iInter fun i =>
    (isClosed_Icc.preimage (EuclideanSpace.proj i).continuous).measurableSet

lemma volume_bandCube_lt_top (d : ℕ) (σ : ℝ) : volume (bandCube d σ) < ∞ := by
  have hsub : bandCube d σ ⊆ Metric.closedBall (0 : EuclideanSpace ℝ (Fin d))
      (Real.sqrt d * |σ| + 1) := by
    intro ξ hξ
    have hσ0 : 0 ≤ σ ∨ d = 0 := by
      rcases Nat.eq_zero_or_pos d with hd | hd
      · exact Or.inr hd
      · exact Or.inl (le_trans (abs_nonneg _) (hξ ⟨0, hd⟩))
    rw [Metric.mem_closedBall, dist_eq_norm, sub_zero]
    have hsum : ∑ i : Fin d, (ξ i) ^ 2 ≤ (d:ℝ) * σ ^ 2 := by
      calc ∑ i : Fin d, (ξ i) ^ 2 ≤ ∑ _ : Fin d, σ ^ 2 := by
            apply Finset.sum_le_sum
            intro i _
            exact sq_le_sq' (abs_le.mp (hξ i)).1 (abs_le.mp (hξ i)).2
        _ = (d:ℝ) * σ ^ 2 := by rw [Finset.sum_const, Finset.card_fin, nsmul_eq_mul]
    rcases hσ0 with hσ0 | hd0
    · have hnorm : ‖ξ‖ ^ 2 = ∑ i : Fin d, (ξ i) ^ 2 := by
        rw [EuclideanSpace.norm_sq_eq]; simp
      have hle : ‖ξ‖ ≤ Real.sqrt ((d:ℝ) * σ ^ 2) := by
        rw [← Real.sqrt_sq (norm_nonneg ξ), hnorm]
        exact Real.sqrt_le_sqrt hsum
      refine hle.trans ?_
      rw [Real.sqrt_mul (Nat.cast_nonneg d), Real.sqrt_sq_eq_abs]
      linarith [abs_nonneg σ]
    · subst hd0
      have hzero : ξ = 0 := Subsingleton.eq_zero ξ
      rw [hzero, norm_zero]
      positivity
  have : IsFiniteMeasureOnCompacts (volume : Measure (EuclideanSpace ℝ (Fin d))) := inferInstance
  exact lt_of_le_of_lt (measure_mono hsub) ((isCompact_closedBall _ _).measure_lt_top)

lemma memLp_one_of_memLp_two_of_ae_support_cube (d : ℕ) (σ : ℝ)
    {G : EuclideanSpace ℝ (Fin d) → ℂ}
    (h2 : MemLp G 2 (volume : Measure (EuclideanSpace ℝ (Fin d))))
    (hsupp : ∀ᵐ ξ ∂(volume : Measure (EuclideanSpace ℝ (Fin d))),
      ξ ∉ bandCube d σ → G ξ = 0) :
    MemLp G 1 (volume : Measure (EuclideanSpace ℝ (Fin d))) := by
  have hG_eq : G =ᵐ[(volume : Measure (EuclideanSpace ℝ (Fin d)))]
      (bandCube d σ).indicator G := by
    filter_upwards [hsupp] with ξ hξ
    by_cases h : ξ ∈ bandCube d σ
    · rw [Set.indicator_of_mem h]
    · rw [Set.indicator_of_notMem h]; exact hξ h
  have h2' : MemLp ((bandCube d σ).indicator G) 2
      (volume : Measure (EuclideanSpace ℝ (Fin d))) := h2.ae_eq hG_eq
  have hs_ne_top : volume (bandCube d σ) ≠ ∞ := ne_of_lt (volume_bandCube_lt_top d σ)
  have h1' : MemLp ((bandCube d σ).indicator G) 1
      (volume : Measure (EuclideanSpace ℝ (Fin d))) :=
    MemLp.mono_exponent_of_measure_support_ne_top h2'
      (fun x hx => Set.indicator_of_notMem hx G) hs_ne_top (by norm_num)
  exact h1'.ae_eq hG_eq.symm

end Support


section Final

/-- The real-linear embedding `ℝᵈ → ℂᵈ`. -/
noncomputable def iotaL (d : ℕ) : EuclideanSpace ℝ (Fin d) →L[ℝ] (Fin d → ℂ) :=
  ContinuousLinearMap.pi (fun i => Complex.ofRealCLM.comp (EuclideanSpace.proj i))

@[simp] lemma iotaL_apply (v : EuclideanSpace ℝ (Fin d)) :
    iotaL d v = fun i => (v i : ℂ) := rfl

@[simp] lemma iotaL_single (i : Fin d) :
    iotaL d (EuclideanSpace.single i (1:ℝ)) = Pi.single i (1:ℂ) := by
  ext j; rw [iotaL_apply]; simp only [PiLp.single_apply, Pi.single_apply]
  split <;> simp

lemma fourierPowSMulRight_single (H : EuclideanSpace ℝ (Fin d) → ℂ)
    (a : EuclideanSpace ℝ (Fin d)) (m : ℕ) (i : Fin m → Fin d) :
    VectorFourier.fourierPowSMulRight (-innerSL ℝ) H a m
        (fun j => EuclideanSpace.single (i j) (1:ℝ))
      = (2 * Real.pi * Complex.I) ^ m • ((∏ j, (a (i j) : ℂ)) • H a) := by
  rw [VectorFourier.fourierPowSMulRight_apply]
  have hprod : (∏ j : Fin m, (-innerSL ℝ) a (EuclideanSpace.single (i j) (1:ℝ)))
      = ∏ j : Fin m, -(a (i j)) := by
    apply Finset.prod_congr rfl; intro j _
    simp only [neg_apply, innerSL_apply_apply]
    rw [EuclideanSpace.inner_single_right]; simp
  rw [hprod, Finset.prod_neg, Finset.card_fin]
  simp only [Complex.real_smul]
  push_cast
  rw [show -(2 * Real.pi * Complex.I) = (-1) * (2 * Real.pi * Complex.I) by ring, mul_pow, neg_pow]
  have h1 : (-1:ℂ)^m * (-1)^m = 1 := by rw [← pow_add]; exact Even.neg_one_pow ⟨m, by ring⟩
  linear_combination ((2 * ↑Real.pi * Complex.I) ^ m * (∏ x, ↑(a (i x))) * H a) * h1

lemma enorm_fourierInv (Y : Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin d)))) :
    ‖𝓕⁻ Y‖ₑ = ‖Y‖ₑ := by
  have h : ‖𝓕⁻ Y‖ = ‖Y‖ := by
    have := MeasureTheory.Lp.norm_fourier_eq (𝓕⁻ Y)
    rw [FourierInvPair.fourier_fourierInv_eq] at this
    exact this.symm
  rw [MeasureTheory.Lp.enorm_def, MeasureTheory.Lp.enorm_def]
  rw [MeasureTheory.Lp.norm_def, MeasureTheory.Lp.norm_def] at h
  rcases (ENNReal.toReal_eq_toReal_iff _ _).mp h with h' | ⟨h1,h2⟩ | ⟨h1,h2⟩
  · exact h'
  · exact absurd h2 (MeasureTheory.Lp.eLpNorm_ne_top Y)
  · exact absurd h1 (MeasureTheory.Lp.eLpNorm_ne_top _)

lemma lp_enorm_sq_eq_lintegral (g : Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin d)))) :
    ‖g‖ₑ ^ (2:ℝ) = ∫⁻ x, ‖(g : EuclideanSpace ℝ (Fin d) → ℂ) x‖ₑ ^ (2:ℝ) := by
  rw [MeasureTheory.Lp.enorm_def,
      MeasureTheory.eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)]
  have h2 : (2:ℝ≥0∞).toReal = 2 := by simp
  rw [h2, show (1:ℝ)/(2:ℝ) = 1/2 by norm_num, ← ENNReal.rpow_mul]
  norm_num

/-- Plancherel's theorem in `lintegral` form for an `L¹ ∩ L²` function. -/
lemma lintegral_norm_sq_fourierInv {Ψ : EuclideanSpace ℝ (Fin d) → ℂ}
    (h1 : MemLp Ψ 1 (volume : Measure (EuclideanSpace ℝ (Fin d))))
    (h2 : MemLp Ψ 2 (volume : Measure (EuclideanSpace ℝ (Fin d)))) :
    ∫⁻ x, ‖𝓕⁻ Ψ x‖ₑ ^ (2:ℝ) = ∫⁻ a, ‖Ψ a‖ₑ ^ (2:ℝ) := by
  have hcoe := fourierInv_toLp_ae_eq_fourierInv h1 h2
  have hL : ∫⁻ x, ‖𝓕⁻ Ψ x‖ₑ ^ (2:ℝ) = ‖𝓕⁻ (h2.toLp Ψ)‖ₑ ^ (2:ℝ) := by
    rw [lp_enorm_sq_eq_lintegral (𝓕⁻ (h2.toLp Ψ))]
    apply lintegral_congr_ae
    filter_upwards [hcoe] with x hx
    rw [hx]
  have hH : ∫⁻ a, ‖Ψ a‖ₑ ^ (2:ℝ) = ‖h2.toLp Ψ‖ₑ ^ (2:ℝ) := by
    rw [lp_enorm_sq_eq_lintegral (h2.toLp Ψ)]
    apply lintegral_congr_ae
    filter_upwards [h2.coeFn_toLp] with a ha
    rw [ha]
  rw [hL, hH, enorm_fourierInv]

/-- Plancherel's theorem in integral form for an `L¹ ∩ L²` function. -/
lemma integral_norm_sq_fourierInv {Ψ : EuclideanSpace ℝ (Fin d) → ℂ}
    (h1 : MemLp Ψ 1 (volume : Measure (EuclideanSpace ℝ (Fin d))))
    (h2 : MemLp Ψ 2 (volume : Measure (EuclideanSpace ℝ (Fin d)))) :
    ∫ x, ‖𝓕⁻ Ψ x‖ ^ 2 = ∫ a, ‖Ψ a‖ ^ 2 := by
  have hcoe := fourierInv_toLp_ae_eq_fourierInv h1 h2
  have hc : AEStronglyMeasurable (fun x => ‖𝓕⁻ Ψ x‖ ^ 2)
      (volume : Measure (EuclideanSpace ℝ (Fin d))) := by
    have hthis : AEStronglyMeasurable
        (fun x => ‖(𝓕⁻ (h2.toLp Ψ) : Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin d)))) x‖ ^ 2)
        (volume : Measure (EuclideanSpace ℝ (Fin d))) :=
      (MeasureTheory.Lp.aestronglyMeasurable (𝓕⁻ (h2.toLp Ψ))).norm.pow 2
    refine hthis.congr ?_
    filter_upwards [hcoe] with x hx
    rw [hx]
  have hd : AEStronglyMeasurable (fun x => ‖Ψ x‖ ^ 2)
      (volume : Measure (EuclideanSpace ℝ (Fin d))) := h2.aestronglyMeasurable.norm.pow 2
  rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall fun x => sq_nonneg _) hc,
    integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall fun x => sq_nonneg _) hd]
  have key1 : ∀ a : EuclideanSpace ℝ (Fin d),
      ENNReal.ofReal (‖𝓕⁻ Ψ a‖ ^ 2) = ‖𝓕⁻ Ψ a‖ₑ ^ (2:ℝ) := by
    intro a; rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm, ENNReal.rpow_ofNat]
  have key2 : ∀ a : EuclideanSpace ℝ (Fin d),
      ENNReal.ofReal (‖Ψ a‖ ^ 2) = ‖Ψ a‖ₑ ^ (2:ℝ) := by
    intro a; rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm, ENNReal.rpow_ofNat]
  simp_rw [key1, key2]
  rw [lintegral_norm_sq_fourierInv h1 h2]

end Final


section Assembly

variable {H : EuclideanSpace ℝ (Fin d) → ℂ}

lemma integrable_norm_pow_mul {σ : ℝ} (hσ : 0 ≤ σ) (hH : Integrable H)
    (hsupp : ∀ᵐ a ∂(volume : Measure (EuclideanSpace ℝ (Fin d))), a ∉ bandCube d σ → H a = 0)
    (n : ℕ) : Integrable (fun a : EuclideanSpace ℝ (Fin d) => ‖a‖ ^ n * ‖H a‖) := by
  have hbase : Integrable (fun a : EuclideanSpace ℝ (Fin d) =>
      (Real.sqrt d * |σ| + 1) ^ n * ‖H a‖) :=
    hH.norm.const_mul ((Real.sqrt d * |σ| + 1) ^ n)
  refine hbase.mono' ?_ ?_
  · exact ((continuous_norm.pow n).aestronglyMeasurable).mul hH.norm.aestronglyMeasurable
  · filter_upwards [hsupp] with a ha
    by_cases hmem : a ∈ bandCube d σ
    · have ha' : ‖a‖ ≤ Real.sqrt d * |σ| + 1 := by
        have hσ0 : 0 ≤ σ ∨ d = 0 := by
          rcases Nat.eq_zero_or_pos d with hd | hd
          · exact Or.inr hd
          · exact Or.inl (le_trans (abs_nonneg _) (hmem ⟨0, hd⟩))
        rcases hσ0 with hσ0 | hd0
        · have hsum : ∑ i : Fin d, (a i) ^ 2 ≤ (d:ℝ) * σ ^ 2 := by
            calc ∑ i : Fin d, (a i) ^ 2 ≤ ∑ _ : Fin d, σ ^ 2 := by
                  apply Finset.sum_le_sum
                  intro i _
                  exact sq_le_sq' (abs_le.mp (hmem i)).1 (abs_le.mp (hmem i)).2
              _ = (d:ℝ) * σ ^ 2 := by rw [Finset.sum_const, Finset.card_fin, nsmul_eq_mul]
          have hnorm : ‖a‖ ^ 2 = ∑ i : Fin d, (a i) ^ 2 := by
            rw [EuclideanSpace.norm_sq_eq]; simp
          have hle : ‖a‖ ≤ Real.sqrt ((d:ℝ) * σ ^ 2) := by
            rw [← Real.sqrt_sq (norm_nonneg a), hnorm]; exact Real.sqrt_le_sqrt hsum
          refine hle.trans ?_
          rw [Real.sqrt_mul (Nat.cast_nonneg d), Real.sqrt_sq_eq_abs]
          linarith [abs_nonneg σ]
        · subst hd0
          have hzero : a = 0 := Subsingleton.eq_zero a
          rw [hzero, norm_zero]; positivity
      rw [Real.norm_eq_abs,
        abs_of_nonneg (mul_nonneg (pow_nonneg (norm_nonneg a) n) (norm_nonneg (H a)))]
      exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg a) ha' n)
        (norm_nonneg (H a))
    · rw [ha hmem]
      simp

end Assembly


lemma phase_iota_eq (x a : EuclideanSpace ℝ (Fin d)) :
    phase d (fun i => (x i : ℂ)) a
      = Complex.exp (↑(2 * Real.pi * inner ℝ a x) * Complex.I) := by
  rw [phase]
  congr 1
  rw [show inner ℝ a x = ∑ i, a i * x i from by simp [PiLp.inner_apply, mul_comm]]
  push_cast
  rw [Finset.mul_sum, Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  ring


lemma fourierIntegral_eq_fourierInv (φ : EuclideanSpace ℝ (Fin d) → ℂ)
    (x : EuclideanSpace ℝ (Fin d)) :
    VectorFourier.fourierIntegral 𝐞 volume
        (ContinuousLinearMap.toLinearMap₁₂ (-innerSL ℝ)) φ x = 𝓕⁻ φ x := by
  rw [VectorFourier.fourierIntegral, Real.fourierInv_eq']
  apply integral_congr_ae
  filter_upwards with a
  have harg : -((ContinuousLinearMap.toLinearMap₁₂ (-innerSL ℝ)) a) x = inner ℝ a x := by
    simp [ContinuousLinearMap.toLinearMap₁₂_apply]
  rw [harg, Circle.smul_def, Real.fourierChar_apply]

/-- The mixed symbol `(2πi)^m ∏ a_{i_j} · H`. -/
noncomputable def mixSym (d : ℕ) (m : ℕ) (H : EuclideanSpace ℝ (Fin d) → ℂ) (i : Fin m → Fin d) :
    EuclideanSpace ℝ (Fin d) → ℂ :=
  fun a => (2 * Real.pi * Complex.I) ^ m * (∏ j : Fin m, (a (i j) : ℂ)) * H a

lemma continuous_mixSym_fst (m : ℕ) (i : Fin m → Fin d) :
    Continuous (fun a : EuclideanSpace ℝ (Fin d) =>
      (2 * Real.pi * Complex.I) ^ m * (∏ j : Fin m, (a (i j) : ℂ))) := by
  apply Continuous.mul continuous_const
  apply continuous_finsetProd
  intro j _
  exact Complex.continuous_ofReal.comp (EuclideanSpace.proj (i j)).continuous

lemma norm_mixSym_le {σ : ℝ} (hσ : 0 ≤ σ) (m : ℕ) (H : EuclideanSpace ℝ (Fin d) → ℂ)
    (i : Fin m → Fin d) (a : EuclideanSpace ℝ (Fin d)) (ha : a ∈ bandCube d σ) :
    ‖mixSym d m H i a‖ ≤ (2 * Real.pi * σ) ^ m * ‖H a‖ := by
  have hni : ‖(2 * Real.pi * Complex.I : ℂ)‖ = 2 * Real.pi := norm_iota
  rw [mixSym, norm_mul, norm_mul, norm_pow, hni]
  have h1 : ‖∏ j : Fin m, (a (i j) : ℂ)‖ ≤ σ ^ m := by
    rw [norm_prod]
    calc ∏ j : Fin m, ‖(a (i j) : ℂ)‖ = ∏ j : Fin m, |a (i j)| := by
          apply Finset.prod_congr rfl; intro j _; rw [Complex.norm_real, Real.norm_eq_abs]
      _ ≤ ∏ _ : Fin m, σ := Finset.prod_le_prod (fun j _ => abs_nonneg _) (fun j _ => ha (i j))
      _ = σ ^ m := by rw [Finset.prod_const, Finset.card_fin]
  have heq : (2 * Real.pi * σ) ^ m = (2 * Real.pi) ^ m * σ ^ m := by rw [mul_pow]
  rw [heq]
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h1 (by positivity))
    (norm_nonneg _)

lemma memLp_mixSym {σ : ℝ} (hσ : 0 ≤ σ) (m : ℕ) {H : EuclideanSpace ℝ (Fin d) → ℂ}
    {p : ℝ≥0∞} (hH : MemLp H p (volume : Measure (EuclideanSpace ℝ (Fin d))))
    (hsupp : ∀ᵐ a ∂(volume : Measure (EuclideanSpace ℝ (Fin d))), a ∉ bandCube d σ → H a = 0)
    (i : Fin m → Fin d) :
    MemLp (mixSym d m H i) p (volume : Measure (EuclideanSpace ℝ (Fin d))) := by
  refine MemLp.of_le (hH.const_mul (((2 * Real.pi * σ) ^ m : ℝ) : ℂ)) ?_ ?_
  · exact ((continuous_mixSym_fst m i).aestronglyMeasurable).mul hH.aestronglyMeasurable
  · filter_upwards [hsupp] with a ha
    by_cases hmem : a ∈ bandCube d σ
    · calc ‖mixSym d m H i a‖ ≤ (2 * Real.pi * σ) ^ m * ‖H a‖ := norm_mixSym_le hσ m H i a hmem
        _ = ‖(((2 * Real.pi * σ) ^ m : ℝ) : ℂ) * H a‖ := by
              rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    · simp [mixSym, ha hmem]

lemma integrable_mixSym {σ : ℝ} (hσ : 0 ≤ σ) (m : ℕ) {H : EuclideanSpace ℝ (Fin d) → ℂ}
    (hH : MemLp H 1 (volume : Measure (EuclideanSpace ℝ (Fin d))))
    (hsupp : ∀ᵐ a ∂(volume : Measure (EuclideanSpace ℝ (Fin d))), a ∉ bandCube d σ → H a = 0)
    (i : Fin m → Fin d) : Integrable (mixSym d m H i) :=
  memLp_one_iff_integrable.mp (memLp_mixSym hσ m hH hsupp i)

lemma integrable_norm_sq {H : EuclideanSpace ℝ (Fin d) → ℂ}
    (hH : MemLp H 2 (volume : Measure (EuclideanSpace ℝ (Fin d)))) :
    Integrable (fun a : EuclideanSpace ℝ (Fin d) => ‖H a‖ ^ 2) :=
  (memLp_two_iff_integrable_sq_norm hH.aestronglyMeasurable).mp hH

theorem bandlimited_entire_extension_cube (d : ℕ) (σ : ℝ) (hσ : 0 ≤ σ)
    (f : EuclideanSpace ℝ (Fin d) → ℂ)
    (hf : MemLp f 2 (volume : Measure (EuclideanSpace ℝ (Fin d))))
    (hsupp : ∀ᵐ ξ ∂(volume : Measure (EuclideanSpace ℝ (Fin d))),
      ξ ∉ {ξ : EuclideanSpace ℝ (Fin d) | ∀ i : Fin d, |ξ i| ≤ σ} →
      ((𝓕 (hf.toLp f) : Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin d)))) :
        EuclideanSpace ℝ (Fin d) → ℂ) ξ = 0) :
    ∃ F : (Fin d → ℂ) → ℂ, Differentiable ℂ F ∧
      (∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin d))),
        F (fun i : Fin d => (x i : ℂ)) = f x) ∧
      (∀ m : ℕ,
        Integrable (fun x : EuclideanSpace ℝ (Fin d) =>
          ‖iteratedFDeriv ℝ m F (fun i : Fin d => (x i : ℂ))‖ ^ 2) ∧
        (∫ x : EuclideanSpace ℝ (Fin d),
          ‖iteratedFDeriv ℝ m F (fun i : Fin d => (x i : ℂ))‖ ^ 2) ≤
          (2 * Real.pi * σ * d) ^ (2 * m) *
            (∫ x : EuclideanSpace ℝ (Fin d), ‖F (fun i : Fin d => (x i : ℂ))‖ ^ 2)) := by
  classical
  set Hg : Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin d))) := 𝓕 (hf.toLp f) with hHg
  set H : EuclideanSpace ℝ (Fin d) → ℂ := ⇑Hg with hHdef
  have hHmem : MemLp H 2 (volume : Measure (EuclideanSpace ℝ (Fin d))) := Lp.memLp Hg
  have hHsupp : ∀ᵐ ξ ∂(volume : Measure (EuclideanSpace ℝ (Fin d))),
      ξ ∉ bandCube d σ → H ξ = 0 := hsupp
  have hH1 : MemLp H 1 (volume : Measure (EuclideanSpace ℝ (Fin d))) :=
    memLp_one_of_memLp_two_of_ae_support_cube d σ hHmem hHsupp
  have hHint : Integrable H := memLp_one_iff_integrable.mp hH1
  have hpt : ∀ x : EuclideanSpace ℝ (Fin d), FT d H (fun i => (x i : ℂ)) = 𝓕⁻ H x := by
    intro x
    rw [FT, Real.fourierInv_eq']
    apply integral_congr_ae
    filter_upwards with a
    rw [phase_iota_eq, mul_comm]
    rfl
  refine ⟨FT d H, differentiable_FT H hσ hHint hHsupp, ?_, ?_⟩
  · -- almost-everywhere equality with `f`
    have h1 : (fun x => 𝓕⁻ H x) =ᵐ[(volume : Measure (EuclideanSpace ℝ (Fin d)))]
        ((𝓕⁻ (hHmem.toLp H) : Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin d)))) :
          EuclideanSpace ℝ (Fin d) → ℂ) :=
      (fourierInv_toLp_ae_eq_fourierInv hH1 hHmem).symm
    have h3 : (hHmem.toLp H) = Hg := Lp.toLp_coeFn Hg (Lp.memLp Hg)
    have h4 : ((𝓕⁻ Hg : Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin d))))) = hf.toLp f := by
      change ((𝓕⁻ (𝓕 (hf.toLp f)) : Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin d))))) =
        hf.toLp f
      rw [fourierInv_fourier_eq]
    have h5 : ((𝓕⁻ (hHmem.toLp H) : Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin d)))) :
          EuclideanSpace ℝ (Fin d) → ℂ) =ᵐ[(volume : Measure (EuclideanSpace ℝ (Fin d)))] f := by
      filter_upwards [MemLp.coeFn_toLp hf] with x hx
      have hx' : ((𝓕⁻ (hHmem.toLp H) : Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin d)))) :
            EuclideanSpace ℝ (Fin d) → ℂ) x = (hf.toLp f : EuclideanSpace ℝ (Fin d) → ℂ) x := by
        rw [h3, h4]
      rw [hx', hx]
    filter_upwards [h1, h5] with x hx1 hx5
    rw [hpt x, hx1, hx5]
  · intro m
    have hC : ContDiff ℂ ⊤ (FT d H) := contDiff_complex_FT H hσ hHint hHsupp
    have hR : ContDiff ℝ ⊤ (FT d H) := contDiff_real_FT H hσ hHint hHsupp
    set G : EuclideanSpace ℝ (Fin d) → ℂ := fun x => FT d H (iotaL d x) with hGdef
    have hGinv : G = fun x => 𝓕⁻ H x := by
      funext x
      rw [hGdef]
      simp only [iotaL_apply]
      exact hpt x
    have hchain : ∀ x : EuclideanSpace ℝ (Fin d), iteratedFDeriv ℝ m G x
        = (iteratedFDeriv ℝ m (FT d H) (iotaL d x)).compContinuousLinearMap (fun _ => iotaL d) :=
      fun x => ContinuousLinearMap.iteratedFDeriv_comp_right (iotaL d) hR x le_top
    have hres : ∀ x : EuclideanSpace ℝ (Fin d), iteratedFDeriv ℝ m (FT d H) (iotaL d x)
        = (iteratedFDeriv ℂ m (FT d H) (iotaL d x)).restrictScalars ℝ :=
      fun x => (ContDiffAt.restrictScalars_iteratedFDeriv (𝕜 := ℝ) (𝕜' := ℂ)
        ((hC.contDiffAt).of_le le_top)).symm
    have hpoint : ∀ x : EuclideanSpace ℝ (Fin d),
        ‖iteratedFDeriv ℝ m (FT d H) (iotaL d x)‖
          ≤ ∑ i : Fin m → Fin d,
              ‖(iteratedFDeriv ℝ m G x) (fun j => EuclideanSpace.single (i j) (1:ℝ))‖ := by
      intro x
      have hwit : ∀ v, iteratedFDeriv ℝ m (FT d H) (iotaL d x) v
          = iteratedFDeriv ℂ m (FT d H) (iotaL d x) v := by
        intro v; rw [hres x]; rfl
      refine (norm_le_sum_apply_single _ _ hwit).trans ?_
      apply Finset.sum_le_sum
      intro i _
      rw [hchain x, ContinuousMultilinearMap.compContinuousLinearMap_apply]
      simp only [iotaL_single]
      exact le_rfl
    have hHgeo : ∀ n : ℕ, Integrable (fun a : EuclideanSpace ℝ (Fin d) =>
        ‖a‖ ^ n * ‖H a‖) := fun n => integrable_norm_pow_mul hσ hHint hHsupp n
    have hmix : ∀ (x : EuclideanSpace ℝ (Fin d)) (i : Fin m → Fin d),
        (iteratedFDeriv ℝ m G x) (fun j => EuclideanSpace.single (i j) (1:ℝ))
          = 𝓕⁻ (mixSym d m H i) x := by
      intro x i
      rw [hGinv]
      rw [show (fun y : EuclideanSpace ℝ (Fin d) => 𝓕⁻ H y)
          = fun y => VectorFourier.fourierIntegral 𝐞 volume
              (ContinuousLinearMap.toLinearMap₁₂ (-innerSL ℝ)) H y from by
        funext y; exact (fourierIntegral_eq_fourierInv H y).symm]
      rw [VectorFourier.iteratedFDeriv_fourierIntegral (-innerSL ℝ) (fun n _ => hHgeo n)
        hHmem.1 (le_top)]
      rw [Real.fourierIntegral_continuousMultilinearMap_apply'
        (VectorFourier.integrable_fourierPowSMulRight (-innerSL ℝ) (hHgeo m) hHmem.1)]
      rw [fourierIntegral_eq_fourierInv]
      rw [show (fun y : EuclideanSpace ℝ (Fin d) =>
            VectorFourier.fourierPowSMulRight (-innerSL ℝ) H y m
              (fun j => EuclideanSpace.single (i j) (1:ℝ))) = mixSym d m H i from by
        funext a
        rw [fourierPowSMulRight_single, mixSym]
        simp only [smul_eq_mul, mul_assoc]]
    -- Plancherel for each `i` and the final assembly
    have hInt2 : ∀ i : Fin m → Fin d,
        Integrable (fun x : EuclideanSpace ℝ (Fin d) =>
          ‖𝓕⁻ (mixSym d m H i) x‖ ^ 2) := by
      intro i
      have h2 : MemLp (mixSym d m H i) 2 (volume : Measure (EuclideanSpace ℝ (Fin d))) :=
        memLp_mixSym hσ m hHmem hHsupp i
      have h1 : MemLp (mixSym d m H i) 1 (volume : Measure (EuclideanSpace ℝ (Fin d))) :=
        memLp_mixSym hσ m hH1 hHsupp i
      have hcoe := fourierInv_toLp_ae_eq_fourierInv h1 h2
      have hbase : Integrable (fun x : EuclideanSpace ℝ (Fin d) =>
          ‖(𝓕⁻ (h2.toLp (mixSym d m H i)) :
            Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin d)))) x‖ ^ 2) :=
        (memLp_two_iff_integrable_sq_norm (MeasureTheory.Lp.aestronglyMeasurable
          (𝓕⁻ (h2.toLp (mixSym d m H i))))).mp
          (MeasureTheory.Lp.memLp (𝓕⁻ (h2.toLp (mixSym d m H i))))
      have heq : (fun x : EuclideanSpace ℝ (Fin d) =>
            ‖(𝓕⁻ (h2.toLp (mixSym d m H i)) :
              Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin d)))) x‖ ^ 2)
          =ᵐ[(volume : Measure (EuclideanSpace ℝ (Fin d)))]
            (fun x => ‖𝓕⁻ (mixSym d m H i) x‖ ^ 2) :=
        hcoe.fun_comp (fun z : ℂ => ‖z‖ ^ 2)
      exact hbase.congr heq
    have hPointwise : ∀ x : EuclideanSpace ℝ (Fin d),
        ‖iteratedFDeriv ℝ m (FT d H) (iotaL d x)‖ ^ 2
          ≤ (d : ℝ) ^ m * ∑ i : Fin m → Fin d, ‖𝓕⁻ (mixSym d m H i) x‖ ^ 2 := by
      intro x
      have h1 := hpoint x
      have h2 : ‖iteratedFDeriv ℝ m (FT d H) (iotaL d x)‖ ^ 2
          ≤ (∑ i : Fin m → Fin d,
              ‖(iteratedFDeriv ℝ m G x) (fun j => EuclideanSpace.single (i j) (1:ℝ))‖) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) h1 2
      refine h2.trans ?_
      simp only [hmix]
      have := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset (Fin m → Fin d)))
        (f := fun i => ‖𝓕⁻ (mixSym d m H i) x‖)
      simpa [Finset.card_univ, Fintype.card_fun, Fintype.card_fin, Nat.cast_pow] using this
    -- integrability of the target
    have hTint : Integrable (fun x : EuclideanSpace ℝ (Fin d) =>
        ‖iteratedFDeriv ℝ m (FT d H) (iotaL d x)‖ ^ 2) := by
      have hsum : Integrable (fun x : EuclideanSpace ℝ (Fin d) =>
          (d : ℝ) ^ m * ∑ i : Fin m → Fin d, ‖𝓕⁻ (mixSym d m H i) x‖ ^ 2) := by
        refine Integrable.const_mul ?_ _
        exact integrable_finsetSum Finset.univ (fun i _ => hInt2 i)
      refine hsum.mono' ?_ ?_
      · have hcont : Continuous (fun x : EuclideanSpace ℝ (Fin d) =>
            iteratedFDeriv ℝ m (FT d H) (iotaL d x)) :=
          (hR.continuous_iteratedFDeriv (by simp)).comp (iotaL d).continuous
        exact (hcont.norm.pow 2).aestronglyMeasurable
      · filter_upwards with x
        rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
        exact hPointwise x
    have hpl : ∫ a : EuclideanSpace ℝ (Fin d), ‖H a‖ ^ 2
        = ∫ x : EuclideanSpace ℝ (Fin d), ‖FT d H (fun i : Fin d => (x i : ℂ))‖ ^ 2 := by
      rw [(integral_norm_sq_fourierInv hH1 hHmem).symm]
      apply integral_congr_ae
      filter_upwards with x
      rw [hpt x]
    refine ⟨hTint, ?_⟩
    set_option maxHeartbeats 8000000 in
    have hIntBound : ∀ i : Fin m → Fin d,
        ∫ x, ‖𝓕⁻ (mixSym d m H i) x‖ ^ 2 ≤ (2 * Real.pi * σ) ^ (2 * m) *
          ∫ a, ‖H a‖ ^ 2 := by
      intro i
      have h2 : MemLp (mixSym d m H i) 2 (volume : Measure (EuclideanSpace ℝ (Fin d))) :=
        memLp_mixSym hσ m hHmem hHsupp i
      have h1 : MemLp (mixSym d m H i) 1 (volume : Measure (EuclideanSpace ℝ (Fin d))) :=
        memLp_mixSym hσ m hH1 hHsupp i
      rw [integral_norm_sq_fourierInv h1 h2]
      calc ∫ a, ‖mixSym d m H i a‖ ^ 2
          ≤ ∫ a, ((2 * Real.pi * σ) ^ (2 * m) * ‖H a‖ ^ 2) := by
            apply integral_mono_ae
              ((memLp_two_iff_integrable_sq_norm h2.aestronglyMeasurable).mp h2)
              ((integrable_norm_sq hHmem).const_mul _)
            filter_upwards [hHsupp] with a ha
            by_cases hmem : a ∈ bandCube d σ
            · have hb := norm_mixSym_le hσ m H i a hmem
              calc ‖mixSym d m H i a‖ ^ 2 ≤ ((2 * Real.pi * σ) ^ m * ‖H a‖) ^ 2 :=
                    pow_le_pow_left₀ (norm_nonneg _) hb 2
                _ = (2 * Real.pi * σ) ^ (2 * m) * ‖H a‖ ^ 2 := by
                    rw [mul_pow, ← pow_mul, show m * 2 = 2 * m by ring]
            · have hz : mixSym d m H i a = 0 := by simp [mixSym, ha hmem]
              rw [hz, norm_zero]
              simp only [pow_two, mul_zero]
              exact mul_nonneg (by positivity) (mul_self_nonneg _)

        _ = (2 * Real.pi * σ) ^ (2 * m) * ∫ a, ‖H a‖ ^ 2 := by
              rw [integral_const_mul]
    set_option maxHeartbeats 8000000 in
    calc ∫ x : EuclideanSpace ℝ (Fin d),
          ‖iteratedFDeriv ℝ m (FT d H) (iotaL d x)‖ ^ 2
        ≤ ∫ x : EuclideanSpace ℝ (Fin d),
            (d : ℝ) ^ m * ∑ i : Fin m → Fin d, ‖𝓕⁻ (mixSym d m H i) x‖ ^ 2 := by
          apply integral_mono_ae hTint
          · refine Integrable.const_mul ?_ _
            exact integrable_finsetSum Finset.univ (fun i _ => hInt2 i)
          · filter_upwards with x using hPointwise x
      _ = (d : ℝ) ^ m * ∑ i : Fin m → Fin d,
            ∫ x, ‖𝓕⁻ (mixSym d m H i) x‖ ^ 2 := by
          rw [integral_const_mul]
          congr 1
          exact integral_finsetSum Finset.univ (fun i _ => hInt2 i)
      _ ≤ (d : ℝ) ^ m * ∑ _i : Fin m → Fin d,
            (2 * Real.pi * σ) ^ (2 * m) * ∫ a, ‖H a‖ ^ 2 := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          exact Finset.sum_le_sum (fun i _ => hIntBound i)
      _ = (d : ℝ) ^ m * ((d : ℝ) ^ m *
            ((2 * Real.pi * σ) ^ (2 * m) * ∫ a, ‖H a‖ ^ 2)) := by
          rw [Finset.sum_const, nsmul_eq_mul]
          simp [Finset.card_univ, Fintype.card_fin, Nat.cast_pow]
      _ = (2 * Real.pi * σ * d) ^ (2 * m) * ∫ a, ‖H a‖ ^ 2 := by
          rw [mul_pow]
          ring
      _ = (2 * Real.pi * σ * d) ^ (2 * m) *
            ∫ x : EuclideanSpace ℝ (Fin d), ‖FT d H (fun i : Fin d => (x i : ℂ))‖ ^ 2 := by
          rw [hpl]

end Commons.Analysis.Fourier.LogvinenkoSereda