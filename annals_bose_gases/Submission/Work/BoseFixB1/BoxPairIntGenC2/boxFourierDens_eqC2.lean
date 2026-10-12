import Mathlib.Tactic.Have
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Fourier.FourierTransform
import Submission.Work.BoseFixB1.boxPairFibreAbsLe
import Submission.Work.BoseFixB1.measurable_boxPairFibreFun_uncurry
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB1.BoxPairIntGenC2.boxFourierDens_eqC2`

The Fourier transform of the box pair density `boxPairDensSum volA ℓ A χ Ψ` at `−u` is the
momentum-space pair content `boxPairDensFourier volA ℓ A χ Ψ ((2π) • u)`, for a window `χ`
that is only assumed `Continuous` (with compact support, vanishing off `A`) and a state `Ψ`
that is only `Continuous`.

The per-pair content of the proof is factored through the *abstract* change-of-variables
statement `perPairFourierGen`: for an arbitrary kernel `F : E3 × E3 → ℝ` which is merely
measurable and bounded on `acube ℓ × acube ℓ`,

`∫_v e^{2πi⟪u,v⟫} (∫_{z∈A} χ(z+v) χ z F(z+v,z)) = ∫_{A}∫_{A} χ y χ z e^{2πi⟪u,y−z⟫} F(y,z)`,

i.e. Fubini, the translation `y = z + v` (`integral_add_right_eq_self`) and the support
collapse of `χ` on `A`.  Keeping `F` abstract means the heavy box definitions
(`boxPairFibreFun`) never have to be unfolded inside the integral manipulations; they are
instantiated only once, when the general statement is applied to the box pair fibre.

The companion `integrableFourierDensGen` is the integrability of the Fourier-side integrand
(compact support plus a uniform bound), which is what makes the final interchange of the
finite pair sum with the `v`-integral legitimate.
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped Topology Real BigOperators ENNReal FourierTransform

namespace Work.BoseFixB1.BoxPairIntGenC2

open _root_.BoseGases Submission.BoseGases

local notation "E3" => EuclideanSpace ℝ (Fin 3)

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

/-! ## A generic integrability tool -/

/-- A function that vanishes off a compact set, is a.e. strongly measurable, and is bounded
on that compact set, is integrable. -/
theorem integrable_of_compact_bound_aux {α : Type*} [MeasurableSpace α] [TopologicalSpace α]
    [OpensMeasurableSpace α] [T2Space α] {μ : Measure α} [IsFiniteMeasureOnCompacts μ]
    {G : Type*} [NormedAddCommGroup G] {f : α → G} {K : Set α} (hK : IsCompact K)
    (hfm : AEStronglyMeasurable f μ) (hf0 : ∀ x, x ∉ K → f x = 0) {C : ℝ}
    (hC : ∀ x ∈ K, ‖f x‖ ≤ C) : Integrable f μ := by
  have hfin : μ K ≠ ∞ := hK.measure_lt_top.ne
  have hg : Integrable (K.indicator fun _ : α => (C : ℝ)) μ :=
    (integrable_indicator_iff hK.measurableSet).mpr (integrableOn_const hfin (by simp))
  refine hg.mono' hfm ?_
  filter_upwards with x
  by_cases hx : x ∈ K
  · rw [Set.indicator_of_mem hx]; exact hC x hx
  · rw [Set.indicator_of_notMem hx, hf0 x hx]; simp

/-! ## The box pair fibre is bounded on the cube -/

/-- On the cube `acube ℓ` the peeled box pair fibre is bounded, for a continuous state `Ψ`.
This is `Work.BoseFixB1.boxPairFibreAbsLe` fed with a bound of `Ψ` on the compact box
`abox (N+2) ℓ`. -/
theorem boxFibreBound_aux {N : ℕ} {ℓ volA : ℝ} {A : Set E3}
    (hA : MeasurableSet A) (hℓ : 0 < ℓ) (hAc : A ⊆ acube ℓ)
    (hvolA : volA = (MeasureTheory.volume A).toReal) (hvolpos : 0 < volA)
    {Ψ : X (N + 2) → ℝ} (hΨ : Continuous Ψ) (i j : Fin (N + 2)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ y ∈ acube ℓ, ∀ z ∈ acube ℓ,
      |boxPairFibreFun volA ℓ A Ψ i j y z| ≤ C := by
  obtain ⟨CΨ, hCΨ⟩ := IsCompact.exists_bound_of_continuousOn
    (abox_compact (N + 2) hℓ) hΨ.continuousOn
  refine ⟨4 * |CΨ| ^ 2 * ℓ ^ (3 * N), by positivity, ?_⟩
  intro y hy z hz
  have hΨB : ∀ x ∈ abox (N + 2) ℓ, |Ψ x| ≤ |CΨ| := by
    intro x hx
    have h := hCΨ x hx
    rw [Real.norm_eq_abs] at h
    exact le_trans h (le_abs_self CΨ)
  by_cases hij : i = j
  · have h0 : boxPairFibreFun volA ℓ A Ψ i j y z = 0 := by simp [boxPairFibreFun, hij]
    rw [h0, abs_zero]
    positivity
  · exact boxPairFibreAbsLe hA hℓ hAc hvolA hvolpos (abs_nonneg CΨ) hΨB hij hy hz

/-! ## The abstract per-pair Fourier identity -/

/-- **The per-pair Fourier identity, with an abstract kernel.**  For a measurable kernel `F`
bounded by `C` on the cube, the Fourier transform at `−u` of the relative-coordinate density
built from `F` equals the double `A`-integral of the window against `F` with the phase
`e^{i⟪(2π)u,y−z⟫}`. -/
theorem perPairFourierGen {ℓ : ℝ} {A : Set E3}
    (hA : MeasurableSet A) (hℓ : 0 < ℓ) (hAc : A ⊆ acube ℓ)
    {χ : E3 → ℝ} (hχc : Continuous χ) (hχs : HasCompactSupport χ)
    (hχsupp : ∀ z, z ∉ A → χ z = 0)
    {F : E3 × E3 → ℝ} (hFm : Measurable F) {C : ℝ} (hC0 : 0 ≤ C)
    (hFb : ∀ y ∈ acube ℓ, ∀ z ∈ acube ℓ, |F (y, z)| ≤ C)
    (u : E3) :
    (∫ v, Complex.exp (Complex.I * ((2 * Real.pi * inner ℝ u v : ℝ) : ℂ))
        * ((∫ z in A, χ (z + v) * χ z * F (z + v, z) : ℝ) : ℂ))
      = ∫ y in A, ∫ z in A, (χ y : ℂ) * (χ z : ℂ)
          * Complex.exp (Complex.I * ((inner ℝ ((2 * Real.pi : ℝ) • u) (y - z) : ℝ) : ℂ))
          * ((F (y, z) : ℝ) : ℂ) := by
  have hχmeas : Measurable χ := hχc.measurable
  -- the window is bounded
  obtain ⟨Cχ, hCχ0, hCχb⟩ : ∃ C : ℝ, 0 ≤ C ∧ ∀ z, |χ z| ≤ C := by
    obtain ⟨C', hC'⟩ := hχc.bounded_above_of_compact_support hχs
    exact ⟨C', le_trans (norm_nonneg (χ 0)) (hC' 0),
      fun z => by simpa [Real.norm_eq_abs] using hC' z⟩
  have hχAc : ∀ z : E3, z ∉ acube ℓ → χ z = 0 := fun z hz =>
    hχsupp z (fun hmem => hz (hAc hmem))
  obtain ⟨R, hR⟩ : ∃ R : ℝ, ∀ y ∈ acube ℓ, ‖y‖ ≤ R :=
    (acube_isBounded ℓ hℓ.le).exists_norm_le
  set E : E3 → ℂ := fun v => Complex.exp (Complex.I * ((2 * Real.pi * inner ℝ u v : ℝ) : ℂ))
    with hE
  have hnorm_exp : ∀ t : ℝ, ‖Complex.exp (Complex.I * (t : ℂ))‖ = 1 := by
    intro t
    rw [mul_comm Complex.I, Complex.norm_exp_ofReal_mul_I]
  have hEnorm : ∀ v : E3, ‖E v‖ = 1 := by
    intro v
    rw [hE]
    exact hnorm_exp (2 * Real.pi * inner ℝ u v)
  have hEcont : Continuous E := by
    rw [hE]
    refine Complex.continuous_exp.comp (continuous_const.mul (Complex.continuous_ofReal.comp ?_))
    exact continuous_const.mul (continuous_inner.comp (continuous_const.prodMk continuous_id))
  -- the pointwise bound of the shifted kernel
  have hbdd : ∀ v z : E3, |χ (z + v) * χ z * F (z + v, z)| ≤ Cχ * Cχ * C := by
    intro v z
    rw [abs_mul, abs_mul]
    by_cases h1 : z + v ∈ acube ℓ
    · by_cases h2 : z ∈ acube ℓ
      · exact mul_le_mul (mul_le_mul (hCχb _) (hCχb _) (abs_nonneg _) hCχ0)
          (hFb _ h1 _ h2) (abs_nonneg _) (mul_nonneg hCχ0 hCχ0)
      · rw [hχAc z h2]
        simp only [abs_zero, mul_zero, zero_mul]
        exact mul_nonneg (mul_nonneg hCχ0 hCχ0) hC0
    · rw [hχAc _ h1]
      simp only [abs_zero, mul_zero, zero_mul]
      exact mul_nonneg (mul_nonneg hCχ0 hCχ0) hC0
  -- the `A`-integral may be taken over all of `ℝ³`
  have hunres : ∀ v : E3, ((∫ z in A, χ (z + v) * χ z * F (z + v, z) : ℝ) : ℂ)
      = ∫ z, ((χ (z + v) * χ z * F (z + v, z) : ℝ) : ℂ) := by
    intro v
    have h1 : ((∫ z in A, χ (z + v) * χ z * F (z + v, z) : ℝ) : ℂ)
        = ∫ z in A, ((χ (z + v) * χ z * F (z + v, z) : ℝ) : ℂ) :=
      (integral_ofReal (μ := (volume : Measure E3).restrict A)
        (f := fun z : E3 => χ (z + v) * χ z * F (z + v, z))).symm
    rw [h1]
    exact setIntegral_eq_integral_of_forall_compl_eq_zero (fun z hz => by
      rw [hχsupp z hz]
      simp)
  -- STEP 1: the `(v,z)`-Fubini
  have hInt3 : Integrable (fun q : E3 × E3 => E q.1 *
      ((χ (q.2 + q.1) * χ q.2 * F (q.2 + q.1, q.2) : ℝ) : ℂ))
      (volume.prod volume) := by
    rw [← MeasureTheory.Measure.volume_eq_prod E3 E3]
    refine integrable_of_compact_bound_aux (C := Cχ * Cχ * C)
      (K := (Metric.closedBall (0 : E3) (2 * R)).prod (acube ℓ))
      ((isCompact_closedBall (0 : E3) (2 * R)).prod (acube_compact hℓ)) ?_ ?_ ?_
    · refine ((hEcont.measurable.comp measurable_fst).mul
        (Complex.continuous_ofReal.measurable.comp ?_)).aemeasurable.aestronglyMeasurable
      exact ((hχmeas.comp (measurable_snd.add measurable_fst)).mul
        (hχmeas.comp measurable_snd)).mul
        (hFm.comp (Measurable.prodMk (measurable_snd.add measurable_fst) measurable_snd))
    · intro q hq
      by_cases h2 : q.2 ∈ acube ℓ
      · have h1 : q.1 ∉ Metric.closedBall (0 : E3) (2 * R) := fun h1 => hq ⟨h1, h2⟩
        have hnorm : 2 * R < ‖q.1‖ := by
          rw [Metric.mem_closedBall, dist_eq_norm, sub_zero] at h1
          exact not_le.mp h1
        have hzero : χ (q.2 + q.1) = 0 := by
          by_contra hne
          have hyA : q.2 + q.1 ∈ A := by
            by_contra hh
            exact hne (hχsupp _ hh)
          have hsub : ‖q.1‖ ≤ 2 * R := by
            have h := norm_sub_le (q.2 + q.1) q.2
            have he : (q.2 + q.1) - q.2 = q.1 := by abel
            rw [he] at h
            have h1' := hR _ (hAc hyA)
            have h2' := hR _ h2
            linarith
          linarith
        rw [hzero]
        simp
      · have hz0 : χ q.2 = 0 := hχAc q.2 h2
        rw [hz0]
        simp
    · intro q hq
      have hq2 : q.2 ∈ acube ℓ := hq.2
      rw [norm_mul, hEnorm q.1, one_mul,
        show ((χ (q.2 + q.1) * χ q.2 * F (q.2 + q.1, q.2) : ℝ) : ℂ)
          = Complex.ofRealLI (χ (q.2 + q.1) * χ q.2 * F (q.2 + q.1, q.2)) from rfl,
        Complex.ofRealLI.norm_map, Real.norm_eq_abs, abs_mul, abs_mul]
      by_cases h3 : q.2 + q.1 ∈ acube ℓ
      · exact mul_le_mul (mul_le_mul (hCχb _) (hCχb _) (abs_nonneg _) hCχ0)
          (hFb _ h3 _ hq2) (abs_nonneg _) (mul_nonneg hCχ0 hCχ0)
      · rw [hχAc _ h3]
        simp only [abs_zero, mul_zero, zero_mul]
        exact mul_nonneg (mul_nonneg hCχ0 hCχ0) hC0
  have hstep1 : (∫ v, E v * (∫ z,
        ((χ (z + v) * χ z * F (z + v, z) : ℝ) : ℂ)))
      = ∫ z, ∫ v, E v *
          ((χ (z + v) * χ z * F (z + v, z) : ℝ) : ℂ) := by
    rw [show (∫ v, E v * (∫ z,
          ((χ (z + v) * χ z * F (z + v, z) : ℝ) : ℂ)))
        = ∫ v, ∫ z, E v *
            ((χ (z + v) * χ z * F (z + v, z) : ℝ) : ℂ) from
      integral_congr_ae (Eventually.of_forall fun v => by
        simp only []
        rw [MeasureTheory.integral_const_mul])]
    exact MeasureTheory.integral_integral_swap hInt3
  -- STEP 2: the per-`z` translation substitution
  have hstep2 : ∀ z : E3, (∫ v, E v *
        ((χ (z + v) * χ z * F (z + v, z) : ℝ) : ℂ))
      = ∫ y, Complex.exp (Complex.I * ((2 * Real.pi * inner ℝ u (y - z) : ℝ) : ℂ))
          * ((χ y * χ z * F (y, z) : ℝ) : ℂ) := by
    intro z
    rw [show (fun v : E3 => E v *
          ((χ (z + v) * χ z * F (z + v, z) : ℝ) : ℂ))
        = fun v : E3 => (fun y : E3 =>
            Complex.exp (Complex.I * ((2 * Real.pi * inner ℝ u (y - z) : ℝ) : ℂ))
            * ((χ y * χ z * F (y, z) : ℝ) : ℂ)) (v + z) from by
      funext v
      rw [hE]
      simp only []
      rw [add_sub_cancel_right, add_comm z v]]
    exact MeasureTheory.integral_add_right_eq_self
      (fun y : E3 => Complex.exp (Complex.I * ((2 * Real.pi * inner ℝ u (y - z) : ℝ) : ℂ))
        * ((χ y * χ z * F (y, z) : ℝ) : ℂ)) z
  -- STEP 3: the `(z,y)`-Fubini back
  have hInt4 : Integrable (fun q : E3 × E3 =>
      Complex.exp (Complex.I * ((2 * Real.pi * inner ℝ u (q.2 - q.1) : ℝ) : ℂ))
        * ((χ q.2 * χ q.1 * F (q.2, q.1) : ℝ) : ℂ))
      (volume.prod volume) := by
    rw [← MeasureTheory.Measure.volume_eq_prod E3 E3]
    refine integrable_of_compact_bound_aux (C := Cχ * Cχ * C)
      (K := (acube ℓ).prod (acube ℓ))
      ((acube_compact hℓ).prod (acube_compact hℓ)) ?_ ?_ ?_
    · have hph : Continuous (fun q : E3 × E3 =>
          Complex.exp (Complex.I * ((2 * Real.pi * inner ℝ u (q.2 - q.1) : ℝ) : ℂ))) := by
        refine Complex.continuous_exp.comp (continuous_const.mul
          (Complex.continuous_ofReal.comp ?_))
        exact continuous_const.mul
          (continuous_inner.comp (continuous_const.prodMk (continuous_snd.sub continuous_fst)))
      refine ((hph.measurable).mul
        (Complex.continuous_ofReal.measurable.comp ?_)).aemeasurable.aestronglyMeasurable
      exact ((hχmeas.comp measurable_snd).mul (hχmeas.comp measurable_fst)).mul
        (hFm.comp (Measurable.prodMk measurable_snd measurable_fst))
    · intro q hq
      by_cases h1 : q.1 ∈ acube ℓ
      · have h2 : q.2 ∉ acube ℓ := fun h2 => hq ⟨h1, h2⟩
        have hz0 : χ q.2 = 0 := hχAc q.2 h2
        rw [hz0]
        simp
      · have hz0 : χ q.1 = 0 := hχAc q.1 h1
        rw [hz0]
        simp
    · intro q hq
      have hq1 : q.1 ∈ acube ℓ := hq.1
      have hq2 : q.2 ∈ acube ℓ := hq.2
      rw [norm_mul, hnorm_exp (2 * Real.pi * inner ℝ u (q.2 - q.1)), one_mul,
        show ((χ q.2 * χ q.1 * F (q.2, q.1) : ℝ) : ℂ)
          = Complex.ofRealLI (χ q.2 * χ q.1 * F (q.2, q.1)) from rfl,
        Complex.ofRealLI.norm_map, Real.norm_eq_abs, abs_mul, abs_mul]
      exact mul_le_mul (mul_le_mul (hCχb _) (hCχb _) (abs_nonneg _) hCχ0)
        (hFb _ hq2 _ hq1) (abs_nonneg _) (mul_nonneg hCχ0 hCχ0)
  have hstep3 : (∫ z, ∫ y,
        Complex.exp (Complex.I * ((2 * Real.pi * inner ℝ u (y - z) : ℝ) : ℂ))
          * ((χ y * χ z * F (y, z) : ℝ) : ℂ))
      = ∫ y, ∫ z, Complex.exp (Complex.I * ((2 * Real.pi * inner ℝ u (y - z) : ℝ) : ℂ))
          * ((χ y * χ z * F (y, z) : ℝ) : ℂ) :=
    MeasureTheory.integral_integral_swap hInt4
  -- STEP 4: restrict both integrals to `A`
  have hstep4 : (∫ y, ∫ z, Complex.exp (Complex.I * ((2 * Real.pi * inner ℝ u (y - z) : ℝ) : ℂ))
        * ((χ y * χ z * F (y, z) : ℝ) : ℂ))
      = ∫ y in A, ∫ z in A,
          Complex.exp (Complex.I * ((2 * Real.pi * inner ℝ u (y - z) : ℝ) : ℂ))
          * ((χ y * χ z * F (y, z) : ℝ) : ℂ) := by
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := A)
      (f := fun y : E3 =>
        ∫ z, Complex.exp (Complex.I * ((2 * Real.pi * inner ℝ u (y - z) : ℝ) : ℂ))
          * ((χ y * χ z * F (y, z) : ℝ) : ℂ)) (by
      intro y hy
      have hy0 : χ y = 0 := hχsupp y hy
      have hzero : (fun z : E3 =>
          Complex.exp (Complex.I * ((2 * Real.pi * inner ℝ u (y - z) : ℝ) : ℂ))
            * ((χ y * χ z * F (y, z) : ℝ) : ℂ)) = fun _ => 0 := by
        funext z
        rw [hy0]
        simp
      rw [hzero, MeasureTheory.integral_zero])]
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    exact (setIntegral_eq_integral_of_forall_compl_eq_zero (s := A)
      (f := fun z : E3 =>
        Complex.exp (Complex.I * ((2 * Real.pi * inner ℝ u (y - z) : ℝ) : ℂ))
          * ((χ y * χ z * F (y, z) : ℝ) : ℂ)) (by
      intro z hz
      rw [hχsupp z hz]
      simp)).symm
  -- assembly of the per-pair identity
  rw [show (∫ v, Complex.exp (Complex.I * ((2 * Real.pi * inner ℝ u v : ℝ) : ℂ))
        * ((∫ z in A, χ (z + v) * χ z * F (z + v, z) : ℝ) : ℂ))
      = ∫ v, E v * ((∫ z in A, χ (z + v) * χ z * F (z + v, z) : ℝ) : ℂ) from by
    simp only [hE]]
  rw [show (∫ v, E v * ((∫ z in A, χ (z + v) * χ z * F (z + v, z) : ℝ) : ℂ))
      = ∫ v, E v * (∫ z,
          ((χ (z + v) * χ z * F (z + v, z) : ℝ) : ℂ)) from
    integral_congr_ae (Eventually.of_forall fun v => by simp only [hunres v])]
  rw [hstep1]
  rw [show (∫ z, ∫ v, E v *
        ((χ (z + v) * χ z * F (z + v, z) : ℝ) : ℂ))
      = ∫ z, ∫ y, Complex.exp (Complex.I * ((2 * Real.pi * inner ℝ u (y - z) : ℝ) : ℂ))
          * ((χ y * χ z * F (y, z) : ℝ) : ℂ) from
    integral_congr_ae (Eventually.of_forall fun z => hstep2 z)]
  rw [hstep3, hstep4]
  refine integral_congr_ae (Eventually.of_forall fun y => ?_)
  refine integral_congr_ae (Eventually.of_forall fun z => ?_)
  simp only []
  rw [show (inner ℝ ((2 * Real.pi : ℝ) • u) (y - z) : ℝ)
      = 2 * Real.pi * inner ℝ u (y - z) from
    real_inner_smul_left u (y - z) (2 * Real.pi)]
  push_cast
  ring

/-! ## Integrability of the Fourier-side integrand -/

/-- The Fourier-side integrand of the per-pair identity is integrable: the density vanishes
outside `closedBall 0 (2R)` and is bounded by `Cχ²·C·vol(A)` throughout. -/
theorem integrableFourierDensGen {ℓ : ℝ} {A : Set E3}
    (hℓ : 0 < ℓ) (hAc : A ⊆ acube ℓ)
    {χ : E3 → ℝ} (hχc : Continuous χ) (hχs : HasCompactSupport χ)
    (hχsupp : ∀ z, z ∉ A → χ z = 0)
    {F : E3 × E3 → ℝ} (hFm : Measurable F) {C R : ℝ} (hC0 : 0 ≤ C)
    (hFb : ∀ y ∈ acube ℓ, ∀ z ∈ acube ℓ, |F (y, z)| ≤ C)
    (hR : ∀ y ∈ acube ℓ, ‖y‖ ≤ R)
    (u : E3) :
    Integrable (fun v : E3 => Complex.exp (Complex.I * ((2 * Real.pi * inner ℝ u v : ℝ) : ℂ))
        * ((∫ z in A, χ (z + v) * χ z * F (z + v, z) : ℝ) : ℂ))
      (volume : Measure E3) := by
  have hχmeas : Measurable χ := hχc.measurable
  obtain ⟨Cχ, hCχ0, hCχb⟩ : ∃ C : ℝ, 0 ≤ C ∧ ∀ z, |χ z| ≤ C := by
    obtain ⟨C', hC'⟩ := hχc.bounded_above_of_compact_support hχs
    exact ⟨C', le_trans (norm_nonneg (χ 0)) (hC' 0),
      fun z => by simpa [Real.norm_eq_abs] using hC' z⟩
  have hχAc : ∀ z : E3, z ∉ acube ℓ → χ z = 0 := fun z hz =>
    hχsupp z (fun hmem => hz (hAc hmem))
  have hAfin : (volume : Measure E3) A < ∞ := Work.BoseFixB1S.volume_A_lt_top hℓ hAc
  -- measurability of the density
  have hdensm : Measurable (fun v : E3 => ∫ z in A, χ (z + v) * χ z * F (z + v, z)) := by
    have hjoint : StronglyMeasurable (Function.uncurry (fun (v : E3) (z : E3) =>
        χ (z + v) * χ z * F (z + v, z))) := by
      rw [show (Function.uncurry (fun (v : E3) (z : E3) =>
            χ (z + v) * χ z * F (z + v, z)))
          = fun q : E3 × E3 => χ (q.2 + q.1) * χ q.2 * F (q.2 + q.1, q.2) from rfl]
      exact (((hχmeas.comp (measurable_snd.add measurable_fst)).mul
        (hχmeas.comp measurable_snd)).mul
        (hFm.comp (Measurable.prodMk (measurable_snd.add measurable_fst)
          measurable_snd))).stronglyMeasurable
    exact (StronglyMeasurable.integral_prod_right (ν := (volume : Measure E3).restrict A)
      hjoint).measurable
  -- uniform bound on the density
  have hdens : ∀ v : E3,
      |∫ z in A, χ (z + v) * χ z * F (z + v, z)| ≤ Cχ * Cχ * C * (volume : Measure E3).real A := by
    intro v
    have h1 : ‖∫ z in A, χ (z + v) * χ z * F (z + v, z)‖
        ≤ (Cχ * Cχ * C) * (volume : Measure E3).real A :=
      norm_setIntegral_le_of_norm_le_const hAfin (fun z _ => by
        rw [Real.norm_eq_abs, abs_mul, abs_mul]
        by_cases h1 : z + v ∈ acube ℓ
        · by_cases h2 : z ∈ acube ℓ
          · exact mul_le_mul (mul_le_mul (hCχb _) (hCχb _) (abs_nonneg _) hCχ0)
              (hFb _ h1 _ h2) (abs_nonneg _) (mul_nonneg hCχ0 hCχ0)
          · rw [hχAc z h2]
            simp only [abs_zero, mul_zero, zero_mul]
            exact mul_nonneg (mul_nonneg hCχ0 hCχ0) hC0
        · rw [hχAc _ h1]
          simp only [abs_zero, mul_zero, zero_mul]
          exact mul_nonneg (mul_nonneg hCχ0 hCχ0) hC0)
    rwa [Real.norm_eq_abs] at h1
  have hexp : Continuous (fun v : E3 =>
      Complex.exp (Complex.I * ((2 * Real.pi * inner ℝ u v : ℝ) : ℂ))) := by
    refine Complex.continuous_exp.comp (continuous_const.mul (Complex.continuous_ofReal.comp ?_))
    exact continuous_const.mul (continuous_inner.comp (continuous_const.prodMk continuous_id))
  have hexpn : ∀ v : E3, ‖Complex.exp (Complex.I * ((2 * Real.pi * inner ℝ u v : ℝ) : ℂ))‖ = 1 :=
    fun v => by rw [mul_comm Complex.I, Complex.norm_exp_ofReal_mul_I]
  refine integrable_of_compact_bound_aux (C := Cχ * Cχ * C * (volume : Measure E3).real A)
    (K := Metric.closedBall (0 : E3) (2 * R))
    (f := fun v : E3 =>
      Complex.exp (Complex.I * ((2 * Real.pi * inner ℝ u v : ℝ) : ℂ))
        * ((∫ z in A, χ (z + v) * χ z * F (z + v, z) : ℝ) : ℂ))
    (isCompact_closedBall (0 : E3) (2 * R)) ?_ ?_ ?_
  · exact (hexp.measurable.mul
      (Complex.continuous_ofReal.measurable.comp hdensm)).aemeasurable.aestronglyMeasurable
  · intro v hv
    have hnorm : 2 * R < ‖v‖ := by
      rw [Metric.mem_closedBall, dist_eq_norm, sub_zero] at hv
      exact not_le.mp hv
    have hzero : (fun z : E3 => χ (z + v) * χ z * F (z + v, z)) = fun _ => 0 := by
      funext z
      by_cases hmem : z ∈ A
      · have hzv : z + v ∉ A := by
          intro hmem2
          have hsub : ‖v‖ ≤ 2 * R := by
            have h := norm_sub_le (z + v) z
            have he : (z + v) - z = v := by abel
            rw [he] at h
            have h1' := hR _ (hAc hmem2)
            have h2' := hR _ (hAc hmem)
            linarith
          linarith
        simp only [hχsupp (z + v) hzv, mul_zero, zero_mul]
      · simp only [hχsupp z hmem, mul_zero, zero_mul]
    have hint : (∫ z in A, χ (z + v) * χ z * F (z + v, z)) = 0 := by
      rw [hzero, MeasureTheory.integral_zero]
    rw [hint]
    simp
  · intro v _
    rw [norm_mul, hexpn v, one_mul,
      show ((∫ z in A, χ (z + v) * χ z * F (z + v, z) : ℝ) : ℂ)
        = Complex.ofRealLI (∫ z in A, χ (z + v) * χ z * F (z + v, z)) from rfl,
      Complex.ofRealLI.norm_map, Real.norm_eq_abs]
    exact hdens v

/-! ## The summed identity -/

theorem boxFourierDens_eqC2 {N : ℕ} {ℓ volA : ℝ} {A : Set (EuclideanSpace ℝ (Fin 3))}
    (hA : MeasurableSet A) (hℓ : 0 < ℓ) (hAc : A ⊆ Submission.BoseGases.acube ℓ)
    (hvolA : volA = (MeasureTheory.volume A).toReal) (hvolpos : 0 < volA)
    {χ : EuclideanSpace ℝ (Fin 3) → ℝ} (hχc : Continuous χ) (hχs : HasCompactSupport χ)
    (hχsupp : ∀ z, z ∉ A → χ z = 0)
    {Ψ : Submission.BoseGases.X (N + 2) → ℝ} (hΨ : Continuous Ψ) (u : EuclideanSpace ℝ (Fin 3)) :
    FourierTransform.fourier (fun v => ((Work.BoseFixB1.boxPairDensSum volA ℓ A χ Ψ v : ℝ) : ℂ))
        (-u)
      = Work.BoseFixB1.boxPairDensFourier volA ℓ A χ Ψ ((2 * Real.pi) • u) := by
  have hχmeas : Measurable χ := hχc.measurable
  obtain ⟨R, hR⟩ : ∃ R : ℝ, ∀ y ∈ acube ℓ, ‖y‖ ≤ R :=
    (acube_isBounded ℓ hℓ.le).exists_norm_le
  -- the per-pair identity
  have hpair : ∀ p ∈ Submission.BoseGases.pairSet (N + 2),
      (∫ v, Complex.exp (Complex.I * ((2 * Real.pi * inner ℝ u v : ℝ) : ℂ))
          * ((Work.BoseFixB1.boxPairDens volA ℓ A χ Ψ p.1 p.2 v : ℝ) : ℂ))
        = ∫ y in A, ∫ z in A, (χ y : ℂ) * (χ z : ℂ)
            * Complex.exp (Complex.I * ((inner ℝ ((2 * Real.pi : ℝ) • u) (y - z) : ℝ) : ℂ))
            * ((Work.BoseFixB1.boxPairFibreFun volA ℓ A Ψ p.1 p.2 y z : ℝ) : ℂ) := by
    intro p _
    obtain ⟨Cf, hCf0, hCfb⟩ := boxFibreBound_aux hA hℓ hAc hvolA hvolpos hΨ p.1 p.2
    simpa [Work.BoseFixB1.boxPairDens] using
      perPairFourierGen hA hℓ hAc hχc hχs hχsupp
        (measurable_boxPairFibreFun_uncurry hA hΨ.measurable p.1 p.2) hCf0 hCfb u
  -- each pair summand is integrable
  have hterm : ∀ p ∈ Submission.BoseGases.pairSet (N + 2),
      Integrable (fun v : E3 => Complex.exp (Complex.I * ((2 * Real.pi * inner ℝ u v : ℝ) : ℂ))
        * ((Work.BoseFixB1.boxPairDens volA ℓ A χ Ψ p.1 p.2 v : ℝ) : ℂ)) volume := by
    intro p _
    obtain ⟨Cf, hCf0, hCfb⟩ := boxFibreBound_aux hA hℓ hAc hvolA hvolpos hΨ p.1 p.2
    simpa [Work.BoseFixB1.boxPairDens] using
      integrableFourierDensGen hℓ hAc hχc hχs hχsupp
        (measurable_boxPairFibreFun_uncurry hA hΨ.measurable p.1 p.2) hCf0 hCfb hR u
  -- assembly
  rw [Real.fourier_eq']
  have hker : (fun v : E3 =>
      Complex.exp (↑(-2 * Real.pi * inner ℝ v (-u)) * Complex.I)
        • ((Work.BoseFixB1.boxPairDensSum volA ℓ A χ Ψ v : ℝ) : ℂ))
      = fun v => Complex.exp (Complex.I * ((2 * Real.pi * inner ℝ u v : ℝ) : ℂ))
          * ((Work.BoseFixB1.boxPairDensSum volA ℓ A χ Ψ v : ℝ) : ℂ) := by
    funext v
    simp only [smul_eq_mul]
    congr 1
    congr 1
    rw [show -2 * Real.pi * inner ℝ v (-u) = 2 * Real.pi * inner ℝ u v from by
      rw [inner_neg_right, real_inner_comm v u]; ring]
    ring
  rw [hker]
  have hsum : (fun v : E3 => Complex.exp (Complex.I * ((2 * Real.pi * inner ℝ u v : ℝ) : ℂ))
        * ((Work.BoseFixB1.boxPairDensSum volA ℓ A χ Ψ v : ℝ) : ℂ))
      = fun v => ∑ p ∈ Submission.BoseGases.pairSet (N + 2),
          Complex.exp (Complex.I * ((2 * Real.pi * inner ℝ u v : ℝ) : ℂ))
            * ((Work.BoseFixB1.boxPairDens volA ℓ A χ Ψ p.1 p.2 v : ℝ) : ℂ) := by
    funext v
    rw [Work.BoseFixB1.boxPairDensSum, Complex.ofReal_sum, Finset.mul_sum]
  rw [hsum, MeasureTheory.integral_finsetSum _
    (fun p hp => hterm p hp)]
  rw [Work.BoseFixB1.boxPairDensFourier]
  exact Finset.sum_congr rfl (fun p hp => hpair p hp)

end Work.BoseFixB1.BoxPairIntGenC2
