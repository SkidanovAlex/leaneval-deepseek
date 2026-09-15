import Mathlib
import Submission.Commons.Analysis.Fourier.hasFDerivAt_fourierLaplace_fin
import Submission.Commons.Analysis.Fourier.fourierInv_toLp_ae_eq_fourierInv
import Submission.Commons.Analysis.Fourier.integral_norm_sq_fourierInv_eq
import Submission.Commons.Analysis.Calculus.Multilinear.norm_le_sum_apply_basis
import Submission.Commons.Analysis.Complex.analyticAt_of_differentiableOn_closedBall
import Submission.Commons.Analysis.Fourier.LogvinenkoSereda.bandlimited_assembly_d3

namespace Commons.Analysis.Fourier

open MeasureTheory FourierTransform
open scoped ENNReal BigOperators

set_option autoImplicit false
set_option maxHeartbeats 100000000
set_option linter.unusedVariables false

variable {d : ℕ}

/-- The Fourier–Laplace transform of `g` at `z ∈ ℂ^d`. -/
private noncomputable def Lap (g : EuclideanSpace ℝ (Fin d) → ℂ) (z : Fin d → ℂ) : ℂ :=
  ∫ ξ : EuclideanSpace ℝ (Fin d),
    Complex.exp (2 * Real.pi * Complex.I * (∑ i, z i * (ξ i : ℂ))) * g ξ

/-- The linear multiplier `ξ ↦ 2πi ⟪v,ξ⟫`. -/
private noncomputable def mLin (v : Fin d → ℂ) (ξ : EuclideanSpace ℝ (Fin d)) : ℂ :=
  2 * Real.pi * Complex.I * (∑ i, v i * (ξ i : ℂ))

private lemma continuous_mLin (v : Fin d → ℂ) : Continuous (mLin v) := by
  rw [show mLin v = fun ξ : EuclideanSpace ℝ (Fin d) =>
      2 * Real.pi * Complex.I * (∑ i, v i * (ξ i : ℂ)) from rfl]
  fun_prop

private lemma norm_mLin_le {σ : ℝ} (hσ : 0 ≤ σ) (v : Fin d → ℂ) {ξ : EuclideanSpace ℝ (Fin d)}
    (hξ : ξ ∈ FourierLaplaceFinAux.fBox σ) :
    ‖mLin v ξ‖ ≤ 2 * Real.pi * σ * (∑ i, ‖v i‖) := by
  have h1 : ‖(∑ i, v i * (ξ i : ℂ))‖ ≤ σ * ∑ i, ‖v i‖ := by
    calc ‖∑ i, v i * (ξ i : ℂ)‖ ≤ ∑ i, ‖v i * (ξ i : ℂ)‖ := norm_sum_le _ _
      _ = ∑ i, ‖v i‖ * ‖(ξ i : ℂ)‖ := by simp [norm_mul]
      _ ≤ ∑ i, ‖v i‖ * σ := by
            apply Finset.sum_le_sum
            intro i _
            apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
            have hc : ‖(ξ i : ℂ)‖ = |ξ i| := by simp
            rw [hc]
            exact abs_le.mpr (hξ i)
      _ = σ * ∑ i, ‖v i‖ := by rw [← Finset.sum_mul, mul_comm]
  have h2 : ‖(2 * Real.pi * Complex.I : ℂ)‖ = 2 * Real.pi :=
    FourierLaplaceFinAux.norm_two_pi_I
  rw [mLin, norm_mul, h2]
  calc 2 * Real.pi * ‖∑ i, v i * (ξ i : ℂ)‖ ≤ 2 * Real.pi * (σ * ∑ i, ‖v i‖) :=
        mul_le_mul_of_nonneg_left h1 (by positivity)
    _ = 2 * Real.pi * σ * ∑ i, ‖v i‖ := by ring

private lemma integrable_mul_of_support {σ M : ℝ} (hM : 0 ≤ M)
    (g : EuclideanSpace ℝ (Fin d) → ℂ) (hg : Integrable g)
    (hsupp : ∀ᵐ ξ ∂(MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin d))),
      ξ ∉ FourierLaplaceFinAux.fBox σ → g ξ = 0)
    (w : EuclideanSpace ℝ (Fin d) → ℂ) (hwc : Continuous w)
    (hbdd : ∀ ξ, ξ ∈ FourierLaplaceFinAux.fBox σ → ‖w ξ‖ ≤ M) :
    Integrable (fun ξ => w ξ * g ξ) := by
  refine (hg.norm.const_mul M).mono' (hwc.aestronglyMeasurable.mul hg.aestronglyMeasurable) ?_
  filter_upwards [hsupp] with ξ hξ
  by_cases h : ξ ∈ FourierLaplaceFinAux.fBox σ
  · rw [norm_mul]
    exact mul_le_mul_of_nonneg_right (hbdd ξ h) (norm_nonneg _)
  · rw [hξ h, mul_zero]
    simp only [norm_zero]
    exact mul_nonneg hM le_rfl

private lemma integrable_mLin_mul {σ : ℝ} (hσ : 0 ≤ σ)
    (g : EuclideanSpace ℝ (Fin d) → ℂ) (hg : Integrable g)
    (hsupp : ∀ᵐ ξ ∂(MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin d))),
      ξ ∉ FourierLaplaceFinAux.fBox σ → g ξ = 0) (v : Fin d → ℂ) :
    Integrable (fun ξ => mLin v ξ * g ξ) :=
  integrable_mul_of_support (M := 2 * Real.pi * σ * ∑ i, ‖v i‖) (by positivity)
    g hg hsupp _ (continuous_mLin v) (fun ξ hξ => norm_mLin_le hσ v hξ)

private lemma fderiv_Lap_apply {σ : ℝ} (hσ : 0 ≤ σ)
    (g : EuclideanSpace ℝ (Fin d) → ℂ) (hg : Integrable g)
    (hsupp : ∀ᵐ ξ ∂(MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin d))),
      ξ ∉ FourierLaplaceFinAux.fBox σ → g ξ = 0) (z v : Fin d → ℂ) :
    fderiv ℂ (Lap g) z v = Lap (fun ξ => mLin v ξ * g ξ) z := by
  obtain ⟨L, hL, hderiv⟩ := hasFDerivAt_fourierLaplace_fin hσ hg hsupp z
  have hfd : fderiv ℂ (Lap g) z = L := hderiv.fderiv
  rw [hfd, hL v]
  simp only [Lap, mLin]
  refine integral_congr_ae (Filter.Eventually.of_forall (fun ξ => ?_))
  ring

private lemma differentiable_Lap {σ : ℝ} (hσ : 0 ≤ σ)
    (g : EuclideanSpace ℝ (Fin d) → ℂ) (hg : Integrable g)
    (hsupp : ∀ᵐ ξ ∂(MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin d))),
      ξ ∉ FourierLaplaceFinAux.fBox σ → g ξ = 0) :
    Differentiable ℂ (Lap g) := by
  intro z
  exact (hasFDerivAt_fourierLaplace_fin hσ hg hsupp z).choose_spec.2.differentiableAt


private lemma analyticOnNhd_Lap {σ : ℝ} (hσ : 0 ≤ σ)
    (g : EuclideanSpace ℝ (Fin d) → ℂ) (hg : Integrable g)
    (hsupp : ∀ᵐ ξ ∂(MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin d))),
      ξ ∉ FourierLaplaceFinAux.fBox σ → g ξ = 0) :
    AnalyticOnNhd ℂ (Lap g) Set.univ :=
  fun z _ => Commons.Analysis.Complex.analyticAt_of_differentiableOn_closedBall
    (R := 1) (by norm_num) (differentiable_Lap hσ g hg hsupp).differentiableOn

/-- The `m`-th complex Fréchet derivative of a Fourier–Laplace transform, applied to an
arbitrary tuple of directions. -/
private theorem iteratedFDeriv_Lap {σ : ℝ} (hσ : 0 ≤ σ)
    (g : EuclideanSpace ℝ (Fin d) → ℂ) (hg : Integrable g)
    (hsupp : ∀ᵐ ξ ∂(MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin d))),
      ξ ∉ FourierLaplaceFinAux.fBox σ → g ξ = 0) :
    ∀ (m : ℕ) (v : Fin m → (Fin d → ℂ)) (z : Fin d → ℂ),
      Integrable (fun ξ => (∏ j, mLin (v j) ξ) * g ξ) ∧
      iteratedFDeriv ℂ m (Lap g) z v = Lap (fun ξ => (∏ j, mLin (v j) ξ) * g ξ) z := by
  intro m
  induction m with
  | zero =>
      intro v z
      refine ⟨?_, ?_⟩
      · simpa using hg
      · rw [iteratedFDeriv_zero_apply]
        simp
  | succ m ih =>
      intro v z
      set vt : Fin m → (Fin d → ℂ) := Fin.tail v with hvt
      set g' : EuclideanSpace ℝ (Fin d) → ℂ :=
        fun ξ => (∏ j : Fin m, mLin (vt j) ξ) * g ξ with hg'def
      have hg'int : Integrable g' := (ih vt z).1
      have hg'supp : ∀ᵐ ξ ∂(MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin d))),
          ξ ∉ FourierLaplaceFinAux.fBox σ → g' ξ = 0 := by
        filter_upwards [hsupp] with ξ hξ hmem
        simp only [hg'def]
        rw [hξ hmem, mul_zero]
      refine ⟨?_, ?_⟩
      · have heq : (fun ξ => (∏ j : Fin (m+1), mLin (v j) ξ) * g ξ)
            = fun ξ => mLin (v 0) ξ * g' ξ := by
          funext ξ
          rw [Fin.prod_univ_succ]
          simp only [hg'def, hvt, Fin.tail]
          ring
        rw [heq]
        exact integrable_mLin_mul hσ g' hg'int hg'supp (v 0)
      · have hda : DifferentiableAt ℂ (iteratedFDeriv ℂ m (Lap g)) z :=
          ((analyticOnNhd_Lap hσ g hg hsupp).iteratedFDeriv m z (Set.mem_univ z)).differentiableAt
        rw [hda.iteratedFDeriv_succ_apply_left']
        have hfun : (fun y => iteratedFDeriv ℂ m (Lap g) y (Fin.tail v)) = Lap g' := by
          funext y
          rw [(ih vt y).2]
        rw [hfun, fderiv_Lap_apply hσ g' hg'int hg'supp z (v 0)]
        congr 1
        funext ξ
        rw [Fin.prod_univ_succ]
        simp only [hg'def, hvt, Fin.tail]
        ring


private lemma Lap_apply_real_eq_fourierInv (g : EuclideanSpace ℝ (Fin d) → ℂ)
    (x : EuclideanSpace ℝ (Fin d)) :
    Lap g (fun i => (x i : ℂ)) = FourierTransform.fourierInv g x := by
  rw [Lap, Real.fourierInv_eq']
  refine integral_congr_ae (Filter.Eventually.of_forall (fun ξ => ?_))
  simp only [PiLp.inner_apply, Real.inner_apply, smul_eq_mul]
  have harg : 2 * Real.pi * Complex.I * (∑ i, (x i : ℂ) * (ξ i : ℂ))
      = ((2 * Real.pi * ∑ i, ξ i * x i : ℝ) : ℂ) * Complex.I := by
    push_cast
    rw [Finset.sum_congr rfl (fun i _ => mul_comm ((x i : ℂ)) ((ξ i : ℂ)))]
    ring
  rw [harg]


/-- The product of the multipliers `2πi ⟪e_{I j}, ξ⟫ = 2πi ξ_{I j}`. -/
private noncomputable def wProd {m : ℕ} (I : Fin m → Fin d) (ξ : EuclideanSpace ℝ (Fin d)) : ℂ :=
  ∏ j, mLin (Pi.single (I j) (1 : ℂ)) ξ

private lemma mLin_single (i : Fin d) (ξ : EuclideanSpace ℝ (Fin d)) :
    mLin (Pi.single i (1 : ℂ)) ξ = 2 * Real.pi * Complex.I * (ξ i : ℂ) := by
  rw [mLin]
  congr 1
  rw [Finset.sum_eq_single i]
  · simp
  · intro b _ hb
    simp [Pi.single_eq_of_ne hb]
  · intro h; exact absurd (Finset.mem_univ i) h

private lemma norm_mLin_single (i : Fin d) (ξ : EuclideanSpace ℝ (Fin d)) :
    ‖mLin (Pi.single i (1 : ℂ)) ξ‖ = 2 * Real.pi * ‖(ξ i : ℂ)‖ := by
  rw [mLin_single, norm_mul, FourierLaplaceFinAux.norm_two_pi_I]

private lemma continuous_wProd {m : ℕ} (I : Fin m → Fin d) : Continuous (wProd I) := by
  unfold wProd
  apply continuous_finsetProd
  intro j _
  exact continuous_mLin _

private lemma norm_wProd_le {σ : ℝ} (hσ : 0 ≤ σ) {m : ℕ} (I : Fin m → Fin d)
    {ξ : EuclideanSpace ℝ (Fin d)} (hξ : ξ ∈ FourierLaplaceFinAux.fBox σ) :
    ‖wProd I ξ‖ ≤ (2 * Real.pi * σ) ^ m := by
  unfold wProd
  rw [norm_prod]
  calc ∏ j, ‖mLin (Pi.single (I j) (1 : ℂ)) ξ‖
      = ∏ j, 2 * Real.pi * ‖(ξ (I j) : ℂ)‖ := by
        apply Finset.prod_congr rfl; intro j _; rw [norm_mLin_single]
    _ ≤ ∏ _j : Fin m, 2 * Real.pi * σ := by
        apply Finset.prod_le_prod
        · intro j _; positivity
        · intro j _
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          have hc : ‖(ξ (I j) : ℂ)‖ = |ξ (I j)| := by simp
          rw [hc]
          exact abs_le.mpr (hξ (I j))
    _ = (2 * Real.pi * σ) ^ m := by
        rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]

private lemma memLp_mul_of_support {σ M : ℝ} (hM : 0 ≤ M) {p : ℝ≥0∞}
    {g : EuclideanSpace ℝ (Fin d) → ℂ} (hg : MemLp g p MeasureTheory.volume)
    (hsupp : ∀ᵐ ξ ∂MeasureTheory.volume, ξ ∉ FourierLaplaceFinAux.fBox σ → g ξ = 0)
    {w : EuclideanSpace ℝ (Fin d) → ℂ} (hwc : Continuous w)
    (hbdd : ∀ ξ, ξ ∈ FourierLaplaceFinAux.fBox σ → ‖w ξ‖ ≤ M) :
    MemLp (fun ξ => w ξ * g ξ) p MeasureTheory.volume := by
  refine (hg.norm.const_mul M).mono' (hwc.aestronglyMeasurable.mul hg.aestronglyMeasurable) ?_
  filter_upwards [hsupp] with ξ hξ
  by_cases h : ξ ∈ FourierLaplaceFinAux.fBox σ
  · rw [norm_mul]
    exact mul_le_mul_of_nonneg_right (hbdd ξ h) (norm_nonneg _)
  · rw [hξ h, mul_zero, norm_zero]
    exact mul_nonneg hM le_rfl

private lemma memLp_wProd_mul {σ : ℝ} (hσ : 0 ≤ σ) {m : ℕ} (I : Fin m → Fin d) {p : ℝ≥0∞}
    {h : EuclideanSpace ℝ (Fin d) → ℂ} (hh : MemLp h p MeasureTheory.volume)
    (hbox : ∀ᵐ ξ ∂MeasureTheory.volume, ξ ∉ FourierLaplaceFinAux.fBox σ → h ξ = 0) :
    MemLp (fun ξ => wProd I ξ * h ξ) p MeasureTheory.volume :=
  memLp_mul_of_support (σ := σ) (M := (2 * Real.pi * σ) ^ m) (w := wProd I) (by positivity)
    hh hbox (continuous_wProd I) (fun ξ hξ => norm_wProd_le hσ I hξ)


private lemma memLp_fourierInv {g : EuclideanSpace ℝ (Fin d) → ℂ}
    (hg1 : MemLp g 1 MeasureTheory.volume) (hg2 : MemLp g 2 MeasureTheory.volume) :
    MemLp (fun x => FourierTransform.fourierInv g x) 2 MeasureTheory.volume := by
  have h1 : MemLp ((FourierTransform.fourierInv (hg2.toLp g) :
      Lp ℂ 2 (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin d)))) :
        EuclideanSpace ℝ (Fin d) → ℂ) 2 MeasureTheory.volume := Lp.memLp _
  have hae := Commons.Analysis.Fourier.fourierInv_toLp_ae_eq_fourierInv hg1 hg2
  exact h1.ae_eq hae

private lemma integral_iteratedFDeriv_basis {σ : ℝ} (hσ : 0 ≤ σ)
    {h : EuclideanSpace ℝ (Fin d) → ℂ} (hm1 : MemLp h 1 MeasureTheory.volume)
    (hm2 : MemLp h 2 MeasureTheory.volume)
    (hbox : ∀ᵐ ξ ∂MeasureTheory.volume, ξ ∉ FourierLaplaceFinAux.fBox σ → h ξ = 0)
    {m : ℕ} (I : Fin m → Fin d) :
    (∫ x : EuclideanSpace ℝ (Fin d),
        ‖iteratedFDeriv ℂ m (Lap h) (fun i => (x i : ℂ))
          (fun j => Pi.single (I j) (1 : ℂ))‖ ^ 2)
      = ∫ ξ, ‖wProd I ξ * h ξ‖ ^ 2 := by
  have hgi1 : MemLp (fun ξ => wProd I ξ * h ξ) 1 MeasureTheory.volume :=
    memLp_wProd_mul hσ I hm1 hbox
  have hgi2 : MemLp (fun ξ => wProd I ξ * h ξ) 2 MeasureTheory.volume :=
    memLp_wProd_mul hσ I hm2 hbox
  have hpt : ∀ x : EuclideanSpace ℝ (Fin d),
      iteratedFDeriv ℂ m (Lap h) (fun i => (x i : ℂ)) (fun j => Pi.single (I j) (1 : ℂ))
        = FourierTransform.fourierInv (fun ξ => wProd I ξ * h ξ) x := by
    intro x
    rw [(iteratedFDeriv_Lap hσ h (MeasureTheory.memLp_one_iff_integrable.mp hm1) hbox m
          (fun j => Pi.single (I j) (1 : ℂ)) (fun i => (x i : ℂ))).2]
    simp only [wProd]
    exact Lap_apply_real_eq_fourierInv _ x
  have hfun : (fun x : EuclideanSpace ℝ (Fin d) =>
        ‖iteratedFDeriv ℂ m (Lap h) (fun i => (x i : ℂ)) (fun j => Pi.single (I j) (1 : ℂ))‖ ^ 2)
      = fun x => ‖FourierTransform.fourierInv (fun ξ => wProd I ξ * h ξ) x‖ ^ 2 := by
    funext x; rw [hpt x]
  rw [hfun]
  exact Commons.Analysis.Fourier.integral_norm_sq_fourierInv_eq hgi1 hgi2


private lemma norm_iteratedFDeriv_real_eq_complex {σ : ℝ} (hσ : 0 ≤ σ)
    {h : EuclideanSpace ℝ (Fin d) → ℂ} (hm1 : MemLp h 1 MeasureTheory.volume)
    (hbox : ∀ᵐ ξ ∂MeasureTheory.volume, ξ ∉ FourierLaplaceFinAux.fBox σ → h ξ = 0)
    (m : ℕ) (x : EuclideanSpace ℝ (Fin d)) :
    ‖iteratedFDeriv ℝ m (Lap h) (fun i => (x i : ℂ))‖
      = ‖iteratedFDeriv ℂ m (Lap h) (fun i => (x i : ℂ))‖ := by
  have hcA : ContDiffAt ℂ (m : ℕ∞) (Lap h) (fun i => (x i : ℂ)) :=
    ((analyticOnNhd_Lap hσ h (MeasureTheory.memLp_one_iff_integrable.mp hm1) hbox).contDiff
      (n := (m : ℕ∞))).contDiffAt
  have hh := hcA.restrictScalars_iteratedFDeriv (𝕜 := ℝ)
  rw [← hh]
  simp only [Function.comp_apply]
  rw [ContinuousMultilinearMap.norm_restrictScalars]

private lemma basis_value_eq_fourierInv {σ : ℝ} (hσ : 0 ≤ σ)
    {h : EuclideanSpace ℝ (Fin d) → ℂ} (hm1 : MemLp h 1 MeasureTheory.volume)
    (hbox : ∀ᵐ ξ ∂MeasureTheory.volume, ξ ∉ FourierLaplaceFinAux.fBox σ → h ξ = 0)
    (m : ℕ) (I : Fin m → Fin d) (x : EuclideanSpace ℝ (Fin d)) :
    iteratedFDeriv ℂ m (Lap h) (fun i => (x i : ℂ)) (fun j => Pi.single (I j) (1 : ℂ))
      = FourierTransform.fourierInv (fun ξ => wProd I ξ * h ξ) x := by
  rw [(iteratedFDeriv_Lap hσ h (MeasureTheory.memLp_one_iff_integrable.mp hm1) hbox m
        (fun j => Pi.single (I j) (1 : ℂ)) (fun i => (x i : ℂ))).2]
  simp only [wProd]
  exact Lap_apply_real_eq_fourierInv _ x

private lemma integrable_fourierInv_sq {σ : ℝ} (hσ : 0 ≤ σ)
    {h : EuclideanSpace ℝ (Fin d) → ℂ} (hm1 : MemLp h 1 MeasureTheory.volume)
    (hm2 : MemLp h 2 MeasureTheory.volume)
    (hbox : ∀ᵐ ξ ∂MeasureTheory.volume, ξ ∉ FourierLaplaceFinAux.fBox σ → h ξ = 0)
    (m : ℕ) (I : Fin m → Fin d) :
    Integrable (fun x => ‖FourierTransform.fourierInv (fun ξ => wProd I ξ * h ξ) x‖ ^ 2)
      MeasureTheory.volume := by
  have hgi1 : MemLp (fun ξ => wProd I ξ * h ξ) 1 MeasureTheory.volume := memLp_wProd_mul hσ I hm1 hbox
  have hgi2 : MemLp (fun ξ => wProd I ξ * h ξ) 2 MeasureTheory.volume := memLp_wProd_mul hσ I hm2 hbox
  have hmem := memLp_fourierInv hgi1 hgi2
  exact (MeasureTheory.memLp_two_iff_integrable_sq_norm hmem.aestronglyMeasurable).mp hmem

private lemma integral_fourierInv_sq_le {σ : ℝ} (hσ : 0 ≤ σ)
    {h : EuclideanSpace ℝ (Fin d) → ℂ} (hm1 : MemLp h 1 MeasureTheory.volume)
    (hm2 : MemLp h 2 MeasureTheory.volume)
    (hbox : ∀ᵐ ξ ∂MeasureTheory.volume, ξ ∉ FourierLaplaceFinAux.fBox σ → h ξ = 0)
    (m : ℕ) (I : Fin m → Fin d) :
    (∫ x, ‖FourierTransform.fourierInv (fun ξ => wProd I ξ * h ξ) x‖ ^ 2)
      ≤ (2 * Real.pi * σ) ^ (2 * m) * ∫ ξ, ‖h ξ‖ ^ 2 := by
  have hgi1 : MemLp (fun ξ => wProd I ξ * h ξ) 1 MeasureTheory.volume := memLp_wProd_mul hσ I hm1 hbox
  have hgi2 : MemLp (fun ξ => wProd I ξ * h ξ) 2 MeasureTheory.volume := memLp_wProd_mul hσ I hm2 hbox
  have hgIint : Integrable (fun ξ => ‖wProd I ξ * h ξ‖ ^ 2) MeasureTheory.volume :=
    (MeasureTheory.memLp_two_iff_integrable_sq_norm hgi2.aestronglyMeasurable).mp hgi2
  have hh2int : Integrable (fun ξ => ‖h ξ‖ ^ 2) MeasureTheory.volume :=
    (MeasureTheory.memLp_two_iff_integrable_sq_norm hm2.aestronglyMeasurable).mp hm2
  rw [Commons.Analysis.Fourier.integral_norm_sq_fourierInv_eq hgi1 hgi2]
  have hle : ∀ᵐ ξ ∂MeasureTheory.volume,
      ‖wProd I ξ * h ξ‖ ^ 2 ≤ (2 * Real.pi * σ) ^ (2 * m) * ‖h ξ‖ ^ 2 := by
    filter_upwards [hbox] with ξ hξ
    by_cases hmem : ξ ∈ FourierLaplaceFinAux.fBox σ
    · have hw : ‖wProd I ξ‖ ≤ (2 * Real.pi * σ) ^ m := norm_wProd_le hσ I hmem
      rw [norm_mul]
      calc (‖wProd I ξ‖ * ‖h ξ‖) ^ 2 = ‖wProd I ξ‖ ^ 2 * ‖h ξ‖ ^ 2 := by ring
        _ ≤ ((2 * Real.pi * σ) ^ m) ^ 2 * ‖h ξ‖ ^ 2 :=
              mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) hw 2) (by positivity)
        _ = (2 * Real.pi * σ) ^ (2 * m) * ‖h ξ‖ ^ 2 := by
              rw [← pow_mul, show m * 2 = 2 * m by ring]
    · rw [hξ hmem, mul_zero, norm_zero, zero_pow (by norm_num : (2:ℕ) ≠ 0)]
      positivity
  calc ∫ ξ, ‖wProd I ξ * h ξ‖ ^ 2
      ≤ ∫ ξ, (2 * Real.pi * σ) ^ (2 * m) * ‖h ξ‖ ^ 2 :=
        integral_mono_ae hgIint (hh2int.const_mul _) hle
    _ = (2 * Real.pi * σ) ^ (2 * m) * ∫ ξ, ‖h ξ‖ ^ 2 := integral_const_mul _ _

private lemma pointwise_iteratedFDeriv_le {σ : ℝ} (hσ : 0 ≤ σ)
    {h : EuclideanSpace ℝ (Fin d) → ℂ} (hm1 : MemLp h 1 MeasureTheory.volume)
    (hbox : ∀ᵐ ξ ∂MeasureTheory.volume, ξ ∉ FourierLaplaceFinAux.fBox σ → h ξ = 0)
    (m : ℕ) (x : EuclideanSpace ℝ (Fin d)) :
    ‖iteratedFDeriv ℝ m (Lap h) (fun i => (x i : ℂ))‖ ^ 2
      ≤ (Fintype.card (Fin m → Fin d) : ℝ) *
        ∑ I : Fin m → Fin d,
          ‖FourierTransform.fourierInv (fun ξ => wProd I ξ * h ξ) x‖ ^ 2 := by
  rw [norm_iteratedFDeriv_real_eq_complex hσ hm1 hbox m x]
  have hb := Commons.Analysis.Calculus.Multilinear.norm_le_sum_apply_basis m
    (iteratedFDeriv ℂ m (Lap h) (fun i => (x i : ℂ)))
  have hsq : ‖iteratedFDeriv ℂ m (Lap h) (fun i => (x i : ℂ))‖ ^ 2
      ≤ (∑ I : Fin m → Fin d,
          ‖iteratedFDeriv ℂ m (Lap h) (fun i => (x i : ℂ)) (fun j => Pi.single (I j) (1 : ℂ))‖) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) hb 2
  refine hsq.trans ?_
  have hsum : (∑ I : Fin m → Fin d,
          ‖iteratedFDeriv ℂ m (Lap h) (fun i => (x i : ℂ)) (fun j => Pi.single (I j) (1 : ℂ))‖)
      = ∑ I : Fin m → Fin d,
          ‖FourierTransform.fourierInv (fun ξ => wProd I ξ * h ξ) x‖ :=
    Finset.sum_congr rfl (fun I _ => by rw [basis_value_eq_fourierInv hσ hm1 hbox m I x])
  rw [hsum]
  exact sq_sum_le_card_mul_sum_sq

private lemma integrable_iteratedFDeriv_sq {σ : ℝ} (hσ : 0 ≤ σ)
    {h : EuclideanSpace ℝ (Fin d) → ℂ} (hm1 : MemLp h 1 MeasureTheory.volume)
    (hm2 : MemLp h 2 MeasureTheory.volume)
    (hbox : ∀ᵐ ξ ∂MeasureTheory.volume, ξ ∉ FourierLaplaceFinAux.fBox σ → h ξ = 0)
    (m : ℕ) :
    Integrable (fun x : EuclideanSpace ℝ (Fin d) =>
      ‖iteratedFDeriv ℝ m (Lap h) (fun i => (x i : ℂ))‖ ^ 2) MeasureTheory.volume := by
  have hRHSint : Integrable (fun x : EuclideanSpace ℝ (Fin d) =>
      (Fintype.card (Fin m → Fin d) : ℝ) *
        ∑ I : Fin m → Fin d,
          ‖FourierTransform.fourierInv (fun ξ => wProd I ξ * h ξ) x‖ ^ 2) MeasureTheory.volume := by
    refine Integrable.const_mul ?_ _
    exact integrable_finsetSum _ (fun I _ => integrable_fourierInv_sq hσ hm1 hm2 hbox m I)
  refine hRHSint.mono' ?_ ?_
  · apply Continuous.aestronglyMeasurable
    have h1 : Continuous (fun x : EuclideanSpace ℝ (Fin d) =>
        ‖iteratedFDeriv ℂ m (Lap h) (fun i => (x i : ℂ))‖ ^ 2) := by
      have hcont : Continuous (iteratedFDeriv ℂ m (Lap h)) :=
        (((analyticOnNhd_Lap hσ h (MeasureTheory.memLp_one_iff_integrable.mp hm1) hbox).iteratedFDeriv m).contDiff
          (n := (⊤ : ℕ∞))).continuous
      have h2 : Continuous (fun x : EuclideanSpace ℝ (Fin d) => (fun i => (x i : ℂ))) := by fun_prop
      exact ((continuous_norm.comp (hcont.comp h2))).pow 2
    have heq : (fun x : EuclideanSpace ℝ (Fin d) =>
          ‖iteratedFDeriv ℝ m (Lap h) (fun i => (x i : ℂ))‖ ^ 2)
        = fun x => ‖iteratedFDeriv ℂ m (Lap h) (fun i => (x i : ℂ))‖ ^ 2 := by
      funext x; rw [norm_iteratedFDeriv_real_eq_complex hσ hm1 hbox m x]
    rw [heq]; exact h1
  · filter_upwards [Filter.Eventually.of_forall (pointwise_iteratedFDeriv_le hσ hm1 hbox m)]
      with x hx
    rw [Real.norm_of_nonneg (by positivity)]
    exact hx

private theorem integral_iteratedFDeriv_Lap_le {σ : ℝ} (hσ : 0 ≤ σ)
    {h : EuclideanSpace ℝ (Fin d) → ℂ} (hm1 : MemLp h 1 MeasureTheory.volume)
    (hm2 : MemLp h 2 MeasureTheory.volume)
    (hbox : ∀ᵐ ξ ∂MeasureTheory.volume, ξ ∉ FourierLaplaceFinAux.fBox σ → h ξ = 0)
    (m : ℕ) :
    (∫ x : EuclideanSpace ℝ (Fin d),
        ‖iteratedFDeriv ℝ m (Lap h) (fun i => (x i : ℂ))‖ ^ 2)
      ≤ (2 * Real.pi * ((d : ℝ) + 1) * σ) ^ (2 * m) * ∫ ξ, ‖h ξ‖ ^ 2 := by
  have hDint := integrable_iteratedFDeriv_sq hσ hm1 hm2 hbox m
  have hBint : ∀ I : Fin m → Fin d,
      Integrable (fun x => ‖FourierTransform.fourierInv (fun ξ => wProd I ξ * h ξ) x‖ ^ 2)
        MeasureTheory.volume := fun I => integrable_fourierInv_sq hσ hm1 hm2 hbox m I
  have hBIle : ∀ I : Fin m → Fin d,
      (∫ x, ‖FourierTransform.fourierInv (fun ξ => wProd I ξ * h ξ) x‖ ^ 2)
        ≤ (2 * Real.pi * σ) ^ (2 * m) * ∫ ξ, ‖h ξ‖ ^ 2 :=
    fun I => integral_fourierInv_sq_le hσ hm1 hm2 hbox m I
  have hRHSint : Integrable (fun x : EuclideanSpace ℝ (Fin d) =>
      (Fintype.card (Fin m → Fin d) : ℝ) *
        ∑ I : Fin m → Fin d,
          ‖FourierTransform.fourierInv (fun ξ => wProd I ξ * h ξ) x‖ ^ 2) MeasureTheory.volume := by
    refine Integrable.const_mul ?_ _
    exact integrable_finsetSum _ (fun I _ => hBint I)
  have hkey : (Fintype.card (Fin m → Fin d) : ℝ) ^ 2 * (2 * Real.pi * σ) ^ (2 * m)
      ≤ (2 * Real.pi * ((d : ℝ) + 1) * σ) ^ (2 * m) := by
    have hcard : (Fintype.card (Fin m → Fin d) : ℝ) = (d : ℝ) ^ m := by
      rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_fin, Nat.cast_pow]
    have hc2 : (Fintype.card (Fin m → Fin d) : ℝ) ^ 2 ≤ ((d : ℝ) + 1) ^ (2 * m) := by
      rw [hcard, show ((d:ℝ) ^ m) ^ 2 = (d:ℝ) ^ (2 * m) by
        rw [← pow_mul, show m * 2 = 2 * m by ring]]
      exact pow_le_pow_left₀ (by positivity) (by linarith) _
    have heq : ((d : ℝ) + 1) ^ (2 * m) * (2 * Real.pi * σ) ^ (2 * m)
        = (2 * Real.pi * ((d : ℝ) + 1) * σ) ^ (2 * m) := by
      rw [← mul_pow]
      congr 1
      ring
    calc (Fintype.card (Fin m → Fin d) : ℝ) ^ 2 * (2 * Real.pi * σ) ^ (2 * m)
        ≤ ((d : ℝ) + 1) ^ (2 * m) * (2 * Real.pi * σ) ^ (2 * m) :=
          mul_le_mul_of_nonneg_right hc2 (by positivity)
      _ = (2 * Real.pi * ((d : ℝ) + 1) * σ) ^ (2 * m) := heq
  have hXnn : (0:ℝ) ≤ ∫ ξ, ‖h ξ‖ ^ 2 := integral_nonneg (fun ξ => by positivity)
  have step1 : (∫ x : EuclideanSpace ℝ (Fin d),
        ‖iteratedFDeriv ℝ m (Lap h) (fun i => (x i : ℂ))‖ ^ 2)
      ≤ ∫ x : EuclideanSpace ℝ (Fin d), (Fintype.card (Fin m → Fin d) : ℝ) *
          ∑ I : Fin m → Fin d,
            ‖FourierTransform.fourierInv (fun ξ => wProd I ξ * h ξ) x‖ ^ 2 :=
    integral_mono_ae hDint hRHSint
      (Filter.Eventually.of_forall (pointwise_iteratedFDeriv_le hσ hm1 hbox m))
  have step2 : (∫ x : EuclideanSpace ℝ (Fin d), (Fintype.card (Fin m → Fin d) : ℝ) *
          ∑ I : Fin m → Fin d,
            ‖FourierTransform.fourierInv (fun ξ => wProd I ξ * h ξ) x‖ ^ 2)
      = (Fintype.card (Fin m → Fin d) : ℝ) *
          ∑ I : Fin m → Fin d,
            ∫ x, ‖FourierTransform.fourierInv (fun ξ => wProd I ξ * h ξ) x‖ ^ 2 := by
    rw [integral_const_mul, integral_finsetSum _ (fun I _ => hBint I)]
  have step3 : (Fintype.card (Fin m → Fin d) : ℝ) *
          ∑ I : Fin m → Fin d,
            ∫ x, ‖FourierTransform.fourierInv (fun ξ => wProd I ξ * h ξ) x‖ ^ 2
      ≤ (Fintype.card (Fin m → Fin d) : ℝ) *
          ∑ _I : Fin m → Fin d, (2 * Real.pi * σ) ^ (2 * m) * ∫ ξ, ‖h ξ‖ ^ 2 :=
    mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun I _ => hBIle I)) (by positivity)
  have step4 : (Fintype.card (Fin m → Fin d) : ℝ) *
          ∑ _I : Fin m → Fin d, (2 * Real.pi * σ) ^ (2 * m) * ∫ ξ, ‖h ξ‖ ^ 2
      = (Fintype.card (Fin m → Fin d) : ℝ) *
          ((Fintype.card (Fin m → Fin d) : ℝ) * ((2 * Real.pi * σ) ^ (2 * m) * ∫ ξ, ‖h ξ‖ ^ 2)) := by
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have step5 : (Fintype.card (Fin m → Fin d) : ℝ) *
          ((Fintype.card (Fin m → Fin d) : ℝ) * ((2 * Real.pi * σ) ^ (2 * m) * ∫ ξ, ‖h ξ‖ ^ 2))
      ≤ (2 * Real.pi * ((d : ℝ) + 1) * σ) ^ (2 * m) * ∫ ξ, ‖h ξ‖ ^ 2 := by
    rw [show (Fintype.card (Fin m → Fin d) : ℝ) *
            ((Fintype.card (Fin m → Fin d) : ℝ) * ((2 * Real.pi * σ) ^ (2 * m) * ∫ ξ, ‖h ξ‖ ^ 2))
          = ((Fintype.card (Fin m → Fin d) : ℝ) ^ 2 * (2 * Real.pi * σ) ^ (2 * m)) * ∫ ξ, ‖h ξ‖ ^ 2 by ring]
    exact mul_le_mul_of_nonneg_right hkey hXnn
  exact le_trans (le_trans (le_trans (le_trans step1 (le_of_eq step2)) step3)
    (le_of_eq step4)) step5


private lemma lt_sum_abs_of_not_mem_fBox {σ : ℝ} {ξ : EuclideanSpace ℝ (Fin d)}
    (h : ξ ∉ FourierLaplaceFinAux.fBox σ) : σ < ∑ i, |ξ i| := by
  rw [FourierLaplaceFinAux.fBox, Set.mem_setOf_eq] at h
  push_neg at h
  obtain ⟨i, hi⟩ := h
  rw [Set.mem_Icc, not_and_or, not_le, not_le] at hi
  have hle : |ξ i| ≤ ∑ j, |ξ j| :=
    Finset.single_le_sum (fun j _ => abs_nonneg (ξ j)) (Finset.mem_univ i)
  rcases hi with hi | hi
  · exact lt_of_lt_of_le (lt_of_lt_of_le (by linarith : σ < -ξ i) (neg_le_abs (ξ i))) hle
  · exact lt_of_lt_of_le (lt_of_lt_of_le hi (le_abs_self (ξ i))) hle

private lemma volume_fBox_lt_top (d : ℕ) {σ : ℝ} :
    (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin d)))
      (FourierLaplaceFinAux.fBox (d := d) σ) < ⊤ := by
  have hsub : FourierLaplaceFinAux.fBox (d := d) σ ⊆ Metric.closedBall 0 (Real.sqrt (d * σ ^ 2)) := by
    intro ξ hξ
    rw [Metric.mem_closedBall, dist_zero_right, EuclideanSpace.norm_eq]
    apply Real.sqrt_le_sqrt
    calc ∑ i, ‖ξ i‖ ^ 2 ≤ ∑ _i : Fin d, σ ^ 2 := by
          apply Finset.sum_le_sum
          intro i _
          rw [Real.norm_eq_abs]
          exact pow_le_pow_left₀ (abs_nonneg (ξ i)) (abs_le.mpr (hξ i)) 2
        _ = d * σ ^ 2 := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  exact Metric.isBounded_closedBall.subset hsub |>.measure_lt_top

private theorem bandlimited_L2_entire_extension (d : ℕ) :
    ∃ A : ℝ, 0 < A ∧ ∀ (σ : ℝ) (hσ : 1 ≤ σ)
      (f : EuclideanSpace ℝ (Fin d) → ℂ)
      (hf : MeasureTheory.MemLp f 2
        (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin d))))
      (hsupp : ∀ᵐ ξ ∂(MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin d))),
        σ < ∑ i : Fin d, |ξ i| →
          ((FourierTransform.fourier (hf.toLp f) :
              Lp ℂ 2 (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin d)))) :
            EuclideanSpace ℝ (Fin d) → ℂ) ξ = 0),
      ∃ F : (Fin d → ℂ) → ℂ, Differentiable ℂ F ∧
        ((fun x : EuclideanSpace ℝ (Fin d) => F (fun i => (x i : ℂ))) =ᵐ[(MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin d)))] f) ∧
        (∀ m : ℕ, Integrable (fun x : EuclideanSpace ℝ (Fin d) =>
            ‖iteratedFDeriv ℝ m F (fun i => (x i : ℂ))‖ ^ 2)
              (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin d))) ∧
          (∫ x : EuclideanSpace ℝ (Fin d),
              ‖iteratedFDeriv ℝ m F (fun i => (x i : ℂ))‖ ^ 2) ≤
            (A * σ) ^ (2 * m) *
              (∫ x : EuclideanSpace ℝ (Fin d), ‖f x‖ ^ 2)) := by
  refine ⟨2 * Real.pi * ((d : ℝ) + 1), by positivity, ?_⟩
  intro σ hσ f hf hsupp
  classical
  have hσ0 : (0:ℝ) ≤ σ := le_trans zero_le_one hσ
  set h2 : Lp ℂ 2 (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin d))) :=
    FourierTransform.fourier (hf.toLp f) with h2def
  set h : EuclideanSpace ℝ (Fin d) → ℂ := ⇑h2 with hdef
  have hm2 : MemLp h 2 (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin d))) :=
    Lp.memLp h2
  have h2eq : hm2.toLp h = h2 := Lp.toLp_coeFn h2 hm2
  have hbox : ∀ᵐ ξ ∂(MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin d))),
      ξ ∉ FourierLaplaceFinAux.fBox σ → h ξ = 0 := by
    filter_upwards [hsupp] with ξ hξ hmem
    exact hξ (lt_sum_abs_of_not_mem_fBox hmem)
  -- exact-support version
  set h' : EuclideanSpace ℝ (Fin d) → ℂ := (FourierLaplaceFinAux.fBox σ).indicator h with h'def
  have hh'ae : h' =ᵐ[(MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin d)))] h := by
    filter_upwards [hbox] with ξ hξ
    by_cases hm : ξ ∈ FourierLaplaceFinAux.fBox σ
    · rw [h'def, Set.indicator_of_mem hm]
    · rw [h'def, Set.indicator_of_notMem hm]; exact (hξ hm).symm
  have hm2' : MemLp h' 2 (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin d))) :=
    hm2.ae_eq hh'ae.symm
  have hm1' : MemLp h' 1 (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin d))) :=
    hm2'.mono_exponent_of_measure_support_ne_top
      (s := FourierLaplaceFinAux.fBox σ)
      (fun x hx => by rw [h'def, Set.indicator_of_notMem hx])
      (ne_of_lt (volume_fBox_lt_top d (σ := σ))) (by norm_num)
  have hbox' : ∀ᵐ ξ ∂(MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin d))),
      ξ ∉ FourierLaplaceFinAux.fBox σ → h' ξ = 0 :=
    Filter.Eventually.of_forall (fun ξ hξ => by rw [h'def, Set.indicator_of_notMem hξ])
  have hLap : Lap h' = Lap h := by
    funext z
    apply integral_congr_ae
    filter_upwards [hh'ae] with ξ hξ
    simp only [hξ]
  have hLap' : ∀ x : EuclideanSpace ℝ (Fin d), Lap h' (fun i => (x i : ℂ))
      = FourierTransform.fourierInv h x := by
    intro x
    rw [Lap_apply_real_eq_fourierInv, Real.fourierInv_congr_ae hh'ae]
  -- Fourier inversion: f =ᵐ fourierInv h
  have hfinv : f =ᵐ[(MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin d)))]
      (fun x => FourierTransform.fourierInv h x) := by
    have hm1 : MemLp h 1 (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin d))) :=
      hm1'.ae_eq hh'ae
    have hA : ((FourierTransform.fourierInv h2 :
        Lp ℂ 2 (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin d)))) :
          EuclideanSpace ℝ (Fin d) → ℂ) =ᵐ[(MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin d)))]
        (fun x => FourierTransform.fourierInv h x) := by
      simpa only [h2eq] using Commons.Analysis.Fourier.fourierInv_toLp_ae_eq_fourierInv hm1 hm2
    have hB : ((FourierTransform.fourierInv h2 :
        Lp ℂ 2 (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin d)))) :
          EuclideanSpace ℝ (Fin d) → ℂ) =ᵐ[(MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin d)))]
            (hf.toLp f : EuclideanSpace ℝ (Fin d) → ℂ) := by
      have hinv : (FourierTransform.fourierInv h2 :
          Lp ℂ 2 (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin d))))
          = hf.toLp f := by
        rw [h2def, FourierTransform.fourierInv_fourier_eq]
      rw [hinv]
    exact (hf.coeFn_toLp.symm.trans hB.symm).trans hA
  refine ⟨Lap h', differentiable_Lap hσ0 h' (MeasureTheory.memLp_one_iff_integrable.mp hm1')
      hbox', ?_, ?_⟩
  · filter_upwards [hfinv] with x hx
    rw [hLap' x, hx]
  · intro m
    refine ⟨?_, ?_⟩
    · have := integrable_iteratedFDeriv_sq (σ := σ) hσ0 hm1' hm2' hbox' m
      simpa using this
    · have h1 := integral_iteratedFDeriv_Lap_le (σ := σ) hσ0 hm1' hm2' hbox' m
      have h2 : (∫ ξ : EuclideanSpace ℝ (Fin d), ‖h' ξ‖ ^ 2)
          = ∫ x : EuclideanSpace ℝ (Fin d), ‖f x‖ ^ 2 := by
        have e1 : (∫ ξ : EuclideanSpace ℝ (Fin d), ‖h' ξ‖ ^ 2)
            = ∫ ξ : EuclideanSpace ℝ (Fin d), ‖h ξ‖ ^ 2 := by
          apply integral_congr_ae
          filter_upwards [hh'ae] with ξ hξ
          simp only [hξ]
        have e2 : (∫ ξ : EuclideanSpace ℝ (Fin d), ‖h ξ‖ ^ 2) = ‖h2‖ ^ 2 :=
          Commons.Analysis.Fourier.lp_integral_norm_sq h2
        have e3 : ‖h2‖ = ‖hf.toLp f‖ := (Lp.fourierTransformₗᵢ _ ℂ).norm_map (hf.toLp f)
        have e4 : ‖hf.toLp f‖ ^ 2 = ∫ x : EuclideanSpace ℝ (Fin d), ‖f x‖ ^ 2 := by
          rw [← Commons.Analysis.Fourier.lp_integral_norm_sq (hf.toLp f)]
          apply integral_congr_ae
          filter_upwards [hf.coeFn_toLp] with x hx
          simp only [hx]
        rw [e1, e2, e3, e4]
      rw [h2] at h1
      exact h1


theorem localization_l2 (d : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (σ lam : ℝ) (hσ : 1 ≤ σ) (hlam : 0 < lam) (hlam1 : lam ≤ 1)
      (γ : EuclideanSpace ℝ (Fin d)) (E : Set (EuclideanSpace ℝ (Fin d))) (hE : MeasurableSet E)
      (hEm : ∀ n : Fin d → ℤ, lam * 2 ^ d ≤
        ((MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin d)))
          (E ∩ {x : EuclideanSpace ℝ (Fin d) | ∀ i : Fin d,
          2 * (n i : ℝ) + γ i ≤ x i ∧ x i ≤ 2 * (n i : ℝ) + γ i + 2})).toReal)
      (f : EuclideanSpace ℝ (Fin d) → ℂ)
      (hf : MeasureTheory.MemLp f 2 (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin d))))
      (hsupp : ∀ᵐ ξ ∂(MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin d))),
        σ < ∑ i : Fin d, |ξ i| →
          ((FourierTransform.fourier (hf.toLp f) : MeasureTheory.Lp ℂ 2 (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin d)))) :
            EuclideanSpace ℝ (Fin d) → ℂ) ξ = 0),
      MeasureTheory.integral MeasureTheory.volume (fun x : EuclideanSpace ℝ (Fin d) => ‖f x‖ ^ 2)
        ≤ (C / lam) ^ (C * σ)
          * MeasureTheory.integral (MeasureTheory.volume.restrict E)
              (fun x : EuclideanSpace ℝ (Fin d) => ‖f x‖ ^ 2) := by
  obtain ⟨A, hApos, hext⟩ := bandlimited_L2_entire_extension d
  obtain ⟨C, hCpos, hasm⟩ := LogvinenkoSereda.bandlimited_assembly_d3 d
  set C' : ℝ := max C 1 with hC'def
  have hC'1 : 1 ≤ C' := le_max_right _ _
  set K : ℝ := max (A / (2 * Real.pi)) 1 with hKdef
  have hK1 : 1 ≤ K := le_max_right _ _
  obtain ⟨C₀, hC₀1, habs⟩ :=
    LogvinenkoSereda.d2_absorb (A := 1) (V := C') (S := C' * K) (k := 0)
      le_rfl hC'1 (by positivity) le_rfl
  refine ⟨C₀, lt_of_lt_of_le zero_lt_one hC₀1, ?_⟩
  intro σ lam hσ hlam hlam1 γ E hE hEm f hf hsupp
  set σ' : ℝ := max 1 (A * σ / (2 * Real.pi)) with hσ'def
  have hσ'1 : 1 ≤ σ' := le_max_left _ _
  have hσ'le : σ' ≤ K * σ := by
    rw [hσ'def, hKdef]
    apply max_le
    · calc (1 : ℝ) = 1 * 1 := by ring
        _ ≤ max (A / (2 * Real.pi)) 1 * σ :=
              mul_le_mul (le_max_right _ _) hσ zero_le_one (le_trans zero_le_one (le_max_right _ _))
    · have h : A * σ / (2 * Real.pi) = (A / (2 * Real.pi)) * σ := by ring
      rw [h]
      exact mul_le_mul_of_nonneg_right (le_max_left _ _) (le_trans zero_le_one hσ)
  obtain ⟨F, hFdiff, hFeq, hFbd⟩ := hext σ hσ f hf hsupp
  have hFint : (∫ x : EuclideanSpace ℝ (Fin d), ‖F (fun i => (x i : ℂ))‖ ^ 2)
      = ∫ x : EuclideanSpace ℝ (Fin d), ‖f x‖ ^ 2 := by
    apply integral_congr_ae
    filter_upwards [hFeq] with x hx
    rw [hx]
  have hL2 : ∀ m : ℕ,
      Integrable (fun x : EuclideanSpace ℝ (Fin d) => ‖iteratedFDeriv ℝ m F (fun i => (x i : ℂ))‖ ^ 2) ∧
      (∫ x : EuclideanSpace ℝ (Fin d), ‖iteratedFDeriv ℝ m F (fun i => (x i : ℂ))‖ ^ 2) ≤
        (2 * Real.pi * σ') ^ (2 * m) * (∫ x : EuclideanSpace ℝ (Fin d), ‖F (fun i => (x i : ℂ))‖ ^ 2) := by
    intro m
    obtain ⟨hint, hbd⟩ := hFbd m
    refine ⟨hint, ?_⟩
    have hbase : A * σ ≤ 2 * Real.pi * σ' := by
      rw [hσ'def]
      have h2π : (0:ℝ) < 2 * Real.pi := by positivity
      by_cases hcase : 1 ≤ A * σ / (2 * Real.pi)
      · rw [max_eq_right hcase]
        rw [show 2 * Real.pi * (A * σ / (2 * Real.pi)) = A * σ by
          rw [mul_div_assoc', mul_div_cancel_left₀ (A * σ) h2π.ne']]
      · push_neg at hcase
        rw [max_eq_left (le_of_lt hcase), mul_one]
        exact le_of_lt ((div_lt_one h2π).mp hcase)
    have h1 : (A * σ) ^ (2 * m) ≤ (2 * Real.pi * σ') ^ (2 * m) :=
      pow_le_pow_left₀ (by positivity) hbase (2 * m)
    calc (∫ x : EuclideanSpace ℝ (Fin d), ‖iteratedFDeriv ℝ m F (fun i => (x i : ℂ))‖ ^ 2)
        ≤ (A * σ) ^ (2 * m) * (∫ x : EuclideanSpace ℝ (Fin d), ‖f x‖ ^ 2) := hbd
      _ ≤ (2 * Real.pi * σ') ^ (2 * m) * (∫ x : EuclideanSpace ℝ (Fin d), ‖f x‖ ^ 2) :=
            mul_le_mul_of_nonneg_right h1 (integral_nonneg (fun x => by positivity))
      _ = (2 * Real.pi * σ') ^ (2 * m) * (∫ x : EuclideanSpace ℝ (Fin d), ‖F (fun i => (x i : ℂ))‖ ^ 2) := by
            rw [← hFint]
  have hkey := hasm σ' lam hσ'1 hlam hlam1 γ F hFdiff hL2 E hE hEm
  have hFeqE : (fun x : EuclideanSpace ℝ (Fin d) => F (fun i => (x i : ℂ)))
      =ᵐ[MeasureTheory.volume.restrict E] f :=
    MeasureTheory.ae_restrict_of_ae hFeq
  have hFintE : (∫ x in E, ‖F (fun i => (x i : ℂ))‖ ^ 2)
      = ∫ x in E, ‖f x‖ ^ 2 := by
    apply integral_congr_ae
    filter_upwards [hFeqE] with x hx
    rw [hx]
  have hbase1 : (1:ℝ) ≤ C' / lam :=
    (one_le_div hlam).mpr (le_trans hlam1 hC'1)
  have hC'pos : (0:ℝ) < C' := lt_of_lt_of_le zero_lt_one hC'1
  have hstep1 : (C / lam) ^ (C * σ') ≤ (C' / lam) ^ (C' * σ') := by
    have hBB' : C / lam ≤ C' / lam :=
      div_le_div_of_nonneg_right (le_max_left C 1) hlam.le
    calc (C / lam) ^ (C * σ') ≤ (C' / lam) ^ (C * σ') :=
          Real.rpow_le_rpow (by positivity) hBB' (by positivity)
      _ ≤ (C' / lam) ^ (C' * σ') :=
          Real.rpow_le_rpow_of_exponent_le hbase1
            (by nlinarith [le_max_left C 1, hC'1, le_max_left (1:ℝ) σ', hσ'1])
  have hstep2 : (C' / lam) ^ (C' * σ') ≤ (C' / lam) ^ (C' * K * σ) := by
    apply Real.rpow_le_rpow_of_exponent_le hbase1
    have : C' * σ' ≤ C' * (K * σ) := mul_le_mul_of_nonneg_left hσ'le hC'pos.le
    linarith [this]
  calc (MeasureTheory.integral MeasureTheory.volume (fun x : EuclideanSpace ℝ (Fin d) => ‖f x‖ ^ 2))
      = (MeasureTheory.integral MeasureTheory.volume (fun x : EuclideanSpace ℝ (Fin d) => ‖F (fun i => (x i : ℂ))‖ ^ 2)) := hFint.symm
    _ ≤ (C / lam) ^ (C * σ') * (∫ x in E, ‖F (fun i => (x i : ℂ))‖ ^ 2) := hkey
    _ = (C / lam) ^ (C * σ') * (∫ x in E, ‖f x‖ ^ 2) := by rw [hFintE]
    _ ≤ (C' / lam) ^ (C' * σ') * (∫ x in E, ‖f x‖ ^ 2) :=
          mul_le_mul_of_nonneg_right hstep1 (integral_nonneg (fun x => by positivity))
    _ ≤ (C' / lam) ^ (C' * K * σ) * (∫ x in E, ‖f x‖ ^ 2) :=
          mul_le_mul_of_nonneg_right hstep2 (integral_nonneg (fun x => by positivity))
    _ ≤ (C₀ / lam) ^ (C₀ * σ) * (∫ x in E, ‖f x‖ ^ 2) := by
          apply mul_le_mul_of_nonneg_right _ (integral_nonneg (fun x => by positivity))
          have h := habs lam σ hlam hlam1 hσ
          simpa [one_mul, mul_assoc, add_zero] using h

end Commons.Analysis.Fourier
