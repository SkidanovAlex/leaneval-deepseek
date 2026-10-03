import Mathlib
import Submission.Work.A7.varphiN_integrable_measurable
import Submission.Work.KMTPlan.A6.EeModulation
import Submission.Work.KMTAreas.A7.lacBumpDecimation
import Submission.Work.KMTAreas.A7.lacBumpSeed
import Submission.Work.KMTAreas.A7.lacBumpKernel
import Submission.Work.KMTAreas.A7.lacBumpPsiFacts

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace Work.KMTAreas.A7

open MeasureTheory
open scoped ENNReal NNReal BigOperators FourierTransform

/-! ## Fourier rules -/

/-- The complex character `v ↦ exp (2πi (v * x))` appearing in the inverse Fourier transform. -/
noncomputable def lacBump_charFun (x : ℝ) : ℝ → ℂ :=
  fun v => Complex.exp (↑(2 * Real.pi * (v * x)) * Complex.I)

/-- The character `lacBump_charFun x` is a.e. strongly measurable. -/
lemma lacBump_charFun_aestronglyMeasurable (x : ℝ) :
    AEStronglyMeasurable (lacBump_charFun x) (volume : Measure ℝ) := by
  show AEStronglyMeasurable
    (fun v : ℝ => Complex.exp (↑(2 * Real.pi * (v * x)) * Complex.I)) volume
  exact (Complex.continuous_exp.comp (by fun_prop)).aestronglyMeasurable

/-- The character `lacBump_charFun x` is unimodular. -/
lemma lacBump_norm_charFun (x v : ℝ) : ‖lacBump_charFun x v‖ = 1 := by
  show ‖Complex.exp (↑(2 * Real.pi * (v * x)) * Complex.I)‖ = 1
  rw [Complex.norm_exp]
  simp

/-- The inverse Fourier transform as an integral against `lacBump_charFun`. -/
lemma lacBump_fourierInv_eq_integral_mul (g : ℝ → ℂ) (x : ℝ) :
    FourierTransformInv.fourierInv g x = ∫ v : ℝ, lacBump_charFun x v * g v := by
  rw [show FourierTransformInv.fourierInv g x
      = ∫ v : ℝ, Complex.exp (↑(2 * Real.pi * inner ℝ v x) * Complex.I) • g v from
    Real.fourierInv_eq' g x]
  refine integral_congr_ae (Filter.Eventually.of_forall (fun v => ?_))
  simp only [lacBump_charFun, Real.inner_apply, smul_eq_mul]

/-- Linearity of `𝓕⁻` over a finite sum of integrable functions. -/
lemma lacBump_fourierInv_finsetSum {ι : Type*} (s : Finset ι) {g : ι → ℝ → ℂ}
    (hg : ∀ i ∈ s, Integrable (g i) (volume : Measure ℝ)) (x : ℝ) :
    FourierTransformInv.fourierInv (fun ξ => ∑ i ∈ s, g i ξ) x
      = ∑ i ∈ s, FourierTransformInv.fourierInv (g i) x := by
  have h1 : FourierTransformInv.fourierInv (fun ξ => ∑ i ∈ s, g i ξ) x
      = ∫ v : ℝ, ∑ i ∈ s, lacBump_charFun x v * g i v := by
    rw [lacBump_fourierInv_eq_integral_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall (fun v => ?_))
    simp only [Finset.mul_sum]
  have h2 : (∫ v : ℝ, ∑ i ∈ s, lacBump_charFun x v * g i v)
      = ∑ i ∈ s, ∫ v : ℝ, lacBump_charFun x v * g i v :=
    integral_finsetSum s (fun i hi => Integrable.bdd_mul (hg i hi)
      (lacBump_charFun_aestronglyMeasurable x)
      (Filter.Eventually.of_forall (fun v => le_of_eq (lacBump_norm_charFun x v))))
  have h3 : ∀ i ∈ s, (∫ v : ℝ, lacBump_charFun x v * g i v)
      = FourierTransformInv.fourierInv (g i) x := by
    intro i hi
    rw [lacBump_fourierInv_eq_integral_mul]
  rw [h1, h2, Finset.sum_congr rfl h3]

/-- Scalar linearity of `𝓕⁻`. -/
lemma lacBump_fourierInv_const_mul (c : ℂ) (g : ℝ → ℂ) (x : ℝ) :
    FourierTransformInv.fourierInv (fun ξ => c * g ξ) x
      = c * FourierTransformInv.fourierInv g x := by
  rw [lacBump_fourierInv_eq_integral_mul, lacBump_fourierInv_eq_integral_mul]
  have hpt : (fun v : ℝ => lacBump_charFun x v * (c * g v))
      = fun v : ℝ => c * (lacBump_charFun x v * g v) := by
    funext v; ring
  rw [hpt, MeasureTheory.integral_const_mul]

/-! ## Integrability of the bumps -/

/-- The modulated bump `varphiNt N k₁ t = φ_N · ee (N t ·)` is integrable. -/
lemma lacBump_integrable_varphiNt (N k₁ : ℕ) (t : ℝ) :
    Integrable (varphiNt N k₁ t) (volume : Measure ℝ) := by
  have h2 : AEStronglyMeasurable (fun ξ : ℝ => ee ((N : ℝ) * t * ξ)) volume :=
    (Work.KMTPlan.A6.continuous_ee.comp (by fun_prop)).aestronglyMeasurable
  have h3 : ∀ᵐ ξ : ℝ ∂(volume : Measure ℝ), ‖ee ((N : ℝ) * t * ξ)‖ ≤ 1 :=
    Filter.Eventually.of_forall (fun ξ => le_of_eq (Work.KMTPlan.A6.norm_ee _))
  show Integrable (fun ξ : ℝ => varphiN N k₁ ξ * ee ((N : ℝ) * t * ξ)) (volume : Measure ℝ)
  exact Integrable.mul_bdd (Work.A7.varphiN_integrable_measurable N k₁).1 h2 h3

/-- A scalar multiple of the modulated bump is integrable. -/
lemma lacBump_integrable_smul_varphiNt (N k₁ : ℕ) (t : ℝ) (c : ℂ) :
    Integrable (fun ξ : ℝ => c * varphiNt N k₁ t ξ) (volume : Measure ℝ) := by
  have h := (lacBump_integrable_varphiNt N k₁ t).const_mul c
  simpa only [smul_eq_mul] using h

/-! ## The operator identity -/

/-- **The multiplier is the convolution with the inverse Fourier transform of its symbol.** -/
lemma lacBump_contMulOp_eq_integral (m f : ℝ → ℂ) (hm : Integrable m (volume : Measure ℝ))
    (hf : Integrable f (volume : Measure ℝ)) (x : ℝ) :
    Work.Analysis.IWMultiplier.contMulOp m f x
      = ∫ y : ℝ, f y * FourierTransformInv.fourierInv m (x - y) := by
  rw [Work.Analysis.IWMultiplier.contMulOp]
  exact Commons.Analysis.Fourier.fourierInv_mul_fourier_eq_convolution hm hf x

/-- The multiplier with an `L¹`-symbol is continuous (hence a.e. strongly measurable). -/
lemma lacBump_contMulOp_continuous {φ f : ℝ → ℂ}
    (hg : Integrable (fun ξ : ℝ => φ ξ * 𝓕 f ξ) (volume : Measure ℝ)) :
    Continuous (Work.Analysis.IWMultiplier.contMulOp φ f) := by
  rw [Work.Analysis.IWMultiplier.contMulOp, Real.fourierInv_eq_fourier_comp_neg]
  exact VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
    (innerSL ℝ).continuous₂ hg.comp_neg

/-- Linearity of the continuous multiplier in its symbol, for a finite sum of symbols. -/
lemma lacBump_contMulOp_finsetSum {ι : Type*} (s : Finset ι) (φ : ι → ℝ → ℂ)
    (f : SchwartzMap ℝ ℂ) (hφ : ∀ i ∈ s, Integrable (φ i) (volume : Measure ℝ)) :
    Work.Analysis.IWMultiplier.contMulOp (fun ξ => ∑ i ∈ s, φ i ξ) (f : ℝ → ℂ)
      = ∑ i ∈ s, Work.Analysis.IWMultiplier.contMulOp (φ i) (f : ℝ → ℂ) := by
  have hpt : (fun ξ : ℝ => (∑ i ∈ s, φ i ξ) * 𝓕 (f : ℝ → ℂ) ξ)
      = fun ξ : ℝ => ∑ i ∈ s, φ i ξ * 𝓕 (f : ℝ → ℂ) ξ := by
    funext ξ; rw [Finset.sum_mul]
  have hFtop : MemLp (fun ξ : ℝ => 𝓕 (f : ℝ → ℂ) ξ) ⊤ (volume : Measure ℝ) := by
    simpa only [SchwartzMap.fourier_coe] using
      (SchwartzMap.memLp (𝓕 f) ⊤ (volume : Measure ℝ))
  have hlin : ∀ x : ℝ, FourierTransformInv.fourierInv
        (fun ξ : ℝ => ∑ i ∈ s, φ i ξ * 𝓕 (f : ℝ → ℂ) ξ) x
      = ∑ i ∈ s, FourierTransformInv.fourierInv
          (fun ξ : ℝ => φ i ξ * 𝓕 (f : ℝ → ℂ) ξ) x := by
    intro x
    exact lacBump_fourierInv_finsetSum s
      (g := fun i ξ => φ i ξ * 𝓕 (f : ℝ → ℂ) ξ)
      (fun i hi => Integrable.mul_of_top_left (hφ i hi) hFtop) x
  calc Work.Analysis.IWMultiplier.contMulOp (fun ξ => ∑ i ∈ s, φ i ξ) (f : ℝ → ℂ)
      = FourierTransformInv.fourierInv
          (fun ξ : ℝ => ∑ i ∈ s, φ i ξ * 𝓕 (f : ℝ → ℂ) ξ) := by
        rw [Work.Analysis.IWMultiplier.contMulOp, hpt]
    _ = ∑ i ∈ s, FourierTransformInv.fourierInv
          (fun ξ : ℝ => φ i ξ * 𝓕 (f : ℝ → ℂ) ξ) := by
        funext x
        rw [Finset.sum_apply]
        exact hlin x
    _ = ∑ i ∈ s, Work.Analysis.IWMultiplier.contMulOp (φ i) (f : ℝ → ℂ) := by
        refine Finset.sum_congr rfl (fun i hi => ?_)
        rw [Work.Analysis.IWMultiplier.contMulOp]

/-- **The pointwise identity of the kernels of one fibre.** -/
lemma lacBump_kernel_fiber (M k₁ : ℕ) (hk₁ : 1 ≤ k₁) (t : ℝ) (a : ℕ → ℝ≥0) (U : Finset ℕ)
    (r : ℕ) (ε : ℕ → ℂ) (Ψ : ℝ → ℝ)
    (hΨ : ∀ u : ℝ, (Ψ u : ℂ) = FourierTransformInv.fourierInv lacψ u)
    (hker : ∀ (N : ℕ) (z : ℝ), FourierTransformInv.fourierInv (varphiNt N k₁ t) z
      = Work.Analysis.CzShift.shiftKernel Ψ (lacσ N k₁) (-((N : ℝ) * t) / lacσ N k₁) z) :
    (fun z : ℝ => FourierTransformInv.fourierInv
        (fun ξ : ℝ => ∑ n ∈ U.filter (fun n => n % M = r),
          ε n * varphiNt (Nat.floor (a n)) k₁ t ξ) z)
      = fun z : ℝ => ∑ n ∈ U.filter (fun n => n % M = r),
          ε n * Work.Analysis.CzShift.shiftKernel Ψ (lacσ (Nat.floor (a n)) k₁)
            (-((Nat.floor (a n) : ℝ) * t) / lacσ (Nat.floor (a n)) k₁) z := by
  funext z
  rw [lacBump_fourierInv_finsetSum (U.filter (fun n => n % M = r))
    (fun n _ => lacBump_integrable_smul_varphiNt (Nat.floor (a n)) k₁ t (ε n))]
  refine Finset.sum_congr rfl (fun n hn => ?_)
  rw [lacBump_fourierInv_const_mul (ε n) _ z, hker (Nat.floor (a n)) z]

/-- **The operator of one fibre is the `czOp` of the shifted-kernel family.** -/
lemma lacBump_fiberOp_eq_czOp (M k₁ : ℕ) (hk₁ : 1 ≤ k₁) (t : ℝ) (a : ℕ → ℝ≥0) (U : Finset ℕ)
    (r : ℕ) (ε : ℕ → ℂ) (Ψ : ℝ → ℝ)
    (hΨ : ∀ u : ℝ, (Ψ u : ℂ) = FourierTransformInv.fourierInv lacψ u)
    (hker : ∀ (N : ℕ) (z : ℝ), FourierTransformInv.fourierInv (varphiNt N k₁ t) z
      = Work.Analysis.CzShift.shiftKernel Ψ (lacσ N k₁) (-((N : ℝ) * t) / lacσ N k₁) z)
    (f : SchwartzMap ℝ ℂ) :
    Work.Analysis.IWMultiplier.contMulOp
        (fun ξ : ℝ => ∑ n ∈ U.filter (fun n => n % M = r),
          ε n * varphiNt (Nat.floor (a n)) k₁ t ξ) (f : ℝ → ℂ)
      = Work.Analysis.CzShift.czOp (U.filter (fun n => n % M = r))
          (fun n => Work.Analysis.CzShift.shiftKernel Ψ (lacσ (Nat.floor (a n)) k₁)
            (-((Nat.floor (a n) : ℝ) * t) / lacσ (Nat.floor (a n)) k₁))
          (fun n => ε n) (f : ℝ → ℂ) := by
  rw [lacBump_contMulOp_finsetSum (U.filter (fun n => n % M = r))
    (fun n ξ => ε n * varphiNt (Nat.floor (a n)) k₁ t ξ) f
    (fun n _ => lacBump_integrable_smul_varphiNt (Nat.floor (a n)) k₁ t (ε n))]
  unfold Work.Analysis.CzShift.czOp
  funext x
  simp only [Finset.sum_apply]
  refine Finset.sum_congr rfl (fun n hn => ?_)
  have h1 : FourierTransformInv.fourierInv
      (fun ξ : ℝ => ε n * varphiNt (Nat.floor (a n)) k₁ t ξ)
      = fun z : ℝ => ε n * Work.Analysis.CzShift.shiftKernel Ψ (lacσ (Nat.floor (a n)) k₁)
          (-((Nat.floor (a n) : ℝ) * t) / lacσ (Nat.floor (a n)) k₁) z := by
    funext z
    rw [lacBump_fourierInv_const_mul (ε n) _ z, hker (Nat.floor (a n)) z]
  rw [lacBump_contMulOp_eq_integral _ _
      (lacBump_integrable_smul_varphiNt (Nat.floor (a n)) k₁ t (ε n)) f.integrable x, h1,
    smul_eq_mul, ← MeasureTheory.integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall (fun y => ?_))
  ring

/-- The symbol is the sum of its fibres. -/
lemma lacBump_symbol_fiber (M : ℕ) (hM : 0 < M) (k₁ : ℕ) (t : ℝ) (a : ℕ → ℝ≥0) (U : Finset ℕ)
    (ε : ℕ → ℂ) :
    (fun ξ : ℝ => ∑ n ∈ U, ε n * varphiNt (Nat.floor (a n)) k₁ t ξ)
      = fun ξ : ℝ => ∑ r ∈ Finset.range M,
          ∑ n ∈ U.filter (fun n => n % M = r), ε n * varphiNt (Nat.floor (a n)) k₁ t ξ := by
  funext ξ
  exact (Finset.sum_fiberwise_of_maps_to (s := U) (t := Finset.range M) (g := fun n => n % M)
    (fun n _ => Finset.mem_range.mpr (Nat.mod_lt n hM))
    (fun n => ε n * varphiNt (Nat.floor (a n)) k₁ t ξ)).symm

end Work.KMTAreas.A7

namespace Work.KMTAreas.A7

open MeasureTheory
open scoped ENNReal NNReal BigOperators FourierTransform

theorem lacunaryBump_mult_bound_k1pos (p : ℝ) (hp : 1 < p) (Λ : NNReal) (hΛ : 1 < Λ) :
    ∃ C : NNReal, 0 < C ∧
      ∀ (k₁ : ℕ) (hk₁ : 1 ≤ k₁) (t : ℝ) (ht : t ∈ Set.Icc (1/2 : ℝ) 1) (a : ℕ → NNReal)
        (ha : PointwiseErgodicTheorems.Lacunary Λ a) (ha1 : ∀ n, 1 ≤ a n)
        (U : Finset ℕ) (ε : ℕ → ℂ) (hε : ∀ n, ‖ε n‖ ≤ 1),
        Work.Analysis.IWMultiplier.IsLqMultiplierBound (ENNReal.ofReal p)
          (fun ξ : ℝ => ∑ n ∈ U, ε n * Work.KMTAreas.A7.varphiNt (Nat.floor (a n)) k₁ t ξ)
          (C * (1 + k₁)) := by
  -- the decimation
  obtain ⟨M, hMpos, hMlac⟩ : ∃ M : ℕ, 0 < M ∧ ∀ (k₁ : ℕ) (a : ℕ → ℝ≥0),
      PointwiseErgodicTheorems.Lacunary Λ a → (∀ n, 1 ≤ a n) → ∀ (U : Finset ℕ) (r : ℕ),
      Work.Analysis.CzShift.LacunaryFam 2 (U.filter (fun n => n % M = r))
        (fun n => lacσ (Nat.floor (a n)) k₁) :=
    Work.KMTAreas.A7.lacBumpDecimation Λ hΛ
  -- the Calderón--Zygmund seed
  obtain ⟨Ψ, Ψ', B, hB1, hseed, hΨre, hΨF⟩ : ∃ (Ψ Ψ' : ℝ → ℝ) (B : ℝ), 1 ≤ B ∧
      Work.Analysis.CzShift.IsCZSeed Ψ Ψ' B ∧
      (∀ u : ℝ, (Ψ u : ℂ) = FourierTransformInv.fourierInv lacψ u) ∧
      (∀ ξ : ℝ, 𝓕 (fun u : ℝ => (Ψ u : ℂ)) ξ = lacψ ξ) :=
    Work.KMTAreas.A7.lacBumpSeed
  -- the elementary facts about `lacψ` and `lacσ`
  obtain ⟨hψ0, hψsupp, hψbd, hσpos, hσshift⟩ : lacψ 0 = 0 ∧
      (∀ ξ : ℝ, 1 < |ξ| → lacψ ξ = 0) ∧
      (∀ ξ : ℝ, ‖lacψ ξ‖ ≤ 8 * min 1 |ξ|) ∧
      (∀ N k₁ : ℕ, 0 < lacσ N k₁) ∧
      (∀ N k₁ : ℕ, 1 ≤ N → (N : ℝ) / lacσ N k₁ ≤ (2 : ℝ) ^ (k₁ + 1)) :=
    Work.KMTAreas.A7.lacBumpPsiFacts
  -- the shifted Calderón--Zygmund theorem
  obtain ⟨C₀, hC₀pos, hC₀⟩ :=
    Work.Analysis.CzShift.cz_shift_lp 2 B 8 (by norm_num) hB1 (by norm_num) hp
  have hC₀nn : 0 ≤ C₀ := le_of_lt hC₀pos
  have hBnn : 0 ≤ B := le_trans zero_le_one hB1
  have hCconst : 0 ≤ (M : ℝ) * (2 * (C₀ * (B + 1)) + 1) := by positivity
  have hCconstpos : 0 < (M : ℝ) * (2 * (C₀ * (B + 1)) + 1) := by
    have hM0 : (0 : ℝ) < M := by exact_mod_cast hMpos
    have h1 : 0 ≤ C₀ * (B + 1) := mul_nonneg hC₀nn (by linarith)
    have h2 : 0 < 2 * (C₀ * (B + 1)) + 1 := by linarith
    exact mul_pos hM0 h2
  refine ⟨⟨(M : ℝ) * (2 * (C₀ * (B + 1)) + 1), hCconst⟩, ?_, ?_⟩
  · exact NNReal.coe_pos.mp hCconstpos
  intro k₁ hk₁ t ht a ha ha1 U ε hε
  -- the shift function of the term `n`
  let lam : ℕ → ℝ := fun n => -((Nat.floor (a n) : ℝ) * t) / lacσ (Nat.floor (a n)) k₁
  -- the kernel identity of the child lemma, in pointwise form
  have hker : ∀ (N : ℕ) (z : ℝ), FourierTransformInv.fourierInv (varphiNt N k₁ t) z
      = Work.Analysis.CzShift.shiftKernel Ψ (lacσ N k₁) (-((N : ℝ) * t) / lacσ N k₁) z := by
    intro N z
    exact congrFun (Work.KMTAreas.A7.lacBumpKernel Ψ hΨre N k₁ hk₁ t) z
  have hsupp : ∀ ξ : ℝ, 8 < |ξ| → 𝓕 (fun u : ℝ => (Ψ u : ℂ)) ξ = 0 := by
    intro ξ hξ
    rw [hΨF ξ]
    exact hψsupp ξ (by linarith)
  have hbd : ∀ ξ : ℝ, ‖𝓕 (fun u : ℝ => (Ψ u : ℂ)) ξ‖ ≤ 8 * min 1 |ξ| := by
    intro ξ
    rw [hΨF ξ]
    exact hψbd ξ
  -- the bound for one fibre, uniform in the fibre
  have hfiber : ∀ (r : ℕ) (f : SchwartzMap ℝ ℂ),
      eLpNorm (Work.Analysis.IWMultiplier.contMulOp
          (fun ξ : ℝ => ∑ n ∈ U.filter (fun n => n % M = r),
            ε n * varphiNt (Nat.floor (a n)) k₁ t ξ) (f : ℝ → ℂ))
        (ENNReal.ofReal p) volume
      ≤ ENNReal.ofReal (C₀ * (B * (1 + ((k₁ : ℝ) + 1)) + 1))
          * eLpNorm (f : ℝ → ℂ) (ENNReal.ofReal p) volume := by
    intro r f
    have hsh : ∀ n ∈ U.filter (fun n => n % M = r), |lam n| ≤ 2 ^ ((k₁ : ℝ) + 1) := by
      intro n hn
      have hN1 : 1 ≤ Nat.floor (a n) :=
        Nat.le_floor (show ((1 : ℕ) : ℝ) ≤ (a n : ℝ) by exact_mod_cast ha1 n)
      have hσp : 0 < lacσ (Nat.floor (a n)) k₁ := hσpos _ _
      have ht1 : t ≤ 1 := ht.2
      have ht0 : 0 ≤ t := by linarith [ht.1]
      have hσb := hσshift (Nat.floor (a n)) k₁ hN1
      have hσb' : (Nat.floor (a n) : ℝ)
          ≤ (2 : ℝ) ^ (k₁ + 1) * lacσ (Nat.floor (a n)) k₁ := by
        rw [div_le_iff₀ hσp] at hσb
        exact hσb
      have h2pow : ((2 : ℝ) ^ (k₁ + 1)) = (2 : ℝ) ^ ((k₁ : ℝ) + 1) := by
        rw [← Real.rpow_natCast (2 : ℝ) (k₁ + 1)]
        congr 1
        push_cast
        ring
      rw [← h2pow]
      rw [show lam n = -((Nat.floor (a n) : ℝ) * t) / lacσ (Nat.floor (a n)) k₁ from rfl,
        abs_div, abs_neg, abs_mul, abs_of_nonneg (Nat.cast_nonneg _), abs_of_pos hσp,
        div_le_iff₀ hσp]
      calc (Nat.floor (a n) : ℝ) * |t| ≤ (Nat.floor (a n) : ℝ) * 1 :=
            mul_le_mul_of_nonneg_left (by rw [abs_of_nonneg ht0]; exact ht1) (Nat.cast_nonneg _)
        _ = (Nat.floor (a n) : ℝ) := mul_one _
        _ ≤ (2 : ℝ) ^ (k₁ + 1) * lacσ (Nat.floor (a n)) k₁ := hσb'
    have hcz := hC₀ (U.filter (fun n => n % M = r))
      (fun n => lacσ (Nat.floor (a n)) k₁) lam Ψ Ψ' ((k₁ : ℝ) + 1)
      (hMlac k₁ a ha ha1 U r) hseed (by linarith [show (0:ℝ) ≤ (k₁:ℝ) by positivity])
      hsh hsupp hbd (fun n => ε n) (fun n _ => hε n) (f : ℝ → ℂ) f.integrable
      (SchwartzMap.memLp f (ENNReal.ofReal p) (volume : Measure ℝ))
    rw [lacBump_fiberOp_eq_czOp M k₁ hk₁ t a U r ε Ψ hΨre hker f]
    exact hcz
  intro f
  -- the Fourier transform of a Schwartz function is integrable
  have hFtop : MemLp (fun ξ : ℝ => 𝓕 (f : ℝ → ℂ) ξ) ⊤ (volume : Measure ℝ) := by
    simpa only [SchwartzMap.fourier_coe] using
      (SchwartzMap.memLp (𝓕 f) ⊤ (volume : Measure ℝ))
  -- the symbol is the sum of its fibres
  rw [lacBump_symbol_fiber M hMpos k₁ t a U ε]
  -- the multiplier is the sum of the fibre multipliers
  rw [lacBump_contMulOp_finsetSum (Finset.range M)
    (fun r ξ => ∑ n ∈ U.filter (fun n => n % M = r),
      ε n * varphiNt (Nat.floor (a n)) k₁ t ξ) f
    (fun r _ => integrable_finsetSum _ (fun n _ =>
      lacBump_integrable_smul_varphiNt (Nat.floor (a n)) k₁ t (ε n)))]
  -- the triangle inequality over the fibres
  refine (eLpNorm_sum_le ?_).trans ?_
  · exact ENNReal.one_le_ofReal.mpr (le_of_lt hp)
  · refine (Finset.sum_le_sum (fun r _ => hfiber r f)).trans ?_
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, ← mul_assoc]
    refine mul_le_mul_of_nonneg_right ?_ zero_le
    have hM0 : (0 : ℝ) ≤ (M : ℝ) := Nat.cast_nonneg M
    have hk1 : (0 : ℝ) ≤ (k₁ : ℝ) := Nat.cast_nonneg k₁
    have hB0 : 0 ≤ B := le_trans zero_le_one hB1
    have hC₀nn : 0 ≤ C₀ := le_of_lt hC₀pos
    have hrealineq : (M : ℝ) * (C₀ * (B * (1 + ((k₁ : ℝ) + 1)) + 1))
        ≤ (M : ℝ) * (2 * (C₀ * (B + 1)) + 1) * (1 + (k₁ : ℝ)) := by
      have hCB : 0 ≤ C₀ * B := mul_nonneg hC₀nn hB0
      have hCBk : 0 ≤ C₀ * B * k₁ := mul_nonneg hCB hk1
      have hCk : 0 ≤ C₀ * k₁ := mul_nonneg hC₀nn hk1
      have key : C₀ * (B * (1 + ((k₁ : ℝ) + 1)) + 1)
          ≤ (2 * (C₀ * (B + 1)) + 1) * (1 + (k₁ : ℝ)) := by
        nlinarith [hCB, hCBk, hCk, hC₀nn, hB0, hk1]
      calc (M : ℝ) * (C₀ * (B * (1 + ((k₁ : ℝ) + 1)) + 1))
          ≤ (M : ℝ) * ((2 * (C₀ * (B + 1)) + 1) * (1 + (k₁ : ℝ))) :=
            mul_le_mul_of_nonneg_left key hM0
        _ = (M : ℝ) * (2 * (C₀ * (B + 1)) + 1) * (1 + (k₁ : ℝ)) := by ring
    rw [← ENNReal.ofReal_natCast M,
      ← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ (M : ℝ))]
    refine ENNReal.ofReal_le_ofReal ?_
    push_cast
    exact hrealineq

end Work.KMTAreas.A7
