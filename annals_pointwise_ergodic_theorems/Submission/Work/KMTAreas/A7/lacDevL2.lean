/-
# The `ℓ²` bound for the linearised deviation kernel of the lacunary bump-dilation family

This file proves `Work.KMTAreas.A7.lacDevL2`: the convolution operator `T_kg = k ⋆ g` with the
linearised deviation kernel `k = lacDevLin K σ U ω` is bounded on `ℓ²(ℤ)`, with a constant `A`
which depends only on the pointwise bound `C` of the symbol
`θ ↦ ∑'_j k_j e^{2πijθ}` of `k`.

The proof is Plancherel on `ℤ`:

* the kernel `k = lacDevLin K σ U ω` is `ℓ¹`, being a finite signed sum of the summable deviation
  kernels `devKern K σ n` (`summable_norm_lacDevLin`);
* consequently the symbol series `∑'_j k_j e^{2πijξ}` converges uniformly and defines a continuous
  (hence measurable and bounded) function `m : ℝ/ℤ → ℂ`, the class
  `Work.KMTAreas.A7.lacDevSymC`;
* the Fourier coefficients of `m` are the coefficients of the series, `fourierCoeff m j = k j`,
  by termwise integration (`integral_tsum`) and the orthogonality of the characters
  (`fourierCoeff_fourier`);
* the `ℓ²(ℤ)` multiplier with symbol `m` (`Work.Analysis.IonescuWainger.multiplierOf`) acts by
  convolution with `k` on all of `ℓ²(ℤ)`
  (`Work.KMTPlan.A6.fourierCoeff_lpSMul_fourierZ_l2`), hence its operator norm — bounded by the
  sup norm `C` of `m` (Plancherel) — bounds the convolution operator on `ℓ²(ℤ)`, which is the
  claim after translating `eLpNorm · 2 (count : Measure ℤ)` into the `ℓ²` norm.
-/
import Mathlib
import Submission.Work.KMTAreas.A7.LacDevBasics
import Submission.Work.KMTPlan.A6.iwConvEqIwOpSetMemlp
import Submission.Port.Aesm

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Work.KMTAreas.A7

open MeasureTheory
open scoped ENNReal BigOperators

noncomputable section

open Work.Analysis.IonescuWainger

/-! ## Elementary summability and `ℓ²` facts for lattice sequences -/

/-- A summable `ℤ`-indexed sequence of norms is bounded. -/
lemma bounded_of_summable_norm_lattice {g : ℤ → ℂ} (hg : Summable (fun n : ℤ => ‖g n‖)) :
    ∃ M : ℝ, ∀ n : ℤ, ‖g n‖ ≤ M := by
  have h1 : Filter.Tendsto (fun n : ℤ => ‖g n‖) Filter.cofinite (nhds 0) :=
    hg.tendsto_cofinite_zero
  have h2 : ∀ᶠ n : ℤ in Filter.cofinite, ‖g n‖ < 1 :=
    h1.eventually (eventually_lt_nhds (by norm_num))
  have hfin : ({n : ℤ | ¬ (‖g n‖ < 1)}).Finite := Filter.eventually_cofinite.mp h2
  refine ⟨max 1 (∑ m ∈ hfin.toFinset, ‖g m‖), fun n => ?_⟩
  by_cases hn : 1 ≤ ‖g n‖
  · have hmem : n ∈ hfin.toFinset := by
      rw [Set.Finite.mem_toFinset]
      exact not_lt.mpr hn
    exact le_trans (Finset.single_le_sum (fun m _ => norm_nonneg _) hmem) (le_max_right _ _)
  · exact le_trans (le_of_lt (not_le.mp hn)) (le_max_left _ _)

/-- An `ℓ¹` sequence on `ℤ` is `ℓ²`. -/
lemma summable_memℓp_two {g : ℤ → ℂ} (hg : Summable g) : Memℓp g 2 := by
  rw [memℓp_gen_iff (show 0 < (2 : ENNReal).toReal by norm_num)]
  have hsum : Summable (fun n : ℤ => ‖g n‖) := summable_norm_iff.mpr hg
  obtain ⟨M, hM⟩ := bounded_of_summable_norm_lattice hsum
  have hM0 : 0 ≤ M := le_trans (norm_nonneg (g 0)) (hM 0)
  refine Summable.of_nonneg_of_le
    (f := fun n : ℤ => ‖g n‖ * M)
    (g := fun n : ℤ => ‖g n‖ ^ (2 : ENNReal).toReal)
    (fun n => Real.rpow_nonneg (norm_nonneg _) _) (fun n => ?_) (hsum.mul_right M)
  rw [show (2 : ENNReal).toReal = 2 by norm_num, Real.rpow_two, pow_two]
  exact mul_le_mul_of_nonneg_left (hM n) (norm_nonneg (g n))

/-- The linearised deviation kernel `lacDevLin K σ U ω` is `ℓ¹`. -/
lemma summable_norm_lacDevLin (K : SchwartzMap ℝ ℂ) (σ : ℕ → ℕ) (hσ1 : ∀ n, 1 ≤ σ n)
    (U : Finset ℕ) (ω : ℕ → Bool) :
    Summable (fun j : ℤ => ‖lacDevLin K σ U ω j‖) := by
  have hmajor : Summable (fun j : ℤ => ∑ n ∈ U, ‖devKern K σ n j‖) := by
    classical
    induction U using Finset.induction_on with
    | empty => simpa using (summable_zero : Summable (fun _ : ℤ => (0 : ℝ)))
    | insert a s ha ih =>
      have hfun : (fun j : ℤ => ∑ n ∈ insert a s, ‖devKern K σ n j‖)
          = (fun j : ℤ => ‖devKern K σ a j‖)
            + (fun j : ℤ => ∑ n ∈ s, ‖devKern K σ n j‖) := by
        funext j
        simp [Finset.sum_insert ha]
      rw [hfun]
      exact ((devKern_summable K σ hσ1 a).norm).add ih
  refine Summable.of_nonneg_of_le
    (f := fun j : ℤ => ∑ n ∈ U, ‖devKern K σ n j‖)
    (g := fun j : ℤ => ‖lacDevLin K σ U ω j‖) (fun j => norm_nonneg _) (fun j => ?_) hmajor
  calc ‖lacDevLin K σ U ω j‖
      = ‖∑ n ∈ U, Work.KMTAreas.ADev.bSign ω n * devKern K σ n j‖ := rfl
    _ ≤ ∑ n ∈ U, ‖devKern K σ n j‖ := by
        refine (norm_sum_le _ _).trans ?_
        exact Finset.sum_le_sum fun n _ => by
          rw [norm_mul]
          exact mul_le_of_le_one_left (norm_nonneg _) (Work.KMTAreas.ADev.norm_bSign_le ω n)

/-- Reindexing a lattice convolution. -/
lemma tsum_conv_flip_lattice (k g : ℤ → ℂ) (x : ℤ) :
    (∑' y : ℤ, k (x - y) * g y) = ∑' j : ℤ, k j * g (x - j) := by
  have h := Equiv.tsum_eq (Equiv.subLeft x) (fun y : ℤ => k (x - y) * g y)
  simp only [Equiv.subLeft_apply] at h
  rw [← h]
  refine tsum_congr fun j => ?_
  rw [sub_sub_cancel]

/-! ## The symbol of the linearised deviation kernel -/

/-- The symbol of the linearised deviation kernel, as a continuous function on the frequency
circle: the uniformly convergent series `ξ ↦ ∑'_j k_j e^{2πijξ}`. -/
def lacDevSymC (K : SchwartzMap ℝ ℂ) (σ : ℕ → ℕ) (U : Finset ℕ) (ω : ℕ → Bool) :
    C(AddCircle (1 : ℝ), ℂ) :=
  ∑' j : ℤ, lacDevLin K σ U ω j • fourier (T := 1) j

/-- The value of the symbol is the pointwise Fourier series of the kernel. -/
lemma lacDevSymC_apply (K : SchwartzMap ℝ ℂ) (σ : ℕ → ℕ) (U : Finset ℕ) (ω : ℕ → Bool)
    (hk : Summable (fun j : ℤ => ‖lacDevLin K σ U ω j‖)) (ξ : AddCircle (1 : ℝ)) :
    lacDevSymC K σ U ω ξ = ∑' j : ℤ, lacDevLin K σ U ω j * fourier (T := 1) j ξ := by
  have hsumC : Summable (fun j : ℤ =>
      lacDevLin K σ U ω j • (fourier (T := 1) j : C(AddCircle (1 : ℝ), ℂ))) := by
    refine Summable.of_norm ?_
    have h : (fun j : ℤ => ‖lacDevLin K σ U ω j •
          (fourier (T := 1) j : C(AddCircle (1 : ℝ), ℂ))‖) = fun j => ‖lacDevLin K σ U ω j‖ := by
      funext j
      rw [norm_smul, fourier_norm, mul_one]
    rw [h]
    exact hk
  have h := (ContinuousLinearMap.hasSum (ContinuousMap.evalCLM ℂ ξ) hsumC.hasSum).tsum_eq
  simp only [ContinuousMap.evalCLM_apply] at h
  exact h.symm

/-- The Fourier coefficients of the symbol are the coefficients of its defining series. -/
lemma fourierCoeff_eq_of_eq_tsum (k : ℤ → ℂ) (hk : Summable (fun j : ℤ => ‖k j‖))
    (m : AddCircle (1 : ℝ) → ℂ)
    (hm : ∀ ξ : AddCircle (1 : ℝ), m ξ = ∑' j : ℤ, k j * fourier (T := 1) j ξ) (j : ℤ) :
    fourierCoeff (T := 1) m j = k j := by
  have hfou : ∀ (n : ℤ) (ξ : AddCircle (1 : ℝ)), ‖fourier (T := 1) n ξ‖ = 1 := by
    intro n ξ
    rw [fourier_apply]
    exact Circle.norm_coe _
  have hmeas : ∀ n : ℤ, AEStronglyMeasurable (fun ξ : AddCircle (1 : ℝ) =>
      fourier (T := 1) (-j) ξ * (k n * fourier (T := 1) n ξ)) circleMeasure := by
    intro n
    exact ((map_continuous (fourier (T := 1) (-j))).mul
      (continuous_const.mul (map_continuous (fourier (T := 1) n)))).aestronglyMeasurable
  have hnorn : ∀ n : ℤ, ∫⁻ ξ : AddCircle (1 : ℝ),
      ‖fourier (T := 1) (-j) ξ * (k n * fourier (T := 1) n ξ)‖ₑ ∂circleMeasure = ‖k n‖ₑ := by
    intro n
    have hpt : ∀ ξ : AddCircle (1 : ℝ),
        ‖fourier (T := 1) (-j) ξ * (k n * fourier (T := 1) n ξ)‖ₑ = ‖k n‖ₑ := by
      intro ξ
      have h1 : ‖fourier (T := 1) (-j) ξ‖ₑ = 1 := by
        rw [← ofReal_norm, hfou (-j) ξ]
        norm_num
      have h2 : ‖fourier (T := 1) n ξ‖ₑ = 1 := by
        rw [← ofReal_norm, hfou n ξ]
        norm_num
      rw [enorm_mul, enorm_mul, h1, h2]
      norm_num
    rw [lintegral_congr hpt, lintegral_const, measure_univ, mul_one]
  have hne : ∑' n : ℤ, ∫⁻ ξ : AddCircle (1 : ℝ),
      ‖fourier (T := 1) (-j) ξ * (k n * fourier (T := 1) n ξ)‖ₑ ∂circleMeasure ≠ ⊤ := by
    rw [tsum_congr hnorn]
    have hfin : (∑' n : ℤ, ‖k n‖ₑ) = ENNReal.ofReal (∑' n : ℤ, ‖k n‖) := by
      rw [ENNReal.ofReal_tsum_of_nonneg (fun n => norm_nonneg _) hk]
      exact tsum_congr fun n => (ofReal_norm (k n)).symm
    rw [hfin]
    exact ENNReal.ofReal_ne_top
  have hkey : fourierCoeff (T := 1) m j
      = ∑' n : ℤ, ∫ ξ : AddCircle (1 : ℝ),
          fourier (T := 1) (-j) ξ * (k n * fourier (T := 1) n ξ) ∂circleMeasure := by
    rw [fourierCoeff]
    have hthis : (fun t : AddCircle (1 : ℝ) => fourier (T := 1) (-j) t • m t)
        = fun ξ => ∑' n : ℤ, fourier (T := 1) (-j) ξ * (k n * fourier (T := 1) n ξ) := by
      funext ξ
      rw [hm ξ, tsum_mul_left]
      simp [smul_eq_mul]
    rw [hthis, integral_tsum hmeas hne]
  rw [hkey]
  have hinner : ∀ n : ℤ, ∫ ξ : AddCircle (1 : ℝ),
        fourier (T := 1) (-j) ξ * (k n * fourier (T := 1) n ξ) ∂circleMeasure
      = k n * (if j = n then (1 : ℂ) else 0) := by
    intro n
    have h5 : fourierCoeff (T := 1) (fun ξ : AddCircle (1 : ℝ) => fourier (T := 1) n ξ) j
        = if j = n then (1 : ℂ) else 0 := by
      rw [congrFun (fourierCoeff_fourier (T := 1) n) j]
      by_cases h : j = n
      · rw [if_pos h, h, Pi.single_eq_same]
      · rw [if_neg h, Pi.single_eq_of_ne h]
    have hcoe : fourierCoeff (T := 1) (fun ξ : AddCircle (1 : ℝ) =>
          k n * fourier (T := 1) n ξ) j = k n * (if j = n then (1 : ℂ) else 0) := by
      rw [fourierCoeff.const_mul, h5]
    simpa only [fourierCoeff, smul_eq_mul] using hcoe
  have htsum : (∑' n : ℤ, k n * (if j = n then (1 : ℂ) else 0)) = k j := by
    refine (tsum_eq_single j ?_).trans ?_
    · intro n hn
      rw [if_neg (Ne.symm hn), mul_zero]
    · simp
  exact (tsum_congr hinner).trans htsum

/-- The symbol of the kernel, evaluated on the circle, obeys the same bound as the real
characters of the hypothesis. -/
lemma norm_tsum_fourier_le (k : ℤ → ℂ) (C : ℝ)
    (hsym : ∀ θ : ℝ, ‖∑' j : ℤ, k j * Work.KMTAreas.ADev.chr j θ‖ ≤ C) :
    ∀ ξ : AddCircle (1 : ℝ), ‖∑' j : ℤ, k j * fourier (T := 1) j ξ‖ ≤ C := by
  intro ξ
  obtain ⟨θ, rfl⟩ := QuotientAddGroup.mk_surjective ξ
  have hcongr : (∑' j : ℤ, k j * fourier (T := 1) j (θ : AddCircle (1 : ℝ)))
      = ∑' j : ℤ, k j * Work.KMTAreas.ADev.chr j θ := by
    refine tsum_congr fun j => ?_
    refine congrArg (fun z => k j * z) ?_
    rw [fourier_coe_apply, Work.KMTAreas.ADev.chr]
    congr 1
    push_cast
    ring
  rw [hcongr]
  exact hsym θ

/-! ## The multiplier identity on `ℓ²(ℤ)` -/

/-- The `n`-th value of the `ℓ²(ℤ)` Fourier multiplier with symbol `m` is the `n`-th Fourier
coefficient of `m · 𝓕_ℤ F`. -/
lemma multiplierOf_apply_eq_fourierCoeff (m : AddCircle (1 : ℝ) → ℂ)
    (hm : MemLp m ⊤ circleMeasure) (F : L2Z) (n : ℤ) :
    ⇑(multiplierOf m hm F) n = fourierCoeff (⇑(hm.toLp m • fourierZ F)) n := by
  have h1 : ⇑(multiplierOf m hm F) n = (fourierZ.symm (hm.toLp m • fourierZ F)) n := rfl
  rw [h1]
  have hsymm : fourierZ.symm = (fourierBasis (T := 1)).repr := rfl
  rw [hsymm]
  exact fourierBasis_repr _ n

/-! ## The main theorem -/

theorem lacDevL2 (K : SchwartzMap ℝ ℂ) (C : ℝ) (hC : 0 < C)
    (hsym : ∀ (σ : ℕ → ℕ), (∀ n, 1 ≤ σ n) → (∀ n, 2 * σ n ≤ σ (n + 1)) →
      ∀ (U : Finset ℕ) (ω : ℕ → Bool) (θ : ℝ),
        ‖∑' j : ℤ, Work.KMTAreas.A7.lacDevLin K σ U ω j * Work.KMTAreas.ADev.chr j θ‖ ≤ C) :
    ∃ A : ℝ, 0 < A ∧ ∀ (σ : ℕ → ℕ), (∀ n, 1 ≤ σ n) → (∀ n, 2 * σ n ≤ σ (n + 1)) →
      ∀ (U : Finset ℕ) (ω : ℕ → Bool) (g : ℤ → ℂ), Summable g →
        MeasureTheory.eLpNorm
            (fun x : ℤ => ∑' y : ℤ, Work.KMTAreas.A7.lacDevLin K σ U ω (x - y) * g y)
            2 (MeasureTheory.Measure.count : MeasureTheory.Measure ℤ)
        ≤ ENNReal.ofReal A * MeasureTheory.eLpNorm g 2
            (MeasureTheory.Measure.count : MeasureTheory.Measure ℤ) := by
  refine ⟨C, hC, ?_⟩
  intro σ hσ1 hσ2 U ω g hg
  have hk : Summable (fun j : ℤ => ‖lacDevLin K σ U ω j‖) :=
    summable_norm_lacDevLin K σ hσ1 U ω
  set mfun : AddCircle (1 : ℝ) → ℂ := fun ξ => lacDevSymC K σ U ω ξ with hmfun_def
  have hmapp : ∀ ξ : AddCircle (1 : ℝ), mfun ξ
      = ∑' j : ℤ, lacDevLin K σ U ω j * fourier (T := 1) j ξ := by
    intro ξ
    simp only [hmfun_def]
    exact lacDevSymC_apply K σ U ω hk ξ
  have hbnd : ∀ ξ : AddCircle (1 : ℝ), ‖mfun ξ‖ ≤ C := by
    intro ξ
    rw [hmapp ξ]
    exact norm_tsum_fourier_le (lacDevLin K σ U ω) C (fun θ => hsym σ hσ1 hσ2 U ω θ) ξ
  have hcont : Continuous mfun := by
    simpa only [hmfun_def] using map_continuous (lacDevSymC K σ U ω)
  have hmm : MemLp mfun ⊤ circleMeasure :=
    MemLp.of_bound hcont.aestronglyMeasurable C (ae_of_all _ hbnd)
  have heLp : eLpNorm mfun ⊤ circleMeasure ≤ ENNReal.ofReal C := by
    rw [eLpNorm_exponent_top (hf := by pw_aesm), eLpNormEssSup_eq_essSup_enorm]
    refine essSup_le_of_ae_le (ENNReal.ofReal C) (ae_of_all _ fun ξ => ?_)
    rw [ENNReal.ofReal, enorm_le_coe, ← NNReal.coe_le_coe, coe_nnnorm,
      Real.coe_toNNReal C hC.le]
    exact hbnd ξ
  have hop : ‖multiplierOf mfun hmm‖ ≤ C := norm_multiplierOf_le hmm hC.le heLp
  have hg2 : Memℓp g 2 := summable_memℓp_two hg
  have hconv : ⇑(multiplierOf mfun hmm (⟨g, hg2⟩ : L2Z))
      = fun n : ℤ => ∑' j : ℤ, lacDevLin K σ U ω j * g (n - j) := by
    funext n
    rw [multiplierOf_apply_eq_fourierCoeff mfun hmm (⟨g, hg2⟩ : L2Z) n,
      Work.KMTPlan.A6.fourierCoeff_lpSMul_fourierZ_l2 hmm (⟨g, hg2⟩ : L2Z) n]
    refine tsum_congr fun j => ?_
    rw [fourierCoeff_eq_of_eq_tsum (lacDevLin K σ U ω) hk mfun hmapp j]
  have hmem : Memℓp (fun n : ℤ => ∑' j : ℤ, lacDevLin K σ U ω j * g (n - j)) 2 :=
    hconv ▸ (multiplierOf mfun hmm (⟨g, hg2⟩ : L2Z)).property
  have hflip : (fun x : ℤ => ∑' y : ℤ, lacDevLin K σ U ω (x - y) * g y)
      = fun n : ℤ => ∑' j : ℤ, lacDevLin K σ U ω j * g (n - j) := by
    funext x
    exact tsum_conv_flip_lattice (lacDevLin K σ U ω) g x
  have e2 : (⟨fun n : ℤ => ∑' j : ℤ, lacDevLin K σ U ω j * g (n - j), hmem⟩
        : lp (fun _ : ℤ => ℂ) 2)
      = multiplierOf mfun hmm (⟨g, hg2⟩ : L2Z) := Subtype.ext hconv.symm
  rw [hflip, Work.Analysis.IWMultiplier.eLpNorm_two_count_eq_ofReal_lpNorm _ hmem, e2,
    Work.Analysis.IWMultiplier.eLpNorm_two_count_eq_ofReal_lpNorm g hg2]
  calc ENNReal.ofReal ‖multiplierOf mfun hmm (⟨g, hg2⟩ : L2Z)‖
      ≤ ENNReal.ofReal (C * ‖(⟨g, hg2⟩ : L2Z)‖) := by
        refine ENNReal.ofReal_le_ofReal ?_
        calc ‖multiplierOf mfun hmm (⟨g, hg2⟩ : L2Z)‖
            ≤ ‖multiplierOf mfun hmm‖ * ‖(⟨g, hg2⟩ : L2Z)‖ :=
              ContinuousLinearMap.le_opNorm _ _
          _ ≤ C * ‖(⟨g, hg2⟩ : L2Z)‖ := by gcongr
    _ = ENNReal.ofReal C * ENNReal.ofReal ‖(⟨g, hg2⟩ : L2Z)‖ := ENNReal.ofReal_mul hC.le

end

end Work.KMTAreas.A7
