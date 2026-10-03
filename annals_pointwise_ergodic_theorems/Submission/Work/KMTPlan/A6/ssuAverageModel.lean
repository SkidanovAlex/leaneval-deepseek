/-
# The band realisation of the halved average (`ssuAverageModel`)

This file proves `Work.KMTPlan.A6.ssuAverageModel`: the halved average
`Ã_N(A,B)(x) = N⁻¹ ∑_{N/2 < n ≤ N} A(x-n) B(x-P(n))` of the two exact-height Ionescu–Wainger
multipliers `A = Tm ρ l₁ φ f`, `B = Tm ρ l₂ ψ g` agrees, up to the explicit error
`ssuErr P u N`, with the model sum

`∑_{α ∈ A_{l₁}} ∑_{β ∈ A_{l₂}} ssuCoeff P N α β · (band at α of A) · (band at β of B)`

in which each band is the single-arithmetic-frequency piece `iwConv {α} (periodize φ) f` and
`ssuCoeff P N α β` is the mean of the arithmetic character `n ↦ e(nα + β P(n))` over the window.

The proof is the paper's §5 band realisation: writing `ΔA_n = A(·-n) - (modulated bands)` and
`ΔB_n = B(·-P(n)) - (modulated bands)`, the shift–modulation estimate
`Work.KMTPlan.A6.shift_modulation_le` bounds `ΔA_n`, `ΔB_n` by `2π|n|2^{-3u}‖A‖₂` and
`2π|P(n)|2^{-3du}‖B‖₂`, while the modulated band sums have exactly the norm of `A`, `B`
(orthogonality of the non-aliasing bands).  Cauchy–Schwarz in `ℓ¹` then gives the stated error.
-/
import Mathlib
import Submission.Work.KMTPlan.A6.SsuDefs
import Submission.Work.KMTPlan.A6.shift_modulation_le
import Submission.Commons.MeasureTheory.Function.eLpNorm_mul_le_eLpNorm_mul_eLpNorm
import Submission.Port.Aesm

set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace Work.KMTPlan.A6

open MeasureTheory Polynomial Finset
open scoped ENNReal NNReal BigOperators
open Work.Analysis.IonescuWainger Work.Analysis.IWMultiplier Work.KMTAreas.A7

local notation "Circ" => Work.Analysis.IonescuWainger.Circle

/-! ## Elementary Hilbert space facts on `ℤ` -/

/-- Cauchy–Schwarz for the `ℓ¹`-norm of a product of two `ℓ²`-sequences. -/
theorem ssu_eLpNorm_mul_le_two (f g : ℤ → ℂ) :
    eLpNorm (fun x : ℤ => f x * g x) 1 Measure.count
      ≤ eLpNorm f 2 Measure.count * eLpNorm g 2 Measure.count := by
  have h1 : eLpNorm (fun x : ℤ => f x * g x) 1 Measure.count
      = eLpNorm (fun x : ℤ => ‖f x‖ₑ * ‖g x‖ₑ) 1 Measure.count := by
    rw [← MeasureTheory.eLpNorm_enorm (hf := by pw_aesm) (f := fun x : ℤ => f x * g x)]
    exact MeasureTheory.eLpNorm_congr_ae
      (ae_of_all _ (fun x => by simp only [enorm_mul]))
  have h12 : (1 : ENNReal)⁻¹ = (2 : ENNReal)⁻¹ + (2 : ENNReal)⁻¹ := by
    rw [inv_one]
    exact ENNReal.inv_two_add_inv_two.symm
  rw [h1, ← MeasureTheory.eLpNorm_enorm (hf := by pw_aesm) (f := f), ← MeasureTheory.eLpNorm_enorm (hf := by pw_aesm) (f := g)]
  exact Commons.MeasureTheory.Function.eLpNorm_mul_le_eLpNorm_mul_eLpNorm (p := 1) (q := 2) (r := 2)
    h12 (Measurable.of_discrete.aemeasurable) (Measurable.of_discrete.aemeasurable)

/-- The triangle inequality for a finite family of products: the `ℓ¹`-norm of
`∑_n g n · h n` is bounded by the sum of the products of the `ℓ²`-norms. -/
theorem ssu_sum_mul_le {s : Finset ℕ} {g h : ℕ → ℤ → ℂ} {εg εh : ℕ → ENNReal}
    (hgb : ∀ n ∈ s, eLpNorm (g n) 2 Measure.count ≤ εg n)
    (hhb : ∀ n ∈ s, eLpNorm (h n) 2 Measure.count ≤ εh n) :
    eLpNorm (fun x : ℤ => ∑ n ∈ s, g n x * h n x) 1 Measure.count
      ≤ ∑ n ∈ s, εg n * εh n := by
  have hsum : (∑ n ∈ s, fun x : ℤ => g n x * h n x)
      = fun x : ℤ => ∑ n ∈ s, g n x * h n x := by
    funext x
    simp only [Finset.sum_apply]
  rw [← hsum]
  refine (MeasureTheory.eLpNorm_sum_le
    le_rfl).trans ?_
  exact Finset.sum_le_sum (fun n hn =>
    (ssu_eLpNorm_mul_le_two (g n) (h n)).trans (mul_le_mul' (hgb n hn) (hhb n hn)))

/-- Translation invariance of the `ℓ²`-seminorm on `ℤ` for the counting measure. -/
theorem ssu_eLpNorm_sub_right (f : ℤ → ℂ) (m : ℤ) :
    eLpNorm (fun x : ℤ => f (x - m)) 2 Measure.count = eLpNorm f 2 Measure.count := by
  have hsub : eLpNorm (fun x : ℤ => ‖f (x - m)‖ₑ) 2 Measure.count
      = eLpNorm (fun x : ℤ => ‖f x‖ₑ) 2 Measure.count := by
    rw [show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by norm_num]
    exact Commons.Analysis.Convolution.eLpNorm_sub_right_ennreal (fun w : ℤ => ‖f w‖ₑ) m
      (by norm_num : (0 : ℝ) < 2)
  rw [← MeasureTheory.eLpNorm_enorm (hf := by pw_aesm) (f := fun x : ℤ => f (x - m)),
    ← MeasureTheory.eLpNorm_enorm (hf := by pw_aesm) (f := f)]
  exact hsub

/-- Multiplication by a nonnegative real scales the `ℓ¹`-seminorm. -/
theorem ssu_eLpNorm_const_mul (r : ℝ) (hr : 0 ≤ r) (g : ℤ → ℂ) :
    eLpNorm (fun x : ℤ => (r : ℂ) * g x) 1 Measure.count
      = ENNReal.ofReal r * eLpNorm g 1 Measure.count := by
  rw [show (fun x : ℤ => (r : ℂ) * g x) = r • g from by
    funext x
    rw [Pi.smul_apply, Complex.real_smul]]
  rw [MeasureTheory.eLpNorm_const_smul, Real.enorm_eq_ofReal_abs, abs_of_nonneg hr]

/-! ## The bands do not interact: modulation invariance of the band sum -/

/-- **Pointwise bound for a finite combination of non-aliasing bands.**  If `Φ` is supported in
the arc `ℝ_{≤K}` and the frequencies of `S` are non-aliasing at scale `K`, then at each point `ξ`
at most one of the translates `Φ (· - α)` is non-zero, so a unimodular combination of the
single-frequency symbols is dominated by `iwSymbolSet S Φ`. -/
theorem ssu_symbol_sum_le (K : ℤ) (S : Finset Circ) {Φ : Circ → ℂ}
    (hsupp : SupportedInArc K Φ) (hNA : NonAliasing K S) (c : Circ → ℂ)
    (hc : ∀ α, ‖c α‖ ≤ 1) (ξ : Circ) :
    ‖∑ α ∈ S, c α * iwSymbolSet {α} Φ ξ‖ ≤ ‖iwSymbolSet S Φ ξ‖ := by
  classical
  set T : Finset Circ := S.filter (fun α => iwSymbolSet {α} Φ ξ ≠ 0) with hTdef
  have hmemT : ∀ α, α ∈ T ↔ α ∈ S ∧ iwSymbolSet {α} Φ ξ ≠ 0 := fun α => by
    rw [hTdef, Finset.mem_filter]
  have hTsub : T ⊆ S := fun α hα => ((hmemT α).mp hα).1
  have hzero : ∀ α ∈ S, α ∉ T → iwSymbolSet {α} Φ ξ = 0 := by
    intro α hα hαT
    by_contra hne
    exact hαT ((hmemT α).mpr ⟨hα, hne⟩)
  have huniq : ∀ a ∈ T, ∀ b ∈ T, a = b := by
    intro a ha b hb
    have haS : a ∈ S := hTsub ha
    have hbS : b ∈ S := hTsub hb
    have hane : iwSymbolSet {a} Φ ξ ≠ 0 := ((hmemT a).mp ha).2
    have hbne : iwSymbolSet {b} Φ ξ ≠ 0 := ((hmemT b).mp hb).2
    by_contra hne
    have hanePhi : Φ (ξ - a) ≠ 0 := by simpa [iwSymbolSet] using hane
    have hbnePhi : Φ (ξ - b) ≠ 0 := by simpa [iwSymbolSet] using hbne
    obtain ⟨θ, hθ, hθξ⟩ := hsupp (ξ - a) hanePhi
    obtain ⟨θ2, hθ2, hθ2ξ⟩ := hsupp (ξ - b) hbnePhi
    have heq : a + (θ : Circ) = b + (θ2 : Circ) := by rw [hθξ, hθ2ξ]; abel
    exact hne (hNA a haS b hbS θ hθ θ2 hθ2 heq).1
  have hSsum : iwSymbolSet S Φ ξ = ∑ α ∈ T, iwSymbolSet {α} Φ ξ := by
    rw [iwSymbolSet_singletons_apply]
    exact (Finset.sum_subset hTsub hzero).symm
  have hLsum : (∑ α ∈ S, c α * iwSymbolSet {α} Φ ξ)
      = ∑ α ∈ T, c α * iwSymbolSet {α} Φ ξ :=
    (Finset.sum_subset hTsub (fun α hα hαT => by rw [hzero α hα hαT, mul_zero])).symm
  rcases T.eq_empty_or_nonempty with hT0 | ⟨α0, hα0⟩
  · have hS0 : iwSymbolSet S Φ ξ = 0 := by rw [hSsum, hT0, Finset.sum_empty]
    have hL0 : (∑ α ∈ S, c α * iwSymbolSet {α} Φ ξ) = 0 := by
      rw [hLsum, hT0, Finset.sum_empty]
    rw [hL0, hS0]
  · have hTeq : T = {α0} :=
      Finset.eq_singleton_iff_unique_mem.mpr ⟨hα0, fun x hx => huniq x hx α0 hα0⟩
    have hS1 : iwSymbolSet S Φ ξ = iwSymbolSet {α0} Φ ξ := by
      rw [hSsum, hTeq, Finset.sum_singleton]
    have hL1 : (∑ α ∈ S, c α * iwSymbolSet {α} Φ ξ)
        = c α0 * iwSymbolSet {α0} Φ ξ := by
      rw [hLsum, hTeq, Finset.sum_singleton]
    rw [hL1, hS1, norm_mul]
    calc ‖c α0‖ * ‖iwSymbolSet {α0} Φ ξ‖ ≤ 1 * ‖iwSymbolSet {α0} Φ ξ‖ :=
          mul_le_mul_of_nonneg_right (hc α0) (norm_nonneg _)
      _ = ‖iwSymbolSet {α0} Φ ξ‖ := one_mul _

/-- **The modulated band sum has the `ℓ²` norm of the full multiplier.**  A unimodular
combination of the single-frequency bands of `iwOpSet S Φ` has `ℓ²` norm at most that of
`iwOpSet S Φ`, because the bands are pairwise orthogonal (disjointly supported spectra). -/
theorem ssu_modSum_eLpNorm_le (K : ℤ) (S : Finset Circ) {Φ : Circ → ℂ}
    (hΦ : MemLp Φ ⊤ circleMeasure) (hsupp : SupportedInArc K Φ) (hNA : NonAliasing K S)
    (F : L2Z) (c : Circ → ℂ) (hc : ∀ α, ‖c α‖ ≤ 1) :
    eLpNorm (fun x : ℤ => ∑ α ∈ S, c α * ⇑(iwOpSet {α} Φ
        (Work.Analysis.IWMultiplier.memLp_iwSymbolSet {α} hΦ) F) x) 2 Measure.count
      ≤ eLpNorm (⇑(iwOpSet S Φ
          (Work.Analysis.IWMultiplier.memLp_iwSymbolSet S hΦ) F)) 2 Measure.count := by
  classical
  set D : L2Z := ∑ α ∈ S, c α • (iwOpSet {α} Φ
      (Work.Analysis.IWMultiplier.memLp_iwSymbolSet {α} hΦ) F) with hD
  have hcoeD : ⇑D =ᵐ[Measure.count]
      (fun x : ℤ => ∑ α ∈ S, c α * ⇑(iwOpSet {α} Φ
        (Work.Analysis.IWMultiplier.memLp_iwSymbolSet {α} hΦ) F) x) := by
    filter_upwards with x
    rw [hD, lp.coeFn_sum, Finset.sum_apply]
    exact Finset.sum_congr rfl (fun α _ => by
      rw [lp.coeFn_smul, Pi.smul_apply, smul_eq_mul])
  have hFZ : ⇑(fourierZ D) =ᵐ[circleMeasure]
      (fun ξ : Circ => ∑ α ∈ S, c α * (iwSymbolSet {α} Φ ξ * ⇑(fourierZ F) ξ)) := by
    have hmap : fourierZ D = ∑ α ∈ S, c α • fourierZ (iwOpSet {α} Φ
        (Work.Analysis.IWMultiplier.memLp_iwSymbolSet {α} hΦ) F) := by
      rw [hD, map_sum]
      exact Finset.sum_congr rfl (fun α _ => by rw [map_smul])
    have hall : ∀ᵐ ξ ∂circleMeasure, ∀ α ∈ S,
        ⇑(c α • fourierZ (iwOpSet {α} Φ
          (Work.Analysis.IWMultiplier.memLp_iwSymbolSet {α} hΦ) F)) ξ
          = c α * (iwSymbolSet {α} Φ ξ * ⇑(fourierZ F) ξ) := by
      rw [Filter.eventually_all_finset]
      intro α _
      filter_upwards [Lp.coeFn_smul (c α) (fourierZ (iwOpSet {α} Φ
        (Work.Analysis.IWMultiplier.memLp_iwSymbolSet {α} hΦ) F)),
        shiftMod_ae_fourierZ_single {α} hΦ F] with ξ h1ξ h2ξ
      rw [h1ξ]
      simp only [Pi.smul_apply, smul_eq_mul, h2ξ]
    rw [hmap]
    filter_upwards [Lp.coeFn_finsetSum S (fun α : Circ => c α • fourierZ (iwOpSet {α} Φ
      (Work.Analysis.IWMultiplier.memLp_iwSymbolSet {α} hΦ) F)), hall] with ξ h1 h2
    rw [h1, Finset.sum_apply]
    exact Finset.sum_congr rfl (fun α hαS => h2 α hαS)
  have hDnorm : eLpNorm ⇑(fourierZ D) 2 circleMeasure = ‖D‖ₑ := by
    rw [← Lp.enorm_def (fourierZ D), ← ofReal_norm, ← ofReal_norm, fourierZ.norm_map D]
  have hSnorm : eLpNorm ⇑(fourierZ (iwOpSet S Φ
        (Work.Analysis.IWMultiplier.memLp_iwSymbolSet S hΦ) F)) 2 circleMeasure
      = ‖iwOpSet S Φ (Work.Analysis.IWMultiplier.memLp_iwSymbolSet S hΦ) F‖ₑ := by
    rw [← Lp.enorm_def (fourierZ (iwOpSet S Φ
        (Work.Analysis.IWMultiplier.memLp_iwSymbolSet S hΦ) F)),
      ← ofReal_norm, ← ofReal_norm,
      fourierZ.norm_map (iwOpSet S Φ (Work.Analysis.IWMultiplier.memLp_iwSymbolSet S hΦ) F)]
  have hD2 : eLpNorm ⇑D 2 Measure.count = eLpNorm ⇑(fourierZ D) 2 circleMeasure :=
    (enorm_lp_count D).trans hDnorm.symm
  have hS2 : eLpNorm (⇑(iwOpSet S Φ
        (Work.Analysis.IWMultiplier.memLp_iwSymbolSet S hΦ) F)) 2 Measure.count
      = eLpNorm ⇑(fourierZ (iwOpSet S Φ
          (Work.Analysis.IWMultiplier.memLp_iwSymbolSet S hΦ) F)) 2 circleMeasure :=
    (enorm_lp_count (iwOpSet S Φ (Work.Analysis.IWMultiplier.memLp_iwSymbolSet S hΦ) F)).trans
      hSnorm.symm
  rw [← eLpNorm_congr_ae hcoeD, hD2, hS2]
  refine MeasureTheory.eLpNorm_mono_ae (hf := by pw_aesm) ?_
  filter_upwards [hFZ, shiftMod_ae_fourierZ_single S hΦ F] with ξ h1 h2
  rw [h1, h2]
  have hfac : (∑ α ∈ S, c α * (iwSymbolSet {α} Φ ξ * ⇑(fourierZ F) ξ))
      = (∑ α ∈ S, c α * iwSymbolSet {α} Φ ξ) * ⇑(fourierZ F) ξ := by
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl (fun α _ => by ring)
  rw [hfac]
  simp only [norm_mul]
  exact mul_le_mul_of_nonneg_right (ssu_symbol_sum_le K S hsupp hNA c hc ξ) (norm_nonneg _)

/-! ## The algebraic rearrangement of the coefficients -/

/-- The double frequency sum of the band coefficients rearranges into the window average of the
products of the band sums (Fubini for finite sums, plus distributivity). -/
theorem ssu_coeff_rearrange (c : ℂ) (S₁ S₂ : Finset Circ) (s : Finset ℕ)
    (w₁ w₂ : ℕ → Circ → ℂ) (u v : Circ → ℂ) :
    (∑ α ∈ S₁, ∑ β ∈ S₂, (c * ∑ n ∈ s, w₁ n α * w₂ n β) * u α * v β)
      = c * ∑ n ∈ s, (∑ α ∈ S₁, w₁ n α * u α) * (∑ β ∈ S₂, w₂ n β * v β) := by
  have h1 : (∑ α ∈ S₁, ∑ β ∈ S₂, (c * ∑ n ∈ s, w₁ n α * w₂ n β) * u α * v β)
      = c * ∑ α ∈ S₁, ∑ β ∈ S₂, (∑ n ∈ s, w₁ n α * w₂ n β) * u α * v β := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun α _ => ?_)
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun β _ => by ring)
  have h2 : (∑ α ∈ S₁, ∑ β ∈ S₂, (∑ n ∈ s, w₁ n α * w₂ n β) * u α * v β)
      = ∑ α ∈ S₁, ∑ β ∈ S₂, ∑ n ∈ s, w₁ n α * w₂ n β * u α * v β := by
    refine Finset.sum_congr rfl (fun α _ => Finset.sum_congr rfl (fun β _ => ?_))
    rw [Finset.sum_mul, Finset.sum_mul]
  have h3 : (∑ α ∈ S₁, ∑ β ∈ S₂, ∑ n ∈ s, w₁ n α * w₂ n β * u α * v β)
      = ∑ n ∈ s, ∑ α ∈ S₁, ∑ β ∈ S₂, w₁ n α * w₂ n β * u α * v β := by
    rw [show (∑ α ∈ S₁, ∑ β ∈ S₂, ∑ n ∈ s, w₁ n α * w₂ n β * u α * v β)
        = ∑ α ∈ S₁, ∑ n ∈ s, ∑ β ∈ S₂, w₁ n α * w₂ n β * u α * v β from
      Finset.sum_congr rfl (fun α _ => Finset.sum_comm)]
    exact Finset.sum_comm
  have h4 : (∑ n ∈ s, ∑ α ∈ S₁, ∑ β ∈ S₂, w₁ n α * w₂ n β * u α * v β)
      = ∑ n ∈ s, (∑ α ∈ S₁, w₁ n α * u α) * (∑ β ∈ S₂, w₂ n β * v β) := by
    refine Finset.sum_congr rfl (fun n _ => ?_)
    rw [Finset.sum_mul_sum]
    exact Finset.sum_congr rfl (fun α _ => Finset.sum_congr rfl (fun β _ => by ring))
  rw [h1, h2, h3, h4]

/-! ## The window arithmetic -/

/-- The window average of the two error weights is dominated by `ssuErr`. -/
theorem ssu_window_bound (P : Polynomial ℤ) (u N : ℕ) (hN : 1 ≤ N) :
    ((N : ℝ)⁻¹) * (∑ n ∈ Finset.Ioc (N / 2) N,
        (2 * Real.pi * |(n : ℝ)| * (2 : ℝ) ^ (-(3 * (u : ℤ)))
          + 2 * Real.pi * |((P.eval (n : ℤ) : ℤ) : ℝ)|
              * (2 : ℝ) ^ (-(3 * (P.natDegree : ℤ) * (u : ℤ)))))
      ≤ ssuErr P u N := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hcard : (((Finset.Ioc (N / 2) N).card : ℕ) : ℝ) ≤ (N : ℝ) := by
    rw [Nat.card_Ioc]
    exact_mod_cast (Nat.sub_le N (N / 2))
  have hs1 : (∑ n ∈ Finset.Ioc (N / 2) N, |(n : ℝ)|) ≤ (N : ℝ) * (N : ℝ) := by
    have h1 : ∀ n ∈ Finset.Ioc (N / 2) N, |(n : ℝ)| ≤ (N : ℝ) := by
      intro n hn
      rw [abs_of_nonneg (Nat.cast_nonneg n)]
      exact_mod_cast (Finset.mem_Ioc.mp hn).2
    refine (Finset.sum_le_sum h1).trans ?_
    rw [Finset.sum_const, nsmul_eq_mul]
    exact mul_le_mul_of_nonneg_right hcard (Nat.cast_nonneg N)
  have hs2 : (∑ n ∈ Finset.Ioc (N / 2) N, |((P.eval (n : ℤ) : ℤ) : ℝ)|)
      ≤ (N : ℝ) * (ssuPc P * (N : ℝ) ^ P.natDegree) := by
    have h1 : ∀ n ∈ Finset.Ioc (N / 2) N, |((P.eval (n : ℤ) : ℤ) : ℝ)|
        ≤ ssuPc P * (N : ℝ) ^ P.natDegree := fun n hn =>
      ssuPc_eval_bound P N n hN (Finset.mem_Ioc.mp hn).2
    refine (Finset.sum_le_sum h1).trans ?_
    rw [Finset.sum_const, nsmul_eq_mul]
    exact mul_le_mul_of_nonneg_right hcard
      (mul_nonneg (ssuPc_nonneg P) (pow_nonneg (Nat.cast_nonneg N) _))
  have e1 : (∑ n ∈ Finset.Ioc (N / 2) N,
        2 * Real.pi * |(n : ℝ)| * (2 : ℝ) ^ (-(3 * (u : ℤ))))
      = 2 * Real.pi * (2 : ℝ) ^ (-(3 * (u : ℤ)))
          * (∑ n ∈ Finset.Ioc (N / 2) N, |(n : ℝ)|) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun n _ => by ring)
  have e2 : (∑ n ∈ Finset.Ioc (N / 2) N,
        2 * Real.pi * |((P.eval (n : ℤ) : ℤ) : ℝ)|
          * (2 : ℝ) ^ (-(3 * (P.natDegree : ℤ) * (u : ℤ))))
      = 2 * Real.pi * (2 : ℝ) ^ (-(3 * (P.natDegree : ℤ) * (u : ℤ)))
          * (∑ n ∈ Finset.Ioc (N / 2) N, |((P.eval (n : ℤ) : ℤ) : ℝ)|) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun n _ => by ring)
  rw [Finset.sum_add_distrib, e1, e2]
  have hfac : ((N : ℝ)⁻¹)
        * (2 * Real.pi * (2 : ℝ) ^ (-(3 * (u : ℤ)))
              * (∑ n ∈ Finset.Ioc (N / 2) N, |(n : ℝ)|)
          + 2 * Real.pi * (2 : ℝ) ^ (-(3 * (P.natDegree : ℤ) * (u : ℤ)))
              * (∑ n ∈ Finset.Ioc (N / 2) N, |((P.eval (n : ℤ) : ℤ) : ℝ)|))
      = 2 * Real.pi * (2 : ℝ) ^ (-(3 * (u : ℤ)))
          * (((N : ℝ)⁻¹) * (∑ n ∈ Finset.Ioc (N / 2) N, |(n : ℝ)|))
        + 2 * Real.pi * (2 : ℝ) ^ (-(3 * (P.natDegree : ℤ) * (u : ℤ)))
          * (((N : ℝ)⁻¹) * (∑ n ∈ Finset.Ioc (N / 2) N, |((P.eval (n : ℤ) : ℤ) : ℝ)|)) := by
    ring
  rw [hfac]
  have hNin : ((N : ℝ)⁻¹) * (N : ℝ) = 1 := inv_mul_cancel₀ (ne_of_gt hNpos)
  have f1 : ((N : ℝ)⁻¹) * (∑ n ∈ Finset.Ioc (N / 2) N, |(n : ℝ)|) ≤ (N : ℝ) := by
    have h := mul_le_mul_of_nonneg_left hs1 (inv_nonneg.mpr (Nat.cast_nonneg N))
    calc ((N : ℝ)⁻¹) * (∑ n ∈ Finset.Ioc (N / 2) N, |(n : ℝ)|)
        ≤ ((N : ℝ)⁻¹) * ((N : ℝ) * (N : ℝ)) := h
      _ = (N : ℝ) := by rw [← mul_assoc, hNin, one_mul]
  have f2 : ((N : ℝ)⁻¹) * (∑ n ∈ Finset.Ioc (N / 2) N, |((P.eval (n : ℤ) : ℤ) : ℝ)|)
      ≤ ssuPc P * (N : ℝ) ^ P.natDegree := by
    have h := mul_le_mul_of_nonneg_left hs2 (inv_nonneg.mpr (Nat.cast_nonneg N))
    calc ((N : ℝ)⁻¹) * (∑ n ∈ Finset.Ioc (N / 2) N, |((P.eval (n : ℤ) : ℤ) : ℝ)|)
        ≤ ((N : ℝ)⁻¹) * ((N : ℝ) * (ssuPc P * (N : ℝ) ^ P.natDegree)) := h
      _ = ssuPc P * (N : ℝ) ^ P.natDegree := by rw [← mul_assoc, hNin, one_mul]
  have g1 : 0 ≤ 2 * Real.pi * (2 : ℝ) ^ (-(3 * (u : ℤ))) := by positivity
  have g2 : 0 ≤ 2 * Real.pi * (2 : ℝ) ^ (-(3 * (P.natDegree : ℤ) * (u : ℤ))) := by positivity
  have k1 := mul_le_mul_of_nonneg_left f1 g1
  have k2 := mul_le_mul_of_nonneg_left f2 g2
  have hfin : 2 * Real.pi * (2 : ℝ) ^ (-(3 * (u : ℤ))) * (N : ℝ)
        + 2 * Real.pi * (2 : ℝ) ^ (-(3 * (P.natDegree : ℤ) * (u : ℤ)))
            * (ssuPc P * (N : ℝ) ^ P.natDegree) = ssuErr P u N := by
    rw [ssuErr]
    ring
  have hsum_le := add_le_add k1 k2
  rw [hfin] at hsum_le
  exact hsum_le

/-- **The band realisation of the halved average.** -/
theorem ssuAverageModel (ρ : ℝ) (P : Polynomial ℤ) (hd : 2 ≤ P.natDegree)
    (l₁ l₂ u N : ℕ) (φ ψ : ℝ → ℂ) (f g : ℤ → ℂ)
    (hN : 1 ≤ N) (hu : 1 ≤ u)
    (hΦ : MemLp (periodize φ) ⊤ circleMeasure)
    (hΨ : MemLp (periodize ψ) ⊤ circleMeasure)
    (hφ : ∀ ξ : ℝ, φ ξ ≠ 0 → |ξ| ≤ (2 : ℝ) ^ (-(3 * (u : ℤ))))
    (hψ : ∀ ξ : ℝ, ψ ξ ≠ 0 → |ξ| ≤ (2 : ℝ) ^ (-(3 * (P.natDegree : ℤ) * (u : ℤ))))
    (hNA₁ : NonAliasing (-(3 * (u : ℤ))) (Work.KMTAreas.A7.diffFreqs ρ l₁))
    (hNA₂ : NonAliasing (-(3 * ((P.natDegree : ℤ) * (u : ℤ)))) (Work.KMTAreas.A7.diffFreqs ρ l₂))
    (hf : MemLp f 2 Measure.count) (hg : MemLp g 2 Measure.count) :
    eLpNorm (fun x : ℤ =>
        Work.KMTPlan.A6.ssuAvg P N (Work.KMTAreas.A7.Tm ρ l₁ φ f)
            (Work.KMTAreas.A7.Tm ρ l₂ ψ g) x
        - ∑ α ∈ Work.KMTAreas.A7.diffFreqs ρ l₁,
            ∑ β ∈ Work.KMTAreas.A7.diffFreqs ρ l₂,
              Work.KMTPlan.A6.ssuCoeff P N α β
                * iwConv {α} (periodize φ) f x * iwConv {β} (periodize ψ) g x)
      1 Measure.count
      ≤ ENNReal.ofReal (Work.KMTPlan.A6.ssuErr P u N)
          * eLpNorm (Work.KMTAreas.A7.Tm ρ l₁ φ f) 2 Measure.count
          * eLpNorm (Work.KMTAreas.A7.Tm ρ l₂ ψ g) 2 Measure.count := by
  classical
  set S₁ : Finset Circ := Work.KMTAreas.A7.diffFreqs ρ l₁ with hS₁
  set S₂ : Finset Circ := Work.KMTAreas.A7.diffFreqs ρ l₂ with hS₂
  set Φ : Circ → ℂ := periodize φ with hΦeq
  set Ψ : Circ → ℂ := periodize ψ with hΨeq
  set K₁ : ℤ := -(3 * (u : ℤ)) with hK₁
  set K₂ : ℤ := -(3 * ((P.natDegree : ℤ) * (u : ℤ))) with hK₂
  set F : L2Z := toL2Z hf with hFeq
  set G : L2Z := toL2Z hg with hGeq
  set A : ℤ → ℂ := Work.KMTAreas.A7.Tm ρ l₁ φ f with hAeq
  set B : ℤ → ℂ := Work.KMTAreas.A7.Tm ρ l₂ ψ g with hBeq
  set s : Finset ℕ := Finset.Ioc (N / 2) N with hs
  set EA : ENNReal := eLpNorm A 2 Measure.count with hEA
  set EB : ENNReal := eLpNorm B 2 Measure.count with hEB
  have hΦm : MemLp Φ ⊤ circleMeasure := by simpa only [hΦeq] using hΦ
  have hΨm : MemLp Ψ ⊤ circleMeasure := by simpa only [hΨeq] using hΨ
  have hsupp₁ : SupportedInArc K₁ Φ := by
    rw [hK₁, hΦeq]
    exact supportedInArc_periodize_of_support u hu φ hφ
  have hsupp₂ : SupportedInArc K₂ Ψ := by
    have h0 : SupportedInArc (-(3 * ↑(P.natDegree * u))) (periodize ψ) :=
      supportedInArc_periodize_of_support (P.natDegree * u)
        (Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))) ψ (by
          intro ξ hξ
          have h := hψ ξ hξ
          simpa only [Nat.cast_mul, mul_assoc] using h)
    simpa [hK₂, hΨeq, Nat.cast_mul, mul_assoc] using h0
  have hNA₁' : NonAliasing K₁ S₁ := by rw [hK₁, hS₁]; exact hNA₁
  have hNA₂' : NonAliasing K₂ S₂ := by rw [hK₂, hS₂]; exact hNA₂
  have hFcoe : f = ⇑F := by rw [hFeq]; exact (toL2Z_coe hf).symm
  have hGcoe : g = ⇑G := by rw [hGeq]; exact (toL2Z_coe hg).symm
  have hAf : A = ⇑(iwOpSet S₁ Φ (Work.Analysis.IWMultiplier.memLp_iwSymbolSet S₁ hΦm) F) := by
    rw [hAeq, Work.KMTAreas.A7.Tm, ← hS₁, ← hΦeq, hFcoe]
    exact iwConvEqIwOpSetMemlp _ _
  have hBf : B = ⇑(iwOpSet S₂ Ψ (Work.Analysis.IWMultiplier.memLp_iwSymbolSet S₂ hΨm) G) := by
    rw [hBeq, Work.KMTAreas.A7.Tm, ← hS₂, ← hΨeq, hGcoe]
    exact iwConvEqIwOpSetMemlp _ _
  have huα : ∀ α : Circ, iwConv {α} Φ f
      = ⇑(iwOpSet {α} Φ (Work.Analysis.IWMultiplier.memLp_iwSymbolSet {α} hΦm) F) := by
    intro α
    rw [hFcoe]
    exact iwConvEqIwOpSetMemlp _ _
  have hvβ : ∀ β : Circ, iwConv {β} Ψ g
      = ⇑(iwOpSet {β} Ψ (Work.Analysis.IWMultiplier.memLp_iwSymbolSet {β} hΨm) G) := by
    intro β
    rw [hGcoe]
    exact iwConvEqIwOpSetMemlp _ _
  -- the shift–modulation estimates
  have hdevA : ∀ n : ℤ,
      eLpNorm (fun x : ℤ => ⇑(iwOpSet S₁ Φ
            (Work.Analysis.IWMultiplier.memLp_iwSymbolSet S₁ hΦm) F) (x - n)
          - ∑ α ∈ S₁, fourier (T := 1) n α *
              ⇑(iwOpSet {α} Φ (Work.Analysis.IWMultiplier.memLp_iwSymbolSet {α} hΦm) F) x)
          2 Measure.count
        ≤ ENNReal.ofReal (2 * Real.pi * |(n : ℝ)| * (2 : ℝ) ^ K₁)
            * eLpNorm (⇑(iwOpSet S₁ Φ
                (Work.Analysis.IWMultiplier.memLp_iwSymbolSet S₁ hΦm) F)) 2 Measure.count := by
    intro n
    have h := shift_modulation_le K₁ S₁ hΦm hsupp₁ hNA₁' F (-n)
    simp only [neg_neg] at h
    simpa [sub_eq_add_neg, abs_neg] using h
  have hdevB : ∀ m : ℤ,
      eLpNorm (fun x : ℤ => ⇑(iwOpSet S₂ Ψ
            (Work.Analysis.IWMultiplier.memLp_iwSymbolSet S₂ hΨm) G) (x - m)
          - ∑ β ∈ S₂, fourier (T := 1) m β *
              ⇑(iwOpSet {β} Ψ (Work.Analysis.IWMultiplier.memLp_iwSymbolSet {β} hΨm) G) x)
          2 Measure.count
        ≤ ENNReal.ofReal (2 * Real.pi * |(m : ℝ)| * (2 : ℝ) ^ K₂)
            * eLpNorm (⇑(iwOpSet S₂ Ψ
                (Work.Analysis.IWMultiplier.memLp_iwSymbolSet S₂ hΨm) G)) 2 Measure.count := by
    intro m
    have h := shift_modulation_le K₂ S₂ hΨm hsupp₂ hNA₂' G (-m)
    simp only [neg_neg] at h
    simpa [sub_eq_add_neg, abs_neg] using h
  -- the objects of the decomposition
  set modA : ℕ → ℤ → ℂ := fun n x =>
    ∑ α ∈ S₁, fourier (T := 1) (n : ℤ) α * iwConv {α} Φ f x with hmodAdef
  set modB : ℕ → ℤ → ℂ := fun n x =>
    ∑ β ∈ S₂, fourier (T := 1) (P.eval (n : ℤ)) β * iwConv {β} Ψ g x with hmodBdef
  set devA : ℕ → ℤ → ℂ := fun n x => A (x - (n : ℤ)) - modA n x with hdevAdef
  set devB : ℕ → ℤ → ℂ := fun n x => B (x - P.eval (n : ℤ)) - modB n x with hdevBdef
  set Bsh : ℕ → ℤ → ℂ := fun n x => B (x - P.eval (n : ℤ)) with hBshdef
  have hdevA_bd : ∀ n : ℕ,
      eLpNorm (devA n) 2 Measure.count
        ≤ ENNReal.ofReal (2 * Real.pi * |((n : ℤ) : ℝ)| * (2 : ℝ) ^ K₁) * EA := by
    intro n
    have hfun : devA n = fun x : ℤ => ⇑(iwOpSet S₁ Φ
          (Work.Analysis.IWMultiplier.memLp_iwSymbolSet S₁ hΦm) F) (x - (n : ℤ))
        - ∑ α ∈ S₁, fourier (T := 1) (n : ℤ) α *
            ⇑(iwOpSet {α} Φ (Work.Analysis.IWMultiplier.memLp_iwSymbolSet {α} hΦm) F) x := by
      funext x
      simp only [hdevAdef, hmodAdef, hAf, huα]
    rw [hfun, hEA, hAf]
    exact hdevA (n : ℤ)
  have hdevB_bd : ∀ n : ℕ,
      eLpNorm (devB n) 2 Measure.count
        ≤ ENNReal.ofReal (2 * Real.pi * |((P.eval (n : ℤ) : ℤ) : ℝ)| * (2 : ℝ) ^ K₂) * EB := by
    intro n
    have hfun : devB n = fun x : ℤ => ⇑(iwOpSet S₂ Ψ
          (Work.Analysis.IWMultiplier.memLp_iwSymbolSet S₂ hΨm) G) (x - P.eval (n : ℤ))
        - ∑ β ∈ S₂, fourier (T := 1) (P.eval (n : ℤ)) β *
            ⇑(iwOpSet {β} Ψ (Work.Analysis.IWMultiplier.memLp_iwSymbolSet {β} hΨm) G) x := by
      funext x
      simp only [hdevBdef, hmodBdef, hBf, hvβ]
    rw [hfun, hEB, hBf]
    exact hdevB (P.eval (n : ℤ))
  have hmodA_bd : ∀ n : ℕ, eLpNorm (modA n) 2 Measure.count ≤ EA := by
    intro n
    have hfun : modA n = fun x : ℤ => ∑ α ∈ S₁, fourier (T := 1) (n : ℤ) α *
        ⇑(iwOpSet {α} Φ (Work.Analysis.IWMultiplier.memLp_iwSymbolSet {α} hΦm) F) x := by
      funext x
      simp only [hmodAdef, huα]
    rw [hfun, hEA, hAf]
    exact ssu_modSum_eLpNorm_le K₁ S₁ hΦm hsupp₁ hNA₁' F
      (fun α => fourier (T := 1) (n : ℤ) α)
      (fun α => le_of_eq (shiftMod_norm_fourier_apply (T := 1) (n : ℤ) α))
  have hmodB_bd : ∀ n : ℕ, eLpNorm (modB n) 2 Measure.count ≤ EB := by
    intro n
    have hfun : modB n = fun x : ℤ => ∑ β ∈ S₂, fourier (T := 1) (P.eval (n : ℤ)) β *
        ⇑(iwOpSet {β} Ψ (Work.Analysis.IWMultiplier.memLp_iwSymbolSet {β} hΨm) G) x := by
      funext x
      simp only [hmodBdef, hvβ]
    rw [hfun, hEB, hBf]
    exact ssu_modSum_eLpNorm_le K₂ S₂ hΨm hsupp₂ hNA₂' G
      (fun β => fourier (T := 1) (P.eval (n : ℤ)) β)
      (fun β => le_of_eq (shiftMod_norm_fourier_apply (T := 1) (P.eval (n : ℤ)) β))
  have hBsh_bd : ∀ n : ℕ, eLpNorm (Bsh n) 2 Measure.count = EB := by
    intro n
    have hfun : Bsh n = fun x : ℤ => B (x - P.eval (n : ℤ)) := by
      funext x; simp only [hBshdef]
    rw [hfun, hEB]
    exact ssu_eLpNorm_sub_right B (P.eval (n : ℤ))
  -- the pointwise identity
  have hcmul : ((N : ℂ))⁻¹ = (((N : ℝ)⁻¹ : ℝ) : ℂ) := by
    rw [← Complex.ofReal_natCast, ← Complex.ofReal_inv]
  have hkey : ∀ x : ℤ,
      (ssuAvg P N A B x
        - ∑ α ∈ S₁, ∑ β ∈ S₂, ssuCoeff P N α β * iwConv {α} Φ f x * iwConv {β} Ψ g x)
      = (((N : ℝ)⁻¹ : ℝ) : ℂ) * ∑ n ∈ s,
          (devA n x * Bsh n x + modA n x * devB n x) := by
    intro x
    have hmodel :
        (∑ α ∈ S₁, ∑ β ∈ S₂, ssuCoeff P N α β * iwConv {α} Φ f x * iwConv {β} Ψ g x)
        = (((N : ℝ)⁻¹ : ℝ) : ℂ) * ∑ n ∈ s, modA n x * modB n x := by
      rw [show (∑ α ∈ S₁, ∑ β ∈ S₂, ssuCoeff P N α β * iwConv {α} Φ f x * iwConv {β} Ψ g x)
          = (∑ α ∈ S₁, ∑ β ∈ S₂, ((((N : ℝ)⁻¹ : ℝ) : ℂ)
                * ∑ n ∈ s, fourier (T := 1) (n : ℤ) α
                    * fourier (T := 1) (P.eval (n : ℤ)) β)
              * iwConv {α} Φ f x * iwConv {β} Ψ g x) from by
            refine Finset.sum_congr rfl (fun α _ => Finset.sum_congr rfl (fun β _ => ?_))
            rw [ssuCoeff, hcmul]]
      rw [ssu_coeff_rearrange]
    have havg : ssuAvg P N A B x
        = (((N : ℝ)⁻¹ : ℝ) : ℂ)
            * ∑ n ∈ s, A (x - (n : ℤ)) * B (x - P.eval (n : ℤ)) := by
      simp only [ssuAvg, hs]
    rw [hmodel, havg, ← mul_sub]
    congr 1
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun n _ => ?_)
    simp only [hdevAdef, hdevBdef, hBshdef]
    ring
  -- the two sums
  have hsum1 : eLpNorm (fun x : ℤ => ∑ n ∈ s, devA n x * Bsh n x) 1 Measure.count
      ≤ (∑ n ∈ s, ENNReal.ofReal (2 * Real.pi * |((n : ℤ) : ℝ)| * (2 : ℝ) ^ K₁))
          * EA * EB := by
    have h := ssu_sum_mul_le (s := s) (g := devA) (h := Bsh)
      (εg := fun n => ENNReal.ofReal (2 * Real.pi * |((n : ℤ) : ℝ)| * (2 : ℝ) ^ K₁) * EA)
      (εh := fun _ => EB)
      (fun n _ => hdevA_bd n) (fun n _ => by rw [hBsh_bd n])
    refine h.trans (le_of_eq ?_)
    rw [← Finset.sum_mul, ← Finset.sum_mul]
  have hsum2 : eLpNorm (fun x : ℤ => ∑ n ∈ s, modA n x * devB n x) 1 Measure.count
      ≤ (∑ n ∈ s, ENNReal.ofReal (2 * Real.pi * |((P.eval (n : ℤ) : ℤ) : ℝ)| * (2 : ℝ) ^ K₂))
          * EA * EB := by
    have h := ssu_sum_mul_le (s := s) (g := modA) (h := devB)
      (εg := fun _ => EA)
      (εh := fun n => ENNReal.ofReal (2 * Real.pi * |((P.eval (n : ℤ) : ℤ) : ℝ)|
        * (2 : ℝ) ^ K₂) * EB)
      (fun n _ => hmodA_bd n) (fun n _ => hdevB_bd n)
    refine h.trans (le_of_eq ?_)
    rw [← Finset.mul_sum, ← Finset.sum_mul]
    ac_rfl
  -- assembly
  rw [show (fun x : ℤ => ssuAvg P N A B x
        - ∑ α ∈ S₁, ∑ β ∈ S₂, ssuCoeff P N α β * iwConv {α} Φ f x * iwConv {β} Ψ g x)
      = fun x : ℤ => (((N : ℝ)⁻¹ : ℝ) : ℂ) * ∑ n ∈ s,
          (devA n x * Bsh n x + modA n x * devB n x) from funext hkey]
  have hsplit : (fun x : ℤ => ∑ n ∈ s, (devA n x * Bsh n x + modA n x * devB n x))
      = (fun x : ℤ => ∑ n ∈ s, devA n x * Bsh n x)
        + (fun x : ℤ => ∑ n ∈ s, modA n x * devB n x) := by
    funext x
    simp only [Pi.add_apply, Finset.sum_add_distrib]
  have hAinv : 0 ≤ (N : ℝ)⁻¹ := inv_nonneg.mpr (Nat.cast_nonneg N)
  calc eLpNorm (fun x : ℤ => (((N : ℝ)⁻¹ : ℝ) : ℂ) * ∑ n ∈ s,
        (devA n x * Bsh n x + modA n x * devB n x)) 1 Measure.count
      = ENNReal.ofReal ((N : ℝ)⁻¹)
          * eLpNorm (fun x : ℤ => ∑ n ∈ s, (devA n x * Bsh n x + modA n x * devB n x))
              1 Measure.count := ssu_eLpNorm_const_mul _ hAinv _
    _ = ENNReal.ofReal ((N : ℝ)⁻¹)
          * eLpNorm ((fun x : ℤ => ∑ n ∈ s, devA n x * Bsh n x)
              + (fun x : ℤ => ∑ n ∈ s, modA n x * devB n x)) 1 Measure.count := by
          rw [hsplit]
    _ ≤ ENNReal.ofReal ((N : ℝ)⁻¹)
          * (eLpNorm (fun x : ℤ => ∑ n ∈ s, devA n x * Bsh n x) 1 Measure.count
            + eLpNorm (fun x : ℤ => ∑ n ∈ s, modA n x * devB n x) 1 Measure.count) := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          exact MeasureTheory.eLpNorm_add_le le_rfl
    _ ≤ ENNReal.ofReal ((N : ℝ)⁻¹)
          * ((∑ n ∈ s, ENNReal.ofReal (2 * Real.pi * |((n : ℤ) : ℝ)| * (2 : ℝ) ^ K₁))
              * EA * EB
            + (∑ n ∈ s, ENNReal.ofReal (2 * Real.pi * |((P.eval (n : ℤ) : ℤ) : ℝ)|
                * (2 : ℝ) ^ K₂)) * EA * EB) := by
          refine mul_le_mul_of_nonneg_left (add_le_add hsum1 hsum2) (by positivity)
    _ = ENNReal.ofReal (((N : ℝ)⁻¹) * (∑ n ∈ s,
            (2 * Real.pi * |(n : ℝ)| * (2 : ℝ) ^ (-(3 * (u : ℤ)))
              + 2 * Real.pi * |((P.eval (n : ℤ) : ℤ) : ℝ)|
                  * (2 : ℝ) ^ (-(3 * ((P.natDegree : ℤ) * (u : ℤ)))))))
          * EA * EB := by
          have hAn : ∀ n ∈ s, 0 ≤ 2 * Real.pi * |((n : ℤ) : ℝ)| * (2 : ℝ) ^ K₁ :=
            fun n _ => by positivity
          have hBn : ∀ n ∈ s, 0 ≤ 2 * Real.pi * |((P.eval (n : ℤ) : ℤ) : ℝ)|
              * (2 : ℝ) ^ K₂ := fun n _ => by positivity
          rw [← add_mul, ← add_mul,
            ← ENNReal.ofReal_sum_of_nonneg hAn, ← ENNReal.ofReal_sum_of_nonneg hBn,
            ← ENNReal.ofReal_add (Finset.sum_nonneg hAn) (Finset.sum_nonneg hBn),
            ← Finset.sum_add_distrib, hK₁, hK₂]
          simp only [mul_assoc, Int.cast_natCast]
          rw [ENNReal.ofReal_mul hAinv, mul_assoc]
    _ ≤ ENNReal.ofReal (ssuErr P u N) * EA * EB := by
          have hw : ((N : ℝ)⁻¹) * (∑ n ∈ s,
                (2 * Real.pi * |(n : ℝ)| * (2 : ℝ) ^ (-(3 * (u : ℤ)))
                  + 2 * Real.pi * |((P.eval (n : ℤ) : ℤ) : ℝ)|
                      * (2 : ℝ) ^ (-(3 * ((P.natDegree : ℤ) * (u : ℤ))))))
              ≤ ssuErr P u N := by
            simpa only [← hs, mul_assoc] using ssu_window_bound P u N hN
          exact mul_le_mul' (mul_le_mul' (ENNReal.ofReal_le_ofReal hw) le_rfl) le_rfl

end Work.KMTPlan.A6
