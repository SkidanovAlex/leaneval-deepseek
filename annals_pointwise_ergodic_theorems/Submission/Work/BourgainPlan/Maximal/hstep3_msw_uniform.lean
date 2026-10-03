import Mathlib
import Submission.Work.BourgainPlan.Maximal.hstep3_msw

namespace Work.BourgainPlan.Maximal

open MeasureTheory
open scoped ENNReal BigOperators
open Work.BourgainPlan.IonescuWainger
open Work.BourgainPlan.Thm52

noncomputable section

local notation "haarT" => (AddCircle.haarAddCircle (T := 1))

/-!
# The uniform-in-`S` form of the Magyar--Stein--Wainger step 3

`Maximal.hstep3_msw` proves Tao's step 3 (the symbol disposal) for a *fixed* family `S` of pairwise
coprime moduli; its constant is nevertheless built out of

* the Magyar--Stein--Wainger sampling constant `Cms(p)` of `msw_torsion_kernel` (`p = 2r`),
* the Marcinkiewicz--Zygmund constant `Cmz(p)` of `mz_square_function_lp` (`p = 2r`), and
* the factor `2 ^ k` of the strata inclusion--exclusion `lpL2_family_strata_incl_excl`,

so it does not depend on `S` or on `qmax` at all.  This file re-runs that proof chain with the
private auxiliary lemmas reproduced under `u_`-prefixed names (the originals are `private`), and
then hoists the constant out of the quantifiers, which is the form the MST assembly needs
(`MST_ROUTE.md` §7, item 3: the constant of `hstep3` has to be uniform in the level `N`).
-/
/-- The coefficient sequence of a circle function, in the corpus's convention
`j ↦ ∫ ψ · star (fourier j)`. -/
private noncomputable def u_psiCoeff (ψ : Circ → ℂ) : ℤ → ℂ :=
  fun j => ∫ ξ, ψ ξ * star (fourier j ξ) ∂haarT

/-! ## Auxiliary facts about the circle lifting and the torsion kernels -/

/-- `fourierCoeff` written with the corpus's convention. -/
private lemma u_fourierCoeff_eq_integral (ψ : Circ → ℂ) (j : ℤ) :
    fourierCoeff ψ j = u_psiCoeff ψ j := by
  rw [u_psiCoeff, fourierCoeff]
  refine integral_congr_ae (Filter.Eventually.of_forall (fun ξ => ?_))
  show fourier (-j) ξ • ψ ξ = ψ ξ * star (fourier j ξ)
  rw [smul_eq_mul, mul_comm, fourier_neg, starRingEnd_apply]

/-- **Parseval**: the Fourier coefficients of an a.e.-bounded circle function are
square-summable. -/
private lemma u_summable_sq_fourierCoeff {ψ : Circ → ℂ} (hψ : MemLp ψ ⊤ haarT) :
    Summable (fun j : ℤ => ‖fourierCoeff ψ j‖ ^ 2) := by
  have h2 : MemLp ψ 2 haarT := hψ.mono_exponent le_top
  have hcoef : fourierCoeff ((h2.toLp ψ : Lp ℂ 2 haarT) : Circ → ℂ) = fourierCoeff ψ :=
    fourierCoeff_congr_ae h2.coeFn_toLp
  have h := hasSum_sq_fourierCoeff (h2.toLp ψ)
  rw [hcoef] at h
  exact h.summable

/-- The corpus form of Parseval's identity. -/
private lemma u_summable_sq_kernel {ψ : Circ → ℂ} (hψ : MemLp ψ ⊤ haarT) :
    Summable (fun j : ℤ => ‖u_psiCoeff ψ j‖ ^ 2) :=
  (summable_congr (fun j => by rw [u_fourierCoeff_eq_integral])).mp (u_summable_sq_fourierCoeff hψ)

/-- The torsion kernel of a square-summable coefficient sequence is square-summable. -/
private lemma u_summable_sq_torsionKernel {B : Finset ℕ} {K : ℤ → ℂ}
    (hK : Summable (fun j : ℤ => ‖K j‖ ^ 2)) :
    Summable (fun j : ℤ => ‖torsionKernel B K j‖ ^ 2) := by
  refine Summable.of_nonneg_of_le (fun j => by positivity) (fun j => ?_)
    (hK.mul_left ((QA B : ℝ) ^ 2))
  rw [torsionKernel]
  by_cases h : (QA B : ℤ) ∣ j
  · rw [if_pos h, norm_mul, Complex.norm_natCast, mul_pow]
  · rw [if_neg h, mul_zero, norm_zero, zero_pow (by norm_num : (2:ℕ) ≠ 0)]
    positivity

/-- The single torsion multiplier, written as the convolution with the torsion kernel. -/
private lemma u_opArc_sigmaSubAFinset_eq_kernel {B : Finset ℕ} (ψ : Circ → ℂ)
    (hψ : MemLp ψ ⊤ haarT) (h : ℤ → ℂ) (hh : Memℓp h 2) (n : ℤ) :
    opArc ψ hψ (sigmaSubAFinset B) h hh n
      = ∑' j : ℤ, h j * torsionKernel B (u_psiCoeff ψ) (n - j) := by
  rw [opArc_eq_tsum_kernel ψ hψ (fun m => rfl) (sigmaSubAFinset B) h hh n]
  refine tsum_congr (fun j => ?_)
  congr 1
  rw [charSum_sigmaSubAFinset, torsionKernel]
  by_cases hd : (QA B : ℤ) ∣ (n - j)
  · rw [if_pos hd, if_pos hd]
    rfl
  · rw [if_neg hd, if_neg hd]; ring

/-! ## The Magyar–Stein–Wainger sampling principle for the lifted circle symbol -/

/-- **The MSW sampling principle applied to the fundamental-domain lift** `circleLift ψ`: for a
symbol `ψ` supported in the ball of radius `ε` with `ε · Q < 1/2`, whose `ℝ`-multiplier norm on
`Lᵖ` is at most `A`, the decimated (torsion) multiplier of `Q` is `ℓᵖ`-bounded with constant
`C · A` on finitely supported inputs. -/
private lemma u_msw_torsion_circleLift {p : ℝ} (hp : 1 < p) :
    ∃ C : ℝ, 0 < C ∧ ∀ {ψ : Circ → ℂ} (hψ : MemLp ψ ⊤ haarT) {ε A : ℝ} (hε : 0 < ε)
      (hA : 0 ≤ A) (hψsupp : ∀ ξ : Circ, ε < ‖ξ‖ → ψ ξ = 0) {Q : ℕ} (hQ : 1 ≤ Q)
      (hQε : ε * (Q : ℝ) < 1 / 2)
      (hMult : ∀ g : ℝ → ℂ, MeasureTheory.Integrable g →
        ∫⁻ x : ℝ, ‖FourierTransformInv.fourierInv
            (fun ξ : ℝ => circleLift ψ ξ * FourierTransform.fourier g ξ) x‖ₑ ^ p
          ∂MeasureTheory.volume
          ≤ ENNReal.ofReal (A ^ p) * ∫⁻ x : ℝ, ‖g x‖ₑ ^ p ∂MeasureTheory.volume)
      (s : Finset ℤ) (a : ℤ → ℂ) (ha : ∀ n, n ∉ s → a n = 0),
      ∫⁻ n : ℤ, ‖∑ k ∈ s, a k * decimatedKernel Q (circleLift ψ) (n - k)‖ₑ ^ p
          ∂MeasureTheory.Measure.count
        ≤ ENNReal.ofReal ((C * A) ^ p) * ∫⁻ n : ℤ, ‖a n‖ₑ ^ p ∂MeasureTheory.Measure.count := by
  obtain ⟨C, hC, hmsw⟩ := msw_torsion_kernel (p := p) hp
  refine ⟨C, hC, ?_⟩
  intro ψ hψ ε A hε hA hψsupp Q hQ hQε hMult s a ha
  have hQpos : (0:ℝ) < (Q : ℝ) := by
    have h1 : (1:ℝ) ≤ (Q : ℝ) := by exact_mod_cast hQ
    linarith
  have hεle : ε ≤ 1 / (2 * (Q : ℝ)) := by
    rw [le_div_iff₀ (by positivity)]
    linarith
  have hsupp : ∀ ξ : ℝ,
      ξ ∉ Set.Icc (-(1 / (2 * (Q : ℝ)))) (1 / (2 * (Q : ℝ))) → circleLift ψ ξ = 0 := by
    intro ξ hξ
    refine circleLift_eq_zero_of_support (a := ε) hψsupp ξ (fun hmem => hξ ?_)
    simp only [Set.mem_Icc] at hmem ⊢
    exact ⟨by linarith [hmem.1], by linarith [hmem.2]⟩
  have hOp : ∀ g : ℝ → ℂ, MeasureTheory.Integrable g →
      (∀ ξ : ℝ, ξ ∉ Set.Icc (-(1/2):ℝ) (1/2) → FourierTransform.fourier g ξ = 0) →
      ∫⁻ x : ℝ, ENNReal.ofReal ‖FourierTransformInv.fourierInv
          (fun ξ : ℝ => circleLift ψ ξ * FourierTransform.fourier g ξ) x‖ ^ p
        ∂MeasureTheory.volume
        ≤ ENNReal.ofReal (A ^ p) * ∫⁻ x : ℝ, ENNReal.ofReal ‖g x‖ ^ p ∂MeasureTheory.volume := by
    intro g hg _
    simpa only [ofReal_norm] using hMult g hg
  simpa only [ofReal_norm, decimatedKernel] using
    hmsw Q hQ (circleLift ψ) (Work.Thm52.integrable_circleLift hψ) hsupp A hA hOp s a ha

/-! ## The density extension from finitely supported inputs to `ℓ²` -/

/-- Cauchy–Schwarz in `ℓ²`: the product of two square-summable sequences is summable. -/
private lemma u_summable_mul_of_summable_sq {f g : ℤ → ℂ}
    (hf : Summable (fun i : ℤ => ‖f i‖ ^ 2)) (hg : Summable (fun i : ℤ => ‖g i‖ ^ 2)) :
    Summable (fun i : ℤ => f i * g i) := by
  refine Summable.of_norm ?_
  have h2 : Summable (fun i : ℤ => (‖f i‖ ^ 2 + ‖g i‖ ^ 2) / 2) := (hf.add hg).div_const 2
  refine Summable.of_nonneg_of_le (fun i => by positivity) (fun i => ?_) h2
  rw [norm_mul]
  nlinarith [sq_nonneg (‖f i‖ - ‖g i‖)]

/-- A square-summable `ℓ²`-sequence has summable squared norms. -/
private lemma u_summable_sq_of_memLp_two {h : ℤ → ℂ} (hh : Memℓp h 2) :
    Summable (fun i : ℤ => ‖h i‖ ^ 2) := by
  have h1 : Summable (fun i : ℤ => ‖h i‖ ^ (2:ℝ)) :=
    (memℓp_gen_iff (p := (2:ℝ≥0∞)) (by norm_num) (f := h)).mp hh
  refine (summable_congr (fun i => ?_)).mp h1
  rw [Real.rpow_two, pow_two]

/-- The symmetric truncations of a summable convolution converge to the full sum. -/
private lemma u_tendsto_trunc_kernel {K : ℤ → ℂ} (hK : Summable (fun j : ℤ => ‖K j‖ ^ 2))
    (h : ℤ → ℂ) (hh : Memℓp h 2) (n : ℤ) :
    Filter.Tendsto (fun j : ℕ => ∑' i : ℤ, (⇑(trunc h j) : ℤ → ℂ) i * K (n - i))
      Filter.atTop (nhds (∑' i : ℤ, h i * K (n - i))) := by
  have hsumm : Summable (fun i : ℤ => h i * K (n - i)) :=
    u_summable_mul_of_summable_sq (u_summable_sq_of_memLp_two hh)
      (hK.comp_injective (fun a b hab => by simp only [sub_right_inj] at hab; exact hab))
  have htr : ∀ j : ℕ, (∑ i ∈ Finset.Icc (-(j:ℤ)) (j:ℤ), h i * K (n - i))
      = ∑' i : ℤ, (⇑(trunc h j) : ℤ → ℂ) i * K (n - i) := by
    intro j
    rw [tsum_eq_sum (s := Finset.Icc (-(j:ℤ)) (j:ℤ)) (fun i hi => by
      rw [trunc_apply, if_neg hi, zero_mul])]
    exact Finset.sum_congr rfl (fun i hi => by rw [trunc_apply, if_pos hi])
  exact (tendsto_sum_Icc_atTop_tsum hsumm).congr' (Filter.Eventually.of_forall htr)

/-- **The density/extension step**: a bound proved for finitely supported inputs extends to all
inputs, by Fatou along the symmetric truncations. -/
private lemma u_lintegral_le_of_finsupp_bound {p : ℝ} (hp : 0 < p) {D : ℝ}
    (Λ : (ℤ → ℂ) → (ℤ → ℂ))
    (hfin : ∀ a : ℤ →₀ ℂ,
      ∫⁻ n : ℤ, ‖Λ (⇑a) n‖ₑ ^ p ∂MeasureTheory.Measure.count
        ≤ ENNReal.ofReal (D ^ p) * ∫⁻ n : ℤ, ‖(⇑a : ℤ → ℂ) n‖ₑ ^ p ∂MeasureTheory.Measure.count)
    (h : ℤ → ℂ)
    (hconv : ∀ n : ℤ,
      Filter.Tendsto (fun j : ℕ => Λ (⇑(trunc h j)) n) Filter.atTop (nhds (Λ h n))) :
    ∫⁻ n : ℤ, ‖Λ h n‖ₑ ^ p ∂MeasureTheory.Measure.count
      ≤ ENNReal.ofReal (D ^ p) * ∫⁻ n : ℤ, ‖h n‖ₑ ^ p ∂MeasureTheory.Measure.count := by
  have happ : Filter.Tendsto
      (fun j : ℕ => ∫⁻ k : ℤ, ‖(⇑(trunc h j) : ℤ → ℂ) k‖ₑ ^ p ∂MeasureTheory.Measure.count)
      Filter.atTop (nhds (∫⁻ k : ℤ, ‖h k‖ₑ ^ p ∂MeasureTheory.Measure.count)) := by
    have h1 : (fun j : ℕ => ∫⁻ k : ℤ, ‖(⇑(trunc h j) : ℤ → ℂ) k‖ₑ ^ p
          ∂MeasureTheory.Measure.count)
        = fun j : ℕ => ∫⁻ k : ℤ, ENNReal.ofReal
            ‖(if k ∈ Finset.Icc (-(j:ℤ)) (j:ℤ) then h k else 0 : ℂ)‖ ^ p
            ∂MeasureTheory.Measure.count := by
      funext j
      refine lintegral_congr (fun k => ?_)
      rw [trunc_apply]
      by_cases hk : k ∈ Finset.Icc (-(j:ℤ)) (j:ℤ) <;> simp [hk, ofReal_norm]
    have h2 : (∫⁻ k : ℤ, ‖h k‖ₑ ^ p ∂MeasureTheory.Measure.count)
        = ∫⁻ k : ℤ, ENNReal.ofReal ‖h k‖ ^ p ∂MeasureTheory.Measure.count := by
      refine lintegral_congr (fun k => ?_)
      simp [ofReal_norm]
    rw [h1, h2]
    exact tendsto_lintegral_Icc_truncation p hp h
  have hpoint : ∀ n : ℤ, ‖Λ h n‖ₑ ^ p
      ≤ Filter.liminf (fun j : ℕ => ‖Λ (⇑(trunc h j)) n‖ₑ ^ p) Filter.atTop := by
    intro n
    have hcont : Continuous (fun a : ℂ => ‖a‖ₑ ^ p) :=
      ENNReal.continuous_rpow_const.comp continuous_enorm
    have h1 : Filter.Tendsto (fun j : ℕ => ‖Λ (⇑(trunc h j)) n‖ₑ ^ p) Filter.atTop
        (nhds (‖Λ h n‖ₑ ^ p)) :=
      (hcont.tendsto (Λ h n)).comp (hconv n)
    exact le_of_eq h1.liminf_eq.symm
  have hlim : Filter.liminf
      (fun j : ℕ => ENNReal.ofReal (D ^ p)
        * ∫⁻ k : ℤ, ‖(⇑(trunc h j) : ℤ → ℂ) k‖ₑ ^ p ∂MeasureTheory.Measure.count) Filter.atTop
      = ENNReal.ofReal (D ^ p) * ∫⁻ k : ℤ, ‖h k‖ₑ ^ p ∂MeasureTheory.Measure.count := by
    rw [(ENNReal.Tendsto.const_mul happ (Or.inr ENNReal.ofReal_ne_top)).liminf_eq]
  calc ∫⁻ n : ℤ, ‖Λ h n‖ₑ ^ p ∂MeasureTheory.Measure.count
      ≤ ∫⁻ n : ℤ, Filter.liminf (fun j : ℕ => ‖Λ (⇑(trunc h j)) n‖ₑ ^ p)
          Filter.atTop ∂MeasureTheory.Measure.count := lintegral_mono hpoint
    _ ≤ Filter.liminf (fun j : ℕ => ∫⁻ n : ℤ, ‖Λ (⇑(trunc h j)) n‖ₑ ^ p
          ∂MeasureTheory.Measure.count) Filter.atTop :=
        lintegral_liminf_le'
          (fun j => (Measurable.of_discrete : Measurable
            (fun n : ℤ => ‖Λ (⇑(trunc h j)) n‖ₑ ^ p)).aemeasurable)
    _ ≤ Filter.liminf (fun j : ℕ => ENNReal.ofReal (D ^ p)
          * ∫⁻ k : ℤ, ‖(⇑(trunc h j) : ℤ → ℂ) k‖ₑ ^ p ∂MeasureTheory.Measure.count) Filter.atTop :=
        Filter.liminf_le_liminf (Filter.Eventually.of_forall (fun j => hfin (trunc h j)))
    _ = ENNReal.ofReal (D ^ p) * ∫⁻ k : ℤ, ‖h k‖ₑ ^ p ∂MeasureTheory.Measure.count := hlim

/-- **The single-operator bound** for the torsion multiplier: from the finitely supported bound
(the MSW sampling principle) to all `ℓ²`-inputs. -/
private lemma u_torsion_lp_bound_of_finsupp {p : ℝ} (hp : 0 < p) {C A : ℝ}
    {ψ : Circ → ℂ} (hψ : MemLp ψ ⊤ haarT) {B : Finset ℕ}
    (hfs : ∀ (s : Finset ℤ) (a : ℤ → ℂ), (∀ n, n ∉ s → a n = 0) →
      ∫⁻ n : ℤ, ‖∑ k ∈ s, a k * torsionKernel B (u_psiCoeff ψ) (n - k)‖ₑ ^ p
          ∂MeasureTheory.Measure.count
        ≤ ENNReal.ofReal ((C * A) ^ p) * ∫⁻ n : ℤ, ‖a n‖ₑ ^ p ∂MeasureTheory.Measure.count) :
    ∀ (h : ℤ → ℂ) (hh : Memℓp h 2),
      ∫⁻ n : ℤ, ‖opArc ψ hψ (sigmaSubAFinset B) h hh n‖ₑ ^ p ∂MeasureTheory.Measure.count
        ≤ ENNReal.ofReal ((C * A) ^ p) * ∫⁻ n : ℤ, ‖h n‖ₑ ^ p ∂MeasureTheory.Measure.count := by
  intro h hh
  have hKsumt : Summable (fun j : ℤ => ‖torsionKernel B (u_psiCoeff ψ) j‖ ^ 2) :=
    u_summable_sq_torsionKernel (u_summable_sq_kernel hψ)
  let Lam : (ℤ → ℂ) → (ℤ → ℂ) := fun g n =>
    ∑' i : ℤ, g i * torsionKernel B (u_psiCoeff ψ) (n - i)
  have hunfold : ∀ (g : ℤ → ℂ) (n : ℤ), Lam g n
      = ∑' i : ℤ, g i * torsionKernel B (u_psiCoeff ψ) (n - i) := fun g n => rfl
  have hfin : ∀ a : ℤ →₀ ℂ,
      ∫⁻ n : ℤ, ‖Lam (⇑a) n‖ₑ ^ p ∂MeasureTheory.Measure.count
        ≤ ENNReal.ofReal ((C * A) ^ p)
          * ∫⁻ n : ℤ, ‖(⇑a : ℤ → ℂ) n‖ₑ ^ p ∂MeasureTheory.Measure.count := by
    intro a
    have h1 : (fun n : ℤ => ‖Lam (⇑a) n‖ₑ ^ p)
        = fun n : ℤ => ‖∑ k ∈ a.support, (⇑a : ℤ → ℂ) k
            * torsionKernel B (u_psiCoeff ψ) (n - k)‖ₑ ^ p := by
      funext n
      rw [hunfold]
      congr 1
      rw [tsum_eq_sum (s := a.support) (fun i hi => by
        rw [Finsupp.notMem_support_iff.mp hi, zero_mul])]
    rw [h1]
    exact hfs a.support (⇑a) (fun n hn => Finsupp.notMem_support_iff.mp hn)
  have hconv : ∀ n : ℤ, Filter.Tendsto (fun j : ℕ => Lam (⇑(trunc h j)) n) Filter.atTop
      (nhds (Lam h n)) := fun n => u_tendsto_trunc_kernel hKsumt h hh n
  have hmain := u_lintegral_le_of_finsupp_bound hp Lam hfin h hconv
  rw [show (fun n : ℤ => ‖Lam h n‖ₑ ^ p)
      = fun n : ℤ => ‖opArc ψ hψ (sigmaSubAFinset B) h hh n‖ₑ ^ p from by
    funext n
    rw [hunfold, ← u_opArc_sigmaSubAFinset_eq_kernel ψ hψ h hh n]] at hmain
  exact hmain


/-- The norm of a modulated sequence is that of the original one. -/
private lemma u_norm_modSeq_apply (ρ : ℤ → ℂ) (θ : Circ) (m : ℤ) :
    ‖modSeq ρ θ m‖ = ‖ρ m‖ := by
  rw [modSeq, norm_mul, norm_fourier_apply', mul_one]

/-- The same, in the `ofReal`/square form used by the mixed norms. -/
private lemma u_ofReal_norm_modSeq (ρ : ℤ → ℂ) (θ : Circ) (m : ℤ) :
    ENNReal.ofReal (‖modSeq ρ θ m‖ ^ 2) = ENNReal.ofReal (‖ρ m‖ ^ 2) := by
  rw [u_norm_modSeq_apply]

/-- `(x ^ (1/q)) ^ q = x` for `q > 0`. -/
private lemma u_rpow_inv_cancel {q : ℝ} (hq : 0 < q) (x : ℝ≥0∞) :
    (x ^ (1/q)) ^ q = x := by
  rw [← ENNReal.rpow_mul, one_div_mul_cancel (ne_of_gt hq), ENNReal.rpow_one]

/-- **The mixed norm `(Σ'_n (Σ_t ‖·‖²)^{p/2})^{1/p}` as an `∫⁻`.** -/
private lemma u_lintegral_mixed_eq {ι : Type*} [Fintype ι] (T : ι → ℤ → ℂ) (p : ℝ) :
    ∫⁻ n : ℤ, (∑ i, ‖T i n‖ₑ ^ (2:ℝ)) ^ (p/2) ∂MeasureTheory.Measure.count
      = ∑' n : ℤ, (∑ i, ENNReal.ofReal (‖T i n‖ ^ 2)) ^ (p/2) := by
  rw [lintegral_count]
  refine tsum_congr (fun n => ?_)
  congr 1
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [← ofReal_norm, ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) (by norm_num), Real.rpow_two]

/-- **From a bound on the `∫⁻` of the mixed norm to the mixed norm itself**, taking the `(1/p)`-th
power. -/
private lemma u_mixed_le_of_lintegral {ι : Type*} [Fintype ι] {p : ℝ} (hp : 0 < p) {D : ℝ}
    (hD : 0 ≤ D) {T G : ι → ℤ → ℂ}
    (h : ∫⁻ n : ℤ, (∑ i, ‖T i n‖ₑ ^ (2:ℝ)) ^ (p/2) ∂MeasureTheory.Measure.count
        ≤ ENNReal.ofReal (D^p)
          * ∫⁻ n : ℤ, (∑ i, ‖G i n‖ₑ ^ (2:ℝ)) ^ (p/2) ∂MeasureTheory.Measure.count) :
    (∑' n : ℤ, (∑ i, ENNReal.ofReal (‖T i n‖ ^ 2)) ^ (p/2)) ^ (1/p)
      ≤ ENNReal.ofReal D
        * (∑' n : ℤ, (∑ i, ENNReal.ofReal (‖G i n‖ ^ 2)) ^ (p/2)) ^ (1/p) := by
  rw [u_lintegral_mixed_eq T p, u_lintegral_mixed_eq G p] at h
  have hp1 : (0:ℝ) ≤ 1/p := one_div_nonneg.mpr hp.le
  calc (∑' n : ℤ, (∑ i, ENNReal.ofReal (‖T i n‖ ^ 2)) ^ (p/2)) ^ (1/p)
      ≤ (ENNReal.ofReal (D^p) * (∑' n : ℤ, (∑ i, ENNReal.ofReal (‖G i n‖ ^ 2)) ^ (p/2)))^(1/p) :=
        ENNReal.rpow_le_rpow h hp1
    _ = (ENNReal.ofReal (D^p))^(1/p)
          * (∑' n : ℤ, (∑ i, ENNReal.ofReal (‖G i n‖ ^ 2)) ^ (p/2))^(1/p) :=
        ENNReal.mul_rpow_of_nonneg _ _ hp1
    _ = ENNReal.ofReal D * (∑' n : ℤ, (∑ i, ENNReal.ofReal (‖G i n‖ ^ 2)) ^ (p/2))^(1/p) := by
        congr 1
        rw [ENNReal.ofReal_rpow_of_nonneg (Real.rpow_nonneg hD p) hp1]
        congr 1
        rw [← Real.rpow_mul hD, mul_one_div_cancel (ne_of_gt hp), Real.rpow_one]

/-- **The family (Marcinkiewicz–Zygmund) bound for the torsion multiplier**, with the constant made
explicit: if every single torsion multiplier satisfies the `ℓᵖ` bound with constant `B` (as
`mz_square_function_lp` requires, in its signed form) and `Cmz` is the MZ constant, then the whole
family obeys the mixed-norm bound with constant `Cmz · Bᵖ`. -/
private lemma u_torsion_family_bound_explicit {p : ℝ} (hp : 1 < p) {Cmz : ℝ} (hCmz : 0 < Cmz)
    (hmz : ∀ {ι κ : Type} [Fintype ι] [Fintype κ]
      (T : ι → lp (fun _ : ℤ => ℂ) 2 → (ℤ → ℂ))
      (hlin : ∀ i, IsLinearMap ℂ (T i))
      (hmeas : ∀ (i : ι) (f : lp (fun _ : ℤ => ℂ) 2),
        AEMeasurable (T i f) MeasureTheory.Measure.count)
      (A : ℝ) (hA : 0 ≤ A)
      (hT : ∀ (ε : ι → Bool) (f : lp (fun _ : ℤ => ℂ) 2),
        ∫⁻ y : ℤ, ‖∑ i : ι, (if ε i then (1 : ℂ) else -1) * T i f y‖ₑ ^ p
            ∂MeasureTheory.Measure.count
          ≤ ENNReal.ofReal (A ^ p)
            * ∫⁻ y : ℤ, ‖(⇑f : ℤ → ℂ) y‖ₑ ^ p ∂MeasureTheory.Measure.count)
      (f : κ → lp (fun _ : ℤ => ℂ) 2),
      ∫⁻ y : ℤ, (∑ i : ι, ∑ t : κ, ‖T i (f t) y‖ₑ ^ (2 : ℝ)) ^ (p / 2)
          ∂MeasureTheory.Measure.count
        ≤ ENNReal.ofReal (Cmz * A ^ p)
          * ∫⁻ y : ℤ, (∑ t : κ, ‖(⇑(f t) : ℤ → ℂ) y‖ₑ ^ (2 : ℝ)) ^ (p / 2)
              ∂MeasureTheory.Measure.count)
    {φ : Circ → ℂ} (hφ : MemLp φ ⊤ haarT) {Q : Finset ℕ} {B : ℝ} (hB : 0 ≤ B)
    (hkernel : ∀ g : lp (fun _ : ℤ => ℂ) 2,
      ∫⁻ n : ℤ, ‖(⇑(opMulLM (arcSymbolLp φ hφ (sigmaSubAFinset Q)) g) : ℤ → ℂ) n‖ₑ ^ p
          ∂MeasureTheory.Measure.count
        ≤ ENNReal.ofReal (B ^ p)
          * ∫⁻ n : ℤ, ‖(⇑g : ℤ → ℂ) n‖ₑ ^ p ∂MeasureTheory.Measure.count) :
    ∀ {κ : Type} [Fintype κ] (F : κ → ℤ → ℂ) (hF : ∀ t, Memℓp (F t) 2),
      ∫⁻ n : ℤ, (∑ t : κ, ‖opArc φ hφ (sigmaSubAFinset Q) (F t) (hF t) n‖ₑ ^ (2 : ℝ)) ^ (p / 2)
          ∂MeasureTheory.Measure.count
        ≤ ENNReal.ofReal (Cmz * B ^ p)
          * ∫⁻ n : ℤ, (∑ t : κ, ‖F t n‖ₑ ^ (2 : ℝ)) ^ (p / 2)
              ∂MeasureTheory.Measure.count := by
  intro κ _ F hF
  set G : κ → lp (fun _ : ℤ => ℂ) 2 := fun t => ⟨F t, hF t⟩ with hG
  have hGcoe : ∀ t : κ, (⇑(G t) : ℤ → ℂ) = F t := fun t => rfl
  have hsigned : ∀ (ε : Unit → Bool) (f : lp (fun _ : ℤ => ℂ) 2),
      ∫⁻ y : ℤ, ‖∑ i : Unit, (if ε i then (1 : ℂ) else -1)
          * (⇑(opMulLM (arcSymbolLp φ hφ (sigmaSubAFinset Q)) f) : ℤ → ℂ) y‖ₑ ^ p
          ∂MeasureTheory.Measure.count
        ≤ ENNReal.ofReal (B ^ p)
          * ∫⁻ y : ℤ, ‖(⇑f : ℤ → ℂ) y‖ₑ ^ p ∂MeasureTheory.Measure.count := by
    intro ε f
    have hpt : ∀ y : ℤ, ‖∑ i : Unit, (if ε i then (1 : ℂ) else -1)
          * (⇑(opMulLM (arcSymbolLp φ hφ (sigmaSubAFinset Q)) f) : ℤ → ℂ) y‖ₑ
        = ‖(⇑(opMulLM (arcSymbolLp φ hφ (sigmaSubAFinset Q)) f) : ℤ → ℂ) y‖ₑ := by
      intro y
      rw [Fintype.sum_unique]
      by_cases hy : ε () = true
      · rw [if_pos hy, one_mul]
      · rw [if_neg hy, neg_mul, enorm_neg, one_mul]
    calc ∫⁻ y : ℤ, ‖∑ i : Unit, (if ε i then (1 : ℂ) else -1)
            * (⇑(opMulLM (arcSymbolLp φ hφ (sigmaSubAFinset Q)) f) : ℤ → ℂ) y‖ₑ ^ p
            ∂MeasureTheory.Measure.count
        = ∫⁻ y : ℤ,
            ‖(⇑(opMulLM (arcSymbolLp φ hφ (sigmaSubAFinset Q)) f) : ℤ → ℂ) y‖ₑ ^ p
            ∂MeasureTheory.Measure.count := by
          refine lintegral_congr (fun y => ?_)
          rw [hpt y]
      _ ≤ _ := hkernel f
  have key := hmz (ι := Unit) (κ := κ)
    (fun _ : Unit => fun g : lp (fun _ : ℤ => ℂ) 2 =>
      (⇑(opMulLM (arcSymbolLp φ hφ (sigmaSubAFinset Q)) g) : ℤ → ℂ))
    (fun _ => IsLinearMap.mk
      (fun a b => congrArg (fun v : lp (fun _ : ℤ => ℂ) 2 => (⇑v : ℤ → ℂ))
        ((opMulLM (arcSymbolLp φ hφ (sigmaSubAFinset Q))).map_add a b))
      (fun c a => congrArg (fun v : lp (fun _ : ℤ => ℂ) 2 => (⇑v : ℤ → ℂ))
        ((opMulLM (arcSymbolLp φ hφ (sigmaSubAFinset Q))).map_smul c a)))
    (fun _ g => (Measurable.of_discrete : Measurable
      ((⇑(opMulLM (arcSymbolLp φ hφ (sigmaSubAFinset Q)) g) : ℤ → ℂ))).aemeasurable)
    B hB hsigned G
  have hL : ∫⁻ y : ℤ, (∑ _i : Unit, ∑ t : κ,
        ‖(⇑(opMulLM (arcSymbolLp φ hφ (sigmaSubAFinset Q)) (G t)) : ℤ → ℂ) y‖ₑ ^ (2 : ℝ))
        ^ (p / 2) ∂MeasureTheory.Measure.count
      = ∫⁻ y : ℤ, (∑ t : κ,
          ‖opArc φ hφ (sigmaSubAFinset Q) (F t) (hF t) y‖ₑ ^ (2 : ℝ)) ^ (p / 2)
          ∂MeasureTheory.Measure.count := by
    refine lintegral_congr (fun y => ?_)
    rw [Fintype.sum_unique]
    refine congrArg (fun z => z ^ (p / 2)) ?_
    refine Finset.sum_congr rfl (fun t _ => ?_)
    rw [show (⇑(opMulLM (arcSymbolLp φ hφ (sigmaSubAFinset Q)) (G t)) : ℤ → ℂ) y
        = opArc φ hφ (sigmaSubAFinset Q) (F t) (hF t) y from by
      rw [opMulLM_apply]
      rfl]
  have hR : ∫⁻ y : ℤ, (∑ t : κ, ‖(⇑(G t) : ℤ → ℂ) y‖ₑ ^ (2 : ℝ)) ^ (p / 2)
        ∂MeasureTheory.Measure.count
      = ∫⁻ y : ℤ, (∑ t : κ, ‖F t y‖ₑ ^ (2 : ℝ)) ^ (p / 2) ∂MeasureTheory.Measure.count := by
    refine lintegral_congr (fun y => ?_)
    exact congrArg (fun z => z ^ (p / 2))
      (Finset.sum_congr rfl (fun t _ => by rw [hGcoe t]))
  rw [← hL, ← hR]
  exact key

/-- The uniform-in-`S` form of `Maximal.hstep3_msw`: the constant `C` is hoisted before `qmax` and `S`. -/
theorem hstep3_msw_uniform {k r : ℕ} (hr : 2 ≤ r) (hk : 1 ≤ k) :
    ∃ C : ℝ, 0 < C ∧ ∀ {qmax : ℕ} (hqmax : 1 ≤ qmax) {S : Finset ℕ}
      (h2S : ∀ q ∈ S, 2 ≤ q)
      (hS : ∀ p ∈ S, ∀ q ∈ S, p ≠ q → Nat.Coprime p q)
      (hmax : ∀ q ∈ S, q ≤ qmax),
      ∀ (ε : ℝ) (hε0 : 0 < ε) (hεq : ε * (qmax : ℝ) ^ k < 1 / 2)
      (ψ : Work.BourgainPlan.IonescuWainger.Circle → ℂ)
      (hψ : MeasureTheory.MemLp ψ ⊤ (AddCircle.haarAddCircle (T := 1)))
      (hψsupp : ∀ (ξ : Work.BourgainPlan.IonescuWainger.Circle), ε < ‖ξ‖ → ψ ξ = 0)
      (A : ℝ) (hA : 0 ≤ A),
      (∀ (g : ℝ → ℂ), MeasureTheory.Integrable g →
        ∫⁻ x : ℝ, ‖FourierTransformInv.fourierInv
            (fun ξ : ℝ => Work.BourgainPlan.Thm52.circleLift ψ ξ
              * FourierTransform.fourier g ξ) x‖ₑ ^ (2 * (r : ℝ)) ∂MeasureTheory.volume
          ≤ ENNReal.ofReal (A ^ (2 * (r : ℝ)))
            * ∫⁻ x : ℝ, ‖g x‖ₑ ^ (2 * (r : ℝ)) ∂MeasureTheory.volume) →
      ∀ (A₀ : Finset ℕ), A₀ ⊆ S → A₀.card ≤ k →
        ∀ (F : ↥(Work.BourgainPlan.IonescuWainger.strataCompFinset S k A₀) → ℤ → ℂ)
          (hF : ∀ t, Memℓp (F t) 2),
        ∑' n : ℤ, (∑ α : ↥(Work.BourgainPlan.IonescuWainger.strataCompFinset S k A₀),
            ENNReal.ofReal (‖Work.BourgainPlan.IonescuWainger.opArc ψ hψ
              (Work.BourgainPlan.IonescuWainger.arcShift
                (Work.BourgainPlan.IonescuWainger.sigmaStrataFinset A₀) α.1)
              (F α) (hF α) n‖ ^ 2)) ^ (r : ℝ)
          ≤ ENNReal.ofReal ((C * A) ^ (2 * (r : ℝ))) *
            ∑' n : ℤ, (∑ α : ↥(Work.BourgainPlan.IonescuWainger.strataCompFinset S k A₀),
              ENNReal.ofReal (‖F α n‖ ^ 2)) ^ (r : ℝ) := by
  classical
  have hr1 : (2:ℝ) ≤ (r:ℝ) := by exact_mod_cast hr
  have hqpos : (0:ℝ) < 2 * (r:ℝ) := by linarith
  have hp1 : (1:ℝ) < 2 * (r:ℝ) := by linarith
  have hp1le : (1:ℝ) ≤ 2 * (r:ℝ) := le_of_lt hp1
  have hp2 : (2 * (r:ℝ)) / 2 = (r:ℝ) := by ring
  obtain ⟨Cms, hCms, hmsw⟩ := u_msw_torsion_circleLift (p := 2*(r:ℝ)) hp1
  obtain ⟨Cmz, hCmz, hmz⟩ := mz_square_function_lp (p := 2*(r:ℝ)) hp1le
  set Cf : ℝ := Cmz ^ (1/(2*(r:ℝ))) * Cms * 2 ^ k with hCfdef
  refine ⟨Cf, ?_, ?_⟩
  · rw [hCfdef]
    exact mul_pos (mul_pos (Real.rpow_pos_of_pos hCmz _) hCms) (by positivity)
  intro qmax hqmax S h2S hS hmax ε hε0 hεq ψ hψ hψsupp A hA hMult A₀ hA₀S hA₀card F hF
  have hA₀2 : ∀ q ∈ A₀, 2 ≤ q := fun q hq => h2S q (hA₀S hq)
  have hA₀cop : ∀ p ∈ A₀, ∀ q ∈ A₀, p ≠ q → Nat.Coprime p q :=
    fun p hp q hq hpq => hS p (hA₀S hp) q (hA₀S hq) hpq
  set D : ℝ := Cmz ^ (1/(2*(r:ℝ))) * (Cms * A) with hDdef
  have hDle : 0 ≤ D := by
    rw [hDdef]
    exact mul_nonneg (Real.rpow_pos_of_pos hCmz _).le (mul_nonneg hCms.le hA)
  have htor : ∀ (B : Finset ℕ), B ⊆ A₀ → ∀ {κ : Type} [Fintype κ] (G : κ → ℤ → ℂ)
      (hG : ∀ t, Memℓp (G t) 2),
      (∑' n : ℤ, (∑ t : κ, ENNReal.ofReal
          (‖opArc ψ hψ (sigmaSubAFinset B) (G t) (hG t) n‖ ^ 2)) ^ ((2*(r:ℝ))/2))
        ^ (1/(2*(r:ℝ)))
        ≤ ENNReal.ofReal D * (∑' n : ℤ, (∑ t : κ, ENNReal.ofReal
            (‖G t n‖ ^ 2)) ^ ((2*(r:ℝ))/2)) ^ (1/(2*(r:ℝ))) := by
    intro B hBA₀ κ _ G hG
    have hB2 : ∀ q ∈ B, 2 ≤ q := fun q hq => h2S q (hA₀S (hBA₀ hq))
    have hQ1 : 1 ≤ QA B := by
      rw [QA]
      exact Finset.one_le_prod₀ (fun q hq => by have := hB2 q hq; omega)
    have hqmax1 : (1:ℝ) ≤ (qmax:ℝ) := by exact_mod_cast hqmax
    have hQB : QA B ≤ qmax ^ B.card := QA_le_pow_card hmax (hBA₀.trans hA₀S)
    have hQle : (QA B : ℝ) ≤ (qmax:ℝ) ^ k := by
      have h1 : (QA B : ℝ) ≤ (qmax:ℝ) ^ B.card := by exact_mod_cast hQB
      have h2 : (qmax:ℝ) ^ B.card ≤ (qmax:ℝ) ^ k :=
        pow_le_pow_right₀ hqmax1 (le_trans (Finset.card_le_card hBA₀) hA₀card)
      linarith
    have hQε : ε * (QA B : ℝ) < 1 / 2 :=
      lt_of_le_of_lt (mul_le_mul_of_nonneg_left hQle hε0.le) hεq
    have hker : ∀ j : ℤ,
        decimatedKernel (QA B) (circleLift ψ) j = torsionKernel B (u_psiCoeff ψ) j :=
      fun j => (decimatedKernel_circleLift (QA B) ψ j).trans
        (decimatedKernel_neg_coe_eq_torsionKernel ψ hψ j)
    have hfs := hmsw hψ hε0 hA hψsupp hQ1 hQε (fun g hg => hMult g hg)
    have hfs' : ∀ (s : Finset ℤ) (a : ℤ → ℂ), (∀ n, n ∉ s → a n = 0) →
        ∫⁻ n : ℤ, ‖∑ k ∈ s, a k * torsionKernel B (u_psiCoeff ψ) (n - k)‖ₑ ^ (2*(r:ℝ))
            ∂MeasureTheory.Measure.count
          ≤ ENNReal.ofReal ((Cms * A) ^ (2*(r:ℝ)))
            * ∫⁻ n : ℤ, ‖a n‖ₑ ^ (2*(r:ℝ)) ∂MeasureTheory.Measure.count := by
      intro s a ha
      have h := hfs s a ha
      refine le_of_eq_of_le ?_ h
      refine lintegral_congr (fun n => ?_)
      rw [show (∑ k ∈ s, a k * decimatedKernel (QA B) (circleLift ψ) (n - k))
          = ∑ k ∈ s, a k * torsionKernel B (u_psiCoeff ψ) (n - k) from
        Finset.sum_congr rfl (fun k _ => by rw [hker (n - k)])]
    have hsingle := u_torsion_lp_bound_of_finsupp hqpos hψ hfs'
    have hkernel : ∀ g : lp (fun _ : ℤ => ℂ) 2,
        ∫⁻ n : ℤ,
            ‖(⇑(opMulLM (arcSymbolLp ψ hψ (sigmaSubAFinset B)) g) : ℤ → ℂ) n‖ₑ ^ (2*(r:ℝ))
            ∂MeasureTheory.Measure.count
          ≤ ENNReal.ofReal ((Cms * A) ^ (2*(r:ℝ)))
            * ∫⁻ n : ℤ, ‖(⇑g : ℤ → ℂ) n‖ₑ ^ (2*(r:ℝ)) ∂MeasureTheory.Measure.count := by
      intro g
      have h := hsingle g.1 g.2
      rw [show (fun n : ℤ =>
            ‖(⇑(opMulLM (arcSymbolLp ψ hψ (sigmaSubAFinset B)) g) : ℤ → ℂ) n‖ₑ ^ (2*(r:ℝ)))
          = fun n : ℤ => ‖opArc ψ hψ (sigmaSubAFinset B) g.1 g.2 n‖ₑ ^ (2*(r:ℝ)) from by
        funext n
        rw [opMulLM_apply]
        rfl]
      exact h
    have hfam := u_torsion_family_bound_explicit (p := 2*(r:ℝ)) hp1 hCmz hmz hψ
      (mul_nonneg hCms.le hA) hkernel G hG
    have hconst : Cmz * (Cms * A) ^ (2*(r:ℝ))
        = (Cmz ^ (1/(2*(r:ℝ))) * (Cms * A)) ^ (2*(r:ℝ)) := by
      rw [Real.mul_rpow (Real.rpow_nonneg hCmz.le _) (mul_nonneg hCms.le hA),
        ← Real.rpow_mul hCmz.le, one_div_mul_cancel (ne_of_gt hqpos), Real.rpow_one]
    rw [hconst, ← hDdef] at hfam
    exact u_mixed_le_of_lintegral (p := 2*(r:ℝ)) (D := D)
      (T := fun t n => opArc ψ hψ (sigmaSubAFinset B) (G t) (hG t) n)
      (G := fun t n => G t n) hqpos hDle hfam
  have hstrata := lpL2_family_strata_incl_excl (p := 2*(r:ℝ)) hp1le ψ hψ hA₀2 hA₀cop
    (D := D) htor (fun α : ↥(strataCompFinset S k A₀) => modSeq (F α) α.1)
    (fun α => memℓp_modSeq (hF α) α.1)
  have hL : (∑' n : ℤ, (∑ t : ↥(strataCompFinset S k A₀), ENNReal.ofReal
        (‖opArc ψ hψ (arcShift (sigmaStrataFinset A₀) t.1) (F t) (hF t) n‖ ^ 2))
        ^ ((2*(r:ℝ))/2))
      = (∑' n : ℤ, (∑ t : ↥(strataCompFinset S k A₀), ENNReal.ofReal
        (‖opArc ψ hψ (sigmaStrataFinset A₀) (modSeq (F t) t.1)
          (memℓp_modSeq (hF t) t.1) n‖ ^ 2)) ^ ((2*(r:ℝ))/2)) := by
    refine tsum_congr (fun n => ?_)
    exact congrArg (fun z => z ^ ((2*(r:ℝ))/2))
      (Finset.sum_congr rfl (fun t _ => by
        rw [opArc_arcShift ψ hψ (sigmaStrataFinset A₀) t.1 (F t) (hF t),
          u_ofReal_norm_modSeq]))
  have hR : (∑' n : ℤ, (∑ t : ↥(strataCompFinset S k A₀), ENNReal.ofReal (‖F t n‖ ^ 2))
        ^ ((2*(r:ℝ))/2))
      = (∑' n : ℤ, (∑ t : ↥(strataCompFinset S k A₀), ENNReal.ofReal
        (‖modSeq (F t) t.1 n‖ ^ 2)) ^ ((2*(r:ℝ))/2)) := by
    refine tsum_congr (fun n => ?_)
    exact congrArg (fun z => z ^ ((2*(r:ℝ))/2))
      (Finset.sum_congr rfl (fun t _ => (u_ofReal_norm_modSeq (F t) t.1 n).symm))
  have hmain : (∑' n : ℤ, (∑ t : ↥(strataCompFinset S k A₀), ENNReal.ofReal
        (‖opArc ψ hψ (sigmaStrataFinset A₀) (modSeq (F t) t.1)
          (memℓp_modSeq (hF t) t.1) n‖ ^ 2)) ^ ((2*(r:ℝ))/2))
      ≤ ENNReal.ofReal ((2:ℝ) ^ A₀.card * D) ^ (2*(r:ℝ))
        * (∑' n : ℤ, (∑ t : ↥(strataCompFinset S k A₀), ENNReal.ofReal
            (‖modSeq (F t) t.1 n‖ ^ 2)) ^ ((2*(r:ℝ))/2)) := by
    have h1 := ENNReal.rpow_le_rpow hstrata (le_of_lt hqpos)
    rw [u_rpow_inv_cancel hqpos, ENNReal.mul_rpow_of_nonneg _ _ (le_of_lt hqpos),
      u_rpow_inv_cancel hqpos] at h1
    exact h1
  have hDle' : (2:ℝ) ^ A₀.card * D ≤ Cf * A := by
    rw [hDdef, hCfdef]
    have h2k : (2:ℝ) ^ A₀.card ≤ (2:ℝ) ^ k :=
      pow_le_pow_right₀ (by norm_num) hA₀card
    calc (2:ℝ) ^ A₀.card * (Cmz ^ (1/(2*(r:ℝ))) * (Cms * A))
        ≤ (2:ℝ) ^ k * (Cmz ^ (1/(2*(r:ℝ))) * (Cms * A)) :=
          mul_le_mul_of_nonneg_right h2k
            (mul_nonneg (Real.rpow_pos_of_pos hCmz _).le (mul_nonneg hCms.le hA))
      _ = (Cmz ^ (1/(2*(r:ℝ))) * Cms * 2 ^ k) * A := by ring
  have hconst_le : ENNReal.ofReal ((2:ℝ) ^ A₀.card * D) ^ (2*(r:ℝ))
      ≤ ENNReal.ofReal ((Cf * A) ^ (2*(r:ℝ))) := by
    rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) (le_of_lt hqpos)]
    exact ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow (by positivity) hDle' (le_of_lt hqpos))
  rw [hp2] at hmain hL hR
  calc (∑' n : ℤ, (∑ t : ↥(strataCompFinset S k A₀), ENNReal.ofReal
        (‖opArc ψ hψ (arcShift (sigmaStrataFinset A₀) t.1) (F t) (hF t) n‖ ^ 2)) ^ (r:ℝ))
      = (∑' n : ℤ, (∑ t : ↥(strataCompFinset S k A₀), ENNReal.ofReal
          (‖opArc ψ hψ (sigmaStrataFinset A₀) (modSeq (F t) t.1)
            (memℓp_modSeq (hF t) t.1) n‖ ^ 2)) ^ (r:ℝ)) := hL
    _ ≤ ENNReal.ofReal ((2:ℝ) ^ A₀.card * D) ^ (2*(r:ℝ))
          * (∑' n : ℤ, (∑ t : ↥(strataCompFinset S k A₀), ENNReal.ofReal
              (‖modSeq (F t) t.1 n‖ ^ 2)) ^ (r:ℝ)) := hmain
    _ ≤ ENNReal.ofReal ((Cf * A) ^ (2*(r:ℝ)))
          * (∑' n : ℤ, (∑ t : ↥(strataCompFinset S k A₀), ENNReal.ofReal
              (‖F t n‖ ^ 2)) ^ (r:ℝ)) := mul_le_mul' hconst_le (le_of_eq hR.symm)

end

end Work.BourgainPlan.Maximal
