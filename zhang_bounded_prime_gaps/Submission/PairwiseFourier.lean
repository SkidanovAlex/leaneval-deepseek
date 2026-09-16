import Mathlib
import Submission.PairwiseKernel
import Submission.DivisorKernel

open scoped BigOperators Topology FourierTransform SchwartzMap
open Filter MeasureTheory

set_option linter.unusedVariables false
set_option maxHeartbeats 2000000

/-!
# The pairwise Fubini identity (Lemma 4.1, the `2k`-fold divisor sum)

Polymath8a's Lemma 4.1 substitutes the Fourier representation (37) of the smooth
cutoffs into the divisor sum (36) and applies Fubini.  For the `k`-coordinate
pairwise-restricted sum (the shape in which the lemma is actually applied by the
sieve, see `Submission.SieveSupport`/session notes) this gives

    Σ_{x} [pairwise] ∏_j μ(d_j)μ(d'_j)/[d_j,d'_j]·F_j(log_R d_j)·G_j(log_R d'_j)
      = ∫_{ℝ^{2k}} (∏_{p ∤ q} K_p)(ξ,ξ′) · ∏_j 𝓕(eᵘF_j)(ξ_j)·𝓕(eᵘG_j)(ξ′_j) ,

the `k`-coordinate analogue of `Submission.DivisorKernel.divisorSum_eq_kernelIntegral`.
The kernel of the ξ-integral is the pairwise Euler product `pairKernel`
(`Submission.PairwiseKernel`), whose limit definition makes the identification of
the `x`-sum with the kernel the pointwise statement `pairKernelSum_eq_pairKernel`.

All kernel-verified, zero `sorry`.
-/

namespace Commons.NumberTheory.MaynardSieve

/-- The pairwise-restricted `k`-coordinate divisor-summand with the smooth
cutoffs: the product over coordinates of
`μ(d)μ(d′)/[d,d′]·F_j(log_R d)·G_j(log_R d′)`, restricted to tuples whose lcm
moduli are pairwise coprime and each coprime to `q`. -/
noncomputable def pairWeightDiv {k : ℕ} (F G : Fin k → ℝ → ℝ) (q R : ℕ)
    (x : Fin k → ℕ × ℕ) : ℂ :=
  if (∀ j : Fin k, ((x j).1.lcm (x j).2).Coprime q) ∧ PairwiseCoprimeK x then
    ∏ j : Fin k, (mobiusLcmWeight q (x j).1 (x j).2 * (F j (logR (x j).1 R) : ℂ) *
      (G j (logR (x j).2 R) : ℂ))
  else 0

/-- The per-term Fourier kernel of the pairwise Fubini step. -/
noncomputable def pairKernelPhase {k : ℕ} (F G : Fin k → ℝ → ℝ) (q R : ℕ)
    (x : Fin k → ℕ × ℕ) (p : Fin k → ℝ × ℝ) : ℂ :=
  if (∀ j : Fin k, ((x j).1.lcm (x j).2).Coprime q) ∧ PairwiseCoprimeK x then
    (∏ j : Fin k, mobiusLcmWeight q (x j).1 (x j).2) *
      (∏ j : Fin k, divisorPhase R (x j).1 (p j).1) *
      (∏ j : Fin k, divisorPhase R (x j).2 (p j).2) *
      (∏ j : Fin k, (fourierCut (F j) (p j).1 * fourierCut (G j) (p j).2))
  else 0

/-- The one-coordinate majorant in the `ξ`-variables. -/
noncomputable def phaseMajorant {k : ℕ} (F G : Fin k → ℝ → ℝ) (p : Fin k → ℝ × ℝ) : ℝ :=
  ∏ j : Fin k, (‖fourierCut (F j) (p j).1‖ * ‖fourierCut (G j) (p j).2‖)

/-- The norm of the per-term kernel is the product of the one-coordinate
majorants times the Fourier transforms. -/
theorem norm_pairKernelPhase_le {k : ℕ} (F G : Fin k → ℝ → ℝ) (q R : ℕ) (hR : 1 < R)
    (x : Fin k → ℕ × ℕ) (p : Fin k → ℝ × ℝ) :
    ‖pairKernelPhase F G q R x p‖ ≤
      (∏ j : Fin k, kernelMajorant q R (x j)) * phaseMajorant F G p := by
  rw [phaseMajorant]
  rw [pairKernelPhase]
  by_cases hg : (∀ j : Fin k, ((x j).1.lcm (x j).2).Coprime q) ∧ PairwiseCoprimeK x
  · rw [if_pos hg]
    have hper : ∀ j : Fin k, ‖mobiusLcmWeight q (x j).1 (x j).2‖ *
        ‖divisorPhase R (x j).1 (p j).1‖ * ‖divisorPhase R (x j).2 (p j).2‖ =
        kernelMajorant q R (x j) := by
      intro j
      rw [← norm_mul, ← norm_mul]
      exact norm_weight_phase q R (x j).1 (x j).2 hR (p j).1 (p j).2
    rw [norm_mul, norm_mul, norm_mul, norm_prod, norm_prod, norm_prod, norm_prod]
    simp only [norm_mul]
    have hthree : (∏ j : Fin k, ‖mobiusLcmWeight q (x j).1 (x j).2‖) *
        (∏ j : Fin k, ‖divisorPhase R (x j).1 (p j).1‖) *
        (∏ j : Fin k, ‖divisorPhase R (x j).2 (p j).2‖) =
        ∏ j : Fin k, (‖mobiusLcmWeight q (x j).1 (x j).2‖ *
          ‖divisorPhase R (x j).1 (p j).1‖ * ‖divisorPhase R (x j).2 (p j).2‖) := by
      rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
    rw [hthree, Finset.prod_congr rfl (fun j _ => hper j)]
  · rw [if_neg hg, norm_zero]
    refine mul_nonneg (Finset.prod_nonneg (fun j _ => kernelMajorant_nonneg q R (x j)))
      (Finset.prod_nonneg (fun j _ => mul_nonneg (norm_nonneg _) (norm_nonneg _)))


/-! ## Pointwise forms of the definitions -/

lemma pairWeightDiv_apply {k : ℕ} (F G : Fin k → ℝ → ℝ) (q R : ℕ) (x : Fin k → ℕ × ℕ) :
    pairWeightDiv F G q R x =
      (if (∀ j : Fin k, ((x j).1.lcm (x j).2).Coprime q) ∧ PairwiseCoprimeK x then
        ∏ j : Fin k, (mobiusLcmWeight q (x j).1 (x j).2 * (F j (logR (x j).1 R) : ℂ) *
          (G j (logR (x j).2 R) : ℂ))
      else 0) := rfl

lemma pairKernelPhase_apply {k : ℕ} (F G : Fin k → ℝ → ℝ) (q R : ℕ) (x : Fin k → ℕ × ℕ)
    (p : Fin k → ℝ × ℝ) :
    pairKernelPhase F G q R x p =
      (if (∀ j : Fin k, ((x j).1.lcm (x j).2).Coprime q) ∧ PairwiseCoprimeK x then
        (∏ j : Fin k, mobiusLcmWeight q (x j).1 (x j).2) *
          (∏ j : Fin k, divisorPhase R (x j).1 (p j).1) *
          (∏ j : Fin k, divisorPhase R (x j).2 (p j).2) *
          (∏ j : Fin k, (fourierCut (F j) (p j).1 * fourierCut (G j) (p j).2))
      else 0) := rfl

/-! ## Integrability, the integral bound and summability -/

/-- The majorant is integrable. -/
lemma integrable_phaseMajorant {k : ℕ} (F G : Fin k → ℝ → ℝ)
    (hcsF : ∀ j, HasCompactSupport (F j)) (hsmF : ∀ j, ContDiff ℝ (↑(⊤ : ℕ∞)) (F j))
    (hcsG : ∀ j, HasCompactSupport (G j)) (hsmG : ∀ j, ContDiff ℝ (↑(⊤ : ℕ∞)) (G j)) :
    Integrable (phaseMajorant F G) := by
  have hsingle : ∀ j : Fin k, Integrable (fun q : ℝ × ℝ =>
      ‖fourierCut (F j) q.1‖ * ‖fourierCut (G j) q.2‖) := by
    intro j
    rw [show (volume : Measure (ℝ × ℝ)) = Measure.prod volume volume from rfl]
    exact (integrable_norm_fourierCut (F j) (hcsF j) (hsmF j)).mul_prod
      (integrable_norm_fourierCut (G j) (hcsG j) (hsmG j))
  exact MeasureTheory.Integrable.fintype_prod hsingle

/-- The one-coordinate double integral separates (real-valued version). -/
lemma integral_mul_integral_eq_real (f g : ℝ → ℝ) :
    (∫ ξ, f ξ) * (∫ ξ', g ξ') = ∫ p : ℝ × ℝ, f p.1 * g p.2 := by
  have h : (∫ p : ℝ × ℝ, f p.1 * g p.2) = (∫ ξ, f ξ) * (∫ ξ', g ξ') := by
    rw [show (volume : Measure (ℝ × ℝ)) = Measure.prod volume volume from rfl]
    rw [integral_prod_mul]
  exact h.symm

/-- The one-coordinate double integral separates. -/
lemma integral_mul_integral_fourierCut (F G : ℝ → ℝ) :
    (∫ q : ℝ × ℝ, ‖fourierCut F q.1‖ * ‖fourierCut G q.2‖) = l1Cut F * l1Cut G := by
  have h := integral_mul_integral_eq_real (fun ξ : ℝ => ‖fourierCut F ξ‖)
    (fun ξ : ℝ => ‖fourierCut G ξ‖)
  rw [l1Cut]
  exact h.symm

/-- The integral of the majorant is the product of the one-coordinate `L¹`
norms. -/
lemma integral_phaseMajorant {k : ℕ} (F G : Fin k → ℝ → ℝ) :
    ∫ p : Fin k → ℝ × ℝ, phaseMajorant F G p = ∏ j : Fin k, (l1Cut (F j) * l1Cut (G j)) := by
  have hstep : (∏ j : Fin k, (l1Cut (F j) * l1Cut (G j))) =
      ∏ j : Fin k, (∫ q : ℝ × ℝ, ‖fourierCut (F j) q.1‖ * ‖fourierCut (G j) q.2‖) :=
    Finset.prod_congr rfl (fun j _ => (integral_mul_integral_fourierCut (F j) (G j)).symm)
  rw [hstep, ← MeasureTheory.integral_fintype_prod_volume_eq_prod
    (fun j (q : ℝ × ℝ) => ‖fourierCut (F j) q.1‖ * ‖fourierCut (G j) q.2‖)]
  rfl

/-- Measurability of the per-term kernel in `p`. -/
lemma aestronglyMeasurable_pairKernelPhase {k : ℕ} (F G : Fin k → ℝ → ℝ) (q R : ℕ)
    (hcsF : ∀ j, HasCompactSupport (F j)) (hsmF : ∀ j, ContDiff ℝ (↑(⊤ : ℕ∞)) (F j))
    (hcsG : ∀ j, HasCompactSupport (G j)) (hsmG : ∀ j, ContDiff ℝ (↑(⊤ : ℕ∞)) (G j))
    (x : Fin k → ℕ × ℕ) :
    AEStronglyMeasurable (pairKernelPhase F G q R x) := by
  classical
  have hfc : ∀ j : Fin k, Continuous fun p : Fin k → ℝ × ℝ => fourierCut (F j) (p j).1 := by
    intro j
    have h : Continuous (fourierCut (F j)) := by
      have h2 := (schwartzCut (F j) (hcsF j) (hsmF j)).continuous
      rw [schwartzCut_coe (F j) (hcsF j) (hsmF j)] at h2
      exact h2
    fun_prop (disch := exact h)
  have hgc : ∀ j : Fin k, Continuous fun p : Fin k → ℝ × ℝ => fourierCut (G j) (p j).2 := by
    intro j
    have h : Continuous (fourierCut (G j)) := by
      have h2 := (schwartzCut (G j) (hcsG j) (hsmG j)).continuous
      rw [schwartzCut_coe (G j) (hcsG j) (hsmG j)] at h2
      exact h2
    fun_prop (disch := exact h)
  have hph : ∀ j : Fin k, Continuous fun p : Fin k → ℝ × ℝ => divisorPhase R (x j).1 (p j).1 := by
    intro j
    have h : Continuous fun q : ℝ × ℝ => divisorPhase R (x j).1 q.1 := by
      unfold divisorPhase logR; fun_prop
    fun_prop (disch := exact h)
  have hph' : ∀ j : Fin k, Continuous fun p : Fin k → ℝ × ℝ => divisorPhase R (x j).2 (p j).2 := by
    intro j
    have h : Continuous fun q : ℝ × ℝ => divisorPhase R (x j).2 q.2 := by
      unfold divisorPhase logR; fun_prop
    fun_prop (disch := exact h)
  rw [show pairKernelPhase F G q R x = fun p : Fin k → ℝ × ℝ =>
      if (∀ j : Fin k, ((x j).1.lcm (x j).2).Coprime q) ∧ PairwiseCoprimeK x then
        (∏ j : Fin k, mobiusLcmWeight q (x j).1 (x j).2) *
          (∏ j : Fin k, divisorPhase R (x j).1 (p j).1) *
          (∏ j : Fin k, divisorPhase R (x j).2 (p j).2) *
          (∏ j : Fin k, (fourierCut (F j) (p j).1 * fourierCut (G j) (p j).2))
      else 0 from rfl]
  by_cases hg : (∀ j : Fin k, ((x j).1.lcm (x j).2).Coprime q) ∧ PairwiseCoprimeK x
  · simp only [if_pos hg]
    exact (((continuous_const.mul (continuous_finsetProd _ (fun j _ => hph j))).mul
      (continuous_finsetProd _ (fun j _ => hph' j))).mul
      (continuous_finsetProd _ (fun j _ => (hfc j).mul (hgc j)))).aestronglyMeasurable
  · simp only [if_neg hg]
    exact aestronglyMeasurable_const

/-- Integrability of the per-term kernel. -/
theorem integrable_pairKernelPhase {k : ℕ} (F G : Fin k → ℝ → ℝ) (q R : ℕ)
    (hcsF : ∀ j, HasCompactSupport (F j)) (hsmF : ∀ j, ContDiff ℝ (↑(⊤ : ℕ∞)) (F j))
    (hcsG : ∀ j, HasCompactSupport (G j)) (hsmG : ∀ j, ContDiff ℝ (↑(⊤ : ℕ∞)) (G j))
    (hR : 1 < R) (x : Fin k → ℕ × ℕ) :
    Integrable (pairKernelPhase F G q R x) := by
  refine Integrable.mono'
    ((integrable_phaseMajorant F G hcsF hsmF hcsG hsmG).const_mul
      (∏ j : Fin k, kernelMajorant q R (x j)))
    (aestronglyMeasurable_pairKernelPhase F G q R hcsF hsmF hcsG hsmG x) ?_
  filter_upwards with p
  simpa using norm_pairKernelPhase_le F G q R hR x p

/-- The integral bound for one term. -/
theorem integral_norm_pairKernelPhase_le {k : ℕ} (F G : Fin k → ℝ → ℝ) (q R : ℕ)
    (hcsF : ∀ j, HasCompactSupport (F j)) (hsmF : ∀ j, ContDiff ℝ (↑(⊤ : ℕ∞)) (F j))
    (hcsG : ∀ j, HasCompactSupport (G j)) (hsmG : ∀ j, ContDiff ℝ (↑(⊤ : ℕ∞)) (G j))
    (hR : 1 < R) (x : Fin k → ℕ × ℕ) :
    ∫ p : Fin k → ℝ × ℝ, ‖pairKernelPhase F G q R x p‖ ≤
      (∏ j : Fin k, kernelMajorant q R (x j)) *
        ∏ j : Fin k, (l1Cut (F j) * l1Cut (G j)) := by
  have hbase := integrable_phaseMajorant F G hcsF hsmF hcsG hsmG
  have hmono := integral_mono (integrable_pairKernelPhase F G q R hcsF hsmF hcsG hsmG hR x).norm
    (hbase.const_mul (∏ j : Fin k, kernelMajorant q R (x j)))
    (fun p => by simpa using norm_pairKernelPhase_le F G q R hR x p)
  rw [integral_const_mul] at hmono
  rw [integral_phaseMajorant F G] at hmono
  exact hmono

/-- Summability of the integrals of the norms of the per-term kernels. -/
theorem summable_integral_norm_pairKernelPhase {k : ℕ} (F G : Fin k → ℝ → ℝ) (q R : ℕ)
    (hq : q ≠ 0) (hcsF : ∀ j, HasCompactSupport (F j)) (hsmF : ∀ j, ContDiff ℝ (↑(⊤ : ℕ∞)) (F j))
    (hcsG : ∀ j, HasCompactSupport (G j)) (hsmG : ∀ j, ContDiff ℝ (↑(⊤ : ℕ∞)) (G j))
    (hR : 1 < R) :
    Summable fun x : Fin k → ℕ × ℕ => ∫ p : Fin k → ℝ × ℝ, ‖pairKernelPhase F G q R x p‖ := by
  have hsingle : ∀ j : Fin k, Summable fun d : ℕ × ℕ => ‖(kernelMajorant q R d : ℂ)‖ := by
    intro j
    have h : (fun d : ℕ × ℕ => ‖(kernelMajorant q R d : ℂ)‖) = kernelMajorant q R := by
      funext d
      rw [Complex.norm_of_nonneg (kernelMajorant_nonneg q R d)]
    rw [h]
    exact summable_kernelMajorant q R hq hR
  have hprod := summable_norm_prod_pi k (fun _ (d : ℕ × ℕ) => (kernelMajorant q R d : ℂ)) hsingle
  have hprod' : Summable fun x : Fin k → ℕ × ℕ => ∏ j : Fin k, kernelMajorant q R (x j) := by
    have h : (fun x : Fin k → ℕ × ℕ => ∏ j : Fin k, kernelMajorant q R (x j)) =
        fun x : Fin k → ℕ × ℕ => ‖∏ j : Fin k, ((kernelMajorant q R (x j) : ℝ) : ℂ)‖ := by
      funext x
      rw [norm_prod]
      refine Finset.prod_congr rfl (fun j _ => ?_)
      rw [Complex.norm_of_nonneg (kernelMajorant_nonneg q R (x j))]
    rw [h]
    exact hprod
  exact Summable.of_nonneg_of_le (fun x => integral_nonneg (fun p => norm_nonneg _))
    (fun x => integral_norm_pairKernelPhase_le F G q R hcsF hsmF hcsG hsmG hR x)
    (hprod'.mul_right _)

/-! ## The per-term Fourier expansion -/

/-- **Per-term Fourier expansion.**  Each summand of the pairwise divisor sum is
the integral of the per-term kernel. -/
theorem pairWeightDiv_eq_integral_pairKernelPhase {k : ℕ} (F G : Fin k → ℝ → ℝ)
    (hcsF : ∀ j, HasCompactSupport (F j)) (hsmF : ∀ j, ContDiff ℝ (↑(⊤ : ℕ∞)) (F j))
    (hcsG : ∀ j, HasCompactSupport (G j)) (hsmG : ∀ j, ContDiff ℝ (↑(⊤ : ℕ∞)) (G j))
    (q R : ℕ) (hR : 1 < R) (x : Fin k → ℕ × ℕ) :
    pairWeightDiv F G q R x = ∫ p : Fin k → ℝ × ℝ, pairKernelPhase F G q R x p := by
  classical
  rw [pairWeightDiv_apply]
  by_cases hg : (∀ j : Fin k, ((x j).1.lcm (x j).2).Coprime q) ∧ PairwiseCoprimeK x
  · rw [if_pos hg]
    -- Fourier expansion of each coordinate's cutoffs
    have hexp : (∏ j : Fin k, (mobiusLcmWeight q (x j).1 (x j).2 *
          (F j (logR (x j).1 R) : ℂ) * (G j (logR (x j).2 R) : ℂ))) =
        ∏ j : Fin k, (mobiusLcmWeight q (x j).1 (x j).2 *
          (∫ ξ : ℝ, divisorPhase R (x j).1 ξ * fourierCut (F j) ξ) *
          (∫ ξ' : ℝ, divisorPhase R (x j).2 ξ' * fourierCut (G j) ξ')) := by
      refine Finset.prod_congr rfl (fun j _ => ?_)
      rw [divisorForm_fourierCut (F j) (hcsF j) (hsmF j) R (x j).1,
        divisorForm_fourierCut (G j) (hcsG j) (hsmG j) R (x j).2]
    rw [hexp, Finset.prod_mul_distrib, Finset.prod_mul_distrib]
    have hint : (∏ j : Fin k, (∫ ξ : ℝ, divisorPhase R (x j).1 ξ * fourierCut (F j) ξ)) *
        (∏ j : Fin k, (∫ ξ' : ℝ, divisorPhase R (x j).2 ξ' * fourierCut (G j) ξ')) =
        ∫ p : Fin k → ℝ × ℝ, ∏ j : Fin k,
          ((divisorPhase R (x j).1 (p j).1 * fourierCut (F j) (p j).1) *
            (divisorPhase R (x j).2 (p j).2 * fourierCut (G j) (p j).2)) := by
      rw [← Finset.prod_mul_distrib]
      rw [show (∏ j : Fin k, ((∫ ξ : ℝ, divisorPhase R (x j).1 ξ * fourierCut (F j) ξ) *
            (∫ ξ' : ℝ, divisorPhase R (x j).2 ξ' * fourierCut (G j) ξ'))) =
          ∏ j : Fin k, (∫ u : ℝ × ℝ,
            (divisorPhase R (x j).1 u.1 * fourierCut (F j) u.1) *
            (divisorPhase R (x j).2 u.2 * fourierCut (G j) u.2)) from
        Finset.prod_congr rfl (fun j _ => integral_mul_integral_eq _ _)]
      rw [← MeasureTheory.integral_fintype_prod_volume_eq_prod
        (fun j (u : ℝ × ℝ) => (divisorPhase R (x j).1 u.1 * fourierCut (F j) u.1) *
          (divisorPhase R (x j).2 u.2 * fourierCut (G j) u.2))]
    rw [show (∏ j : Fin k, mobiusLcmWeight q (x j).1 (x j).2) *
          (∏ j : Fin k, (∫ ξ : ℝ, divisorPhase R (x j).1 ξ * fourierCut (F j) ξ)) *
          (∏ j : Fin k, (∫ ξ' : ℝ, divisorPhase R (x j).2 ξ' * fourierCut (G j) ξ')) =
        (∏ j : Fin k, mobiusLcmWeight q (x j).1 (x j).2) *
          ((∏ j : Fin k, (∫ ξ : ℝ, divisorPhase R (x j).1 ξ * fourierCut (F j) ξ)) *
            (∏ j : Fin k, (∫ ξ' : ℝ, divisorPhase R (x j).2 ξ' * fourierCut (G j) ξ')))
        from by ring]
    rw [hint, ← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall (fun p => ?_))
    rw [pairKernelPhase_apply, if_pos hg]
    dsimp only
    simp only [Finset.prod_mul_distrib]
    ring
  · rw [if_neg hg]
    rw [show (∫ p : Fin k → ℝ × ℝ, pairKernelPhase F G q R x p) = ∫ p : Fin k → ℝ × ℝ, 0 from by
      refine integral_congr_ae (Filter.Eventually.of_forall (fun p => ?_))
      rw [pairKernelPhase_apply, if_neg hg]]
    simp


/-! ## The pairwise Fubini identity -/

/-- The per-term kernel is the (guarded) `k`-coordinate kernel weight times the
Fourier transforms of the cutoffs. -/
lemma pairKernelPhase_eq_kernelWeightK_mul {k : ℕ} (F G : Fin k → ℝ → ℝ) (q R : ℕ) (hR : 1 < R)
    (x : Fin k → ℕ × ℕ) (p : Fin k → ℝ × ℝ) :
    pairKernelPhase F G q R x p =
      pairKernelWeight q (fun j => logZ (-(2 * Real.pi * (p j).1)) R)
          (fun j => logZ (-(2 * Real.pi * (p j).2)) R) x *
        ∏ j : Fin k, (fourierCut (F j) (p j).1 * fourierCut (G j) (p j).2) := by
  classical
  by_cases hg : (∀ j : Fin k, ((x j).1.lcm (x j).2).Coprime q) ∧ PairwiseCoprimeK x
  · rw [pairKernelPhase_apply, if_pos hg, pairKernelWeight, if_pos hg, kernelWeightK]
    have hkern : ∀ j : Fin k, kernelWeight (logZ (-(2 * Real.pi * (p j).1)) R)
        (logZ (-(2 * Real.pi * (p j).2)) R) (x j) =
        mobiusLcmWeight q (x j).1 (x j).2 * divisorPhase R (x j).1 (p j).1 *
          divisorPhase R (x j).2 (p j).2 := by
      intro j
      have hqj : ((x j).1.lcm (x j).2).Coprime q := hg.1 j
      have h1 : kernelWeight (logZ (-(2 * Real.pi * (p j).1)) R)
          (logZ (-(2 * Real.pi * (p j).2)) R) (x j) =
          kernelWeightQ q (logZ (-(2 * Real.pi * (p j).1)) R)
            (logZ (-(2 * Real.pi * (p j).2)) R) (x j) := by
        rw [kernelWeightQ, if_pos hqj]
      rw [h1]
      exact kernelWeightQ_eq_phase_mul q R (x j).1 (x j).2 hR _ _
    rw [Finset.prod_congr rfl (fun j _ => hkern j)]
    simp only [Finset.prod_mul_distrib]
  · rw [pairKernelPhase_apply, if_neg hg, pairKernelWeight, if_neg hg]
    simp

/-- **The pairwise Fubini identity.**  The pairwise-restricted `k`-coordinate
divisor sum equals the `2k`-fold `ξ`-integral of the kernel `pairKernelSum`
against the Fourier transforms of the cutoffs. -/
theorem pairwiseDivisorSum_eq_kernelSumIntegral {k : ℕ} (F G : Fin k → ℝ → ℝ)
    (hcsF : ∀ j, HasCompactSupport (F j)) (hsmF : ∀ j, ContDiff ℝ (↑(⊤ : ℕ∞)) (F j))
    (hcsG : ∀ j, HasCompactSupport (G j)) (hsmG : ∀ j, ContDiff ℝ (↑(⊤ : ℕ∞)) (G j))
    (q R : ℕ) (hq : q ≠ 0) (hR : 1 < R) :
    (∑' x : Fin k → ℕ × ℕ, pairWeightDiv F G q R x) =
      ∫ p : Fin k → ℝ × ℝ, pairKernelSum q
          (fun j => logZ (-(2 * Real.pi * (p j).1)) R)
          (fun j => logZ (-(2 * Real.pi * (p j).2)) R) *
        (∏ j : Fin k, (fourierCut (F j) (p j).1 * fourierCut (G j) (p j).2)) := by
  classical
  have hterm : ∀ x : Fin k → ℕ × ℕ,
      pairWeightDiv F G q R x = ∫ p : Fin k → ℝ × ℝ, pairKernelPhase F G q R x p :=
    fun x => pairWeightDiv_eq_integral_pairKernelPhase F G hcsF hsmF hcsG hsmG q R hR x
  have hInt : ∀ x : Fin k → ℕ × ℕ, Integrable (pairKernelPhase F G q R x) :=
    fun x => integrable_pairKernelPhase F G q R hcsF hsmF hcsG hsmG hR x
  have hSumm : Summable fun x : Fin k → ℕ × ℕ =>
      ∫ p : Fin k → ℝ × ℝ, ‖pairKernelPhase F G q R x p‖ :=
    summable_integral_norm_pairKernelPhase F G q R hq hcsF hsmF hcsG hsmG hR
  calc (∑' x : Fin k → ℕ × ℕ, pairWeightDiv F G q R x)
      = ∑' x : Fin k → ℕ × ℕ, ∫ p : Fin k → ℝ × ℝ, pairKernelPhase F G q R x p :=
        tsum_congr hterm
    _ = ∫ p : Fin k → ℝ × ℝ, ∑' x : Fin k → ℕ × ℕ, pairKernelPhase F G q R x p :=
        integral_tsum_of_summable_integral_norm hInt hSumm
    _ = ∫ p : Fin k → ℝ × ℝ, pairKernelSum q
          (fun j => logZ (-(2 * Real.pi * (p j).1)) R)
          (fun j => logZ (-(2 * Real.pi * (p j).2)) R) *
        (∏ j : Fin k, (fourierCut (F j) (p j).1 * fourierCut (G j) (p j).2)) := by
        refine integral_congr_ae (Filter.Eventually.of_forall (fun p => ?_))
        dsimp only
        have h1 : (∑' x : Fin k → ℕ × ℕ, pairKernelPhase F G q R x p) =
            ∑' x : Fin k → ℕ × ℕ, (pairKernelWeight q
                (fun j => logZ (-(2 * Real.pi * (p j).1)) R)
                (fun j => logZ (-(2 * Real.pi * (p j).2)) R) x *
              ∏ j : Fin k, (fourierCut (F j) (p j).1 * fourierCut (G j) (p j).2)) :=
          tsum_congr (fun x => pairKernelPhase_eq_kernelWeightK_mul F G q R hR x p)
        rw [h1, tsum_mul_right, pairKernelSum]


/-- **The pairwise Fubini identity, in terms of the kernel `pairKernel`.** -/
theorem pairwiseDivisorSum_eq_kernelIntegral {k : ℕ} (F G : Fin k → ℝ → ℝ)
    (hcsF : ∀ j, HasCompactSupport (F j)) (hsmF : ∀ j, ContDiff ℝ (↑(⊤ : ℕ∞)) (F j))
    (hcsG : ∀ j, HasCompactSupport (G j)) (hsmG : ∀ j, ContDiff ℝ (↑(⊤ : ℕ∞)) (G j))
    (q R : ℕ) (hq : q ≠ 0) (hR : 1 < R) :
    (∑' x : Fin k → ℕ × ℕ, pairWeightDiv F G q R x) =
      ∫ p : Fin k → ℝ × ℝ, pairKernel q
          (fun j => logZ (-(2 * Real.pi * (p j).1)) R)
          (fun j => logZ (-(2 * Real.pi * (p j).2)) R) *
        (∏ j : Fin k, (fourierCut (F j) (p j).1 * fourierCut (G j) (p j).2)) := by
  rw [pairwiseDivisorSum_eq_kernelSumIntegral F G hcsF hsmF hcsG hsmG q R hq hR]
  refine integral_congr_ae (Filter.Eventually.of_forall (fun p => ?_))
  dsimp only
  have hlog : 0 < Real.log (R : ℝ) := Real.log_pos (by exact_mod_cast hR)
  rw [pairKernelSum_eq_pairKernel q hq
    (fun j => by rw [logZ_re]; exact div_pos one_pos hlog)
    (fun j => by rw [logZ_re]; exact div_pos one_pos hlog)]

end Commons.NumberTheory.MaynardSieve
