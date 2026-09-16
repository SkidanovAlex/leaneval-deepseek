import Mathlib
import Submission.KernelSum
import Submission.ZFourierGlue
import Submission.Truncation

open scoped BigOperators Topology FourierTransform SchwartzMap
open Filter MeasureTheory

set_option linter.unusedVariables false
set_option maxHeartbeats 2000000

/-!
# The divisor-sum ↔ kernel-integral identity (P8 Lemma 4.1, Fubini step)

Polymath8a's Lemma 4.1 substitutes the Fourier representation (37) of the
smooth cutoffs into the doubly-indexed divisor sum (36) and applies Fubini,
obtaining (38): the divisor sum equals the double ξ-integral of the kernel
`K` against the Fourier transforms of `e^u F(u)`, `e^u G(u)`.

This module formalizes that step for the `μ(d)μ(d′)/[d,d′]` weight:

    Σ_{a,b} μ(a)μ(b)[a,b]⁻¹ · F(log_R a)·G(log_R b)  (with ([a,b], q) = 1)
      = ∫_{ℝ²} K(ξ,ξ′) · 𝓕(eᵘF)(ξ) · 𝓕(eᵘG)(ξ′) ,

where `K = kernelFun q (logZ(−2πξ) R) (logZ(−2πξ′) R)` is the Euler-product
kernel of `Submission.KernelSum`/`KernelFun` (P8 (38)/(39)).

The ingredients are: the per-term Fourier expansion `divisorForm_smoothComp`,
the identification of the phase
`exp(−log_R b + 2πi·log_R b·ξ) = (b:ℂ)^{−logZ(−2πξ) R}` for `b ≠ 0`, the
factorization `kernelWeightQ = μμ[a,b]⁻¹ · (a)^{−α}(b)^{−β}`, and the
absolute convergence `summable_kernelWeightQ` which lets the infinite sum be
interchanged with the integral.

All kernel-verified, zero `sorry`.
-/

namespace Commons.NumberTheory.MaynardSieve

/-- The Möbius/lcm weight of the divisor kernel: `μ(a)μ(b)/[a,b]` for
`([a,b], q) = 1`, and `0` otherwise. -/
noncomputable def mobiusLcmWeight (q a b : ℕ) : ℂ :=
  if (Nat.lcm a b).Coprime q then
    ((ArithmeticFunction.moebius a : ℤ) : ℂ) * ((ArithmeticFunction.moebius b : ℤ) : ℂ) *
      (((Nat.lcm a b : ℕ) : ℂ))⁻¹
  else 0

/-- Factorization of the kernel weight into the Möbius/lcm weight and the two
`cpow` factors. -/
lemma kernelWeightQ_eq (q a b : ℕ) (α β : ℂ) :
    kernelWeightQ q α β (a, b) = mobiusLcmWeight q a b * (a : ℂ) ^ (-α) * (b : ℂ) ^ (-β) := by
  unfold kernelWeightQ mobiusLcmWeight kernelWeight
  simp only [Prod.fst, Prod.snd]
  split_ifs <;> ring

/-- **The divisor phase is a `cpow`.**  For `1 < R` and `b ≠ 0`,
`exp(−log_R b + 2πi·log_R b·ξ) = (b:ℂ)^{−logZ(−2πξ) R}`. -/
lemma divisorPhase_eq_cpow {R b : ℕ} (hR : 1 < R) (hb : b ≠ 0) (ξ : ℝ) :
    divisorPhase R b ξ = (b : ℂ) ^ (-(logZ (-(2 * Real.pi * ξ)) R)) := by
  have hbc : (b : ℂ) ≠ 0 := by exact_mod_cast hb
  have hbR : (0 : ℝ) < (b : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hb
  have hlogR : (Real.log (R : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.log_pos (by exact_mod_cast hR)).ne'
  have hlog : Complex.log (b : ℂ) = ((Real.log (b : ℝ) : ℝ) : ℂ) := by
    have h := Complex.ofReal_log (x := (b : ℝ)) hbR.le
    simpa using h.symm
  rw [Complex.cpow_def_of_ne_zero hbc, hlog, logZ, divisorPhase, logR]
  congr 1
  push_cast
  field_simp
  ring


/-- The P8 (37) Fourier expansion of a cutoff, in the `divisorPhase`/`fourierCut`
normalization used for the Fubini step. -/
lemma divisorForm_fourierCut (F : ℝ → ℝ) (hcs : HasCompactSupport F)
    (hsm : ContDiff ℝ (↑(⊤ : ℕ∞)) F) (R d : ℕ) :
    (F (logR d R) : ℂ) = ∫ ξ : ℝ, divisorPhase R d ξ * fourierCut F ξ :=
  divisorForm_smoothComp F hcs hsm R d

/-- **Fubini for a product of two integrals**: the product of the integrals is
the double integral of the product. -/
lemma integral_mul_integral_eq (f g : ℝ → ℂ) :
    (∫ ξ, f ξ) * (∫ ξ', g ξ') = ∫ p : ℝ × ℝ, f p.1 * g p.2 := by
  have h : (∫ p : ℝ × ℝ, f p.1 * g p.2) = (∫ ξ, f ξ) * (∫ ξ', g ξ') := by
    rw [show (volume : Measure (ℝ × ℝ)) = Measure.prod volume volume from rfl]
    rw [integral_prod_mul]
  exact h.symm

/-- The norm of a divisor phase: `‖exp(−log_R b + 2πi log_R b ξ)‖ = b^{−1/log R}`. -/
lemma norm_divisorPhase {R b : ℕ} (hR : 1 < R) (hb : b ≠ 0) (ξ : ℝ) :
    ‖divisorPhase R b ξ‖ = (b : ℝ) ^ (-(1 / Real.log (R : ℝ))) := by
  have hbR : (0 : ℝ) < (b : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hb
  have hcast : (b : ℂ) = ((b : ℝ) : ℂ) := by push_cast; ring
  rw [divisorPhase_eq_cpow hR hb ξ, hcast,
    Complex.norm_cpow_eq_rpow_re_of_pos hbR (-(logZ (-(2 * Real.pi * ξ)) R))]
  congr 1
  rw [Complex.neg_re, logZ_re]


/-- The majorant of the kernel weight:
`|μ(a)μ(b)|·[a,b]⁻¹·a^{−1/log R}·b^{−1/log R}`. -/
noncomputable def kernelMajorant (q R : ℕ) (x : ℕ × ℕ) : ℝ :=
  ‖mobiusLcmWeight q x.1 x.2‖ * (x.1 : ℝ) ^ (-(1 / Real.log (R : ℝ))) *
    (x.2 : ℝ) ^ (-(1 / Real.log (R : ℝ)))

/-- The Möbius/lcm weight vanishes in the first coordinate at `0`. -/
lemma mobiusLcmWeight_zero_fst (q b : ℕ) : mobiusLcmWeight q 0 b = 0 := by
  unfold mobiusLcmWeight
  split_ifs with hc
  · have h : ArithmeticFunction.moebius 0 = 0 := by simp [ArithmeticFunction.moebius]
    rw [h]; ring
  · rfl

/-- The Möbius/lcm weight vanishes in the second coordinate at `0`. -/
lemma mobiusLcmWeight_zero_snd (q a : ℕ) : mobiusLcmWeight q a 0 = 0 := by
  unfold mobiusLcmWeight
  split_ifs with hc
  · have h : ArithmeticFunction.moebius 0 = 0 := by simp [ArithmeticFunction.moebius]
    rw [h]; ring
  · rfl

/-- The norm of the weighted divisor phase is the majorant. -/
lemma norm_weight_phase (q R a b : ℕ) (hR : 1 < R) (ξ ξ' : ℝ) :
    ‖mobiusLcmWeight q a b * divisorPhase R a ξ * divisorPhase R b ξ'‖ =
      kernelMajorant q R (a, b) := by
  rw [norm_mul, norm_mul, kernelMajorant]
  simp only [Prod.fst, Prod.snd]
  by_cases ha : a = 0
  · rw [ha, mobiusLcmWeight_zero_fst]; simp
  · by_cases hb : b = 0
    · rw [hb, mobiusLcmWeight_zero_snd]; simp
    · rw [norm_divisorPhase hR ha ξ, norm_divisorPhase hR hb ξ']

/-- The norm of the kernel weight at the real points `1/log R` is the majorant. -/
lemma norm_kernelWeightQ_eq_majorant (q R : ℕ) (hR : 1 < R) (x : ℕ × ℕ) :
    ‖kernelWeightQ q (((1 / Real.log (R : ℝ)) : ℝ) : ℂ)
        (((1 / Real.log (R : ℝ)) : ℝ) : ℂ) x‖ = kernelMajorant q R x := by
  rw [kernelWeightQ_eq, norm_mul, norm_mul, kernelMajorant]
  by_cases ha : x.1 = 0
  · rw [ha, mobiusLcmWeight_zero_fst]; simp
  · by_cases hb : x.2 = 0
    · rw [hb, mobiusLcmWeight_zero_snd]; simp
    · have ha' : (0 : ℝ) < (x.1 : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero ha
      have hb' : (0 : ℝ) < (x.2 : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hb
      have hca : (x.1 : ℂ) = ((x.1 : ℝ) : ℂ) := by push_cast; ring
      have hcb : (x.2 : ℂ) = ((x.2 : ℝ) : ℂ) := by push_cast; ring
      rw [hca, hcb, Complex.norm_cpow_eq_rpow_re_of_pos ha',
        Complex.norm_cpow_eq_rpow_re_of_pos hb']
      simp only [Complex.neg_re, Complex.ofReal_re]

/-- **Summability of the majorant.** -/
lemma summable_kernelMajorant (q R : ℕ) (hq : q ≠ 0) (hR : 1 < R) :
    Summable (kernelMajorant q R) := by
  have hL : (0 : ℝ) < Real.log (R : ℝ) := Real.log_pos (by exact_mod_cast hR)
  have h1 : (0 : ℝ) < (((1 / Real.log (R : ℝ)) : ℝ) : ℂ).re := by
    rw [Complex.ofReal_re]; positivity
  have h2 : (0 : ℝ) < (((1 / Real.log (R : ℝ)) : ℝ) : ℂ).re := by
    rw [Complex.ofReal_re]; positivity
  have h := summable_kernelWeightQ q h1 h2
  rwa [show (fun x : ℕ × ℕ => ‖kernelWeightQ q (((1 / Real.log (R : ℝ)) : ℝ) : ℂ)
      (((1 / Real.log (R : ℝ)) : ℝ) : ℂ) x‖) = kernelMajorant q R from
    funext (norm_kernelWeightQ_eq_majorant q R hR)] at h

/-- **Factorization of the kernel weight into the weighted divisor phases.** -/
lemma kernelWeightQ_eq_phase_mul (q R a b : ℕ) (hR : 1 < R) (ξ ξ' : ℝ) :
    kernelWeightQ q (logZ (-(2 * Real.pi * ξ)) R) (logZ (-(2 * Real.pi * ξ')) R) (a, b)
      = mobiusLcmWeight q a b * divisorPhase R a ξ * divisorPhase R b ξ' := by
  rw [kernelWeightQ_eq]
  by_cases ha : a = 0
  · rw [ha, mobiusLcmWeight_zero_fst]; ring
  · by_cases hb : b = 0
    · rw [hb, mobiusLcmWeight_zero_snd]; ring
    · rw [divisorPhase_eq_cpow hR ha ξ, divisorPhase_eq_cpow hR hb ξ']


/-- **The divisor sum equals the kernel integral** (P8 Lemma 4.1, Fubini step):
for `q ≠ 0`, `1 < R` and smooth compactly supported real cutoffs `F, G`,

    Σ_{a,b} μ(a)μ(b)[a,b]⁻¹·F(log_R a)·G(log_R b)  (with ([a,b], q) = 1)
      = ∫_{ℝ²} K(ξ,ξ′)·𝓕(eᵘF)(ξ)·𝓕(eᵘG)(ξ′) ,

where `K(ξ, ξ′) = kernelFun q (logZ(−2πξ) R) (logZ(−2πξ′) R)`. -/
theorem divisorSum_eq_kernelIntegral
    (F G : ℝ → ℝ) (hcsF : HasCompactSupport F) (hsmF : ContDiff ℝ (↑(⊤ : ℕ∞)) F)
    (hcsG : HasCompactSupport G) (hsmG : ContDiff ℝ (↑(⊤ : ℕ∞)) G)
    (q R : ℕ) (hq : q ≠ 0) (hR : 1 < R) :
    (∑' x : ℕ × ℕ, mobiusLcmWeight q x.1 x.2 * (F (logR x.1 R) : ℂ) *
        (G (logR x.2 R) : ℂ))
      = ∫ p : ℝ × ℝ, kernelFun q (logZ (-(2 * Real.pi * p.1)) R)
          (logZ (-(2 * Real.pi * p.2)) R) * (fourierCut F p.1 * fourierCut G p.2) := by
  classical
  have hL : 0 < Real.log (R : ℝ) := Real.log_pos (by exact_mod_cast hR)
  have hFred0 : ∀ ξ : ℝ, 0 < (logZ ξ R).re := fun ξ => by rw [logZ_re]; exact div_pos one_pos hL
  have hFcont : Continuous (fourierCut F) := by
    have h := (schwartzCut F hcsF hsmF).continuous
    rw [schwartzCut_coe F hcsF hsmF] at h
    exact h
  have hGcont : Continuous (fourierCut G) := by
    have h := (schwartzCut G hcsG hsmG).continuous
    rw [schwartzCut_coe G hcsG hsmG] at h
    exact h
  have hFmeas : Measurable (fourierCut F) := hFcont.measurable
  have hGmeas : Measurable (fourierCut G) := hGcont.measurable
  have hFint : Integrable (fun ξ : ℝ => ‖fourierCut F ξ‖) := by
    simpa only [fourierCut] using integrable_norm_fourierCut F hcsF hsmF
  have hGint : Integrable (fun ξ : ℝ => ‖fourierCut G ξ‖) := by
    simpa only [fourierCut] using integrable_norm_fourierCut G hcsG hsmG
  have hbase : Integrable (fun p : ℝ × ℝ => ‖fourierCut F p.1‖ * ‖fourierCut G p.2‖) := by
    rw [show (volume : Measure (ℝ × ℝ)) = Measure.prod volume volume from rfl]
    exact hFint.mul_prod hGint
  set H : ℕ × ℕ → ℝ × ℝ → ℂ := fun x p =>
    mobiusLcmWeight q x.1 x.2 * divisorPhase R x.1 p.1 * divisorPhase R x.2 p.2 *
      (fourierCut F p.1 * fourierCut G p.2) with hHdef
  -- pointwise norm bound for `H x`
  have hHnorm : ∀ (x : ℕ × ℕ) (p : ℝ × ℝ), ‖H x p‖ ≤
      kernelMajorant q R x * (‖fourierCut F p.1‖ * ‖fourierCut G p.2‖) := by
    intro x p
    rw [hHdef]
    have h2 : ‖mobiusLcmWeight q x.1 x.2 * divisorPhase R x.1 p.1 * divisorPhase R x.2 p.2 *
        (fourierCut F p.1 * fourierCut G p.2)‖ =
        ‖mobiusLcmWeight q x.1 x.2 * divisorPhase R x.1 p.1 * divisorPhase R x.2 p.2‖ *
          ‖fourierCut F p.1 * fourierCut G p.2‖ := norm_mul _ _
    have h3 : ‖fourierCut F p.1 * fourierCut G p.2‖ = ‖fourierCut F p.1‖ * ‖fourierCut G p.2‖ :=
      norm_mul _ _
    rw [h2, h3, norm_weight_phase q R x.1 x.2 hR p.1 p.2]
  have hHmeas : ∀ x : ℕ × ℕ, AEStronglyMeasurable (H x) := by
    intro x
    have h1 : Continuous fun p : ℝ × ℝ => divisorPhase R x.1 p.1 := by
      unfold divisorPhase logR; fun_prop
    have h2 : Continuous fun p : ℝ × ℝ => divisorPhase R x.2 p.2 := by
      unfold divisorPhase logR; fun_prop
    have h3 : Continuous fun p : ℝ × ℝ => fourierCut F p.1 :=
      hFcont.comp continuous_fst
    have h4 : Continuous fun p : ℝ × ℝ => fourierCut G p.2 :=
      hGcont.comp continuous_snd
    rw [hHdef]
    exact (((continuous_const.mul h1).mul h2).mul (h3.mul h4)).aestronglyMeasurable
  have hH_int : ∀ x : ℕ × ℕ, Integrable (H x) := by
    intro x
    refine Integrable.mono' (hbase.const_mul (kernelMajorant q R x)) (hHmeas x) ?_
    filter_upwards with p
    exact hHnorm x p
  have hH_summ : Summable (fun x : ℕ × ℕ => ∫ p : ℝ × ℝ, ‖H x p‖) := by
    have hle : ∀ x : ℕ × ℕ, ∫ p : ℝ × ℝ, ‖H x p‖ ≤ kernelMajorant q R x * (l1Cut F * l1Cut G) := by
      intro x
      have hmono := integral_mono (hH_int x).norm (hbase.const_mul (kernelMajorant q R x))
        (fun p => hHnorm x p)
      rw [integral_const_mul] at hmono
      have h2 : ∫ p : ℝ × ℝ, ‖fourierCut F p.1‖ * ‖fourierCut G p.2‖ = l1Cut F * l1Cut G := by
        rw [show (volume : Measure (ℝ × ℝ)) = Measure.prod volume volume from rfl]
        exact integral_prod_mul (fun ξ => ‖fourierCut F ξ‖) (fun ξ => ‖fourierCut G ξ‖)
      calc ∫ p : ℝ × ℝ, ‖H x p‖
          ≤ kernelMajorant q R x * ∫ p : ℝ × ℝ, ‖fourierCut F p.1‖ * ‖fourierCut G p.2‖ := hmono
        _ = kernelMajorant q R x * (l1Cut F * l1Cut G) := by rw [h2]
    exact Summable.of_nonneg_of_le (fun x => integral_nonneg (fun p => norm_nonneg _)) hle
      ((summable_kernelMajorant q R hq hR).mul_right _)
  -- the per-term Fourier expansion
  have hterm : ∀ x : ℕ × ℕ, mobiusLcmWeight q x.1 x.2 * (F (logR x.1 R) : ℂ) *
        (G (logR x.2 R) : ℂ) = ∫ p : ℝ × ℝ, H x p := by
    intro x
    rw [divisorForm_fourierCut F hcsF hsmF R x.1, divisorForm_fourierCut G hcsG hsmG R x.2]
    have h1 : (∫ ξ, divisorPhase R x.1 ξ * fourierCut F ξ) *
          (∫ ξ', divisorPhase R x.2 ξ' * fourierCut G ξ') =
        ∫ p : ℝ × ℝ, (divisorPhase R x.1 p.1 * fourierCut F p.1) *
          (divisorPhase R x.2 p.2 * fourierCut G p.2) :=
      integral_mul_integral_eq _ _
    rw [show mobiusLcmWeight q x.1 x.2 * (∫ ξ, divisorPhase R x.1 ξ * fourierCut F ξ) *
          (∫ ξ', divisorPhase R x.2 ξ' * fourierCut G ξ') =
          mobiusLcmWeight q x.1 x.2 * ((∫ ξ, divisorPhase R x.1 ξ * fourierCut F ξ) *
            (∫ ξ', divisorPhase R x.2 ξ' * fourierCut G ξ')) from by ring]
    rw [h1, ← integral_const_mul, hHdef]
    refine congrArg (fun h : ℝ × ℝ → ℂ => ∫ p : ℝ × ℝ, h p) ?_
    funext p
    ring
  calc (∑' x : ℕ × ℕ, mobiusLcmWeight q x.1 x.2 * (F (logR x.1 R) : ℂ) *
        (G (logR x.2 R) : ℂ))
      = ∑' x : ℕ × ℕ, ∫ p : ℝ × ℝ, H x p := tsum_congr hterm
    _ = ∫ p : ℝ × ℝ, ∑' x : ℕ × ℕ, H x p :=
        integral_tsum_of_summable_integral_norm hH_int hH_summ
    _ = ∫ p : ℝ × ℝ, kernelFun q (logZ (-(2 * Real.pi * p.1)) R)
          (logZ (-(2 * Real.pi * p.2)) R) * (fourierCut F p.1 * fourierCut G p.2) := by
        refine integral_congr_ae (Filter.Eventually.of_forall (fun p => ?_))
        show (∑' x : ℕ × ℕ, H x p) = kernelFun q (logZ (-(2 * Real.pi * p.1)) R)
          (logZ (-(2 * Real.pi * p.2)) R) * (fourierCut F p.1 * fourierCut G p.2)
        have hpt : (∑' x : ℕ × ℕ, H x p) =
            kernelSum q (logZ (-(2 * Real.pi * p.1)) R) (logZ (-(2 * Real.pi * p.2)) R) *
              (fourierCut F p.1 * fourierCut G p.2) := by
          rw [hHdef, tsum_mul_right]
          refine congrArg (fun z : ℂ => z * (fourierCut F p.1 * fourierCut G p.2)) ?_
          rw [kernelSum]
          exact tsum_congr (fun x => (kernelWeightQ_eq_phase_mul q R x.1 x.2 hR p.1 p.2).symm)
        rw [hpt, kernelSum_eq_kernelFun q hq (hFred0 (-(2 * Real.pi * p.1)))
          (hFred0 (-(2 * Real.pi * p.2)))]

end Commons.NumberTheory.MaynardSieve
