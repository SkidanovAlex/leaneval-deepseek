import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.FTS.EllSol.EllPkgAux.MollBase
import Submission.Work.FTS.EllSol.EllPkgAux.KernelDefs
import Submission.Work.FTS.EllSol.PkgK5.K5c.MollDefs
import Submission.Work.FTS.EllSol.EllPkgAux.kernelJensen
import Submission.Work.FTS.EllSol.EllPkgAux.logJensen
import Submission.Work.FTS.EllSol.EllPkgAux.wExpCmp
import Submission.Work.FTS.EllSol.EllPkgAux.KernelAux
import Submission.Work.FTS.EllSol.EllPkgAux.MollDom.mmDefs
import Submission.Work.FTS.ClassC.UopGenAux.wsq_sKer_log_integral_le

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology ENNReal
open MeasureTheory Set Filter

namespace Work.FTS.EllSol.EllPkgAux.MollDom

open Work.FTS.EllSol.PkgK5.K5c

set_option maxHeartbeats 4000000
set_option maxRecDepth 2000

local notation "Iθ" => Work.Spaces.Iθ
local notation "Iz" => Work.Spaces.Iz
local notation "σθ" => Work.FTS.EllipticEst.thEta

/-! ## The `ℝ≥0∞`-valued vocabulary of the estimate

Everything in the proof of `mollMasterUnif` is nonnegative, so the whole estimate is carried out in
`ℝ≥0∞` (`ofReal` of each kernel and each weight) and only at the very end converted back to a
Bochner statement.  The `mu`-prefixed names are local to this file family. -/

/-- `ofReal` of the square of the radial weight. -/
def muWHat (z : ℝ) : ℝ≥0∞ := ENNReal.ofReal ((Work.Spaces.w z) ^ 2)

/-- `ofReal` of the logarithmic mollification kernel. -/
def muKHat (δ z t : ℝ) : ℝ≥0∞ := ENNReal.ofReal (sKer δ (Real.log z - t))

/-- `ofReal` of the angular three-image kernel. -/
def muJHat (ε θ s : ℝ) : ℝ≥0∞ := ENNReal.ofReal (KJ ε θ s)

/-- `ofReal` of the angular weight `sin(2θ)^{-η}`. -/
def muSigHat (θ : ℝ) : ℝ≥0∞ := ENNReal.ofReal (σθ θ)

/-- `ofReal` of the square of a slice of `X`. -/
def muXsHat (X : ℝ → ℝ → ℝ) (t s : ℝ) : ℝ≥0∞ := ENNReal.ofReal ((X (Real.exp t) s) ^ 2)

/-- The `θ`-integrated angular kernel `∫⁻_θ σ(θ) KJ ε θ s`. -/
def muBHat (ε s : ℝ) : ℝ≥0∞ := ∫⁻ θ in Iθ, muSigHat θ * muJHat ε θ s

/-- The two-kernel pairing of one slice: `∫⁻_t k δ z t (∫⁻_s KJ ε θ s (X(e^t,s))²)`. -/
def muQHat (δ ε : ℝ) (X : ℝ → ℝ → ℝ) (z θ : ℝ) : ℝ≥0∞ :=
  ∫⁻ t, muKHat δ z t * (∫⁻ s in Iθ, muJHat ε θ s * muXsHat X t s)

/-- The `w²`-weighted `σ_η`-functional of `F`, in `ℝ≥0∞`. -/
def muMHat (F : ℝ → ℝ → ℝ) : ℝ≥0∞ :=
  ∫⁻ z in Iz, muWHat z * (∫⁻ θ in Iθ, ENNReal.ofReal ((F z θ) ^ 2 * σθ θ))

/-- The `w²`-weighted two-kernel functional of `X`, in `ℝ≥0∞`. -/
def muNHat (δ ε : ℝ) (X : ℝ → ℝ → ℝ) : ℝ≥0∞ :=
  ∫⁻ z in Iz, muWHat z * (∫⁻ θ in Iθ, muSigHat θ * muQHat δ ε X z θ)

/-! ## The defining equations of the vocabulary (as rewrite rules) -/

lemma muWHat_def (z : ℝ) : muWHat z = ENNReal.ofReal ((Work.Spaces.w z) ^ 2) := rfl
lemma muKHat_def (δ z t : ℝ) : muKHat δ z t = ENNReal.ofReal (sKer δ (Real.log z - t)) := rfl
lemma muJHat_def (ε θ s : ℝ) : muJHat ε θ s = ENNReal.ofReal (KJ ε θ s) := rfl
lemma muSigHat_def (θ : ℝ) : muSigHat θ = ENNReal.ofReal (σθ θ) := rfl
lemma muXsHat_def (X : ℝ → ℝ → ℝ) (t s : ℝ) :
    muXsHat X t s = ENNReal.ofReal ((X (Real.exp t) s) ^ 2) := rfl
lemma muBHat_def (ε s : ℝ) : muBHat ε s = ∫⁻ θ in Iθ, muSigHat θ * muJHat ε θ s := rfl
lemma muQHat_def (δ ε : ℝ) (X : ℝ → ℝ → ℝ) (z θ : ℝ) : muQHat δ ε X z θ =
    ∫⁻ t, muKHat δ z t * (∫⁻ s in Iθ, muJHat ε θ s * muXsHat X t s) := rfl
lemma muMHat_def (F : ℝ → ℝ → ℝ) : muMHat F = ∫⁻ z in Iz,
    muWHat z * (∫⁻ θ in Iθ, ENNReal.ofReal ((F z θ) ^ 2 * σθ θ)) := rfl
lemma muNHat_def (δ ε : ℝ) (X : ℝ → ℝ → ℝ) : muNHat δ ε X = ∫⁻ z in Iz,
    muWHat z * (∫⁻ θ in Iθ, muSigHat θ * muQHat δ ε X z θ) := rfl

/-! ## Elementary facts about the measures, the weights and the kernels -/

/-- `Iz = [0,∞)` and `(0,∞)` carry the same restricted measure. -/
lemma mu_Ioi : volume.restrict Iz = volume.restrict (Set.Ioi (0 : ℝ)) := by
  rw [Work.Spaces.Iz]
  exact (MeasureTheory.Measure.restrict_congr_set
    (MeasureTheory.Ioi_ae_eq_Ici (μ := volume) (a := 0))).symm

lemma mu_measurable_w : Measurable Work.Spaces.w := by
  unfold Work.Spaces.w
  fun_prop

lemma mu_measurable_kHat (δ z : ℝ) : Measurable (fun t : ℝ => muKHat δ z t) := by
  unfold muKHat
  exact ENNReal.measurable_ofReal.comp
    ((Work.FTS.EllSol.K5cAux.continuous_sKer δ).measurable.comp
      (measurable_const.sub measurable_id))

lemma mu_measurable_kHat' (δ : ℝ) : Measurable (fun p : ℝ × ℝ => muKHat δ p.1 p.2) := by
  unfold muKHat
  exact ENNReal.measurable_ofReal.comp
    ((Work.FTS.EllSol.K5cAux.continuous_sKer δ).measurable.comp
      ((Real.measurable_log.comp measurable_fst).sub measurable_snd))

lemma mu_measurable_KJhat (ε : ℝ) : Measurable (fun p : ℝ × ℝ => muJHat ε p.1 p.2) := by
  unfold muJHat
  exact ENNReal.measurable_ofReal.comp (Work.FTS.EllSol.EllPkgAux.continuous_KJ ε).measurable

lemma mu_aemeasurable_sigHat : AEMeasurable muSigHat (volume.restrict Iθ) :=
  ENNReal.measurable_ofReal.comp_aemeasurable
    (Work.FTS.EllipticEst.integrableOn_thEta.1).aemeasurable

lemma mu_aemeasurable_XsHat {X : ℝ → ℝ → ℝ}
    (hXmeas : AEMeasurable (fun p : ℝ × ℝ => X (Real.exp p.1) p.2)
      (volume.prod (volume.restrict Iθ))) :
    AEMeasurable (fun p : ℝ × ℝ => muXsHat X p.1 p.2)
      (volume.prod (volume.restrict Iθ)) := by
  unfold muXsHat
  exact ENNReal.measurable_ofReal.comp_aemeasurable (hXmeas.pow_const 2)

/-- The product of the angular kernel and the slice square, as `ofReal` of the product. -/
lemma muJHat_mul_muXsHat (X : ℝ → ℝ → ℝ) (ε θ t s : ℝ) (hε : 0 < ε) :
    muJHat ε θ s * muXsHat X t s = ENNReal.ofReal (KJ ε θ s * (X (Real.exp t) s) ^ 2) := by
  rw [muJHat_def, muXsHat_def]
  exact (ENNReal.ofReal_mul (KJ_nonneg hε θ s)).symm

/-- The product of the slice square and the angular weight, as `ofReal` of the product. -/
lemma muXsHat_mul_muSigHat (X : ℝ → ℝ → ℝ) (t s : ℝ) :
    muXsHat X t s * muSigHat s = ENNReal.ofReal ((X (Real.exp t) s) ^ 2 * σθ s) := by
  rw [muXsHat_def, muSigHat_def]
  exact (ENNReal.ofReal_mul (sq_nonneg _)).symm

/-- The product of the radial weight and the log-mollification kernel, as `ofReal`. -/
lemma muWHat_mul_muKHat (δ z t : ℝ) :
    muWHat z * muKHat δ z t
      = ENNReal.ofReal ((Work.Spaces.w z) ^ 2 * sKer δ (Real.log z - t)) := by
  rw [muWHat_def, muKHat_def]
  exact (ENNReal.ofReal_mul (sq_nonneg _)).symm

/-- The product of the angular weight and the angular kernel, as `ofReal`. -/
lemma muSigHat_mul_muJHat (ε θ s : ℝ) (hε : 0 < ε) :
    muSigHat θ * muJHat ε θ s = ENNReal.ofReal (σθ θ * KJ ε θ s) := by
  rw [muSigHat_def, muJHat_def]
  exact (ENNReal.ofReal_mul' (KJ_nonneg hε θ s)).symm

/-- `muWHat z * ofReal u = ofReal (w z² * u)`. -/
lemma muWHat_mul_ofReal (u : ℝ) (hu : 0 ≤ u) (z : ℝ) :
    muWHat z * ENNReal.ofReal u = ENNReal.ofReal ((Work.Spaces.w z) ^ 2 * u) := by
  rw [muWHat_def]
  exact (ENNReal.ofReal_mul (sq_nonneg _)).symm

/-- The `s`-functional of `X` at fixed `t`, as `ofReal` of the honest slice functional. -/
lemma mu_VsHat_eq {X : ℝ → ℝ → ℝ}
    (hXhon : ∀ z : ℝ, 0 < z → IntegrableOn (fun θ : ℝ => (X z θ) ^ 2 * σθ θ) Iθ) (t : ℝ) :
    (∫⁻ s in Iθ, muXsHat X t s * muSigHat s) = ENNReal.ofReal (MmV X t) := by
  have hInt : IntegrableOn (fun s : ℝ => (X (Real.exp t) s) ^ 2 * σθ s) Iθ :=
    hXhon (Real.exp t) (Real.exp_pos t)
  have hnn : 0 ≤ᵐ[volume.restrict Iθ]
      (fun s : ℝ => (X (Real.exp t) s) ^ 2 * σθ s) :=
    MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc
      (fun s hs => mul_nonneg (sq_nonneg _) (Work.FTS.EllipticEst.thEta_nonneg hs))
  have hfun : (fun s : ℝ => muXsHat X t s * muSigHat s)
      = fun s : ℝ => ENNReal.ofReal ((X (Real.exp t) s) ^ 2 * σθ s) := by
    funext s
    exact muXsHat_mul_muSigHat X t s
  rw [hfun]
  exact (MeasureTheory.ofReal_integral_eq_lintegral_ofReal hInt hnn).symm

/-- **The `KJ`-slice conversion.**  If `s ↦ KJ ε θ s (X(e^t,s))²` is integrable on `Iθ`, then
`ofReal` of its Bochner integral is the lintegral of `muJHat · muXsHat`. -/
lemma mu_ofReal_integral_eq_lintegral_KJ {X : ℝ → ℝ → ℝ} (ε θ t : ℝ) (hε : 0 < ε)
    (hInt : IntegrableOn (fun s : ℝ => KJ ε θ s * (X (Real.exp t) s) ^ 2) Iθ) :
    ENNReal.ofReal (∫ s in Iθ, KJ ε θ s * (X (Real.exp t) s) ^ 2)
      = ∫⁻ s in Iθ, muJHat ε θ s * muXsHat X t s := by
  refine (MeasureTheory.ofReal_integral_eq_lintegral_ofReal hInt ?_).trans ?_
  · exact MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc
      (fun s _ => mul_nonneg (KJ_nonneg hε θ s) (sq_nonneg _))
  · have hfun : (fun s : ℝ => ENNReal.ofReal (KJ ε θ s * (X (Real.exp t) s) ^ 2))
        = fun s : ℝ => muJHat ε θ s * muXsHat X t s := by
      funext s
      exact (muJHat_mul_muXsHat X ε θ t s hε).symm
    rw [hfun]


/-- `ofReal u * muSigHat θ = ofReal (u * σθ θ)`. -/
lemma mu_ofReal_mul_muSigHat (u : ℝ) (hu : 0 ≤ u) (θ : ℝ) :
    ENNReal.ofReal u * muSigHat θ = ENNReal.ofReal (u * σθ θ) := by
  rw [muSigHat_def]
  exact (ENNReal.ofReal_mul hu).symm

/-- `(3 : ℝ≥0∞) ≠ ⊤`. -/
lemma mu_three_ne_top : (3 : ℝ≥0∞) ≠ ⊤ := by norm_num

/-- Squaring is monotone in `ℝ≥0∞`. -/
lemma mu_sq_le_sq {a b : ℝ≥0∞} (h : a ≤ b) : a ^ 2 ≤ b ^ 2 := by
  rw [sq, sq]
  exact mul_le_mul' h h

/-- Continuity of the angular slice `s ↦ KJ ε θ s`. -/
lemma mu_continuous_KJ_slice (ε θ : ℝ) : Continuous (fun s : ℝ => KJ ε θ s) := by
  have h1 : Continuous (fun s : ℝ => (θ, s)) := continuous_const.prodMk continuous_id
  have h2 := (Work.FTS.EllSol.EllPkgAux.continuous_KJ ε).comp h1
  have hfun : ((fun p : ℝ × ℝ => KJ ε p.1 p.2) ∘ fun s : ℝ => (θ, s)) = fun s : ℝ => KJ ε θ s := by
    funext s
    rfl
  rwa [hfun] at h2

/-! ## The two measure-theoretic tools -/

/-- For a nonnegative real function, `ofReal` of the Bochner integral is at most the lintegral of
the `ofReal`s (no integrability hypothesis needed). -/
lemma mu_ofReal_integral_le_lintegral {α : Type*} [MeasurableSpace α] {μ : Measure α} {f : α → ℝ}
    (hf : 0 ≤ᵐ[μ] f) :
    ENNReal.ofReal (∫ x, f x ∂μ) ≤ ∫⁻ x, ENNReal.ofReal (f x) ∂μ := by
  by_cases h : Integrable f μ
  · rw [MeasureTheory.ofReal_integral_eq_lintegral_ofReal h hf]
  · rw [MeasureTheory.integral_undef h, ENNReal.ofReal_zero]
    exact zero_le

/-- **Cauchy–Schwarz in `ℝ≥0∞`** (the `√k`–`√k·g` splitting of `∫⁻ k·g`). -/
lemma mu_ofReal_cs {α : Type*} [MeasurableSpace α] {μ : Measure α} {k g : α → ℝ}
    (hk : AEMeasurable k μ) (hg : AEMeasurable g μ) (hknn : ∀ a, 0 ≤ k a)
    (hgnn : ∀ a, 0 ≤ g a) :
    (∫⁻ a, ENNReal.ofReal (k a) * ENNReal.ofReal (g a) ∂μ) ^ 2
      ≤ (∫⁻ a, ENNReal.ofReal (k a) ∂μ)
        * (∫⁻ a, ENNReal.ofReal (k a) * (ENNReal.ofReal (g a)) ^ 2 ∂μ) := by
  have hks : AEMeasurable (fun a => Real.sqrt (k a)) μ :=
    Real.continuous_sqrt.measurable.comp_aemeasurable hk
  have hf : AEMeasurable (fun a => ENNReal.ofReal (Real.sqrt (k a))) μ :=
    ENNReal.measurable_ofReal.comp_aemeasurable hks
  have hg' : AEMeasurable (fun a => ENNReal.ofReal (Real.sqrt (k a) * g a)) μ :=
    ENNReal.measurable_ofReal.comp_aemeasurable (hks.mul hg)
  have hhold := ENNReal.lintegral_mul_le_Lp_mul_Lq μ (p := 2) (q := 2)
    Real.HolderConjugate.two_two hf hg'
  simp only [Pi.mul_apply] at hhold
  have hL : (∫⁻ a, (fun x => ENNReal.ofReal (Real.sqrt (k x))) a
        * (fun x => ENNReal.ofReal (Real.sqrt (k x) * g x)) a ∂μ)
      = ∫⁻ a, ENNReal.ofReal (k a) * ENNReal.ofReal (g a) ∂μ := by
    refine lintegral_congr (fun a => ?_)
    have h1 : ENNReal.ofReal (Real.sqrt (k a)) * ENNReal.ofReal (Real.sqrt (k a) * g a)
        = ENNReal.ofReal (Real.sqrt (k a) * (Real.sqrt (k a) * g a)) :=
      (ENNReal.ofReal_mul (Real.sqrt_nonneg (k a))).symm
    rw [h1, ← ENNReal.ofReal_mul (hknn a)]
    congr 1
    rw [← mul_assoc, Real.mul_self_sqrt (hknn a)]
  rw [hL] at hhold
  have hA : (∫⁻ a, (fun x => ENNReal.ofReal (Real.sqrt (k x))) a ^ (2 : ℝ) ∂μ)
      = ∫⁻ a, ENNReal.ofReal (k a) ∂μ := by
    refine lintegral_congr (fun a => ?_)
    rw [ENNReal.ofReal_rpow_of_nonneg (Real.sqrt_nonneg (k a)) (by norm_num : (0 : ℝ) ≤ 2),
      Real.rpow_two, Real.sq_sqrt (hknn a)]
  have hB : (∫⁻ a, (fun x => ENNReal.ofReal (Real.sqrt (k x) * g x)) a ^ (2 : ℝ) ∂μ)
      = ∫⁻ a, ENNReal.ofReal (k a) * (ENNReal.ofReal (g a)) ^ 2 ∂μ := by
    refine lintegral_congr (fun a => ?_)
    rw [ENNReal.ofReal_rpow_of_nonneg (mul_nonneg (Real.sqrt_nonneg (k a)) (hgnn a))
        (by norm_num : (0 : ℝ) ≤ 2), Real.rpow_two, mul_pow, Real.sq_sqrt (hknn a)]
    rw [← ENNReal.ofReal_pow (hgnn a) 2, ← ENNReal.ofReal_mul (hknn a)]
  rw [hA, hB] at hhold
  calc (∫⁻ a, ENNReal.ofReal (k a) * ENNReal.ofReal (g a) ∂μ) ^ 2
      ≤ ((∫⁻ a, ENNReal.ofReal (k a) ∂μ) ^ (1 / 2 : ℝ)
          * (∫⁻ a, ENNReal.ofReal (k a) * (ENNReal.ofReal (g a)) ^ 2 ∂μ) ^ (1 / 2 : ℝ)) ^ 2 := by
        rw [sq, sq]
        exact mul_le_mul' hhold hhold
    _ = (∫⁻ a, ENNReal.ofReal (k a) ∂μ)
          * (∫⁻ a, ENNReal.ofReal (k a) * (ENNReal.ofReal (g a)) ^ 2 ∂μ) := by
        rw [mul_pow]
        congr 1
        · rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul,
            show (1 / 2 : ℝ) * ((2 : ℕ) : ℝ) = 1 by norm_num, ENNReal.rpow_one]
        · rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul,
            show (1 / 2 : ℝ) * ((2 : ℕ) : ℝ) = 1 by norm_num, ENNReal.rpow_one]

/-- The logarithmic kernel has total mass `1` in `ℝ≥0∞`. -/
lemma mu_kHat_lintegral_one (δ : ℝ) (hδ : 0 < δ) (z : ℝ) :
    ∫⁻ t, muKHat δ z t = 1 := by
  have hint : Integrable (fun t : ℝ => sKer δ (Real.log z - t)) volume :=
    Work.FTS.EllSol.EllPkgAux.lj_sKer_integrable_sub hδ (Real.log z)
  have hnn : 0 ≤ᵐ[volume] (fun t : ℝ => sKer δ (Real.log z - t)) :=
    Eventually.of_forall (fun t => sKer_nonneg hδ _)
  have h1 : (∫⁻ t, ENNReal.ofReal (sKer δ (Real.log z - t)))
      = ENNReal.ofReal (∫ t, sKer δ (Real.log z - t)) :=
    (MeasureTheory.ofReal_integral_eq_lintegral_ofReal hint hnn).symm
  have h2 : (∫ t, sKer δ (Real.log z - t)) = 1 :=
    Work.FTS.EllSol.EllPkgAux.lj_sKer_integral_sub δ hδ (Real.log z)
  simp only [muKHat]
  rw [h1, h2, ENNReal.ofReal_one]

end Work.FTS.EllSol.EllPkgAux.MollDom
