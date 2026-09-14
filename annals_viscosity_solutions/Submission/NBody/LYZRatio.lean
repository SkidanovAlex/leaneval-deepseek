import Submission.NBody.LYZUnif
import Submission.NBody.EnergyAe
import Submission.NBody.LYZCone
import Submission.Commons.Analysis.InnerProductSpace.norm_sub_smul_sq_le_ratio
import Mathlib

/-!
# Section 7 of Liu--Yan--Zhou: the large-time behaviour of `m_λ`-geodesics

This module formalises Liu--Yan--Zhou's Lemma 7.1.  For an `h`-minimiser `γ` on `[0, τ]` with
`γ τ = x* + 2^n • a` which satisfies the estimates of Lemma `unif` (`exists_lyz_unif`), and for
`t ∈ [σ n₀, τ]`, one has

* `γ t` is collision free (`flatgz`, Liu--Yan--Zhou's Lemma 3.4);
* `∫₀^t ‖γ̇‖²_[m] = A_h(γ|[0,t]) ≤ 2h |γ t - x*|_[m] (1 + Ψ̄²) ≤ 8 h t` (7.1);
* `1/2 ≤ |γ t - x*|_[m] / (√(2h) t) ≤ 1 + Ψ̄²` (7.2);
* `|γ t - x* - √(2h) t a|²_[m] / (√(2h) t)² ≤ 2^16 Ψ̄(√(2h) t / 2)²` (7.3).

The two outputs used downstream are the uniform `L²` bound (7.1) and the asymptotic shape (7.3);
the ratio bounds (7.2) give the a priori location of the crossing times `σ_j`.
-/

open ViscositySolutions
open Filter Gradient Real Set Metric
open scoped BigOperators Topology ENNReal
open MeasureTheory

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1600000

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable [Nontrivial E]
variable {N : ℕ}

namespace Submission.NBody

/-! ## The mass inner product and the mass norm -/

/-- The mass inner product is the Euclidean inner product of the mass-scaled configurations. -/
lemma massInner_eq_inner_massScale {m : Fin N → ℝ} (hm : ∀ i, 0 ≤ m i) (v w : EN E N) :
    massInner m v w = inner ℝ (massScale m v) (massScale m w) := by
  rw [massInner, PiLp.inner_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [massScale_apply, massScale_apply, real_inner_smul_left, real_inner_smul_right,
    ← mul_assoc, Real.mul_self_sqrt (hm i)]

/-- The mass inner product of `v` with itself is the square of the mass norm. -/
lemma massInner_self_eq_weightedNorm_sq {m : Fin N → ℝ} (hm : ∀ i, 0 ≤ m i) (v : EN E N) :
    massInner m v v = ‖v‖_[m] ^ 2 := by
  rw [massInner_eq_inner_massScale hm, real_inner_self_eq_norm_sq,
    weightedNorm_eq_norm_massScale hm]

lemma massInner_add_left {m : Fin N → ℝ} (hm : ∀ i, 0 ≤ m i) (u v w : EN E N) :
    massInner m (u + v) w = massInner m u w + massInner m v w := by
  rw [massInner_eq_inner_massScale hm, massInner_eq_inner_massScale hm,
    massInner_eq_inner_massScale hm, massScale_add, inner_add_left]

lemma massInner_smul_left {m : Fin N → ℝ} (hm : ∀ i, 0 ≤ m i) (c : ℝ) (u w : EN E N) :
    massInner m (c • u) w = c * massInner m u w := by
  rw [massInner_eq_inner_massScale hm, massInner_eq_inner_massScale hm, massScale_smul,
    inner_smul_left]
  simp

/-- The elementary identity `⟪u, a⟫ = ‖u‖ * (1 - ‖‖u‖⁻¹ • u - a‖² / 2)` for a unit vector `a`. -/
lemma inner_eq_norm_mul_sub_half {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    {u a : F} (hd : 0 < ‖u‖) (ha : ‖a‖ = 1) :
    inner ℝ u a = ‖u‖ * (1 - (1 / 2) * ‖(‖u‖)⁻¹ • u - a‖ ^ 2) := by
  have h1 : ‖(‖u‖)⁻¹ • u - a‖ ^ 2 = 2 - 2 * (‖u‖)⁻¹ * inner ℝ u a := by
    rw [norm_sub_sq_real, real_inner_smul_left, norm_smul, Real.norm_eq_abs,
      abs_of_pos (inv_pos.mpr hd), ha]
    field_simp
    ring
  rw [h1]
  field_simp
  ring

/-- The expansion of the square of a mass norm. -/
lemma weightedNorm_add_smul_sq {m : Fin N → ℝ} (hm : ∀ i, 0 ≤ m i) (u a : EN E N) (c : ℝ) :
    ‖u + c • a‖_[m] ^ 2 = ‖u‖_[m] ^ 2 + 2 * c * massInner m u a + c ^ 2 * ‖a‖_[m] ^ 2 := by
  rw [weightedNorm_eq_norm_massScale hm, massScale_add, massScale_smul, norm_add_sq_real,
    massInner_eq_inner_massScale hm, weightedNorm_eq_norm_massScale hm,
    weightedNorm_eq_norm_massScale hm, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs,
    real_inner_smul_right]
  ring

/-- The mass-norm form of `⟪u, a⟫ = ‖u‖ * (1 - ‖‖u‖⁻¹ • u - a‖² / 2)`. -/
lemma massInner_eq_weightedNorm_mul_sub_half {m : Fin N → ℝ} (hm : ∀ i, 0 ≤ m i)
    {u a : EN E N} (hd : 0 < ‖u‖_[m]) (ha : ‖a‖_[m] = 1) :
    massInner m u a = ‖u‖_[m] * (1 - (1 / 2) * ‖(‖u‖_[m])⁻¹ • u - a‖_[m] ^ 2) := by
  have hsu : ‖massScale m u‖ = ‖u‖_[m] := (weightedNorm_eq_norm_massScale hm u).symm
  have hsa : ‖massScale m a‖ = 1 := by rw [← weightedNorm_eq_norm_massScale hm a, ha]
  have hsub : massScale m ((‖u‖_[m])⁻¹ • u - a)
      = (‖u‖_[m])⁻¹ • massScale m u - massScale m a := by
    rw [massScale_sub, massScale_smul]
  have hnorm : ‖(‖u‖_[m])⁻¹ • massScale m u - massScale m a‖
      = ‖(‖u‖_[m])⁻¹ • u - a‖_[m] := by
    rw [← hsub, weightedNorm_eq_norm_massScale hm ((‖u‖_[m])⁻¹ • u - a)]
  rw [massInner_eq_inner_massScale hm]
  rw [inner_eq_norm_mul_sub_half (u := massScale m u) (a := massScale m a) (by rwa [hsu]) hsa,
    hsu, hnorm]

/-! ## A Cauchy--Schwarz (Hölder) bound for the mass norm -/

/-- **Hölder-`1/2` bound for the mass norm along an absolutely continuous curve**: if the `∫⁻` of
the squared mass norm of the derivative is at most `A`, then the mass displacement is at most
`√A √(b - a)`. -/
theorem weightedNorm_sub_le_sqrt_mul_sqrt {m : Fin N → ℝ} (hm : ∀ i, 0 < m i)
    {γ : ℝ → EN E N} {a b A : ℝ} (hab : a ≤ b) (hA : 0 ≤ A)
    (hac : AbsolutelyContinuousOnInterval γ a b)
    (h : ∫⁻ t in Set.Ioc a b, ENNReal.ofReal (‖deriv γ t‖_[m] ^ 2) ≤ ENNReal.ofReal A) :
    ‖γ b - γ a‖_[m] ≤ Real.sqrt A * Real.sqrt (b - a) := by
  letI : MeasurableSpace E := borel E
  haveI : BorelSpace E := ⟨rfl⟩
  have hf : AEMeasurable (fun t : ℝ => ENNReal.ofReal (‖deriv γ t‖_[m]))
      (volume.restrict (Set.Ioc a b)) := by
    refine ENNReal.continuous_ofReal.measurable.comp_aemeasurable ?_
    refine (continuous_weightedNorm' m).measurable.comp_aemeasurable ?_
    exact (Commons.MeasureTheory.Integral.aestronglyMeasurable_deriv_of_absolutelyContinuousOnInterval
      hac).aemeasurable
  have hg : AEMeasurable (fun _ : ℝ => (1 : ℝ≥0∞)) (volume.restrict (Set.Ioc a b)) :=
    aemeasurable_const
  have hpq : (2 : ℝ).HolderConjugate 2 := Real.holderConjugate_iff.mpr ⟨by norm_num, by norm_num⟩
  have hholder := ENNReal.lintegral_mul_le_Lp_mul_Lq
    (volume.restrict (Set.Ioc a b)) hpq hf hg
  simp only [Pi.mul_apply, mul_one] at hholder
  have hsq : ∫⁻ t in Set.Ioc a b, (ENNReal.ofReal (‖deriv γ t‖_[m])) ^ (2:ℝ)
      = ∫⁻ t in Set.Ioc a b, ENNReal.ofReal (‖deriv γ t‖_[m] ^ 2) := by
    refine lintegral_congr fun t => ?_
    rw [ENNReal.rpow_two, ENNReal.ofReal_pow (weightedNorm_nonneg m _)]
  have hone : ∫⁻ _t in Set.Ioc a b, (1 : ℝ≥0∞) ^ (2:ℝ) = ENNReal.ofReal (b - a) := by
    rw [show (fun _ : ℝ => (1:ℝ≥0∞) ^ (2:ℝ)) = fun _ => 1 by funext t; simp,
      lintegral_one, Measure.restrict_apply_univ, Real.volume_Ioc]
  rw [hsq, hone] at hholder
  have hmain : ∫⁻ t in Set.Ioc a b, ENNReal.ofReal (‖deriv γ t‖_[m])
      ≤ ENNReal.ofReal (Real.sqrt A * Real.sqrt (b - a)) := by
    calc ∫⁻ t in Set.Ioc a b, ENNReal.ofReal (‖deriv γ t‖_[m])
        ≤ (∫⁻ t in Set.Ioc a b, ENNReal.ofReal (‖deriv γ t‖_[m] ^ 2)) ^ ((1:ℝ)/2)
            * (ENNReal.ofReal (b - a)) ^ ((1:ℝ)/2) := hholder
      _ ≤ (ENNReal.ofReal A) ^ ((1:ℝ)/2) * (ENNReal.ofReal (b - a)) ^ ((1:ℝ)/2) :=
          mul_le_mul' (ENNReal.rpow_le_rpow h (by norm_num))
            (ENNReal.rpow_le_rpow le_rfl (by norm_num))
      _ = ENNReal.ofReal (Real.sqrt A) * ENNReal.ofReal (Real.sqrt (b - a)) := by
          rw [ENNReal.ofReal_rpow_of_nonneg hA (by norm_num),
            ENNReal.ofReal_rpow_of_nonneg (sub_nonneg.mpr hab) (by norm_num),
            ← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow]
      _ = ENNReal.ofReal (Real.sqrt A * Real.sqrt (b - a)) :=
          (ENNReal.ofReal_mul (Real.sqrt_nonneg _)).symm
  have h1 := ofReal_weightedNorm_sub_le_lintegral hm hab hac
  exact (ENNReal.ofReal_le_ofReal_iff
    (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))).mp (h1.trans hmain)

/-! ## The elementary estimate behind (7.3) -/

/-! ## Liu--Yan--Zhou, Lemma 7.1 -/

/-- **Liu--Yan--Zhou's Lemma 7.1** (pointwise form, at a time `t ∈ [0, τ]` carrying the
estimates of Lemma `unif`).  With `x* = γ 0 + s₀ • a`, `D = |γ t - x*|_[m]`:

* `γ t` is `(9/10) ν`-separated;
* `∫₀^t |γ̇|²_[m] = A_h(γ|[0,t]) ≤ √(2h) D (1 + Ψ̄(D)²)`;
* `∫₀^t |γ̇|²_[m] ≤ 8 h t`;
* `√(2h) t / (1 + Ψ̄(D)²) ≤ D ≤ √(2h) t (1 + Ψ̄(D)²)`;
* `|γ t - x* - √(2h) t a|²_[m] ≤ 2^18 Ψ̄(√(2h) t / 2)² (√(2h) t)²`. -/
theorem lyz_ratio_estimates {m : Fin N → ℝ} {h : ℝ} (hh : 0 < h) (hm : ∀ i, 0 < m i)
    {xstar a : EN E N} {ν s₀ θ : ℝ} (hν : 0 < ν) (hsep : Separated a ν) (ha : ‖a‖_[m] = 1)
    {K : ℝ} (hK : 0 < K) (hKn : ∀ y : EN E N, ‖y‖ ≤ K * ‖y‖_[m])
    (hKθ : K * θ ≤ ν / 16) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1)
    {A B M : ℝ} (hA0 : 0 ≤ A) (hB0 : 0 ≤ B) (hM0 : 0 ≤ M)
    {Ψb : ℝ → ℝ} (hΨbnn : ∀ t, 0 ≤ Ψb t)
    (hslow : ∀ s t, 0 < s → s ≤ t → t ≤ 2 * s → Ψb t ≤ 2 * Ψb s)
    (hrel : ∀ t, 0 < t → Real.sqrt (lyzPsi A B M t / t) ≤ Ψb t)
    {γ : ℝ → EN E N} {τ t : ℝ} (hτ : 0 < τ) (ht : 0 < t) (htτ : t ≤ τ)
    (hΨb1 : Ψb (‖γ t - xstar‖_[m]) ≤ 1)
    (hac : AbsolutelyContinuousOnInterval γ 0 τ)
    (hfin : actionOn m h γ 0 τ < ⊤)
    (hmin : IsHMinimizer m h γ 0 τ)
    (hΦ : actionPot m h (γ 0) xstar < ⊤)
    (hAφ : (Real.sqrt (2 * h))⁻¹ * (actionPot m h (γ 0) xstar).toReal ≤ A)
    (hpotB : ∀ b : EN E N, ‖b‖_[m] = 1 → ‖b - a‖_[m] ≤ θ → ∀ T : ℝ, 0 ≤ T →
        ∫ s in (0:ℝ)..T, U m (xstar + s • b) ≤ (2 * h) * B * Real.log (2 * T + 2 * M + 1))
    (hncB : ∀ b : EN E N, ‖b‖_[m] = 1 → ‖b - a‖_[m] ≤ θ → ∀ s : ℝ, 0 ≤ s →
        WithoutCollisions (xstar + s • b))
    (hxstar : xstar = γ 0 + s₀ • a) (hs₀1 : 1 ≤ s₀)
    (hs₀K : ‖γ 0‖_[m] + 40 * K * ‖γ 0‖_[m] / ν ≤ s₀)
    (hs₀K2 : 50 * K * ‖γ 0‖_[m] / ν ≤ s₀)
    (hDpos0 : 0 < ‖γ t - xstar‖_[m])
    (hdirm0 : ‖(‖γ t - xstar‖_[m])⁻¹ • (γ t - xstar) - a‖_[m]
        ≤ 64 * Ψb (‖γ t - xstar‖_[m]))
    (hconeΨ0 : 64 * Ψb (‖γ t - xstar‖_[m]) ≤ θ)
    (hlenb0 : massLength m γ 0 t ≤ ‖γ t - xstar‖_[m] * (1 + Ψb (‖γ t - xstar‖_[m]) ^ 2)) :
    Separated (γ t) ((9:ℝ) / 10 * ν) ∧
    (∫ s in (0:ℝ)..t, ‖deriv γ s‖_[m] ^ 2 = (actionOn m h γ 0 t).toReal) ∧
    ((actionOn m h γ 0 t).toReal
        ≤ Real.sqrt (2 * h) * (‖γ t - xstar‖_[m] * (1 + Ψb (‖γ t - xstar‖_[m]) ^ 2))) ∧
    (∫ s in (0:ℝ)..t, ‖deriv γ s‖_[m] ^ 2 ≤ 8 * h * t) ∧
    (Real.sqrt (2 * h) * t / (1 + Ψb (‖γ t - xstar‖_[m]) ^ 2) ≤ ‖γ t - xstar‖_[m]) ∧
    (‖γ t - xstar‖_[m] ≤ Real.sqrt (2 * h) * t * (1 + Ψb (‖γ t - xstar‖_[m]) ^ 2)) ∧
    (‖γ t - xstar - (Real.sqrt (2 * h) * t) • a‖_[m] ^ 2
      ≤ 2 ^ 22 * Ψb (Real.sqrt (2 * h) * t / 2) ^ 2 * (Real.sqrt (2 * h) * t) ^ 2) ∧
    (∫⁻ s in Set.Ioc (0:ℝ) t, ENNReal.ofReal (‖deriv γ s‖_[m] ^ 2)
      ≤ ENNReal.ofReal (8 * h * t)) := by
  have hm0 : ∀ i, 0 ≤ m i := fun i => (hm i).le
  set D : ℝ := ‖γ t - xstar‖_[m] with hDdef
  have hDpos : 0 < D := by rw [hDdef]; exact hDpos0
  have hdirm : ‖D⁻¹ • (γ t - xstar) - a‖_[m] ≤ 64 * Ψb D := by rw [hDdef]; exact hdirm0
  have hconeΨ : 64 * Ψb D ≤ θ := by rw [hDdef]; exact hconeΨ0
  have hlenb : massLength m γ 0 t ≤ D * (1 + Ψb D ^ 2) := by rw [hDdef]; exact hlenb0
  have hΨbD0 : 0 ≤ Ψb D := hΨbnn D
  have hΨbD1 : Ψb D ≤ 1 := by rw [hDdef]; exact hΨb1
  have hsqrt : 0 < Real.sqrt (2 * h) := Real.sqrt_pos.mpr (by linarith)
  have hsq2h : Real.sqrt (2 * h) ^ 2 = 2 * h := Real.sq_sqrt (by linarith)
  set b : EN E N := D⁻¹ • (γ t - xstar) with hbdef
  have hbca : ‖b - a‖_[m] ≤ θ := by
    rw [hbdef]; exact hdirm.trans hconeΨ
  have hbnorm : ‖b‖_[m] = 1 := by
    rw [hbdef, weightedNorm_smul hm0, abs_of_pos (inv_pos.mpr hDpos), ← hDdef,
      inv_mul_cancel₀ hDpos.ne']
  have hbγ : xstar + D • b = γ t := by
    rw [hbdef, smul_smul, mul_inv_cancel₀ hDpos.ne', one_smul, add_sub_cancel]
  have hsepκ : Separated (γ t) ((9:ℝ) / 10 * ν) := by
    have h := separated_cone_ray hm hK hKn hν hsep ha hbnorm hθ0 hbca hKθ hs₀1 hs₀K hs₀K2
      D hDpos.le
    rwa [← hxstar, hbγ] at h
  have hncseg : ∀ s ∈ Set.Icc (0:ℝ) D, WithoutCollisions (xstar + s • b) :=
    fun s hs => hncB b hbnorm hbca s hs.1
  have hmin_t : IsHMinimizer m h γ 0 t := IsHMinimizer.sub_left_of_le hac hmin hfin ht htτ
  have hac_t : AbsolutelyContinuousOnInterval γ 0 t := hac.mono (by
    rw [uIcc_of_le ht.le, uIcc_of_le hτ.le]
    exact Set.Icc_subset_Icc_right htτ)
  have hfin_t : actionOn m h γ 0 t < ⊤ := actionOn_lt_top_of_le ht.le htτ hfin
  have hfc_t : actionPot m h (γ 0) (γ t) < ⊤ := hmin_t ▸ hfin_t
  have hnull : (volume.restrict (Set.Ioc (0:ℝ) t)) ({0, t} : Set ℝ) = 0 := by
    rw [Measure.restrict_apply (Set.toFinite ({0, t} : Set ℝ)).measurableSet]
    exact measure_mono_null Set.inter_subset_left ((Set.toFinite _).measure_zero volume)
  -- the energy identity
  have hE : ∫ s in (0:ℝ)..t, ‖deriv γ s‖_[m] ^ 2 = (actionOn m h γ 0 t).toReal :=
    integral_weightedNorm_sq_eq_actionOn_of_min hm hh.le ht hac_t hmin_t hfc_t
  -- the upper bound on the action
  have hlog : 0 ≤ Real.log (2 * D + 2 * M + 1) := Real.log_nonneg (by linarith)
  have hpotD : ∫ s in (0:ℝ)..D, U m (xstar + s • b)
      ≤ (2 * h) * B * Real.log (2 * D + 2 * M + 1) := hpotB b hbnorm hbca D hDpos.le
  have hrelD : Real.sqrt (lyzPsi A B M D / D) ≤ Ψb D := hrel D hDpos
  have hA2 : (actionOn m h γ 0 t).toReal ≤ Real.sqrt (2 * h) * (D * (1 + Ψb D ^ 2)) :=
    actionOn_toReal_le_sqrt_mul hh hm0 hDpos hmin_t hbγ.symm hbnorm hncseg hΦ hAφ hpotD hlog
      hA0 hB0 hM0 hrelD
  -- the limit of real/`ℝ≥0∞` integrals
  have hbound_lintegral : ∫⁻ s in Set.Ioc (0:ℝ) t, ENNReal.ofReal (‖deriv γ s‖_[m] ^ 2)
      ≤ ENNReal.ofReal ((actionOn m h γ 0 t).toReal) := by
    have h1 : ∫⁻ s in Set.Ioc (0:ℝ) t, ENNReal.ofReal (‖deriv γ s‖_[m] ^ 2)
        ≤ actionOn m h γ 0 t := by
      rw [actionOn]
      refine lintegral_mono_ae ?_
      filter_upwards [ae_restrict_mem measurableSet_Ioc, compl_mem_ae_iff.mpr hnull,
        ae_energy_eq_of_minimizer_Ioc hm hh.le ht hac_t hmin_t hfc_t,
        ae_withoutCollisions_of_actionOn_lt_top hac_t hfin_t] with s hsI hs hEs hncS
      have hne : s ≠ t := fun h => hs (by simp [h])
      have hst : s < t := lt_of_le_of_ne hsI.2 hne
      rw [lagrangian_eq_ofReal_lagR hncS,
        lagR_eq_weightedNorm_sq_of_energy_eq (fun i => (hm i).le) hEs]
    exact h1.trans (le_of_eq (ENNReal.ofReal_toReal hfin_t.ne).symm)
  -- Cauchy--Schwarz
  have hCS : ‖γ t - γ 0‖_[m] ≤ Real.sqrt ((actionOn m h γ 0 t).toReal) * Real.sqrt t :=
    (weightedNorm_sub_le_sqrt_mul_sqrt hm ht.le ENNReal.toReal_nonneg hac_t
      hbound_lintegral).trans_eq (by rw [sub_zero])
  have hu_eq : γ t - γ 0 = (γ t - xstar) + s₀ • a := by
    rw [hxstar]; abel
  have hinner0 : massInner m (γ t - xstar) a
      = D * (1 - (1 / 2) * ‖b - a‖_[m] ^ 2) := by
    have h := massInner_eq_weightedNorm_mul_sub_half hm0 hDpos ha
    rw [← hDdef, ← hbdef] at h
    exact h
  have hinner_nonneg : 0 ≤ massInner m (γ t - xstar) a := by
    rw [hinner0]
    have h3 : ‖b - a‖_[m] ^ 2 ≤ 1 := by
      have h4 := pow_le_pow_left₀ (weightedNorm_nonneg m (b - a)) hbca 2
      nlinarith [h4, hθ0, hθ1]
    nlinarith [hDpos]
  have hD_le : D ≤ ‖γ t - γ 0‖_[m] := by
    have hsq : D ^ 2 ≤ ‖γ t - γ 0‖_[m] ^ 2 := by
      have h2 : ‖γ t - γ 0‖_[m] ^ 2
          = ‖γ t - xstar‖_[m] ^ 2 + 2 * s₀ * massInner m (γ t - xstar) a
            + s₀ ^ 2 * ‖a‖_[m] ^ 2 := by
        rw [hu_eq, weightedNorm_add_smul_sq hm0]
      rw [h2, ← hDdef, ha, one_pow, mul_one]
      nlinarith [hinner_nonneg, hs₀1]
    have h := sq_le_sq.mp hsq
    rwa [abs_of_nonneg hDpos.le, abs_of_nonneg (weightedNorm_nonneg m _)] at h
  -- the upper ratio bound
  have hDhi : D ≤ Real.sqrt (2 * h) * t * (1 + Ψb D ^ 2) := by
    have hsqD : D ^ 2 ≤ (actionOn m h γ 0 t).toReal * t := by
      have h1 : ‖γ t - γ 0‖_[m] ^ 2 ≤ (actionOn m h γ 0 t).toReal * t := by
        calc ‖γ t - γ 0‖_[m] ^ 2
            ≤ (Real.sqrt ((actionOn m h γ 0 t).toReal) * Real.sqrt t) ^ 2 :=
              pow_le_pow_left₀ (weightedNorm_nonneg m _) hCS 2
          _ = (actionOn m h γ 0 t).toReal * t := by
              rw [mul_pow, Real.sq_sqrt ENNReal.toReal_nonneg, Real.sq_sqrt ht.le]
      exact (pow_le_pow_left₀ hDpos.le hD_le 2).trans h1
    have hA' : (actionOn m h γ 0 t).toReal ≤ Real.sqrt (2 * h) * D * (1 + Ψb D ^ 2) := by
      calc (actionOn m h γ 0 t).toReal ≤ Real.sqrt (2 * h) * (D * (1 + Ψb D ^ 2)) := hA2
        _ = Real.sqrt (2 * h) * D * (1 + Ψb D ^ 2) := by ring
    have hkey : D * D ≤ (Real.sqrt (2 * h) * t * (1 + Ψb D ^ 2)) * D := by
      have h3 : (Real.sqrt (2 * h) * t * (1 + Ψb D ^ 2)) * D
          = Real.sqrt (2 * h) * D * (1 + Ψb D ^ 2) * t := by ring
      rw [h3]
      calc D * D = D ^ 2 := by ring
        _ ≤ (actionOn m h γ 0 t).toReal * t := hsqD
        _ ≤ Real.sqrt (2 * h) * D * (1 + Ψb D ^ 2) * t :=
            mul_le_mul_of_nonneg_right hA' ht.le
    exact (mul_le_mul_iff_of_pos_right hDpos).mp hkey
  -- the lower ratio bound
  have hlen_ge : Real.sqrt (2 * h) * t ≤ massLength m γ 0 t := by
    have hae : ∀ᵐ s ∂(volume.restrict (Set.Ioc (0:ℝ) t)),
        Real.sqrt (2 * h) ≤ ‖deriv γ s‖_[m] := by
      filter_upwards [ae_energy_eq_of_minimizer_Ioc hm hh.le ht hac_t hmin_t hfc_t] with s hs
      exact sqrt_two_h_le_weightedNorm_of_energy_eq (fun i => (hm i).le) hs
    have h1 : ∫⁻ s in Set.Ioc (0:ℝ) t, ENNReal.ofReal (Real.sqrt (2 * h))
        ≤ ∫⁻ s in Set.Ioc (0:ℝ) t, ENNReal.ofReal (‖deriv γ s‖_[m]) :=
      lintegral_mono_ae (by filter_upwards [hae] with s hs; exact ENNReal.ofReal_le_ofReal hs)
    have hint : IntervalIntegrable (fun s : ℝ => ‖deriv γ s‖_[m]) volume 0 t :=
      intervalIntegrable_weightedNorm_deriv hm0 ht.le hac_t
    have hbridge : ∫⁻ s in Set.Ioc (0:ℝ) t, ENNReal.ofReal (‖deriv γ s‖_[m])
        = ENNReal.ofReal (massLength m γ 0 t) := by
      rw [massLength, intervalIntegral.integral_of_le ht.le]
      exact (MeasureTheory.ofReal_integral_eq_lintegral_ofReal
        ((intervalIntegrable_iff_integrableOn_Ioc_of_le ht.le).mp hint)
        (Filter.Eventually.of_forall fun s => weightedNorm_nonneg m _)).symm
    rw [hbridge, setLIntegral_const, Real.volume_Ioc, sub_zero] at h1
    rw [← ENNReal.ofReal_mul (Real.sqrt_nonneg _)] at h1
    exact (ENNReal.ofReal_le_ofReal_iff (massLength_nonneg ht.le)).mp h1
  have hDlo : Real.sqrt (2 * h) * t / (1 + Ψb D ^ 2) ≤ D := by
    have h1 : Real.sqrt (2 * h) * t ≤ D * (1 + Ψb D ^ 2) := hlen_ge.trans hlenb
    have h2 : (0:ℝ) < 1 + Ψb D ^ 2 := by positivity
    rw [div_le_iff₀ h2]
    linarith
  -- the uniform `L²` bound
  have hL2 : ∫ s in (0:ℝ)..t, ‖deriv γ s‖_[m] ^ 2 ≤ 8 * h * t := by
    rw [hE]
    have h1 : 1 + Ψb D ^ 2 ≤ 2 := by nlinarith [hΨbD0, hΨbD1]
    have h2 : (actionOn m h γ 0 t).toReal ≤ Real.sqrt (2 * h) * D * 2 := by
      calc (actionOn m h γ 0 t).toReal ≤ Real.sqrt (2 * h) * (D * (1 + Ψb D ^ 2)) := hA2
        _ = Real.sqrt (2 * h) * D * (1 + Ψb D ^ 2) := by ring
        _ ≤ Real.sqrt (2 * h) * D * 2 := by
            exact mul_le_mul_of_nonneg_left h1 (mul_nonneg (Real.sqrt_nonneg _) hDpos.le)
    have h3 : Real.sqrt (2 * h) * D * 2
        ≤ Real.sqrt (2 * h) * (Real.sqrt (2 * h) * t * (1 + Ψb D ^ 2)) * 2 :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hDhi (Real.sqrt_nonneg _)) (by norm_num)
    have h4 : Real.sqrt (2 * h) * (Real.sqrt (2 * h) * t * (1 + Ψb D ^ 2)) * 2
        = 4 * h * t * (1 + Ψb D ^ 2) := by
      rw [show Real.sqrt (2 * h) * (Real.sqrt (2 * h) * t * (1 + Ψb D ^ 2)) * 2
          = 2 * (Real.sqrt (2 * h) * Real.sqrt (2 * h)) * t * (1 + Ψb D ^ 2) by ring,
        show Real.sqrt (2 * h) * Real.sqrt (2 * h) = 2 * h by rw [← pow_two, hsq2h]]
      ring
    have h5 : 4 * h * t * (1 + Ψb D ^ 2) ≤ 8 * h * t := by
      have h6 : 0 ≤ 4 * h * t := by positivity
      nlinarith [h1, h6]
    linarith
  -- the asymptotic shape (7.3)
  have h73 : ‖γ t - xstar - (Real.sqrt (2 * h) * t) • a‖_[m] ^ 2
      ≤ 2 ^ 22 * Ψb (Real.sqrt (2 * h) * t / 2) ^ 2 * (Real.sqrt (2 * h) * t) ^ 2 := by
    have hc : 0 < Real.sqrt (2 * h) * t := mul_pos hsqrt ht
    have hc2 : (0:ℝ) < Real.sqrt (2 * h) * t / 2 := by positivity
    have h1e : (0:ℝ) < 1 + Ψb D ^ 2 := by positivity
    have hu : 0 < ‖massScale m (γ t - xstar)‖ := by
      rw [← weightedNorm_eq_norm_massScale hm0 (γ t - xstar), ← hDdef]; exact hDpos
    have ha' : ‖massScale m a‖ = 1 := by rw [← weightedNorm_eq_norm_massScale hm0 a, ha]
    have hrlo : Real.sqrt (2 * h) * t / (1 + Ψb D ^ 2) ≤ ‖massScale m (γ t - xstar)‖ := by
      rw [← weightedNorm_eq_norm_massScale hm0 (γ t - xstar), ← hDdef]; exact hDlo
    have hrhi : ‖massScale m (γ t - xstar)‖ ≤ Real.sqrt (2 * h) * t * (1 + Ψb D ^ 2) := by
      rw [← weightedNorm_eq_norm_massScale hm0 (γ t - xstar), ← hDdef]; exact hDhi
    have hδ : ‖(‖massScale m (γ t - xstar)‖)⁻¹ • massScale m (γ t - xstar)
        - massScale m a‖ ≤ 64 * Ψb D := by
      have h1 : ‖(‖massScale m (γ t - xstar)‖)⁻¹ • massScale m (γ t - xstar) - massScale m a‖
          = ‖D⁻¹ • (γ t - xstar) - a‖_[m] := by
        rw [← weightedNorm_eq_norm_massScale hm0 (γ t - xstar), ← hDdef, ← massScale_smul,
          ← massScale_sub, ← weightedNorm_eq_norm_massScale hm0]
      rw [h1]; exact hdirm
    have hmain :=
      Commons.Analysis.InnerProductSpace.norm_sub_smul_sq_le_ratio (F := EN E N)
      (u := massScale m (γ t - xstar))
      (a := massScale m a) (c := Real.sqrt (2 * h) * t) (e := Ψb D)
      hc hu ha' hΨbD0 hΨbD1 hrlo hrhi hδ
    have hconv : ‖massScale m (γ t - xstar) - (Real.sqrt (2 * h) * t) • massScale m a‖
        = ‖γ t - xstar - (Real.sqrt (2 * h) * t) • a‖_[m] := by
      rw [← massScale_smul, ← massScale_sub, weightedNorm_eq_norm_massScale hm0]
    rw [hconv] at hmain
    have h6 : 1 + Ψb D ^ 2 ≤ 2 := by nlinarith [hΨbD0, hΨbD1]
    have hDa : Real.sqrt (2 * h) * t / 2 ≤ D := by
      have h : Real.sqrt (2 * h) * t / 2 ≤ Real.sqrt (2 * h) * t / (1 + Ψb D ^ 2) :=
        div_le_div_of_nonneg_left (mul_nonneg (Real.sqrt_nonneg _) ht.le) h1e h6
      linarith
    have hDb : D ≤ 2 * (Real.sqrt (2 * h) * t) := by nlinarith [hDhi, h6]
    have hslow' : Ψb D ≤ 8 * Ψb (Real.sqrt (2 * h) * t / 2) := by
      rcases le_total D (Real.sqrt (2 * h) * t) with hle | hge
      · have hhs := hslow (Real.sqrt (2 * h) * t / 2) D hc2 hDa (by linarith)
        have h8 : 0 ≤ Ψb (Real.sqrt (2 * h) * t / 2) := hΨbnn _
        linarith
      · have h1 := hslow (Real.sqrt (2 * h) * t) (2 * (Real.sqrt (2 * h) * t)) hc
          (by linarith) (by linarith)
        have h2 := hslow (Real.sqrt (2 * h) * t / 2) (Real.sqrt (2 * h) * t) hc2
          (by linarith) (by linarith)
        have h3 := hslow (Real.sqrt (2 * h) * t) D hc hge hDb
        have h8 : 0 ≤ Ψb (Real.sqrt (2 * h) * t / 2) := hΨbnn _
        linarith
    have h7 : Ψb D ^ 2 ≤ 64 * Ψb (Real.sqrt (2 * h) * t / 2) ^ 2 := by
      have h8 : 0 ≤ Ψb (Real.sqrt (2 * h) * t / 2) := hΨbnn _
      nlinarith [hslow', hΨbD0]
    calc ‖γ t - xstar - (Real.sqrt (2 * h) * t) • a‖_[m] ^ 2
        ≤ 2 ^ 16 * Ψb D ^ 2 * (Real.sqrt (2 * h) * t) ^ 2 := hmain
      _ ≤ 2 ^ 16 * (64 * Ψb (Real.sqrt (2 * h) * t / 2) ^ 2)
            * (Real.sqrt (2 * h) * t) ^ 2 := by
          have h9 : (0:ℝ) ≤ 2 ^ 16 * (Real.sqrt (2 * h) * t) ^ 2 := by positivity
          nlinarith [h7, h9]
      _ = 2 ^ 22 * Ψb (Real.sqrt (2 * h) * t / 2) ^ 2 * (Real.sqrt (2 * h) * t) ^ 2 := by
          ring_nf
  have hL2' : (actionOn m h γ 0 t).toReal ≤ 8 * h * t := by rw [← hE]; exact hL2
  exact ⟨hsepκ, hE, hA2, hL2, hDlo, hDhi, h73, hbound_lintegral.trans
    (ENNReal.ofReal_le_ofReal hL2')⟩


/-! ## Lemma 7.1 with the estimates of Lemma `unif` discharged -/

/-- **Liu--Yan--Zhou's Lemma 7.1, packaged with `exists_lyz_unif`.**  For an `h`-minimiser `γ` on
`[0,τ]` satisfying the hypotheses of Lemma `unif`, the crossing times `σ i` exist and, for every
`t ∈ [σ n₀, τ]`, `γ t` is collision free, the uniform `L²` bound `∫₀^t |γ̇|²_[m] ≤ 8 h t` holds, the
ratio bounds (7.2) hold, and the asymptotic shape (7.3) holds. -/
theorem exists_lyz_ratio {m : Fin N → ℝ} {h : ℝ} (hh : 0 < h) (hm : ∀ i, 0 < m i)
    {xstar a : EN E N} {ν s₀ θ : ℝ} (hν : 0 < ν) (hsep : Separated a ν) (ha : ‖a‖_[m] = 1)
    {K : ℝ} (hK : 0 < K) (hKn : ∀ y : EN E N, ‖y‖ ≤ K * ‖y‖_[m])
    (hKθ : K * θ ≤ ν / 16) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1)
    {A B M : ℝ} (hA0 : 0 ≤ A) (hB0 : 0 ≤ B) (hM0 : 0 ≤ M)
    {Ψ Ψb : ℝ → ℝ} (hΨnn : ∀ T, 0 ≤ T → 0 ≤ Ψ T)
    (hΨmono : ∀ T T', 0 ≤ T → T ≤ T' → Ψ T ≤ Ψ T')
    (hΨbnn : ∀ t, 0 ≤ Ψb t)
    (hslow : ∀ s t, 0 < s → s ≤ t → t ≤ 2 * s → Ψb t ≤ 2 * Ψb s)
    (hrel : ∀ t, 0 < t → Real.sqrt (Ψ t / t) ≤ Ψb t)
    (hsumm : Summable fun k : ℕ => Real.sqrt (Ψ ((2:ℝ) ^ k) / (2:ℝ) ^ k))
    (htail : ∀ i : ℕ, lyzTail Ψ i ≤ Ψb ((2:ℝ) ^ i))
    {n₀ n : ℕ} (hn : n₀ ≤ n)
    (hΨb1 : ∀ t : ℝ, (2:ℝ) ^ n₀ ≤ t → Ψb t ≤ 1)
    {τ : ℝ} {γ : ℝ → EN E N}
    (hτ : 0 < τ) (hac : AbsolutelyContinuousOnInterval γ 0 τ)
    (hfin : actionOn m h γ 0 τ < ⊤) (hmin : IsHMinimizer m h γ 0 τ)
    (hγτ : γ τ = xstar + (2:ℝ) ^ n • a)
    (h0lt : ‖γ 0 - xstar‖_[m] < (2:ℝ) ^ n₀)
    (hΦ : actionPot m h (γ 0) xstar < ⊤)
    (hAφ : (Real.sqrt (2 * h))⁻¹ * (actionPot m h (γ 0) xstar).toReal ≤ A)
    (hΨhalf : ∀ i, n₀ ≤ i → i < n → Ψ ((2:ℝ) ^ (i + 1)) ≤ (2:ℝ) ^ (i + 1) / 2)
    (hx0 : ∀ i, n₀ ≤ i → i < n → ‖γ 0 - xstar‖_[m] ≤ Ψ ((2:ℝ) ^ (i + 1)))
    (hpotB : ∀ b : EN E N, ‖b‖_[m] = 1 → ‖b - a‖_[m] ≤ θ → ∀ T : ℝ, 0 ≤ T →
        ∫ s in (0:ℝ)..T, U m (xstar + s • b) ≤ (2 * h) * B * Real.log (2 * T + 2 * M + 1))
    (hncB : ∀ b : EN E N, ‖b‖_[m] = 1 → ‖b - a‖_[m] ≤ θ → ∀ s : ℝ, 0 ≤ s →
        WithoutCollisions (xstar + s • b))
    (hΨlyz : ∀ T : ℝ, Ψ T = lyzPsi A B M T)
    (hθ50 : 50 * lyzTail Ψ (n₀ + 1) ≤ θ)
    (hθΨb : ∀ t : ℝ, (2:ℝ) ^ n₀ ≤ t → 64 * Ψb t ≤ θ)
    (hxstar : xstar = γ 0 + s₀ • a) (hs₀1 : 1 ≤ s₀)
    (hs₀K : ‖γ 0‖_[m] + 40 * K * ‖γ 0‖_[m] / ν ≤ s₀)
    (hs₀K2 : 50 * K * ‖γ 0‖_[m] / ν ≤ s₀) :
    ∃ σ : ℕ → ℝ,
      σ n = τ ∧
      (∀ i, n₀ ≤ i → i ≤ n → σ i ∈ Set.Icc 0 τ ∧ ‖γ (σ i) - xstar‖_[m] = (2:ℝ) ^ i ∧
        (∀ t ∈ Set.Icc (σ i) τ, (2:ℝ) ^ i ≤ ‖γ t - xstar‖_[m])) ∧
      (∀ i, n₀ ≤ i → i < n → σ i ≤ σ (i + 1)) ∧
      (∀ t ∈ Set.Icc (σ n₀) τ, Separated (γ t) ((9:ℝ) / 10 * ν)) ∧
      (∀ t ∈ Set.Icc (σ n₀) τ, WithoutCollisions (γ t)) ∧
      (∀ t ∈ Set.Icc (σ n₀) τ, ∫ s in (0:ℝ)..t, ‖deriv γ s‖_[m] ^ 2 ≤ 8 * h * t) ∧
      (∀ t ∈ Set.Icc (σ n₀) τ,
        ‖γ t - xstar - (Real.sqrt (2 * h) * t) • a‖_[m] ^ 2
          ≤ 2 ^ 22 * Ψb (Real.sqrt (2 * h) * t / 2) ^ 2 * (Real.sqrt (2 * h) * t) ^ 2) ∧
      (∀ t ∈ Set.Icc (σ n₀) τ,
        Real.sqrt (2 * h) * t / (1 + Ψb (‖γ t - xstar‖_[m]) ^ 2) ≤ ‖γ t - xstar‖_[m]) ∧
      (∀ t ∈ Set.Icc (σ n₀) τ,
        ‖γ t - xstar‖_[m] ≤ Real.sqrt (2 * h) * t * (1 + Ψb (‖γ t - xstar‖_[m]) ^ 2)) ∧
      (∀ t ∈ Set.Icc (σ n₀) τ,
        ∫⁻ s in Set.Ioc (0:ℝ) t, ENNReal.ofReal (‖deriv γ s‖_[m] ^ 2)
          ≤ ENNReal.ofReal (8 * h * t)) := by
  have hrelL : ∀ t, 0 < t → Real.sqrt (lyzPsi A B M t / t) ≤ Ψb t := by
    intro t ht
    rw [← hΨlyz t]
    exact hrel t ht
  obtain ⟨σ, hσn, hσv, hσmono, hlen, hdir⟩ := exists_lyz_unif hh hm hA0 hB0 hM0 ha hΨnn hΨmono
    hΨbnn hrel hslow hsumm htail hn hτ hac hfin hmin hγτ h0lt hΦ hAφ hΨhalf hx0 hpotB hncB
    hΨlyz hθ50
  have hσ0pos : 0 < σ n₀ := by
    by_contra hcon
    push Not at hcon
    have h0 : σ n₀ = 0 := le_antisymm hcon (hσv n₀ le_rfl hn).1.1
    have h1 : ‖γ (σ n₀) - xstar‖_[m] = (2:ℝ) ^ n₀ := (hσv n₀ le_rfl hn).2.1
    rw [h0] at h1
    linarith [h0lt, h1]
  have hDpos : ∀ t ∈ Set.Icc (σ n₀) τ, 0 < ‖γ t - xstar‖_[m] := by
    intro t ht
    have h1 := (hσv n₀ le_rfl hn).2.2 t ht
    have h2 : (0:ℝ) < (2:ℝ) ^ n₀ := by positivity
    linarith
  have hdirm : ∀ t ∈ Set.Icc (σ n₀) τ,
      ‖(‖γ t - xstar‖_[m])⁻¹ • (γ t - xstar) - a‖_[m] ≤ 64 * Ψb (‖γ t - xstar‖_[m]) :=
    fun t ht => hdir t ht
  have hcone : ∀ t ∈ Set.Icc (σ n₀) τ, 64 * Ψb (‖γ t - xstar‖_[m]) ≤ θ := by
    intro t ht
    exact hθΨb _ ((hσv n₀ le_rfl hn).2.2 t ht)
  have hlenb : ∀ t ∈ Set.Icc (σ n₀) τ,
      massLength m γ 0 t ≤ ‖γ t - xstar‖_[m] * (1 + Ψb (‖γ t - xstar‖_[m]) ^ 2) :=
    fun t ht => hlen t ht
  have hkey : ∀ t ∈ Set.Icc (σ n₀) τ,
      (Separated (γ t) ((9:ℝ) / 10 * ν) ∧
       (∫ s in (0:ℝ)..t, ‖deriv γ s‖_[m] ^ 2 ≤ 8 * h * t) ∧
       (‖γ t - xstar - (Real.sqrt (2 * h) * t) • a‖_[m] ^ 2
          ≤ 2 ^ 22 * Ψb (Real.sqrt (2 * h) * t / 2) ^ 2 * (Real.sqrt (2 * h) * t) ^ 2) ∧
       (Real.sqrt (2 * h) * t / (1 + Ψb (‖γ t - xstar‖_[m]) ^ 2) ≤ ‖γ t - xstar‖_[m]) ∧
       (‖γ t - xstar‖_[m] ≤ Real.sqrt (2 * h) * t * (1 + Ψb (‖γ t - xstar‖_[m]) ^ 2)) ∧
       (∫⁻ s in Set.Ioc (0:ℝ) t, ENNReal.ofReal (‖deriv γ s‖_[m] ^ 2)
          ≤ ENNReal.ofReal (8 * h * t))) := by
    intro t ht
    have htpos : 0 < t := lt_of_lt_of_le hσ0pos ht.1
    obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ :=
      lyz_ratio_estimates hh hm hν hsep ha hK hKn hKθ hθ0 hθ1 hA0 hB0 hM0 hΨbnn
        hslow hrelL hτ htpos ht.2 (hΨb1 _ ((hσv n₀ le_rfl hn).2.2 t ht)) hac hfin hmin hΦ
        hAφ hpotB hncB hxstar hs₀1 hs₀K hs₀K2
        (hDpos t ht) (hdirm t ht) (hcone t ht) (hlenb t ht)
    exact ⟨h1, h4, h7, h5, h6, h8⟩
  refine ⟨σ, hσn, hσv, hσmono, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro t ht
    exact (hkey t ht).1
  · intro t ht i j hij
    have h2 : (0:ℝ) < (9:ℝ) / 10 * ν := by positivity
    exact ne_of_gt (lt_of_lt_of_le h2 ((hkey t ht).1 i j hij))
  · intro t ht
    exact (hkey t ht).2.1
  · intro t ht
    exact (hkey t ht).2.2.1
  · intro t ht
    exact (hkey t ht).2.2.2.1
  · intro t ht
    exact (hkey t ht).2.2.2.2.1
  · intro t ht
    exact (hkey t ht).2.2.2.2.2

end Submission.NBody
