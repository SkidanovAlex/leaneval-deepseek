import Mathlib
import Submission.Work.KMTPlan.A6.MdlAdelicProb
import Submission.Work.KMTAreas.A7Hi.vrsdIntegralLeSamples
import Submission.Port.Aesm

-- v4.35 port: restore the v4.34 instance-unification behaviour (respectTransparency) in this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.A6Clean

open MeasureTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

/-! ## Auxiliary lemmas

### The finite `ℓ^R`-sum as an `eLpNorm`

For `R > 0` and `g : Fin J → ℝ≥0∞` the finite `ℓ^R`-sum `(∑_i (g i)^R)^{1/R}` is the `eLpNorm` of
`g` with exponent `R` against the counting measure on `Fin J`.  This identification turns Minkowski's
inequality for `eLpNorm` (`Commons.MeasureTheory.Lp.eLpNorm_tsum_le_tsum_eLpNorm`) into the weighted
`ℓ^R`-Minkowski inequality needed for the chain part of the variational datum. -/

private theorem rpow_sum_rpow_eq_eLpNorm_count {J : ℕ} {R : ℝ} (hR : 0 < R)
    (g : Fin J → ℝ≥0∞) :
    (∑ i : Fin J, (g i) ^ R) ^ (1 / R)
      = eLpNorm g (ENNReal.ofReal R) (Measure.count : Measure (Fin J)) := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (hf := by pw_aesm)
      (ne_of_gt (ENNReal.ofReal_pos.mpr hR)) ENNReal.ofReal_ne_top,
    ENNReal.toReal_ofReal hR.le, lintegral_count]
  congr 1
  rw [tsum_fintype]
  exact Finset.sum_congr rfl fun i _ => by rw [enorm_eq_self]

/-- Homogeneity of the finite `ℓ^R`-sum in an `ℝ≥0∞`-valued weight. -/
private theorem ennreal_const_mul_rpow_sum {J : ℕ} {R : ℝ} (hR : 0 < R) (a : ℝ≥0∞)
    (g : Fin J → ℝ≥0∞) :
    (∑ i : Fin J, (a * g i) ^ R) ^ (1 / R) = a * (∑ i : Fin J, (g i) ^ R) ^ (1 / R) := by
  have h : ∀ i : Fin J, (a * g i) ^ R = a ^ R * (g i) ^ R :=
    fun i => ENNReal.mul_rpow_of_nonneg _ _ hR.le
  rw [Finset.sum_congr rfl (fun i _ => h i), ← Finset.mul_sum,
    ENNReal.mul_rpow_of_nonneg _ _ (by positivity), ← ENNReal.rpow_mul,
    mul_one_div_cancel hR.ne', ENNReal.rpow_one]

/-- **Weighted Minkowski in the finite `ℓ^R`-norm.**  For `R ≥ 1`, `ℝ≥0∞`-valued weights `a` and a
family `Z`, the `ℓ^R`-norm of the weighted sum `∑'_m a m ⬝ Z m` is at most the `ℓ¹`-weighted sum of
the `ℓ^R`-norms. -/
private theorem ennreal_lR_weighted_minkowski {J : ℕ} {R : ℝ} (hR : 1 ≤ R)
    (a : ℤ → ℝ≥0∞) (Z : ℤ → Fin J → ℝ≥0∞) :
    (∑ i : Fin J, (∑' m : ℤ, a m * Z m i) ^ R) ^ (1 / R)
      ≤ ∑' m : ℤ, a m * (∑ i : Fin J, (Z m i) ^ R) ^ (1 / R) := by
  have hR0 : 0 < R := lt_of_lt_of_le zero_lt_one hR
  have hp1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal R := by
    rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal hR
  have hMink := Commons.MeasureTheory.Lp.eLpNorm_tsum_le_tsum_eLpNorm
      (μ := (Measure.count : Measure (Fin J))) (p := ENNReal.ofReal R) hp1
      (f := fun m : ℤ => fun i : Fin J => a m * Z m i)
      (fun m => (measurable_of_countable _).aemeasurable)
  rw [rpow_sum_rpow_eq_eLpNorm_count hR0]
  refine hMink.trans ?_
  refine ENNReal.tsum_le_tsum fun m => ?_
  rw [← rpow_sum_rpow_eq_eLpNorm_count hR0]
  exact le_of_eq (ennreal_const_mul_rpow_sum hR0 (a m) (Z m))

/-! ### Triangle inequalities for the `L²(ZMod Q)`-valued variational datum

`Work.KMTPlan.A6.VrLiftDataP R Q u` is
`(⨆ n, eLpNorm (u n) 2 (zmodProb Q)) + (⨆ chains, (∑_i (eLpNorm Δ_i 2) ^ R) ^ (1/R))`, i.e. the
`V^R(ℕ; L²(ZMod Q))`-datum of a packet family.  We prove here that it is subadditive and positively
homogeneous with respect to a weighted lattice sum `∑'_m c m ⬝ v m`, which is the vector-valued
form of `Work.KMTAreas.A7Hi.variationalNorm_tsum_le` (the scalar case, used for
`Work.KMTAreas.A7Hi.vrsdIntegralLeSamples`). -/

/-- Minkowski's inequality for the `L²(zmodProb Q)`-norm against a countable sum. -/
private theorem eLpNorm_tsum_mul_le_zmod {Q : ℕ} [NeZero Q] (c : ℤ → ℂ) (v : ℤ → ZMod Q → ℂ) :
    eLpNorm (fun θ => ∑' m : ℤ, c m * v m θ) 2 (Work.KMTPlan.A6.zmodProb Q)
      ≤ ∑' m : ℤ, ‖c m‖ₑ * eLpNorm (fun θ => v m θ) 2 (Work.KMTPlan.A6.zmodProb Q) := by
  refine (eLpNorm_mono_enorm (hf := by pw_aesm) (f := fun θ : ZMod Q => ∑' m : ℤ, c m * v m θ)
      (g := fun θ : ZMod Q => ∑' m : ℤ, ‖c m * v m θ‖ₑ) ?_).trans ?_
  · intro θ
    simpa only [enorm_eq_self] using
      (enorm_tsum_le_tsum_enorm (f := fun m : ℤ => c m * v m θ))
  · have hMink := Commons.MeasureTheory.Lp.eLpNorm_tsum_le_tsum_eLpNorm
        (μ := Work.KMTPlan.A6.zmodProb Q) (p := 2) (by norm_num)
        (f := fun m : ℤ => fun θ : ZMod Q => ‖c m * v m θ‖ₑ)
        (fun m => ((measurable_of_countable (fun θ : ZMod Q => c m * v m θ)).enorm).aemeasurable)
    refine hMink.trans (ENNReal.tsum_le_tsum fun m => ?_)
    rw [eLpNorm_enorm (hf := by pw_aesm)]
    exact (eLpNorm_const_smul (c m) (fun θ : ZMod Q => v m θ) 2
      (Work.KMTPlan.A6.zmodProb Q)).le

/-- The chain part of the variational datum is subadditive under a weighted lattice sum, with the
`ℓ^R`-triangle applied to the increment vector of the chain `k`. -/
private theorem chain_tsum_mul_le_zmod {Q : ℕ} [NeZero Q] {R : ℝ} (hR : 1 ≤ R)
    (c : ℤ → ℂ) (v : ℤ → ℕ → ZMod Q → ℂ)
    (hsum : ∀ (n : ℕ) (θ : ZMod Q), Summable (fun m : ℤ => c m * v m n θ))
    (w : ℕ → ZMod Q → ℂ) (hw : ∀ n θ, w n θ = ∑' m : ℤ, c m * v m n θ)
    (J : ℕ) (k : Fin (J + 1) → ℕ) :
    (∑ i : Fin J, (eLpNorm (w (k i.succ) - w (k i.castSucc)) 2
        (Work.KMTPlan.A6.zmodProb Q)) ^ R) ^ (1 / R)
      ≤ ∑' m : ℤ, ‖c m‖ₑ * (∑ i : Fin J,
          (eLpNorm (v m (k i.succ) - v m (k i.castSucc)) 2
            (Work.KMTPlan.A6.zmodProb Q)) ^ R) ^ (1 / R) := by
  have hR0 : 0 < R := lt_of_lt_of_le zero_lt_one hR
  have hstep : ∀ i : Fin J, eLpNorm (w (k i.succ) - w (k i.castSucc)) 2
        (Work.KMTPlan.A6.zmodProb Q)
      ≤ ∑' m : ℤ, ‖c m‖ₑ * eLpNorm (v m (k i.succ) - v m (k i.castSucc)) 2
          (Work.KMTPlan.A6.zmodProb Q) := by
    intro i
    have hΔ : (w (k i.succ) - w (k i.castSucc))
        = fun θ : ZMod Q => ∑' m : ℤ, c m * ((v m (k i.succ) - v m (k i.castSucc)) θ) := by
      funext θ
      rw [Pi.sub_apply, hw (k i.succ) θ, hw (k i.castSucc) θ]
      rw [← Summable.tsum_sub (hsum (k i.succ) θ) (hsum (k i.castSucc) θ)]
      exact tsum_congr fun m => by rw [Pi.sub_apply]; ring
    rw [hΔ]
    exact eLpNorm_tsum_mul_le_zmod c (fun m => v m (k i.succ) - v m (k i.castSucc))
  refine ((ENNReal.rpow_le_rpow (Finset.sum_le_sum fun i _ =>
      ENNReal.rpow_le_rpow (hstep i) hR0.le) (div_nonneg zero_le_one hR0.le))).trans ?_
  exact ennreal_lR_weighted_minkowski hR (fun m => ‖c m‖ₑ)
    (fun m i => eLpNorm (v m (k i.succ) - v m (k i.castSucc)) 2 (Work.KMTPlan.A6.zmodProb Q))

/-- **Subadditivity of the `L²(ZMod Q)`-valued `V^R`-datum under a weighted lattice sum**

  `VrLiftDataP R Q (fun n θ => ∑'_m c m * v m n θ)
     ≤ ∑'_m ‖c m‖ₑ * VrLiftDataP R Q (v m)`.

This is the vector-valued analogue of the proved scalar
`Work.KMTAreas.A7Hi.variationalNorm_tsum_le`; the weights `c m` do not depend on `(n, θ)`, which is
what makes the interpolation step of the vector-valued lattice sampling work. -/
private theorem VrLiftDataP_tsum_mul_le {Q : ℕ} [NeZero Q] (R : ℝ) (hR : 1 ≤ R)
    (c : ℤ → ℂ) (v : ℤ → ℕ → ZMod Q → ℂ)
    (hsum : ∀ (n : ℕ) (θ : ZMod Q), Summable (fun m : ℤ => c m * v m n θ)) :
    Work.KMTPlan.A6.VrLiftDataP R Q (fun n θ => ∑' m : ℤ, c m * v m n θ)
      ≤ ∑' m : ℤ, ‖c m‖ₑ * Work.KMTPlan.A6.VrLiftDataP R Q (v m) := by
  have hsup : (⨆ n : ℕ, eLpNorm (fun θ => ∑' m : ℤ, c m * v m n θ) 2
        (Work.KMTPlan.A6.zmodProb Q))
      ≤ ∑' m : ℤ, ‖c m‖ₑ * (⨆ n : ℕ, eLpNorm (fun θ => v m n θ) 2
          (Work.KMTPlan.A6.zmodProb Q)) := by
    refine iSup_le fun n => (eLpNorm_tsum_mul_le_zmod c (fun m θ => v m n θ)).trans ?_
    exact ENNReal.tsum_le_tsum fun m => mul_le_mul' le_rfl
      (le_iSup (fun n => eLpNorm (fun θ => v m n θ) 2 (Work.KMTPlan.A6.zmodProb Q)) n)
  have hchain : (⨆ (J : ℕ) (k : Fin (J + 1) → ℕ) (_ : Monotone k),
        ENNReal.rpow (Finset.univ.sum fun i : Fin J =>
          ENNReal.rpow (eLpNorm ((fun n θ => ∑' m : ℤ, c m * v m n θ) (k i.succ)
            - (fun n θ => ∑' m : ℤ, c m * v m n θ) (k i.castSucc)) 2
              (Work.KMTPlan.A6.zmodProb Q)) R) (1 / R))
      ≤ ∑' m : ℤ, ‖c m‖ₑ * (⨆ (J : ℕ) (k : Fin (J + 1) → ℕ) (_ : Monotone k),
          ENNReal.rpow (Finset.univ.sum fun i : Fin J =>
            ENNReal.rpow (eLpNorm (v m (k i.succ) - v m (k i.castSucc)) 2
              (Work.KMTPlan.A6.zmodProb Q)) R) (1 / R)) := by
    refine iSup_le fun J => iSup_le fun k => iSup_le fun hk => ?_
    refine (chain_tsum_mul_le_zmod hR c v hsum
      (fun n θ => ∑' m : ℤ, c m * v m n θ) (fun n θ => rfl) J k).trans ?_
    refine ENNReal.tsum_le_tsum fun m => mul_le_mul' le_rfl ?_
    exact le_iSup_of_le J (le_iSup_of_le k (le_iSup_of_le hk le_rfl))
  have hRHS : (∑' m : ℤ, ‖c m‖ₑ * Work.KMTPlan.A6.VrLiftDataP R Q (v m))
      = (∑' m : ℤ, ‖c m‖ₑ * (⨆ n : ℕ, eLpNorm (v m n) 2 (Work.KMTPlan.A6.zmodProb Q)))
        + (∑' m : ℤ, ‖c m‖ₑ * (⨆ (J : ℕ) (k : Fin (J + 1) → ℕ) (_ : Monotone k),
            ENNReal.rpow (Finset.univ.sum fun i : Fin J =>
              ENNReal.rpow (eLpNorm (v m (k i.succ) - v m (k i.castSucc)) 2
                (Work.KMTPlan.A6.zmodProb Q)) R) (1 / R))) := by
    rw [← ENNReal.tsum_add]
    exact tsum_congr fun m => by rw [Work.KMTPlan.A6.VrLiftDataP, mul_add]
  rw [Work.KMTPlan.A6.VrLiftDataP, hRHS]
  exact add_le_add hsup hchain

/-! ### Translation invariance of the Lebesgue integral -/

private theorem lintegral_shift_sub (F : ℝ → ℝ≥0∞) (y : ℝ) :
    (∫⁻ x : ℝ, F (x - y)) = ∫⁻ x : ℝ, F x := by
  have h := MeasureTheory.lintegral_add_right_eq_self (μ := (volume : Measure ℝ))
    (fun z : ℝ => F (z - y)) y
  simpa only [add_sub_cancel_right] using h.symm

/-! ## The general `p` form of the sampling theorem -/

/-- **Vector-valued lattice sampling (general exponent).**  The `L²(ZMod Q)`-valued `V^R`-datum of
a band-limited family `(𝓕⁻(B n θ))` is controlled by its integer samples, with a constant uniform in
`Q`, `R ≥ 1` and the amplitudes `B`.  This is the vector-valued form of
`Work.KMTAreas.A7Hi.vrsdIntegralLeSamples`. -/
private theorem vrLiftDataP_lattice_sampling (p : ℝ) (hp : 1 < p) :
    ∃ C : ℝ, 0 < C ∧ ∀ {Q : ℕ} [NeZero Q] (R : ℝ) (hR : 1 ≤ R)
      (B : ℕ → ZMod Q → ℝ → ℂ),
      (∀ (n : ℕ) (θ : ZMod Q), MeasureTheory.Integrable (B n θ)) →
      (∀ (n : ℕ) (θ : ZMod Q) (ξ : ℝ),
        ξ ∉ Set.Icc (-(1 / 4 : ℝ)) (1 / 4) → B n θ ξ = 0) →
      ∫⁻ X : ℝ, (Work.KMTPlan.A6.VrLiftDataP R Q
          (fun n θ => FourierTransformInv.fourierInv (B n θ) X)) ^ p
        ≤ ENNReal.ofReal C * ∑' m : ℤ, (Work.KMTPlan.A6.VrLiftDataP R Q
            (fun n θ => FourierTransformInv.fourierInv (B n θ) ((m : ℤ) : ℝ))) ^ p := by
  obtain ⟨A, hApos, hAbound⟩ := Commons.Analysis.Fourier.schwartz_lattice_sum_bound
    Work.KMTAreas.A7Rep.samplingKernel
  refine ⟨A ^ (p - 1) * (∫ x : ℝ, ‖(Work.KMTAreas.A7Rep.samplingKernel : ℝ → ℂ) x‖) + 1,
    ?_, ?_⟩
  · have h1 : (0 : ℝ) ≤ A ^ (p - 1) := Real.rpow_nonneg hApos.le _
    have h2 : (0 : ℝ) ≤ ∫ x : ℝ, ‖(Work.KMTAreas.A7Rep.samplingKernel : ℝ → ℂ) x‖ :=
      integral_nonneg (fun x => norm_nonneg _)
    nlinarith [mul_nonneg h1 h2]
  intro Q _ R hR B hBint hBband
  set ψ : SchwartzMap ℝ ℂ := Work.KMTAreas.A7Rep.samplingKernel with hψdef
  have hp0 : 0 < p := lt_trans zero_lt_one hp
  have hp1 : (0 : ℝ) ≤ p - 1 := by linarith
  have hψ1 : ∀ ξ ∈ Set.Icc (-(1 / 4 : ℝ)) (1 / 4),
      FourierTransform.fourier (ψ : ℝ → ℂ) ξ = 1 := by
    intro ξ hξ
    rw [hψdef, Work.KMTAreas.A7Hi.fourier_samplingKernel]
    exact Work.KMTAreas.A7Rep.samplingChi_one ξ hξ
  have hψs : ∀ ξ : ℝ, ξ ∉ Set.Icc (-(1 / 2 : ℝ)) (1 / 2) →
      FourierTransform.fourier (ψ : ℝ → ℂ) ξ = 0 := by
    intro ξ hξ
    rw [hψdef, Work.KMTAreas.A7Hi.fourier_samplingKernel]
    exact Work.KMTAreas.A7Rep.samplingChi_zero ξ hξ
  have hbdd : ∀ (n : ℕ) (θ : ZMod Q) (x : ℝ),
      ‖FourierTransformInv.fourierInv (B n θ) x‖ ≤ ∫ η : ℝ, ‖B n θ η‖ := by
    intro n θ x
    rw [Real.fourierInv_eq']
    refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
    apply integral_congr_ae
    filter_upwards with η
    rw [Real.inner_apply, smul_eq_mul, norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul]
  set G : ℝ → ℝ≥0∞ := fun x => Work.KMTPlan.A6.VrLiftDataP R Q
    (fun n θ => FourierTransformInv.fourierInv (B n θ) x) with hG
  -- the pointwise sampling bound
  have hsample : ∀ x : ℝ, G x ≤ ∑' m : ℤ, ‖ψ (x - ((m : ℤ) : ℝ))‖ₑ * G ((m : ℤ) : ℝ) := by
    intro x
    have hrep : (fun n θ => FourierTransformInv.fourierInv (B n θ) x)
        = fun n θ => ∑' m : ℤ, (ψ : ℝ → ℂ) (x - ((m : ℤ) : ℝ)) *
            FourierTransformInv.fourierInv (B n θ) ((m : ℤ) : ℝ) := by
      funext n θ
      exact Work.KMTAreas.A7Hi.fourierInv_lattice_reproduction (B n θ) (hBint n θ) (by norm_num)
        (hBband n θ) ψ hψ1 hψs x
    have htri := VrLiftDataP_tsum_mul_le (Q := Q) R hR
      (fun m : ℤ => (ψ : ℝ → ℂ) (x - ((m : ℤ) : ℝ)))
      (fun m n θ => FourierTransformInv.fourierInv (B n θ) ((m : ℤ) : ℝ))
      (fun n θ => Work.KMTAreas.A7Hi.summable_int_schwartz_mul_bounded ψ
        (fun m : ℤ => FourierTransformInv.fourierInv (B n θ) ((m : ℤ) : ℝ))
        (fun m => hbdd n θ ((m : ℤ) : ℝ)) x)
    simpa only [hG, hrep] using htri
  have hsample' : ∀ x : ℝ, G x ≤ ∑' m : ℤ, G ((m : ℤ) : ℝ) * ‖ψ (x - ((m : ℤ) : ℝ))‖ₑ := fun x =>
    (hsample x).trans (le_of_eq (tsum_congr (fun m => mul_comm _ _)))
  have hsumψ : ∀ y : ℝ, Summable (fun m : ℤ => ‖ψ (y - (m : ℝ))‖) :=
    fun y => Work.KMTAreas.A7Hi.summable_int_norm_schwartz_sub ψ y
  have hWt : ∀ y : ℝ, (∑' m : ℤ, ‖ψ (y - (m : ℝ))‖ₑ) ≤ ENNReal.ofReal A := by
    intro y
    rw [show (∑' m : ℤ, ‖ψ (y - (m : ℝ))‖ₑ)
          = ∑' m : ℤ, ENNReal.ofReal ‖ψ (y - (m : ℝ))‖ from
        tsum_congr (fun m => by rw [ofReal_norm]),
      ← ENNReal.ofReal_tsum_of_nonneg (fun m => norm_nonneg _) (hsumψ y)]
    exact ENNReal.ofReal_le_ofReal (hAbound y)
  set Wt : ENNReal := ∫⁻ x : ℝ, ‖ψ x‖ₑ with hWtdef
  have hW_eq : Wt = ENNReal.ofReal (∫ x : ℝ, ‖ψ x‖) := by
    rw [hWtdef, show (fun x : ℝ => ‖ψ x‖ₑ) = fun x => ENNReal.ofReal ‖ψ x‖ from
        funext (fun x => by rw [ofReal_norm]),
      ← MeasureTheory.ofReal_integral_eq_lintegral_ofReal ψ.integrable.norm
        (Filter.Eventually.of_forall (fun x => norm_nonneg _))]
  have hWx : ∀ m : ℤ, (∫⁻ x : ℝ, ‖ψ (x - ((m : ℤ) : ℝ))‖ₑ) = Wt := by
    intro m
    rw [hWtdef]
    exact lintegral_shift_sub (fun y : ℝ => ‖ψ y‖ₑ) ((m : ℤ) : ℝ)
  have hmain : ∀ x : ℝ, G x ^ p
      ≤ (∑' m : ℤ, ‖ψ (x - ((m : ℤ) : ℝ))‖ₑ) ^ (p - 1) *
          ∑' m : ℤ, G ((m : ℤ) : ℝ) ^ p * ‖ψ (x - ((m : ℤ) : ℝ))‖ₑ := by
    intro x
    have hf : AEMeasurable (fun m : ℤ => G ((m : ℤ) : ℝ)) (Measure.count : Measure ℤ) :=
      (measurable_of_countable _).aemeasurable
    have hw : AEMeasurable (fun m : ℤ => ‖ψ (x - ((m : ℤ) : ℝ))‖ₑ) (Measure.count : Measure ℤ) :=
      (measurable_of_countable _).aemeasurable
    have h1 := Commons.Analysis.Fourier.lintegral_mul_rpow_le_rpow_mul_lintegral_measure
      (Measure.count : Measure ℤ) hp hf hw
    rw [lintegral_count, lintegral_count, lintegral_count] at h1
    exact (ENNReal.rpow_le_rpow (hsample' x) (le_of_lt hp0)).trans h1
  have hstep1 : ∫⁻ x : ℝ, G x ^ p
      ≤ ∫⁻ x : ℝ, (∑' m : ℤ, ‖ψ (x - ((m : ℤ) : ℝ))‖ₑ) ^ (p - 1) *
          ∑' m : ℤ, G ((m : ℤ) : ℝ) ^ p * ‖ψ (x - ((m : ℤ) : ℝ))‖ₑ :=
    lintegral_mono hmain
  have hstep2 : ∫⁻ x : ℝ, (∑' m : ℤ, ‖ψ (x - ((m : ℤ) : ℝ))‖ₑ) ^ (p - 1) *
        ∑' m : ℤ, G ((m : ℤ) : ℝ) ^ p * ‖ψ (x - ((m : ℤ) : ℝ))‖ₑ
      ≤ ∫⁻ x : ℝ, ENNReal.ofReal A ^ (p - 1) *
          ∑' m : ℤ, G ((m : ℤ) : ℝ) ^ p * ‖ψ (x - ((m : ℤ) : ℝ))‖ₑ := by
    apply lintegral_mono; intro x
    exact mul_le_mul_of_nonneg_right (ENNReal.rpow_le_rpow (hWt x) hp1) bot_le
  have hmeasc : ∀ m : ℤ, AEMeasurable
      (fun x : ℝ => G ((m : ℤ) : ℝ) ^ p * ‖ψ (x - ((m : ℤ) : ℝ))‖ₑ) volume := by
    intro m
    have h2 : AEMeasurable (fun x : ℝ => ‖ψ (x - ((m : ℤ) : ℝ))‖ₑ) volume :=
      (((ψ.continuous.comp (continuous_id.sub continuous_const)).measurable).enorm).aemeasurable
    exact aemeasurable_const.mul h2
  have hfinal : ∫⁻ x : ℝ, G x ^ p
      ≤ ENNReal.ofReal (A ^ (p - 1) * (∫ x : ℝ, ‖ψ x‖) + 1) *
          ∑' m : ℤ, G ((m : ℤ) : ℝ) ^ p := by
    calc ∫⁻ x : ℝ, G x ^ p
        ≤ ∫⁻ x : ℝ, ENNReal.ofReal A ^ (p - 1) *
            ∑' m : ℤ, G ((m : ℤ) : ℝ) ^ p * ‖ψ (x - ((m : ℤ) : ℝ))‖ₑ :=
          hstep1.trans hstep2
      _ = ENNReal.ofReal A ^ (p - 1) *
            ∫⁻ x : ℝ, ∑' m : ℤ, G ((m : ℤ) : ℝ) ^ p * ‖ψ (x - ((m : ℤ) : ℝ))‖ₑ := by
          rw [lintegral_const_mul'' _ (AEMeasurable.tsum hmeasc)]
      _ = ENNReal.ofReal A ^ (p - 1) *
            ∑' m : ℤ, ∫⁻ x : ℝ,
              G ((m : ℤ) : ℝ) ^ p * ‖ψ (x - ((m : ℤ) : ℝ))‖ₑ := by
          rw [lintegral_tsum hmeasc]
      _ = ENNReal.ofReal A ^ (p - 1) *
            ∑' m : ℤ, G ((m : ℤ) : ℝ) ^ p * ∫⁻ x : ℝ, ‖ψ (x - ((m : ℤ) : ℝ))‖ₑ := by
          congr 1
          apply tsum_congr; intro m
          exact lintegral_const_mul'' _ (by
            exact (((ψ.continuous.comp
              (continuous_id.sub continuous_const)).measurable).enorm).aemeasurable)
      _ = ENNReal.ofReal A ^ (p - 1) * ∑' m : ℤ, G ((m : ℤ) : ℝ) ^ p * Wt := by
          congr 1
          apply tsum_congr; intro m
          rw [hWx m]
      _ = ENNReal.ofReal A ^ (p - 1) * (Wt * ∑' m : ℤ, G ((m : ℤ) : ℝ) ^ p) := by
          congr 1
          rw [ENNReal.tsum_mul_right, mul_comm]
      _ = ENNReal.ofReal A ^ (p - 1) * Wt * ∑' m : ℤ, G ((m : ℤ) : ℝ) ^ p := by
          rw [mul_assoc]
      _ = ENNReal.ofReal (A ^ (p - 1) * (∫ x : ℝ, ‖ψ x‖)) *
            ∑' m : ℤ, G ((m : ℤ) : ℝ) ^ p := by
          rw [hW_eq, ENNReal.ofReal_rpow_of_nonneg hApos.le hp1,
            ← ENNReal.ofReal_mul (Real.rpow_nonneg hApos.le _)]
      _ ≤ ENNReal.ofReal (A ^ (p - 1) * (∫ x : ℝ, ‖ψ x‖) + 1) *
            ∑' m : ℤ, G ((m : ℤ) : ℝ) ^ p := by
          apply mul_le_mul_of_nonneg_right _ bot_le
          exact ENNReal.ofReal_le_ofReal (by linarith)
  simpa only [hG, hψdef] using hfinal

/- **Vector-valued lattice sampling for the packet datum** (the analytic core of the §8 clauses
`(lin-1)`/`(lin-2)`).

For a family of amplitudes `B n θ : ℝ → ℂ` (integrable, Fourier-supported in `Icc (-1/4) (1/4)`),
the `L²(ZMod Q)`-valued `V^R`-datum `VrLiftDataP R Q (fun n θ => 𝓕⁻(B n θ) ·)` of the band-limited
family is controlled by its integer samples, with `C` uniform in `Q`, `R ≥ 1` and `B`:

  `∫⁻ X, (VrLiftDataP R Q (fun n θ => 𝓕⁻(B n θ) X)) ^ 2
     ≤ ofReal C * ∑'_m (VrLiftDataP R Q (fun n θ => 𝓕⁻(B n θ) m)) ^ 2`.

Route (mirroring the PROVED scalar `Work.KMTAreas.A7Hi.vrsdIntegralLeSamples`,
`Submission/Work/KMTAreas/A7Hi/vrsdIntegralLeSamples.lean`, whose private bricks
`variationalNorm_sampling_pointwise` / `lintegral_variationalNorm_rpow_le_lattice_tsum` are in
`Submission/Work/KMTAreas/A7Hi/integral_le_latticeVrSampling.lean`):
* `Work.KMTAreas.A7Hi.fourierInv_lattice_reproduction` (PROVED, in `vrsdIntegralLeSamples.lean`)
  gives, for each `(n, θ)`, the pointwise interpolation
  `𝓕⁻(B n θ) X = ∑'_m ψ (X - m) * 𝓕⁻(B n θ) m` with the sampling kernel
  `ψ = Work.KMTAreas.A7Rep.samplingKernel` (`𝓕ψ = samplingChi`, `1` on `Icc (-1/4) (1/4)`, `0` off
  `Icc (-1/2) (1/2)`);
* the triangle inequality for `VrLiftDataP` under a weighted lattice sum (proved in this file as
  `VrLiftDataP_tsum_mul_le`) turns the interpolation into
  `VrLiftDataP R Q (fun n θ => 𝓕⁻(B n θ) X) ≤ ∑'_m ‖ψ (X - m)‖ₑ * VrLiftDataP R Q (fun n θ => 𝓕⁻(B n θ) m)`
  — the weight `ψ (X - m)` does not depend on `θ`, which is what makes the vector-valued step work;
* the weighted Hölder/Tonelli computation of `lintegral_variationalNorm_rpow_le_lattice_tsum` at
  `p := 2`: `(∑'_m a m X v m)^2 ≤ (∑'_m a m X) * (∑'_m a m X v m^2)` with `a m X := ‖ψ (X - m)‖`,
  the uniform lattice bound `∃ A > 0, ∀ X, ∑'_m ‖ψ (X - m)‖ ≤ A`
  (`Commons.Analysis.Fourier.schwartz_lattice_sum_bound`), and `∫⁻ X, ‖ψ (X - m)‖ = ∫ x, ‖ψ x‖`.
  The constant is `A * (∫ x, ‖ψ x‖) + 1`.-/
theorem VrLiftSamplingLattice :
    ∃ C : ℝ, 0 < C ∧ ∀ {Q : ℕ} [NeZero Q] (R : ℝ) (hR : 1 ≤ R)
      (B : ℕ → ZMod Q → ℝ → ℂ),
      (∀ (n : ℕ) (θ : ZMod Q), MeasureTheory.Integrable (B n θ)) →
      (∀ (n : ℕ) (θ : ZMod Q) (ξ : ℝ),
        ξ ∉ Set.Icc (-(1 / 4 : ℝ)) (1 / 4) → B n θ ξ = 0) →
      ∫⁻ X : ℝ, (Work.KMTPlan.A6.VrLiftDataP R Q
          (fun n θ => FourierTransformInv.fourierInv (B n θ) X)) ^ (2 : ℕ)
        ≤ ENNReal.ofReal C * ∑' m : ℤ, (Work.KMTPlan.A6.VrLiftDataP R Q
            (fun n θ => FourierTransformInv.fourierInv (B n θ) ((m : ℤ) : ℝ))) ^ (2 : ℕ) := by
  obtain ⟨C, hCpos, hC⟩ := vrLiftDataP_lattice_sampling 2 (by norm_num)
  refine ⟨C, hCpos, ?_⟩
  intro Q _ R hR B hBint hBband
  have h := hC R hR B hBint hBband
  have h2 : ∀ x : ℝ≥0∞, x ^ (2 : ℕ) = x ^ (2 : ℝ) := by
    intro x
    rw [← ENNReal.rpow_natCast]
    norm_num
  simp only [h2]
  exact h

end

end Work.A6Clean
