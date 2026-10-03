import Mathlib
import Submission.Work.KMTAreas.A7Hi.FiberOpVarUniformLpNoLossClean
import Submission.Work.KMTAreas.A7.varShiftDiffPrep
import Submission.Work.KMTAreas.A7Hi.fiberOp_Tex_eq_twisted
import Submission.Port.Aesm

/-!
# `varEstTle_compositeCompare` is **FALSE** as stated: the `M = 0` corner

The requested statement quantifies over an arbitrary `M : NNReal` with no positivity hypothesis.
Taking `M = 0` is allowed, and the multiplier hypothesis is then *satisfied* by the degenerate
choice of data `Φ n := -ψ`, `Ψ n := ψ` (with `ψ = η_{≤k}` the narrow smooth bump, `ψ ≠ 0`),
because the symbol `Σ_{n ∈ U} ±(Φ n ξ + Ψ n ξ) = 0` is the zero symbol and
`IsLqMultiplierBound q 0 0` holds trivially.  The conclusion of the statement then reads

  `LHS ≤ ENNReal.ofReal (K * 0) * RHS = 0`,

forcing `LHS = 0`.  But the left-hand side is *positive* for these data: at level `l = 0` the
Ionescu–Wainger set is `{0}` and `Tle ρ 0` is convolution with the coefficients of `periodize φ`,
so the double application `Tle ρ 0 ψ (Tle ρ 0 ψ ·)` is `Tle ρ 0 (ψ · ψ) ·` (the composition
identity `iwConv_comp` plus `periodize (ψ·ψ) = periodize ψ · periodize ψ` for a narrow bump), and
`iwConv {0} Ψ (delta 0) 0 = fourierCoeff Ψ 0 = cw (ψ·ψ) 0 = ∫_ℝ ψ² ≠ 0` (the bump equals `1` on
`[-2^k/2, 2^k/2]`, so that integral is `≥ 2^k > 0`).  The family in `n` is thus the non-zero
constant `-∫_ℝ ψ²`, whose `r`-variational norm is `‖∫_ℝ ψ²‖ₑ` (`variationalNorm_const`), and the
`ℓ²(ℤ)`-norm of this (non-zero) family is `≠ 0`, contradicting `LHS ≤ 0`.

The repair is to add the positivity hypothesis `0 < M` (as in the companion lemma
`Work.KMTAreas.A7.varEst_of_narrow_schwartz_symbols`).

The statement itself is kept verbatim at the bottom of this file (with its `sorry`).
-/

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace Work.A7Hi

open MeasureTheory
open scoped ENNReal NNReal BigOperators FourierTransform

local notation "Circ" => Work.Analysis.IonescuWainger.Circle

noncomputable section

/-! ## Elementary auxiliary facts -/

/-- The zero symbol is a bounded `L^q` Fourier multiplier with constant `0`. -/
theorem isLqMultiplierBound_zero (q : ENNReal) :
    Work.Analysis.IWMultiplier.IsLqMultiplierBound q (fun _ : ℝ => 0) 0 := by
  intro f
  have hzero : Work.Analysis.IWMultiplier.contMulOp (fun _ : ℝ => 0) (f : ℝ → ℂ) = 0 := by
    simp only [Work.Analysis.IWMultiplier.contMulOp]
    ext x
    simp [Real.fourierInv_eq_fourier_comp_neg, Real.fourier_eq]
  rw [hzero, MeasureTheory.eLpNorm_zero]
  simp

/-- The periodisation is additive (negation form). -/
theorem periodize_neg_local (φ : ℝ → ℂ) :
    Work.Analysis.IonescuWainger.periodize (fun x : ℝ => -φ x)
      = fun γ : Circ => -Work.Analysis.IonescuWainger.periodize φ γ := by
  funext γ
  simp only [Work.Analysis.IonescuWainger.periodize, Pi.neg_apply, tsum_neg]

/-- `fourierCoeff` is additive (negation form). -/
theorem fourierCoeff_neg (m : Circ → ℂ) (j : ℤ) :
    fourierCoeff (fun ξ => -m ξ) j = -fourierCoeff m j := by
  rw [fourierCoeff, fourierCoeff, ← integral_neg]
  exact integral_congr_ae (Filter.Eventually.of_forall (fun t => by simp [smul_neg]))

/-- The Ionescu–Wainger symbol is additive (negation form). -/
theorem iwSymbolSet_neg (A : Finset Circ) (Ψ : Circ → ℂ) :
    Work.Analysis.IonescuWainger.iwSymbolSet A (fun ξ => -Ψ ξ)
      = fun ξ => -(Work.Analysis.IonescuWainger.iwSymbolSet A Ψ ξ) := by
  funext ξ
  simp [Work.Analysis.IonescuWainger.iwSymbolSet, Finset.sum_neg_distrib]

/-- The Ionescu–Wainger convolution is additive (negation form). -/
theorem iwConv_neg_symbol (A : Finset Circ) (Ψ : Circ → ℂ) (g : ℤ → ℂ) :
    Work.Analysis.IWMultiplier.iwConv A (fun ξ => -Ψ ξ) g
      = -Work.Analysis.IWMultiplier.iwConv A Ψ g := by
  funext n
  rw [Work.Analysis.IWMultiplier.iwConv_apply, iwSymbolSet_neg, Pi.neg_apply,
    Work.Analysis.IWMultiplier.iwConv_apply, ← tsum_neg]
  refine tsum_congr (fun j => ?_)
  simp only [Work.Analysis.IWMultiplier.iwKernel, fourierCoeff_neg, neg_smul]

/-- For the degenerate pair `Φ n = -ψ`, `Ψ n = ψ` the signed-sum symbol is identically zero, so
the multiplier hypothesis of the target holds with constant `0`. -/
theorem hMult_neg_self (ψ : ℝ → ℂ) (U : Finset ℕ) (ω : ℕ → Bool) (q : ENNReal) (hq : 1 < q) :
    Work.Analysis.IWMultiplier.IsLqMultiplierBound q
      (fun ξ : ℝ => ∑ n ∈ U, (if ω n then (1 : ℂ) else -1) * (-(ψ ξ) + ψ ξ)) 0 := by
  have hfun : (fun ξ : ℝ => ∑ n ∈ U, (if ω n then (1 : ℂ) else -1) * (-(ψ ξ) + ψ ξ))
      = fun _ : ℝ => 0 := by
    funext ξ
    simp
  rw [hfun]
  exact isLqMultiplierBound_zero q

/-! ## The narrow smooth bump `η_{≤k}` -/

/-- The narrow smooth bump `η_{≤k}(θ) = η(θ/2^k)`. -/
abbrev cBump (k : ℤ) : ℝ → ℂ := Work.Analysis.IonescuWainger.etaCut Work.KMTContract.kmtEta k

theorem cBump_contDiff (k : ℤ) : ContDiff ℝ (⊤ : ℕ∞) (cBump k) :=
  Work.KMTAreas.A7.contDiff_etaCut k

theorem cBump_contDiff_two (k : ℤ) : ContDiff ℝ 2 (cBump k) :=
  (cBump_contDiff k).of_le (WithTop.coe_le_coe.mpr (le_top : (2 : ℕ∞) ≤ ⊤))

theorem cBump_hasCompactSupport (k : ℤ) : HasCompactSupport (cBump k) :=
  Work.KMTAreas.A7.hasCompactSupport_etaCut k

theorem cBump_apply (k : ℤ) (θ : ℝ) :
    cBump k θ = Work.KMTContract.kmtEta (θ / (2 : ℝ) ^ k) :=
  (Work.KMTContract.etaCutRegular k).2.1 θ

theorem cBump_zero_of_le (k : ℤ) {θ : ℝ} (h : (2 : ℝ) ^ k ≤ |θ|) : cBump k θ = 0 :=
  (Work.KMTContract.etaCutRegular k).2.2 θ h

theorem cBump_narrow (k : ℤ) {θ : ℝ} (h : cBump k θ ≠ 0) : |θ| < (2 : ℝ) ^ k :=
  not_le.mp fun hle => h (cBump_zero_of_le k hle)

theorem cBump_one (k : ℤ) {θ : ℝ} (h : |θ| ≤ (2 : ℝ) ^ k / 2) : cBump k θ = 1 := by
  rw [cBump_apply]
  refine Work.KMTContract.kmtEta_one ?_
  have h2k : (0 : ℝ) < (2 : ℝ) ^ k := zpow_pos (by norm_num) k
  rw [abs_div, abs_of_pos h2k]
  rw [div_le_iff₀ h2k]
  linarith

/-- The bump is bounded by `1`. -/
theorem norm_cBump_le_one (k : ℤ) (θ : ℝ) : ‖cBump k θ‖ ≤ 1 :=
  Work.KMTAreas.A7.norm_etaCut_le_one k θ

theorem cBump_mul_self_eq (k : ℤ) (v : ℝ) :
    cBump k v * cBump k v
      = (((Work.KMTContract.kmtBump (v / (2 : ℝ) ^ k)) ^ 2 : ℝ) : ℂ) := by
  rw [cBump_apply, Work.KMTContract.kmtEta]
  push_cast
  ring

theorem integrable_cBump (k : ℤ) : Integrable (cBump k) volume :=
  Continuous.integrable_of_hasCompactSupport (cBump_contDiff k).continuous
    (cBump_hasCompactSupport k)

theorem cBump_sq_hasCompactSupport (k : ℤ) :
    HasCompactSupport (fun v : ℝ => cBump k v * cBump k v) := by
  refine HasCompactSupport.of_support_subset_isCompact
    (K := Set.Icc (-(2 : ℝ) ^ k) ((2 : ℝ) ^ k)) isCompact_Icc ?_
  intro v hv
  have h1 : cBump k v ≠ 0 := fun h => hv (by simp [h])
  exact abs_le.mp (cBump_narrow k h1).le

theorem integrable_cBump_sq (k : ℤ) :
    Integrable (fun v : ℝ => cBump k v * cBump k v) volume :=
  Continuous.integrable_of_hasCompactSupport
    ((cBump_contDiff k).continuous.mul (cBump_contDiff k).continuous)
    (cBump_sq_hasCompactSupport k)

theorem summable_norm_cw_cBump (k : ℤ) :
    Summable (fun j : ℤ => ‖Work.KMTAreas.A7.cw (cBump k) j‖) := by
  have h := Work.KMTAreas.A7.summable_norm_fourierCoeff_periodize (cBump_contDiff_two k)
    (cBump_hasCompactSupport k)
  simpa only [← Work.KMTAreas.A7.periodize_fourierCoeff_eq_cw (integrable_cBump k)] using h

theorem summable_norm_cw_cBump_sq (k : ℤ) :
    Summable (fun j : ℤ =>
      ‖Work.KMTAreas.A7.cw (fun v : ℝ => cBump k v * cBump k v) j‖) := by
  have hcd : ContDiff ℝ 2 (fun v : ℝ => cBump k v * cBump k v) :=
    (cBump_contDiff_two k).mul (cBump_contDiff_two k)
  have h := Work.KMTAreas.A7.summable_norm_fourierCoeff_periodize hcd
    (cBump_sq_hasCompactSupport k)
  simpa only [← Work.KMTAreas.A7.periodize_fourierCoeff_eq_cw (integrable_cBump_sq k)] using h

theorem integrable_periodize_cBump (k : ℤ) :
    Integrable (Work.Analysis.IonescuWainger.periodize (cBump k))
      Work.Analysis.IonescuWainger.circleMeasure :=
  (Work.KMTAreas.A7Hi.periodizeMemLpTop (integrable_cBump k) (summable_norm_cw_cBump k)).integrable
    le_top

theorem integrable_periodize_cBump_sq (k : ℤ) :
    Integrable (Work.Analysis.IonescuWainger.periodize
      (fun v : ℝ => cBump k v * cBump k v)) Work.Analysis.IonescuWainger.circleMeasure :=
  (Work.KMTAreas.A7Hi.periodizeMemLpTop (integrable_cBump_sq k)
    (summable_norm_cw_cBump_sq k)).integrable le_top

theorem summable_fourierCoeff_cBump (k : ℤ) :
    Summable (fun j : ℤ =>
      fourierCoeff (Work.Analysis.IonescuWainger.periodize (cBump k)) j) :=
  Work.KMTAreas.A7.summable_fourierCoeff_periodize (cBump_contDiff_two k)
    (cBump_hasCompactSupport k)

/-! ## The composition identity and the value at `0` -/

/-- The square of the bump has compact support. -/
theorem cBump_sq_narrow (k : ℤ) {v : ℝ} (h : cBump k v * cBump k v ≠ 0) :
    |v| ≤ (2 : ℝ) ^ k := by
  have h1 : cBump k v ≠ 0 := fun hz => h (by rw [hz, zero_mul])
  exact (cBump_narrow k h1).le

/-! ## Non-vanishing of `∫ ψ²` -/

/-- **The integral of the square of the bump is non-zero**: the bump equals `1` on
`[-2^k/2, 2^k/2]`, so the integral is at least `2^k > 0`. -/
theorem integral_cBump_sq_ne_zero (k : ℤ) : (∫ v : ℝ, cBump k v * cBump k v) ≠ 0 := by
  set g : ℝ → ℝ := fun v => (Work.KMTContract.kmtBump (v / (2 : ℝ) ^ k)) ^ 2 with hg
  have h2k : (0 : ℝ) < (2 : ℝ) ^ k := zpow_pos (by norm_num) k
  have hgcont : Continuous g := by
    have h1 : Continuous fun v : ℝ => Work.KMTContract.kmtBump (v / (2 : ℝ) ^ k) :=
      (ContDiffBump.continuous (f := Work.KMTContract.kmtBump)).comp (continuous_id.div_const _)
    rw [hg]
    exact (continuous_id.pow 2).comp h1
  have hgcs : HasCompactSupport g := by
    refine HasCompactSupport.of_support_subset_isCompact
      (K := Set.Icc (-(2 : ℝ) ^ k) ((2 : ℝ) ^ k)) isCompact_Icc ?_
    intro v hv
    have hv' : Work.KMTContract.kmtBump (v / (2 : ℝ) ^ k) ≠ 0 := by
      intro hz
      exact hv (by simp [hg, hz])
    have hlt : |v / (2 : ℝ) ^ k| < 1 := by
      by_contra hcon
      have hge : (1 : ℝ) ≤ |v / (2 : ℝ) ^ k| := not_lt.mp hcon
      have hzero : Work.KMTContract.kmtEta (v / (2 : ℝ) ^ k) = 0 :=
        Work.KMTContract.kmtEta_zero hge
      have : ((Work.KMTContract.kmtBump (v / (2 : ℝ) ^ k) : ℝ) : ℂ) = 0 := by
        simpa only [Work.KMTContract.kmtEta] using hzero
      exact hv' (Complex.ofReal_eq_zero.mp this)
    have : |v| < (2 : ℝ) ^ k := by
      rw [abs_div, abs_of_pos h2k] at hlt
      rw [div_lt_one h2k] at hlt
      exact hlt
    exact abs_le.mp this.le
  have hInt : Integrable g volume :=
    Continuous.integrable_of_hasCompactSupport hgcont hgcs
  have hmono : 0 ≤ᵐ[volume] g := Filter.Eventually.of_forall (fun v => sq_nonneg _)
  have hle := MeasureTheory.setIntegral_le_integral hInt hmono
    (s := Set.Icc (-((2 : ℝ) ^ k / 2)) ((2 : ℝ) ^ k / 2))
  have hcongr : Set.EqOn g (fun _ => (1 : ℝ)) (Set.Icc (-((2 : ℝ) ^ k / 2)) ((2 : ℝ) ^ k / 2)) := by
    intro v hv
    have hv' : |v| ≤ (2 : ℝ) ^ k / 2 := abs_le.mpr ⟨hv.1, hv.2⟩
    have hhalf : |v / (2 : ℝ) ^ k| ≤ 1 / 2 := by
      rw [abs_div, abs_of_pos h2k, div_le_iff₀ h2k]
      linarith
    have hone : Work.KMTContract.kmtBump (v / (2 : ℝ) ^ k) = 1 := by
      refine ContDiffBump.one_of_mem_closedBall Work.KMTContract.kmtBump ?_
      rw [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs, Work.KMTContract.kmtBump]
      exact hhalf
    rw [hg]
    simp only
    rw [hone]
    norm_num
  have hval : (2 : ℝ) ^ k
      ≤ MeasureTheory.Measure.real (volume : Measure ℝ)
        (Set.Icc (-((2 : ℝ) ^ k / 2)) ((2 : ℝ) ^ k / 2)) := by
    rw [MeasureTheory.measureReal_def, Real.volume_Icc,
      show ((2 : ℝ) ^ k / 2) - (-((2 : ℝ) ^ k / 2)) = (2 : ℝ) ^ k from by ring]
    exact le_of_eq (ENNReal.toReal_ofReal h2k.le).symm
  have heq : (2 : ℝ) ^ k ≤ ∫ v in Set.Icc (-((2 : ℝ) ^ k / 2)) ((2 : ℝ) ^ k / 2), g v := by
    rw [MeasureTheory.setIntegral_congr_fun measurableSet_Icc hcongr,
      MeasureTheory.setIntegral_const, smul_eq_mul, mul_one]
    exact hval
  have hpos : 0 < ∫ v : ℝ, g v := lt_of_lt_of_le h2k (le_trans heq hle)
  have hmain : (∫ v : ℝ, cBump k v * cBump k v) = ((∫ v : ℝ, g v : ℝ) : ℂ) := by
    rw [show (fun v : ℝ => cBump k v * cBump k v) = (fun v : ℝ => ((g v : ℝ) : ℂ)) from
      funext (fun v => by rw [hg, cBump_mul_self_eq])]
    exact integral_ofReal
  intro hzero
  have hre : ((∫ v : ℝ, g v : ℝ) : ℂ) = 0 := hmain.symm.trans hzero
  have hzero' : (∫ v : ℝ, g v) = 0 := by
    simpa using congrArg Complex.re hre
  linarith

/-! ## Positivity of the `ℒ²(ℤ)` norm -/

/-- The `p`-th power of the `ℒᵖ` seminorm over the counting measure on `ℤ` is the `p`-sum (the
same statement as `Work.A7HiRep.tsum_rpow_eq_eLpNorm_rpow`, proved here to avoid the import). -/
theorem tsum_rpow_eq_eLpNorm_rpow_local {p : ℝ} (hp : 0 < p) (F : ℤ → ENNReal) :
    (∑' m : ℤ, (F m) ^ p)
      = (MeasureTheory.eLpNorm F (ENNReal.ofReal p) MeasureTheory.Measure.count) ^ p := by
  rw [MeasureTheory.eLpNorm_eq_lintegral_rpow_enorm_toReal (hf := by pw_aesm) (ENNReal.ofReal_ne_zero_iff.mpr hp)
    ENNReal.ofReal_ne_top, ENNReal.toReal_ofReal hp.le]
  have h1 : (∫⁻ m : ℤ, ‖F m‖ₑ ^ p ∂MeasureTheory.Measure.count) = ∑' m : ℤ, (F m) ^ p := by
    rw [MeasureTheory.lintegral_count]
    exact tsum_congr fun m => by rw [enorm_eq_self]
  rw [h1, ← ENNReal.rpow_mul, one_div, inv_mul_cancel₀ hp.ne', ENNReal.rpow_one]

/-! ## The refutation -/

/-! ## The requested statement, kept verbatim (it is FALSE, see `not_varEstTle_compositeCompare`) -/

theorem varEstTle_compositeCompare (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
    (r : NNReal) (hr : 2 < r) (p : ENNReal) (hp : 1 < p) (hptop : p < ⊤) :
    ∃ Cρ : ℝ, 0 < Cρ ∧ ∃ K : ℝ, 0 < K ∧
      ∀ (l : ℕ) (k : ℤ) (hgm : Work.Analysis.IonescuWainger.GoodMajorArcs ρ Cρ l k)
        (hk : (2 : ℝ) ^ k < 1 / 2)
        (Φ : ℕ → ℝ → ℂ) (Ψ : ℕ → ℝ → ℂ) (M : NNReal)
        (hnarΦ : ∀ n ξ, Φ n ξ ≠ 0 → ξ ∈ Work.Analysis.IonescuWainger.realArc k)
        (hnarΨ : ∀ n ξ, Ψ n ξ ≠ 0 → ξ ∈ Work.Analysis.IonescuWainger.realArc k)
        (hMult : ∀ (U : Finset ℕ) (ω : ℕ → Bool) (q : ENNReal) (hq : 1 < q) (hqt : q < ⊤),
          Work.Analysis.IWMultiplier.IsLqMultiplierBound q
            (fun ξ : ℝ => ∑ n ∈ U, (if ω n then (1 : ℂ) else -1) * (Φ n ξ + Ψ n ξ)) M)
        (f : ℤ → ℂ),
        MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
            (fun n : ℕ => Work.KMTAreas.A7.Tle ρ l (Φ n)
              (Work.KMTAreas.A7.Tle ρ l (Ψ n) f) x)) p MeasureTheory.Measure.count
        ≤ ENNReal.ofReal (K * M) * MeasureTheory.eLpNorm (fun x : ℤ =>
            PointwiseErgodicTheorems.variationalNorm r
              (fun n : ℕ => Work.KMTAreas.A7.Tle ρ l (Ψ n) f x)) p
            MeasureTheory.Measure.count := by sorry

end

end Work.A7Hi
