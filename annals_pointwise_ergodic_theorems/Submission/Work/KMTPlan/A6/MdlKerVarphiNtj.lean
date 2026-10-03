/-
# A summable majorant for the kernel of `Tle ρ l` applied to the modified bump `φ_{N,t,-1}`

This module proves `Work.KMTPlan.A6.MdlKerVarphiNtj`: for the *modified* bump of the
integration-by-parts identity of Krause--Mirek--Tao §6,

  `φ_{N,t,-1}(ξ) = varphiNtj N k (-1) t ξ = (2^{-k}Nξ)^{-1} φ_N(ξ) e(Ntξ)`   (`1 ≤ k`),

the convolution kernel `i ↦ mdlIWKer ρ l (φ_{N,t,-1}) i` of the Ionescu--Wainger projection
`Tle ρ l φ_{N,t,-1}` admits a *summable majorant in `i`*, uniform in `t ∈ [1/2,1]`, and is
measurable in `t`; moreover `φ_{N,t,-1}` is integrable.

The plan is exactly that of the already-proved sibling `Work.KMTPlan.A6.MdlKerVarphiNt` (the
`k = 0`, `j = 0` bump `varphiNt`), with the modulated bump replaced by `varphiNtj N k (-1) t`:

* `mdlBumpNeg1 N k = (2^{-k}Nξ)^{-1} φ_N(ξ)` is the unmodulated modified bump.  For `1 ≤ k` it is
  `C²` with compact support: `φ_N(ξ) = η(2^{Log N-k}ξ) - η(2^{Log N-k+1}ξ)` *vanishes identically*
  for `|ξ| < 2^{k - Log N - 2}` (`varphiN_eq_zero_of_abs_lt`), so the singular factor
  `(2^{-k}Nξ)^{-1}` is multiplied by something flat at `0`; away from `0` the product is smooth.
* `varphiNtj N k (-1) t = mdlBumpNeg1 N k · e(Nt·)` (`varphiNtj_neg1_apply`), and
  `norm_iteratedDeriv_two_mul_ee_le` bounds the second derivative of the modulated bump by
  `‖q''‖ + 2(2πN)‖q'‖ + (2πN)²‖q‖` (using `|t| ≤ 1`).
* the kernel decay `Work.KMTAreas.A7.iwKernel_decay_of_bump` (with `C²` + compact support and the
  two uniform `L¹`-bounds of `varphiNtj_bounds`) gives
  `‖mdlIWKer ρ l φ i‖ ≤ (4 (card A) S + 1) ‖kmtKernWeight i‖`, whose right-hand side is summable.
* measurability in `t` comes from `Work.KMTAreas.A7.measurable_fourierCoeff_iwSymbolSet` applied
  to the jointly measurable family `(t,ξ) ↦ varphiNtj N k (-1) t ξ`.
-/
import Mathlib
import Submission.Work.KMTPlan.A6.MdlDecayDefs
import Submission.Work.KMTAreas.A7.Tle_varphiNt_bounded

set_option maxHeartbeats 1000000

namespace Work.KMTPlan.A6

noncomputable section

open MeasureTheory Filter
open scoped Topology
open Work.KMTAreas.A7

/-! ## The unmodulated modified bump `(2^{-k}Nξ)^{-1} φ_N(ξ)` -/

/-- The unmodulated modified bump `q(ξ) = (2^{-k}Nξ)^{-1} φ_N(ξ)` of the integration-by-parts
identity (the modulation `e(Ntξ)` split off). -/
def mdlBumpNeg1 (N k : ℕ) : ℝ → ℂ :=
  fun ξ => ((((2 : ℝ) ^ (-(k : ℝ)) * (N : ℝ) * ξ : ℝ)) : ℂ)⁻¹ * varphiN N k ξ

/-- The modified bump `varphiNtj N k (-1) t` is the modulation `e(Nt·)` times `mdlBumpNeg1 N k`. -/
theorem varphiNtj_neg1_apply (N k : ℕ) (t ξ : ℝ) :
    varphiNtj N k (-1) t ξ = mdlBumpNeg1 N k ξ * ee ((N : ℝ) * t * ξ) := by
  simp only [varphiNtj, varphiNt, mdlBumpNeg1, zpow_neg_one, mul_assoc]

/-- **`φ_N` vanishes on a neighbourhood of the origin** (for `k ≥ 1`): it is identically zero on
`|ξ| < 2^{k - Log N - 2}`, where both cutoffs `η(2^{Log N-k}ξ)`, `η(2^{Log N-k+1}ξ)` equal `1`. -/
theorem varphiN_eq_zero_of_abs_lt (N k : ℕ) (hk : 1 ≤ k) {y : ℝ}
    (hy : |y| < (1 / 4 : ℝ) * (2 : ℝ) ^ ((k : ℝ) - (Work.Analysis.EndVar.logN N : ℝ))) :
    varphiN N k y = 0 := by
  have hk0 : k ≠ 0 := by omega
  simp only [varphiN, if_neg hk0]
  have hδpos : 0 < (2 : ℝ) ^ ((Work.Analysis.EndVar.logN N : ℝ) - (k : ℝ)) :=
    Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) _
  have hdelta : (2 : ℝ) ^ ((k : ℝ) - (Work.Analysis.EndVar.logN N : ℝ)) =
      ((2 : ℝ) ^ ((Work.Analysis.EndVar.logN N : ℝ) - (k : ℝ)))⁻¹ := by
    rw [show (k : ℝ) - (Work.Analysis.EndVar.logN N : ℝ) =
        -((Work.Analysis.EndVar.logN N : ℝ) - (k : ℝ)) by ring,
      Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)]
  have hmain : (2 : ℝ) ^ ((Work.Analysis.EndVar.logN N : ℝ) - (k : ℝ)) * |y| < 1 / 4 := by
    have h := mul_lt_mul_of_pos_left hy hδpos
    rw [hdelta] at h
    have heq : (2 : ℝ) ^ ((Work.Analysis.EndVar.logN N : ℝ) - (k : ℝ)) *
        ((1 / 4 : ℝ) * ((2 : ℝ) ^ ((Work.Analysis.EndVar.logN N : ℝ) - (k : ℝ)))⁻¹) = 1 / 4 := by
      calc (2 : ℝ) ^ ((Work.Analysis.EndVar.logN N : ℝ) - (k : ℝ)) *
            ((1 / 4 : ℝ) * ((2 : ℝ) ^ ((Work.Analysis.EndVar.logN N : ℝ) - (k : ℝ)))⁻¹)
          = (1 / 4 : ℝ) *
              ((2 : ℝ) ^ ((Work.Analysis.EndVar.logN N : ℝ) - (k : ℝ)) *
                ((2 : ℝ) ^ ((Work.Analysis.EndVar.logN N : ℝ) - (k : ℝ)))⁻¹) := by ring
        _ = (1 / 4 : ℝ) * 1 := by rw [mul_inv_cancel₀ (ne_of_gt hδpos)]
        _ = 1 / 4 := by ring
    linarith [h, heq]
  have h1 : |(2 : ℝ) ^ ((Work.Analysis.EndVar.logN N : ℝ) - (k : ℝ)) * y| ≤ 1 / 2 := by
    rw [abs_mul, abs_of_pos hδpos]
    linarith [hmain]
  have h2 : |(2 : ℝ) ^ ((Work.Analysis.EndVar.logN N : ℝ) - (k : ℝ) + 1) * y| ≤ 1 / 2 := by
    have hpow : (2 : ℝ) ^ ((Work.Analysis.EndVar.logN N : ℝ) - (k : ℝ) + 1) =
        2 * (2 : ℝ) ^ ((Work.Analysis.EndVar.logN N : ℝ) - (k : ℝ)) := by
      rw [show (Work.Analysis.EndVar.logN N : ℝ) - (k : ℝ) + 1 =
          ((Work.Analysis.EndVar.logN N : ℝ) - (k : ℝ)) + 1 by ring,
        Real.rpow_add (by norm_num : (0 : ℝ) < 2), Real.rpow_one]
      ring
    have hpos : 0 < (2 : ℝ) ^ ((Work.Analysis.EndVar.logN N : ℝ) - (k : ℝ) + 1) :=
      Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) _
    rw [abs_mul, abs_of_pos hpos, hpow]
    nlinarith [hmain]
  rw [Work.KMTContract.kmtEta_one h1, Work.KMTContract.kmtEta_one h2, sub_self]

/-- `φ_N` vanishes strictly beyond `2^{k - Log N}`. -/
theorem varphiN_eq_zero_of_lt_abs (N k : ℕ) {y : ℝ}
    (hy : (2 : ℝ) ^ ((k : ℝ) - (Work.Analysis.EndVar.logN N : ℝ)) < |y|) :
    varphiN N k y = 0 := by
  by_contra h
  exact absurd (varphiN_support N k y h) (not_le.mpr hy)

/-! ## Smoothness and compact support of `mdlBumpNeg1` -/

theorem contDiff_mdlBumpNeg1 (N k : ℕ) (hk : 1 ≤ k) : ContDiff ℝ 2 (mdlBumpNeg1 N k) := by
  rcases Nat.eq_zero_or_pos N with hN | hN
  · subst hN
    have hzero : mdlBumpNeg1 0 k = fun _ : ℝ => (0 : ℂ) := by
      funext ξ
      simp only [mdlBumpNeg1, Nat.cast_zero, mul_zero, zero_mul, Complex.ofReal_zero, inv_zero]
    rw [hzero]
    exact contDiff_const
  · rw [contDiff_iff_contDiffAt]
    intro x
    by_cases hx : |x| < (1 / 4 : ℝ) * (2 : ℝ) ^ ((k : ℝ) - (Work.Analysis.EndVar.logN N : ℝ))
    · -- `q` vanishes on the neighbourhood `Ioo (-δ) δ` of `x`
      have hδpos : 0 < (1 / 4 : ℝ) * (2 : ℝ) ^ ((k : ℝ) - (Work.Analysis.EndVar.logN N : ℝ)) := by
        positivity
      have hxmem : x ∈ Set.Ioo
          (-((1 / 4 : ℝ) * (2 : ℝ) ^ ((k : ℝ) - (Work.Analysis.EndVar.logN N : ℝ))))
          ((1 / 4 : ℝ) * (2 : ℝ) ^ ((k : ℝ) - (Work.Analysis.EndVar.logN N : ℝ))) :=
        ⟨by have := neg_abs_le x; linarith, lt_of_le_of_lt (le_abs_self x) hx⟩
      have hev : mdlBumpNeg1 N k =ᶠ[𝓝 x] (fun _ : ℝ => (0 : ℂ)) := by
        refine Filter.mem_of_superset (isOpen_Ioo.mem_nhds hxmem) (fun y hy => ?_)
        have hyabs : |y| <
            (1 / 4 : ℝ) * (2 : ℝ) ^ ((k : ℝ) - (Work.Analysis.EndVar.logN N : ℝ)) := abs_lt.mpr hy
        have hφ : varphiN N k y = 0 := varphiN_eq_zero_of_abs_lt N k hk hyabs
        simp only [Set.mem_setOf_eq, mdlBumpNeg1, hφ, mul_zero]
      exact contDiffAt_const.congr_of_eventuallyEq hev
    · -- away from the origin `q` is a product of smooth functions
      have hδpos : 0 < (1 / 4 : ℝ) * (2 : ℝ) ^ ((k : ℝ) - (Work.Analysis.EndVar.logN N : ℝ)) := by
        positivity
      have hx0 : x ≠ 0 := by
        intro h
        rw [h, abs_zero] at hx
        exact absurd hδpos hx
      have hc : (0 : ℝ) < (2 : ℝ) ^ (-(k : ℝ)) * (N : ℝ) := by positivity
      have hval : (2 : ℝ) ^ (-(k : ℝ)) * (N : ℝ) * x ≠ 0 :=
        mul_ne_zero (ne_of_gt hc) hx0
      have hvalC : ((((2 : ℝ) ^ (-(k : ℝ)) * (N : ℝ) * x : ℝ)) : ℂ) ≠ 0 :=
        fun h => hval (Complex.ofReal_injective h)
      have hlin : ContDiffAt ℝ 2 (fun ξ : ℝ =>
          ((((2 : ℝ) ^ (-(k : ℝ)) * (N : ℝ) * ξ : ℝ)) : ℂ)) x := by
        have h1 : ContDiff ℝ 2 (fun ξ : ℝ => (2 : ℝ) ^ (-(k : ℝ)) * (N : ℝ) * ξ) :=
          (contDiff_const (c := (2 : ℝ) ^ (-(k : ℝ)) * (N : ℝ))).mul contDiff_id
        exact (Complex.ofRealCLM.contDiff.comp h1).contDiffAt
      have hinv : ContDiffAt ℝ 2 (fun ξ : ℝ =>
          ((((2 : ℝ) ^ (-(k : ℝ)) * (N : ℝ) * ξ : ℝ)) : ℂ)⁻¹) x := by
        have h : ContDiffAt ℝ 2 (fun z : ℂ => z⁻¹)
            ((((2 : ℝ) ^ (-(k : ℝ)) * (N : ℝ) * x : ℝ)) : ℂ) :=
          (contDiffAt_id (𝕜 := ℝ)).inv hvalC
        simpa only [Function.comp_def] using h.comp x hlin
      show ContDiffAt ℝ 2 (fun ξ : ℝ =>
          ((((2 : ℝ) ^ (-(k : ℝ)) * (N : ℝ) * ξ : ℝ)) : ℂ)⁻¹ * varphiN N k ξ) x
      exact hinv.mul ((contDiff_varphiN N k).contDiffAt)

theorem hasCompactSupport_mdlBumpNeg1 (N k : ℕ) : HasCompactSupport (mdlBumpNeg1 N k) := by
  refine HasCompactSupport.of_support_subset_isCompact (K := Set.Icc
    (-((2 : ℝ) ^ ((k : ℝ) - (Work.Analysis.EndVar.logN N : ℝ))))
    ((2 : ℝ) ^ ((k : ℝ) - (Work.Analysis.EndVar.logN N : ℝ)))) isCompact_Icc ?_
  intro x hx
  have hφ : varphiN N k x ≠ 0 := fun h => hx (by simp only [mdlBumpNeg1, h, mul_zero])
  exact abs_le.mp (varphiN_support N k x hφ)

theorem hcs_iteratedDeriv_mdlBumpNeg1 (N k m : ℕ) (hm : m ≤ 2) :
    HasCompactSupport (iteratedDeriv m (mdlBumpNeg1 N k)) := by
  interval_cases m
  · rw [iteratedDeriv_zero]; exact hasCompactSupport_mdlBumpNeg1 N k
  · rw [iteratedDeriv_one]; exact (hasCompactSupport_mdlBumpNeg1 N k).deriv
  · rw [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one]
    exact ((hasCompactSupport_mdlBumpNeg1 N k).deriv).deriv

theorem integrable_iteratedDeriv_mdlBumpNeg1 (N k m : ℕ) (hk : 1 ≤ k) (hm : m ≤ 2) :
    Integrable (fun y => ‖iteratedDeriv m (mdlBumpNeg1 N k) y‖) := by
  have hcont : Continuous (iteratedDeriv m (mdlBumpNeg1 N k)) :=
    (contDiff_mdlBumpNeg1 N k hk).continuous_iteratedDeriv m (by exact_mod_cast hm)
  exact (hcont.integrable_of_hasCompactSupport (hcs_iteratedDeriv_mdlBumpNeg1 N k m hm)).norm

/-! ## The price of the modulation -/

/-- The second derivative of `q · e(Nt·)` is dominated by the second derivative of `q`, the
`2(2πN)`-multiple of its first derivative and the `(2πN)²`-multiple of `q` itself, for
`t ∈ [1/2,1]`. -/
theorem norm_iteratedDeriv_two_mdlBumpNeg1_le (N _k : ℕ) {q : ℝ → ℂ} (hq : ContDiff ℝ 2 q)
    (t : ℝ) (ht : t ∈ Set.Icc (1/2 : ℝ) 1) (y : ℝ) :
    ‖iteratedDeriv 2 (fun ξ : ℝ => q ξ * ee (((N : ℝ) * t) * ξ)) y‖ ≤
      ‖iteratedDeriv 2 q y‖ + (2 * (2 * Real.pi * (N : ℝ))) * ‖iteratedDeriv 1 q y‖
        + (2 * Real.pi * (N : ℝ)) ^ 2 * ‖q y‖ := by
  have hb := norm_iteratedDeriv_two_mul_ee_le q ((N : ℝ) * t) hq y
  have htabs : |t| ≤ 1 := by
    rw [abs_le]; exact ⟨by linarith [ht.1], ht.2⟩
  have hc : |(N : ℝ) * t| ≤ (N : ℝ) := by
    rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg N)]
    exact mul_le_of_le_one_right (Nat.cast_nonneg N) htabs
  refine le_trans hb ?_
  have h1 : 2 * (2 * Real.pi * |(N : ℝ) * t|) * ‖iteratedDeriv 1 q y‖ ≤
      2 * (2 * Real.pi * (N : ℝ)) * ‖iteratedDeriv 1 q y‖ := by gcongr
  have h2 : (2 * Real.pi * |(N : ℝ) * t|) ^ 2 * ‖q y‖ ≤
      (2 * Real.pi * (N : ℝ)) ^ 2 * ‖q y‖ := by gcongr
  linarith

/-! ## Uniform bounds for the modified bump -/

theorem varphiNtj_bounds_neg1 (N k : ℕ) (hk : 1 ≤ k) :
    ∃ R S : ℝ, 0 ≤ S ∧ ∀ t ∈ Set.Icc (1/2 : ℝ) 1,
      (∀ y : ℝ, R ≤ |y| → Work.KMTPlan.A6.varphiNtj N k (-1) t y = 0) ∧
      ContDiff ℝ 2 (fun ξ => Work.KMTPlan.A6.varphiNtj N k (-1) t ξ) ∧
      HasCompactSupport (fun ξ => Work.KMTPlan.A6.varphiNtj N k (-1) t ξ) ∧
      (∫ y, ‖Work.KMTPlan.A6.varphiNtj N k (-1) t y‖) ≤ S ∧
      (∫ y, ‖iteratedDeriv 2 (fun ξ => Work.KMTPlan.A6.varphiNtj N k (-1) t ξ) y‖) ≤ S := by
  have hcd : ContDiff ℝ 2 (mdlBumpNeg1 N k) := contDiff_mdlBumpNeg1 N k hk
  have hcs : HasCompactSupport (mdlBumpNeg1 N k) := hasCompactSupport_mdlBumpNeg1 N k
  set R : ℝ := (2 : ℝ) ^ ((k : ℝ) - (Work.Analysis.EndVar.logN N : ℝ)) + 1 with hR
  set A : ℝ := ∫ y, ‖mdlBumpNeg1 N k y‖ with hA
  set B : ℝ := ∫ y, ‖iteratedDeriv 1 (mdlBumpNeg1 N k) y‖ with hB
  set C : ℝ := ∫ y, ‖iteratedDeriv 2 (mdlBumpNeg1 N k) y‖ with hC
  set S : ℝ := A + 2 * (2 * Real.pi * (N : ℝ)) * B + (2 * Real.pi * (N : ℝ)) ^ 2 * A + C + 1
    with hS
  have hA0 : 0 ≤ A := by rw [hA]; exact integral_nonneg (fun y => norm_nonneg _)
  have hB0 : 0 ≤ B := by rw [hB]; exact integral_nonneg (fun y => norm_nonneg _)
  have hC0 : 0 ≤ C := by rw [hC]; exact integral_nonneg (fun y => norm_nonneg _)
  have hcoef1 : 0 ≤ 2 * (2 * Real.pi * (N : ℝ)) * B :=
    mul_nonneg (mul_nonneg (by norm_num) (by positivity)) hB0
  have hcoef2 : 0 ≤ (2 * Real.pi * (N : ℝ)) ^ 2 * A := mul_nonneg (by positivity) hA0
  have hSnn : 0 ≤ S := by rw [hS]; linarith
  refine ⟨R, S, hSnn, ?_⟩
  intro t ht
  have hmod : ∀ ξ : ℝ, Work.KMTPlan.A6.varphiNtj N k (-1) t ξ =
      mdlBumpNeg1 N k ξ * ee (((N : ℝ) * t) * ξ) := by
    intro ξ
    rw [varphiNtj_neg1_apply]
  have hfun : (fun ξ : ℝ => Work.KMTPlan.A6.varphiNtj N k (-1) t ξ) =
      fun ξ => mdlBumpNeg1 N k ξ * ee (((N : ℝ) * t) * ξ) := funext hmod
  have hsupp : ∀ y : ℝ, R ≤ |y| → Work.KMTPlan.A6.varphiNtj N k (-1) t y = 0 := by
    intro y hy
    rw [hmod y]
    have hy' : (2 : ℝ) ^ ((k : ℝ) - (Work.Analysis.EndVar.logN N : ℝ)) < |y| := by
      rw [hR] at hy; linarith
    have hφ : varphiN N k y = 0 := varphiN_eq_zero_of_lt_abs N k hy'
    simp only [mdlBumpNeg1, hφ, mul_zero, zero_mul]
  refine ⟨hsupp, ?_, ?_, ?_, ?_⟩
  · rw [hfun]
    exact hcd.mul (contDiff_ee_const_mul 2 ((N : ℝ) * t))
  · refine HasCompactSupport.of_support_subset_isCompact (K := Set.Icc (-R) R) isCompact_Icc ?_
    intro y hy
    have hle : ¬ (R ≤ |y|) := fun h => hy (hsupp y h)
    rw [Set.mem_Icc, ← abs_le]
    exact le_of_lt (not_le.mp hle)
  · have hcongr : (fun y => ‖Work.KMTPlan.A6.varphiNtj N k (-1) t y‖) =
        fun y => ‖mdlBumpNeg1 N k y‖ := by
      funext y
      rw [hmod y, norm_mul, norm_ee, mul_one]
    rw [hcongr, ← hA, hS]
    linarith
  · have hpt : ∀ y, ‖iteratedDeriv 2 (fun ξ => Work.KMTPlan.A6.varphiNtj N k (-1) t ξ) y‖ ≤
        ‖iteratedDeriv 2 (mdlBumpNeg1 N k) y‖ +
          (2 * (2 * Real.pi * (N : ℝ))) * ‖iteratedDeriv 1 (mdlBumpNeg1 N k) y‖ +
          (2 * Real.pi * (N : ℝ)) ^ 2 * ‖mdlBumpNeg1 N k y‖ := by
      intro y
      have h := norm_iteratedDeriv_two_mdlBumpNeg1_le N k hcd t ht y
      simpa only [hfun] using h
    have hI1 : Integrable (fun y => ‖iteratedDeriv 2 (mdlBumpNeg1 N k) y‖) :=
      integrable_iteratedDeriv_mdlBumpNeg1 N k 2 hk le_rfl
    have hI2 : Integrable (fun y => (2 * (2 * Real.pi * (N : ℝ))) *
        ‖iteratedDeriv 1 (mdlBumpNeg1 N k) y‖) :=
      (integrable_iteratedDeriv_mdlBumpNeg1 N k 1 hk (by norm_num)).const_mul _
    have hI3 : Integrable (fun y => (2 * Real.pi * (N : ℝ)) ^ 2 * ‖mdlBumpNeg1 N k y‖) := by
      simpa using (integrable_iteratedDeriv_mdlBumpNeg1 N k 0 hk (by norm_num)).const_mul
        ((2 * Real.pi * (N : ℝ)) ^ 2)
    have hI12 : Integrable (fun y => ‖iteratedDeriv 2 (mdlBumpNeg1 N k) y‖ +
        (2 * (2 * Real.pi * (N : ℝ))) * ‖iteratedDeriv 1 (mdlBumpNeg1 N k) y‖) := hI1.add hI2
    have hmaj : Integrable (fun y => (‖iteratedDeriv 2 (mdlBumpNeg1 N k) y‖ +
        (2 * (2 * Real.pi * (N : ℝ))) * ‖iteratedDeriv 1 (mdlBumpNeg1 N k) y‖) +
        (2 * Real.pi * (N : ℝ)) ^ 2 * ‖mdlBumpNeg1 N k y‖) := hI12.add hI3
    have hLint : Integrable (fun y =>
        ‖iteratedDeriv 2 (fun ξ => Work.KMTPlan.A6.varphiNtj N k (-1) t ξ) y‖) := by
      have hcont : Continuous (fun y =>
          ‖iteratedDeriv 2 (fun ξ => Work.KMTPlan.A6.varphiNtj N k (-1) t ξ) y‖) := by
        rw [hfun]
        exact ((hcd.mul (contDiff_ee_const_mul 2 ((N : ℝ) * t))).continuous_iteratedDeriv 2
          le_rfl).norm
      exact hmaj.mono' hcont.aestronglyMeasurable
        (Filter.Eventually.of_forall (fun y => by simpa only [norm_norm] using hpt y))
    have hmono := integral_mono hLint hmaj hpt
    have heq : (∫ y, (‖iteratedDeriv 2 (mdlBumpNeg1 N k) y‖ +
            (2 * (2 * Real.pi * (N : ℝ))) * ‖iteratedDeriv 1 (mdlBumpNeg1 N k) y‖ +
            (2 * Real.pi * (N : ℝ)) ^ 2 * ‖mdlBumpNeg1 N k y‖))
        = C + (2 * (2 * Real.pi * (N : ℝ))) * B + (2 * Real.pi * (N : ℝ)) ^ 2 * A := by
      rw [integral_add hI12 hI3, integral_add hI1 hI2, integral_const_mul, integral_const_mul,
        ← hA, ← hB, ← hC]
    have hfinal : (∫ y, ‖iteratedDeriv 2 (fun ξ => Work.KMTPlan.A6.varphiNtj N k (-1) t ξ) y‖) ≤
        C + (2 * (2 * Real.pi * (N : ℝ))) * B + (2 * Real.pi * (N : ℝ)) ^ 2 * A :=
      le_trans hmono (le_of_eq heq)
    rw [hS]
    linarith

/-! ## Measurability in `t` -/

/-- Joint measurability of `(t, ξ) ↦ varphiNtj N k (-1) t ξ`. -/
theorem measurable_varphiNtj_neg1_uncurry (N k : ℕ) :
    Measurable fun p : ℝ × ℝ => varphiNtj N k (-1) p.1 p.2 := by
  have hz : Measurable fun p : ℝ × ℝ =>
      ((((2 : ℝ) ^ (-(k : ℝ)) * (N : ℝ) * p.2 : ℝ)) : ℂ) :=
    Complex.continuous_ofReal.measurable.comp
      (((continuous_const.mul continuous_const).mul continuous_snd).measurable)
  have h1 : Measurable fun p : ℝ × ℝ =>
      ((((2 : ℝ) ^ (-(k : ℝ)) * (N : ℝ) * p.2 : ℝ)) : ℂ)⁻¹ := hz.inv
  have h2 : Measurable fun p : ℝ × ℝ => varphiNt N k p.1 p.2 := by
    have hee : Measurable ee := by unfold ee; fun_prop
    unfold varphiNt
    exact ((contDiff_varphiN N k).continuous.measurable.comp measurable_snd).mul
      (hee.comp ((measurable_fst.const_mul (N : ℝ)).mul measurable_snd))
  have hprod : Measurable fun p : ℝ × ℝ =>
      ((((2 : ℝ) ^ (-(k : ℝ)) * (N : ℝ) * p.2 : ℝ)) : ℂ)⁻¹ * varphiNt N k p.1 p.2 :=
    h1.mul h2
  simpa only [varphiNtj, zpow_neg_one] using hprod

/-- Measurability in `t` of the IW kernel of the modified bump `varphiNtj N k (-1) t`. -/
theorem measurable_iwKernel_varphiNtj_neg1 (ρ : ℝ) (l N k : ℕ) (j : ℤ) :
    Measurable (fun t : ℝ => Work.Analysis.IWMultiplier.iwKernel
      (Work.Analysis.IonescuWainger.iwSymbolSet (Work.Analysis.IonescuWainger.iwArithFreqs ρ l)
        (Work.Analysis.IonescuWainger.periodize (varphiNtj N k (-1) t))) j) := by
  have h := measurable_fourierCoeff_iwSymbolSet (Work.Analysis.IonescuWainger.iwArithFreqs ρ l) j
    (φ := fun t ξ => varphiNtj N k (-1) t ξ) (measurable_varphiNtj_neg1_uncurry N k)
  simpa only [Work.Analysis.IWMultiplier.iwKernel] using h

/-! ## The target -/

/-- A summable majorant for the convolution kernel of `Tle ρ l` applied to the *modified* bump
`φ_{N,t,-1} = varphiNtj N k (-1) t` (the one produced by the integration-by-parts identity, hence
the hypothesis `1 ≤ k`, without which it is not integrable), uniform in `t ∈ [1/2,1]`, together
with the integrability of the bump and the measurability in `t` of the kernel. -/
theorem MdlKerVarphiNtj (ρ : ℝ) (l N k : ℕ) (hk : 1 ≤ k) :
    (∀ t ∈ Set.Icc (1/2 : ℝ) 1, MeasureTheory.Integrable (Work.KMTPlan.A6.varphiNtj N k (-1) t)) ∧
      ∃ a : ℤ → ℝ, Summable a ∧
      (∀ t ∈ Set.Icc (1/2 : ℝ) 1, ∀ i : ℤ,
        ‖Work.KMTPlan.A6.mdlIWKer ρ l (Work.KMTPlan.A6.varphiNtj N k (-1) t) i‖ ≤ a i) ∧
      (∀ i : ℤ, Measurable (fun t : ℝ =>
        Work.KMTPlan.A6.mdlIWKer ρ l (Work.KMTPlan.A6.varphiNtj N k (-1) t) i)) := by
  classical
  obtain ⟨R, S, hSnn, hB⟩ := varphiNtj_bounds_neg1 N k hk
  refine ⟨?_, fun i => (4 * (((Work.Analysis.IonescuWainger.iwArithFreqs ρ l).card : ℝ) * S) + 1)
      * ‖Work.KMTAreas.A7.kmtKernWeight i‖, ?_, ?_, ?_⟩
  · intro t ht
    exact ((hB t ht).2.1.continuous).integrable_of_hasCompactSupport (hB t ht).2.2.1
  · exact Work.KMTAreas.A7.summable_kmtKernWeight.mul_left _
  · intro t ht i
    obtain ⟨-, hcd, hcs, h1, h2⟩ := hB t ht
    have h := Work.KMTAreas.A7.iwKernel_decay_of_bump (Work.Analysis.IonescuWainger.iwArithFreqs ρ l)
      hcd hcs hSnn h1 h2 i
    exact h
  · intro i
    have h := measurable_iwKernel_varphiNtj_neg1 ρ l N k i
    simpa only [mdlIWKer, Work.KMTAreas.A7.iwKer] using h

end

end Work.KMTPlan.A6
