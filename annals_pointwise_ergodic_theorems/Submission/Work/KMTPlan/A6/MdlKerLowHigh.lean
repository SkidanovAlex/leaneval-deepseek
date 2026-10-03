/-
# The kernel packages of the two modified bumps of the low-high case

The operator-level integration-by-parts identity (ii) of §6 (the `(k₁,k₂) = (0,k₂)`, `k₂ ≥ 1` case,
`Work.KMTPlan.A6.MdlDecayLowHigh`) involves, beyond the two *unmodified* modulated bumps
`φ_{N,t}`, `φ̃_{N,t}` (whose kernel packages are `MdlKerVarphiNt`, `MdlKerVarphitildeNt`), the two
*modified* bumps

* `varphiNtj N 0 1 t ξ = (Nξ) φ_{N,t}(ξ)` (the `f`-side, `j = +1`, bottom scale `k₁ = 0`), and
* `varphitildeNtj P N k₂ (-1) t ξ = (2^{-dk₂}N^dξ)^{-1} φ̃_{N,t}(ξ)` (the `g`-side, `j = -1`,
  `k₂ ≥ 1`),

which are the two `t`-dependences produced by identity (ii).  This module proves, for each of them,
the three facts needed to interchange the `t`-integral with the convolution series of the §6
functional calculus (`Work.KMTPlan.A6.MdlNFIntegral`):

* integrability of the bump (needed for `mdlIWKer_eq_cw`);
* a *summable* majorant of the convolution kernel `mdlIWKer ρ l (bump t) ·`, uniform in
  `t ∈ [1/2,1]` (obtained from `iwKernel_decay_of_bump`, whose hypotheses are the uniform `C²` /
  compact-support / `L¹`-bounds of the bump and of its second derivative, from
  `varphiNtj_bounds` / the amplitude `mdlAmpNeg` below);
* measurability in `t` of each kernel coefficient
  (`measurable_fourierCoeff_iwSymbolSet`).
-/
import Mathlib
import Submission.Work.KMTPlan.A6.MdlDecayDefs
import Submission.Work.KMTPlan.A6.varphiNtj_bounds
import Submission.Work.KMTPlan.A6.varphiNt_modulation_bounds
import Submission.Work.KMTAreas.A7.abs_PevalR_mul_le
import Submission.Work.KMTAreas.A7.fourierDecay_varphitildeN
import Submission.Work.KMTAreas.A7.Tle_varphiNt_bounded

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Work.KMTPlan.A6

noncomputable section

open MeasureTheory Polynomial Finset Filter Topology
open scoped ENNReal NNReal BigOperators Interval
open Work.Analysis.EndVar
open Work.KMTAreas.A7
open Work.Analysis.IonescuWainger

/-! ## The `f`-side modified bump `(2^{-k}Nξ) φ_{N,t}(ξ)` -/

/-- The amplitude of the modified bump `varphiNtj N k 1 t`: `ξ ↦ 2^{-k}Nξ · φ_N(ξ)` (the phase
`e(Ntξ)` is factored out). -/
def mdlAmpPos (N k : ℕ) : ℝ → ℂ :=
  fun ξ => ((((2 : ℝ) ^ (-(k : ℝ)) * (N : ℝ) * ξ : ℝ)) : ℂ) * varphiN N k ξ

/-- The modified bump is the modulation of its amplitude. -/
theorem varphiNtj_one_eq (N k : ℕ) (t : ℝ) :
    varphiNtj N k 1 t = fun ξ => mdlAmpPos N k ξ * ee (((N : ℝ) * t) * ξ) := by
  funext ξ
  simp only [varphiNtj, varphiNt, mdlAmpPos, zpow_one, Pi.mul_apply]
  ring

theorem contDiff_mdlAmpPos (N k : ℕ) : ContDiff ℝ 2 (mdlAmpPos N k) := by
  unfold mdlAmpPos
  refine ContDiff.mul ?_ (contDiff_varphiN N k)
  exact (Complex.ofRealCLM.contDiff (n := 2)).comp
    ((contDiff_const (c := (2 : ℝ) ^ (-(k : ℝ)) * (N : ℝ))).mul contDiff_id)

theorem hasCompactSupport_mdlAmpPos (N k : ℕ) : HasCompactSupport (mdlAmpPos N k) := by
  refine (hasCompactSupport_varphiN N k).mono ?_
  intro ξ hξ
  simp only [Function.mem_support] at hξ ⊢
  intro h
  exact hξ (by simp only [mdlAmpPos, h, mul_zero])

/-- **The kernel package of the `f`-side modified bump** `varphiNtj N k 1 t`. -/
theorem mdlKerVarphiNtjOne (ρ : ℝ) (l N k : ℕ) :
    (∀ t ∈ Set.Icc (1/2 : ℝ) 1, MeasureTheory.Integrable (varphiNtj N k 1 t)) ∧
      ∃ a : ℤ → ℝ, Summable a ∧
      (∀ t ∈ Set.Icc (1/2 : ℝ) 1, ∀ i : ℤ,
        ‖mdlIWKer ρ l (varphiNtj N k 1 t) i‖ ≤ a i) ∧
      (∀ i : ℤ, Measurable (fun t : ℝ => mdlIWKer ρ l (varphiNtj N k 1 t) i)) := by
  obtain ⟨S, hSnn, hS⟩ := varphiNt_modulation_bounds N (mdlAmpPos N k)
    (contDiff_mdlAmpPos N k) (hasCompactSupport_mdlAmpPos N k)
  have hcd : ∀ t : ℝ, ContDiff ℝ 2 (varphiNtj N k 1 t) := by
    intro t
    rw [varphiNtj_one_eq]
    exact (contDiff_mdlAmpPos N k).mul (contDiff_ee_const_mul 2 ((N : ℝ) * t))
  have hcs : ∀ t : ℝ, HasCompactSupport (varphiNtj N k 1 t) := by
    intro t
    rw [varphiNtj_one_eq]
    exact (hasCompactSupport_mdlAmpPos N k).mono (fun ξ hξ => by
      simp only [Function.mem_support, Pi.mul_apply] at hξ ⊢
      intro h
      exact hξ (by rw [h, zero_mul]))
  have hbnd : ∀ t ∈ Set.Icc (1/2 : ℝ) 1,
      (∫ y, ‖varphiNtj N k 1 t y‖) ≤ S ∧
        (∫ y, ‖iteratedDeriv 2 (varphiNtj N k 1 t) y‖) ≤ S := by
    intro t ht
    rw [varphiNtj_one_eq]
    exact hS t ht
  refine ⟨fun t _ => ?_, ?_⟩
  · exact (hcd t).continuous.integrable_of_hasCompactSupport (hcs t)
  · refine ⟨fun i => (4 * (((iwArithFreqs ρ l).card : ℝ) * S) + 1) * ‖kmtKernWeight i‖,
      summable_kmtKernWeight.mul_left _, fun t ht i => ?_, fun i => ?_⟩
    · exact iwKernel_decay_of_bump (iwArithFreqs ρ l) (hcd t) (hcs t) hSnn
        (hbnd t ht).1 (hbnd t ht).2 i
    · have hmeas : Measurable fun p : ℝ × ℝ => varphiNtj N k 1 p.1 p.2 := by
        have hz : Measurable fun p : ℝ × ℝ =>
            ((((2 : ℝ) ^ (-(k : ℝ)) * (N : ℝ) * p.2 : ℝ)) : ℂ) :=
          Complex.continuous_ofReal.measurable.comp
            (((continuous_const.mul continuous_const).mul continuous_snd).measurable)
        have h1 : Measurable fun p : ℝ × ℝ =>
            ((((2 : ℝ) ^ (-(k : ℝ)) * (N : ℝ) * p.2 : ℝ)) : ℂ) := hz
        have h2 : Measurable fun p : ℝ × ℝ => varphiNt N k p.1 p.2 := by
          have hee : Measurable ee := by unfold ee; fun_prop
          unfold varphiNt
          exact ((contDiff_varphiN N k).continuous.measurable.comp measurable_snd).mul
            (hee.comp ((measurable_fst.const_mul (N : ℝ)).mul measurable_snd))
        have hprod : Measurable fun p : ℝ × ℝ =>
            ((((2 : ℝ) ^ (-(k : ℝ)) * (N : ℝ) * p.2 : ℝ)) : ℂ) * varphiNt N k p.1 p.2 :=
          h1.mul h2
        simpa only [varphiNtj, zpow_one] using hprod
      have := measurable_fourierCoeff_iwSymbolSet (iwArithFreqs ρ l) i
        (φ := fun t ξ => varphiNtj N k 1 t ξ) hmeas
      simpa only [mdlIWKer, iwKer, Work.Analysis.IWMultiplier.iwKernel] using this

/-! ## The `g`-side modified bump `(2^{-dk}N^dξ)^{-1} φ̃_{N,t}(ξ)` -/

/-- The amplitude of the modified bump `varphitildeNtj P N k (-1) t`:
`ξ ↦ (2^{-dk}N^dξ)^{-1} φ̃_N(ξ)`, `d = P.natDegree`. -/
def mdlAmpNeg (P : Polynomial ℤ) (N k : ℕ) : ℝ → ℂ :=
  fun ξ => ((((2 : ℝ) ^ (-((P.natDegree : ℝ) * (k : ℝ))) * ((N : ℝ)) ^ P.natDegree * ξ : ℝ))
      : ℂ)⁻¹ * varphitildeN P.natDegree N k ξ

/-- The modified bump is the modulation of its amplitude. -/
theorem varphitildeNtj_neg_eq (P : Polynomial ℤ) (N k : ℕ) (t : ℝ) :
    varphitildeNtj P N k (-1) t
      = fun ξ => mdlAmpNeg P N k ξ * ee (PevalR P ((N : ℝ) * t) * ξ) := by
  funext ξ
  simp only [varphitildeNtj, varphitildeNt, mdlAmpNeg, zpow_neg_one, Pi.mul_apply]
  ring

/-- **Vanishing of `φ̃_N` near the origin for `k ≥ 1`.**  If `|y|` times the larger of the two
rescalings is at most `1/2`, then both `η`-arguments are in `[-1/2,1/2]`, so both cutoffs equal
`1` and the difference vanishes. -/
theorem varphitildeN_eq_zero_of_scaled_le (d N k : ℕ) (hk : 1 ≤ k) {y : ℝ}
    (hy : (2 : ℝ) ^ ((d : ℝ) * ((logN N : ℝ) - (k : ℝ) + 1)) * |y| ≤ 1 / 2) :
    varphitildeN d N k y = 0 := by
  have hk0 : k ≠ 0 := by omega
  rw [varphitildeN, if_neg hk0]
  have h2 : |(2 : ℝ) ^ ((d : ℝ) * ((logN N : ℝ) - (k : ℝ) + 1)) * y| ≤ 1 / 2 := by
    rw [abs_mul, abs_of_pos (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) _)]
    exact hy
  have h1 : |(2 : ℝ) ^ ((d : ℝ) * ((logN N : ℝ) - (k : ℝ))) * y| ≤ 1 / 2 := by
    rw [abs_mul, abs_of_pos (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) _)]
    refine le_trans (mul_le_mul_of_nonneg_right ?_ (abs_nonneg y)) hy
    exact (Real.rpow_le_rpow_left_iff (by norm_num : (1 : ℝ) < 2)).mpr
      (mul_le_mul_of_nonneg_left (by linarith : (logN N : ℝ) - (k : ℝ) ≤ (logN N : ℝ) - (k : ℝ) + 1)
        (Nat.cast_nonneg d))
  rw [Work.KMTContract.kmtEta_one h1, Work.KMTContract.kmtEta_one h2, sub_self]

theorem hasCompactSupport_mdlAmpNeg (P : Polynomial ℤ) (N k : ℕ) :
    HasCompactSupport (mdlAmpNeg P N k) := by
  refine (hasCompactSupport_varphitildeN P.natDegree N k).mono ?_
  intro ξ hξ
  simp only [Function.mem_support] at hξ ⊢
  intro h
  exact hξ (by simp only [mdlAmpNeg, h, mul_zero])

theorem contDiff_mdlAmpNeg (P : Polynomial ℤ) (N k : ℕ) (hk : 1 ≤ k) :
    ContDiff ℝ 2 (mdlAmpNeg P N k) := by
  by_cases hc : (2 : ℝ) ^ (-((P.natDegree : ℝ) * (k : ℝ))) * ((N : ℝ)) ^ P.natDegree = 0
  · have hzero : mdlAmpNeg P N k = fun _ : ℝ => (0 : ℂ) := by
      funext ξ
      simp only [mdlAmpNeg, hc, zero_mul, Complex.ofReal_zero, inv_zero, zero_mul]
    rw [hzero]; exact contDiff_const
  · rw [contDiff_iff_contDiffAt]
    intro x
    set δ : ℝ := (1 / 2 : ℝ) * (2 : ℝ) ^ ((P.natDegree : ℝ) * ((k : ℝ) - (logN N : ℝ) - 1)) with hδ
    have hδpos : 0 < δ := by
      rw [hδ]
      exact mul_pos (by norm_num) (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) _)
    by_cases hx : |x| < δ
    · have hxmem : Set.Ioo (-δ) δ ∈ 𝓝 x :=
        isOpen_Ioo.mem_nhds (by rw [Set.mem_Ioo]; exact abs_lt.mp hx)
      have hev : mdlAmpNeg P N k =ᶠ[𝓝 x] (fun _ : ℝ => (0 : ℂ)) := by
        refine Filter.mem_of_superset hxmem (fun y hy => ?_)
        have hyabs : |y| < δ := abs_lt.mpr hy
        have hscaled : (2 : ℝ) ^ ((P.natDegree : ℝ) * ((logN N : ℝ) - (k : ℝ) + 1)) * |y| ≤ 1 / 2 := by
          have hkey : (2 : ℝ) ^ ((P.natDegree : ℝ) * ((logN N : ℝ) - (k : ℝ) + 1)) *
              ((1 / 2 : ℝ) * (2 : ℝ) ^ ((P.natDegree : ℝ) * ((k : ℝ) - (logN N : ℝ) - 1))) = 1 / 2 := by
            have h1 : (2 : ℝ) ^ ((P.natDegree : ℝ) * ((logN N : ℝ) - (k : ℝ) + 1)) *
                ((1 / 2 : ℝ) * (2 : ℝ) ^ ((P.natDegree : ℝ) * ((k : ℝ) - (logN N : ℝ) - 1))) =
                (1 / 2 : ℝ) * ((2 : ℝ) ^ ((P.natDegree : ℝ) * ((logN N : ℝ) - (k : ℝ) + 1)) *
                  (2 : ℝ) ^ ((P.natDegree : ℝ) * ((k : ℝ) - (logN N : ℝ) - 1))) := by ring
            rw [h1, ← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
            rw [show (P.natDegree : ℝ) * ((logN N : ℝ) - (k : ℝ) + 1)
                + (P.natDegree : ℝ) * ((k : ℝ) - (logN N : ℝ) - 1) = 0 by ring, Real.rpow_zero]
            norm_num
          have hpos : (0 : ℝ) < (2 : ℝ) ^ ((P.natDegree : ℝ) * ((logN N : ℝ) - (k : ℝ) + 1)) :=
            Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) _
          have hlt : (2 : ℝ) ^ ((P.natDegree : ℝ) * ((logN N : ℝ) - (k : ℝ) + 1)) * |y| < 1 / 2 := by
            have h := mul_lt_mul_of_pos_left
              (show |y| < (1 / 2 : ℝ) * (2 : ℝ) ^ ((P.natDegree : ℝ) * ((k : ℝ) - (logN N : ℝ) - 1))
                from hyabs)
              hpos
            rwa [hkey] at h
          exact le_of_lt hlt
        have hψ : varphitildeN P.natDegree N k y = 0 :=
          varphitildeN_eq_zero_of_scaled_le P.natDegree N k hk hscaled
        simp only [Set.mem_ofPred_eq, mdlAmpNeg, hψ, mul_zero]
      exact contDiffAt_const.congr_of_eventuallyEq hev
    · have hxδ : δ ≤ |x| := le_of_not_gt hx
      have hx0 : x ≠ 0 := by
        intro h; rw [h, abs_zero] at hxδ; linarith
      have hc' : (2 : ℝ) ^ (-((P.natDegree : ℝ) * (k : ℝ))) * ((N : ℝ)) ^ P.natDegree * x
          ≠ 0 := mul_ne_zero hc hx0
      have hval : ((((2 : ℝ) ^ (-((P.natDegree : ℝ) * (k : ℝ))) * ((N : ℝ)) ^ P.natDegree
          * x : ℝ)) : ℂ) ≠ 0 := fun h => hc' (Complex.ofReal_injective h)
      have hlin : ContDiffAt ℝ 2 (fun ξ : ℝ =>
          ((((2 : ℝ) ^ (-((P.natDegree : ℝ) * (k : ℝ))) * ((N : ℝ)) ^ P.natDegree * ξ : ℝ))
            : ℂ)) x := by
        have h1 : ContDiff ℝ 2 (fun ξ : ℝ =>
            (2 : ℝ) ^ (-((P.natDegree : ℝ) * (k : ℝ))) * ((N : ℝ)) ^ P.natDegree * ξ) :=
          (contDiff_const (c := (2 : ℝ) ^ (-((P.natDegree : ℝ) * (k : ℝ)))
            * ((N : ℝ)) ^ P.natDegree)).mul contDiff_id
        exact ((Complex.ofRealCLM.contDiff (n := 2)).comp h1).contDiffAt
      have hinv : ContDiffAt ℝ 2 (fun ξ : ℝ =>
          ((((2 : ℝ) ^ (-((P.natDegree : ℝ) * (k : ℝ))) * ((N : ℝ)) ^ P.natDegree * ξ : ℝ))
            : ℂ)⁻¹) x := by
        have h : ContDiffAt ℝ 2 (fun z : ℂ => z⁻¹)
            ((((2 : ℝ) ^ (-((P.natDegree : ℝ) * (k : ℝ))) * ((N : ℝ)) ^ P.natDegree
              * x : ℝ)) : ℂ) :=
          (contDiffAt_id (𝕜 := ℝ)).inv hval
        simpa only [Function.comp_def] using h.comp x hlin
      show ContDiffAt ℝ 2 (fun ξ : ℝ =>
          ((((2 : ℝ) ^ (-((P.natDegree : ℝ) * (k : ℝ))) * ((N : ℝ)) ^ P.natDegree * ξ : ℝ))
            : ℂ)⁻¹ * varphitildeN P.natDegree N k ξ) x
      exact hinv.mul (contDiff_varphitildeN P.natDegree N k).contDiffAt

/-! ## Integrability of the amplitude and of its derivatives -/

theorem hcs_iteratedDeriv_mdlAmpNeg (P : Polynomial ℤ) (N k m : ℕ) (hm : m ≤ 2) :
    HasCompactSupport (iteratedDeriv m (mdlAmpNeg P N k)) := by
  interval_cases m
  · rw [iteratedDeriv_zero]; exact hasCompactSupport_mdlAmpNeg P N k
  · rw [iteratedDeriv_one]; exact (hasCompactSupport_mdlAmpNeg P N k).deriv
  · rw [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one]
    exact ((hasCompactSupport_mdlAmpNeg P N k).deriv).deriv

theorem integrable_iteratedDeriv_mdlAmpNeg (P : Polynomial ℤ) (N k m : ℕ) (hk : 1 ≤ k)
    (hm : m ≤ 2) :
    Integrable (fun y => ‖iteratedDeriv m (mdlAmpNeg P N k) y‖) := by
  have hcont : Continuous (iteratedDeriv m (mdlAmpNeg P N k)) :=
    (contDiff_mdlAmpNeg P N k hk).continuous_iteratedDeriv m (by exact_mod_cast hm)
  exact (hcont.integrable_of_hasCompactSupport (hcs_iteratedDeriv_mdlAmpNeg P N k m hm)).norm

/-! ## The uniform modulation bounds of the `g`-side modified bump -/

/-- The uniform-in-`t` `L¹`-bounds of the modified bump `mdlAmpNeg P N k · e(PevalR P (Nt)·)` and
of its second derivative. -/
theorem mdlAmpNeg_modulation_bounds (P : Polynomial ℤ) (N k : ℕ) (hk : 1 ≤ k) :
    ∃ S : ℝ, 0 ≤ S ∧ ∀ t ∈ Set.Icc (1/2 : ℝ) 1,
      (∫ y, ‖mdlAmpNeg P N k y * ee (PevalR P ((N : ℝ) * t) * y)‖) ≤ S ∧
      (∫ y, ‖iteratedDeriv 2
        (fun ξ : ℝ => mdlAmpNeg P N k ξ * ee (PevalR P ((N : ℝ) * t) * ξ)) y‖) ≤ S := by
  set M : ℝ := (∑ i ∈ Finset.range (P.natDegree + 1), |(P.coeff i : ℝ)|)
    * (1 + (N : ℝ)) ^ P.natDegree with hM
  set c : ℝ := 2 * (2 * Real.pi * M) with hc
  set A : ℝ := ∫ y, ‖mdlAmpNeg P N k y‖ with hA
  set B : ℝ := ∫ y, ‖iteratedDeriv 1 (mdlAmpNeg P N k) y‖ with hB
  set C : ℝ := ∫ y, ‖iteratedDeriv 2 (mdlAmpNeg P N k) y‖ with hC
  have hcd := contDiff_mdlAmpNeg P N k hk
  have hcs := hasCompactSupport_mdlAmpNeg P N k
  have hI1 : Integrable (fun y => ‖iteratedDeriv 2 (mdlAmpNeg P N k) y‖) :=
    ((hcd.continuous_iteratedDeriv 2 le_rfl).integrable_of_hasCompactSupport
      (hcs_iteratedDeriv_mdlAmpNeg P N k 2 le_rfl)).norm
  have hI2 : Integrable (fun y => c * ‖iteratedDeriv 1 (mdlAmpNeg P N k) y‖) :=
    (((hcd.continuous_iteratedDeriv 1 (by norm_num)).integrable_of_hasCompactSupport
      (hcs_iteratedDeriv_mdlAmpNeg P N k 1 (by norm_num))).norm).const_mul c
  have hI3 : Integrable (fun y => c ^ 2 * ‖mdlAmpNeg P N k y‖) :=
    (((hcd.continuous.integrable_of_hasCompactSupport hcs).norm).const_mul (c ^ 2))
  have hA0 : 0 ≤ A := integral_nonneg (fun y => norm_nonneg _)
  have hB0 : 0 ≤ B := integral_nonneg (fun y => norm_nonneg _)
  have hC0 : 0 ≤ C := integral_nonneg (fun y => norm_nonneg _)
  have hc0 : 0 ≤ c := by rw [hc]; positivity
  have hM0 : 0 ≤ M := by rw [hM]; positivity
  have hA0' : 0 ≤ A + c * B + c ^ 2 * A + C + 1 := by
    have : 0 ≤ c * B := mul_nonneg hc0 hB0
    have : 0 ≤ c ^ 2 * A := mul_nonneg (by positivity) hA0
    linarith
  refine ⟨A + c * B + c ^ 2 * A + C + 1, hA0', fun t ht => ⟨?_, ?_⟩⟩
  · have hcongr : (fun y => ‖mdlAmpNeg P N k y * ee (PevalR P ((N : ℝ) * t) * y)‖)
        = fun y => ‖mdlAmpNeg P N k y‖ := by
      funext y; rw [norm_mul, norm_ee, mul_one]
    rw [hcongr, ← hA]
    have : 0 ≤ c * B := mul_nonneg hc0 hB0
    have : 0 ≤ c ^ 2 * A := mul_nonneg (by positivity) hA0
    linarith
  · have ht1 : |t| ≤ 1 := by rw [abs_le]; exact ⟨by linarith [ht.1], ht.2⟩
    have hv : |PevalR P ((N : ℝ) * t)| ≤ M := by
      rw [hM]; exact abs_PevalR_mul_le P N ht1
    have hpt : ∀ y : ℝ, ‖iteratedDeriv 2
          (fun ξ : ℝ => mdlAmpNeg P N k ξ * ee (PevalR P ((N : ℝ) * t) * ξ)) y‖ ≤
        ‖iteratedDeriv 2 (mdlAmpNeg P N k) y‖
          + c * ‖iteratedDeriv 1 (mdlAmpNeg P N k) y‖
          + c ^ 2 * ‖mdlAmpNeg P N k y‖ := by
      intro y
      have h := norm_iteratedDeriv_two_mul_ee_le (mdlAmpNeg P N k) (PevalR P ((N : ℝ) * t)) hcd y
      have hshape : (mdlAmpNeg P N k * fun ξ : ℝ => ee (PevalR P ((N : ℝ) * t) * ξ)) =
          (fun ξ : ℝ => mdlAmpNeg P N k ξ * ee (PevalR P ((N : ℝ) * t) * ξ)) := rfl
      rw [hshape] at h
      have h2π : (0 : ℝ) ≤ 2 * Real.pi := by positivity
      have hstep : 2 * (2 * Real.pi * |PevalR P ((N : ℝ) * t)|) ≤ 2 * (2 * Real.pi * M) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hv h2π) (by norm_num)
      have h1 : 2 * (2 * Real.pi * |PevalR P ((N : ℝ) * t)|)
            * ‖iteratedDeriv 1 (mdlAmpNeg P N k) y‖
          ≤ c * ‖iteratedDeriv 1 (mdlAmpNeg P N k) y‖ := by
        rw [hc]
        exact mul_le_mul_of_nonneg_right hstep (norm_nonneg _)
      have h2 : (2 * Real.pi * |PevalR P ((N : ℝ) * t)|) ^ 2 * ‖mdlAmpNeg P N k y‖
          ≤ c ^ 2 * ‖mdlAmpNeg P N k y‖ := by
        rw [hc]
        refine mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) ?_ 2) (norm_nonneg _)
        nlinarith [mul_le_mul_of_nonneg_left hv h2π, hM0, Real.pi_pos]
      linarith [h, h1, h2]
    have hI12 : Integrable (fun y => ‖iteratedDeriv 2 (mdlAmpNeg P N k) y‖
        + c * ‖iteratedDeriv 1 (mdlAmpNeg P N k) y‖) := hI1.add hI2
    have hLint : Integrable (fun y => ‖iteratedDeriv 2
        (fun ξ : ℝ => mdlAmpNeg P N k ξ * ee (PevalR P ((N : ℝ) * t) * ξ)) y‖) := by
      have hcd2 : ContDiff ℝ 2
          (fun ξ : ℝ => mdlAmpNeg P N k ξ * ee (PevalR P ((N : ℝ) * t) * ξ)) :=
        hcd.mul (contDiff_ee_const_mul 2 _)
      have hcs2 : HasCompactSupport
          (fun ξ : ℝ => mdlAmpNeg P N k ξ * ee (PevalR P ((N : ℝ) * t) * ξ)) :=
        hcs.mono (fun ξ hξ => by
          simp only [Function.mem_support, Pi.mul_apply] at hξ ⊢
          intro h; exact hξ (by rw [h, zero_mul]))
      have hcs3 : HasCompactSupport (iteratedDeriv 2
          (fun ξ : ℝ => mdlAmpNeg P N k ξ * ee (PevalR P ((N : ℝ) * t) * ξ))) := by
        rw [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one]
        exact (hcs2.deriv).deriv
      exact ((hcd2.continuous_iteratedDeriv 2 le_rfl).integrable_of_hasCompactSupport hcs3).norm
    have hmono := integral_mono hLint (hI12.add hI3) hpt
    have heq : (∫ y, ‖iteratedDeriv 2 (mdlAmpNeg P N k) y‖
          + c * ‖iteratedDeriv 1 (mdlAmpNeg P N k) y‖
          + c ^ 2 * ‖mdlAmpNeg P N k y‖)
        = C + c * B + c ^ 2 * A := by
      rw [integral_add hI12 hI3, integral_add hI1 hI2, integral_const_mul, integral_const_mul,
        ← hA, ← hB, ← hC]
    have hfinal : (∫ y, ‖iteratedDeriv 2
          (fun ξ : ℝ => mdlAmpNeg P N k ξ * ee (PevalR P ((N : ℝ) * t) * ξ)) y‖)
        ≤ C + c * B + c ^ 2 * A := le_trans hmono (le_of_eq heq)
    have : 0 ≤ c * B := mul_nonneg hc0 hB0
    have : 0 ≤ c ^ 2 * A := mul_nonneg (by positivity) hA0
    linarith [hfinal]

/-! ## The kernel package of the `g`-side modified bump -/

/-- Joint measurability of `(t,ξ) ↦ varphitildeNtj P N k (-1) t ξ`. -/
theorem measurable_varphitildeNtj_neg_uncurry (P : Polynomial ℤ) (N k : ℕ) :
    Measurable fun p : ℝ × ℝ => varphitildeNtj P N k (-1) p.1 p.2 := by
  have hz : Measurable fun p : ℝ × ℝ =>
      ((((2 : ℝ) ^ (-((P.natDegree : ℝ) * (k : ℝ))) * ((N : ℝ)) ^ P.natDegree * p.2 : ℝ))
        : ℂ) :=
    Complex.continuous_ofReal.measurable.comp
      (((continuous_const.mul continuous_const).mul continuous_snd).measurable)
  have h1 : Measurable fun p : ℝ × ℝ =>
      ((((2 : ℝ) ^ (-((P.natDegree : ℝ) * (k : ℝ))) * ((N : ℝ)) ^ P.natDegree * p.2 : ℝ))
        : ℂ)⁻¹ := hz.inv
  have h2 : Measurable fun p : ℝ × ℝ =>
      varphitildeNt P P.natDegree N k p.1 p.2 := by
    have hk' : Measurable (varphitildeN P.natDegree N k) :=
      (contDiff_varphitildeN P.natDegree N k).continuous.measurable
    have hee : Measurable ee := by unfold ee; fun_prop
    have hv : Measurable fun p : ℝ × ℝ => PevalR P ((N : ℝ) * p.1) := by
      have hp : Measurable (PevalR P) := by unfold PevalR; fun_prop
      exact hp.comp ((measurable_const_mul (N : ℝ)).comp measurable_fst)
    unfold varphitildeNt
    exact (hk'.comp measurable_snd).mul (hee.comp (hv.mul measurable_snd))
  have hprod : Measurable fun p : ℝ × ℝ =>
      ((((2 : ℝ) ^ (-((P.natDegree : ℝ) * (k : ℝ))) * ((N : ℝ)) ^ P.natDegree * p.2 : ℝ))
        : ℂ)⁻¹ * varphitildeNt P P.natDegree N k p.1 p.2 := h1.mul h2
  simpa only [varphitildeNtj, zpow_neg_one] using hprod

/-- **The kernel package of the `g`-side modified bump** `varphitildeNtj P N k (-1) t`, `k ≥ 1`. -/
theorem mdlKerVarphitildeNtjNeg (ρ : ℝ) (l : ℕ) (P : Polynomial ℤ) (N k : ℕ) (hk : 1 ≤ k) :
    (∀ t ∈ Set.Icc (1/2 : ℝ) 1, MeasureTheory.Integrable (varphitildeNtj P N k (-1) t)) ∧
      ∃ a : ℤ → ℝ, Summable a ∧
      (∀ t ∈ Set.Icc (1/2 : ℝ) 1, ∀ i : ℤ,
        ‖mdlIWKer ρ l (varphitildeNtj P N k (-1) t) i‖ ≤ a i) ∧
      (∀ i : ℤ, Measurable (fun t : ℝ => mdlIWKer ρ l (varphitildeNtj P N k (-1) t) i)) := by
  obtain ⟨S, hSnn, hS⟩ := mdlAmpNeg_modulation_bounds P N k hk
  have hcd : ∀ t : ℝ, ContDiff ℝ 2 (varphitildeNtj P N k (-1) t) := by
    intro t
    rw [varphitildeNtj_neg_eq]
    exact (contDiff_mdlAmpNeg P N k hk).mul (contDiff_ee_const_mul 2 (PevalR P ((N : ℝ) * t)))
  have hcs : ∀ t : ℝ, HasCompactSupport (varphitildeNtj P N k (-1) t) := by
    intro t
    rw [varphitildeNtj_neg_eq]
    exact (hasCompactSupport_mdlAmpNeg P N k).mono (fun ξ hξ => by
      simp only [Function.mem_support, Pi.mul_apply] at hξ ⊢
      intro h
      exact hξ (by rw [h, zero_mul]))
  have hbnd : ∀ t ∈ Set.Icc (1/2 : ℝ) 1,
      (∫ y, ‖varphitildeNtj P N k (-1) t y‖) ≤ S ∧
        (∫ y, ‖iteratedDeriv 2 (varphitildeNtj P N k (-1) t) y‖) ≤ S := by
    intro t ht
    rw [varphitildeNtj_neg_eq]
    exact hS t ht
  refine ⟨fun t _ => ?_, ?_⟩
  · exact (hcd t).continuous.integrable_of_hasCompactSupport (hcs t)
  · refine ⟨fun i => (4 * (((iwArithFreqs ρ l).card : ℝ) * S) + 1) * ‖kmtKernWeight i‖,
      summable_kmtKernWeight.mul_left _, fun t ht i => ?_, fun i => ?_⟩
    · exact iwKernel_decay_of_bump (iwArithFreqs ρ l) (hcd t) (hcs t) hSnn
        (hbnd t ht).1 (hbnd t ht).2 i
    · have := measurable_fourierCoeff_iwSymbolSet (iwArithFreqs ρ l) i
        (φ := fun t ξ => varphitildeNtj P N k (-1) t ξ) (measurable_varphitildeNtj_neg_uncurry P N k)
      simpa only [mdlIWKer, iwKer, Work.Analysis.IWMultiplier.iwKernel] using this

end

end Work.KMTPlan.A6
