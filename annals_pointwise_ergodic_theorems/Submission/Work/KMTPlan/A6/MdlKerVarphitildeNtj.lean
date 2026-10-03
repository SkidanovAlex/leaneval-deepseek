/-
# A summable majorant for the kernel of `Tle ρ l` applied to the modified bump `φ̃_{N,t,1}`

This module proves `Work.KMTPlan.A6.MdlKerVarphitildeNtj`: for the *modified* bump of the
integration-by-parts identity of Krause--Mirek--Tao §6,

  `φ̃_{N,t,1}(ξ) = varphitildeNtj P N 0 1 t ξ = N^d ξ · φ̃_N(ξ) e(P(Nt)ξ)`,
  `d = P.natDegree`,

the convolution kernel `i ↦ mdlIWKer ρ l (φ̃_{N,t,1}) i` of the Ionescu--Wainger projection
`Tle ρ l φ̃_{N,t,1}` admits a *summable majorant in `i`*, uniform in `t ∈ [1/2,1]`, and is
measurable in `t`; moreover `φ̃_{N,t,1}` is integrable.

The plan is exactly that of the already-proved siblings `Work.KMTPlan.A6.MdlKerVarphiNt`,
`Work.KMTPlan.A6.MdlKerVarphitildeNt` and `Work.KMTPlan.A6.MdlKerVarphiNtj`, with the modulated
bump replaced by `varphitildeNtj P N 0 1 t`:

* `mdlTildeP1 P N = N^d ξ · φ̃_N(ξ)` is the unmodulated modified bump.  It is a polynomial factor
  times `φ̃_N`, hence `C²` with compact support (`contDiff_varphitildeN`,
  `hasCompactSupport_varphitildeN`), and so are its first two derivatives.
* `varphitildeNtj P N 0 1 t = mdlTildeP1 P N · e(P(Nt)·)` (`varphitildeNtj_apply`), and
  `norm_iteratedDeriv_two_mul_ee_le` bounds the second derivative of the modulated bump by
  `‖q''‖ + 2(2πM)‖q'‖ + (2πM)²‖q‖` with `M ≥ sup_{t ∈ [1/2,1]} |P(Nt)|` (`abs_PevalR_mul_le`).
* the kernel decay `Work.KMTAreas.A7.iwKernel_decay_of_bump` (with `C²` + compact support and the
  two uniform `L¹`-bounds of `mdlTildeP1_bounds`) gives
  `‖mdlIWKer ρ l φ̃_{N,t,1} i‖ ≤ (4 (card A) S + 1) ‖kmtKernWeight i‖`, whose right-hand side is
  summable.
* measurability in `t` comes from `Work.KMTAreas.A7.measurable_fourierCoeff_iwSymbolSet` applied
  to the jointly measurable family `(t,ξ) ↦ varphitildeNtj P N 0 1 t ξ`.
-/
import Mathlib
import Submission.Work.KMTPlan.A6.MdlDecayDefs
import Submission.Work.KMTAreas.A7.Tle_varphiNt_bounded
import Submission.Work.KMTAreas.A7.fourierDecay_varphitildeN
import Submission.Work.KMTAreas.A7.abs_PevalR_mul_le

set_option maxHeartbeats 1000000

namespace Work.KMTPlan.A6

noncomputable section

open MeasureTheory Polynomial Finset Filter Topology
open scoped ENNReal NNReal BigOperators Interval
open Work.KMTAreas.A7
open Work.Analysis.IonescuWainger Work.Analysis.IWMultiplier

/-! ## The unmodulated modified bump `N^d ξ · φ̃_N(ξ)` -/

/-- The unmodulated modified bump `q(ξ) = N^d ξ · φ̃_N(ξ)` at the bottom scale `k₂ = 0` (the
modulation `e(P(Nt)ξ)` split off). -/
def mdlTildeP1 (P : Polynomial ℤ) (N : ℕ) : ℝ → ℂ :=
  fun ξ => (((N : ℝ) ^ P.natDegree * ξ : ℝ) : ℂ) * varphitildeN P.natDegree N 0 ξ

/-- The modified bump `varphitildeNtj P N 0 1 t` is the modulation `e(P(Nt)·)` times
`mdlTildeP1 P N`. -/
theorem varphitildeNtj_apply (P : Polynomial ℤ) (N : ℕ) (t ξ : ℝ) :
    varphitildeNtj P N 0 1 t ξ = mdlTildeP1 P N ξ * ee (PevalR P ((N : ℝ) * t) * ξ) := by
  rw [varphitildeNtj, varphitildeNt]
  simp only [zpow_one, Nat.cast_zero, mul_zero, neg_zero, Real.rpow_zero, one_mul, mdlTildeP1]
  ring

/-! ## Smoothness and compact support of `mdlTildeP1` -/

/-- `q(ξ) = N^d ξ · φ̃_N(ξ)` is `C²` (a polynomial factor times the smooth bump `φ̃_N`). -/
theorem contDiff_mdlTildeP1 (P : Polynomial ℤ) (N : ℕ) : ContDiff ℝ 2 (mdlTildeP1 P N) := by
  have h1 : ContDiff ℝ 2 (fun ξ : ℝ => (N : ℝ) ^ P.natDegree * ξ) :=
    contDiff_const.mul contDiff_id
  have h2 : ContDiff ℝ 2 (fun ξ : ℝ => (((N : ℝ) ^ P.natDegree * ξ : ℝ) : ℂ)) :=
    (Complex.ofRealCLM.contDiff (𝕜 := ℝ) (n := 2)).comp h1
  exact h2.mul (contDiff_varphitildeN P.natDegree N 0)

/-- `q(ξ) = N^d ξ · φ̃_N(ξ)` has compact support (that of `φ̃_N`). -/
theorem hasCompactSupport_mdlTildeP1 (P : Polynomial ℤ) (N : ℕ) :
    HasCompactSupport (mdlTildeP1 P N) :=
  (hasCompactSupport_varphitildeN P.natDegree N 0).mul_left

/-- The `m`-th derivative of `q` (`m ≤ 2`) has compact support. -/
theorem hcs_iteratedDeriv_mdlTildeP1 (P : Polynomial ℤ) (N m : ℕ) (hm : m ≤ 2) :
    HasCompactSupport (iteratedDeriv m (mdlTildeP1 P N)) := by
  interval_cases m
  · rw [iteratedDeriv_zero]; exact hasCompactSupport_mdlTildeP1 P N
  · rw [iteratedDeriv_one]; exact (hasCompactSupport_mdlTildeP1 P N).deriv
  · rw [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one]
    exact ((hasCompactSupport_mdlTildeP1 P N).deriv).deriv

/-- The `L¹` norm of the `m`-th derivative of `q` is finite, for `m ≤ 2`. -/
theorem integrable_iteratedDeriv_mdlTildeP1 (P : Polynomial ℤ) (N m : ℕ) (hm : m ≤ 2) :
    Integrable (fun y => ‖iteratedDeriv m (mdlTildeP1 P N) y‖) := by
  have hcont : Continuous (iteratedDeriv m (mdlTildeP1 P N)) :=
    (contDiff_mdlTildeP1 P N).continuous_iteratedDeriv m (by exact_mod_cast hm)
  exact (hcont.integrable_of_hasCompactSupport (hcs_iteratedDeriv_mdlTildeP1 P N m hm)).norm

/-! ## Uniform-in-`t` bounds for the modulated bump -/

/-- **Uniform-in-`t` bounds for the modified bump `φ̃_{N,t,1}`.**  There is `S ≥ 0` such that for
every `t ∈ [1/2,1]` the bump `φ̃_{N,t,1} = varphitildeNtj P N 0 1 t` is `C²` with compact support
and both `∫‖φ̃_{N,t,1}‖` and `∫‖(φ̃_{N,t,1})''‖` are bounded by `S`. -/
theorem mdlTildeP1_bounds (P : Polynomial ℤ) (N : ℕ) :
    ∃ S : ℝ, 0 ≤ S ∧ ∀ t ∈ Set.Icc (1/2 : ℝ) 1,
      ContDiff ℝ 2 (fun ξ => varphitildeNtj P N 0 1 t ξ) ∧
      HasCompactSupport (fun ξ => varphitildeNtj P N 0 1 t ξ) ∧
      (∫ y, ‖varphitildeNtj P N 0 1 t y‖) ≤ S ∧
      (∫ y, ‖iteratedDeriv 2 (fun ξ => varphitildeNtj P N 0 1 t ξ) y‖) ≤ S := by
  set M : ℝ := max 1 ((∑ i ∈ Finset.range (P.natDegree + 1), |(P.coeff i : ℝ)|) *
    (1 + (N : ℝ)) ^ P.natDegree) with hMdef
  set A : ℝ := ∫ y, ‖mdlTildeP1 P N y‖ with hA
  set B : ℝ := ∫ y, ‖iteratedDeriv 1 (mdlTildeP1 P N) y‖ with hB
  set C : ℝ := ∫ y, ‖iteratedDeriv 2 (mdlTildeP1 P N) y‖ with hC
  set S : ℝ := A + 2 * (2 * Real.pi * M) * B + (2 * Real.pi * M) ^ 2 * A + C + 1 with hS
  have hM1 : 0 ≤ M := le_trans zero_le_one (le_max_left 1 _)
  have hA0 : 0 ≤ A := by rw [hA]; exact integral_nonneg (fun y => norm_nonneg _)
  have hB0 : 0 ≤ B := by rw [hB]; exact integral_nonneg (fun y => norm_nonneg _)
  have hC0 : 0 ≤ C := by rw [hC]; exact integral_nonneg (fun y => norm_nonneg _)
  have h2B : 0 ≤ 2 * (2 * Real.pi * M) * B :=
    mul_nonneg (mul_nonneg (by norm_num) (mul_nonneg (by positivity) hM1)) hB0
  have h2A : 0 ≤ (2 * Real.pi * M) ^ 2 * A := mul_nonneg (sq_nonneg _) hA0
  have hSnn : 0 ≤ S := by rw [hS]; linarith
  have hAS : A ≤ S := by rw [hS]; linarith
  have hCS : C + (2 * (2 * Real.pi * M)) * B + (2 * Real.pi * M) ^ 2 * A ≤ S := by
    rw [hS]; linarith
  refine ⟨S, hSnn, ?_⟩
  intro t ht
  have heqfun : (fun ξ : ℝ => varphitildeNtj P N 0 1 t ξ) =
      fun ξ => mdlTildeP1 P N ξ * ee (PevalR P ((N : ℝ) * t) * ξ) :=
    funext (fun ξ => varphitildeNtj_apply P N t ξ)
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [heqfun]
    exact (contDiff_mdlTildeP1 P N).mul (contDiff_ee_const_mul 2 _)
  · rw [heqfun]
    exact (hasCompactSupport_mdlTildeP1 P N).mul_right
  · have hcongr : (fun y => ‖varphitildeNtj P N 0 1 t y‖) =
        fun y => ‖mdlTildeP1 P N y‖ := by
      funext y
      rw [varphitildeNtj_apply P N t y]
      simp only [norm_mul, norm_ee, mul_one]
    rw [hcongr, ← hA]
    exact hAS
  · have ht1 : |t| ≤ 1 := by
      rw [abs_le]; exact ⟨by linarith [ht.1], ht.2⟩
    have hc : |PevalR P ((N : ℝ) * t)| ≤ M :=
      le_trans (abs_PevalR_mul_le P N ht1) (le_max_right 1 _)
    have hpt : ∀ y, ‖iteratedDeriv 2 (fun ξ => varphitildeNtj P N 0 1 t ξ) y‖ ≤
        ‖iteratedDeriv 2 (mdlTildeP1 P N) y‖
          + (2 * (2 * Real.pi * M)) * ‖iteratedDeriv 1 (mdlTildeP1 P N) y‖
          + (2 * Real.pi * M) ^ 2 * ‖mdlTildeP1 P N y‖ := by
      intro y
      have hmod := norm_iteratedDeriv_two_mul_ee_le (mdlTildeP1 P N) (PevalR P ((N : ℝ) * t))
        (contDiff_mdlTildeP1 P N) y
      rw [heqfun]
      refine le_trans hmod ?_
      have h1 : 2 * (2 * Real.pi * |PevalR P ((N : ℝ) * t)|) ≤ 2 * (2 * Real.pi * M) := by
        have : 2 * Real.pi * |PevalR P ((N : ℝ) * t)| ≤ 2 * Real.pi * M :=
          mul_le_mul_of_nonneg_left hc (by positivity)
        linarith
      have h2 : (2 * Real.pi * |PevalR P ((N : ℝ) * t)|) ^ 2 ≤ (2 * Real.pi * M) ^ 2 :=
        pow_le_pow_left₀ (by positivity) (mul_le_mul_of_nonneg_left hc (by positivity)) 2
      linarith [mul_le_mul_of_nonneg_right h1
          (norm_nonneg (iteratedDeriv 1 (mdlTildeP1 P N) y)),
        mul_le_mul_of_nonneg_right h2 (norm_nonneg (mdlTildeP1 P N y))]
    have hI1 : Integrable (fun y => ‖iteratedDeriv 2 (mdlTildeP1 P N) y‖) :=
      integrable_iteratedDeriv_mdlTildeP1 P N 2 le_rfl
    have hI2 : Integrable (fun y => (2 * (2 * Real.pi * M)) *
        ‖iteratedDeriv 1 (mdlTildeP1 P N) y‖) :=
      (integrable_iteratedDeriv_mdlTildeP1 P N 1 (by norm_num)).const_mul _
    have hI3 : Integrable (fun y => (2 * Real.pi * M) ^ 2 * ‖mdlTildeP1 P N y‖) := by
      simpa using (integrable_iteratedDeriv_mdlTildeP1 P N 0 (by norm_num)).const_mul
        ((2 * Real.pi * M) ^ 2)
    have hI12 : Integrable (fun y => ‖iteratedDeriv 2 (mdlTildeP1 P N) y‖ +
        (2 * (2 * Real.pi * M)) * ‖iteratedDeriv 1 (mdlTildeP1 P N) y‖) := hI1.add hI2
    have hLint : Integrable (fun y =>
        ‖iteratedDeriv 2 (fun ξ => varphitildeNtj P N 0 1 t ξ) y‖) := by
      have hcont : Continuous (fun y =>
          ‖iteratedDeriv 2 (fun ξ => varphitildeNtj P N 0 1 t ξ) y‖) :=
        ((show ContDiff ℝ 2 (fun ξ => varphitildeNtj P N 0 1 t ξ) from by
          rw [heqfun]
          exact (contDiff_mdlTildeP1 P N).mul (contDiff_ee_const_mul 2 _)).continuous_iteratedDeriv
          2 le_rfl).norm
      exact (hI12.add hI3).mono' hcont.aestronglyMeasurable
        (Filter.Eventually.of_forall (fun y => by
          simpa only [norm_norm, Pi.add_apply] using hpt y))
    have hmono := integral_mono hLint (hI12.add hI3) hpt
    have heq : (∫ y, (‖iteratedDeriv 2 (mdlTildeP1 P N) y‖ +
            (2 * (2 * Real.pi * M)) * ‖iteratedDeriv 1 (mdlTildeP1 P N) y‖ +
            (2 * Real.pi * M) ^ 2 * ‖mdlTildeP1 P N y‖))
        = C + (2 * (2 * Real.pi * M)) * B + (2 * Real.pi * M) ^ 2 * A := by
      rw [integral_add hI12 hI3, integral_add hI1 hI2, integral_const_mul, integral_const_mul,
        ← hA, ← hB, ← hC]
    have hfinal : (∫ y, ‖iteratedDeriv 2 (fun ξ => varphitildeNtj P N 0 1 t ξ) y‖) ≤
        C + (2 * (2 * Real.pi * M)) * B + (2 * Real.pi * M) ^ 2 * A :=
      le_trans hmono (le_of_eq heq)
    exact le_trans hfinal hCS

/-! ## Measurability in `t` -/

/-- Joint measurability of `(t, ξ) ↦ varphitildeNtj P N 0 1 t ξ`. -/
theorem measurable_varphitildeNtj_uncurry (P : Polynomial ℤ) (N : ℕ) :
    Measurable fun q : ℝ × ℝ => varphitildeNtj P N 0 1 q.1 q.2 := by
  have hee : Measurable ee := by unfold ee; fun_prop
  have hq : Measurable (mdlTildeP1 P N) := (contDiff_mdlTildeP1 P N).continuous.measurable
  have hP : Measurable (fun q : ℝ × ℝ => PevalR P ((N : ℝ) * q.1)) := by
    have hp : Measurable (PevalR P) := by unfold PevalR; fun_prop
    exact hp.comp ((measurable_const_mul (N : ℝ)).comp measurable_fst)
  have hfun : (fun q : ℝ × ℝ => varphitildeNtj P N 0 1 q.1 q.2) =
      fun q : ℝ × ℝ => mdlTildeP1 P N q.2 * ee (PevalR P ((N : ℝ) * q.1) * q.2) :=
    funext (fun q => varphitildeNtj_apply P N q.1 q.2)
  rw [hfun]
  exact (hq.comp measurable_snd).mul (hee.comp (hP.mul measurable_snd))

/-- Measurability in `t` of the IW kernel of the modified bump `varphitildeNtj P N 0 1 t`. -/
theorem measurable_iwKernel_varphitildeNtj (ρ : ℝ) (l : ℕ) (P : Polynomial ℤ) (N : ℕ) (j : ℤ) :
    Measurable (fun t : ℝ => iwKernel
      (iwSymbolSet (iwArithFreqs ρ l) (periodize (varphitildeNtj P N 0 1 t))) j) := by
  have h := measurable_fourierCoeff_iwSymbolSet (iwArithFreqs ρ l) j
    (φ := fun t ξ => varphitildeNtj P N 0 1 t ξ) (measurable_varphitildeNtj_uncurry P N)
  simpa only [iwKernel] using h

/-! ## The target -/

/-- A summable majorant for the convolution kernel of `Tle ρ l` applied to the *modified* bump
`φ̃_{N,t,1} = varphitildeNtj P N 0 1 t` (the `N^d ξ`-multiple of the modulated bump at the bottom
scale `k₂ = 0`), uniform in `t ∈ [1/2,1]`, together with the integrability of the bump and the
measurability in `t` of the kernel. -/
theorem MdlKerVarphitildeNtj (ρ : ℝ) (l : ℕ) (P : Polynomial ℤ) (N : ℕ) :
    (∀ t ∈ Set.Icc (1/2 : ℝ) 1,
        MeasureTheory.Integrable (Work.KMTPlan.A6.varphitildeNtj P N 0 1 t)) ∧
      ∃ a : ℤ → ℝ, Summable a ∧
      (∀ t ∈ Set.Icc (1/2 : ℝ) 1, ∀ i : ℤ,
        ‖Work.KMTPlan.A6.mdlIWKer ρ l (Work.KMTPlan.A6.varphitildeNtj P N 0 1 t) i‖ ≤ a i) ∧
      (∀ i : ℤ, Measurable (fun t : ℝ =>
        Work.KMTPlan.A6.mdlIWKer ρ l (Work.KMTPlan.A6.varphitildeNtj P N 0 1 t) i)) := by
  classical
  obtain ⟨S, hSnn, hS⟩ := mdlTildeP1_bounds P N
  refine ⟨?_, fun i => (4 * (((iwArithFreqs ρ l).card : ℝ) * S) + 1) * ‖kmtKernWeight i‖,
    ?_, ?_, ?_⟩
  · intro t ht
    exact ((hS t ht).1.continuous).integrable_of_hasCompactSupport (hS t ht).2.1
  · exact summable_kmtKernWeight.mul_left _
  · intro t ht i
    exact iwKernel_decay_of_bump (iwArithFreqs ρ l) (hS t ht).1 (hS t ht).2.1 hSnn
      (hS t ht).2.2.1 (hS t ht).2.2.2 i
  · intro i
    simpa only [mdlIWKer, iwKer] using measurable_iwKernel_varphitildeNtj ρ l P N i

end

end Work.KMTPlan.A6
