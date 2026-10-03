import Mathlib
import Submission.Work.KMTPlan.A6.MdlDecayDefs
import Submission.Work.KMTAreas.A7.Tle_varphiNt_bounded
import Submission.Work.KMTAreas.A7.Tle_varphitildeNt_bounded

set_option maxHeartbeats 1000000

namespace Work.KMTPlan.A6

noncomputable section

open MeasureTheory Polynomial Finset Filter Topology
open scoped ENNReal NNReal BigOperators Interval
open Work.KMTAreas.A7
open Work.Analysis.IonescuWainger Work.Analysis.IWMultiplier

/-! ## Smoothness and `L¹` bounds for the modulated `d`-fold bump `φ̃_{N,t}` -/

/-- `φ̃_{N,t}` is `C²`. -/
theorem contDiff_varphitildeNt_aux (P : Polynomial ℤ) (d N k : ℕ) (t : ℝ) :
    ContDiff ℝ 2 (varphitildeNt P d N k t) := by
  rw [show varphitildeNt P d N k t
      = fun ξ : ℝ => varphitildeN d N k ξ * ee (PevalR P ((N : ℝ) * t) * ξ) from rfl]
  exact (contDiff_varphitildeN d N k).mul (contDiff_ee_const_mul 2 _)

/-- `φ̃_{N,t}` has compact support. -/
theorem hasCompactSupport_varphitildeNt_aux (P : Polynomial ℤ) (d N k : ℕ) (t : ℝ) :
    HasCompactSupport (varphitildeNt P d N k t) := by
  rw [show varphitildeNt P d N k t
      = fun ξ : ℝ => varphitildeN d N k ξ * ee (PevalR P ((N : ℝ) * t) * ξ) from rfl]
  exact (hasCompactSupport_varphitildeN d N k).mul_right

/-- The `m`-th derivative of `φ̃_N` (`m ≤ 2`) has compact support. -/
theorem hcs_iteratedDeriv_varphitildeN (d N k m : ℕ) (hm : m ≤ 2) :
    HasCompactSupport (iteratedDeriv m (varphitildeN d N k)) := by
  interval_cases m
  · rw [iteratedDeriv_zero]; exact hasCompactSupport_varphitildeN d N k
  · rw [iteratedDeriv_one]; exact (hasCompactSupport_varphitildeN d N k).deriv
  · rw [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one]
    exact ((hasCompactSupport_varphitildeN d N k).deriv).deriv

/-- The `L¹` norm of the `m`-th derivative of `φ̃_N` is finite, for `m ≤ 2`. -/
theorem integrable_iteratedDeriv_varphitildeN (d N k m : ℕ) (hm : m ≤ 2) :
    Integrable (fun y => ‖iteratedDeriv m (varphitildeN d N k) y‖) := by
  have hcont : Continuous (iteratedDeriv m (varphitildeN d N k)) :=
    (contDiff_varphitildeN d N k).continuous_iteratedDeriv m (by exact_mod_cast hm)
  exact (hcont.integrable_of_hasCompactSupport (hcs_iteratedDeriv_varphitildeN d N k m hm)).norm

/-- The `m`-th derivative of the modulated bump `φ̃_{N,t}` (`m ≤ 2`) has compact support. -/
theorem hcs_iteratedDeriv_varphitildeNt (P : Polynomial ℤ) (d N k m : ℕ) (hm : m ≤ 2)
    (t : ℝ) :
    HasCompactSupport (iteratedDeriv m (fun ξ => varphitildeNt P d N k t ξ)) := by
  interval_cases m
  · rw [iteratedDeriv_zero]; exact hasCompactSupport_varphitildeNt_aux P d N k t
  · rw [iteratedDeriv_one]; exact (hasCompactSupport_varphitildeNt_aux P d N k t).deriv
  · rw [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one]
    exact ((hasCompactSupport_varphitildeNt_aux P d N k t).deriv).deriv

/-- The `L¹` norm of the `m`-th derivative of the modulated bump `φ̃_{N,t}` is finite, `m ≤ 2`. -/
theorem integrable_iteratedDeriv_varphitildeNt (P : Polynomial ℤ) (d N k m : ℕ) (hm : m ≤ 2)
    (t : ℝ) :
    Integrable (fun y => ‖iteratedDeriv m (fun ξ => varphitildeNt P d N k t ξ) y‖) := by
  have hcont : Continuous (iteratedDeriv m (fun ξ => varphitildeNt P d N k t ξ)) :=
    (contDiff_varphitildeNt_aux P d N k t).continuous_iteratedDeriv m (by exact_mod_cast hm)
  exact (hcont.integrable_of_hasCompactSupport
    (hcs_iteratedDeriv_varphitildeNt P d N k m hm t)).norm

/-- **The price of the modulation `e(P(Nt)·)`**: the second derivative of `φ̃_{N,t}` is controlled
by those of `φ̃_N`, with the modulation frequency bounded by `M ≥ |PevalR P (N t)|`. -/
theorem norm_iteratedDeriv_two_varphitildeNt_le (P : Polynomial ℤ) (d N k : ℕ) (t : ℝ)
    {M : ℝ} (hM : |PevalR P ((N : ℝ) * t)| ≤ M) (y : ℝ) :
    ‖iteratedDeriv 2 (fun ξ => varphitildeNt P d N k t ξ) y‖ ≤
      ‖iteratedDeriv 2 (varphitildeN d N k) y‖
        + (2 * (2 * Real.pi * M)) * ‖iteratedDeriv 1 (varphitildeN d N k) y‖
        + (2 * Real.pi * M) ^ 2 * ‖varphitildeN d N k y‖ := by
  refine le_trans (norm_iteratedDeriv_two_mul_ee_le (varphitildeN d N k)
    (PevalR P ((N : ℝ) * t)) (contDiff_varphitildeN d N k) y) ?_
  have h1 : 2 * (2 * Real.pi * |PevalR P ((N : ℝ) * t)|) ≤ 2 * (2 * Real.pi * M) := by
    have : 2 * Real.pi * |PevalR P ((N : ℝ) * t)| ≤ 2 * Real.pi * M :=
      mul_le_mul_of_nonneg_left hM (by positivity)
    linarith
  have h2 : (2 * Real.pi * |PevalR P ((N : ℝ) * t)|) ^ 2 ≤ (2 * Real.pi * M) ^ 2 :=
    pow_le_pow_left₀ (by positivity)
      (mul_le_mul_of_nonneg_left hM (by positivity)) 2
  linarith [mul_le_mul_of_nonneg_right h1 (norm_nonneg (iteratedDeriv 1 (varphitildeN d N k) y)),
    mul_le_mul_of_nonneg_right h2 (norm_nonneg (varphitildeN d N k y))]

/-- **Uniform-in-`t` bounds for the modulated `d`-fold bump `φ̃_{N,t}`.**  There is `S ≥ 0` such
that for every `t ∈ [1/2,1]` the bump `φ̃_{N,t}` is `C²` with compact support and both `∫‖φ̃_{N,t}‖`
and `∫‖(φ̃_{N,t})''‖` are bounded by `S`. -/
theorem varphitildeNt_bounds (P : Polynomial ℤ) (d N k : ℕ) :
    ∃ S : ℝ, 0 ≤ S ∧ ∀ t ∈ Set.Icc (1/2 : ℝ) 1,
      ContDiff ℝ 2 (fun ξ => varphitildeNt P d N k t ξ) ∧
      HasCompactSupport (fun ξ => varphitildeNt P d N k t ξ) ∧
      (∫ y, ‖varphitildeNt P d N k t y‖) ≤ S ∧
      (∫ y, ‖iteratedDeriv 2 (fun ξ => varphitildeNt P d N k t ξ) y‖) ≤ S := by
  set M : ℝ := max 1 ((∑ i ∈ Finset.range (P.natDegree + 1), |(P.coeff i : ℝ)|) *
    (1 + (N : ℝ)) ^ P.natDegree) with hMdef
  set A : ℝ := ∫ y, ‖varphitildeN d N k y‖ with hA
  set B : ℝ := ∫ y, ‖iteratedDeriv 1 (varphitildeN d N k) y‖ with hB
  set C : ℝ := ∫ y, ‖iteratedDeriv 2 (varphitildeN d N k) y‖ with hC
  set S : ℝ := A + 2 * (2 * Real.pi * M) * B + (2 * Real.pi * M) ^ 2 * A + C + 1 with hS
  have hM1 : 0 ≤ M := le_trans zero_le_one (le_max_left 1 _)
  have hA0 : 0 ≤ A := by rw [hA]; exact integral_nonneg (fun y => norm_nonneg _)
  have hB0 : 0 ≤ B := by rw [hB]; exact integral_nonneg (fun y => norm_nonneg _)
  have hC0 : 0 ≤ C := by rw [hC]; exact integral_nonneg (fun y => norm_nonneg _)
  have hcoef : (0 : ℝ) ≤ 2 * (2 * Real.pi * M) :=
    mul_nonneg (by norm_num)
      (mul_nonneg (mul_nonneg (by norm_num) Real.pi_pos.le) hM1)
  have h2B : 0 ≤ 2 * (2 * Real.pi * M) * B := mul_nonneg hcoef hB0
  have h2A : 0 ≤ (2 * Real.pi * M) ^ 2 * A := mul_nonneg (sq_nonneg _) hA0
  have hSnn : 0 ≤ S := by rw [hS]; linarith
  refine ⟨S, hSnn, ?_⟩
  intro t ht
  refine ⟨contDiff_varphitildeNt_aux P d N k t, hasCompactSupport_varphitildeNt_aux P d N k t,
    ?_, ?_⟩
  · have hcongr : (fun y => ‖varphitildeNt P d N k t y‖) = fun y => ‖varphitildeN d N k y‖ := by
      funext y
      rw [varphitildeNt, norm_mul, norm_ee, mul_one]
    rw [hcongr, ← hA, hS]
    linarith
  · have ht1 : |t| ≤ 1 := by
      rw [abs_le]; exact ⟨by linarith [ht.1], ht.2⟩
    have hc : |PevalR P ((N : ℝ) * t)| ≤ M :=
      le_trans (abs_PevalR_mul_le P N ht1) (le_max_right 1 _)
    have hpt : ∀ y, ‖iteratedDeriv 2 (fun ξ => varphitildeNt P d N k t ξ) y‖ ≤
        ‖iteratedDeriv 2 (varphitildeN d N k) y‖
          + (2 * (2 * Real.pi * M)) * ‖iteratedDeriv 1 (varphitildeN d N k) y‖
          + (2 * Real.pi * M) ^ 2 * ‖varphitildeN d N k y‖ :=
      fun y => norm_iteratedDeriv_two_varphitildeNt_le P d N k t hc y
    have hI1 : Integrable (fun y => ‖iteratedDeriv 2 (varphitildeN d N k) y‖) :=
      integrable_iteratedDeriv_varphitildeN d N k 2 le_rfl
    have hI2 : Integrable (fun y => (2 * (2 * Real.pi * M)) *
        ‖iteratedDeriv 1 (varphitildeN d N k) y‖) :=
      (integrable_iteratedDeriv_varphitildeN d N k 1 (by norm_num)).const_mul _
    have hI3 : Integrable (fun y => (2 * Real.pi * M) ^ 2 * ‖varphitildeN d N k y‖) :=
      ((integrable_varphitildeN_aux d N k).norm).const_mul ((2 * Real.pi * M) ^ 2)
    have hI12 : Integrable (fun y => ‖iteratedDeriv 2 (varphitildeN d N k) y‖ +
        (2 * (2 * Real.pi * M)) * ‖iteratedDeriv 1 (varphitildeN d N k) y‖) := hI1.add hI2
    have hLint : Integrable (fun y =>
        ‖iteratedDeriv 2 (fun ξ => varphitildeNt P d N k t ξ) y‖) :=
      integrable_iteratedDeriv_varphitildeNt P d N k 2 le_rfl t
    have hmono := integral_mono hLint ((hI1.add hI2).add hI3) hpt
    have heq : (∫ y, (‖iteratedDeriv 2 (varphitildeN d N k) y‖ +
            (2 * (2 * Real.pi * M)) * ‖iteratedDeriv 1 (varphitildeN d N k) y‖ +
            (2 * Real.pi * M) ^ 2 * ‖varphitildeN d N k y‖))
        = C + (2 * (2 * Real.pi * M)) * B + (2 * Real.pi * M) ^ 2 * A := by
      rw [integral_add hI12 hI3, integral_add hI1 hI2, integral_const_mul,
        integral_const_mul, ← hA, ← hB, ← hC]
    have hfinal : (∫ y, ‖iteratedDeriv 2 (fun ξ => varphitildeNt P d N k t ξ) y‖) ≤
        C + (2 * (2 * Real.pi * M)) * B + (2 * Real.pi * M) ^ 2 * A :=
      le_trans hmono (le_of_eq heq)
    rw [hS]
    linarith

/-! ## Measurability in `t` of the IW kernel of `φ̃_{N,t}` -/

/-- Joint measurability of `(t, ξ) ↦ φ̃_{N,t}(ξ)` at the generic scale `d`. -/
theorem measurable_varphitildeNt_uncurry_gen (P : Polynomial ℤ) (d N k : ℕ) :
    Measurable (fun q : ℝ × ℝ => varphitildeNt P d N k q.1 q.2) := by
  have hk : Measurable Work.KMTContract.kmtEta := by
    have h : Work.KMTContract.kmtEta
        = fun x : ℝ => ((Work.KMTContract.kmtBump : ℝ → ℝ) x : ℂ) := rfl
    rw [h]
    exact Complex.continuous_ofReal.measurable.comp
      Work.KMTContract.kmtBump.continuous.measurable
  have hvp : Measurable (varphitildeN d N k) := by
    unfold varphitildeN
    split_ifs with h0
    · exact hk.comp (measurable_const_mul _)
    · exact (hk.comp (measurable_const_mul _)).sub (hk.comp (measurable_const_mul _))
  have hee : Measurable ee := by
    unfold ee; fun_prop
  have hP : Measurable (fun q : ℝ × ℝ => PevalR P ((N : ℝ) * q.1)) := by
    have hp : Measurable (PevalR P) := by unfold PevalR; fun_prop
    exact hp.comp ((measurable_const_mul (N : ℝ)).comp measurable_fst)
  unfold varphitildeNt
  exact ((hvp.comp measurable_snd).mul (hee.comp (hP.mul measurable_snd)))

/-- Measurability in `t` of the IW kernel of `φ̃_{N,t}` at the generic scale `d`. -/
theorem measurable_iwKernel_varphitildeNt_gen (P : Polynomial ℤ) (ρ : ℝ) (l d N k : ℕ)
    (j : ℤ) :
    Measurable (fun t : ℝ => iwKernel
      (iwSymbolSet (iwArithFreqs ρ l) (periodize (varphitildeNt P d N k t))) j) := by
  have h := measurable_fourierCoeff_iwSymbolSet (iwArithFreqs ρ l) j
    (φ := fun t ξ => varphitildeNt P d N k t ξ) (measurable_varphitildeNt_uncurry_gen P d N k)
  simpa only [iwKernel] using h

/-! ## The target -/

/-- A summable majorant for the convolution kernel of `Tle ρ l` applied to the modulated bump
`φ̃_{N,t} = varphitildeNt P d N k t`, uniform in `t ∈ [1/2,1]`, together with the measurability
in `t` of that kernel. -/
theorem MdlKerVarphitildeNt (ρ : ℝ) (l d N k : ℕ) (P : Polynomial ℤ) :
    ∃ a : ℤ → ℝ, Summable a ∧
      (∀ t ∈ Set.Icc (1/2 : ℝ) 1, ∀ i : ℤ,
        ‖Work.KMTPlan.A6.mdlIWKer ρ l (Work.KMTAreas.A7.varphitildeNt P d N k t) i‖ ≤ a i) ∧
      (∀ i : ℤ, Measurable (fun t : ℝ =>
        Work.KMTPlan.A6.mdlIWKer ρ l (Work.KMTAreas.A7.varphitildeNt P d N k t) i)) := by
  classical
  obtain ⟨S, hSnn, hS⟩ := varphitildeNt_bounds P d N k
  set C : ℝ := 4 * (((iwArithFreqs ρ l).card : ℝ) * S) + 1 with hC
  refine ⟨fun i => C * (1 / (1 + |(i : ℝ)|) ^ 2), ?_, ?_, ?_⟩
  · have h' : Summable (fun i : ℤ => C * ‖kmtKernWeight i‖) :=
      summable_kmtKernWeight.mul_left C
    refine h'.congr fun i => ?_
    rw [norm_kmtKernWeight]
  · intro t ht i
    obtain ⟨hcd, hcs, h1, h2⟩ := hS t ht
    have hdec := iwKernel_decay_of_bump (iwArithFreqs ρ l) hcd hcs hSnn h1 h2 i
    have hker : ‖Work.KMTPlan.A6.mdlIWKer ρ l (Work.KMTAreas.A7.varphitildeNt P d N k t) i‖
        = ‖Work.Analysis.IWMultiplier.iwKernel
            (Work.Analysis.IonescuWainger.iwSymbolSet
              (Work.Analysis.IonescuWainger.iwArithFreqs ρ l)
              (Work.Analysis.IonescuWainger.periodize
                (Work.KMTAreas.A7.varphitildeNt P d N k t))) i‖ := rfl
    rw [hker, hC]
    refine le_trans hdec ?_
    rw [norm_kmtKernWeight]
  · intro i
    exact measurable_iwKernel_varphitildeNt_gen P ρ l d N k i

end

end Work.KMTPlan.A6
