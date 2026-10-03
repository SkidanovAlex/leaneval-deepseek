/-
# Auxiliary summability and Fourier facts for the identity `symC - symM = symD` (Area A6)

This module collects the elementary analytic inputs of the proof that the §6 symbol
`Work.KMTPlan.A6.symC` of the concrete column, minus the symbol `Work.KMTPlan.A6.symM` of the
model column, is the symbol `Work.KMTPlan.A6.symD` of their difference:

* orbit sums of compactly supported bumps are summable (`symp_summable_comp_add`);
* the `ℓ¹` summability of the Fourier coefficients `cw m j` of a `C²` compactly supported `m`
  (`symp_summable_cw_of_contDiff_hasCompactSupport`) and its instances for the §5/§6 bumps;
* Poisson summation `symp_cw_tsum_fourier` (and the lift form `symp_tsum_cw_mul_fourier_of_lift`),
  identifying `∑'_j cw m j · e (j z)` with the periodisation of `m`;
* the character identity `symp_fourier_eq_eeC` (`fourier j γ = e (j · gamR γ)`), needed to cancel
  the arithmetic frequency against the shift by `gamR γ`.

The module deliberately does not import the A7 module `SmallKernMassBasics` (which contains the
same statements under different names, and which was at some point made unbuildable by a duplicate
declaration of `tmKernel_varphitildeNt_decay`), so that the statements here rest only on the older
and stable A7 files `cw_etaCut_decay`, `FourierDecayExplicit`, `KmtKernelL1Uniform`,
`varphiNt_bounds`, `fourierDecay_varphitildeN` and `Basic`.
-/
import Mathlib
import Submission.Work.KMTAreas.A7.KmtKernelL1Uniform
import Submission.Work.KMTAreas.A7.varphiNt_bounds
import Submission.Work.KMTAreas.A7.fourierDecay_varphitildeN
import Submission.Work.KMTPlan.A6.LowSmallSymDefs
import Submission.Work.KMTPlan.A6.SymSeq_TmKernel_cont

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace Work.KMTPlan.A6

open MeasureTheory Polynomial Finset Filter Topology
open scoped ENNReal NNReal BigOperators FourierTransform
open Work.Analysis.IonescuWainger
open Work.KMTAreas.A7

noncomputable section

local notation "Circ" => Work.Analysis.IonescuWainger.Circle

/-! ## 1. Orbit sums of compactly supported functions -/

/-- A compactly supported function vanishes outside a symmetric interval. -/
lemma symp_exists_abs_bound_of_hasCompactSupport {ψ : ℝ → ℂ} (hs : HasCompactSupport ψ) :
    ∃ R : ℝ, 0 ≤ R ∧ ∀ x : ℝ, R < |x| → ψ x = 0 := by
  obtain ⟨r, hr⟩ := hs.isCompact.isBounded.subset_closedBall (0 : ℝ)
  refine ⟨max r 0, le_max_right _ _, fun x hx => ?_⟩
  by_contra hne
  have hmem : x ∈ tsupport ψ := subset_tsupport ψ hne
  have h1 := hr hmem
  rw [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs] at h1
  linarith [le_max_left r 0]

/-- **The orbit sums of a compactly supported function are summable.** -/
lemma symp_summable_comp_add {ψ : ℝ → ℂ} (hs : HasCompactSupport ψ) (c : ℝ) :
    Summable fun m : ℤ => ψ (c + m) := by
  obtain ⟨R, _, hR⟩ := symp_exists_abs_bound_of_hasCompactSupport hs
  refine summable_of_ne_finset_zero (s := Finset.Icc ⌈-(R + |c| + 1)⌉ ⌊R + |c| + 1⌋)
    (fun m hm => ?_)
  refine hR _ ?_
  by_contra hnot
  push Not at hnot
  have hcm : |((m : ℤ) : ℝ) + c| ≤ R := by rw [add_comm]; exact hnot
  have hm1 : |((m : ℤ) : ℝ)| ≤ |c| + R := by
    have h2 := abs_sub_abs_le_abs_sub ((m : ℤ) : ℝ) (-c)
    rw [abs_neg, sub_neg_eq_add] at h2
    linarith
  rw [Finset.mem_Icc] at hm
  refine hm ⟨?_, ?_⟩
  · rw [Int.ceil_le]
    linarith [neg_abs_le ((m : ℤ) : ℝ), hm1]
  · rw [Int.le_floor]
    linarith [le_abs_self ((m : ℤ) : ℝ), hm1]

lemma symp_summable_varphiN_orbit (N k : ℕ) (c : ℝ) :
    Summable fun m : ℤ => varphiN N k (c + m) :=
  symp_summable_comp_add (hasCompactSupport_varphiN N k) c

lemma symp_summable_varphitildeN_orbit (d N k : ℕ) (c : ℝ) :
    Summable fun m : ℤ => varphitildeN d N k (c + m) :=
  symp_summable_comp_add (hasCompactSupport_varphitildeN d N k) c

lemma symp_summable_varphiNt_orbit (N k : ℕ) (t c : ℝ) :
    Summable fun m : ℤ => varphiNt N k t (c + m) :=
  symp_summable_comp_add (hasCompactSupport_varphiNt N k t) c

/-! ## 2. The character `e (z) = exp (2 π i z)` and `fourier` on the circle -/

lemma symp_eeC_eq_ee (z : ℝ) : eeC z = Work.KMTAreas.A7.ee z := rfl

lemma symp_norm_eeC (z : ℝ) : ‖eeC z‖ = 1 := by
  rw [eeC, Complex.norm_exp]
  simp

lemma symp_eeC_add (a b : ℝ) : eeC (a + b) = eeC a * eeC b := by
  rw [eeC, eeC, eeC, ← Complex.exp_add]
  congr 1
  push_cast
  ring

lemma symp_eeC_int (n : ℤ) : eeC (n : ℝ) = 1 := by
  rw [eeC, show (2 * (Real.pi : ℂ) * Complex.I * ((n : ℝ) : ℂ))
      = (n : ℂ) * (2 * Real.pi * Complex.I) by push_cast; ring]
  exact Complex.exp_int_mul_two_pi_mul_I n

/-- **The characters of `fourier` are `e (j · γ)`** in the `gamR` coordinate. -/
lemma symp_fourier_eq_eeC (j : ℤ) (γ : Circ) :
    fourier (T := 1) j γ = eeC ((j : ℝ) * gamR γ) := by
  have h : (((gamR γ : ℝ)) : Circ) = γ := by
    rw [gamR]
    exact AddCircle.coe_equivIco
  conv_lhs => rw [← h]
  exact fourier_coe_one' j (gamR γ)

/-- The periodisation at a lift is the orbit sum (`periodizeCoeEqTsum`). -/
lemma symp_periodize_eq_tsum (φ : ℝ → ℂ) (z : ℝ) :
    periodize φ ((z : ℝ) : Circ) = ∑' m : ℤ, φ (z + m) :=
  Work.KMTContract.periodizeCoeEqTsum φ z

/-! ## 3. Summability of the Fourier coefficients `cw m` -/

/-- **The Fourier coefficients of a `C²` compactly supported function are `ℓ¹`.**  The proof is
the explicit quadratic decay `FourierDecayExplicit` (with the constant
`4 max ‖m‖₁ ‖m''‖₁ + 1`) dominated by the summable comparison weight `kmtKernWeight`. -/
theorem symp_summable_cw_of_contDiff_hasCompactSupport {m : ℝ → ℂ} (hcd : ContDiff ℝ 2 m)
    (hcs : HasCompactSupport m) : Summable fun j : ℤ => ‖cw m j‖ := by
  refine Summable.of_nonneg_of_le (fun j => norm_nonneg _) (fun j => ?_)
    (summable_kmtKernWeight.mul_left
      (4 * max (∫ y, ‖m y‖) (∫ y, ‖iteratedDeriv 2 m y‖) + 1))
  rw [cw_eq_fourierTransform, norm_kmtKernWeight, one_div]
  simpa only [div_eq_mul_inv] using FourierDecayExplicit hcd hcs (j : ℝ)

/-- `φ̃_{N,t}` is `C²` (the modulation by `e (P (N t) ξ)` is smooth). -/
lemma symp_contDiff_varphitildeNt (P : Polynomial ℤ) (d N k : ℕ) (t : ℝ) :
    ContDiff ℝ 2 (varphitildeNt P d N k t) := by
  unfold varphitildeNt
  exact (contDiff_varphitildeN d N k).mul (contDiff_ee_const_mul 2 (PevalR P ((N : ℝ) * t)))

/-- `φ̃_{N,t}` is compactly supported (as is `φ̃_N`). -/
lemma symp_hasCompactSupport_varphitildeNt (P : Polynomial ℤ) (d N k : ℕ) (t : ℝ) :
    HasCompactSupport (varphitildeNt P d N k t) := by
  unfold varphitildeNt
  exact (hasCompactSupport_varphitildeN d N k).mul_right

/-- `φ̃_{N,t}` is integrable. -/
lemma symp_integrable_varphitildeNt (P : Polynomial ℤ) (d N k : ℕ) (t : ℝ) :
    Integrable (varphitildeNt P d N k t) :=
  (symp_contDiff_varphitildeNt P d N k t).continuous.integrable_of_hasCompactSupport
    (symp_hasCompactSupport_varphitildeNt P d N k t)

lemma symp_summable_varphitildeNt_orbit (P : Polynomial ℤ) (d N k : ℕ) (t c : ℝ) :
    Summable fun m : ℤ => varphitildeNt P d N k t (c + m) :=
  symp_summable_comp_add (symp_hasCompactSupport_varphitildeNt P d N k t) c

theorem symp_summable_cw_varphiN (N k : ℕ) :
    Summable fun j : ℤ => ‖cw (varphiN N k) j‖ :=
  symp_summable_cw_of_contDiff_hasCompactSupport (contDiff_varphiN N k)
    (hasCompactSupport_varphiN N k)

theorem symp_summable_cw_varphitildeN (d N k : ℕ) :
    Summable fun j : ℤ => ‖cw (varphitildeN d N k) j‖ :=
  symp_summable_cw_of_contDiff_hasCompactSupport (contDiff_varphitildeN d N k)
    (hasCompactSupport_varphitildeN d N k)

theorem symp_summable_cw_varphiNt (N k : ℕ) (t : ℝ) :
    Summable fun j : ℤ => ‖cw (varphiNt N k t) j‖ :=
  symp_summable_cw_of_contDiff_hasCompactSupport (contDiff_varphiNt N k t)
    (hasCompactSupport_varphiNt N k t)

theorem symp_summable_cw_varphitildeNt (P : Polynomial ℤ) (d N k : ℕ) (t : ℝ) :
    Summable fun j : ℤ => ‖cw (varphitildeNt P d N k t) j‖ :=
  symp_summable_cw_of_contDiff_hasCompactSupport (symp_contDiff_varphitildeNt P d N k t)
    (symp_hasCompactSupport_varphitildeNt P d N k t)

lemma symp_contDiff_mStarF (u : ℕ) : ContDiff ℝ 2 (mStarF u) :=
  (contDiff_etaCut (-(2 * (u : ℤ)))).of_le (WithTop.coe_le_coe.mpr le_top)

lemma symp_hasCompactSupport_mStarF (u : ℕ) : HasCompactSupport (mStarF u) :=
  hasCompactSupport_etaCut (-(2 * (u : ℤ)))

lemma symp_contDiff_mStargF (d u : ℕ) : ContDiff ℝ 2 (mStargF d u) :=
  (contDiff_etaCut (-((d : ℤ) * 2 * (u : ℤ)))).of_le (WithTop.coe_le_coe.mpr le_top)

lemma symp_hasCompactSupport_mStargF (d u : ℕ) : HasCompactSupport (mStargF d u) :=
  hasCompactSupport_etaCut (-((d : ℤ) * 2 * (u : ℤ)))

theorem symp_summable_cw_mStarF (u : ℕ) :
    Summable fun j : ℤ => ‖cw (mStarF u) j‖ := by
  obtain ⟨C, _, hC⟩ := cw_etaCut_decay (-(2 * (u : ℤ)))
  refine Summable.of_nonneg_of_le (fun j => norm_nonneg _) (fun j => ?_)
    (summable_kmtKernWeight.mul_left C)
  rw [norm_kmtKernWeight, one_div]
  simpa only [mStarF, div_eq_mul_inv] using hC j

theorem symp_summable_cw_mStargF (d u : ℕ) :
    Summable fun j : ℤ => ‖cw (mStargF d u) j‖ := by
  obtain ⟨C, _, hC⟩ := cw_etaCut_decay (-((d : ℤ) * 2 * (u : ℤ)))
  refine Summable.of_nonneg_of_le (fun j => norm_nonneg _) (fun j => ?_)
    (summable_kmtKernWeight.mul_left C)
  rw [norm_kmtKernWeight, one_div]
  simpa only [mStargF, div_eq_mul_inv] using hC j

/-! ## 4. Poisson summation for `cw` -/

/-- **Poisson summation for `cw` at a lift.**  For a `C²` compactly supported `m` and any `x : ℝ`,
`∑'_j cw m j · e (j x) = ∑'_k m (x + k)`. -/
theorem symp_tsum_cw_mul_fourier_of_lift {m : ℝ → ℂ} (hm : ContDiff ℝ 2 m)
    (hcs : HasCompactSupport m) (x : ℝ) :
    ∑' j : ℤ, cw m j * fourier (T := 1) j ((x : ℝ) : Circ) = ∑' k : ℤ, m (x + k) := by
  have hsum_cw : Summable fun j : ℤ => ‖cw m j‖ :=
    symp_summable_cw_of_contDiff_hasCompactSupport hm hcs
  have hsum : Summable fun j : ℤ => 𝓕 m (j : ℝ) := by
    refine Summable.of_norm ?_
    simpa only [cw_eq_fourierTransform] using hsum_cw
  have hbig : m =O[Filter.cocompact ℝ] (fun y : ℝ => |y| ^ (-(2 : ℝ))) := by
    refine Asymptotics.IsBigO.of_bound 1 ?_
    have hme : m =ᶠ[Filter.cocompact ℝ] 0 := by
      simpa using (hasCompactSupport_iff_eventuallyEq.mp hcs)
    filter_upwards [hme] with y hy
    simp only [Pi.zero_apply] at hy
    rw [hy]
    simp only [norm_zero]
    positivity
  have hp := Real.tsum_eq_tsum_fourier_of_rpow_decay_of_summable (f := m) hm.continuous
    (b := 2) one_lt_two hbig hsum x
  rw [hp]
  exact tsum_congr fun j => by rw [cw_eq_fourierTransform]

/-- **Poisson summation for `cw`, on the circle.** -/
theorem symp_cw_tsum_fourier {m : ℝ → ℂ} (hm : ContDiff ℝ 2 m) (hcs : HasCompactSupport m)
    (θ : Circ) : ∑' j : ℤ, cw m j * fourier (T := 1) j θ = periodize m θ := by
  rw [periodize]
  have h := symp_tsum_cw_mul_fourier_of_lift hm hcs
    ((AddCircle.equivIco (1 : ℝ) 0 θ).val)
  rwa [AddCircle.coe_equivIco] at h

end

end Work.KMTPlan.A6
