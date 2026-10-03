/-
# Uniform C2 and L1 bounds for the modified KMT bumps `varphiNtj`

The modified bumps of the Krause--Mirek--Tao integration-by-parts identity (Section 6) are

  `varphiNtj N k j t ξ = (2^{-k}Nξ)^j · varphiN N k ξ · e(Ntξ)`,

where `varphiN` is the difference of rescalings of the fixed cutoff `η`
(`Work.KMTAreas.A7.varphiN`).  The paper only uses `j ∈ {-1,0,1}`, and the case `(k,j) = (0,-1)` is
excluded there, since `(Nξ)^{-1}` is singular at the frequency origin; the hypothesis
`hk : k ≠ 0 ∨ 0 ≤ j` is exactly that non-singularity condition.

This file proves that `varphiNtj N k j t` is `C²` with compact support for every `j` satisfying
`hk`, with the `L¹`-norms of the bump and of its second derivative bounded uniformly in
`t ∈ [1/2,1]`.

The singular factor is split off:

* `varphiNtjCore N k j = (2^{-k}Nξ)^j varphiN N k ξ` (no modulation);
* `varphiNtj N k j t = varphiNtjCore N k j · e(Nt·)` (`varphiNtj_eq_core_mul`), so that the Leibniz
  rule `Work.KMTAreas.A7.norm_iteratedDeriv_two_mul_ee_le` gives the second-derivative bound and
  the unimodularity `‖e‖ = 1` gives the first one;
* the core is `C²`: for `0 ≤ j` the factor `(2^{-k}Nξ)^j` is a polynomial; for `j < 0` (hence
  `1 ≤ k`) it is singular only at `ξ = 0`, where `varphiN` vanishes on a whole neighbourhood
  (`varphiN_eq_zero_of_abs_lt`), so the product is smooth there.  The same vanishing gives the
  compact support of the core, since `varphiN` has compact support.

All the auxiliary declarations of this file are `private`, so that the module can be imported
alongside `Submission.Work.KMTPlan.A6.MdlKerVarphiNtj` (which declares a same-named helper
`varphiN_eq_zero_of_abs_lt` and its own `varphiNtj_bounds` for the special case `j = -1`, `1 ≤ k`);
that module is deliberately *not* imported here (it would clash by name, and it currently does not
build).
-/
import Mathlib
import Submission.Work.KMTPlan.A6.MdlDefs
import Submission.Work.KMTAreas.A7.varphiNt_bounds

namespace Work.KMTPlan.A6

open MeasureTheory Filter
open scoped Topology
open Work.KMTAreas.A7
open Work.Analysis.EndVar

noncomputable section

set_option maxHeartbeats 1000000

/-! ## The unmodulated core -/

/-- The unmodulated core `(2^{-k}Nξ)^j varphiN N k ξ` of the modified bump. -/
private def varphiNtjCore (N k : ℕ) (j : ℤ) : ℝ → ℂ :=
  fun ξ => ((((2 : ℝ) ^ (-(k : ℝ)) * (N : ℝ) * ξ : ℝ)) : ℂ) ^ j * varphiN N k ξ

/-- The modified bump is the modulation `e(Nt·)` of its core. -/
private theorem varphiNtj_eq_core_mul (N k : ℕ) (j : ℤ) (t : ℝ) :
    varphiNtj N k j t = varphiNtjCore N k j * fun ξ : ℝ => ee (((N : ℝ) * t) * ξ) := by
  funext ξ
  simp only [varphiNtj, varphiNtjCore, varphiNt, Pi.mul_apply]
  exact (mul_assoc _ _ _).symm

/-! ## Vanishing of `varphiN` near the origin for `k ≥ 1` -/

/-- For `1 ≤ k` the bump `varphiN N k` is identically zero on the open ball of radius
`(1/4) 2^{k - Log N}` around the origin: there both cutoffs `η(2^{Log N-k}·)` and
`η(2^{Log N-k+1}·)` equal `1`. -/
private lemma varphiN_eq_zero_of_abs_lt (N k : ℕ) (hk : 1 ≤ k) {y : ℝ}
    (hy : |y| < (1 / 4 : ℝ) * (2 : ℝ) ^ ((k : ℝ) - (logN N : ℝ))) :
    varphiN N k y = 0 := by
  have hk0 : k ≠ 0 := by omega
  simp only [varphiN, if_neg hk0]
  have hδpos : 0 < (2 : ℝ) ^ ((logN N : ℝ) - (k : ℝ)) :=
    Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) _
  have hne : (2 : ℝ) ^ ((logN N : ℝ) - (k : ℝ)) ≠ 0 := ne_of_gt hδpos
  have hdelta : (2 : ℝ) ^ ((k : ℝ) - (logN N : ℝ)) =
      ((2 : ℝ) ^ ((logN N : ℝ) - (k : ℝ)))⁻¹ := by
    rw [show (k : ℝ) - (logN N : ℝ) = -((logN N : ℝ) - (k : ℝ)) by ring,
      Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)]
  have heq : (2 : ℝ) ^ ((logN N : ℝ) - (k : ℝ)) *
      ((1 / 4 : ℝ) * ((2 : ℝ) ^ ((logN N : ℝ) - (k : ℝ)))⁻¹) = 1 / 4 := by
    rw [mul_comm ((1 / 4 : ℝ)) ((2 : ℝ) ^ ((logN N : ℝ) - (k : ℝ)))⁻¹, ← mul_assoc,
      mul_inv_cancel₀ hne, one_mul]
  have hmain : (2 : ℝ) ^ ((logN N : ℝ) - (k : ℝ)) * |y| < 1 / 4 := by
    have h := mul_lt_mul_of_pos_left hy hδpos
    rw [hdelta] at h
    linarith [h, heq]
  have h1 : |(2 : ℝ) ^ ((logN N : ℝ) - (k : ℝ)) * y| ≤ 1 / 2 := by
    rw [abs_mul, abs_of_pos hδpos]; linarith
  have h2 : |(2 : ℝ) ^ ((logN N : ℝ) - (k : ℝ) + 1) * y| ≤ 1 / 2 := by
    have hpow : (2 : ℝ) ^ ((logN N : ℝ) - (k : ℝ) + 1) =
        2 * (2 : ℝ) ^ ((logN N : ℝ) - (k : ℝ)) := by
      rw [show (logN N : ℝ) - (k : ℝ) + 1 = ((logN N : ℝ) - (k : ℝ)) + 1 by ring,
        Real.rpow_add (by norm_num : (0 : ℝ) < 2), Real.rpow_one]
      ring
    have hpos : 0 < (2 : ℝ) ^ ((logN N : ℝ) - (k : ℝ) + 1) :=
      Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) _
    rw [abs_mul, abs_of_pos hpos, hpow]
    nlinarith [hmain]
  rw [Work.KMTContract.kmtEta_one h1, Work.KMTContract.kmtEta_one h2, sub_self]

/-! ## Smoothness of the core -/

/-- The core is `C²` when `j < 0` (so that `1 ≤ k`): the singular factor `(2^{-k}Nξ)^{-(m+1)}`
meets `varphiN` only where the latter is identically zero, and elsewhere it is smooth. -/
private lemma contDiff_varphiNtjCore_negSucc (N k m : ℕ) (hk : 1 ≤ k) :
    ContDiff ℝ 2 (fun ξ : ℝ =>
      ((((2 : ℝ) ^ (-(k : ℝ)) * (N : ℝ) * ξ : ℝ)) : ℂ) ^ (Int.negSucc m) *
        varphiN N k ξ) := by
  rcases Nat.eq_zero_or_pos N with hN | hN
  · subst hN
    have hzero : (fun ξ : ℝ =>
        ((((2 : ℝ) ^ (-(k : ℝ)) * ((0 : ℕ) : ℝ) * ξ : ℝ)) : ℂ) ^ (Int.negSucc m) *
          varphiN 0 k ξ) = fun _ => 0 := by
      funext ξ
      rw [zpow_negSucc]
      simp
    rw [hzero]; exact contDiff_const
  · rw [contDiff_iff_contDiffAt]
    intro x
    set δ : ℝ := (1 / 4 : ℝ) * (2 : ℝ) ^ ((k : ℝ) - (logN N : ℝ)) with hδ
    by_cases hx : |x| < δ
    · have hxmem : Set.Ioo (-δ) δ ∈ 𝓝 x :=
        isOpen_Ioo.mem_nhds (by rw [Set.mem_Ioo]; exact abs_lt.mp hx)
      have hev : (fun ξ : ℝ => ((((2 : ℝ) ^ (-(k : ℝ)) * (N : ℝ) * ξ : ℝ)) : ℂ) ^
            (Int.negSucc m) * varphiN N k ξ) =ᶠ[𝓝 x] (fun _ => 0) := by
        refine Filter.mem_of_superset hxmem (fun ξ hξ => ?_)
        simp only [Set.mem_ofPred_eq]
        have hlt : |ξ| < (1 / 4 : ℝ) * (2 : ℝ) ^ ((k : ℝ) - (logN N : ℝ)) := by
          rw [← hδ]
          exact abs_lt.mpr (by simpa only [Set.mem_Ioo] using hξ)
        rw [varphiN_eq_zero_of_abs_lt N k hk hlt, mul_zero]
      exact (contDiffAt_const (c := (0 : ℂ))).congr_of_eventuallyEq hev
    · have hxδ : δ ≤ |x| := le_of_not_gt hx
      have hδpos : 0 < δ := by
        rw [hδ]
        exact mul_pos (by norm_num) (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) _)
      have hx0 : x ≠ 0 := by
        intro h; rw [h, abs_zero] at hxδ; linarith
      have hcne : (2 : ℝ) ^ (-(k : ℝ)) * (N : ℝ) * x ≠ 0 := by
        have h1 : (0 : ℝ) < (2 : ℝ) ^ (-(k : ℝ)) := Real.rpow_pos_of_pos (by norm_num) _
        have h2 : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
        exact mul_ne_zero (mul_ne_zero (ne_of_gt h1) (ne_of_gt h2)) hx0
      have hne : ((((2 : ℝ) ^ (-(k : ℝ)) * (N : ℝ) * x : ℝ)) : ℂ) ^ (m + 1) ≠ 0 :=
        pow_ne_zero _ (Complex.ofReal_ne_zero.mpr hcne)
      have hpow : ContDiffAt ℝ 2 (fun ξ : ℝ =>
          ((((2 : ℝ) ^ (-(k : ℝ)) * (N : ℝ) * ξ : ℝ)) : ℂ) ^ (m + 1)) x :=
        (by fun_prop : ContDiff ℝ 2 (fun ξ : ℝ =>
          ((((2 : ℝ) ^ (-(k : ℝ)) * (N : ℝ) * ξ : ℝ)) : ℂ) ^ (m + 1))).contDiffAt
      simp only [zpow_negSucc]
      exact (hpow.inv hne).mul (contDiff_varphiN N k).contDiffAt

/-- The core is `C²` when `0 ≤ j`: the factor `(2^{-k}Nξ)^j` is then a polynomial. -/
private lemma contDiff_varphiNtjCore_of_nonneg (N k : ℕ) (j : ℤ) (hj : 0 ≤ j) :
    ContDiff ℝ 2 (varphiNtjCore N k j) := by
  have hfun : varphiNtjCore N k j =
      fun ξ : ℝ => ((((2 : ℝ) ^ (-(k : ℝ)) * (N : ℝ) * ξ : ℝ)) : ℂ) ^ (j.toNat) *
        varphiN N k ξ := by
    funext ξ
    simp only [varphiNtjCore]
    conv_lhs => rw [← Int.toNat_of_nonneg hj]
    rw [zpow_natCast]
  rw [hfun]
  apply ContDiff.mul
  · fun_prop
  · exact contDiff_varphiN N k

/-- The core is `C²` under the non-singularity hypothesis `k ≠ 0 ∨ 0 ≤ j`. -/
private lemma contDiff_varphiNtjCore (N k : ℕ) (j : ℤ) (hk : k ≠ 0 ∨ 0 ≤ j) :
    ContDiff ℝ 2 (varphiNtjCore N k j) := by
  rcases lt_or_ge j 0 with hj | hj
  · have hk1 : 1 ≤ k := by
      rcases hk with h | h
      · omega
      · omega
    obtain ⟨m, hm⟩ := Int.eq_negSucc_of_lt_zero hj
    have hfun : varphiNtjCore N k j = fun ξ : ℝ =>
        ((((2 : ℝ) ^ (-(k : ℝ)) * (N : ℝ) * ξ : ℝ)) : ℂ) ^ (Int.negSucc m) *
          varphiN N k ξ := by
      funext ξ
      simp only [varphiNtjCore, hm]
    rw [hfun]
    exact contDiff_varphiNtjCore_negSucc N k m hk1
  · exact contDiff_varphiNtjCore_of_nonneg N k j hj

/-! ## Compact support of the core -/

/-- The core is supported in the support of `varphiN`, hence has compact support. -/
private lemma hasCompactSupport_varphiNtjCore (N k : ℕ) (j : ℤ) :
    HasCompactSupport (varphiNtjCore N k j) := by
  refine (hasCompactSupport_varphiN N k).mono ?_
  intro ξ hξ
  simp only [Function.mem_support] at hξ ⊢
  intro hφ
  exact hξ (by simp only [varphiNtjCore, hφ, mul_zero])

/-! ## Integrability of the derivatives of the core -/

/-- The `L¹`-norms of the core and of its first two derivatives are finite. -/
private lemma integrable_iteratedDeriv_varphiNtjCore (N k : ℕ) (j : ℤ) (hk : k ≠ 0 ∨ 0 ≤ j)
    (m : ℕ) (hm : m ≤ 2) :
    Integrable (fun y => ‖iteratedDeriv m (varphiNtjCore N k j) y‖) := by
  have hcd := contDiff_varphiNtjCore N k j hk
  have hcs : HasCompactSupport (iteratedDeriv m (varphiNtjCore N k j)) := by
    interval_cases m
    · rw [iteratedDeriv_zero]; exact hasCompactSupport_varphiNtjCore N k j
    · rw [iteratedDeriv_one]; exact (hasCompactSupport_varphiNtjCore N k j).deriv
    · rw [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one]
      exact ((hasCompactSupport_varphiNtjCore N k j).deriv).deriv
  have hcont : Continuous (iteratedDeriv m (varphiNtjCore N k j)) :=
    hcd.continuous_iteratedDeriv m (by exact_mod_cast hm)
  exact (hcont.integrable_of_hasCompactSupport hcs).norm

/-! ## The modified bump -/

/-- The modified bump is `C²` for every `t` under the non-singularity hypothesis. -/
private theorem contDiff_varphiNtj (N k : ℕ) (j : ℤ) (hk : k ≠ 0 ∨ 0 ≤ j) (t : ℝ) :
    ContDiff ℝ 2 (varphiNtj N k j t) := by
  rw [varphiNtj_eq_core_mul]
  exact (contDiff_varphiNtjCore N k j hk).mul (contDiff_ee_const_mul 2 ((N : ℝ) * t))

/-- The modified bump has compact support. -/
private theorem hasCompactSupport_varphiNtj (N k : ℕ) (j : ℤ) (t : ℝ) :
    HasCompactSupport (varphiNtj N k j t) := by
  rw [varphiNtj_eq_core_mul]
  refine (hasCompactSupport_varphiNtjCore N k j).mono ?_
  intro ξ hξ
  simp only [Function.mem_support, Pi.mul_apply] at hξ ⊢
  intro hq
  exact hξ (by rw [hq, zero_mul])

/-! ## The main bounds -/

theorem varphiNtj_bounds (N k : ℕ) (j : ℤ) (hk : k ≠ 0 ∨ 0 ≤ j) :
    ∃ S : ℝ, 0 ≤ S ∧ ∀ t ∈ Set.Icc (1/2 : ℝ) 1,
      ContDiff ℝ 2 (Work.KMTPlan.A6.varphiNtj N k j t) ∧
      HasCompactSupport (Work.KMTPlan.A6.varphiNtj N k j t) ∧
      (∫ y, ‖Work.KMTPlan.A6.varphiNtj N k j t y‖ ∂MeasureTheory.volume) ≤ S ∧
      (∫ y, ‖iteratedDeriv 2 (Work.KMTPlan.A6.varphiNtj N k j t) y‖ ∂MeasureTheory.volume) ≤ S := by
  set A : ℝ := ∫ y, ‖varphiNtjCore N k j y‖ with hA
  set B : ℝ := ∫ y, (‖iteratedDeriv 2 (varphiNtjCore N k j) y‖ +
      (2 * (2 * Real.pi * (N : ℝ))) * ‖iteratedDeriv 1 (varphiNtjCore N k j) y‖ +
      (2 * Real.pi * (N : ℝ)) ^ 2 * ‖varphiNtjCore N k j y‖) with hB
  have hI0 : Integrable (fun y => ‖varphiNtjCore N k j y‖) :=
    integrable_iteratedDeriv_varphiNtjCore N k j hk 0 (by norm_num)
  have hI1 : Integrable (fun y => ‖iteratedDeriv 1 (varphiNtjCore N k j) y‖) :=
    integrable_iteratedDeriv_varphiNtjCore N k j hk 1 (by norm_num)
  have hI2 : Integrable (fun y => ‖iteratedDeriv 2 (varphiNtjCore N k j) y‖) :=
    integrable_iteratedDeriv_varphiNtjCore N k j hk 2 le_rfl
  have hmaj : Integrable (fun y => ‖iteratedDeriv 2 (varphiNtjCore N k j) y‖ +
      (2 * (2 * Real.pi * (N : ℝ))) * ‖iteratedDeriv 1 (varphiNtjCore N k j) y‖ +
      (2 * Real.pi * (N : ℝ)) ^ 2 * ‖varphiNtjCore N k j y‖) :=
    (hI2.add (hI1.const_mul (2 * (2 * Real.pi * (N : ℝ))))).add
      (hI0.const_mul ((2 * Real.pi * (N : ℝ)) ^ 2))
  have hA0 : 0 ≤ A := by
    rw [hA]; exact integral_nonneg (fun y => norm_nonneg _)
  have hB0 : 0 ≤ B := by
    rw [hB]; exact integral_nonneg (fun y => by positivity)
  refine ⟨max A B + 1, ?_, ?_⟩
  · have h1 : 0 ≤ max A B := le_trans hA0 (le_max_left A B)
    linarith
  · intro t ht
    refine ⟨contDiff_varphiNtj N k j hk t, hasCompactSupport_varphiNtj N k j t, ?_, ?_⟩
    · have hcongr : (fun y => ‖varphiNtj N k j t y‖) = fun y => ‖varphiNtjCore N k j y‖ := by
        funext y
        rw [varphiNtj_eq_core_mul, Pi.mul_apply, norm_mul, norm_ee, mul_one]
      have heq : (∫ y, ‖varphiNtj N k j t y‖) = A := by
        rw [hcongr]
      rw [heq]
      linarith [le_max_left A B]
    · have hpt : ∀ y, ‖iteratedDeriv 2 (varphiNtj N k j t) y‖ ≤
          (‖iteratedDeriv 2 (varphiNtjCore N k j) y‖ +
            (2 * (2 * Real.pi * (N : ℝ))) * ‖iteratedDeriv 1 (varphiNtjCore N k j) y‖ +
            (2 * Real.pi * (N : ℝ)) ^ 2 * ‖varphiNtjCore N k j y‖) := by
        intro y
        have hb := norm_iteratedDeriv_two_mul_ee_le (varphiNtjCore N k j) ((N : ℝ) * t)
          (contDiff_varphiNtjCore N k j hk) y
        have htabs : |t| ≤ 1 := by rw [abs_le]; exact ⟨by linarith [ht.1], ht.2⟩
        have hc : |(N : ℝ) * t| ≤ (N : ℝ) := by
          rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg N)]
          exact mul_le_of_le_one_right (Nat.cast_nonneg N) htabs
        have h1 : 2 * (2 * Real.pi * |(N : ℝ) * t|) *
              ‖iteratedDeriv 1 (varphiNtjCore N k j) y‖ ≤
            2 * (2 * Real.pi * (N : ℝ)) * ‖iteratedDeriv 1 (varphiNtjCore N k j) y‖ := by
          gcongr
        have h2 : (2 * Real.pi * |(N : ℝ) * t|) ^ 2 * ‖varphiNtjCore N k j y‖ ≤
            (2 * Real.pi * (N : ℝ)) ^ 2 * ‖varphiNtjCore N k j y‖ := by gcongr
        simp only [varphiNtj_eq_core_mul]
        linarith [hb, h1, h2]
      have hLint : Integrable (fun y => ‖iteratedDeriv 2 (varphiNtj N k j t) y‖) := by
        have hcont : Continuous (fun y => ‖iteratedDeriv 2 (varphiNtj N k j t) y‖) :=
          ((contDiff_varphiNtj N k j hk t).continuous_iteratedDeriv 2 le_rfl).norm
        exact hmaj.mono' hcont.aestronglyMeasurable
          (Filter.Eventually.of_forall (fun y => by simpa only [norm_norm] using hpt y))
      have hmono : (∫ y, ‖iteratedDeriv 2 (varphiNtj N k j t) y‖) ≤
          ∫ y, (‖iteratedDeriv 2 (varphiNtjCore N k j) y‖ +
            (2 * (2 * Real.pi * (N : ℝ))) * ‖iteratedDeriv 1 (varphiNtjCore N k j) y‖ +
            (2 * Real.pi * (N : ℝ)) ^ 2 * ‖varphiNtjCore N k j y‖) := by
        simpa using integral_mono hLint hmaj hpt
      have hB' : (∫ y, (‖iteratedDeriv 2 (varphiNtjCore N k j) y‖ +
            (2 * (2 * Real.pi * (N : ℝ))) * ‖iteratedDeriv 1 (varphiNtjCore N k j) y‖ +
            (2 * Real.pi * (N : ℝ)) ^ 2 * ‖varphiNtjCore N k j y‖)) = B := hB.symm
      rw [hB'] at hmono
      linarith [hmono, le_max_right A B]

end

end Work.KMTPlan.A6
