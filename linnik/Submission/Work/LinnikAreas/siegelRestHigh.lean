import Mathlib
import Submission.Work.LinnikAreas.SiegelBase
import Submission.Work.LinnikAreas.boxMaxZero
import Submission.Work.LinnikAreas.pairCountHeight_dom

open DirichletCharacter Complex
open scoped Classical BigOperators
noncomputable section

namespace Work.LinnikAreas

open Work.LinnikContract

set_option linter.unusedVariables false

/-- Every zero counted by `zeroMult` (any character, principal or not) has positive real part. -/
theorem zeroMult_re_pos {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {ρ : ℂ}
    (h : zeroMult χ ρ ≠ 0) : 0 < ρ.re := by
  by_cases hχ : χ = 1
  · subst hχ
    rw [boxMaxZeroAux.zeroMult_one_eq_completedRiemannZeta q ρ] at h
    have hΛ : completedRiemannZeta ρ = 0 := apply_eq_zero_of_analyticOrderNatAt_ne_zero h
    by_contra hc
    push_neg at hc
    have hΛ' : completedRiemannZeta (1 - ρ) = 0 := by
      rw [completedRiemannZeta_one_sub ρ]; exact hΛ
    have hs1 : 1 ≤ (1 - ρ).re := by simp; linarith only [hc]
    have hs0 : (1 - ρ) ≠ 0 := by
      intro h0
      have h1 : ρ = 1 := by linear_combination -h0
      rw [h1] at hc; norm_num at hc
    have hz : riemannZeta (1 - ρ) = 0 := by
      rw [riemannZeta_def_of_ne_zero hs0, hΛ']; simp
    exact riemannZeta_ne_zero_of_one_le_re hs1 hz
  · haveI : NeZero χ.conductor := ⟨DirichletCharacter.conductor_ne_zero χ⟩
    have h2 : analyticOrderNatAt (DirichletCharacter.completedLFunction χ.primitiveCharacter) ρ
        ≠ 0 := h
    have hz : DirichletCharacter.completedLFunction χ.primitiveCharacter ρ = 0 :=
      apply_eq_zero_of_analyticOrderNatAt_ne_zero h2
    exact (Commons.NumberTheory.DirichletCharacter.zerosInStrip χ.primitiveCharacter
      (boxMaxZeroAux.primitiveCharacter_ne_one_of_ne_one χ hχ)
      (DirichletCharacter.primitiveCharacter_isPrimitive χ) ρ hz).1

/-- Kernel bound on a high zero (`|Im ρ| > 1`) of level `q > 1`:
`mult·‖Hk‖ ≤ 4·mult·e^{-a₀λ}/T²` with `T = |Im ρ|·log q` and `a₀ = 49/10`. -/
lemma high_kernel_le {q : ℕ} [NeZero q] (hq : 1 < q) (z : DirichletCharacter ℂ q × ℂ)
    (hzm : zeroMult z.1 z.2 ≠ 0) (hhigh : 1 < |z.2.im|) :
    (zeroMult z.1 z.2 : ℝ) * ‖Hk (11 / 2) (3 / 10) ((1 - z.2) * (Real.log q : ℂ))‖
      ≤ 4 * ((zeroMult z.1 z.2 : ℝ) * Real.exp (-(49 / 10) * lamOf q z.2))
          / (|z.2.im| * Real.log q) ^ 2 := by
  have hlog : 0 < Real.log q := Real.log_pos (by exact_mod_cast hq)
  have himpos : 0 < |z.2.im| := by linarith only [hhigh]
  have hTpos : 0 < |z.2.im| * Real.log q := mul_pos himpos hlog
  have hρ : z.2.re < 1 := boxMaxZeroAux.zeroMult_re_lt_one z.1 hzm
  have hbound := Siegel.Hk_norm_le_invSq_lamOf (q := q) (L := 11 / 2) (K := 3 / 10)
    (by norm_num) hq hρ
  have hcoef : (11 / 2 : ℝ) - 2 * (3 / 10) = 49 / 10 := by norm_num
  rw [hcoef] at hbound
  -- `T ≤ ‖(1-ρ)𝓛‖`
  have him : ((1 - z.2) * (Real.log q : ℂ)).im = -z.2.im * Real.log q := by
    simp only [Complex.mul_im, Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im,
      Complex.ofReal_re, Complex.ofReal_im, sub_zero, zero_mul, mul_zero, neg_mul]
    ring
  have hTn : |z.2.im| * Real.log q ≤ ‖(1 - z.2) * (Real.log q : ℂ)‖ := by
    have h := Complex.abs_im_le_norm ((1 - z.2) * (Real.log q : ℂ))
    have h' : |((1 - z.2) * (Real.log q : ℂ)).im| = |z.2.im| * Real.log q := by
      rw [him, abs_mul, abs_neg, abs_of_pos hlog]
    rwa [h'] at h
  have hD2pos : 0 < ‖(1 - z.2) * (Real.log q : ℂ)‖ ^ 2 :=
    pow_pos (lt_of_lt_of_le hTpos hTn) 2
  have hnum : 0 ≤ 4 * ((zeroMult z.1 z.2 : ℝ) * Real.exp (-(49 / 10) * lamOf q z.2)) := by
    positivity
  calc (zeroMult z.1 z.2 : ℝ) * ‖Hk (11 / 2) (3 / 10) ((1 - z.2) * (Real.log q : ℂ))‖
      ≤ (zeroMult z.1 z.2 : ℝ)
          * (4 * Real.exp (-(49 / 10) * lamOf q z.2)
              / ‖(1 - z.2) * (Real.log q : ℂ)‖ ^ 2) :=
        mul_le_mul_of_nonneg_left hbound (Nat.cast_nonneg _)
    _ = 4 * ((zeroMult z.1 z.2 : ℝ) * Real.exp (-(49 / 10) * lamOf q z.2))
          / ‖(1 - z.2) * (Real.log q : ℂ)‖ ^ 2 := by ring
    _ ≤ 4 * ((zeroMult z.1 z.2 : ℝ) * Real.exp (-(49 / 10) * lamOf q z.2))
          / (|z.2.im| * Real.log q) ^ 2 := by
        rw [div_le_div_iff₀ hD2pos (pow_pos hTpos 2)]
        nlinarith [hnum, pow_le_pow_left₀ hTpos.le hTn 2]

/-- **Abel summation in `lam` for a finite set of zero-pairs of bounded height.**  If the
`lam1`-saving height-density count `pairCountHeight χ₁ β₁ t T ≤ C·lam1·e^{ct}·T^{c'}` holds
(`c < 49/10`), then the exponentially weighted multiplicity sum over a finite set of
zero-pairs of height `≤ T₀` is `≤ C·lam1·D·T₀^{c'}` with the explicit constant
`D = e^{max c 0}/(1 - e^{max c 0 - 49/10})`. -/
lemma abel_lam {q : ℕ} [NeZero q] (hq : 1 < q) (χ₁ : DirichletCharacter ℂ q) (β₁ : ℂ)
    {C c c' lam1 : ℝ} (hC : 0 < C) (hlam1 : 0 < lam1) (hc : c < 49 / 10)
    (hcnt : ∀ t T : ℝ, 0 < t → t ≤ Real.log q → 1 ≤ T →
        Siegel.pairCountHeight χ₁ β₁ t T ≤ C * lam1 * Real.exp (c * t) * T ^ c')
    {T₀ : ℝ} (hT₀ : 1 ≤ T₀)
    (S : Finset (DirichletCharacter ℂ q × ℂ))
    (hzm : ∀ z ∈ S, zeroMult z.1 z.2 ≠ 0)
    (hexc : ∀ z ∈ S, ¬(z.1 = χ₁ ∧ z.2 = β₁))
    (him : ∀ z ∈ S, |z.2.im| * Real.log q ≤ T₀) :
    (∑ z ∈ S, (zeroMult z.1 z.2 : ℝ) * Real.exp (-(49 / 10) * lamOf q z.2))
      ≤ C * lam1 * (Real.exp (max c 0) * (1 - Real.exp (max c 0 - 49 / 10))⁻¹) * T₀ ^ c' := by
  have hlog : 0 < Real.log q := Real.log_pos (by exact_mod_cast hq)
  set cs : ℝ := max c 0 with hcsdef
  have hcs0 : 0 ≤ cs := le_max_right _ _
  have hcslt : cs < 49 / 10 := max_lt hc (by norm_num)
  have hr0 : 0 ≤ Real.exp (cs - 49 / 10) := Real.exp_nonneg _
  have hr1 : Real.exp (cs - 49 / 10) < 1 := Real.exp_lt_one_iff.mpr (by linarith only [hcslt])
  set K : ℕ := Nat.ceil (Real.log q) + 1 with hKdef
  have hlam0 : ∀ z ∈ S, 0 < lamOf q z.2 := fun z hz => by
    have h1 : z.2.re < 1 := boxMaxZeroAux.zeroMult_re_lt_one z.1 (hzm z hz)
    rw [lamOf]; exact mul_pos (by linarith only [h1]) hlog
  have hlamlt : ∀ z ∈ S, lamOf q z.2 < Real.log q := fun z hz => by
    have h1 : 0 < z.2.re := zeroMult_re_pos z.1 (hzm z hz)
    rw [lamOf]
    have h2 : 1 - z.2.re < 1 := by linarith only [h1]
    calc (1 - z.2.re) * Real.log q < 1 * Real.log q :=
          mul_lt_mul_of_pos_right h2 hlog
      _ = Real.log q := by ring
  have hgmem : ∀ z ∈ S, Nat.floor (lamOf q z.2) ∈ Finset.range K := by
    intro z hz
    rw [Finset.mem_range]
    have h1 : (Nat.floor (lamOf q z.2) : ℝ) ≤ lamOf q z.2 :=
      Nat.floor_le (le_of_lt (hlam0 z hz))
    have h2 : (Nat.floor (lamOf q z.2) : ℝ) < (Nat.ceil (Real.log q) : ℝ) := by
      have h3 : lamOf q z.2 < (Nat.ceil (Real.log q) : ℝ) :=
        lt_of_lt_of_le (hlamlt z hz) (Nat.le_ceil _)
      linarith only [h1, h3]
    have h4 : Nat.floor (lamOf q z.2) < Nat.ceil (Real.log q) := Nat.cast_lt.mp h2
    rw [hKdef]; omega
  rw [← Finset.sum_fiberwise_of_maps_to hgmem
    (fun z => (zeroMult z.1 z.2 : ℝ) * Real.exp (-(49 / 10) * lamOf q z.2))]
  have hfib : ∀ k ∈ Finset.range K,
      (∑ z ∈ S.filter (fun z => Nat.floor (lamOf q z.2) = k),
          (zeroMult z.1 z.2 : ℝ) * Real.exp (-(49 / 10) * lamOf q z.2))
      ≤ C * lam1 * T₀ ^ c' * (Real.exp (-(49 / 10) * k)
          * Real.exp (c * min ((k : ℝ) + 1) (Real.log q))) := by
    intro k hk
    have htk_pos : 0 < min ((k : ℝ) + 1) (Real.log q) :=
      lt_min (by positivity) hlog
    have htk_le : min ((k : ℝ) + 1) (Real.log q) ≤ Real.log q := min_le_right _ _
    have hstep1 : (∑ z ∈ S.filter (fun z => Nat.floor (lamOf q z.2) = k),
          (zeroMult z.1 z.2 : ℝ) * Real.exp (-(49 / 10) * lamOf q z.2))
        ≤ Real.exp (-(49 / 10) * k) * (∑ z ∈ S.filter (fun z => Nat.floor (lamOf q z.2) = k),
            (zeroMult z.1 z.2 : ℝ)) := by
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum (fun z hz => ?_)
      have hzf : z ∈ S := (Finset.mem_filter.mp hz).1
      have hgk : Nat.floor (lamOf q z.2) = k := (Finset.mem_filter.mp hz).2
      have hkl : (k : ℝ) ≤ lamOf q z.2 := by
        rw [← hgk]; exact Nat.floor_le (le_of_lt (hlam0 z hzf))
      have hexp : Real.exp (-(49 / 10) * lamOf q z.2) ≤ Real.exp (-(49 / 10) * k) := by
        rw [Real.exp_le_exp]; linarith only [hkl]
      calc (zeroMult z.1 z.2 : ℝ) * Real.exp (-(49 / 10) * lamOf q z.2)
          ≤ (zeroMult z.1 z.2 : ℝ) * Real.exp (-(49 / 10) * k) :=
            mul_le_mul_of_nonneg_left hexp (Nat.cast_nonneg _)
        _ = Real.exp (-(49 / 10) * k) * (zeroMult z.1 z.2 : ℝ) := by ring
    have hstep2 : (∑ z ∈ S.filter (fun z => Nat.floor (lamOf q z.2) = k),
            (zeroMult z.1 z.2 : ℝ))
        ≤ Siegel.pairCountHeight χ₁ β₁ (min ((k : ℝ) + 1) (Real.log q)) T₀ := by
      refine pairCountHeight_dom hq χ₁ β₁ _ ?_ ?_ ?_ ?_
      · intro z hz; exact hzm z (Finset.mem_filter.mp hz).1
      · intro z hz
        have hzf := (Finset.mem_filter.mp hz).1
        have hgk := (Finset.mem_filter.mp hz).2
        have h1 : lamOf q z.2 < (k : ℝ) + 1 := by
          have hh := Nat.lt_floor_add_one (lamOf q z.2)
          rw [hgk] at hh; push_cast at hh ⊢; linarith only [hh]
        exact le_min h1.le (le_of_lt (hlamlt z hzf))
      · intro z hz; exact him z (Finset.mem_filter.mp hz).1
      · intro z hz; exact hexc z (Finset.mem_filter.mp hz).1
    have hstep3 : Siegel.pairCountHeight χ₁ β₁ (min ((k : ℝ) + 1) (Real.log q)) T₀
        ≤ C * lam1 * Real.exp (c * min ((k : ℝ) + 1) (Real.log q)) * T₀ ^ c' :=
      hcnt _ T₀ htk_pos htk_le hT₀
    calc (∑ z ∈ S.filter (fun z => Nat.floor (lamOf q z.2) = k),
          (zeroMult z.1 z.2 : ℝ) * Real.exp (-(49 / 10) * lamOf q z.2))
        ≤ Real.exp (-(49 / 10) * k) * (∑ z ∈ S.filter (fun z => Nat.floor (lamOf q z.2) = k),
            (zeroMult z.1 z.2 : ℝ)) := hstep1
      _ ≤ Real.exp (-(49 / 10) * k)
            * (C * lam1 * Real.exp (c * min ((k : ℝ) + 1) (Real.log q)) * T₀ ^ c') :=
          mul_le_mul_of_nonneg_left (le_trans hstep2 hstep3) (Real.exp_nonneg _)
      _ = C * lam1 * T₀ ^ c' * (Real.exp (-(49 / 10) * k)
            * Real.exp (c * min ((k : ℝ) + 1) (Real.log q))) := by ring
  have hterm : ∀ k ∈ Finset.range K,
      Real.exp (-(49 / 10) * k) * Real.exp (c * min ((k : ℝ) + 1) (Real.log q))
        ≤ Real.exp cs * (Real.exp (cs - 49 / 10)) ^ k := by
    intro k hk
    have htk_nonneg : 0 ≤ min ((k : ℝ) + 1) (Real.log q) :=
      le_of_lt (lt_min (by positivity) hlog)
    have htk_le' : min ((k : ℝ) + 1) (Real.log q) ≤ (k : ℝ) + 1 := min_le_left _ _
    have hkey : c * min ((k : ℝ) + 1) (Real.log q) ≤ cs * ((k : ℝ) + 1) := by
      rcases lt_or_ge 0 c with hc0 | hc0
      · have hcs_eq : cs = c := max_eq_left (le_of_lt hc0)
        rw [hcs_eq]
        exact mul_le_mul_of_nonneg_left htk_le' (le_of_lt hc0)
      · have hcs_eq : cs = 0 := max_eq_right hc0
        rw [hcs_eq, zero_mul]
        exact mul_nonpos_of_nonpos_of_nonneg hc0 htk_nonneg
    have hpow : Real.exp cs * (Real.exp (cs - 49 / 10)) ^ k
        = Real.exp (cs + ((k : ℝ) * (cs - 49 / 10))) := by
      rw [← Real.exp_nat_mul, ← Real.exp_add]
    rw [hpow, ← Real.exp_add, Real.exp_le_exp]
    linarith only [hkey]
  have hsum : (∑ k ∈ Finset.range K, Real.exp (-(49 / 10) * k)
        * Real.exp (c * min ((k : ℝ) + 1) (Real.log q)))
      ≤ Real.exp cs * (1 - Real.exp (cs - 49 / 10))⁻¹ := by
    calc (∑ k ∈ Finset.range K, Real.exp (-(49 / 10) * k)
            * Real.exp (c * min ((k : ℝ) + 1) (Real.log q)))
        ≤ ∑ k ∈ Finset.range K, Real.exp cs * (Real.exp (cs - 49 / 10)) ^ k :=
          Finset.sum_le_sum hterm
      _ = Real.exp cs * ∑ k ∈ Finset.range K, (Real.exp (cs - 49 / 10)) ^ k := by
          rw [Finset.mul_sum]
      _ ≤ Real.exp cs * (1 - Real.exp (cs - 49 / 10))⁻¹ := by
          refine mul_le_mul_of_nonneg_left ?_ (Real.exp_nonneg _)
          rw [← tsum_geometric_of_lt_one hr0 hr1]
          exact Summable.sum_le_tsum (Finset.range K) (fun i _ => by positivity)
            (summable_geometric_of_lt_one hr0 hr1)
  calc (∑ k ∈ Finset.range K, ∑ z ∈ S.filter (fun z => Nat.floor (lamOf q z.2) = k),
          (zeroMult z.1 z.2 : ℝ) * Real.exp (-(49 / 10) * lamOf q z.2))
      ≤ ∑ k ∈ Finset.range K, C * lam1 * T₀ ^ c' * (Real.exp (-(49 / 10) * k)
          * Real.exp (c * min ((k : ℝ) + 1) (Real.log q))) := Finset.sum_le_sum hfib
    _ = C * lam1 * T₀ ^ c' * ∑ k ∈ Finset.range K, (Real.exp (-(49 / 10) * k)
          * Real.exp (c * min ((k : ℝ) + 1) (Real.log q))) := by rw [Finset.mul_sum]
    _ ≤ C * lam1 * T₀ ^ c' * (Real.exp cs * (1 - Real.exp (cs - 49 / 10))⁻¹) :=
        mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = C * lam1 * (Real.exp (max c 0) * (1 - Real.exp (max c 0 - 49 / 10))⁻¹) * T₀ ^ c' := by
        rw [← hcsdef]
        ring



/-- Dyadic rpow bookkeeping: `(4^j)^{-1}·2^{j c'} = (2^{c'-2})^j`. -/
private lemma dyadic_key (c' : ℝ) (j : ℕ) :
    ((4 : ℝ) ^ j)⁻¹ * (2 : ℝ) ^ ((j : ℝ) * c') = ((2 : ℝ) ^ (c' - 2)) ^ j := by
  rw [show ((4 : ℝ) ^ j)⁻¹ = ((2 : ℝ) ^ (2 * (j : ℝ)))⁻¹ by
        rw [show (4 : ℝ) ^ j = (2 : ℝ) ^ (2 * (j : ℝ)) by
              rw [show (4 : ℝ) = (2 : ℝ) ^ 2 by norm_num, ← pow_mul,
                ← Real.rpow_natCast 2 (2 * j)]
              push_cast; ring]]
  rw [← Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2),
    ← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
  rw [show -(2 * (j : ℝ)) + (j : ℝ) * c' = (c' - 2) * (j : ℝ) by ring]
  rw [Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2), Real.rpow_natCast]

/-- The dyadic height layer index of a pair, `⌊log₂ ⌊|Im ρ|⌋⌋`. -/
private noncomputable def jj {q : ℕ} (z : DirichletCharacter ℂ q × ℂ) : ℕ :=
  Nat.log 2 (Nat.floor |z.2.im|)

/-- **The high-zero (`|Im ρ| > 1`) mass of a finite set of zero-pairs.**  With the `lam1`-saving
height-density count `pairCountHeight ≤ C·lam1·e^{ct}·T^{c'}` (`c < 49/10`, `c' < 2`) the kernel
sum over the high zeros is `≤ 4·C·lam1·D·2^{c'}·(1-2^{c'-2})^{-1}·(log q)^{c'-2}` with
`D = e^{max c 0}·(1 - e^{max c 0 - 49/10})^{-1}`, which has the required power saving
`(log q)^{c'-2}`. -/
lemma high_finset_bound {q : ℕ} [NeZero q] (hq : 1 < q) (χ₁ : DirichletCharacter ℂ q) (β₁ : ℂ)
    {C c c' lam1 : ℝ} (hC : 0 < C) (hlam1 : 0 < lam1) (hc : c < 49 / 10) (hc' : c' < 2)
    (hcnt : ∀ t T : ℝ, 0 < t → t ≤ Real.log q → 1 ≤ T →
        Siegel.pairCountHeight χ₁ β₁ t T ≤ C * lam1 * Real.exp (c * t) * T ^ c')
    (S : Finset (DirichletCharacter ℂ q × ℂ))
    (hzm : ∀ z ∈ S, zeroMult z.1 z.2 ≠ 0)
    (hhigh : ∀ z ∈ S, 1 < |z.2.im|)
    (hexc : ∀ z ∈ S, ¬(z.1 = χ₁ ∧ z.2 = β₁)) :
    (∑ z ∈ S, (zeroMult z.1 z.2 : ℝ)
        * ‖Hk (11 / 2) (3 / 10) ((1 - z.2) * (Real.log q : ℂ))‖)
      ≤ 4 * C * lam1 * (Real.exp (max c 0) * (1 - Real.exp (max c 0 - 49 / 10))⁻¹)
          * ((2 : ℝ) ^ c' * (1 - (2 : ℝ) ^ (c' - 2))⁻¹) * (Real.log q) ^ (c' - 2) := by
  have hlog : 0 < Real.log q := Real.log_pos (by exact_mod_cast hq)
  have hlogq1 : 1 ≤ 2 * Real.log q := by
    have h1 : Real.log 2 ≤ Real.log q := Real.log_le_log (by norm_num) (by exact_mod_cast hq)
    have h2 : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
    linarith only [hlog, h1, h2]
  have hrm : (2 : ℝ) ^ (c' - 2) < 1 := by
    have h1 : 1 < (2 : ℝ) ^ (2 - c') := Real.one_lt_rpow (by norm_num) (by linarith only [hc'])
    rw [show c' - 2 = -(2 - c') by ring, Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)]
    exact inv_lt_one_of_one_lt₀ h1
  have hrm0 : 0 ≤ (2 : ℝ) ^ (c' - 2) := Real.rpow_nonneg (by norm_num) _
  set D : ℝ := Real.exp (max c 0) * (1 - Real.exp (max c 0 - 49 / 10))⁻¹ with hDdef
  have hD0 : 0 ≤ D := by
    rw [hDdef]
    have h1 : Real.exp (max c 0 - 49 / 10) < 1 := Real.exp_lt_one_iff.mpr (by
      have := max_lt hc (by norm_num : (0 : ℝ) < 49 / 10); linarith only [this])
    positivity
  -- step 1: kernel bound
  have hker : (∑ z ∈ S, (zeroMult z.1 z.2 : ℝ)
        * ‖Hk (11 / 2) (3 / 10) ((1 - z.2) * (Real.log q : ℂ))‖)
      ≤ ∑ z ∈ S, 4 * ((zeroMult z.1 z.2 : ℝ) * Real.exp (-(49 / 10) * lamOf q z.2))
          / (|z.2.im| * Real.log q) ^ 2 :=
    Finset.sum_le_sum (fun z hz => high_kernel_le hq z (hzm z hz) (hhigh z hz))
  -- step 2: per-z bound `4w/(|Im|logq)² ≤ (4/log²q)·(w·(4^{jj})^{-1})`
  have hstep : (∑ z ∈ S, 4 * ((zeroMult z.1 z.2 : ℝ) * Real.exp (-(49 / 10) * lamOf q z.2))
          / (|z.2.im| * Real.log q) ^ 2)
      ≤ (4 / (Real.log q) ^ 2) * ∑ z ∈ S,
          ((zeroMult z.1 z.2 : ℝ) * Real.exp (-(49 / 10) * lamOf q z.2))
            * ((4 : ℝ) ^ (jj z))⁻¹ := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum (fun z hz => ?_)
    have him1 : 1 < |z.2.im| := hhigh z hz
    have hw0 : 0 ≤ (zeroMult z.1 z.2 : ℝ) * Real.exp (-(49 / 10) * lamOf q z.2) := by positivity
    have h4 : (4 : ℝ) ^ (jj z) ≤ |z.2.im| ^ 2 := by
      have hle : (2 : ℝ) ^ (jj z) ≤ |z.2.im| := by
        have hn1 : 1 ≤ Nat.floor |z.2.im| := Nat.floor_pos.mpr him1.le
        have hn : Nat.floor |z.2.im| ≠ 0 := by omega
        have hh := Nat.pow_log_le_self 2 hn
        have h1 : (2 : ℝ) ^ (jj z) ≤ (Nat.floor |z.2.im| : ℝ) := by
          have h2 : (((2:ℕ) ^ Nat.log 2 (Nat.floor |z.2.im|) : ℕ) : ℝ)
              ≤ (Nat.floor |z.2.im| : ℝ) := Nat.cast_le.mpr hh
          push_cast at h2
          simpa [jj] using h2
        have h3 : (Nat.floor |z.2.im| : ℝ) ≤ |z.2.im| := Nat.floor_le (abs_nonneg _)
        linarith only [h1, h3]
      have h3 : (4 : ℝ) ^ (jj z) = ((2 : ℝ) ^ (jj z)) ^ 2 := by
        rw [show (4 : ℝ) = (2 : ℝ) ^ 2 by norm_num]
        exact (pow_mul (2 : ℝ) 2 (jj z)).symm.trans (pow_mul' (2 : ℝ) 2 (jj z))
      rw [h3]
      exact pow_le_pow_left₀ (by positivity) hle 2
    have hpos : 0 < (4 : ℝ) ^ (jj z) * (Real.log q) ^ 2 := by positivity
    have hle2 : (4 : ℝ) ^ (jj z) * (Real.log q) ^ 2 ≤ |z.2.im| ^ 2 * (Real.log q) ^ 2 :=
      mul_le_mul_of_nonneg_right h4 (by positivity)
    calc 4 * ((zeroMult z.1 z.2 : ℝ) * Real.exp (-(49 / 10) * lamOf q z.2))
            / (|z.2.im| * Real.log q) ^ 2
        = 4 * ((zeroMult z.1 z.2 : ℝ) * Real.exp (-(49 / 10) * lamOf q z.2))
            / (|z.2.im| ^ 2 * (Real.log q) ^ 2) := by rw [mul_pow]
      _ ≤ 4 * ((zeroMult z.1 z.2 : ℝ) * Real.exp (-(49 / 10) * lamOf q z.2))
            / ((4 : ℝ) ^ (jj z) * (Real.log q) ^ 2) :=
          div_le_div_of_nonneg_left (by positivity) hpos hle2
      _ = (4 / (Real.log q) ^ 2) * (((zeroMult z.1 z.2 : ℝ)
              * Real.exp (-(49 / 10) * lamOf q z.2)) * ((4 : ℝ) ^ (jj z))⁻¹) := by
          field_simp
  refine le_trans hker (le_trans hstep ?_)
  rw [← Finset.sum_fiberwise_of_maps_to (fun z hz => Finset.mem_image_of_mem jj hz)
        (fun z => ((zeroMult z.1 z.2 : ℝ) * Real.exp (-(49 / 10) * lamOf q z.2))
            * ((4 : ℝ) ^ (jj z))⁻¹)]
  have hperj : ∀ j : ℕ,
      ((4 : ℝ) ^ j)⁻¹ * (C * lam1 * D * (((2 : ℝ) ^ (j + 1) * Real.log q) ^ c'))
        = C * lam1 * D * 2 ^ c' * (Real.log q) ^ c' * ((2 : ℝ) ^ (c' - 2)) ^ j := by
    intro j
    rw [Real.mul_rpow (by positivity) hlog.le,
      show (((2 : ℝ) ^ (j + 1)) ^ c') = (2 : ℝ) ^ (((j + 1 : ℕ) : ℝ) * c') by
        rw [← Real.rpow_natCast 2 (j + 1), Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)],
      show ((j + 1 : ℕ) : ℝ) * c' = ((j : ℝ) * c' + c') by push_cast; ring,
      Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
    rw [show ((4 : ℝ) ^ j)⁻¹
          * (C * lam1 * D * ((2 : ℝ) ^ ((j : ℝ) * c') * (2 : ℝ) ^ c' * (Real.log q) ^ c'))
        = C * lam1 * D * 2 ^ c' * (Real.log q) ^ c'
          * (((4 : ℝ) ^ j)⁻¹ * (2 : ℝ) ^ ((j : ℝ) * c')) by ring]
    rw [dyadic_key]
  have hfib : ∀ j ∈ S.image jj,
      (∑ z ∈ S.filter (fun z => jj z = j),
          ((zeroMult z.1 z.2 : ℝ) * Real.exp (-(49 / 10) * lamOf q z.2))
            * ((4 : ℝ) ^ (jj z))⁻¹)
      ≤ C * lam1 * D * 2 ^ c' * (Real.log q) ^ c' * ((2 : ℝ) ^ (c' - 2)) ^ j := by
    intro j hj
    have hT0 : 1 ≤ (2 : ℝ) ^ (j + 1) * Real.log q := by
      have h2 : (2 : ℝ) ≤ (2 : ℝ) ^ (j + 1) := by
        calc (2 : ℝ) = (2 : ℝ) ^ 1 := by ring
          _ ≤ (2 : ℝ) ^ (j + 1) := pow_le_pow_right₀ (by norm_num) (by omega)
      nlinarith only [hlogq1, h2, hlog]
    have him : ∀ z ∈ S.filter (fun z => jj z = j),
        |z.2.im| * Real.log q ≤ (2 : ℝ) ^ (j + 1) * Real.log q := by
      intro z hz
      have hzf : z ∈ S := (Finset.mem_filter.mp hz).1
      have hjeq : jj z = j := (Finset.mem_filter.mp hz).2
      have him1 : 1 < |z.2.im| := hhigh z hzf
      have hlt : |z.2.im| < (2 : ℝ) ^ (j + 1) := by
        have h1 : Nat.floor |z.2.im| < 2 ^ (Nat.log 2 (Nat.floor |z.2.im|) + 1) :=
          Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) (Nat.floor |z.2.im|)
        have hjeq' : Nat.log 2 (Nat.floor |z.2.im|) = j := hjeq
        rw [hjeq'] at h1
        have h2 : (Nat.floor |z.2.im| : ℝ) + 1 ≤ (2 : ℝ) ^ (j + 1) := by
          have h3 : Nat.floor |z.2.im| + 1 ≤ 2 ^ (j + 1) := h1
          exact_mod_cast h3
        have h4 : |z.2.im| < (Nat.floor |z.2.im| : ℝ) + 1 := Nat.lt_floor_add_one _
        linarith only [h2, h4]
      exact mul_le_mul_of_nonneg_right hlt.le hlog.le
    have habel := abel_lam hq χ₁ β₁ hC hlam1 hc hcnt hT0
      (S.filter (fun z => jj z = j))
      (fun z hz => hzm z (Finset.mem_filter.mp hz).1)
      (fun z hz => hexc z (Finset.mem_filter.mp hz).1) him
    calc (∑ z ∈ S.filter (fun z => jj z = j),
          ((zeroMult z.1 z.2 : ℝ) * Real.exp (-(49 / 10) * lamOf q z.2))
            * ((4 : ℝ) ^ (jj z))⁻¹)
        = (∑ z ∈ S.filter (fun z => jj z = j),
            ((zeroMult z.1 z.2 : ℝ) * Real.exp (-(49 / 10) * lamOf q z.2))
              * ((4 : ℝ) ^ j)⁻¹) := by
          refine Finset.sum_congr rfl (fun z hz => ?_)
          rw [(Finset.mem_filter.mp hz).2]
      _ = ((4 : ℝ) ^ j)⁻¹ * (∑ z ∈ S.filter (fun z => jj z = j),
            ((zeroMult z.1 z.2 : ℝ) * Real.exp (-(49 / 10) * lamOf q z.2))) := by
          rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun z _ => by ring)
      _ ≤ ((4 : ℝ) ^ j)⁻¹ * (C * lam1 * D * (((2 : ℝ) ^ (j + 1) * Real.log q) ^ c')) :=
          mul_le_mul_of_nonneg_left habel (by positivity)
      _ = C * lam1 * D * 2 ^ c' * (Real.log q) ^ c' * ((2 : ℝ) ^ (c' - 2)) ^ j := hperj j
  have hmid : (∑ j ∈ S.image jj, ∑ z ∈ S.filter (fun z => jj z = j),
        ((zeroMult z.1 z.2 : ℝ) * Real.exp (-(49 / 10) * lamOf q z.2))
          * ((4 : ℝ) ^ (jj z))⁻¹)
      ≤ C * lam1 * D * 2 ^ c' * (Real.log q) ^ c' * (1 - (2 : ℝ) ^ (c' - 2))⁻¹ := by
    refine le_trans (Finset.sum_le_sum hfib) ?_
    rw [← Finset.mul_sum]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    rw [← tsum_geometric_of_lt_one hrm0 hrm]
    exact Summable.sum_le_tsum (S.image jj) (fun i _ => by positivity)
      (summable_geometric_of_lt_one hrm0 hrm)
  have hconcl : (4 / (Real.log q) ^ 2)
        * (C * lam1 * D * 2 ^ c' * (Real.log q) ^ c' * (1 - (2 : ℝ) ^ (c' - 2))⁻¹)
      = 4 * C * lam1 * D * ((2 : ℝ) ^ c' * (1 - (2 : ℝ) ^ (c' - 2))⁻¹)
          * (Real.log q) ^ (c' - 2) := by
    have hrpow : (Real.log q) ^ c' = (Real.log q) ^ (c' - 2) * (Real.log q) ^ 2 := by
      rw [show (Real.log q) ^ 2 = (Real.log q) ^ ((2 : ℕ) : ℝ) by rw [Real.rpow_natCast],
        ← Real.rpow_add hlog]
      congr 1; ring
    rw [hrpow]
    field_simp
  exact le_trans (mul_le_mul_of_nonneg_left hmid (by positivity)) (le_of_eq hconcl)



theorem siegelRestHigh (hden : Work.LinnikAreas.Siegel.PairDensityHeightInput) :
    ∃ C : ℝ, 0 < C ∧ ∃ e : ℝ, e < 0 ∧ ∃ q₀ : ℕ,
      ∀ q : ℕ, q₀ ≤ q → ∀ [NeZero q] (χ₁ : DirichletCharacter ℂ q) (β₁ : ℝ),
      χ₁ ≠ 1 → χ₁ ^ 2 = 1 → β₁ < 1 → Work.LinnikContract.zeroMult χ₁ (β₁ : ℂ) ≠ 0 →
      Work.LinnikContract.lamOf q (β₁ : ℂ) ≤ 1 / 2 →
      Work.LinnikAreas.Siegel.restHighZeroSum χ₁ (β₁ : ℂ) (11 / 2) (3 / 10)
        ≤ C * Work.LinnikContract.lamOf q (β₁ : ℂ) * (Real.log q) ^ e := by
  obtain ⟨Ch, hChpos, c, hc, c', hc', q₀h, hcnt⟩ := hden
  have hstep : Real.exp (max c 0 - 49 / 10) < 1 := Real.exp_lt_one_iff.mpr (by
    have := max_lt hc (by norm_num : (0 : ℝ) < 49 / 10); linarith only [this])
  have hr1 : (2 : ℝ) ^ (c' - 2) < 1 := by
    have h1 : 1 < (2 : ℝ) ^ (2 - c') := Real.one_lt_rpow (by norm_num) (by linarith only [hc'])
    rw [show c' - 2 = -(2 - c') by ring, Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)]
    exact inv_lt_one_of_one_lt₀ h1
  refine ⟨4 * Ch * (Real.exp (max c 0) * (1 - Real.exp (max c 0 - 49 / 10))⁻¹)
      * ((2 : ℝ) ^ c' * (1 - (2 : ℝ) ^ (c' - 2))⁻¹), ?_, c' - 2, by linarith only [hc'], max q₀h 2, ?_⟩
  · have h1 : 0 < Real.exp (max c 0) * (1 - Real.exp (max c 0 - 49 / 10))⁻¹ := by positivity
    have h2 : 0 < (2 : ℝ) ^ c' * (1 - (2 : ℝ) ^ (c' - 2))⁻¹ := by positivity
    positivity
  · intro q hq hNq χ₁ β₁ hχ hsq hβ hz hlam
    have hq2 : 1 < q := by have h2 : 2 ≤ q := le_trans (le_max_right _ _) hq; omega
    have hq0h : q₀h ≤ q := le_trans (le_max_left _ _) hq
    have hlog : 0 < Real.log q := Real.log_pos (by exact_mod_cast hq2)
    have hb0 : 0 < β₁ := Siegel.re_mem_Ioo hχ hβ hz
    have hlam1 : 0 < lamOf q (β₁ : ℂ) := by
      rw [lamOf, Complex.ofReal_re]; exact mul_pos (by linarith only [hβ]) hlog
    have hcnt' : ∀ t T : ℝ, 0 < t → t ≤ Real.log q → 1 ≤ T →
        Siegel.pairCountHeight χ₁ (β₁ : ℂ) t T
          ≤ Ch * lamOf q (β₁ : ℂ) * Real.exp (c * t) * T ^ c' :=
      fun t T ht htT hT => hcnt q hq0h χ₁ β₁ hχ hsq hβ hz hlam t T ht htT hT
    -- the high-zero integrand of `restHighZeroSum`
    let p : DirichletCharacter ℂ q × ℂ → Prop := fun z =>
      zeroMult z.1 z.2 ≠ 0 ∧ 1 < |z.2.im| ∧ ¬(z.1 = χ₁ ∧ z.2 = (β₁ : ℂ))
    let F : DirichletCharacter ℂ q × ℂ → ℝ := fun z =>
      if p z then (zeroMult z.1 z.2 : ℝ)
          * ‖Hk (11 / 2) (3 / 10) ((1 - z.2) * (Real.log q : ℂ))‖ else 0
    have hFnn : 0 ≤ F := fun z => by
      simp only [F]; split_ifs with hp
      · exact mul_nonneg (Nat.cast_nonneg _) (norm_nonneg _)
      · exact le_refl 0
    have hFbound : ∀ u : Finset (DirichletCharacter ℂ q × ℂ), ∑ z ∈ u, F z
        ≤ 4 * Ch * (Real.exp (max c 0) * (1 - Real.exp (max c 0 - 49 / 10))⁻¹)
            * ((2 : ℝ) ^ c' * (1 - (2 : ℝ) ^ (c' - 2))⁻¹) * lamOf q (β₁ : ℂ)
            * (Real.log q) ^ (c' - 2) := by
      intro u
      have hsum_eq : ∑ z ∈ u, F z = ∑ z ∈ u.filter p, F z := by
        refine (Finset.sum_subset (Finset.filter_subset _ _) ?_).symm
        intro z hz hnotin
        have hp : ¬ p z := fun hpp => hnotin (Finset.mem_filter.mpr ⟨hz, hpp⟩)
        simp only [F]; rw [if_neg hp]
      rw [hsum_eq]
      have hSF : ∑ z ∈ u.filter p, F z
          = ∑ z ∈ u.filter p, (zeroMult z.1 z.2 : ℝ)
              * ‖Hk (11 / 2) (3 / 10) ((1 - z.2) * (Real.log q : ℂ))‖ := by
        refine Finset.sum_congr rfl (fun z hz => ?_)
        have hp : p z := (Finset.mem_filter.mp hz).2
        simp only [F]; rw [if_pos hp]
      rw [hSF]
      have := high_finset_bound (C := Ch) (c := c) (c' := c') (lam1 := lamOf q (β₁ : ℂ))
        hq2 χ₁ (β₁ : ℂ) hChpos hlam1 hc hc' hcnt' (u.filter p)
        (fun z hz => (Finset.mem_filter.mp hz).2.1)
        (fun z hz => (Finset.mem_filter.mp hz).2.2.1)
        (fun z hz => (Finset.mem_filter.mp hz).2.2.2)
      calc ∑ z ∈ u.filter p, (zeroMult z.1 z.2 : ℝ)
            * ‖Hk (11 / 2) (3 / 10) ((1 - z.2) * (Real.log q : ℂ))‖
          ≤ 4 * Ch * lamOf q (β₁ : ℂ)
              * (Real.exp (max c 0) * (1 - Real.exp (max c 0 - 49 / 10))⁻¹)
              * ((2 : ℝ) ^ c' * (1 - (2 : ℝ) ^ (c' - 2))⁻¹)
              * (Real.log q) ^ (c' - 2) := this
        _ = 4 * Ch * (Real.exp (max c 0) * (1 - Real.exp (max c 0 - 49 / 10))⁻¹)
              * ((2 : ℝ) ^ c' * (1 - (2 : ℝ) ^ (c' - 2))⁻¹) * lamOf q (β₁ : ℂ)
              * (Real.log q) ^ (c' - 2) := by ring
    have hsumm : Summable F := summable_of_sum_le hFnn hFbound
    have htsum : ∑' z : DirichletCharacter ℂ q × ℂ, F z
        ≤ 4 * Ch * (Real.exp (max c 0) * (1 - Real.exp (max c 0 - 49 / 10))⁻¹)
            * ((2 : ℝ) ^ c' * (1 - (2 : ℝ) ^ (c' - 2))⁻¹) * lamOf q (β₁ : ℂ)
            * (Real.log q) ^ (c' - 2) :=
      Real.tsum_le_of_sum_le hFnn hFbound
    rw [Summable.tsum_prod hsumm] at htsum
    rw [tsum_fintype] at htsum
    have hEq : Siegel.restHighZeroSum χ₁ (β₁ : ℂ) (11 / 2) (3 / 10)
        = ∑ χ : DirichletCharacter ℂ q, ∑' ρ : ℂ, F (χ, ρ) := rfl
    rw [hEq]
    exact htsum


end Work.LinnikAreas
