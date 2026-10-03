/-
# `Submission.Work.FIArea7CF.holder6_boundB` — clash-free copy of `Submission.Work.FIArea7.Pub213.holder6_bound`

Imports redirected to the `FIArea7CF` copies; renamed: gnorm_mk_eq→cfx_gnorm_mk_eq, mem_gBox_iff→r2c_mem_gBox_iff.  The workspace contains several
incompatible declarations of `Work.FIArea7.mem_gBox_iff` (and of `norm_uniCoeff_le`,
`log_pow_le_rpow`, `gnorm_mk_eq`), so the amended area-7 assembly and the *FI* §§19–26
chain can only meet through copies.  See NOTES §63.
-/
import Mathlib
import Submission.Work.FIArea7.Pub213.Defs
import Submission.Work.FIArea7.Pub213.Prop213Pub
import Submission.Work.FIArea7.dirichletSym_mul
import Submission.Work.FIArea7.FIsymbols
import Submission.Work.FIArea7.Classical172Defs
import Submission.Commons.NumberTheory.GaussianInt.two_squares_repr_count_le_tau_of_pos
import Submission.Work.FIArea7.R2_bound
import Submission.Work.FIArea7.cardDiscBoxLe
import Submission.Work.FIArea7.sum_tau_pow_le
import Submission.Work.FIArea7CF.meanSquareElem
import Submission.Work.FIArea7.Pub213.Arith
import Submission.Work.FIArea7CF.Conv6Defs
import Submission.Work.FIArea7CF.qBilinDefs
import Submission.Work.FIArea7CF.qBilin_holder6
import Submission.Work.FIArea7CF.r2count_upper
import Submission.Work.FIArea7CF.R2countDefs
import Submission.Work.FIArea7CF.sum_gnorm_fiber_le
import Submission.Work.FIArea7CF.tupCount_le_tau

set_option maxHeartbeats 1600000
set_option autoImplicit false

namespace Work.FIArea7.Pub213

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

lemma mem_boxTup6 {R : ℤ} {t : Fin 6 → GaussianInt} :
    t ∈ Work.FIArea7.boxTup 6 R ↔ ∀ i : Fin 6, t i ∈ Work.FIPlan.gBox R := by
  rw [Work.FIArea7.boxTup, Fintype.mem_piFinset]

/-! ## The sixfold convolution is dominated by a tuple count -/

/-- `‖(conv6 R β) u‖` is at most the number of six-tuples of box elements of nonzero norm `≤ N`
with product `u`, when `β` vanishes on `0` and outside the disc `|z|² ≤ N`. -/
lemma conv6_norm_le_tupCount {R : ℤ} {N : ℝ} {β : GaussianInt → ℂ}
    (hβ1 : ∀ z, ‖β z‖ ≤ 1) (hβN : ∀ z, β z ≠ 0 → (Work.FIPlan.gnorm z : ℝ) ≤ N)
    (hβ0 : ∀ z, β z ≠ 0 → z ≠ 0) (u : GaussianInt) :
    ‖Work.FIArea7.conv6 R β u‖ ≤ (tupCount R N u : ℝ) := by
  classical
  set g : (Fin 6 → GaussianInt) → ℂ :=
    fun t => if Work.FIArea7.tupProd t = u then ∏ i : Fin 6, β (t i) else 0 with hg
  have hpoint : ∀ t ∈ Work.FIArea7.boxTup 6 R, ‖g t‖ ≤ 1 := by
    intro t _
    simp only [hg]
    by_cases h : Work.FIArea7.tupProd t = u
    · rw [if_pos h, norm_prod]
      calc ∏ i : Fin 6, ‖β (t i)‖ ≤ ∏ _i : Fin 6, (1 : ℝ) :=
            Finset.prod_le_prod₀ (fun i _ => norm_nonneg _) (fun i _ => hβ1 (t i))
        _ = 1 := by simp
    · rw [if_neg h]; simp
  have hsupp : ∀ t ∈ Work.FIArea7.boxTup 6 R, g t ≠ 0 →
      t ∈ (nzTup R N).filter (fun t => Work.FIArea7.tupProd t = u) := by
    intro t ht hne
    rw [Finset.mem_filter, mem_nzTup]
    have htu : Work.FIArea7.tupProd t = u := by
      by_contra hc
      simp only [hg, if_neg hc] at hne
      exact hne rfl
    refine ⟨fun i => ?_, htu⟩
    have hβi : β (t i) ≠ 0 := by
      intro h0
      apply hne
      simp only [hg, if_pos htu]
      exact Finset.prod_eq_zero (Finset.mem_univ i) h0
    have hmem : t i ∈ Work.FIPlan.gBox R := (mem_boxTup6.mp ht) i
    rw [mem_nzBox]
    exact ⟨hmem, Work.FIArea7.gnorm_pos_of_ne_zero (hβ0 _ hβi), hβN _ hβi⟩
  have hstep1 : ∑ t ∈ (Work.FIArea7.boxTup 6 R).filter (fun t => g t ≠ 0), ‖g t‖
      = ∑ t ∈ Work.FIArea7.boxTup 6 R, ‖g t‖ := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun t _ => ?_
    by_cases h : g t = 0
    · rw [if_neg (by simp [h]), h]; simp
    · rw [if_pos h]
  calc ‖Work.FIArea7.conv6 R β u‖
      ≤ ∑ t ∈ Work.FIArea7.boxTup 6 R, ‖g t‖ := by
        rw [Work.FIArea7.conv6]
        refine le_trans (norm_sum_le _ _) ?_
        exact le_of_eq (Finset.sum_congr rfl fun t _ => by simp only [hg])
    _ = ∑ t ∈ (Work.FIArea7.boxTup 6 R).filter (fun t => g t ≠ 0), ‖g t‖ := hstep1.symm
    _ ≤ ∑ t ∈ (Work.FIArea7.boxTup 6 R).filter (fun t => g t ≠ 0), (1 : ℝ) :=
        Finset.sum_le_sum fun t ht => hpoint t (Finset.mem_filter.mp ht).1
    _ = (((Work.FIArea7.boxTup 6 R).filter (fun t => g t ≠ 0)).card : ℝ) := by simp
    _ ≤ (((nzTup R N).filter (fun t => Work.FIArea7.tupProd t = u)).card : ℝ) := by
        exact_mod_cast Finset.card_le_card fun t ht =>
          hsupp t (Finset.mem_filter.mp ht).1 (Finset.mem_filter.mp ht).2
    _ = (tupCount R N u : ℝ) := rfl

/-! ## The `ℓ²` bound for the sixfold convolution -/

/-- `r₂(M) ≤ 4 τ(M)`: the number of Gaussian integers of norm `M` is at most four times the
number of rational divisors of `M`. -/
lemma r2count_le_four_tau (M : ℕ) (hM : 1 ≤ M) :
    (Work.FIArea7.r2count M : ℝ) ≤ 4 * (((M.divisors.card : ℕ)) : ℝ) := by
  have h1 : Work.FIArea7.r2count M ≤ 4 * M.divisors.card := by
    have h2 := Work.FIArea7.r2count_upper M (by omega)
    have h3 : (∏ p ∈ M.primeFactors.filter (fun p => p % 4 = 1), (M.factorization p + 1))
        ≤ ∏ p ∈ M.primeFactors, (M.factorization p + 1) :=
      Finset.prod_le_prod_of_subset_of_one_le' (Finset.filter_subset _ _)
        (fun p _ _ => Nat.succ_le_succ (Nat.zero_le _))
    calc Work.FIArea7.r2count M
        ≤ 4 * ∏ p ∈ M.primeFactors.filter (fun p => p % 4 = 1), (M.factorization p + 1) := h2
      _ ≤ 4 * ∏ p ∈ M.primeFactors, (M.factorization p + 1) := Nat.mul_le_mul_left 4 h3
      _ = 4 * M.divisors.card := by rw [Nat.card_divisors (by omega)]
  exact_mod_cast h1

/-- `conv6 R β 0 = 0` when `β` vanishes at `0`. -/
lemma conv6_zero_eq_zero {R : ℤ} {β : GaussianInt → ℂ} (hβ0 : ∀ z, β z ≠ 0 → z ≠ 0) :
    Work.FIArea7.conv6 R β 0 = 0 := by
  rw [Work.FIArea7.conv6, Finset.sum_eq_zero]
  intro t _
  by_cases h : Work.FIArea7.tupProd t = 0
  · rw [if_pos h]
    obtain ⟨i, -, hi⟩ := Finset.prod_eq_zero_iff.mp h
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by
      by_contra hb
      exact hβ0 (t i) hb hi)
  · rw [if_neg h]

/-- **The `ℓ²` bound for the sixfold convolution**, with the pointwise tuple-count input
abstracted.  The exponent `12` is the one supplied by `tupCount_le_tau`; the point is
`Σ_u ‖β^{(6)}(u)‖² ≤ Σ_u (tuple count)² ≤ C₀² Σ_u τ(|u|²)^24`, and the last sum is a
divisor-function moment over the disc of radius `N⁶`, estimated by `sum_tau_pow_le`. -/
theorem conv6_l2_of_count {C0 : ℝ} (hC0 : 0 < C0)
    (hcount : ∀ (R : ℤ) (N : ℝ) (u : GaussianInt), 1 ≤ N → u ≠ 0 →
      (tupCount R N u : ℝ) ≤ C0 * (((Work.FIPlan.gnorm u).divisors.card : ℕ) : ℝ) ^ 12) :
    ∃ C B : ℝ, 0 < C ∧ 0 < B ∧
      ∀ (N : ℝ) (R : ℤ) (β : GaussianInt → ℂ), 1 ≤ N →
        (∀ z, β z ≠ 0 → (Work.FIPlan.gnorm z : ℝ) ≤ N) →
        (∀ z, β z ≠ 0 → z ∈ Work.FIPlan.gBox R) →
        (∀ z, β z ≠ 0 → z ≠ 0) →
        (∀ z, ‖β z‖ ≤ 1) →
        ∑ u ∈ Work.FIArea7.gDisc ⌈N ^ 3⌉ (N ^ 6), ‖Work.FIArea7.conv6 R β u‖ ^ 2
          ≤ C * N ^ 6 * (Real.log (N + 2)) ^ B := by
  classical
  refine ⟨8 * 8 ^ (2 ^ 25 - 1) * C0 ^ 2, ((2 ^ 25 - 1 : ℕ) : ℝ), ?_, ?_, ?_⟩
  · positivity
  · have h : (0 : ℕ) < 2 ^ 25 - 1 := by norm_num
    exact_mod_cast h
  · intro N R β hN hβN hβbox hβ0 hβ1
    set U : Finset GaussianInt := Work.FIArea7.gDisc ⌈N ^ 3⌉ (N ^ 6) with hU
    set s : Finset GaussianInt := U.filter (fun u => u ≠ 0) with hs
    set Y : ℕ := ⌈N ^ 6⌉₊ with hY
    have hzero : Work.FIArea7.conv6 R β 0 = 0 := conv6_zero_eq_zero hβ0
    have hdrop : ∑ u ∈ U, ‖Work.FIArea7.conv6 R β u‖ ^ 2
        = ∑ u ∈ s, ‖Work.FIArea7.conv6 R β u‖ ^ 2 := by
      rw [hs, ← Finset.sum_filter_add_sum_filter_not U (fun u : GaussianInt => u ≠ 0)
        (fun u => ‖Work.FIArea7.conv6 R β u‖ ^ 2)]
      have hz : ∑ u ∈ U.filter (fun u : GaussianInt => ¬ u ≠ 0),
          ‖Work.FIArea7.conv6 R β u‖ ^ 2 = 0 := by
        refine Finset.sum_eq_zero fun u hu => ?_
        rw [Finset.mem_filter] at hu
        have hu0 : u = 0 := by simpa using hu.2
        rw [hu0, hzero]; simp
      rw [hz, add_zero]
    have hsne : ∀ u ∈ s, u ≠ 0 := fun u hu => by
      rw [hs, Finset.mem_filter] at hu
      exact hu.2
    have hgn : ∀ u ∈ s, (Work.FIPlan.gnorm u : ℝ) ≤ N ^ 6 := by
      intro u hu
      rw [hs, Finset.mem_filter] at hu
      rw [hU, Work.FIArea7.gDisc, Finset.mem_filter] at hu
      exact hu.1.2
    have hYmem : ∀ u ∈ s, (Work.FIPlan.gnorm u : ℝ) ≤ (Y : ℝ) := by
      intro u hu
      have h1 : (Work.FIPlan.gnorm u : ℝ) ≤ N ^ 6 := hgn u hu
      have h2 : N ^ 6 ≤ (Y : ℝ) := by
        rw [hY]; exact Nat.le_ceil _
      linarith
    -- Step 1
    have hstep2 : ∑ u ∈ s, ‖Work.FIArea7.conv6 R β u‖ ^ 2
        ≤ ∑ u ∈ s, (tupCount R N u : ℝ) ^ 2 := by
      refine Finset.sum_le_sum fun u _ => ?_
      have h1 := conv6_norm_le_tupCount (R := R) (N := N) hβ1 hβN hβ0 u
      exact pow_le_pow_left₀ (norm_nonneg _) h1 2
    -- Step 2
    have hstep3 : ∑ u ∈ s, (tupCount R N u : ℝ) ^ 2
        ≤ C0 ^ 2 * ∑ u ∈ s, (((Work.FIPlan.gnorm u).divisors.card : ℕ) : ℝ) ^ 24 := by
      have hle : ∀ u ∈ s, (tupCount R N u : ℝ) ^ 2
          ≤ C0 ^ 2 * ((((Work.FIPlan.gnorm u).divisors.card : ℕ) : ℝ) ^ 12) ^ 2 := by
        intro u hu
        have hu' : u ≠ 0 := hsne u hu
        have h1 := hcount R N u hN hu'
        have h2 : (0 : ℝ) ≤ (tupCount R N u : ℝ) := Nat.cast_nonneg _
        have h3 : (0 : ℝ) ≤ C0 * (((Work.FIPlan.gnorm u).divisors.card : ℕ) : ℝ) ^ 12 := by
          positivity
        calc (tupCount R N u : ℝ) ^ 2
            ≤ (C0 * (((Work.FIPlan.gnorm u).divisors.card : ℕ) : ℝ) ^ 12) ^ 2 :=
              pow_le_pow_left₀ h2 h1 2
          _ = C0 ^ 2 * ((((Work.FIPlan.gnorm u).divisors.card : ℕ) : ℝ) ^ 12) ^ 2 := by ring
      calc ∑ u ∈ s, (tupCount R N u : ℝ) ^ 2
          ≤ ∑ u ∈ s, C0 ^ 2 * ((((Work.FIPlan.gnorm u).divisors.card : ℕ) : ℝ) ^ 12) ^ 2 :=
            Finset.sum_le_sum hle
        _ = C0 ^ 2 * ∑ u ∈ s, ((((Work.FIPlan.gnorm u).divisors.card : ℕ) : ℝ) ^ 12) ^ 2 := by
            rw [Finset.mul_sum]
        _ = C0 ^ 2 * ∑ u ∈ s, (((Work.FIPlan.gnorm u).divisors.card : ℕ) : ℝ) ^ 24 := by
            congr 1
            refine Finset.sum_congr rfl fun u _ => ?_
            rw [← pow_mul]
    -- Step 3: group by the value of the norm
    have hstep4 : ∑ u ∈ s, (((Work.FIPlan.gnorm u).divisors.card : ℕ) : ℝ) ^ 24
        ≤ ∑ M ∈ Finset.Icc 1 Y,
            (Work.FIArea7.r2count M : ℝ) * (((M.divisors.card : ℕ) : ℝ) ^ 24) :=
      sum_gnorm_fiber_le (f := fun M => (((M.divisors.card : ℕ) : ℝ) ^ 24))
        (fun M => by positivity) Y hYmem hsne
    -- Step 4: `r₂ M ≤ 4 τ(M)`
    have hstep5 : ∑ M ∈ Finset.Icc 1 Y,
          (Work.FIArea7.r2count M : ℝ) * (((M.divisors.card : ℕ) : ℝ) ^ 24)
        ≤ 4 * ∑ M ∈ Finset.Icc 1 Y, (((M.divisors.card : ℕ) : ℝ) ^ 25) := by
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum fun M hM => ?_
      have hM1 : 1 ≤ M := (Finset.mem_Icc.mp hM).1
      have hr2 := r2count_le_four_tau M hM1
      have hτ : (0 : ℝ) ≤ ((M.divisors.card : ℕ) : ℝ) := Nat.cast_nonneg _
      calc (Work.FIArea7.r2count M : ℝ) * (((M.divisors.card : ℕ) : ℝ) ^ 24)
          ≤ (4 * ((M.divisors.card : ℕ) : ℝ)) * (((M.divisors.card : ℕ) : ℝ) ^ 24) :=
            mul_le_mul_of_nonneg_right hr2 (by positivity)
        _ = 4 * (((M.divisors.card : ℕ) : ℝ) ^ 25) := by
            rw [pow_succ]; ring
    -- Step 5: the divisor moment
    have hstep6 : ∑ M ∈ Finset.Icc 1 Y, (((M.divisors.card : ℕ) : ℝ) ^ 25)
        ≤ (Y : ℝ) * (1 + Real.log (Y : ℝ)) ^ (2 ^ 25 - 1) :=
      Work.FIArea7.sum_tau_pow_le 25 Y
    -- Step 6: the numeric and logarithmic bounds
    have hYle : (Y : ℝ) ≤ 2 * N ^ 6 := by
      rw [hY]
      have h1 : (⌈N ^ 6⌉₊ : ℝ) < N ^ 6 + 1 := Nat.ceil_lt_add_one (by positivity)
      have h2 : (1 : ℝ) ≤ N ^ 6 := one_le_pow₀ hN
      linarith
    have hlog : 1 + Real.log (Y : ℝ) ≤ 8 * Real.log (N + 2) := by
      have hNpos : (0 : ℝ) < N := by linarith
      have hYpos : (0 : ℝ) < (Y : ℝ) := by
        rw [hY]
        exact_mod_cast Nat.ceil_pos.mpr (by positivity)
      have hlogY : Real.log (Y : ℝ) ≤ Real.log (2 * N ^ 6) := Real.log_le_log hYpos hYle
      have hlog2N : Real.log (2 * N ^ 6) = Real.log 2 + 6 * Real.log N := by
        rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (pow_ne_zero 6 (by linarith : N ≠ 0)),
          Real.log_pow]
        push_cast
        ring
      rw [hlog2N] at hlogY
      have hlogN : Real.log N ≤ Real.log (N + 2) := Real.log_le_log hNpos (by linarith)
      have hlog2 : Real.log 2 ≤ Real.log (N + 2) := Real.log_le_log (by norm_num) (by linarith)
      have hlog3 : (1 : ℝ) ≤ Real.log (N + 2) := by
        have h3 : Real.log 3 ≤ Real.log (N + 2) := Real.log_le_log (by norm_num) (by linarith)
        have h1' : (1 : ℝ) ≤ Real.log 3 := by
          rw [Real.le_log_iff_exp_le (by norm_num : (0 : ℝ) < 3)]
          exact Real.exp_one_lt_three.le
        linarith
      linarith
    have hpow : (1 + Real.log (Y : ℝ)) ^ (2 ^ 25 - 1)
        ≤ (8 * Real.log (N + 2)) ^ (2 ^ 25 - 1) :=
      pow_le_pow_left₀ (by positivity) hlog _
    calc ∑ u ∈ U, ‖Work.FIArea7.conv6 R β u‖ ^ 2
        = ∑ u ∈ s, ‖Work.FIArea7.conv6 R β u‖ ^ 2 := hdrop
      _ ≤ ∑ u ∈ s, (tupCount R N u : ℝ) ^ 2 := hstep2
      _ ≤ C0 ^ 2 * ∑ u ∈ s, (((Work.FIPlan.gnorm u).divisors.card : ℕ) : ℝ) ^ 24 := hstep3
      _ ≤ C0 ^ 2 * ∑ M ∈ Finset.Icc 1 Y,
            (Work.FIArea7.r2count M : ℝ) * (((M.divisors.card : ℕ) : ℝ) ^ 24) := by
          refine mul_le_mul_of_nonneg_left hstep4 ?_
          positivity
      _ ≤ C0 ^ 2 * (4 * ∑ M ∈ Finset.Icc 1 Y, (((M.divisors.card : ℕ) : ℝ) ^ 25)) := by
          refine mul_le_mul_of_nonneg_left hstep5 ?_
          positivity
      _ ≤ C0 ^ 2 * (4 * ((Y : ℝ) * (1 + Real.log (Y : ℝ)) ^ (2 ^ 25 - 1))) := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          exact mul_le_mul_of_nonneg_left hstep6 (by norm_num)
      _ ≤ C0 ^ 2 * (4 * ((2 * N ^ 6) * (8 * Real.log (N + 2)) ^ (2 ^ 25 - 1))) := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
          exact mul_le_mul hYle hpow (by positivity) (by positivity)
      _ = 8 * 8 ^ (2 ^ 25 - 1) * C0 ^ 2 * N ^ 6
            * (Real.log (N + 2)) ^ ((2 ^ 25 - 1 : ℕ) : ℝ) := by
          rw [mul_pow, Real.rpow_natCast]
          ring

theorem conv6_l2_offzero : ∃ C B : ℝ, 0 < C ∧ 0 < B ∧
    ∀ (N : ℝ) (R : ℤ) (β : GaussianInt → ℂ), 1 ≤ N →
      (∀ z, β z ≠ 0 → (Work.FIPlan.gnorm z : ℝ) ≤ N) →
      (∀ z, β z ≠ 0 → z ∈ Work.FIPlan.gBox R) →
      (∀ z, β z ≠ 0 → z ≠ 0) →
      (∀ z, ‖β z‖ ≤ 1) →
      ∑ u ∈ Work.FIArea7.gDisc ⌈N ^ 3⌉ (N ^ 6), ‖Work.FIArea7.conv6 R β u‖ ^ 2
        ≤ C * N ^ 6 * (Real.log (N + 2)) ^ B := by
  exact conv6_l2_of_count (by norm_num : (0 : ℝ) < 4 ^ 6)
    (fun R N u hN hu => tupCount_le_tau R N u hN hu)

theorem chain6 {C1 A1 C2 B2 : ℝ} (hC1 : 0 < C1) (hA1 : 0 < A1) (hC2 : 0 < C2) (hB2 : 0 < B2)
    (hms : ∀ (M N : ℝ) (Rw : ℤ) (a : GaussianInt → ℂ), 1 ≤ M → 1 ≤ N →
      (∀ w, a w ≠ 0 → Work.FIPlan.IsPrimary w ∧ IsCoprime w.re w.im ∧ (Work.FIPlan.gnorm w : ℝ) ≤ M) →
      (∀ w, ‖a w‖ ≤ 1) →
      (∑ z ∈ Work.FIPlan.gBox (⌈Real.sqrt N⌉ : ℤ),
          ‖∑ w ∈ Work.FIPlan.gBox Rw, a w * ((DirichletSym w z : ℤ) : ℂ)‖ ^ 2)
        ≤ C1 * (N * M + M ^ 4 * Real.sqrt N + M ^ 6) * (Real.log (M * N + 2)) ^ A1)
    (hconv : ∀ (N : ℝ) (R : ℤ) (β : GaussianInt → ℂ), 1 ≤ N →
      (∀ z, β z ≠ 0 → (Work.FIPlan.gnorm z : ℝ) ≤ N) →
      (∀ z, β z ≠ 0 → z ∈ Work.FIPlan.gBox R) →
      (∀ z, β z ≠ 0 → z ≠ 0) →
      (∀ z, ‖β z‖ ≤ 1) →
      (∑ u ∈ Work.FIArea7.gDisc ⌈N ^ 3⌉ (N ^ 6), ‖Work.FIArea7.conv6 R β u‖ ^ 2)
        ≤ C2 * N ^ 6 * (Real.log (N + 2)) ^ B2)
    (M N : ℝ) (hM : 1 ≤ M) (hN : 1 ≤ N) (Rw Rz : ℤ) (α β : GaussianInt → ℂ)
    (hα1 : ∀ w, ‖α w‖ ≤ 1) (hβ1 : ∀ z, ‖β z‖ ≤ 1)
    (hαsupp : ∀ w, α w ≠ 0 → Work.FIPlan.IsPrimary w ∧ IsCoprime w.re w.im ∧
      (Work.FIPlan.gnorm w : ℝ) ≤ M)
    (hβsupp : ∀ z, β z ≠ 0 → (Work.FIPlan.gnorm z : ℝ) ≤ N)
    (hβnz : ∀ z, β z ≠ 0 → z ≠ 0) :
    ‖QBilin Rw Rz α β‖ ≤ (3 * 9 ^ 10 * 6 ^ A1 * C1 * C2) ^ ((1 : ℝ) / 12) *
      (M ^ ((11 : ℝ) / 12) * N + M ^ ((7 : ℝ) / 6) * N ^ ((3 : ℝ) / 4)
        + M ^ ((4 : ℝ) / 3) * N ^ ((1 : ℝ) / 2)) *
      (Real.log (M * N + 2)) ^ ((A1 + B2) / 12) := by
  classical
  set S : Finset GaussianInt := (Work.FIPlan.gBox Rw).filter (fun w => α w ≠ 0) with hS
  set B : GaussianInt → ℂ :=
    fun w => ∑ z ∈ Work.FIPlan.gBox Rz, β z * ((DirichletSym w z : ℤ) : ℂ) with hB
  set β₀ : GaussianInt → ℂ := fun z => if z ∈ Work.FIPlan.gBox Rz then β z else 0 with hβ0
  set Ut : Finset GaussianInt := Work.FIArea7.gDisc ⌈N ^ 3⌉ (N ^ 6) with hUt
  set S6 : ℝ := ∑ w ∈ S, ‖B w‖ ^ 6 with hS6
  have hS6nn : 0 ≤ S6 := by rw [hS6]; positivity
  -- ### Step A: the Hölder step over the coefficient support
  have hQle : ‖QBilin Rw Rz α β‖ ≤ (9 * M) ^ ((5 : ℝ) / 6) * S6 ^ ((1 : ℝ) / 6) := by
    have hQeq : QBilin Rw Rz α β = ∑ w ∈ S, α w * B w := by
      rw [QBilin_eq_bilinSum]
      rw [show (∑ w ∈ Work.FIPlan.gBox Rw, α w * (∑ z ∈ Work.FIPlan.gBox Rz,
            β z * ((DirichletSym w z : ℤ) : ℂ)))
          = ∑ w ∈ Work.FIPlan.gBox Rw, α w * B w from
        Finset.sum_congr rfl (fun w _ => by rw [hB])]
      rw [hS]
      exact (Finset.sum_subset (Finset.filter_subset (fun w => α w ≠ 0) (Work.FIPlan.gBox Rw))
        (fun w hw hwS => by
          have hα0 : α w = 0 := by
            by_contra hcon
            exact hwS (Finset.mem_filter.mpr ⟨hw, hcon⟩)
          simp [hα0])).symm
    rw [hQeq]
    have h1 := holder6_sum S α B hα1
    have hsub : S ⊆ Work.FIArea7.coeffSuppBox M Rw := by
      intro w hw
      rw [hS, Finset.mem_filter] at hw
      obtain ⟨hw1, hw2⟩ := hw
      obtain ⟨hp, hc, hn⟩ := hαsupp w hw2
      exact Finset.mem_filter.mpr ⟨hw1, hp, hc, hn⟩
    have hcard : ((S.card : ℝ)) ≤ 9 * M := by
      calc ((S.card : ℝ)) ≤ ((Work.FIArea7.coeffSuppBox M Rw).card : ℝ) :=
            Nat.cast_le.mpr (Finset.card_le_card hsub)
        _ ≤ 9 * M := Work.FIArea7.card_coeffSuppBox_le M Rw hM
    calc ‖∑ w ∈ S, α w * B w‖ ≤ ((S.card : ℝ)) ^ ((5 : ℝ) / 6)
          * (∑ w ∈ S, ‖B w‖ ^ 6) ^ ((1 : ℝ) / 6) := h1
      _ ≤ (9 * M) ^ ((5 : ℝ) / 6) * (∑ w ∈ S, ‖B w‖ ^ 6) ^ ((1 : ℝ) / 6) := by
          refine mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg (by positivity) _)
          exact Real.rpow_le_rpow (Nat.cast_nonneg _) hcard (by norm_num)
      _ = (9 * M) ^ ((5 : ℝ) / 6) * S6 ^ ((1 : ℝ) / 6) := by rw [hS6]
  -- ### Step B: `S6` as one complex sum over the `6`-fold convolution
  have hBw : ∀ w ∈ S, B w = ∑ z ∈ Work.FIPlan.gBox Rz, β₀ z * ((DirichletSym w z : ℤ) : ℂ) := by
    intro w _
    rw [hB]
    refine Finset.sum_congr rfl (fun z hz => ?_)
    rw [hβ0]
    simp [hz]
  have hβ0supp : ∀ z, β₀ z ≠ 0 → (Work.FIPlan.gnorm z : ℝ) ≤ N := by
    intro z hz
    have hz' : (if z ∈ Work.FIPlan.gBox Rz then β z else 0) ≠ 0 := by simpa only [hβ0] using hz
    by_cases h : z ∈ Work.FIPlan.gBox Rz
    · rw [if_pos h] at hz'; exact hβsupp z hz'
    · rw [if_neg h] at hz'; exact absurd rfl hz'
  have hβ0box : ∀ z, β₀ z ≠ 0 → z ∈ Work.FIPlan.gBox Rz := by
    intro z hz
    have hz' : (if z ∈ Work.FIPlan.gBox Rz then β z else 0) ≠ 0 := by simpa only [hβ0] using hz
    by_cases h : z ∈ Work.FIPlan.gBox Rz
    · exact h
    · rw [if_neg h] at hz'; exact absurd rfl hz'
  have hβ0le : ∀ z, ‖β₀ z‖ ≤ 1 := by
    intro z
    have : β₀ z = if z ∈ Work.FIPlan.gBox Rz then β z else 0 := by rw [hβ0]
    rw [this]
    by_cases h : z ∈ Work.FIPlan.gBox Rz
    · rw [if_pos h]; exact hβ1 z
    · rw [if_neg h]; simp
  have hβ0nz : ∀ z, β₀ z ≠ 0 → z ≠ 0 := by
    intro z hz
    have hz' : (if z ∈ Work.FIPlan.gBox Rz then β z else 0) ≠ 0 := by simpa only [hβ0] using hz
    by_cases h : z ∈ Work.FIPlan.gBox Rz
    · rw [if_pos h] at hz'; exact hβnz z hz'
    · rw [if_neg h] at hz'; exact absurd rfl hz'
  have hpow : ∀ w ∈ S, B w ^ 6 = ∑ u ∈ Ut,
      Work.FIArea7.conv6 Rz β₀ u * ((DirichletSym w u : ℤ) : ℂ) := by
    intro w hw
    obtain ⟨hwP, hwC, -⟩ : Work.FIPlan.IsPrimary w ∧ IsCoprime w.re w.im ∧
        (Work.FIPlan.gnorm w : ℝ) ≤ M := by
      rw [hS, Finset.mem_filter] at hw
      exact hαsupp w hw.2
    rw [hBw w hw, hUt]
    exact bilinSum_pow6 hN hβ0supp hwP hwC
  -- the unimodular phase of `B w ^ 6`
  set c : GaussianInt → ℂ := fun w => if w ∈ S then
      (if B w = 0 then 0 else star (B w ^ 6) / ((‖B w ^ 6‖ : ℝ) : ℂ)) else 0 with hc
  have hc_zero : ∀ w ∉ S, c w = 0 := by
    intro w hw
    simp only [hc]
    rw [if_neg hw]
  have hc_le : ∀ w, ‖c w‖ ≤ 1 := by
    intro w
    simp only [hc]
    by_cases hw : w ∈ S
    · rw [if_pos hw]
      by_cases hB0 : B w = 0
      · rw [if_pos hB0]; norm_num
      · rw [if_neg hB0, norm_div, norm_star, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (norm_nonneg _)]
        have hz : ((‖B w ^ 6‖ : ℝ)) ≠ 0 := by
          intro h
          exact hB0 ((pow_eq_zero_iff (by norm_num)).mp (norm_eq_zero.mp h))
        rw [div_self hz]
    · rw [if_neg hw]; norm_num
  have hcmul : ∀ w ∈ S, c w * B w ^ 6 = ((‖B w‖ ^ 6 : ℝ) : ℂ) := by
    intro w hw
    simp only [hc]
    rw [if_pos hw]
    by_cases hB0 : B w = 0
    · rw [if_pos hB0, zero_mul, hB0]; simp
    · rw [if_neg hB0]
      have hz : ((B w) ^ 6 : ℂ) ≠ 0 := pow_ne_zero _ hB0
      have hkey : ((B w) ^ 6) * star ((B w) ^ 6) = ((‖(B w) ^ 6‖ ^ 2 : ℝ) : ℂ) := by
        change (B w) ^ 6 * (starRingEnd ℂ) ((B w) ^ 6) = _
        rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
      rw [div_mul_eq_mul_div, mul_comm (star ((B w) ^ 6)) ((B w) ^ 6), hkey,
        ← Complex.ofReal_div]
      congr 1
      rw [norm_pow, pow_two]
      have hs : (‖B w‖ ^ 6 : ℝ) ≠ 0 := pow_ne_zero _ (norm_ne_zero_iff.mpr hB0)
      rw [mul_div_assoc, div_self hs, mul_one]
  set Aa : GaussianInt → ℂ := fun u => ∑ w ∈ Work.FIPlan.gBox Rw,
      c w * ((DirichletSym w u : ℤ) : ℂ) with hAa
  set K2 : ℝ := ∑ u ∈ Ut, ‖Aa u‖ ^ 2 with hK2
  set K1 : ℝ := ∑ u ∈ Ut, ‖Work.FIArea7.conv6 Rz β₀ u‖ ^ 2 with hK1
  have hS6id : ((S6 : ℝ) : ℂ) = ∑ u ∈ Ut, Work.FIArea7.conv6 Rz β₀ u * Aa u := by
    have hA : ((S6 : ℝ) : ℂ) = ∑ w ∈ S, c w * B w ^ 6 := by
      rw [hS6, Complex.ofReal_sum]
      exact Finset.sum_congr rfl (fun w hw => (hcmul w hw).symm)
    have hBsum : ∑ w ∈ S, c w * B w ^ 6 = ∑ w ∈ Work.FIPlan.gBox Rw, c w * B w ^ 6 := by
      rw [hS]
      refine Finset.sum_subset (Finset.filter_subset _ _) (fun w hw hwS => ?_)
      have hc0 : c w = 0 := by
        simp only [hc]
        rw [if_neg hwS]
      rw [hc0, zero_mul]
    have hC : ∑ w ∈ Work.FIPlan.gBox Rw, c w * B w ^ 6
        = ∑ w ∈ Work.FIPlan.gBox Rw, c w * (∑ u ∈ Ut,
            Work.FIArea7.conv6 Rz β₀ u * ((DirichletSym w u : ℤ) : ℂ)) := by
      refine Finset.sum_congr rfl (fun w hw => ?_)
      by_cases hwS : w ∈ S
      · rw [hpow w hwS]
      · have hc0 : c w = 0 := by
          simp only [hc]
          rw [if_neg hwS]
        rw [hc0, zero_mul, zero_mul]
    have hD : ∑ w ∈ Work.FIPlan.gBox Rw, c w * (∑ u ∈ Ut,
          Work.FIArea7.conv6 Rz β₀ u * ((DirichletSym w u : ℤ) : ℂ))
        = ∑ u ∈ Ut, Work.FIArea7.conv6 Rz β₀ u * Aa u := by
      rw [hAa]
      calc ∑ w ∈ Work.FIPlan.gBox Rw, c w * (∑ u ∈ Ut,
            Work.FIArea7.conv6 Rz β₀ u * ((DirichletSym w u : ℤ) : ℂ))
          = ∑ w ∈ Work.FIPlan.gBox Rw, ∑ u ∈ Ut, c w * (Work.FIArea7.conv6 Rz β₀ u
              * ((DirichletSym w u : ℤ) : ℂ)) := by
            refine Finset.sum_congr rfl (fun w _ => ?_)
            rw [Finset.mul_sum]
        _ = ∑ u ∈ Ut, ∑ w ∈ Work.FIPlan.gBox Rw, c w * (Work.FIArea7.conv6 Rz β₀ u
              * ((DirichletSym w u : ℤ) : ℂ)) := Finset.sum_comm
        _ = ∑ u ∈ Ut, ∑ w ∈ Work.FIPlan.gBox Rw, Work.FIArea7.conv6 Rz β₀ u
              * (c w * ((DirichletSym w u : ℤ) : ℂ)) := by
            refine Finset.sum_congr rfl (fun u _ => Finset.sum_congr rfl (fun w _ => by ring))
        _ = ∑ u ∈ Ut, Work.FIArea7.conv6 Rz β₀ u * (∑ w ∈ Work.FIPlan.gBox Rw,
              c w * ((DirichletSym w u : ℤ) : ℂ)) := by
            refine Finset.sum_congr rfl (fun u _ => ?_)
            exact (Finset.mul_sum _ _ _).symm
    rw [hA, hBsum, hC, hD]
  -- ### Step C: Cauchy–Schwarz
  have hK1nn : 0 ≤ K1 := by rw [hK1]; positivity
  have hK2nn : 0 ≤ K2 := by rw [hK2]; positivity
  have hCS : S6 ^ 2 ≤ K1 * K2 := by
    have hmod : S6 = ‖∑ u ∈ Ut, Work.FIArea7.conv6 Rz β₀ u * Aa u‖ := by
      rw [← hS6id, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hS6nn]
    rw [hmod]
    have h1 : ‖∑ u ∈ Ut, Work.FIArea7.conv6 Rz β₀ u * Aa u‖
        ≤ ∑ u ∈ Ut, ‖Work.FIArea7.conv6 Rz β₀ u‖ * ‖Aa u‖ := by
      calc ‖∑ u ∈ Ut, Work.FIArea7.conv6 Rz β₀ u * Aa u‖
          ≤ ∑ u ∈ Ut, ‖Work.FIArea7.conv6 Rz β₀ u * Aa u‖ := norm_sum_le _ _
        _ = ∑ u ∈ Ut, ‖Work.FIArea7.conv6 Rz β₀ u‖ * ‖Aa u‖ := by simp
    have h2 := Finset.sum_mul_sq_le_sq_mul_sq Ut
      (fun u => ‖Work.FIArea7.conv6 Rz β₀ u‖) (fun u => ‖Aa u‖)
    calc ‖∑ u ∈ Ut, Work.FIArea7.conv6 Rz β₀ u * Aa u‖ ^ 2
        ≤ (∑ u ∈ Ut, ‖Work.FIArea7.conv6 Rz β₀ u‖ * ‖Aa u‖) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) h1 2
      _ ≤ (∑ u ∈ Ut, ‖Work.FIArea7.conv6 Rz β₀ u‖ ^ 2) * (∑ u ∈ Ut, ‖Aa u‖ ^ 2) := h2
      _ = K1 * K2 := by rw [hK1, hK2]
  -- ### Step D: the two analytic inputs
  have hK1le : K1 ≤ C2 * N ^ 6 * (Real.log (N + 2)) ^ B2 := by
    rw [hK1, hUt]
    exact hconv N Rz β₀ hN hβ0supp hβ0box hβ0nz hβ0le
  have hK2le : K2 ≤ C1 * (N ^ 6 * M + M ^ 4 * N ^ 3 + M ^ 6)
      * (Real.log (M * N ^ 6 + 2)) ^ A1 := by
    have hN6 : (1 : ℝ) ≤ N ^ 6 := one_le_pow₀ hN
    have hcsupp : ∀ w, c w ≠ 0 → Work.FIPlan.IsPrimary w ∧ IsCoprime w.re w.im ∧
        (Work.FIPlan.gnorm w : ℝ) ≤ M := by
      intro w hw
      have hwS : w ∈ S := by
        by_contra hcon
        exact hw (hc_zero w hcon)
      rw [hS, Finset.mem_filter] at hwS
      exact hαsupp w hwS.2
    have hx := hms M (N ^ 6) Rw c hM hN6 hcsupp hc_le
    have hs : Real.sqrt (N ^ 6) = N ^ 3 := by
      rw [show N ^ 6 = (N ^ 3) ^ 2 by ring, Real.sqrt_sq (by positivity)]
    rw [hs] at hx
    rw [hK2, hUt, hAa]
    refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_) hx
    · intro u hu
      exact (Finset.mem_filter.mp hu).1
    · intro u _ _; positivity
  exact final_arith hC1 hC2 hA1 hB2 hM hN (norm_nonneg _) hS6nn hK1nn hK2nn
    hQle hCS hK1le hK2le

/-! ## The contribution of `z = 0` -/

/-- `ξ_w(0) ≠ 0` forces `|w|² ∈ {0, 1}`: `ξ_w(0) = J(0 | |w|²)`. -/
lemma dirichletSym_zero_ne {w : GaussianInt} (h : Work.FIArea7.DirichletSym w 0 ≠ 0) :
    Work.FIPlan.gnorm w = 0 ∨ Work.FIPlan.gnorm w = 1 := by
  have h0 : jacobiSym (0 : ℤ) (Work.FIPlan.gnorm w) ≠ 0 := by
    simpa only [Work.FIArea7.DirichletSym, mul_zero, Zsqrtd.re_zero] using h
  by_contra hcon
  push Not at hcon
  exact h0 (jacobiSym.eq_zero_iff.mpr ⟨hcon.1, by rw [Int.gcd_eq_natAbs]; simp [hcon.2]⟩)

/-- Deleting `z = 0` from `β` changes `QBilin Rw Rz α β` by at most `9`: the terms with
`ξ_w(0) ≠ 0` have `|w|² = 1` (there are at most `9` of them inside a box, `cardDiscBoxLe`), and
the term `w = 0` is killed by `α 0 = 0`. -/
lemma QBilin_zero_correction {Rw Rz : ℤ} {α β : GaussianInt → ℂ}
    (hα1 : ∀ w, ‖α w‖ ≤ 1) (hβ1 : ∀ z, ‖β z‖ ≤ 1) (hα0 : α 0 = 0) :
    ‖QBilin Rw Rz α β‖ ≤ ‖QBilin Rw Rz α (fun z => if z = 0 then 0 else β z)‖ + 9 := by
  set β' : GaussianInt → ℂ := fun z => if z = 0 then 0 else β z with hβ'def
  have hsplit : QBilin Rw Rz α β = QBilin Rw Rz α β' + QBilin Rw Rz α (β - β') := by
    simp only [QBilin]
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun z _ => ?_
    rw [Pi.sub_apply]
    ring
  have hkey : ∀ w : GaussianInt,
      ‖α w‖ * ‖∑ z ∈ Work.FIPlan.gBox Rz, (β - β') z * ((DirichletSym w z : ℤ) : ℂ)‖
        ≤ (if Work.FIPlan.gnorm w = 1 then (1 : ℝ) else 0) := by
    intro w
    have hsum : ∑ z ∈ Work.FIPlan.gBox Rz, (β - β') z * ((DirichletSym w z : ℤ) : ℂ)
        = if (0 : GaussianInt) ∈ Work.FIPlan.gBox Rz then
            β 0 * ((DirichletSym w 0 : ℤ) : ℂ) else 0 := by
      have hp : ∀ z : GaussianInt, (β - β') z * ((DirichletSym w z : ℤ) : ℂ)
          = (if z = 0 then β 0 * ((DirichletSym w z : ℤ) : ℂ) else 0) := by
        intro z
        rw [hβ'def, Pi.sub_apply]
        by_cases hz : z = 0
        · subst hz; simp
        · simp [hz]
      rw [Finset.sum_congr rfl (fun z _ => hp z)]
      exact Finset.sum_ite_eq' _ _ _
    have hξb : ‖((DirichletSym w 0 : ℤ) : ℂ)‖ ≤ 1 := by
      rw [Complex.norm_intCast]
      exact_mod_cast Work.FIArea7.abs_dirichletSym_le_one w 0
    by_cases h1 : Work.FIPlan.gnorm w = 1
    · rw [if_pos h1, hsum]
      by_cases hc : (0 : GaussianInt) ∈ Work.FIPlan.gBox Rz
      · rw [if_pos hc, norm_mul]
        calc ‖α w‖ * (‖β 0‖ * ‖((DirichletSym w 0 : ℤ) : ℂ)‖)
            ≤ 1 * (1 * 1) := by
              refine mul_le_mul (hα1 w) (mul_le_mul (hβ1 0) hξb (norm_nonneg _) zero_le_one)
                (by positivity) zero_le_one
          _ = 1 := by norm_num
      · rw [if_neg hc]; simp
    · rw [if_neg h1]
      by_cases hw : w = 0
      · subst hw; rw [hα0]; simp
      · have hξ : Work.FIArea7.DirichletSym w 0 = 0 := by
          by_contra hne
          rcases dirichletSym_zero_ne hne with hg | hg
          · exact hw (Work.FIArea7.gnorm_eq_zero_iff.mp hg)
          · exact h1 hg
        rw [hsum]
        by_cases hc : (0 : GaussianInt) ∈ Work.FIPlan.gBox Rz <;> simp [hc, hξ]
  have hdiff : ‖QBilin Rw Rz α (β - β')‖ ≤ 9 := by
    rw [QBilin]
    have hmain : ‖∑ w ∈ Work.FIPlan.gBox Rw, ∑ z ∈ Work.FIPlan.gBox Rz,
          α w * (β - β') z * ((DirichletSym w z : ℤ) : ℂ)‖
        ≤ ∑ w ∈ Work.FIPlan.gBox Rw, (if Work.FIPlan.gnorm w = 1 then (1 : ℝ) else 0) := by
      refine le_trans (norm_sum_le _ _) (Finset.sum_le_sum fun w _ => ?_)
      have hfac : ∑ z ∈ Work.FIPlan.gBox Rz, α w * (β - β') z * ((DirichletSym w z : ℤ) : ℂ)
          = α w * ∑ z ∈ Work.FIPlan.gBox Rz, (β - β') z * ((DirichletSym w z : ℤ) : ℂ) := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun z _ => by ring
      rw [hfac, norm_mul]
      exact hkey w
    refine hmain.trans ?_
    rw [Finset.sum_boole]
    have hsub : (Work.FIPlan.gBox Rw).filter (fun w => Work.FIPlan.gnorm w = 1)
        ⊆ (Work.FIPlan.gBox Rw).filter (fun w => (Work.FIPlan.gnorm w : ℝ) ≤ 1) := by
      intro w hw
      rw [Finset.mem_filter] at hw ⊢
      exact ⟨hw.1, by rw [hw.2]; norm_num⟩
    have h9 := Work.FIArea7.cardDiscBoxLe Rw 1 (by norm_num : (1 : ℝ) ≤ 1)
    have hcard : (((Work.FIPlan.gBox Rw).filter (fun w => Work.FIPlan.gnorm w = 1)).card : ℝ)
        ≤ 9 := by
      exact le_trans (Nat.cast_le.mpr (Finset.card_le_card hsub)) (by simpa using h9)
    exact hcard
  calc ‖QBilin Rw Rz α β‖
      = ‖QBilin Rw Rz α β' + QBilin Rw Rz α (β - β')‖ := by rw [← hsplit]
    _ ≤ ‖QBilin Rw Rz α β'‖ + ‖QBilin Rw Rz α (β - β')‖ := norm_add_le _ _
    _ ≤ ‖QBilin Rw Rz α β'‖ + 9 := by linarith
    _ = ‖QBilin Rw Rz α (fun z => if z = 0 then 0 else β z)‖ + 9 := by rw [hβ'def]

/-! ## The target -/

theorem holder6_bound : ∃ C A : ℝ, 0 < C ∧ 0 < A ∧
  ∀ (M N : ℝ) (Rw Rz : ℤ) (α β : GaussianInt → ℂ), 1 ≤ M → 1 ≤ N →
    (∀ w, ‖α w‖ ≤ 1) → (∀ z, ‖β z‖ ≤ 1) →
    (∀ w, α w ≠ 0 → Work.FIPlan.IsPrimary w ∧ IsCoprime w.re w.im ∧ (Work.FIPlan.gnorm w : ℝ) ≤ M) →
    (∀ z, β z ≠ 0 → (Work.FIPlan.gnorm z : ℝ) ≤ N) →
    ‖QBilin Rw Rz α β‖ ≤ C * (M ^ ((11 : ℝ) / 12) * N + M ^ ((7 : ℝ) / 6) * N ^ ((3 : ℝ) / 4)
      + M ^ ((4 : ℝ) / 3) * N ^ ((1 : ℝ) / 2)) * (Real.log (M * N + 2)) ^ A := by
  obtain ⟨C1, A1, hC1, hA1, hms⟩ := Work.FIArea7.meanSquareElem
  obtain ⟨C2, B2, hC2, hB2, hconv⟩ := conv6_l2_offzero
  refine ⟨(3 * 9 ^ 10 * 6 ^ A1 * C1 * C2) ^ ((1 : ℝ) / 12) + 9, (A1 + B2) / 12, ?_, ?_, ?_⟩
  · have h0 : (0 : ℝ) < 3 * 9 ^ 10 * 6 ^ A1 * C1 * C2 := by positivity
    have := Real.rpow_pos_of_pos h0 ((1 : ℝ) / 12)
    linarith
  · linarith
  · intro M N Rw Rz α β hM hN hα1 hβ1 hαsupp hβsupp
    set β' : GaussianInt → ℂ := fun z => if z = 0 then 0 else β z with hβ'def
    have hα0 : α 0 = 0 := by
      by_contra h
      exact absurd (hαsupp 0 h).1 (by simp [Work.FIPlan.IsPrimary])
    have hβ'1 : ∀ z, ‖β' z‖ ≤ 1 := by
      intro z
      rw [hβ'def]
      by_cases h : z = 0
      · simp [h]
      · simpa [h] using hβ1 z
    have hβ'supp : ∀ z, β' z ≠ 0 → (Work.FIPlan.gnorm z : ℝ) ≤ N := by
      intro z hz
      have hz' : (if z = 0 then 0 else β z) ≠ 0 := by simpa only [hβ'def] using hz
      by_cases h : z = 0
      · rw [if_pos h] at hz'; exact absurd rfl hz'
      · rw [if_neg h] at hz'; exact hβsupp z hz'
    have hβ'nz : ∀ z, β' z ≠ 0 → z ≠ 0 := by
      intro z hz
      have hz' : (if z = 0 then 0 else β z) ≠ 0 := by simpa only [hβ'def] using hz
      by_cases h : z = 0
      · rw [if_pos h] at hz'; exact absurd rfl hz'
      · exact h
    have hchain := chain6 hC1 hA1 hC2 hB2 hms hconv M N hM hN Rw Rz α β'
      hα1 hβ'1 hαsupp hβ'supp hβ'nz
    have hcorr := QBilin_zero_correction (Rw := Rw) (Rz := Rz) (α := α) (β := β) hα1 hβ1 hα0
    set S : ℝ := M ^ ((11 : ℝ) / 12) * N + M ^ ((7 : ℝ) / 6) * N ^ ((3 : ℝ) / 4)
      + M ^ ((4 : ℝ) / 3) * N ^ ((1 : ℝ) / 2) with hS
    set L : ℝ := (Real.log (M * N + 2)) ^ ((A1 + B2) / 12) with hL
    have hS1 : (1 : ℝ) ≤ S := by
      have h1 : (1 : ℝ) ≤ M ^ ((11 : ℝ) / 12) := Real.one_le_rpow hM (by norm_num)
      have h2 : (1 : ℝ) ≤ M ^ ((11 : ℝ) / 12) * N := by nlinarith
      have h3 : (0 : ℝ) ≤ M ^ ((7 : ℝ) / 6) * N ^ ((3 : ℝ) / 4) :=
        mul_nonneg (Real.rpow_nonneg (by linarith) _) (Real.rpow_nonneg (by linarith) _)
      have h4 : (0 : ℝ) ≤ M ^ ((4 : ℝ) / 3) * N ^ ((1 : ℝ) / 2) :=
        mul_nonneg (Real.rpow_nonneg (by linarith) _) (Real.rpow_nonneg (by linarith) _)
      rw [hS]; linarith
    have hL1 : (1 : ℝ) ≤ L := by
      rw [hL]
      exact Real.one_le_rpow (one_le_log_MN hM hN) (by linarith)
    have hX : (1 : ℝ) ≤ S * L := by nlinarith
    have hcorr' : ‖QBilin Rw Rz α β‖ ≤ ‖QBilin Rw Rz α β'‖ + 9 * (S * L) := by
      have : (9 : ℝ) ≤ 9 * (S * L) := by linarith
      linarith
    calc ‖QBilin Rw Rz α β‖
        ≤ ‖QBilin Rw Rz α β'‖ + 9 * (S * L) := hcorr'
      _ ≤ (3 * 9 ^ 10 * 6 ^ A1 * C1 * C2) ^ ((1 : ℝ) / 12) * S * L + 9 * (S * L) := by
          linarith
      _ = ((3 * 9 ^ 10 * 6 ^ A1 * C1 * C2) ^ ((1 : ℝ) / 12) + 9) * S * L := by ring

end

end Work.FIArea7.Pub213
