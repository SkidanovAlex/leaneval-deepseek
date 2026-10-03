/-
# `Submission.Work.FIArea7CF.meanSquareElem` — clash-free copy of `Submission.Work.FIArea7.meanSquareElem`

Imports redirected to the `FIArea7CF` copies; renamed: gnorm_mk_eq→cfx_gnorm_mk_eq, mem_gBox_iff→r2c_mem_gBox_iff.  The workspace contains several
incompatible declarations of `Work.FIArea7.mem_gBox_iff` (and of `norm_uniCoeff_le`,
`log_pow_le_rpow`, `gnorm_mk_eq`), so the amended area-7 assembly and the *FI* §§19–26
chain can only meet through copies.  See NOTES §63.
-/

import Mathlib
import Submission.Work.FIArea7.T_pair_bound
import Submission.Work.FIArea7.FIsymbols
import Submission.Work.FIArea7.card_charMod4d_eq_card_units
import Submission.Work.FIArea7.GaussUnits
import Submission.Work.FIArea7.sum_xiGaussMod_units
import Submission.Work.FIArea7CF.card_pairs_oddPart_sq_le
import Submission.Work.FIArea7.xiC_pair_sum_eq_zero_of_not_sq

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

set_option maxHeartbeats 2000000

namespace Work.FIArea7

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-- xi_w(z) as a complex number. -/
def msXi (w z : GaussianInt) : ℂ := ((DirichletSym w z : ℤ) : ℂ)

/-- The pair sum  over the box. -/
def msT (Rz : ℤ) (w1 w2 : GaussianInt) : ℂ :=
  ∑ z ∈ Work.FIPlan.gBox Rz, msXi w1 z * msXi w2 z

lemma msXi_conj (w z : GaussianInt) : (starRingEnd ℂ) (msXi w z) = msXi w z := by
  rw [msXi, ← Complex.ofReal_intCast]
  exact Complex.conj_ofReal _

lemma norm_starRingEnd (z : ℂ) : ‖(starRingEnd ℂ) z‖ = ‖z‖ := by
  rw [show (starRingEnd ℂ) z = star z from rfl, norm_star]

lemma msXi_normSq_le_one (w z : GaussianInt) : Complex.normSq (msXi w z) ≤ 1 := by
  have h : msXi w z = ((DirichletSym w z : ℝ) : ℂ) := by simp [msXi]
  rw [h, Complex.normSq_ofReal]
  rcases jacobiSym.trichotomy (w * z).re (Work.FIPlan.gnorm w) with hh | hh | hh <;>
    · rw [Work.FIArea7.dirichletSym_def, hh]; norm_num

lemma msXi_norm_le_one (w z : GaussianInt) : ‖msXi w z‖ ≤ 1 := by
  have h := msXi_normSq_le_one w z
  rw [Complex.normSq_eq_norm_sq] at h
  nlinarith [norm_nonneg (msXi w z)]


/-- The expansion of the disc mean square into the pair sums. -/
lemma meanSq_expansion (Rw Rz : ℤ) (a : GaussianInt → ℂ) :
    (∑ z ∈ Work.FIPlan.gBox Rz,
        ‖∑ w ∈ Work.FIPlan.gBox Rw, a w * msXi w z‖ ^ 2)
      = (∑ w1 ∈ Work.FIPlan.gBox Rw, ∑ w2 ∈ Work.FIPlan.gBox Rw,
          a w1 * (starRingEnd ℂ) (a w2)
            * (∑ z ∈ Work.FIPlan.gBox Rz, msXi w1 z * msXi w2 z)).re := by
  classical
  have hpt : ∀ z, ‖∑ w ∈ Work.FIPlan.gBox Rw, a w * msXi w z‖ ^ 2
      = ((∑ w ∈ Work.FIPlan.gBox Rw, a w * msXi w z)
          * (starRingEnd ℂ) (∑ w ∈ Work.FIPlan.gBox Rw, a w * msXi w z)).re := by
    intro z
    have h : (∑ w ∈ Work.FIPlan.gBox Rw, a w * msXi w z)
          * (starRingEnd ℂ) (∑ w ∈ Work.FIPlan.gBox Rw, a w * msXi w z)
        = ((Complex.normSq (∑ w ∈ Work.FIPlan.gBox Rw, a w * msXi w z) : ℝ) : ℂ) :=
      Complex.mul_conj _
    rw [Complex.sq_norm, h, Complex.ofReal_re]
  have hconj : ∀ z, (starRingEnd ℂ) (∑ w ∈ Work.FIPlan.gBox Rw, a w * msXi w z)
      = ∑ w ∈ Work.FIPlan.gBox Rw, (starRingEnd ℂ) (a w) * msXi w z := by
    intro z
    rw [map_sum]
    exact Finset.sum_congr rfl (fun w _ => by rw [map_mul, msXi_conj])
  have hbody : ∀ z, (∑ w ∈ Work.FIPlan.gBox Rw, a w * msXi w z)
        * (starRingEnd ℂ) (∑ w ∈ Work.FIPlan.gBox Rw, a w * msXi w z)
      = ∑ w1 ∈ Work.FIPlan.gBox Rw, ∑ w2 ∈ Work.FIPlan.gBox Rw,
          (a w1 * (starRingEnd ℂ) (a w2)) * (msXi w1 z * msXi w2 z) := by
    intro z
    rw [hconj z, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl (fun w1 _ => Finset.sum_congr rfl (fun w2 _ => ?_))
    ring
  rw [Finset.sum_congr rfl (fun z _ => hpt z), ← Complex.re_sum]
  congr 1
  rw [Finset.sum_congr rfl (fun z _ => hbody z), Finset.sum_comm]
  apply Finset.sum_congr rfl; intro w1 _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro w2 _
  rw [Finset.mul_sum]

/-- Trivial bound on the pair sum. -/
lemma msT_le_triv (Rz : ℤ) (w1 w2 : GaussianInt) :
    ‖msT Rz w1 w2‖ ≤ (((2 * Rz + 1).toNat : ℕ) : ℝ) ^ 2 := by
  rw [msT]
  have h : ∀ z, ‖msXi w1 z * msXi w2 z‖ ≤ 1 := by
    intro z
    rw [norm_mul]
    nlinarith [msXi_norm_le_one w1 z, msXi_norm_le_one w2 z, norm_nonneg (msXi w1 z),
      norm_nonneg (msXi w2 z)]
  calc ‖∑ z ∈ Work.FIPlan.gBox Rz, msXi w1 z * msXi w2 z‖
      ≤ ∑ z ∈ Work.FIPlan.gBox Rz, ‖msXi w1 z * msXi w2 z‖ := norm_sum_le _ _
    _ ≤ ∑ z ∈ Work.FIPlan.gBox Rz, (1 : ℝ) := Finset.sum_le_sum (fun z _ => h z)
    _ = (((2 * Rz + 1).toNat : ℕ) : ℝ) ^ 2 := by
        rw [Finset.sum_const, nsmul_eq_mul, mul_one, card_gBox_sq]
        push_cast
        ring

/-- Pair sum bounded by the counting error when the complete sum vanishes. -/
lemma msT_le_of_vanish (Rz : ℤ) (N1 N2 : ℕ) [NeZero N1] [NeZero N2] (w1 w2 : GaussianInt)
    (hN1 : Work.FIPlan.gnorm w1 = N1) (hN2 : Work.FIPlan.gnorm w2 = N2)
    (hv : (∑ p : ZMod (N1 * N2) × ZMod (N1 * N2),
        xiC (N1 * N2) w1 p * xiC (N1 * N2) w2 p) = 0) :
    ‖msT Rz w1 w2‖
      ≤ 2 * ((((2 * Rz + 1).toNat : ℝ) * ((N1 * N2 : ℕ) : ℝ))
          + (((N1 * N2 : ℕ) : ℝ)) ^ 2) := by
  rw [msT]
  have hb := T_pair_bound Rz N1 N2 w1 w2 hN1 hN2
  rw [hv, norm_zero, mul_zero, zero_add] at hb
  have hEq : (∑ z ∈ Work.FIPlan.gBox Rz, msXi w1 z * msXi w2 z)
      = ∑ z ∈ Work.FIPlan.gBox Rz,
          (DirichletSym w1 z : ℂ) * (DirichletSym w2 z : ℂ) := rfl
  rwa [hEq]

/-- (2 ceil(sqrt X) + 1).toNat ≤ 5 sqrt X for X ≥ 1. -/
lemma toNat_two_ceil_sqrt_le (X : ℝ) (hX : 1 ≤ X) :
    (((2 * ⌈Real.sqrt X⌉ + 1).toNat : ℕ) : ℝ) ≤ 5 * Real.sqrt X := by
  have hs : (1:ℝ) ≤ Real.sqrt X := Real.one_le_sqrt.mpr hX
  have hc1 : (1:ℤ) ≤ ⌈Real.sqrt X⌉ := by
    have h1 : (1:ℝ) ≤ ((⌈Real.sqrt X⌉ : ℤ) : ℝ) := le_trans hs (Int.le_ceil _)
    exact_mod_cast h1
  have hc : (0:ℤ) ≤ 2 * ⌈Real.sqrt X⌉ + 1 := by linarith
  have hcast : (((2 * ⌈Real.sqrt X⌉ + 1).toNat : ℕ) : ℝ)
      = ((2 * ⌈Real.sqrt X⌉ + 1 : ℤ) : ℝ) := by
    rw [← Int.cast_natCast, Int.toNat_of_nonneg hc]
  rw [hcast]
  push_cast
  have hceil : ((⌈Real.sqrt X⌉ : ℤ) : ℝ) < Real.sqrt X + 1 := Int.ceil_lt_add_one _
  nlinarith [hceil, hs]

/-- ((2 ceil(sqrt X) + 1).toNat)^2 ≤ 25 X for X ≥ 1. -/
lemma toNat_two_ceil_sqrt_sq_le (X : ℝ) (hX : 1 ≤ X) :
    ((((2 * ⌈Real.sqrt X⌉ + 1).toNat : ℕ) : ℝ)) ^ 2 ≤ 25 * X := by
  have h1 := toNat_two_ceil_sqrt_le X hX
  have h0 : (0:ℝ) ≤ (((2 * ⌈Real.sqrt X⌉ + 1).toNat : ℕ) : ℝ) := Nat.cast_nonneg _
  have h2 : (5 * Real.sqrt X) ^ 2 = 25 * X := by
    rw [mul_pow, Real.sq_sqrt (by linarith : (0:ℝ) ≤ X)]
    norm_num
  calc ((((2 * ⌈Real.sqrt X⌉ + 1).toNat : ℕ) : ℝ)) ^ 2 ≤ (5 * Real.sqrt X) ^ 2 :=
        pow_le_pow_left₀ h0 h1 2
    _ = 25 * X := h2

/-- 1 ≤ log (M*N+2) for M, N ≥ 1. -/
lemma one_le_log (M N : ℝ) (hM : 1 ≤ M) (hN : 1 ≤ N) : (1:ℝ) ≤ Real.log (M * N + 2) := by
  have hlog3 : (1:ℝ) < Real.log 3 :=
    (Real.lt_log_iff_exp_lt (by norm_num)).mpr Real.exp_one_lt_three
  have hle : Real.log 3 ≤ Real.log (M * N + 2) :=
    Real.log_le_log (by norm_num) (by nlinarith)
  linarith

/-- The log-bookkeeping at the end. -/
lemma one_add_log_le (M N : ℝ) (hM : 1 ≤ M) (hN : 1 ≤ N) :
    1 + Real.log (2 + (((2 * ⌈Real.sqrt M⌉ + 1).toNat : ℕ) : ℝ))
      ≤ 4 * Real.log (M * N + 2) := by
  set L : ℝ := Real.log (M * N + 2) with hL
  have hL1 : (1:ℝ) ≤ L := one_le_log M N hM hN
  have hRr : (((2 * ⌈Real.sqrt M⌉ + 1).toNat : ℕ) : ℝ) ≤ 5 * Real.sqrt M :=
    toNat_two_ceil_sqrt_le M hM
  have hsM1 : (1:ℝ) ≤ Real.sqrt M := Real.one_le_sqrt.mpr hM
  have h7 : 2 + (((2 * ⌈Real.sqrt M⌉ + 1).toNat : ℕ) : ℝ) ≤ 7 * Real.sqrt M := by
    nlinarith [hRr, hsM1]
  have hpos2 : (0:ℝ) < 2 + (((2 * ⌈Real.sqrt M⌉ + 1).toNat : ℕ) : ℝ) := by
    have : (0:ℝ) ≤ (((2 * ⌈Real.sqrt M⌉ + 1).toNat : ℕ) : ℝ) := Nat.cast_nonneg _
    linarith
  have hlog7M : Real.log (2 + (((2 * ⌈Real.sqrt M⌉ + 1).toNat : ℕ) : ℝ))
      ≤ Real.log (7 * Real.sqrt M) := Real.log_le_log hpos2 h7
  have hsMpos : 0 < Real.sqrt M := Real.sqrt_pos.mpr (by linarith)
  have hsplit : Real.log (7 * Real.sqrt M) = Real.log 7 + Real.log M / 2 := by
    rw [Real.log_mul (by norm_num) hsMpos.ne', Real.log_sqrt (by linarith : (0:ℝ) ≤ M)]
  have hlog7lt : Real.log 7 < 2 := by
    rw [Real.log_lt_iff_lt_exp (by norm_num : (0:ℝ) < 7)]
    rw [show (2:ℝ) = 1 + 1 by norm_num, Real.exp_add]
    nlinarith [Real.exp_one_gt_d9, Real.exp_pos 1]
  have hlogMle : Real.log M ≤ L := by
    rw [hL]; exact Real.log_le_log (by linarith) (by nlinarith)
  have hfinal : Real.log (2 + (((2 * ⌈Real.sqrt M⌉ + 1).toNat : ℕ) : ℝ)) ≤ L + 2 := by
    have h1 := hlog7M
    rw [hsplit] at h1
    linarith
  linarith

/-- Membership bound: |Re z| and |Im z| are at most sqrt(|z|^2). -/
lemma msq_gnorm_cast (z : GaussianInt) :
    ((Work.FIPlan.gnorm z : ℕ) : ℝ) = ((z.re : ℝ)) ^ 2 + ((z.im : ℝ)) ^ 2 := by
  have h4 : (Work.FIPlan.gnorm z : ℤ) = z.re ^ 2 + z.im ^ 2 := norm_eq z
  calc ((Work.FIPlan.gnorm z : ℕ) : ℝ) = ((Work.FIPlan.gnorm z : ℤ) : ℝ) := by push_cast; ring
    _ = ((z.re ^ 2 + z.im ^ 2 : ℤ) : ℝ) := by rw [h4]
    _ = ((z.re : ℝ)) ^ 2 + ((z.im : ℝ)) ^ 2 := by push_cast; ring

lemma abs_re_le_sqrt (z : GaussianInt) :
    ((|z.re| : ℤ) : ℝ) ≤ Real.sqrt ((Work.FIPlan.gnorm z : ℕ) : ℝ) := by
  rw [Int.cast_abs, ← Real.sqrt_sq_eq_abs]
  apply Real.sqrt_le_sqrt
  have h3 := msq_gnorm_cast z
  calc ((z.re : ℝ)) ^ 2 ≤ ((z.re : ℝ)) ^ 2 + ((z.im : ℝ)) ^ 2 := by
        nlinarith [sq_nonneg (z.im : ℝ)]
    _ = ((Work.FIPlan.gnorm z : ℕ) : ℝ) := h3.symm

lemma abs_im_le_sqrt (z : GaussianInt) :
    ((|z.im| : ℤ) : ℝ) ≤ Real.sqrt ((Work.FIPlan.gnorm z : ℕ) : ℝ) := by
  rw [Int.cast_abs, ← Real.sqrt_sq_eq_abs]
  apply Real.sqrt_le_sqrt
  have h3 := msq_gnorm_cast z
  calc ((z.im : ℝ)) ^ 2 ≤ ((z.re : ℝ)) ^ 2 + ((z.im : ℝ)) ^ 2 := by
        nlinarith [sq_nonneg (z.re : ℝ)]
    _ = ((Work.FIPlan.gnorm z : ℕ) : ℝ) := h3.symm

lemma msq_mem_gBox_iff {R : ℤ} {z : GaussianInt} :
    z ∈ Work.FIPlan.gBox R ↔ -R ≤ z.re ∧ z.re ≤ R ∧ -R ≤ z.im ∧ z.im ≤ R := by
  rw [Work.FIPlan.gBox, Finset.mem_image]
  constructor
  · rintro ⟨p, hp, rfl⟩
    have hp' := Finset.mem_product.mp hp
    exact ⟨(Finset.mem_Icc.mp hp'.1).1, (Finset.mem_Icc.mp hp'.1).2,
      (Finset.mem_Icc.mp hp'.2).1, (Finset.mem_Icc.mp hp'.2).2⟩
  · rintro ⟨h1, h2, h3, h4⟩
    exact ⟨(z.re, z.im), Finset.mem_product.mpr
      ⟨Finset.mem_Icc.mpr ⟨h1, h2⟩, Finset.mem_Icc.mpr ⟨h3, h4⟩⟩, by cases z; rfl⟩

lemma mem_gBox_of_box (R : ℤ) {z : GaussianInt}
    (hre : ((|z.re| : ℤ) : ℝ) ≤ ((R : ℤ) : ℝ)) (him : ((|z.im| : ℤ) : ℝ) ≤ ((R : ℤ) : ℝ)) :
    z ∈ Work.FIPlan.gBox R := by
  have hre' : |z.re| ≤ R := by exact_mod_cast hre
  have him' : |z.im| ≤ R := by exact_mod_cast him
  rw [msq_mem_gBox_iff]
  exact ⟨(abs_le.mp hre').1, (abs_le.mp hre').2, (abs_le.mp him').1, (abs_le.mp him').2⟩

lemma oddPart_of_odd {n : ℕ} (hn : Odd n) : Work.FIPlan.oddPart n = n := by
  have hn0 : n ≠ 0 := by
    obtain ⟨k, hk⟩ := hn
    omega
  have hv : n.factorization 2 = 0 := by
    by_contra h
    have h1 : 1 ≤ n.factorization 2 := Nat.one_le_iff_ne_zero.mpr h
    have hdvd : 2 ∣ n := by
      have := (Nat.Prime.pow_dvd_iff_le_factorization (p := 2) (k := 1) (n := n)
        (by norm_num) hn0).mpr (by simpa using h1)
      simpa using this
    obtain ⟨k, hk⟩ := hn
    obtain ⟨c, hc⟩ := hdvd
    omega
  rw [Work.FIPlan.oddPart, hv]
  simp

theorem meanSquareElem_of_vanish
    (hvan : ∀ (N1 N2 : ℕ) [NeZero N1] [NeZero N2] (w1 w2 : GaussianInt),
      Work.FIPlan.IsPrimary w1 → Work.FIPlan.IsPrimary w2 →
      IsCoprime w1.re w1.im → IsCoprime w2.re w2.im →
      Work.FIPlan.gnorm w1 = N1 → Work.FIPlan.gnorm w2 = N2 →
      (¬ ∃ s : ℕ, N1 * N2 = s ^ 2) →
      (∑ p : ZMod (N1 * N2) × ZMod (N1 * N2),
        xiC (N1 * N2) w1 p * xiC (N1 * N2) w2 p) = 0) :
    ∃ C A : ℝ, 0 < C ∧ 0 < A ∧
      ∀ (M N : ℝ) (Rw : ℤ) (a : GaussianInt → ℂ), 1 ≤ M → 1 ≤ N →
        (∀ w, a w ≠ 0 → Work.FIPlan.IsPrimary w ∧ IsCoprime w.re w.im ∧
          (Work.FIPlan.gnorm w : ℝ) ≤ M) →
        (∀ w, ‖a w‖ ≤ 1) →
        ∑ z ∈ Work.FIPlan.gBox (⌈Real.sqrt N⌉ : ℤ),
            ‖∑ w ∈ Work.FIPlan.gBox Rw, a w * ((DirichletSym w z : ℤ) : ℂ)‖ ^ 2
          ≤ C * (N * M + M ^ 4 * Real.sqrt N + M ^ 6) * (Real.log (M * N + 2)) ^ A := by
  obtain ⟨C0, hC0pos, hC0⟩ := card_pairs_oddPart_sq_le
  refine ⟨640000 * C0 + 7500, 5, by positivity, by norm_num, ?_⟩
  intro M N Rw a hM hN ha ha1
  have hM0 : (0:ℝ) < M := by linarith
  have hN0 : (0:ℝ) < N := by linarith
  set L : ℝ := Real.log (M * N + 2) with hLdef
  have hL1 : (1:ℝ) ≤ L := one_le_log M N hM hN
  have hL0 : (0:ℝ) < L := lt_of_lt_of_le one_pos hL1
  set Rz : ℤ := ⌈Real.sqrt N⌉ with hRzdef
  set Rm : ℤ := ⌈Real.sqrt M⌉ with hRmdef
  set S : Finset GaussianInt := (Work.FIPlan.gBox Rw).filter (fun w => a w ≠ 0) with hSdef
  set P : GaussianInt × GaussianInt → Prop := fun p =>
      Nat.sqrt (Work.FIPlan.oddPart (Work.FIPlan.gnorm p.1 * Work.FIPlan.gnorm p.2)) ^ 2
        = Work.FIPlan.oddPart (Work.FIPlan.gnorm p.1 * Work.FIPlan.gnorm p.2) with hPdef
  have hSmem : ∀ w ∈ S, a w ≠ 0 := by
    intro w hw
    rw [hSdef] at hw
    exact (Finset.mem_filter.mp hw).2
  have hSprop : ∀ w ∈ S, Work.FIPlan.IsPrimary w ∧ IsCoprime w.re w.im
      ∧ (Work.FIPlan.gnorm w : ℝ) ≤ M := fun w hw => ha w (hSmem w hw)
  have hSle : ∀ w ∈ S, (Work.FIPlan.gnorm w : ℝ) ≤ M := fun w hw => (hSprop w hw).2.2
  have hSprim : ∀ w ∈ S, Work.FIPlan.IsPrimary w := fun w hw => (hSprop w hw).1
  have hScop : ∀ w ∈ S, IsCoprime w.re w.im := fun w hw => (hSprop w hw).2.1
  have hSpos : ∀ w ∈ S, 0 < Work.FIPlan.gnorm w := by
    intro w hw
    have hodd : Odd w.re := (hSprim w hw).1
    have hne : w ≠ 0 := by
      intro h0
      rw [h0] at hodd
      exact (by norm_num : ¬ Odd (0:ℤ)) hodd
    exact gnorm_pos_of_ne_zero hne
  have hSbox : ∀ w ∈ S, w ∈ Work.FIPlan.gBox Rm := by
    intro w hw
    have hle := hSle w hw
    have hsM : Real.sqrt M ≤ ((Rm : ℤ) : ℝ) := by rw [hRmdef]; exact Int.le_ceil _
    have hre : ((|w.re| : ℤ) : ℝ) ≤ ((Rm : ℤ) : ℝ) :=
      le_trans (le_trans (abs_re_le_sqrt w) (Real.sqrt_le_sqrt hle)) hsM
    have him : ((|w.im| : ℤ) : ℝ) ≤ ((Rm : ℤ) : ℝ) :=
      le_trans (le_trans (abs_im_le_sqrt w) (Real.sqrt_le_sqrt hle)) hsM
    exact mem_gBox_of_box Rm hre him
  have hcardS : ((S.card : ℕ) : ℝ) ≤ 25 * M := by
    have h1 : (S.card : ℕ) ≤ (Work.FIPlan.gBox Rm).card :=
      Finset.card_le_card (fun w hw => hSbox w hw)
    rw [card_gBox_sq] at h1
    calc ((S.card : ℕ) : ℝ) ≤ ((((2 * Rm + 1).toNat) ^ 2 : ℕ) : ℝ) := by exact_mod_cast h1
      _ = (((2 * Rm + 1).toNat : ℕ) : ℝ) ^ 2 := by push_cast; ring
      _ ≤ 25 * M := by rw [hRmdef]; exact toNat_two_ceil_sqrt_sq_le M hM
  have hsumS : (∑ w ∈ S, ((Work.FIPlan.gnorm w : ℕ) : ℝ)) ≤ 25 * M ^ 2 := by
    calc (∑ w ∈ S, ((Work.FIPlan.gnorm w : ℕ) : ℝ)) ≤ ∑ w ∈ S, M :=
          Finset.sum_le_sum (fun w hw => hSle w hw)
      _ = (S.card : ℝ) * M := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (25 * M) * M := mul_le_mul_of_nonneg_right hcardS hM0.le
      _ = 25 * M ^ 2 := by ring
  have hsumS2 : (∑ w ∈ S, (((Work.FIPlan.gnorm w : ℕ) : ℝ)) ^ 2) ≤ 25 * M ^ 3 := by
    calc (∑ w ∈ S, (((Work.FIPlan.gnorm w : ℕ) : ℝ)) ^ 2) ≤ ∑ w ∈ S, M ^ 2 :=
          Finset.sum_le_sum (fun w hw => by
            have h := hSle w hw
            have h0 : (0:ℝ) ≤ ((Work.FIPlan.gnorm w : ℕ) : ℝ) := Nat.cast_nonneg _
            nlinarith)
      _ = (S.card : ℝ) * M ^ 2 := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (25 * M) * M ^ 2 := mul_le_mul_of_nonneg_right hcardS (by positivity)
      _ = 25 * M ^ 3 := by ring

  have hoddS : ∀ w ∈ S, Odd (Work.FIPlan.gnorm w) := by
    intro w hw
    obtain ⟨a, ha⟩ := (hSprim w hw).1
    obtain ⟨b, hb⟩ := (hSprim w hw).2.1
    have hZ : Odd (w.re ^ 2 + w.im ^ 2) := ⟨2 * a ^ 2 + 2 * a + 2 * b ^ 2, by rw [ha, hb]; ring⟩
    have h4 : (Work.FIPlan.gnorm w : ℤ) = w.re ^ 2 + w.im ^ 2 := norm_eq w
    have h5 : Odd ((Work.FIPlan.gnorm w : ℕ) : ℤ) := by rw [h4]; exact hZ
    exact_mod_cast h5
  -- the coherent pair count
  have hcardP : ((((S ×ˢ S).filter P).card : ℕ) : ℝ) ≤ 25600 * C0 * M * L ^ 5 := by
    have hsub : (S ×ˢ S).filter P ⊆ (Work.FIPlan.gBox Rm ×ˢ Work.FIPlan.gBox Rm).filter P := by
      intro p hp
      rw [Finset.mem_filter] at hp ⊢
      exact ⟨Finset.mem_product.mpr ⟨hSbox p.1 (Finset.mem_product.mp hp.1).1,
        hSbox p.2 (Finset.mem_product.mp hp.1).2⟩, hp.2⟩
    have h1 : ((((S ×ˢ S).filter P).card : ℕ) : ℝ)
        ≤ ((((Work.FIPlan.gBox Rm ×ˢ Work.FIPlan.gBox Rm).filter P).card : ℕ) : ℝ) := by
      exact_mod_cast Finset.card_le_card hsub
    have h2 := hC0 Rm
    have h3 : ((((2 * Rm + 1).toNat : ℕ) : ℝ) ^ 2) ≤ 25 * M := by
      rw [hRmdef]; exact toNat_two_ceil_sqrt_sq_le M hM
    have h4 : 1 + Real.log (2 + (((2 * Rm + 1).toNat : ℕ) : ℝ)) ≤ 4 * L := by
      rw [hLdef, hRmdef]; exact one_add_log_le M N hM hN
    have h5 : (0:ℝ) ≤ 1 + Real.log (2 + (((2 * Rm + 1).toNat : ℕ) : ℝ)) := by
      have h6 : (0:ℝ) ≤ Real.log (2 + (((2 * Rm + 1).toNat : ℕ) : ℝ)) := by
        apply Real.log_nonneg
        have : (0:ℝ) ≤ (((2 * Rm + 1).toNat : ℕ) : ℝ) := Nat.cast_nonneg _
        linarith
      linarith
    calc ((((S ×ˢ S).filter P).card : ℕ) : ℝ)
        ≤ ((((Work.FIPlan.gBox Rm ×ˢ Work.FIPlan.gBox Rm).filter P).card : ℕ) : ℝ) := h1
      _ ≤ C0 * ((((2 * Rm + 1).toNat : ℕ) : ℝ) ^ 2)
            * (1 + Real.log (2 + (((2 * Rm + 1).toNat : ℕ) : ℝ))) ^ 5 := h2
      _ ≤ C0 * (25 * M) * (4 * L) ^ 5 := by
          refine mul_le_mul (mul_le_mul_of_nonneg_left h3 hC0pos.le) ?_ ?_ ?_
          · exact pow_le_pow_left₀ h5 h4 5
          · positivity
          · positivity
      _ = 25600 * C0 * M * L ^ 5 := by ring

  have stepB : (∑ w1 ∈ Work.FIPlan.gBox Rw, ∑ w2 ∈ Work.FIPlan.gBox Rw,
        a w1 * (starRingEnd ℂ) (a w2) * msT Rz w1 w2).re
      ≤ ∑ p ∈ S ×ˢ S, ‖msT Rz p.1 p.2‖ := by
    have hsubS : S ⊆ Work.FIPlan.gBox Rw := by
      intro w hw
      rw [hSdef] at hw
      exact (Finset.mem_filter.mp hw).1
    calc (∑ w1 ∈ Work.FIPlan.gBox Rw, ∑ w2 ∈ Work.FIPlan.gBox Rw,
            a w1 * (starRingEnd ℂ) (a w2) * msT Rz w1 w2).re
        ≤ ‖∑ w1 ∈ Work.FIPlan.gBox Rw, ∑ w2 ∈ Work.FIPlan.gBox Rw,
            a w1 * (starRingEnd ℂ) (a w2) * msT Rz w1 w2‖ := Complex.re_le_norm _
      _ ≤ ∑ w1 ∈ Work.FIPlan.gBox Rw, ‖∑ w2 ∈ Work.FIPlan.gBox Rw,
            a w1 * (starRingEnd ℂ) (a w2) * msT Rz w1 w2‖ := norm_sum_le _ _
      _ ≤ ∑ w1 ∈ Work.FIPlan.gBox Rw, ∑ w2 ∈ Work.FIPlan.gBox Rw,
            ‖a w1 * (starRingEnd ℂ) (a w2) * msT Rz w1 w2‖ :=
          Finset.sum_le_sum (fun w1 _ => norm_sum_le _ _)
      _ = ∑ w1 ∈ Work.FIPlan.gBox Rw, ∑ w2 ∈ Work.FIPlan.gBox Rw,
            ‖a w1‖ * ‖a w2‖ * ‖msT Rz w1 w2‖ := by
          apply Finset.sum_congr rfl; intro w1 _
          apply Finset.sum_congr rfl; intro w2 _
          rw [norm_mul, norm_mul, norm_starRingEnd]
      _ = ∑ w1 ∈ S, ∑ w2 ∈ S, ‖a w1‖ * ‖a w2‖ * ‖msT Rz w1 w2‖ := by
          have houter : ∀ w1 ∈ Work.FIPlan.gBox Rw, w1 ∉ S →
              (∑ w2 ∈ Work.FIPlan.gBox Rw, ‖a w1‖ * ‖a w2‖ * ‖msT Rz w1 w2‖) = 0 := by
            intro w1 hw1 hw1S
            have h0 : a w1 = 0 := by
              by_contra hne
              exact hw1S (by rw [hSdef]; exact Finset.mem_filter.mpr ⟨hw1, hne⟩)
            simp [h0]
          rw [← Finset.sum_subset hsubS houter]
          apply Finset.sum_congr rfl; intro w1 _
          have hinner : ∀ w2 ∈ Work.FIPlan.gBox Rw, w2 ∉ S →
              ‖a w1‖ * ‖a w2‖ * ‖msT Rz w1 w2‖ = 0 := by
            intro w2 hw2 hw2S
            have h0 : a w2 = 0 := by
              by_contra hne
              exact hw2S (by rw [hSdef]; exact Finset.mem_filter.mpr ⟨hw2, hne⟩)
            simp [h0]
          rw [← Finset.sum_subset hsubS hinner]
      _ = ∑ p ∈ S ×ˢ S, ‖a p.1‖ * ‖a p.2‖ * ‖msT Rz p.1 p.2‖ := by
          rw [Finset.sum_product]
      _ ≤ ∑ p ∈ S ×ˢ S, ‖msT Rz p.1 p.2‖ := by
          apply Finset.sum_le_sum; intro p _
          have h1 : ‖a p.1‖ ≤ 1 := ha1 p.1
          have h2 : ‖a p.2‖ ≤ 1 := ha1 p.2
          have h0 : (0:ℝ) ≤ ‖msT Rz p.1 p.2‖ := norm_nonneg _
          have h3 : ‖a p.1‖ * ‖a p.2‖ ≤ 1 := by
            have := mul_le_mul h1 h2 (norm_nonneg (a p.2)) (by norm_num : (0:ℝ) ≤ 1)
            simpa using this
          calc ‖a p.1‖ * ‖a p.2‖ * ‖msT Rz p.1 p.2‖ ≤ 1 * ‖msT Rz p.1 p.2‖ :=
                mul_le_mul_of_nonneg_right h3 h0
            _ = ‖msT Rz p.1 p.2‖ := one_mul _

  have hP1 : ∑ p ∈ (S ×ˢ S).filter P, ‖msT Rz p.1 p.2‖
      ≤ (25 * N) * (((S ×ˢ S).filter P).card : ℝ) := by
    calc ∑ p ∈ (S ×ˢ S).filter P, ‖msT Rz p.1 p.2‖
        ≤ ∑ p ∈ (S ×ˢ S).filter P, (25 * N) := by
          apply Finset.sum_le_sum; intro p _
          calc ‖msT Rz p.1 p.2‖ ≤ (((2 * Rz + 1).toNat : ℕ) : ℝ) ^ 2 := msT_le_triv Rz p.1 p.2
            _ ≤ 25 * N := by rw [hRzdef]; exact toNat_two_ceil_sqrt_sq_le N hN
      _ = (25 * N) * (((S ×ˢ S).filter P).card : ℝ) := by
          rw [Finset.sum_const, nsmul_eq_mul]; ring
  have hq : (∑ p ∈ S ×ˢ S, ((Work.FIPlan.gnorm p.1 * Work.FIPlan.gnorm p.2 : ℕ) : ℝ))
      = (∑ w ∈ S, ((Work.FIPlan.gnorm w : ℕ) : ℝ)) ^ 2 := by
    rw [Finset.sum_product]
    rw [sq, Finset.sum_mul_sum]
    apply Finset.sum_congr rfl; intro x _
    apply Finset.sum_congr rfl; intro y _
    push_cast; ring
  have hq2 : (∑ p ∈ S ×ˢ S, (((Work.FIPlan.gnorm p.1 * Work.FIPlan.gnorm p.2 : ℕ) : ℝ)) ^ 2)
      = (∑ w ∈ S, (((Work.FIPlan.gnorm w : ℕ) : ℝ)) ^ 2) ^ 2 := by
    rw [Finset.sum_product]
    rw [sq, Finset.sum_mul_sum]
    apply Finset.sum_congr rfl; intro x _
    apply Finset.sum_congr rfl; intro y _
    push_cast; ring
  have hP2 : ∑ p ∈ (S ×ˢ S).filter (fun p => ¬ P p), ‖msT Rz p.1 p.2‖
      ≤ 2 * ((((2 * Rz + 1).toNat : ℝ) * (25 * M ^ 2) ^ 2) + (25 * M ^ 3) ^ 2) := by
    have hper : ∀ p ∈ (S ×ˢ S).filter (fun p => ¬ P p),
        ‖msT Rz p.1 p.2‖ ≤ 2 * ((((2 * Rz + 1).toNat : ℝ)
            * ((Work.FIPlan.gnorm p.1 * Work.FIPlan.gnorm p.2 : ℕ) : ℝ))
            + (((Work.FIPlan.gnorm p.1 * Work.FIPlan.gnorm p.2 : ℕ) : ℝ)) ^ 2) := by
      intro p hp
      have hp' := Finset.mem_filter.mp hp
      have hpS := Finset.mem_product.mp hp'.1
      have hnotP : ¬ P p := hp'.2
      haveI : NeZero (Work.FIPlan.gnorm p.1) := ⟨ne_of_gt (hSpos p.1 hpS.1)⟩
      haveI : NeZero (Work.FIPlan.gnorm p.2) := ⟨ne_of_gt (hSpos p.2 hpS.2)⟩
      have hnsq : ¬ ∃ s : ℕ, Work.FIPlan.gnorm p.1 * Work.FIPlan.gnorm p.2 = s ^ 2 := by
        intro hs
        apply hnotP
        rw [hPdef]
        obtain ⟨s, hs'⟩ := hs
        have hodd : Work.FIPlan.oddPart (Work.FIPlan.gnorm p.1 * Work.FIPlan.gnorm p.2)
            = Work.FIPlan.gnorm p.1 * Work.FIPlan.gnorm p.2 :=
          oddPart_of_odd ((hoddS p.1 hpS.1).mul (hoddS p.2 hpS.2))
        rw [hodd, hs', Nat.sqrt_eq' s]
      exact msT_le_of_vanish Rz (Work.FIPlan.gnorm p.1) (Work.FIPlan.gnorm p.2) p.1 p.2 rfl rfl
        (hvan (Work.FIPlan.gnorm p.1) (Work.FIPlan.gnorm p.2) p.1 p.2
          (hSprim p.1 hpS.1) (hSprim p.2 hpS.2) (hScop p.1 hpS.1) (hScop p.2 hpS.2)
          rfl rfl hnsq)
    calc ∑ p ∈ (S ×ˢ S).filter (fun p => ¬ P p), ‖msT Rz p.1 p.2‖
        ≤ ∑ p ∈ (S ×ˢ S).filter (fun p => ¬ P p), 2 * ((((2 * Rz + 1).toNat : ℝ)
            * ((Work.FIPlan.gnorm p.1 * Work.FIPlan.gnorm p.2 : ℕ) : ℝ))
            + (((Work.FIPlan.gnorm p.1 * Work.FIPlan.gnorm p.2 : ℕ) : ℝ)) ^ 2) :=
          Finset.sum_le_sum hper
      _ ≤ ∑ p ∈ S ×ˢ S, 2 * ((((2 * Rz + 1).toNat : ℝ)
            * ((Work.FIPlan.gnorm p.1 * Work.FIPlan.gnorm p.2 : ℕ) : ℝ))
            + (((Work.FIPlan.gnorm p.1 * Work.FIPlan.gnorm p.2 : ℕ) : ℝ)) ^ 2) := by
          apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          intro p _ _
          positivity
      _ = 2 * ((((2 * Rz + 1).toNat : ℝ)
            * (∑ p ∈ S ×ˢ S, ((Work.FIPlan.gnorm p.1 * Work.FIPlan.gnorm p.2 : ℕ) : ℝ)))
            + (∑ p ∈ S ×ˢ S, (((Work.FIPlan.gnorm p.1 * Work.FIPlan.gnorm p.2 : ℕ) : ℝ)) ^ 2)) := by
          rw [← Finset.mul_sum]
          congr 1
          rw [Finset.sum_add_distrib]
          rw [Finset.mul_sum]
      _ ≤ 2 * ((((2 * Rz + 1).toNat : ℝ) * (25 * M ^ 2) ^ 2) + (25 * M ^ 3) ^ 2) := by
          rw [hq, hq2]
          have h1 : (∑ w ∈ S, ((Work.FIPlan.gnorm w : ℕ) : ℝ)) ^ 2 ≤ (25 * M ^ 2) ^ 2 :=
            pow_le_pow_left₀ (Finset.sum_nonneg (fun w _ => Nat.cast_nonneg _)) hsumS 2
          have h2 : (∑ w ∈ S, (((Work.FIPlan.gnorm w : ℕ) : ℝ)) ^ 2) ^ 2 ≤ (25 * M ^ 3) ^ 2 :=
            pow_le_pow_left₀ (Finset.sum_nonneg (fun w _ => sq_nonneg _)) hsumS2 2
          have ha0 : (0:ℝ) ≤ (((2 * Rz + 1).toNat : ℝ)) := Nat.cast_nonneg _
          have h3 := mul_le_mul_of_nonneg_left h1 ha0
          nlinarith [h3]

  have e2 : 2 * ((((2 * Rz + 1).toNat : ℝ) * (25 * M ^ 2) ^ 2) + (25 * M ^ 3) ^ 2)
      ≤ 6250 * (M ^ 4 * Real.sqrt N) + 1250 * M ^ 6 := by
    have halpha : (((2 * Rz + 1).toNat : ℝ)) ≤ 5 * Real.sqrt N := by
      rw [hRzdef]; exact toNat_two_ceil_sqrt_le N hN
    have hM4 : (0:ℝ) ≤ M ^ 4 := by positivity
    have hstep := mul_le_mul_of_nonneg_right halpha hM4
    nlinarith [hstep]
  have htot : (∑ p ∈ S ×ˢ S, ‖msT Rz p.1 p.2‖)
      ≤ 640000 * C0 * N * M * L ^ 5 + 6250 * (M ^ 4 * Real.sqrt N) + 1250 * M ^ 6 := by
    have hdecomp := Finset.sum_filter_add_sum_filter_not (S ×ˢ S) P (fun p => ‖msT Rz p.1 p.2‖)
    have e1 : (25 * N) * (((S ×ˢ S).filter P).card : ℝ) ≤ (25 * N) * (25600 * C0 * M * L ^ 5) :=
      mul_le_mul_of_nonneg_left hcardP (by positivity)
    calc (∑ p ∈ S ×ˢ S, ‖msT Rz p.1 p.2‖)
        = (∑ p ∈ (S ×ˢ S).filter P, ‖msT Rz p.1 p.2‖)
          + (∑ p ∈ (S ×ˢ S).filter (fun p => ¬ P p), ‖msT Rz p.1 p.2‖) := hdecomp.symm
      _ ≤ (25 * N) * (((S ×ˢ S).filter P).card : ℝ)
          + 2 * ((((2 * Rz + 1).toNat : ℝ) * (25 * M ^ 2) ^ 2) + (25 * M ^ 3) ^ 2) :=
          add_le_add hP1 hP2
      _ ≤ (25 * N) * (25600 * C0 * M * L ^ 5)
          + (6250 * (M ^ 4 * Real.sqrt N) + 1250 * M ^ 6) := by linarith [e1, e2]
      _ = 640000 * C0 * N * M * L ^ 5 + 6250 * (M ^ 4 * Real.sqrt N) + 1250 * M ^ 6 := by ring
  have hmain : (∑ z ∈ Work.FIPlan.gBox Rz, ‖∑ w ∈ Work.FIPlan.gBox Rw, a w * msXi w z‖ ^ 2)
      ≤ (640000 * C0 + 7500) * (N * M + M ^ 4 * Real.sqrt N + M ^ 6) * L ^ 5 := by
    calc (∑ z ∈ Work.FIPlan.gBox Rz, ‖∑ w ∈ Work.FIPlan.gBox Rw, a w * msXi w z‖ ^ 2)
        = (∑ w1 ∈ Work.FIPlan.gBox Rw, ∑ w2 ∈ Work.FIPlan.gBox Rw,
            a w1 * (starRingEnd ℂ) (a w2)
              * (∑ z ∈ Work.FIPlan.gBox Rz, msXi w1 z * msXi w2 z)).re :=
          meanSq_expansion Rw Rz a
      _ = (∑ w1 ∈ Work.FIPlan.gBox Rw, ∑ w2 ∈ Work.FIPlan.gBox Rw,
            a w1 * (starRingEnd ℂ) (a w2) * msT Rz w1 w2).re := by rfl
      _ ≤ ∑ p ∈ S ×ˢ S, ‖msT Rz p.1 p.2‖ := stepB
      _ ≤ 640000 * C0 * N * M * L ^ 5 + 6250 * (M ^ 4 * Real.sqrt N) + 1250 * M ^ 6 := htot
      _ ≤ (640000 * C0 + 7500) * (N * M + M ^ 4 * Real.sqrt N + M ^ 6) * L ^ 5 := by
          have hLp : (1:ℝ) ≤ L ^ 5 := one_le_pow₀ hL1
          have hA : (0:ℝ) ≤ M ^ 4 * Real.sqrt N := by positivity
          have hB : (0:ℝ) ≤ M ^ 6 := by positivity
          have hNM : (0:ℝ) ≤ N * M := by positivity
          have hNLp : (0:ℝ) ≤ N * M * L ^ 5 := by positivity
          have hALp : (0:ℝ) ≤ M ^ 4 * Real.sqrt N * L ^ 5 := by positivity
          have hBLp : (0:ℝ) ≤ M ^ 6 * L ^ 5 := by positivity
          have hLp7500 : (6250:ℝ) ≤ 7500 * L ^ 5 := by linarith
          have hLp1250 : (1250:ℝ) ≤ 7500 * L ^ 5 := by linarith
          have k2 : 6250 * (M ^ 4 * Real.sqrt N) ≤ 7500 * (M ^ 4 * Real.sqrt N) * L ^ 5 := by
            calc 6250 * (M ^ 4 * Real.sqrt N) = (M ^ 4 * Real.sqrt N) * 6250 := by ring
              _ ≤ (M ^ 4 * Real.sqrt N) * (7500 * L ^ 5) :=
                    mul_le_mul_of_nonneg_left hLp7500 hA
              _ = 7500 * (M ^ 4 * Real.sqrt N) * L ^ 5 := by ring
          have k3 : 1250 * M ^ 6 ≤ 7500 * M ^ 6 * L ^ 5 := by
            calc 1250 * M ^ 6 = M ^ 6 * 1250 := by ring
              _ ≤ M ^ 6 * (7500 * L ^ 5) := mul_le_mul_of_nonneg_left hLp1250 hB
              _ = 7500 * M ^ 6 * L ^ 5 := by ring
          have k1 : 640000 * C0 * N * M * L ^ 5
              ≤ 640000 * C0 * (N * M + M ^ 4 * Real.sqrt N + M ^ 6) * L ^ 5 := by
            have h4 : (0:ℝ) ≤ 640000 * C0 * L ^ 5 := by positivity
            have h5 : N * M ≤ N * M + M ^ 4 * Real.sqrt N + M ^ 6 := by linarith
            calc 640000 * C0 * N * M * L ^ 5 = (N * M) * (640000 * C0 * L ^ 5) := by ring
              _ ≤ (N * M + M ^ 4 * Real.sqrt N + M ^ 6) * (640000 * C0 * L ^ 5) :=
                    mul_le_mul_of_nonneg_right h5 h4
              _ = 640000 * C0 * (N * M + M ^ 4 * Real.sqrt N + M ^ 6) * L ^ 5 := by ring
          have hABL : (7500 * (M ^ 4 * Real.sqrt N) * L ^ 5 + 7500 * M ^ 6 * L ^ 5)
              ≤ 7500 * (N * M + M ^ 4 * Real.sqrt N + M ^ 6) * L ^ 5 := by
            have h1 : M ^ 4 * Real.sqrt N + M ^ 6 ≤ N * M + M ^ 4 * Real.sqrt N + M ^ 6 := by
              linarith
            have h0 : (0:ℝ) ≤ 7500 * L ^ 5 := by positivity
            calc 7500 * (M ^ 4 * Real.sqrt N) * L ^ 5 + 7500 * M ^ 6 * L ^ 5
                = (M ^ 4 * Real.sqrt N + M ^ 6) * (7500 * L ^ 5) := by ring
              _ ≤ (N * M + M ^ 4 * Real.sqrt N + M ^ 6) * (7500 * L ^ 5) :=
                    mul_le_mul_of_nonneg_right h1 h0
              _ = 7500 * (N * M + M ^ 4 * Real.sqrt N + M ^ 6) * L ^ 5 := by ring
          have htot1 : 640000 * C0 * N * M * L ^ 5 + 6250 * (M ^ 4 * Real.sqrt N) + 1250 * M ^ 6
              ≤ 640000 * C0 * (N * M + M ^ 4 * Real.sqrt N + M ^ 6) * L ^ 5
                + 7500 * (N * M + M ^ 4 * Real.sqrt N + M ^ 6) * L ^ 5 := by
            linarith [k1, k2, k3, hABL]
          have htot2 : 640000 * C0 * (N * M + M ^ 4 * Real.sqrt N + M ^ 6) * L ^ 5
                + 7500 * (N * M + M ^ 4 * Real.sqrt N + M ^ 6) * L ^ 5
              = (640000 * C0 + 7500) * (N * M + M ^ 4 * Real.sqrt N + M ^ 6) * L ^ 5 := by
            ring
          rw [← htot2]
          exact htot1
  rw [hLdef] at hmain
  rw [show (5:ℝ) = ((5:ℕ):ℝ) from by norm_num, Real.rpow_natCast]
  exact hmain

/-- *FI* Lemma 21.2 / (21.8), the L2-form of the mean square of the Dirichlet symbols.

For coefficients a supported on primary primitive w with |w|^2 <= M and bounded by 1, the box
mean square of A(z) = sum_w a_w xi_w(z) is bounded by C (N M + M^4 sqrt N + M^6) (log (M N + 2))^A. -/
theorem meanSquareElem : ∃ C A : ℝ, 0 < C ∧ 0 < A ∧
  ∀ (M N : ℝ) (Rw : ℤ) (a : GaussianInt → ℂ), 1 ≤ M → 1 ≤ N →
    (∀ w, a w ≠ 0 → Work.FIPlan.IsPrimary w ∧ IsCoprime w.re w.im ∧ (Work.FIPlan.gnorm w : ℝ) ≤ M) →
    (∀ w, ‖a w‖ ≤ 1) →
    ∑ z ∈ Work.FIPlan.gBox (⌈Real.sqrt N⌉ : ℤ),
        ‖∑ w ∈ Work.FIPlan.gBox Rw, a w * ((Work.FIArea7.DirichletSym w z : ℤ) : ℂ)‖ ^ 2
      ≤ C * (N * M + M ^ 4 * Real.sqrt N + M ^ 6) * (Real.log (M * N + 2)) ^ A :=
  meanSquareElem_of_vanish (fun N1 N2 _ _ w1 w2 h1 h2 hp1 hp2 hN1 hN2 hsq =>
    xiC_pair_sum_eq_zero_of_not_sq N1 N2 w1 w2 h1 h2 hp1 hp2 hN1 hN2 hsq)

end

end Work.FIArea7
