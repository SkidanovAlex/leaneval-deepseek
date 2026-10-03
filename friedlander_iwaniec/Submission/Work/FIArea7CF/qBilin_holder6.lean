/-
# `Submission.Work.FIArea7CF.qBilin_holder6` — clash-free copy of `Submission.Work.FIArea7.qBilin_holder6`

Imports redirected to the `FIArea7CF` copies; renamed: mem_gBox_iff→qb_mem_gBox_iff.  The workspace contains several
incompatible declarations of `Work.FIArea7.mem_gBox_iff` (and of `norm_uniCoeff_le`,
`log_pow_le_rpow`, `gnorm_mk_eq`), so the amended area-7 assembly and the *FI* §§19–26
chain can only meet through copies.  See NOTES §63.
-/
import Mathlib
import Submission.Work.FIArea7.Classical172Defs
import Submission.Work.FIArea7.DirichletReciprocity
import Submission.Work.FIArea7.dirichletSym_mul
import Submission.Work.FIArea7CF.qBilinDefs

set_option maxHeartbeats 1600000

namespace Work.FIArea7

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-- `‖Σ_{w∈S} α_w f_w‖ ≤ (#S)^{5/6}(Σ_{w∈S}‖f_w‖⁶)^{1/6}` for `‖α‖ ≤ 1`. -/
lemma holder6_sum (S : Finset GaussianInt) (α f : GaussianInt → ℂ)
    (hα : ∀ w, ‖α w‖ ≤ 1) :
    ‖∑ w ∈ S, α w * f w‖ ≤ ((S.card : ℝ)) ^ ((5 : ℝ) / 6)
      * (∑ w ∈ S, ‖f w‖ ^ 6) ^ ((1 : ℝ) / 6) := by
  have h1 : ‖∑ w ∈ S, α w * f w‖ ≤ ∑ w ∈ S, ‖f w‖ := by
    calc ‖∑ w ∈ S, α w * f w‖ ≤ ∑ w ∈ S, ‖α w * f w‖ := norm_sum_le _ _
      _ = ∑ w ∈ S, ‖α w‖ * ‖f w‖ := by simp
      _ ≤ ∑ w ∈ S, 1 * ‖f w‖ := by
          refine Finset.sum_le_sum (fun w _ => ?_)
          exact mul_le_mul_of_nonneg_right (hα w) (norm_nonneg _)
      _ = ∑ w ∈ S, ‖f w‖ := by simp
  have h2 : ∑ w ∈ S, ‖f w‖ ≤ ((S.card : ℝ)) ^ ((5 : ℝ) / 6)
      * (∑ w ∈ S, ‖f w‖ ^ 6) ^ ((1 : ℝ) / 6) := by
    have hpq : Real.HolderConjugate 6 (6 / 5) := by
      rw [Real.holderConjugate_iff]; constructor <;> norm_num
    have hH := Real.inner_le_Lp_mul_Lq S (fun w : GaussianInt => ‖f w‖) (fun _ => (1 : ℝ)) hpq
    have e1 : (∑ w ∈ S, ‖f w‖ * (1 : ℝ)) = ∑ w ∈ S, ‖f w‖ := by simp
    have e2 : (∑ w ∈ S, |‖f w‖| ^ (6 : ℝ)) = ∑ w ∈ S, ‖f w‖ ^ 6 := by
      refine Finset.sum_congr rfl (fun w _ => ?_)
      rw [abs_of_nonneg (norm_nonneg _)]
      norm_num
    have e3 : (∑ _w ∈ S, |(1 : ℝ)| ^ ((6 : ℝ) / 5)) = ((S.card : ℝ)) := by simp
    rw [e1, e2, e3] at hH
    rw [show ((1 : ℝ) / (6 / 5)) = 5 / 6 by norm_num] at hH
    refine hH.trans_eq ?_
    ring
  exact le_trans h1 h2

lemma gnorm_tupProd_le {N : ℝ} {β : GaussianInt → ℂ}
    (hβ : ∀ z, β z ≠ 0 → (Work.FIPlan.gnorm z : ℝ) ≤ N) {t : Fin 6 → GaussianInt}
    (ht : (∏ i : Fin 6, β (t i)) ≠ 0) :
    (Work.FIPlan.gnorm (Work.FIArea7.tupProd t) : ℝ) ≤ N ^ 6 := by
  have hne : ∀ i : Fin 6, β (t i) ≠ 0 :=
    fun i => (Finset.prod_ne_zero_iff.mp ht) i (Finset.mem_univ i)
  have hb : ∀ i : Fin 6, (Work.FIPlan.gnorm (t i) : ℝ) ≤ N := fun i => hβ _ (hne i)
  rw [Work.FIArea7.tupProd, Work.FIArea7.gnorm_prod_univ]
  have h1 : (((∏ i : Fin 6, Work.FIPlan.gnorm (t i)) : ℕ) : ℝ)
      = ∏ i : Fin 6, ((Work.FIPlan.gnorm (t i) : ℕ) : ℝ) := by push_cast; ring
  rw [h1]
  calc ∏ i : Fin 6, ((Work.FIPlan.gnorm (t i) : ℕ) : ℝ) ≤ ∏ _i : Fin 6, N :=
        Finset.prod_le_prod₀ (fun i _ => Nat.cast_nonneg _) (fun i _ => hb i)
    _ = N ^ 6 := by simp

/-- A primary Gaussian integer of norm `1` is `1`. -/
lemma eq_one_of_primary_gnorm_one {w : GaussianInt} (hp : Work.FIPlan.IsPrimary w)
    (hg : Work.FIPlan.gnorm w = 1) : w = 1 := by
  obtain ⟨ho, he, hmod⟩ := hp
  have h : w.re ^ 2 + w.im ^ 2 = 1 := by
    have h2 := norm_eq w
    rw [hg] at h2
    simpa using h2.symm
  have him2 : w.im ^ 2 ≤ 1 := by nlinarith [sq_nonneg w.re]
  have him0 : w.im = 0 := by
    have habs : |w.im| ≤ (1 : ℤ) := by
      have h' : w.im ^ 2 ≤ (1 : ℤ) ^ 2 := by simpa using him2
      simpa using sq_le_sq.mp h'
    obtain ⟨hg2, hl2⟩ := abs_le.mp habs
    obtain ⟨k2, hk2⟩ := he
    omega
  have hre2 : w.re ^ 2 = 1 := by
    rw [him0] at h
    simpa using h
  have hdvd : (4 : ℤ) ∣ w.re - 1 := by
    have h4 : (4 : ℤ) ∣ (w.re - 1) - w.im := Int.modEq_iff_dvd.mp hmod
    rwa [him0, sub_zero] at h4
  rcases sq_eq_one_iff.mp hre2 with h1 | h1
  · exact Zsqrtd.ext h1 him0
  · exfalso; rw [h1] at hdvd; omega

lemma bilinSum_pow6 {Rz : ℤ} {N : ℝ} (hN : 1 ≤ N) {β : GaussianInt → ℂ}
    (hβ : ∀ z, β z ≠ 0 → (Work.FIPlan.gnorm z : ℝ) ≤ N)
    {w : GaussianInt} (hprim : Work.FIPlan.IsPrimary w) (hcop : IsCoprime w.re w.im) :
    (∑ z ∈ Work.FIPlan.gBox Rz, β z * ((DirichletSym w z : ℤ) : ℂ)) ^ 6
      = ∑ u ∈ Work.FIArea7.gDisc ⌈N ^ 3⌉ (N ^ 6),
          Work.FIArea7.conv6 Rz β u * ((DirichletSym w u : ℤ) : ℂ) := by
  classical
  have hU : ∀ t ∈ Work.FIArea7.boxTup 6 Rz,
      (∏ i : Fin 6, β (t i)) ≠ 0 → Work.FIArea7.tupProd t ∈ Work.FIArea7.gDisc ⌈N ^ 3⌉ (N ^ 6) := by
    intro t _ ht
    have hle := gnorm_tupProd_le hβ ht
    exact Finset.mem_filter.mpr ⟨Work.FIArea7.mem_gBox_ceil_of_gnorm_le hN hle, hle⟩
  rw [Finset.sum_pow']
  change (∑ p ∈ Work.FIArea7.boxTup 6 Rz, ∏ i : Fin 6,
      (β (p i) * ((DirichletSym w (p i) : ℤ) : ℂ))) =
    ∑ u ∈ Work.FIArea7.gDisc ⌈N ^ 3⌉ (N ^ 6),
          Work.FIArea7.conv6 Rz β u * ((DirichletSym w u : ℤ) : ℂ)
  rw [show (∑ p ∈ Work.FIArea7.boxTup 6 Rz, ∏ i : Fin 6,
        (β (p i) * ((DirichletSym w (p i) : ℤ) : ℂ)))
      = ∑ p ∈ Work.FIArea7.boxTup 6 Rz, ((∏ i : Fin 6, β (p i))
        * ((DirichletSym w (Work.FIArea7.tupProd p) : ℤ) : ℂ)) from by
    refine Finset.sum_congr rfl (fun p _ => ?_)
    rw [Finset.prod_mul_distrib, Work.FIArea7.prod_dirichletSym hprim hcop]]
  exact (Work.FIArea7.sum_conv6_mul Rz β (fun u => ((DirichletSym w u : ℤ) : ℂ))
    (Work.FIArea7.gDisc ⌈N ^ 3⌉ (N ^ 6)) hU).symm

lemma final_arith {C1 A1 C2 B2 M N Q S6 K1 K2 : ℝ}
    (hC1 : 0 < C1) (hC2 : 0 < C2) (hA1 : 0 < A1) (hB2 : 0 < B2)
    (hM : 1 ≤ M) (hN : 1 ≤ N) (hQ : 0 ≤ Q) (hS6 : 0 ≤ S6)
    (hK1 : 0 ≤ K1) (hK2 : 0 ≤ K2)
    (h1 : Q ≤ (9 * M) ^ ((5 : ℝ) / 6) * S6 ^ ((1 : ℝ) / 6))
    (h2 : S6 ^ 2 ≤ K1 * K2)
    (h3 : K1 ≤ C2 * N ^ 6 * (Real.log (N + 2)) ^ B2)
    (h4 : K2 ≤ C1 * (N ^ 6 * M + M ^ 4 * N ^ 3 + M ^ 6) * (Real.log (M * N ^ 6 + 2)) ^ A1) :
    Q ≤ (3 * 9 ^ 10 * 6 ^ A1 * C1 * C2) ^ ((1 : ℝ) / 12) *
      (M ^ ((11 : ℝ) / 12) * N + M ^ ((7 : ℝ) / 6) * N ^ ((3 : ℝ) / 4)
        + M ^ ((4 : ℝ) / 3) * N ^ ((1 : ℝ) / 2)) *
      (Real.log (M * N + 2)) ^ ((A1 + B2) / 12) := by
  have hMn : (0 : ℝ) ≤ M := by linarith
  have hNn : (0 : ℝ) ≤ N := by linarith
  have hx1 : 1 ≤ M * N := by nlinarith
  have hx0 : 0 ≤ M * N := by nlinarith
  set L : ℝ := Real.log (M * N + 2) with hL
  have hLpos : 0 < L := by rw [hL]; apply Real.log_pos; nlinarith
  have hLnn : 0 ≤ L := le_of_lt hLpos
  have hlog1 : Real.log (N + 2) ≤ L := by
    rw [hL]; apply Real.log_le_log (by linarith); nlinarith
  have hlog1nn : 0 ≤ Real.log (N + 2) := Real.log_nonneg (by linarith)
  have hlog2 : Real.log (M * N ^ 6 + 2) ≤ 6 * L := by
    have hA : M * N ^ 6 ≤ (M * N) ^ 6 := by
      have hMle : M ≤ M ^ 6 := by
        calc M = M ^ 1 := (pow_one M).symm
          _ ≤ M ^ 6 := pow_le_pow_right₀ hM (by norm_num)
      calc M * N ^ 6 ≤ M ^ 6 * N ^ 6 := mul_le_mul_of_nonneg_right hMle (pow_nonneg hNn 6)
        _ = (M * N) ^ 6 := by ring
    have hB : (M * N) ^ 6 + 2 ≤ (M * N + 2) ^ 6 := by
      have h1 : (M * N) ^ 6 + 2 ≤ (M * N) ^ 6 + 2 * (M * N) ^ 5 := by
        have h5 : 1 ≤ (M * N) ^ 5 := one_le_pow₀ hx1
        linarith
      have h2 : (M * N) ^ 6 + 2 * (M * N) ^ 5 ≤ (M * N + 2) ^ 6 := by
        have e : (M * N) ^ 6 + 2 * (M * N) ^ 5 = (M * N) ^ 5 * (M * N + 2) := by ring
        rw [e]
        have hp : (M * N) ^ 5 ≤ (M * N + 2) ^ 5 := pow_le_pow_left₀ hx0 (by linarith) 5
        calc (M * N) ^ 5 * (M * N + 2) ≤ (M * N + 2) ^ 5 * (M * N + 2) :=
              mul_le_mul_of_nonneg_right hp (by linarith)
          _ = (M * N + 2) ^ 6 := by ring
      linarith
    have hmain : M * N ^ 6 + 2 ≤ (M * N + 2) ^ 6 := by linarith
    calc Real.log (M * N ^ 6 + 2) ≤ Real.log ((M * N + 2) ^ 6) :=
          Real.log_le_log (by nlinarith [mul_nonneg hMn (pow_nonneg hNn 6)]) hmain
      _ = 6 * L := by rw [Real.log_pow, hL]; push_cast; ring
  -- the target
  set T : ℝ := M ^ ((11 : ℝ) / 12) * N + M ^ ((7 : ℝ) / 6) * N ^ ((3 : ℝ) / 4)
      + M ^ ((4 : ℝ) / 3) * N ^ ((1 : ℝ) / 2) with hT
  have h1nn : 0 ≤ M ^ ((11 : ℝ) / 12) * N := by positivity
  have h2nn : 0 ≤ M ^ ((7 : ℝ) / 6) * N ^ ((3 : ℝ) / 4) := by positivity
  have h3nn : 0 ≤ M ^ ((4 : ℝ) / 3) * N ^ ((1 : ℝ) / 2) := by positivity
  have hTnn : 0 ≤ T := by rw [hT]; linarith
  have hp1 : (M ^ ((11 : ℝ) / 12)) ^ 12 = M ^ 11 := by
    rw [← Real.rpow_natCast (M ^ ((11 : ℝ) / 12)) 12, ← Real.rpow_mul hMn]
    norm_num
  have hp2 : (M ^ ((7 : ℝ) / 6)) ^ 12 = M ^ 14 := by
    rw [← Real.rpow_natCast (M ^ ((7 : ℝ) / 6)) 12, ← Real.rpow_mul hMn]
    norm_num
  have hp3 : (M ^ ((4 : ℝ) / 3)) ^ 12 = M ^ 16 := by
    rw [← Real.rpow_natCast (M ^ ((4 : ℝ) / 3)) 12, ← Real.rpow_mul hMn]
    norm_num
  have hq1 : (N ^ ((3 : ℝ) / 4)) ^ 12 = N ^ 9 := by
    rw [← Real.rpow_natCast (N ^ ((3 : ℝ) / 4)) 12, ← Real.rpow_mul hNn]
    norm_num
  have hq2 : (N ^ ((1 : ℝ) / 2)) ^ 12 = N ^ 6 := by
    rw [← Real.rpow_natCast (N ^ ((1 : ℝ) / 2)) 12, ← Real.rpow_mul hNn]
    norm_num
  have ht1 : M ^ 11 * N ^ 12 ≤ T ^ 12 := by
    have hle : M ^ ((11 : ℝ) / 12) * N ≤ T := by rw [hT]; linarith
    calc M ^ 11 * N ^ 12 = (M ^ ((11 : ℝ) / 12) * N) ^ 12 := by
          rw [mul_pow, hp1]
      _ ≤ T ^ 12 := pow_le_pow_left₀ (by positivity) hle 12
  have ht2 : M ^ 14 * N ^ 9 ≤ T ^ 12 := by
    have hle : M ^ ((7 : ℝ) / 6) * N ^ ((3 : ℝ) / 4) ≤ T := by rw [hT]; linarith
    calc M ^ 14 * N ^ 9 = (M ^ ((7 : ℝ) / 6) * N ^ ((3 : ℝ) / 4)) ^ 12 := by
          rw [mul_pow, hp2, hq1]
      _ ≤ T ^ 12 := pow_le_pow_left₀ (by positivity) hle 12
  have ht3 : M ^ 16 * N ^ 6 ≤ T ^ 12 := by
    have hle : M ^ ((4 : ℝ) / 3) * N ^ ((1 : ℝ) / 2) ≤ T := by rw [hT]; linarith
    calc M ^ 16 * N ^ 6 = (M ^ ((4 : ℝ) / 3) * N ^ ((1 : ℝ) / 2)) ^ 12 := by
          rw [mul_pow, hp3, hq2]
      _ ≤ T ^ 12 := pow_le_pow_left₀ (by positivity) hle 12
  -- the `Q ^ 12` bound
  have hstep1 : Q ^ 12 ≤ (9 * M) ^ 10 * S6 ^ 2 := by
    have hAA : ((9 * M) ^ ((5 : ℝ) / 6)) ^ 12 = (9 * M) ^ 10 := by
      rw [← Real.rpow_natCast ((9 * M) ^ ((5 : ℝ) / 6)) 12, ← Real.rpow_mul (by positivity)]
      norm_num
    have hBB : (S6 ^ ((1 : ℝ) / 6)) ^ 12 = S6 ^ 2 := by
      rw [← Real.rpow_natCast (S6 ^ ((1 : ℝ) / 6)) 12, ← Real.rpow_mul hS6]
      norm_num
    calc Q ^ 12 ≤ ((9 * M) ^ ((5 : ℝ) / 6) * S6 ^ ((1 : ℝ) / 6)) ^ 12 :=
          pow_le_pow_left₀ hQ h1 12
      _ = (9 * M) ^ 10 * S6 ^ 2 := by rw [mul_pow, hAA, hBB]
  have hK1' : K1 ≤ C2 * N ^ 6 * L ^ B2 :=
    h3.trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow hlog1nn hlog1 (le_of_lt hB2)) (by positivity))
  have hK2' : K2 ≤ C1 * (N ^ 6 * M + M ^ 4 * N ^ 3 + M ^ 6) * (6 ^ A1 * L ^ A1) := by
    refine h4.trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
    calc (Real.log (M * N ^ 6 + 2)) ^ A1 ≤ (6 * L) ^ A1 :=
          Real.rpow_le_rpow (le_of_lt (Real.log_pos (by nlinarith [mul_nonneg hMn (pow_nonneg hNn 6)]))) hlog2 (le_of_lt hA1)
      _ = 6 ^ A1 * L ^ A1 := Real.mul_rpow (by norm_num : (0:ℝ) ≤ 6) hLnn
  have hQ12 : Q ^ 12 ≤ (9 ^ 10 * 6 ^ A1 * C1 * C2) *
      (M ^ 10 * N ^ 6 * (N ^ 6 * M + M ^ 4 * N ^ 3 + M ^ 6)) * L ^ (A1 + B2) := by
    have hmul : K1 * K2 ≤ (C2 * N ^ 6 * L ^ B2) * (C1 * (N ^ 6 * M + M ^ 4 * N ^ 3 + M ^ 6)
        * (6 ^ A1 * L ^ A1)) :=
      mul_le_mul hK1' hK2' hK2 (by positivity)
    calc Q ^ 12 ≤ (9 * M) ^ 10 * S6 ^ 2 := hstep1
      _ ≤ (9 * M) ^ 10 * (K1 * K2) := mul_le_mul_of_nonneg_left h2 (by positivity)
      _ ≤ (9 * M) ^ 10 * ((C2 * N ^ 6 * L ^ B2) * (C1 * (N ^ 6 * M + M ^ 4 * N ^ 3 + M ^ 6)
            * (6 ^ A1 * L ^ A1))) := mul_le_mul_of_nonneg_left hmul (by positivity)
      _ = (9 ^ 10 * 6 ^ A1 * C1 * C2) * (M ^ 10 * N ^ 6 * (N ^ 6 * M + M ^ 4 * N ^ 3 + M ^ 6))
            * L ^ (A1 + B2) := by
          have hLc : L ^ B2 * L ^ A1 = L ^ (A1 + B2) := by
            rw [← Real.rpow_add hLpos, show B2 + A1 = A1 + B2 by ring]
          rw [hLc.symm, mul_pow]
          ring_nf
  have hT12 : M ^ 10 * N ^ 6 * (N ^ 6 * M + M ^ 4 * N ^ 3 + M ^ 6) ≤ 3 * T ^ 12 := by
    have e : M ^ 10 * N ^ 6 * (N ^ 6 * M + M ^ 4 * N ^ 3 + M ^ 6)
        = M ^ 11 * N ^ 12 + M ^ 14 * N ^ 9 + M ^ 16 * N ^ 6 := by ring
    rw [e]
    linarith [ht1, ht2, ht3, hTnn]
  have hfinal : Q ^ 12 ≤ ((3 * 9 ^ 10 * 6 ^ A1 * C1 * C2) ^ ((1 : ℝ) / 12) * T
      * L ^ ((A1 + B2) / 12)) ^ 12 := by
    have hC12 : ((3 * 9 ^ 10 * 6 ^ A1 * C1 * C2) ^ ((1 : ℝ) / 12)) ^ 12
        = 3 * 9 ^ 10 * 6 ^ A1 * C1 * C2 := by
      rw [← Real.rpow_natCast ((3 * 9 ^ 10 * 6 ^ A1 * C1 * C2) ^ ((1 : ℝ) / 12)) 12,
        ← Real.rpow_mul (by positivity)]
      norm_num
    have hL12 : (L ^ ((A1 + B2) / 12)) ^ 12 = L ^ (A1 + B2) := by
      rw [← Real.rpow_natCast (L ^ ((A1 + B2) / 12)) 12, ← Real.rpow_mul hLnn,
        show ((A1 + B2) / 12 * ((12 : ℕ) : ℝ)) = A1 + B2 by push_cast; ring]
    rw [mul_pow, mul_pow, hC12, hL12]
    refine hQ12.trans ?_
    have hc : (0 : ℝ) ≤ 9 ^ 10 * 6 ^ A1 * C1 * C2 := by positivity
    have hLp : (0 : ℝ) ≤ L ^ (A1 + B2) := Real.rpow_nonneg hLnn _
    calc (9 ^ 10 * 6 ^ A1 * C1 * C2) * (M ^ 10 * N ^ 6 * (N ^ 6 * M + M ^ 4 * N ^ 3 + M ^ 6))
          * L ^ (A1 + B2)
        ≤ (9 ^ 10 * 6 ^ A1 * C1 * C2) * (3 * T ^ 12) * L ^ (A1 + B2) := by
          gcongr
      _ = 3 * 9 ^ 10 * 6 ^ A1 * C1 * C2 * T ^ 12 * L ^ (A1 + B2) := by ring
  have hRnn : 0 ≤ (3 * 9 ^ 10 * 6 ^ A1 * C1 * C2) ^ ((1 : ℝ) / 12) * T * L ^ ((A1 + B2) / 12) :=
    mul_nonneg (mul_nonneg (Real.rpow_nonneg (by positivity) _) hTnn) (Real.rpow_nonneg hLnn _)
  exact (pow_le_pow_iff_left₀ hQ hRnn (show (12 : ℕ) ≠ 0 by norm_num)).mp hfinal


/-! ## The main chain -/

lemma chain_aux {C1 A1 C2 B2 : ℝ} (hC1 : 0 < C1) (hA1 : 0 < A1) (hC2 : 0 < C2) (hB2 : 0 < B2)
    (hms : ∀ (M N : ℝ) (Rw Rz : ℤ) (a : GaussianInt → ℂ), 1 ≤ M → 1 ≤ N →
      (∀ w, a w ≠ 0 → Work.FIPlan.IsPrimary w ∧ IsCoprime w.re w.im ∧ (Work.FIPlan.gnorm w : ℝ) ≤ M) →
      (∀ w, ‖a w‖ ≤ 1) →
      (∑ z ∈ (Work.FIPlan.gBox Rz).filter (fun z => (Work.FIPlan.gnorm z : ℝ) ≤ N),
          ‖∑ w ∈ Work.FIPlan.gBox Rw, a w * ((DirichletSym w z : ℤ) : ℂ)‖ ^ 2)
        ≤ C1 * (N * M + M ^ 4 * Real.sqrt N + M ^ 6) * (Real.log (M * N + 2)) ^ A1)
    (hconv : ∀ (N : ℝ) (R : ℤ) (β : GaussianInt → ℂ), 1 ≤ N →
      (∀ z, β z ≠ 0 → (Work.FIPlan.gnorm z : ℝ) ≤ N) →
      (∀ z, β z ≠ 0 → z ∈ Work.FIPlan.gBox R) →
      (∀ z, ‖β z‖ ≤ 1) →
      (∑ u ∈ (Work.FIArea7.gDisc ⌈N ^ 3⌉ (N ^ 6)).filter (fun u => u ≠ 0),
          ‖Work.FIArea7.conv6 R β u‖ ^ 2)
        ≤ C2 * N ^ 6 * (Real.log (N + 2)) ^ B2)
    (M N : ℝ) (hM : 1 ≤ M) (hN : 1 ≤ N) (Rw Rz : ℤ) (α β : GaussianInt → ℂ)
    (hα1 : ∀ w, ‖α w‖ ≤ 1) (hβ1 : ∀ z, ‖β z‖ ≤ 1)
    (hαsupp : ∀ w, α w ≠ 0 → Work.FIPlan.IsPrimary w ∧ IsCoprime w.re w.im ∧
      (Work.FIPlan.gnorm w : ℝ) ≤ M)
    (hβsupp : ∀ z, β z ≠ 0 → (Work.FIPlan.gnorm z : ℝ) ≤ N) :
    ‖QBilin Rw Rz α β‖
      ≤ (4 ^ ((1 : ℝ) / 6) * 9 ^ ((11 : ℝ) / 6) + (3 * 9 ^ 10 * 6 ^ A1 * C1 * C2)
          ^ ((1 : ℝ) / 12)) *
        (M ^ ((11 : ℝ) / 12) * N + M ^ ((7 : ℝ) / 6) * N ^ ((3 : ℝ) / 4)
          + M ^ ((4 : ℝ) / 3) * N ^ ((1 : ℝ) / 2)) *
        (Real.log (M * N + 2)) ^ ((A1 + B2) / 12) := by
  classical
  have hMn : (0 : ℝ) ≤ M := by linarith
  have hNn : (0 : ℝ) ≤ N := by linarith
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
  -- ### Step C: the `u = 0` term, then Cauchy–Schwarz away from `u = 0`
  set Ut' : Finset GaussianInt := Ut.filter (fun u => u ≠ 0) with hUt'
  have hUt'sub : Ut' ⊆ Ut := by rw [hUt']; exact Finset.filter_subset _ _
  set K1 : ℝ := ∑ u ∈ Ut', ‖Work.FIArea7.conv6 Rz β₀ u‖ ^ 2 with hK1
  set K2 : ℝ := ∑ u ∈ Ut', ‖Aa u‖ ^ 2 with hK2
  have hK1nn : 0 ≤ K1 := by rw [hK1]; positivity
  have hK2nn : 0 ≤ K2 := by rw [hK2]; positivity
  -- the `u = 0` coefficient of the `6`-fold convolution is at most `(9N)^6`
  have hconv0 : ‖Work.FIArea7.conv6 Rz β₀ 0‖ ≤ (9 * N) ^ 6 := by
    have h1 : ‖Work.FIArea7.conv6 Rz β₀ 0‖
        ≤ ∑ t ∈ Work.FIArea7.boxTup 6 Rz, ∏ i : Fin 6, ‖β₀ (t i)‖ := by
      rw [Work.FIArea7.conv6]
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum (fun t _ => ?_))
      by_cases h : Work.FIArea7.tupProd t = 0
      · rw [if_pos h, norm_prod]
      · rw [if_neg h]
        simp only [norm_zero]
        exact Finset.prod_nonneg (fun i _ => norm_nonneg _)
    have h2 : (∑ t ∈ Work.FIArea7.boxTup 6 Rz, ∏ i : Fin 6, ‖β₀ (t i)‖)
        = (∑ z ∈ Work.FIPlan.gBox Rz, ‖β₀ z‖) ^ 6 := by
      rw [Work.FIArea7.boxTup,
        Finset.sum_prod_piFinset (Work.FIPlan.gBox Rz) (fun (_ : Fin 6) (z : GaussianInt) => ‖β₀ z‖)]
      simp
    have h3 : (∑ z ∈ Work.FIPlan.gBox Rz, ‖β₀ z‖) ≤ 9 * N := by
      have hsplit2 : (∑ z ∈ Work.FIPlan.gBox Rz, ‖β₀ z‖)
          = ∑ z ∈ (Work.FIPlan.gBox Rz).filter (fun z => (Work.FIPlan.gnorm z : ℝ) ≤ N),
              ‖β₀ z‖ := by
        refine (Finset.sum_subset (Finset.filter_subset _ _) ?_).symm
        intro z hz hz'
        have hz0 : β₀ z = 0 := by
          by_contra hne
          exact hz' (Finset.mem_filter.mpr ⟨hz, hβ0supp z hne⟩)
        simp [hz0]
      rw [hsplit2]
      calc ∑ z ∈ (Work.FIPlan.gBox Rz).filter (fun z => (Work.FIPlan.gnorm z : ℝ) ≤ N),
            ‖β₀ z‖
          ≤ ∑ _z ∈ (Work.FIPlan.gBox Rz).filter (fun z => (Work.FIPlan.gnorm z : ℝ) ≤ N),
              (1 : ℝ) := Finset.sum_le_sum (fun z _ => hβ0le z)
        _ = (((Work.FIPlan.gBox Rz).filter (fun z => (Work.FIPlan.gnorm z : ℝ) ≤ N)).card : ℝ) := by
              simp
        _ ≤ 9 * N := by
              exact_mod_cast cardDiscBoxLe Rz N hN
    calc ‖Work.FIArea7.conv6 Rz β₀ 0‖ ≤ _ := h1
      _ = (∑ z ∈ Work.FIPlan.gBox Rz, ‖β₀ z‖) ^ 6 := h2
      _ ≤ (9 * N) ^ 6 := pow_le_pow_left₀ (by positivity) h3 6
  -- the `w = 0` value of the inner sum: only `w = 1` can contribute, and `ξ_1(0) = 1`
  have hA0 : ‖Aa 0‖ ≤ 4 := by
    have hAa0 : Aa 0 = ∑ w ∈ Work.FIPlan.gBox Rw,
        c w * ((DirichletSym w 0 : ℤ) : ℂ) := by simp only [hAa]
    rw [hAa0]
    have hzero : ∀ w ∈ Work.FIPlan.gBox Rw, w ≠ 1 →
        c w * ((DirichletSym w 0 : ℤ) : ℂ) = 0 := by
      intro w _ hw
      by_cases hle1 : Work.FIPlan.gnorm w ≤ 1
      · have hcw : c w = 0 := by
          by_contra hcne
          have hwS : w ∈ S := by
            by_contra hcon
            exact hcne (hc_zero w hcon)
          rw [hS, Finset.mem_filter] at hwS
          have hp := (hαsupp w hwS.2).1
          have hgn1 : Work.FIPlan.gnorm w = 1 := by
            rcases Nat.eq_zero_or_pos (Work.FIPlan.gnorm w) with h0 | hpos
            · exfalso
              obtain ⟨ho', -, -⟩ := hp
              rw [Work.FIArea7.gnorm_eq_zero_iff.mp h0, Zsqrtd.re_zero] at ho'
              obtain ⟨k, hk⟩ := ho'
              omega
            · omega
          exact hw (eq_one_of_primary_gnorm_one hp hgn1)
        rw [hcw, zero_mul]
      · have h0 : DirichletSym w 0 = 0 := by
          simpa [DirichletSym] using jacobiSym.zero_left (by omega : 1 < Work.FIPlan.gnorm w)
        rw [h0]; simp
    have hone : DirichletSym (1 : GaussianInt) 0 = 1 := by
      have hgn : Work.FIPlan.gnorm (1 : GaussianInt) = 1 := by
        rw [Work.FIPlan.gnorm, Zsqrtd.norm_one]; rfl
      rw [DirichletSym, hgn, mul_zero, Zsqrtd.re_zero]
      exact jacobiSym.one_right 0
    rw [Finset.sum_eq_single (1 : GaussianInt) hzero (by
      intro h1
      have hc1 : c (1 : GaussianInt) = 0 := hc_zero 1 (by
        intro h1S
        rw [hS, Finset.mem_filter] at h1S
        exact h1 h1S.1)
      rw [hc1, zero_mul]), hone]
    simp only [Int.cast_one, Complex.ofReal_one, mul_one]
    exact le_trans (hc_le 1) (by norm_num)
  have hsplit : ∑ u ∈ Ut, Work.FIArea7.conv6 Rz β₀ u * Aa u
      = (if (0 : GaussianInt) ∈ Ut then Work.FIArea7.conv6 Rz β₀ 0 * Aa 0 else 0)
        + ∑ u ∈ Ut', Work.FIArea7.conv6 Rz β₀ u * Aa u := by
    have h1 : ∑ u ∈ Ut', Work.FIArea7.conv6 Rz β₀ u * Aa u
        = ∑ u ∈ Ut, if u ≠ 0 then Work.FIArea7.conv6 Rz β₀ u * Aa u else 0 := by
      rw [hUt', Finset.sum_filter]
    have h2 : ∑ u ∈ Ut, Work.FIArea7.conv6 Rz β₀ u * Aa u
        = (∑ u ∈ Ut, if u ≠ 0 then Work.FIArea7.conv6 Rz β₀ u * Aa u else 0)
          + ∑ u ∈ Ut, if u = 0 then Work.FIArea7.conv6 Rz β₀ u * Aa u else 0 := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl (fun u _ => ?_)
      by_cases h : u = 0 <;> simp [h]
    have h3 : (∑ u ∈ Ut, if u = 0 then Work.FIArea7.conv6 Rz β₀ u * Aa u else 0)
        = (if (0 : GaussianInt) ∈ Ut then Work.FIArea7.conv6 Rz β₀ 0 * Aa 0 else 0) :=
      Finset.sum_ite_eq' Ut 0 (fun u => Work.FIArea7.conv6 Rz β₀ u * Aa u)
    rw [h2, h3, h1]
    ring
  set X : ℝ := ‖∑ u ∈ Ut', Work.FIArea7.conv6 Rz β₀ u * Aa u‖ with hX
  have hS6le : S6 ≤ 4 * (9 * N) ^ 6 + X := by
    have hmod : S6 = ‖∑ u ∈ Ut, Work.FIArea7.conv6 Rz β₀ u * Aa u‖ := by
      rw [← hS6id, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hS6nn]
    rw [hmod, hsplit]
    rw [hX]
    refine (norm_add_le _ _).trans ?_
    have hterm : ‖(if (0 : GaussianInt) ∈ Ut then Work.FIArea7.conv6 Rz β₀ 0 * Aa 0 else 0)‖
        ≤ 4 * (9 * N) ^ 6 := by
      by_cases h : (0 : GaussianInt) ∈ Ut
      · rw [if_pos h, norm_mul]
        calc ‖Work.FIArea7.conv6 Rz β₀ 0‖ * ‖Aa 0‖ ≤ (9 * N) ^ 6 * 4 :=
              mul_le_mul hconv0 hA0 (norm_nonneg _) (by positivity)
          _ = 4 * (9 * N) ^ 6 := by ring
      · rw [if_neg h]
        simp only [norm_zero]
        positivity
    linarith [hterm, norm_nonneg (∑ u ∈ Ut', Work.FIArea7.conv6 Rz β₀ u * Aa u), hX]
  have hX2 : X ^ 2 ≤ K1 * K2 := by
    have h1 : ‖∑ u ∈ Ut', Work.FIArea7.conv6 Rz β₀ u * Aa u‖
        ≤ ∑ u ∈ Ut', ‖Work.FIArea7.conv6 Rz β₀ u‖ * ‖Aa u‖ := by
      calc ‖∑ u ∈ Ut', Work.FIArea7.conv6 Rz β₀ u * Aa u‖
          ≤ ∑ u ∈ Ut', ‖Work.FIArea7.conv6 Rz β₀ u * Aa u‖ := norm_sum_le _ _
        _ = ∑ u ∈ Ut', ‖Work.FIArea7.conv6 Rz β₀ u‖ * ‖Aa u‖ := by simp
    have h2 := Finset.sum_mul_sq_le_sq_mul_sq Ut'
      (fun u => ‖Work.FIArea7.conv6 Rz β₀ u‖) (fun u => ‖Aa u‖)
    rw [hX]
    calc (‖∑ u ∈ Ut', Work.FIArea7.conv6 Rz β₀ u * Aa u‖) ^ 2
        ≤ (∑ u ∈ Ut', ‖Work.FIArea7.conv6 Rz β₀ u‖ * ‖Aa u‖) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) h1 2
      _ ≤ (∑ u ∈ Ut', ‖Work.FIArea7.conv6 Rz β₀ u‖ ^ 2) * (∑ u ∈ Ut', ‖Aa u‖ ^ 2) := h2
      _ = K1 * K2 := by rw [hK1, hK2]
  -- ### Step D: the two analytic inputs
  have hK1le : K1 ≤ C2 * N ^ 6 * (Real.log (N + 2)) ^ B2 := by
    rw [hK1, hUt', hUt]
    exact hconv N Rz β₀ hN hβ0supp hβ0box hβ0le
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
    have hs : Real.sqrt (N ^ 6) = N ^ 3 := by
      rw [show N ^ 6 = (N ^ 3) ^ 2 by ring, Real.sqrt_sq (by positivity)]
    have hx := hms M (N ^ 6) Rw ⌈N ^ 3⌉ c hM hN6 hcsupp hc_le
    rw [hs] at hx
    have hx' : (∑ u ∈ Ut, ‖Aa u‖ ^ 2) ≤ C1 * (N ^ 6 * M + M ^ 4 * N ^ 3 + M ^ 6)
        * (Real.log (M * N ^ 6 + 2)) ^ A1 := by
      rw [hUt, hAa]; exact hx
    exact (Finset.sum_le_sum_of_subset_of_nonneg hUt'sub (fun u _ _ => by positivity)).trans hx'
  -- ### Step E: final arithmetic
  set Tsum : ℝ := M ^ ((11 : ℝ) / 12) * N + M ^ ((7 : ℝ) / 6) * N ^ ((3 : ℝ) / 4)
      + M ^ ((4 : ℝ) / 3) * N ^ ((1 : ℝ) / 2) with hTsum
  have hTnn : 0 ≤ Tsum := by
    rw [hTsum]
    have a1 := Real.rpow_nonneg hMn (11 / 12 : ℝ)
    have a2 := Real.rpow_nonneg hMn (7 / 6 : ℝ)
    have a3 := Real.rpow_nonneg hMn (4 / 3 : ℝ)
    have b1 := Real.rpow_nonneg hNn (3 / 4 : ℝ)
    have b2 := Real.rpow_nonneg hNn (1 / 2 : ℝ)
    positivity
  set Lam : ℝ := (Real.log (M * N + 2)) ^ ((A1 + B2) / 12) with hLam
  have hL1 : (1 : ℝ) ≤ Real.log (M * N + 2) := by
    have h3 : (3 : ℝ) ≤ M * N + 2 := by nlinarith
    have h13 : (1 : ℝ) ≤ Real.log 3 :=
      (Real.le_log_iff_exp_le (by norm_num)).mpr Real.exp_one_lt_three.le
    exact h13.trans (Real.log_le_log (by norm_num) h3)
  have hLam1 : (1 : ℝ) ≤ Lam := by
    rw [hLam]
    exact Real.one_le_rpow hL1 (by positivity)
  have hLamnn : (0 : ℝ) ≤ Lam := le_trans zero_le_one hLam1
  have hXnn : (0 : ℝ) ≤ X := norm_nonneg _
  have hA6' : ((9 * N) ^ 6 : ℝ) ^ ((1 : ℝ) / 6) = 9 * N := by
    rw [← Real.rpow_natCast (9 * N) 6, ← Real.rpow_mul (by positivity : (0:ℝ) ≤ 9 * N)]
    norm_num
  have hA6 : (4 * (9 * N) ^ 6) ^ ((1 : ℝ) / 6) = 4 ^ ((1 : ℝ) / 6) * (9 * N) := by
    rw [Real.mul_rpow (by norm_num : (0:ℝ) ≤ 4) (by positivity : (0:ℝ) ≤ (9 * N) ^ 6), hA6']
  have hpartA : (9 * M) ^ ((5 : ℝ) / 6) * (4 * (9 * N) ^ 6) ^ ((1 : ℝ) / 6)
      ≤ 4 ^ ((1 : ℝ) / 6) * 9 ^ ((11 : ℝ) / 6) * Tsum * Lam := by
    have hMrp : M ^ ((5 : ℝ) / 6) ≤ M ^ ((11 : ℝ) / 12) :=
      Real.rpow_le_rpow_of_exponent_le hM (by norm_num)
    have h9 : (9 : ℝ) ^ ((5 : ℝ) / 6) * 9 = 9 ^ ((11 : ℝ) / 6) := by
      have h : (9 : ℝ) ^ ((5 : ℝ) / 6) * 9 ^ (1 : ℝ) = 9 ^ ((5 : ℝ) / 6 + 1) :=
        (Real.rpow_add (by norm_num : (0:ℝ) < 9) _ _).symm
      rw [Real.rpow_one] at h
      rw [h, show (5 : ℝ) / 6 + 1 = (11 : ℝ) / 6 by norm_num]
    have h4 : M ^ ((11 : ℝ) / 12) * N ≤ Tsum := by
      rw [hTsum]
      have hh1 : (0 : ℝ) ≤ M ^ ((7 : ℝ) / 6) * N ^ ((3 : ℝ) / 4) := by positivity
      have hh2 : (0 : ℝ) ≤ M ^ ((4 : ℝ) / 3) * N ^ ((1 : ℝ) / 2) := by positivity
      linarith
    have hpos : (0 : ℝ) ≤ 4 ^ ((1 : ℝ) / 6) * 9 ^ ((11 : ℝ) / 6) := by positivity
    have hEq : (9 * M) ^ ((5 : ℝ) / 6) * (4 * (9 * N) ^ 6) ^ ((1 : ℝ) / 6)
        = 4 ^ ((1 : ℝ) / 6) * 9 ^ ((11 : ℝ) / 6) * (M ^ ((5 : ℝ) / 6) * N) := by
      rw [hA6, Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 9) hMn, ← h9]
      ring
    rw [hEq]
    calc 4 ^ ((1 : ℝ) / 6) * 9 ^ ((11 : ℝ) / 6) * (M ^ ((5 : ℝ) / 6) * N)
        ≤ 4 ^ ((1 : ℝ) / 6) * 9 ^ ((11 : ℝ) / 6) * (M ^ ((11 : ℝ) / 12) * N) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hMrp hNn) hpos
      _ ≤ 4 ^ ((1 : ℝ) / 6) * 9 ^ ((11 : ℝ) / 6) * (Lam * Tsum) :=
          mul_le_mul_of_nonneg_left (le_trans h4 (by
            calc Tsum = 1 * Tsum := (one_mul Tsum).symm
              _ ≤ Lam * Tsum := mul_le_mul_of_nonneg_right hLam1 hTnn)) hpos
      _ = 4 ^ ((1 : ℝ) / 6) * 9 ^ ((11 : ℝ) / 6) * Tsum * Lam := by ring
  have hpartB : (9 * M) ^ ((5 : ℝ) / 6) * X ^ ((1 : ℝ) / 6)
      ≤ (3 * 9 ^ 10 * 6 ^ A1 * C1 * C2) ^ ((1 : ℝ) / 12) * Tsum * Lam := by
    have h := final_arith hC1 hC2 hA1 hB2 hM hN (by positivity) hXnn hK1nn hK2nn
      (le_refl ((9 * M) ^ ((5 : ℝ) / 6) * X ^ ((1 : ℝ) / 6))) hX2 hK1le hK2le
    rw [hTsum, hLam]
    exact h
  have hXle : S6 ^ ((1 : ℝ) / 6)
      ≤ (4 * (9 * N) ^ 6) ^ ((1 : ℝ) / 6) + X ^ ((1 : ℝ) / 6) := by
    refine (Real.rpow_le_rpow hS6nn hS6le (by norm_num)).trans ?_
    exact Real.rpow_add_le_add_rpow (by positivity) hXnn (by norm_num) (by norm_num)
  calc ‖QBilin Rw Rz α β‖ ≤ (9 * M) ^ ((5 : ℝ) / 6) * S6 ^ ((1 : ℝ) / 6) := hQle
    _ ≤ (9 * M) ^ ((5 : ℝ) / 6) * ((4 * (9 * N) ^ 6) ^ ((1 : ℝ) / 6) + X ^ ((1 : ℝ) / 6)) :=
        mul_le_mul_of_nonneg_left hXle (by positivity)
    _ = (9 * M) ^ ((5 : ℝ) / 6) * (4 * (9 * N) ^ 6) ^ ((1 : ℝ) / 6)
          + (9 * M) ^ ((5 : ℝ) / 6) * X ^ ((1 : ℝ) / 6) := by ring
    _ ≤ 4 ^ ((1 : ℝ) / 6) * 9 ^ ((11 : ℝ) / 6) * Tsum * Lam
          + (3 * 9 ^ 10 * 6 ^ A1 * C1 * C2) ^ ((1 : ℝ) / 12) * Tsum * Lam :=
        add_le_add hpartA hpartB
    _ = (4 ^ ((1 : ℝ) / 6) * 9 ^ ((11 : ℝ) / 6)
          + (3 * 9 ^ 10 * 6 ^ A1 * C1 * C2) ^ ((1 : ℝ) / 12)) * Tsum * Lam := by ring
    _ = (4 ^ ((1 : ℝ) / 6) * 9 ^ ((11 : ℝ) / 6)
          + (3 * 9 ^ 10 * 6 ^ A1 * C1 * C2) ^ ((1 : ℝ) / 12))
        * (M ^ ((11 : ℝ) / 12) * N + M ^ ((7 : ℝ) / 6) * N ^ ((3 : ℝ) / 4)
          + M ^ ((4 : ℝ) / 3) * N ^ ((1 : ℝ) / 2))
        * (Real.log (M * N + 2)) ^ ((A1 + B2) / 12) := by rw [hTsum, hLam]

/-! ## The target -/

/-- ***FI* (21.9): the `k = 6` Hölder step**, with a logarithmic loss in place of `(MN)^ε`.

For `α` supported on primary primitive `w` with `|w|² ≤ M`, `|α| ≤ 1`, and `β` supported on
`|z|² ≤ N`, `|β| ≤ 1`:

  `‖QBilin Rw Rz α β‖ ≤ C (M^{11/12}N + M^{7/6}N^{3/4} + M^{4/3}N^{1/2})(log(MN+2))^A`.

Proof (*FI* pp. 1026–1027): Hölder with `k = 6` over `w ∈ coeffSupport` gives
`|Q|⁶ ≤ (#supp)⁵·Σ_w |B(w)|⁶` with `B(w) = Σ_z β_z ξ_w(z)`; `Σ_w|B|⁶ = Q(α̃, β⁶)` where `α̃` is the
unimodular phase of `B(w)⁶` and `β⁶` is the 6-fold product-convolution of `β` (multiplicativity:
`dirichletSym_mul`); Cauchy in `z` on `Q(α̃,β⁶)` and then `meanSquareElem` at `(M, N⁶)`; the
`ℓ²`-norm of `β⁶` is bounded by `sum_convPow_sq_le`:
`Σ_z |β⁶(z)|² ≤ C N⁶ (log(N+2))^B`.  Take the 6th root. -/
theorem qBilin_holder6 : ∃ C A : ℝ, 0 < C ∧ 0 < A ∧
  ∀ (M N : ℝ) (Rw Rz : ℤ) (α β : GaussianInt → ℂ), 1 ≤ M → 1 ≤ N →
    (∀ w, ‖α w‖ ≤ 1) → (∀ z, ‖β z‖ ≤ 1) →
    (∀ w, α w ≠ 0 → Work.FIPlan.IsPrimary w ∧ IsCoprime w.re w.im ∧ (Work.FIPlan.gnorm w : ℝ) ≤ M) →
    (∀ z, β z ≠ 0 → (Work.FIPlan.gnorm z : ℝ) ≤ N) →
    ‖Work.FIArea7.QBilin Rw Rz α β‖ ≤ C * (M ^ ((11:ℝ)/12) * N + M ^ ((7:ℝ)/6) * N ^ ((3:ℝ)/4)
                              + M ^ ((4:ℝ)/3) * N ^ ((1:ℝ)/2)) * (Real.log (M * N + 2)) ^ A
:= by
  sorry

end

end Work.FIArea7
