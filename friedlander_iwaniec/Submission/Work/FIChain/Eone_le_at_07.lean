import Mathlib
import Submission.Work.FIChain.Defs
import Submission.ASP.S40
import Submission.ASP.S31
import Submission.ASP.S22
import Submission.ASP.S21
import Submission.ASP.S35
import Submission.ASP.S36
import Submission.ASP.S34
import Submission.ASP.S33
import Submission.ASP.S32
import Submission.ASP.S9b
import Submission.ASP.S9d
import Submission.ASP.S37
import Submission.ASP_R3
import Submission.Work.FIChain.rMain_cubefree_not4_le
import Submission.Work.FIChain.rMain_cubefree_four_dvd_le
import Submission.Work.FIChain.cubefree_tau_sq_FIr_le

namespace Work.FIChain

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-- The `(R₃)`-type cubefree estimate for the companion's remainder `FIr` at the
`x^{141/200}` cut-off: `∑♭³_{k ≤ N} |r_k(t)| ≤ 3 A(x)(log x)^{-λ}` for every `λ`, provided
`N + 1 ≤ x^{141/200}`.  Opened up from `rMain_cubefree_not4_le` / `…four_dvd_le` plus the
elementary discrepancy `|FIg d − 1| ≤ 1`. -/
theorem FIr_cubefree_sum_le_at_07 (lamm : ℝ) : ∃ X₀ : ℕ,
    ∀ x : ℕ, X₀ ≤ x → ∀ t : ℕ, 2 ≤ t → t ≤ x →
    ∀ N : ℕ, 2 ≤ N → (N : ℝ) + 1 ≤ (x : ℝ) ^ ((141 : ℝ) / 200) →
    (∑ k ∈ (Finset.Icc 1 N).filter Submission.ASP.CubefreeN, |Submission.ASP.FIr k t|)
      ≤ 3 * (Submission.Aseq x : ℝ) * (Real.log (x : ℝ)) ^ (-lamm) := by
  obtain ⟨Xn4, hn4⟩ := rMain_cubefree_not4_le lamm
  obtain ⟨X4d, h4d⟩ := rMain_cubefree_four_dvd_le lamm
  obtain ⟨cA, hcA, XA, hAlow⟩ := Submission.exists_const_mul_rpow_le_Aseq
  obtain ⟨Xpt, -, hpt⟩ := Submission.X2Y4R3.poly_tail_gen 1 ((141 : ℝ) / 200) 0 cA lamm
    (by norm_num) (by norm_num) hcA
  refine ⟨Xn4 + X4d + XA + Xpt + 64, fun x hx t ht2 htx N hN2 hRN => ?_⟩
  have hxn4 : Xn4 ≤ x := by omega
  have hx4d : X4d ≤ x := by omega
  have hxA : XA ≤ x := by omega
  have hxpt : Xpt ≤ x := by omega
  have hx64 : 64 ≤ x := by omega
  have hx1 : (1 : ℝ) ≤ (x : ℝ) := by exact_mod_cast (by omega : 1 ≤ x)
  have hlog1 : (1 : ℝ) ≤ Real.log x := by
    have h3 : (3 : ℝ) ≤ (x : ℝ) := by exact_mod_cast (by omega : 3 ≤ x)
    have he : Real.exp 1 ≤ (x : ℝ) := by linarith [Real.exp_one_lt_three, h3]
    have h := Real.log_le_log (Real.exp_pos 1) he
    rwa [Real.log_exp] at h
  have hlog0 : (0 : ℝ) ≤ Real.log x := Real.log_nonneg hx1
  set M : ℕ := N + 1 with hM
  have hM2 : 2 ≤ M := by omega
  have hM3 : 3 ≤ M := by omega
  have hMle : (M : ℝ) ≤ (x : ℝ) ^ ((141 : ℝ) / 200) := by
    rw [hM]; push_cast; exact hRN
  -- ### the `rMain`-part, split by `4 ∣ ·`
  have hsub1 : (Finset.Icc 1 N).filter Submission.ASP.CubefreeN ⊆
      (Finset.range M).filter Submission.CubefreeD := by
    intro k hk
    rw [Finset.mem_filter] at hk ⊢
    obtain ⟨hkI, hkcf⟩ := hk
    obtain ⟨hk1, hkN⟩ := Finset.mem_Icc.mp hkI
    exact ⟨Finset.mem_range.mpr (by omega), hkcf⟩
  have hsplit_rMain : (∑ k ∈ (Finset.range M).filter Submission.CubefreeD,
      |Submission.ASP.rMain k t|)
      ≤ 2 * ((Submission.Aseq x : ℝ) * (Real.log x) ^ (-lamm)) := by
    have hdisj : Disjoint
        ((Finset.range M).filter (fun k => Submission.CubefreeD k ∧ ¬ 4 ∣ k))
        ((Finset.range M).filter (fun k => Submission.CubefreeD k ∧ 4 ∣ k)) := by
      rw [Finset.disjoint_left]
      intro k hk1 hk2
      rw [Finset.mem_filter] at hk1 hk2
      exact hk1.2.2 hk2.2.2
    have heq : (Finset.range M).filter Submission.CubefreeD
        = ((Finset.range M).filter (fun k => Submission.CubefreeD k ∧ ¬ 4 ∣ k))
          ∪ ((Finset.range M).filter (fun k => Submission.CubefreeD k ∧ 4 ∣ k)) := by
      ext k
      simp only [Finset.mem_filter, Finset.mem_union]
      constructor
      · rintro ⟨hm, hc⟩
        by_cases h4 : 4 ∣ k
        · exact Or.inr ⟨hm, hc, h4⟩
        · exact Or.inl ⟨hm, hc, h4⟩
      · rintro (⟨hm, hc, -⟩ | ⟨hm, hc, -⟩) <;> exact ⟨hm, hc⟩
    rw [heq, Finset.sum_union hdisj]
    have e1 : (∑ k ∈ (Finset.range M).filter (fun k => Submission.CubefreeD k ∧ ¬ 4 ∣ k),
        |Submission.ASP.rMain k t|) ≤ (Submission.Aseq x : ℝ) * (Real.log x) ^ (-lamm) := by
      simpa [Submission.ASP.rMain, Submission.ASP.FIg] using hn4 x hxn4 t ht2 htx M hM2 hMle
    have e2 : (∑ k ∈ (Finset.range M).filter (fun k => Submission.CubefreeD k ∧ 4 ∣ k),
        |Submission.ASP.rMain k t|) ≤ (Submission.Aseq x : ℝ) * (Real.log x) ^ (-lamm) := by
      simpa [Submission.ASP.rMain, Submission.ASP.FIg] using h4d x hx4d t ht2 htx M hM3 hMle
    linarith [e1, e2]
  -- ### the `g`-discrepancy part
  have hsplit_g : (∑ k ∈ (Finset.Icc 1 N).filter Submission.ASP.CubefreeN,
      |Submission.ASP.FIg k - 1|) ≤ (N : ℝ) := by
    refine le_trans (Finset.sum_le_sum (fun k _ => Submission.ASP.FIg_sub_one_abs_le k)) ?_
    rw [Finset.sum_const, nsmul_eq_mul, mul_one]
    have hc : (((Finset.Icc 1 N).filter Submission.ASP.CubefreeN).card : ℕ) ≤ N := by
      refine le_trans (Finset.card_filter_le _ _) ?_
      rw [Nat.card_Icc]; omega
    exact_mod_cast hc
  have hNle : (N : ℝ) ≤ (Submission.Aseq x : ℝ) * (Real.log x) ^ (-lamm) := by
    have hNx : (N : ℝ) ≤ (x : ℝ) ^ ((141 : ℝ) / 200) := by linarith [hRN]
    have hpt'' : (x : ℝ) ^ ((141 : ℝ) / 200)
        ≤ cA * (x : ℝ) ^ ((3 : ℝ) / 4) * (Real.log x) ^ (-lamm) := by
      simpa using hpt x hxpt
    calc (N : ℝ) ≤ cA * (x : ℝ) ^ ((3 : ℝ) / 4) * (Real.log x) ^ (-lamm) :=
          le_trans hNx hpt''
      _ ≤ (Submission.Aseq x : ℝ) * (Real.log x) ^ (-lamm) :=
          mul_le_mul_of_nonneg_right (hAlow x hxA) (Real.rpow_nonneg hlog0 _)
  -- ### assemble
  calc (∑ k ∈ (Finset.Icc 1 N).filter Submission.ASP.CubefreeN, |Submission.ASP.FIr k t|)
      ≤ (∑ k ∈ (Finset.range M).filter Submission.CubefreeD, |Submission.ASP.rMain k t|)
        + (N : ℝ) := by
        calc (∑ k ∈ (Finset.Icc 1 N).filter Submission.ASP.CubefreeN, |Submission.ASP.FIr k t|)
            ≤ ∑ k ∈ (Finset.Icc 1 N).filter Submission.ASP.CubefreeN,
                (|Submission.ASP.rMain k t| + |Submission.ASP.FIg k - 1|) :=
              Finset.sum_le_sum (fun k _ => Submission.ASP.FIr_abs_le k t)
          _ = (∑ k ∈ (Finset.Icc 1 N).filter Submission.ASP.CubefreeN, |Submission.ASP.rMain k t|)
              + ∑ k ∈ (Finset.Icc 1 N).filter Submission.ASP.CubefreeN,
                |Submission.ASP.FIg k - 1| := Finset.sum_add_distrib
          _ ≤ (∑ k ∈ (Finset.range M).filter Submission.CubefreeD, |Submission.ASP.rMain k t|)
              + ∑ k ∈ (Finset.Icc 1 N).filter Submission.ASP.CubefreeN,
                |Submission.ASP.FIg k - 1| :=
              add_le_add (Finset.sum_le_sum_of_subset_of_nonneg hsub1
                (fun k _ _ => abs_nonneg _)) le_rfl
          _ ≤ (∑ k ∈ (Finset.range M).filter Submission.CubefreeD, |Submission.ASP.rMain k t|)
              + (N : ℝ) := add_le_add le_rfl hsplit_g
    _ ≤ 2 * ((Submission.Aseq x : ℝ) * (Real.log x) ^ (-lamm))
        + (Submission.Aseq x : ℝ) * (Real.log x) ^ (-lamm) := add_le_add hsplit_rMain hNle
    _ = 3 * (Submission.Aseq x : ℝ) * (Real.log x) ^ (-lamm) := by ring

theorem Eone_le_at_07 (lam : ℝ) : ∃ X₀ : ℕ, ∃ C : ℝ, 0 < C ∧
    ∀ x : ℕ, X₀ ≤ x → ∀ t L : ℕ, 2 ≤ t → t ≤ x → 1 ≤ L →
      ((⌈(x : ℝ) ^ ((7 : ℝ) / 10)⌉₊ * L ^ 2 : ℕ) : ℝ) + 1 ≤ (x : ℝ) ^ ((141 : ℝ) / 200) →
      Submission.ASP.Eone Submission.ASP.FIr t (⌈(x : ℝ) ^ ((7 : ℝ) / 10)⌉₊) L
        ≤ C * (Submission.Aseq x : ℝ) * (Real.log (x : ℝ)) ^ (-lam) := by
  obtain ⟨Xw, Cw, Bw, hCw, hWbound⟩ := cubefree_tau_sq_FIr_le
  set W0 : ℝ := max Bw 0 + 1 with hW0
  have hW0Bw : Bw ≤ W0 := by rw [hW0]; linarith [le_max_left Bw (0 : ℝ)]
  set lamR : ℝ := W0 + 2 * lam + 10 with hlamR
  obtain ⟨Xr, hr⟩ := FIr_cubefree_sum_le_at_07 lamR
  have hCpos : (0 : ℝ) < Real.sqrt (3 * Cw) := Real.sqrt_pos.mpr (by linarith [hCw])
  refine ⟨Xw + Xr + 64, Real.sqrt (3 * Cw), hCpos, ?_⟩
  intro x hx t L ht2 htx hL1 hR
  have hxw : Xw ≤ x := by omega
  have hxr : Xr ≤ x := by omega
  have hx64 : 64 ≤ x := by omega
  have hx1 : (1 : ℝ) ≤ (x : ℝ) := by exact_mod_cast (by omega : 1 ≤ x)
  have hlog1 : (1 : ℝ) ≤ Real.log x := by
    have h3 : (3 : ℝ) ≤ (x : ℝ) := by exact_mod_cast (by omega : 3 ≤ x)
    have he : Real.exp 1 ≤ (x : ℝ) := by linarith [Real.exp_one_lt_three, h3]
    have h := Real.log_le_log (Real.exp_pos 1) he
    rwa [Real.log_exp] at h
  have hlog0 : (0 : ℝ) ≤ Real.log x := le_trans zero_le_one hlog1
  have hlogpos : (0 : ℝ) < Real.log x := lt_of_lt_of_le zero_lt_one hlog1
  set D : ℕ := ⌈(x : ℝ) ^ ((7 : ℝ) / 10)⌉₊ with hD
  set N : ℕ := D * L ^ 2 with hN
  have hD2 : 2 ≤ D := by
    rw [hD]
    have hlt : (1 : ℝ) < (x : ℝ) ^ ((7 : ℝ) / 10) :=
      Real.one_lt_rpow (by exact_mod_cast (by omega : 1 < x)) (by norm_num)
    have hceil : (1 : ℝ) < ((⌈(x : ℝ) ^ ((7 : ℝ) / 10)⌉₊ : ℕ) : ℝ) :=
      lt_of_lt_of_le hlt (Nat.le_ceil _)
    have : 1 < ⌈(x : ℝ) ^ ((7 : ℝ) / 10)⌉₊ := by exact_mod_cast hceil
    omega
  have hLsq : 1 ≤ L ^ 2 := one_le_pow₀ hL1
  have hN2 : 2 ≤ N := by
    rw [hN]
    calc 2 = 2 * 1 := by ring
      _ ≤ D * L ^ 2 := Nat.mul_le_mul hD2 hLsq
  -- ### the crude `τ²` bound
  have hW : (∑ k ∈ (Finset.Icc 1 N).filter Submission.ASP.CubefreeN,
      ((k.divisors.card : ℝ)) ^ 2 * |Submission.ASP.FIr k t|)
      ≤ Cw * (Submission.Aseq x : ℝ) * (Real.log x) ^ W0 := by
    have hMle' : (((N + 1 : ℕ)) : ℝ) ≤ (x : ℝ) ^ ((141 : ℝ) / 200) := by
      push_cast; exact hR
    have hb := hWbound x hxw t ht2 htx (N + 1) (by omega) hMle'
    have hsub : (Finset.Icc 1 N).filter Submission.ASP.CubefreeN ⊆
        (Finset.Icc 1 (N + 1)).filter
          (fun k => ∀ p ∈ k.primeFactors, k.factorization p ≤ 2) := by
      intro k hk
      rw [Finset.mem_filter] at hk ⊢
      obtain ⟨hkI, hkcf⟩ := hk
      obtain ⟨hk1, hkN⟩ := Finset.mem_Icc.mp hkI
      exact ⟨Finset.mem_Icc.mpr ⟨hk1, by omega⟩, hkcf⟩
    refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg hsub
      (fun k _ _ => mul_nonneg (by positivity) (abs_nonneg _))) ?_
    refine le_trans hb ?_
    exact mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hlog1 hW0Bw) (mul_nonneg hCw.le (Nat.cast_nonneg _))
  -- ### the analytic `(R₃)` bound for `FIr`
  have hR3 : (∑ k ∈ (Finset.Icc 1 N).filter Submission.ASP.CubefreeN,
      |Submission.ASP.FIr k t|) ≤ 3 * (Submission.Aseq x : ℝ) * (Real.log x) ^ (-lamR) :=
    hr x hxr t ht2 htx N hN2 hR
  have hCS := Submission.ASP.Rprime3_le_tau2 (fun k => Submission.ASP.FIr k t) N hW hR3
  -- ### `Eone` as the `τ`-weighted cubefree sum
  have hE1raw := Submission.ASP.E1_le Submission.ASP.FIr t D L
    (X := ∑ k ∈ (Finset.Icc 1 (D * L ^ 2)).filter Submission.ASP.CubefreeN,
      ((k.divisors.card : ℝ)) * |Submission.ASP.FIr k t|) le_rfl
  have hE1 : Submission.ASP.Eone Submission.ASP.FIr t D L
      ≤ ∑ k ∈ (Finset.Icc 1 N).filter Submission.ASP.CubefreeN,
          ((k.divisors.card : ℝ)) * |Submission.ASP.FIr k t| := by
    rw [← hN] at hE1raw
    simpa [Submission.ASP.Eone] using hE1raw
  -- ### the square-root algebra
  have hfinal : Real.sqrt (Cw * (Submission.Aseq x : ℝ) * (Real.log x) ^ W0)
        * Real.sqrt (3 * (Submission.Aseq x : ℝ) * (Real.log x) ^ (-lamR))
      ≤ Real.sqrt (3 * Cw) * (Submission.Aseq x : ℝ) * (Real.log x) ^ (-lam) := by
    have hA0 : (0 : ℝ) ≤ (Submission.Aseq x : ℝ) := Nat.cast_nonneg _
    have hW0nn : (0 : ℝ) ≤ (Real.log x) ^ W0 := Real.rpow_nonneg hlog0 _
    have hP2nn : (0 : ℝ) ≤ (Real.log x) ^ (-lamR) := Real.rpow_nonneg hlog0 _
    have hPnn : (0 : ℝ) ≤ (Real.log x) ^ (-lam) := Real.rpow_nonneg hlog0 _
    have hS1nn : (0 : ℝ) ≤ Cw * (Submission.Aseq x : ℝ) * (Real.log x) ^ W0 :=
      mul_nonneg (mul_nonneg hCw.le hA0) hW0nn
    have hS2nn : (0 : ℝ) ≤ 3 * (Submission.Aseq x : ℝ) * (Real.log x) ^ (-lamR) :=
      mul_nonneg (mul_nonneg (by norm_num) hA0) hP2nn
    have hleft : (0 : ℝ) ≤ Real.sqrt (Cw * (Submission.Aseq x : ℝ) * (Real.log x) ^ W0)
        * Real.sqrt (3 * (Submission.Aseq x : ℝ) * (Real.log x) ^ (-lamR)) := by positivity
    have hright : (0 : ℝ) ≤ Real.sqrt (3 * Cw) * (Submission.Aseq x : ℝ)
        * (Real.log x) ^ (-lam) :=
      mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) hA0) hPnn
    have hpow : (Real.log x) ^ W0 * (Real.log x) ^ (-lamR) = (Real.log x) ^ (-2 * lam - 10) := by
      rw [← Real.rpow_add hlogpos]; congr 1; rw [hlamR]; ring
    have hpow2 : ((Real.log x) ^ (-lam)) ^ 2 = (Real.log x) ^ (-2 * lam) := by
      rw [pow_two, ← Real.rpow_add hlogpos]; congr 1; ring
    have hsq : (Real.sqrt (Cw * (Submission.Aseq x : ℝ) * (Real.log x) ^ W0)
          * Real.sqrt (3 * (Submission.Aseq x : ℝ) * (Real.log x) ^ (-lamR))) ^ 2
        ≤ (Real.sqrt (3 * Cw) * (Submission.Aseq x : ℝ) * (Real.log x) ^ (-lam)) ^ 2 := by
      rw [mul_pow, mul_pow, mul_pow, Real.sq_sqrt hS1nn, Real.sq_sqrt hS2nn,
        Real.sq_sqrt (show (0 : ℝ) ≤ 3 * Cw by linarith [hCw])]
      have hprod : Cw * (Submission.Aseq x : ℝ) * (Real.log x) ^ W0
            * (3 * (Submission.Aseq x : ℝ) * (Real.log x) ^ (-lamR))
          = 3 * Cw * ((Submission.Aseq x : ℝ) ^ 2
              * ((Real.log x) ^ W0 * (Real.log x) ^ (-lamR))) := by ring
      rw [hprod, hpow, hpow2]
      have hle : (Real.log x) ^ (-2 * lam - 10) ≤ (Real.log x) ^ (-2 * lam) :=
        Real.rpow_le_rpow_of_exponent_le hlog1 (by linarith)
      have hAx2 : (0 : ℝ) ≤ (Submission.Aseq x : ℝ) ^ 2 := sq_nonneg _
      have step : 3 * Cw * ((Submission.Aseq x : ℝ) ^ 2 * (Real.log x) ^ (-2 * lam - 10))
          ≤ 3 * Cw * ((Submission.Aseq x : ℝ) ^ 2 * (Real.log x) ^ (-2 * lam)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hle hAx2)
          (mul_nonneg (by norm_num) hCw.le)
      exact le_trans step (le_of_eq (by ring))
    have h5 := sq_le_sq.mp hsq
    rw [abs_of_nonneg hleft, abs_of_nonneg hright] at h5
    exact h5
  calc Submission.ASP.Eone Submission.ASP.FIr t D L
      ≤ ∑ k ∈ (Finset.Icc 1 N).filter Submission.ASP.CubefreeN,
          ((k.divisors.card : ℝ)) * |Submission.ASP.FIr k t| := hE1
    _ ≤ Real.sqrt (Cw * (Submission.Aseq x : ℝ) * (Real.log x) ^ W0)
          * Real.sqrt (3 * (Submission.Aseq x : ℝ) * (Real.log x) ^ (-lamR)) := hCS
    _ ≤ Real.sqrt (3 * Cw) * (Submission.Aseq x : ℝ) * (Real.log x) ^ (-lam) := hfinal

end

end Work.FIChain
