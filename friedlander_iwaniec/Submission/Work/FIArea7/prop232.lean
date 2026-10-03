import Mathlib
import Submission.Work.FIArea7.prop232Defs
import Submission.Work.FIArea7.prop232Aux
import Submission.Work.FIArea7.quadEigen_decomp
import Submission.Work.FIArea7.JKSym_mul_eq_zero
import Submission.Work.FIArea7.primarySet_card_le_tau
import Submission.Work.FIArea7.LLinear_eq_sum_LStarLinear
import Submission.Work.FIArea7.KStarDisc_bound
import Submission.Work.FIArea7.msmooth_sum_bound

set_option autoImplicit false
set_option linter.unusedVariables false

namespace Work.FIArea7

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-- The disc version of *FI* (22.4) — proved by `Work.FIArea7.KStarDisc_bound`. -/
def KStarDiscHyp : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ (d : ℕ) (hd : 1 ≤ d) (w : GaussianInt) (k : ℤ)
    (chi : GaussianInt → ℂ) (N : ℕ),
    Work.FIPlan.IsPrimary w → IsCoprime w.re w.im → 1 ≤ N →
    (∀ z : GaussianInt, ‖chi z‖ ≤ 1) →
    (∀ (a b : ℤ), chi ⟨a + 4 * (d : ℤ), b⟩ = chi ⟨a, b⟩) →
    (∀ (a b : ℤ), chi ⟨a, b + 4 * (d : ℤ)⟩ = chi ⟨a, b⟩) →
    ‖KStarDisc N w k chi‖
      ≤ C * (d : ℝ) * (|(k : ℝ)| + 1) * ‖w.toComplex‖
          * (((Work.FIPlan.gnorm w).divisors).card : ℝ)
          * (N : ℝ) ^ ((3 : ℝ) / 4)
          * Real.log (2 + ‖w.toComplex‖ * (N : ℝ))

/-- The `τ(m)^4` arithmetic of *FI* (23.11) — proved by `Work.FIArea7.msmooth_sum_bound`. -/
def KSumHyp : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ (m J N : ℕ), 1 ≤ m →
    ∑ k ∈ (Finset.Icc 1 N).filter (fun k => k ∣ m ^ J),
        ((k : ℝ) ^ ((1 : ℝ) / 4))⁻¹ * (((m * k).divisors.card : ℕ) : ℝ) ^ 2
      ≤ C * (((m.divisors.card : ℕ) : ℝ)) ^ 4

/-! ## The splitting of `L∗(N)` along the primary divisors `ww̄ = M` -/

/-- **`L∗(N) = Σ∧_{ww̄=M} ψ(w) K∗(N)`** (the step that produces (23.12) from (22.4)): for `M ≥ 1`
the restricted linear form factorises over the primary `w` of norm `M`, the inner sum being the
disc sum `KStarDiscZ N w k χ` of `K∗` at that `w`.  The eigenvalue decomposition
(`Work.FIArea7.quadEigen_decomp`) writes `λ(M n)` as a sum over such `w`, and the terms of the
disc sum with `(|z|², M) > 1` vanish by `Work.FIArea7.JKSym_mul_eq_zero`. -/
theorem LStarLinear_eq_sum_KStarDiscZ (M N : ℕ) (k : ℤ) (chi : GaussianInt → ℂ)
    (hM : 1 ≤ M) (hN : 1 ≤ N) (hchi : ∀ z : GaussianInt, ‖chi z‖ ≤ 1)
    (hmul : ∀ z1 z2 : GaussianInt, IsCoprime z1 z2 → chi (z1 * z2) = chi z1 * chi z2) :
    LStarLinear M N (grossenChar chi k)
      = ∑ w ∈ primarySet M, grossenChar chi k w * KStarDiscZ N w k chi := by
  have h1 : LStarLinear M N (grossenChar chi k)
      = ∑ n ∈ (Finset.Icc 1 N).filter (fun n => Nat.Coprime n M),
            quadEigen (grossenChar chi k) (M * n) := by
    rw [LStarLinear, Finset.sum_filter]
  rw [h1]
  have h2 : ∀ n ∈ (Finset.Icc 1 N).filter (fun n => Nat.Coprime n M),
      quadEigen (grossenChar chi k) (M * n)
        = ∑ w ∈ primarySet M, grossenChar chi k w *
            (∑ z ∈ primarySet n, grossenChar chi k z * JKSym (w * z)) := by
    intro n hn
    rw [Finset.mem_filter, Finset.mem_Icc] at hn
    exact quadEigen_decomp hM hn.1.1 hn.2.symm k chi hmul
  rw [Finset.sum_congr rfl h2]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun w hw => ?_)
  rw [← Finset.mul_sum]
  congr 1
  have hcore : (∑ n ∈ (Finset.Icc 1 N).filter (fun n => Nat.Coprime n M),
        ∑ z ∈ primarySet n, grossenChar chi k z * JKSym (w * z))
      = KStarDiscZ N w k chi := by
    have hwprim : Work.FIPlan.IsPrimary w := isPrimary_of_mem_primarySet hw
    have hwg : Work.FIPlan.gnorm w = M := gnorm_of_mem_primarySet hw
    set U : Finset GaussianInt := (Work.FIPlan.gBox ((Nat.sqrt N : ℕ) : ℤ)).filter
      (fun z => Work.FIPlan.IsPrimary z ∧ Work.FIPlan.gnorm z ≤ N ∧
        Nat.Coprime (Work.FIPlan.gnorm z) M) with hUdef
    have hpd : ((↑((Finset.Icc 1 N).filter (fun n => Nat.Coprime n M)) : Set ℕ)).PairwiseDisjoint
        (fun n => primarySet n) := by
      intro x hx y hy hxy
      rw [Function.onFun, Finset.disjoint_left]
      intro z hzx hzy
      rw [mem_primarySet] at hzx hzy
      exact hxy (hzx.2.symm.trans hzy.2)
    have hA : (∑ n ∈ (Finset.Icc 1 N).filter (fun n => Nat.Coprime n M),
          ∑ z ∈ primarySet n, grossenChar chi k z * JKSym (w * z))
        = ∑ z ∈ U, grossenChar chi k z * JKSym (w * z) := by
      rw [← Finset.sum_biUnion hpd]
      congr 1
      ext z
      constructor
      · intro hz
        rw [Finset.mem_biUnion] at hz
        obtain ⟨n, hn, hzn⟩ := hz
        rw [Finset.mem_filter] at hn
        obtain ⟨hnIcc, hcn⟩ := hn
        rw [Finset.mem_Icc] at hnIcc
        rw [mem_primarySet] at hzn
        rw [hUdef, Finset.mem_filter]
        exact ⟨mem_gBox_sqrt_of_gnorm_le (by rw [hzn.2]; exact hnIcc.2), hzn.1,
          by rw [hzn.2]; exact hnIcc.2, by rw [hzn.2]; exact hcn⟩
      · intro hz
        rw [hUdef, Finset.mem_filter] at hz
        obtain ⟨hzbox, hzprim, hzN, hcn⟩ := hz
        rw [Finset.mem_biUnion]
        refine ⟨Work.FIPlan.gnorm z, ?_, ?_⟩
        · rw [Finset.mem_filter, Finset.mem_Icc]
          exact ⟨⟨(gnorm_odd_of_primary hzprim).pos, hzN⟩, hcn⟩
        · rw [mem_primarySet]
          exact ⟨hzprim, rfl⟩
    rw [hA]
    rw [KStarDiscZ]
    refine Finset.sum_subset ?_ ?_
    · intro z hz
      rw [hUdef, Finset.mem_filter] at hz
      obtain ⟨hzbox, hzprim, hzN, hcop⟩ := hz
      rw [Finset.mem_filter]
      refine ⟨hzbox, hzN, hzprim, ?_⟩
      have hcop' : Nat.Coprime (Work.FIPlan.gnorm z) (Work.FIPlan.gnorm w) := by
        rw [hwg]; exact hcop
      exact isCoprime_of_coprime_gnorm hcop'
    · intro z hz hzU
      rw [Finset.mem_filter] at hz
      obtain ⟨hzbox, hzN, hzprim, hzcop⟩ := hz
      have hncop : ¬ Nat.Coprime (Work.FIPlan.gnorm z) M := by
        intro hc
        exact hzU (by rw [hUdef, Finset.mem_filter]; exact ⟨hzbox, hzprim, hzN, hc⟩)
      obtain ⟨p, hp, hpdvd⟩ := Nat.exists_prime_and_dvd (n := (Work.FIPlan.gnorm z).gcd M)
        (by
          intro h
          exact hncop (by rw [Nat.coprime_iff_gcd_eq_one]; exact h))
      have hpz : p ∣ Work.FIPlan.gnorm z := hpdvd.trans (Nat.gcd_dvd_left _ _)
      have hpM : p ∣ M := hpdvd.trans (Nat.gcd_dvd_right _ _)
      have hvw : JKSym (w * z) = 0 :=
        JKSym_mul_eq_zero hp.one_lt hwprim hzprim hzcop hpz (by rw [hwg]; exact hpM)
      rw [hvw, mul_zero]
  rw [hcore]
/-! ## The bound for `L∗(N)` -/

/-- **`L∗(N) ≪ d(|k|+1) τ(M)² √M N^{3/4} log(MN+2)`** (23.12), obtained by summing the disc bound
`KStarDiscHyp` over the `≤ τ(M)` primary `w` with `ww̄ = M` (`primarySet_card_le_tau`). -/
theorem LStarLinear_bound (hDisc : KStarDiscHyp) :
    ∃ C : ℝ, 0 < C ∧ ∀ (M N d : ℕ) (k : ℤ) (chi : GaussianInt → ℂ),
      1 ≤ M → 1 ≤ N → 1 ≤ d →
      (∀ z : GaussianInt, ‖chi z‖ ≤ 1) →
      (∀ z1 z2 : GaussianInt, IsCoprime z1 z2 → chi (z1 * z2) = chi z1 * chi z2) →
      (∀ (a b : ℤ), chi ⟨a + 4 * (d : ℤ), b⟩ = chi ⟨a, b⟩) →
      (∀ (a b : ℤ), chi ⟨a, b + 4 * (d : ℤ)⟩ = chi ⟨a, b⟩) →
      ‖LStarLinear M N (grossenChar chi k)‖
        ≤ C * (d : ℝ) * (|(k : ℝ)| + 1) * (((M.divisors.card : ℕ) : ℝ)) ^ 2
            * Real.sqrt (M : ℝ) * (N : ℝ) ^ ((3 : ℝ) / 4)
            * Real.log ((M : ℝ) * N + 2) := by
  obtain ⟨C₀, hC₀pos, hD⟩ := hDisc
  refine ⟨C₀, hC₀pos, ?_⟩
  intro M N d k chi hM hN hd hchi hmul hp1 hp2
  rw [LStarLinear_eq_sum_KStarDiscZ M N k chi hM hN hchi hmul]
  set T : ℝ := (((M.divisors.card : ℕ) : ℝ)) with hTdef
  set X : ℝ := C₀ * (d : ℝ) * (|(k : ℝ)| + 1) * Real.sqrt (M : ℝ) * T
      * (N : ℝ) ^ ((3 : ℝ) / 4) * Real.log ((M : ℝ) * N + 2) with hXdef
  have hsM : 1 ≤ Real.sqrt (M : ℝ) := Real.one_le_sqrt.mpr (by exact_mod_cast hM)
  have hsMle : Real.sqrt (M : ℝ) ≤ (M : ℝ) := by
    have h2 : Real.sqrt (M : ℝ) * Real.sqrt (M : ℝ) = (M : ℝ) :=
      Real.mul_self_sqrt (Nat.cast_nonneg M)
    nlinarith [hsM, h2]
  have hTnn : 0 ≤ T := by rw [hTdef]; exact Nat.cast_nonneg _
  have hlogarg : (1:ℝ) ≤ (M : ℝ) * N + 2 := by
    have h1 : (1:ℝ) ≤ (M:ℝ) := by exact_mod_cast hM
    have h2 : (0:ℝ) ≤ (M:ℝ) * N := mul_nonneg (le_trans zero_le_one h1) (Nat.cast_nonneg N)
    linarith
  have hXnn : 0 ≤ X := by
    rw [hXdef]
    have h1 : (0:ℝ) ≤ C₀ * (d : ℝ) * (|(k : ℝ)| + 1) * Real.sqrt (M : ℝ) * T := by positivity
    have h2 : (0:ℝ) ≤ (N : ℝ) ^ ((3 : ℝ) / 4) := Real.rpow_nonneg (Nat.cast_nonneg N) _
    have h3 : 0 ≤ Real.log ((M : ℝ) * N + 2) := Real.log_nonneg hlogarg
    exact mul_nonneg (mul_nonneg h1 h2) h3
  have hlogcmp : Real.log (2 + Real.sqrt (M : ℝ) * (N : ℝ)) ≤ Real.log ((M : ℝ) * N + 2) := by
    apply Real.log_le_log (show (0:ℝ) < 2 + Real.sqrt (M : ℝ) * (N : ℝ) by
      have h0 : (0:ℝ) ≤ Real.sqrt (M : ℝ) * (N : ℝ) :=
        mul_nonneg (Real.sqrt_nonneg _) (Nat.cast_nonneg N)
      linarith)
    have h1 : Real.sqrt (M : ℝ) * (N : ℝ) ≤ (M : ℝ) * (N : ℝ) :=
      mul_le_mul_of_nonneg_right hsMle (Nat.cast_nonneg N)
    linarith
  have hterm : ∀ w ∈ primarySet M,
      ‖grossenChar chi k w * KStarDiscZ N w k chi‖
        ≤ C₀ * (d : ℝ) * (|(k : ℝ)| + 1) * Real.sqrt (M : ℝ) * T
            * (N : ℝ) ^ ((3 : ℝ) / 4) * Real.log (2 + Real.sqrt (M : ℝ) * (N : ℝ)) := by
    intro w hw
    have hwprim : Work.FIPlan.IsPrimary w := isPrimary_of_mem_primarySet hw
    have hwg : Work.FIPlan.gnorm w = M := gnorm_of_mem_primarySet hw
    rw [norm_mul]
    by_cases hcop : IsCoprime w.re w.im
    · rw [KStarDiscZ_eq_KStarDisc]
      have hdisc := hD d hd w k chi N hwprim hcop hN hchi hp1 hp2
      have h1 : ‖grossenChar chi k w‖ ≤ 1 := grossenChar_norm_le_one chi k hchi w
      have h2 : (0:ℝ) ≤ ‖KStarDisc N w k chi‖ := norm_nonneg _
      refine le_trans (mul_le_mul h1 hdisc h2 zero_le_one) ?_
      rw [one_mul]
      have hwn : ‖w.toComplex‖ = Real.sqrt (M : ℝ) := by
        rw [norm_toComplex_sqrt, hwg]
      have htau : (((Work.FIPlan.gnorm w).divisors).card : ℝ) = T := by rw [hTdef, hwg]
      rw [hwn, htau]
    · rw [KStarDiscZ_eq_KStarDisc]
      have hzero : KStarDisc N w k chi = 0 := by
        rw [KStarDisc]
        apply Finset.sum_eq_zero
        intro r hr
        rw [KInnerStar]
        apply Finset.sum_eq_zero
        intro s hs
        by_cases h : Work.FIPlan.IsPrimary (⟨r, s⟩ : GaussianInt) ∧
            Work.FIPlan.GaussCoprime (⟨r, s⟩ : GaussianInt) w
        · rw [if_pos h, JKSym_mul_eq_zero_of_not_isCoprime_re_im hwprim h.1 hcop, mul_zero]
        · rw [if_neg h]
      rw [hzero, norm_zero, mul_zero]
      have h1 : (0:ℝ) ≤ C₀ * (d : ℝ) * (|(k : ℝ)| + 1) * Real.sqrt (M : ℝ) * T
          * (N : ℝ) ^ ((3 : ℝ) / 4) := by positivity
      exact mul_nonneg h1 (Real.log_nonneg (by
        have h0 : (0:ℝ) ≤ Real.sqrt (M : ℝ) * (N : ℝ) :=
          mul_nonneg (Real.sqrt_nonneg (M:ℝ)) (by exact_mod_cast Nat.zero_le N)
        linarith))
  refine le_trans (norm_sum_le _ _) ?_
  refine le_trans (Finset.sum_le_sum hterm) ?_
  set F : ℝ := C₀ * (d : ℝ) * (|(k : ℝ)| + 1) * Real.sqrt (M : ℝ) * T
      * (N : ℝ) ^ ((3 : ℝ) / 4) with hFdef
  rw [Finset.sum_const, nsmul_eq_mul]
  have hFnn : 0 ≤ F := by rw [hFdef]; positivity
  have hcard' : ((primarySet M).card : ℝ) ≤ T := by
    rw [hTdef]; exact_mod_cast primarySet_card_le_tau M
  have hlogG : 0 ≤ Real.log (2 + Real.sqrt (M : ℝ) * (N : ℝ)) := Real.log_nonneg (by
    have h0 : (0:ℝ) ≤ Real.sqrt (M : ℝ) * (N : ℝ) :=
      mul_nonneg (Real.sqrt_nonneg _) (Nat.cast_nonneg N)
    linarith)
  calc ((primarySet M).card : ℝ) * (F * Real.log (2 + Real.sqrt (M : ℝ) * (N : ℝ)))
      ≤ T * (F * Real.log (2 + Real.sqrt (M : ℝ) * (N : ℝ))) :=
        mul_le_mul_of_nonneg_right hcard' (mul_nonneg hFnn hlogG)
    _ ≤ T * (F * Real.log ((M : ℝ) * N + 2)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hlogcmp hFnn) hTnn
    _ = C₀ * (d : ℝ) * (|(k : ℝ)| + 1) * T ^ 2 * Real.sqrt (M : ℝ)
          * (N : ℝ) ^ ((3 : ℝ) / 4) * Real.log ((M : ℝ) * N + 2) := by rw [hFdef]; ring

/-! ## The reduction of `L(N)` to the `L∗`-bounds and the arithmetic -/

/-- The elementary comparison `√(mk)·(N/k)^{3/4} ≤ √m·N^{3/4} k^{-1/4}` for `k ≤ N`. -/
lemma sqrt_mul_div_pow_le (m N k : ℕ) (hk1 : 1 ≤ k) (hkN : k ≤ N) :
    Real.sqrt (((m * k : ℕ)) : ℝ) * (((N / k : ℕ)) : ℝ) ^ ((3:ℝ)/4)
      ≤ Real.sqrt ((m:ℝ)) * (N:ℝ) ^ ((3:ℝ)/4) * (((k:ℝ) ^ ((1:ℝ)/4))⁻¹) := by
  have hkR : (0:ℝ) < (k:ℝ) := by exact_mod_cast hk1
  have hNR : (0:ℝ) < (N:ℝ) := by exact_mod_cast (le_trans hk1 hkN)
  have hmR : (0:ℝ) ≤ (m:ℝ) := Nat.cast_nonneg m
  have hnk_nn : (0:ℝ) ≤ ((N / k : ℕ) : ℝ) := Nat.cast_nonneg _
  have hnk_le : ((N / k : ℕ) : ℝ) ≤ (N:ℝ) / (k:ℝ) := by
    rw [le_div_iff₀ hkR]
    have h : N / k * k ≤ N := Nat.div_mul_le_self N k
    have h' : ((N / k : ℕ) : ℝ) * (k:ℝ) ≤ (N:ℝ) := by exact_mod_cast h
    linarith
  have h1 : ((N / k : ℕ) : ℝ) ^ ((3:ℝ)/4) ≤ ((N:ℝ)/(k:ℝ)) ^ ((3:ℝ)/4) :=
    Real.rpow_le_rpow hnk_nn hnk_le (by norm_num)
  have h2 : ((N:ℝ)/(k:ℝ)) ^ ((3:ℝ)/4) = (N:ℝ)^((3:ℝ)/4) * ((k:ℝ)^((3:ℝ)/4))⁻¹ := by
    rw [Real.div_rpow (le_of_lt hNR) (le_of_lt hkR), div_eq_mul_inv]
  have h3 : Real.sqrt (((m*k : ℕ)) : ℝ) = Real.sqrt (m:ℝ) * Real.sqrt (k:ℝ) := by
    rw [show (((m*k : ℕ)) : ℝ) = (m:ℝ) * (k:ℝ) by push_cast; ring, Real.sqrt_mul hmR]
  have h4 : Real.sqrt (k:ℝ) * ((k:ℝ)^((3:ℝ)/4))⁻¹ = ((k:ℝ)^((1:ℝ)/4))⁻¹ := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_neg (le_of_lt hkR), ← Real.rpow_add hkR,
      show (1:ℝ)/2 + -((3:ℝ)/4) = -((1:ℝ)/4) by norm_num, Real.rpow_neg (le_of_lt hkR)]
  calc Real.sqrt (((m*k : ℕ)) : ℝ) * ((N/k : ℕ) : ℝ)^((3:ℝ)/4)
      ≤ Real.sqrt (m:ℝ) * Real.sqrt (k:ℝ) * ((N:ℝ)/(k:ℝ))^((3:ℝ)/4) := by
        rw [h3]; exact mul_le_mul_of_nonneg_left h1 (by positivity)
    _ = Real.sqrt (m:ℝ) * (N:ℝ)^((3:ℝ)/4) * (Real.sqrt (k:ℝ) * ((k:ℝ)^((3:ℝ)/4))⁻¹) := by
        rw [h2]; ring
    _ = Real.sqrt (m:ℝ) * (N:ℝ)^((3:ℝ)/4) * ((k:ℝ)^((1:ℝ)/4))⁻¹ := by rw [h4]

/-- **`L(N) ≪ d(|k|+1) τ(m)^4 √m N^{3/4} log(mN+2)`** (23.11): split `L(N)` along the `m`-smooth
part of `n` (`Work.FIArea7.LLinear_eq_sum_LStarLinear`), apply the `L∗`-bound to each modulus `mk`
and sum with the `τ(m)^4` arithmetic `KSumHyp`. -/
theorem LLinear_bound (hDisc : KStarDiscHyp) (hKsum : KSumHyp) :
    ∃ C : ℝ, 0 < C ∧ ∀ (m N d : ℕ) (k : ℤ) (chi : GaussianInt → ℂ),
      1 ≤ m → 1 ≤ d → 1 ≤ N →
      (∀ z : GaussianInt, ‖chi z‖ ≤ 1) →
      (∀ z1 z2 : GaussianInt, IsCoprime z1 z2 → chi (z1 * z2) = chi z1 * chi z2) →
      (∀ (a b : ℤ), chi ⟨a + 4 * (d : ℤ), b⟩ = chi ⟨a, b⟩) →
      (∀ (a b : ℤ), chi ⟨a, b + 4 * (d : ℤ)⟩ = chi ⟨a, b⟩) →
      ‖LLinear m N (grossenChar chi k)‖
        ≤ C * (d : ℝ) * (|(k : ℝ)| + 1) * (((m.divisors.card : ℕ) : ℝ)) ^ 4
            * Real.sqrt (m : ℝ) * (N : ℝ) ^ ((3 : ℝ) / 4)
            * Real.log ((m : ℝ) * N + 2) := by
  obtain ⟨C₀, hC₀pos, hLstar⟩ := LStarLinear_bound hDisc
  obtain ⟨C₁, hC₁pos, hKsum'⟩ := hKsum
  refine ⟨C₀ * C₁, by positivity, ?_⟩
  intro m N d k chi hm hd hN hchi hmul hp1 hp2
  have hNpos : (0:ℝ) < (N:ℝ) := by exact_mod_cast hN
  have hmpos : (0:ℝ) < (m:ℝ) := by exact_mod_cast hm
  set A : ℝ := C₀ * (d : ℝ) * (|(k : ℝ)| + 1) * Real.sqrt (m : ℝ)
      * (N : ℝ) ^ ((3 : ℝ) / 4) * Real.log ((m : ℝ) * N + 2) with hAdef
  have hAnn : 0 ≤ A := by
    rw [hAdef]
    have h1 : (0:ℝ) ≤ C₀ * (d : ℝ) * (|(k : ℝ)| + 1) * Real.sqrt (m : ℝ) := by positivity
    have h2 : (0:ℝ) ≤ (N : ℝ) ^ ((3 : ℝ) / 4) := Real.rpow_nonneg (Nat.cast_nonneg N) _
    have h3 : 0 ≤ Real.log ((m : ℝ) * N + 2) := by
      apply Real.log_nonneg
      have h4 : (1:ℝ) ≤ (m:ℝ) := by exact_mod_cast hm
      have h5 : (0:ℝ) ≤ (N:ℝ) := Nat.cast_nonneg N
      nlinarith
    exact mul_nonneg (mul_nonneg h1 h2) h3
  have hterm : ∀ k' ∈ (Finset.Icc 1 N).filter (fun k' => k' ∣ m ^ N),
      ‖LStarLinear (m * k') (N / k') (grossenChar chi k)‖
        ≤ A * (((k':ℝ) ^ ((1:ℝ)/4))⁻¹ * (((m * k').divisors.card : ℕ) : ℝ) ^ 2) := by
    intro k' hk'
    rw [Finset.mem_filter, Finset.mem_Icc] at hk'
    obtain ⟨⟨hk1, hkN⟩, hkdvd⟩ := hk'
    have hkpos : 1 ≤ m * k' :=
      Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
    have hdiv : 1 ≤ N / k' := Nat.div_pos hkN hk1
    have h1 : ‖LStarLinear (m * k') (N / k') (grossenChar chi k)‖
        ≤ C₀ * (d:ℝ) * (|(k:ℝ)|+1) * ((((m*k').divisors.card : ℕ) : ℝ)) ^ 2
            * Real.sqrt ((m*k' : ℕ) : ℝ) * (((N/k' : ℕ)) : ℝ) ^ ((3:ℝ)/4)
            * Real.log (((m*k' : ℕ) : ℝ) * ((N/k' : ℕ) : ℝ) + 2) :=
      hLstar (m*k') (N/k') d k chi hkpos hdiv hd hchi hmul hp1 hp2
    have hlog' : Real.log (((m*k' : ℕ) : ℝ) * ((N/k' : ℕ) : ℝ) + 2)
        ≤ Real.log ((m:ℝ) * (N:ℝ) + 2) := by
      have harg : ((m*k' : ℕ) : ℝ) * ((N/k' : ℕ) : ℝ) ≤ (m:ℝ) * (N:ℝ) := by
        have h2 : ((m*k' : ℕ) : ℝ) = (m:ℝ) * (k':ℝ) := by push_cast; ring
        have h4 : N / k' * k' ≤ N := Nat.div_mul_le_self N k'
        have h5 : (((N / k' : ℕ)) : ℝ) * (k':ℝ) ≤ (N:ℝ) := by exact_mod_cast h4
        calc ((m*k' : ℕ) : ℝ) * ((N/k' : ℕ) : ℝ)
            = (m:ℝ) * (((N / k' : ℕ)) * (k':ℝ)) := by rw [h2]; ring
          _ ≤ (m:ℝ) * (N:ℝ) := mul_le_mul_of_nonneg_left h5 (le_of_lt hmpos)
      have hpos : (0:ℝ) < ((m*k' : ℕ) : ℝ) * ((N/k' : ℕ) : ℝ) + 2 := by
        have h2 : (0:ℝ) ≤ ((m*k' : ℕ) : ℝ) := Nat.cast_nonneg _
        have h3 : (0:ℝ) ≤ ((N/k' : ℕ) : ℝ) := Nat.cast_nonneg _
        nlinarith
      exact Real.log_le_log hpos (by linarith)
    have hsq : Real.sqrt ((m*k' : ℕ) : ℝ) * (((N/k' : ℕ)) : ℝ) ^ ((3:ℝ)/4)
        ≤ Real.sqrt (m:ℝ) * (N:ℝ) ^ ((3:ℝ)/4) * ((k':ℝ) ^ ((1:ℝ)/4))⁻¹ :=
      sqrt_mul_div_pow_le m N k' hk1 hkN
    have hτnn : (0:ℝ) ≤ ((((m*k').divisors.card : ℕ) : ℝ)) ^ 2 := by positivity
    have hlogMnn : 0 ≤ Real.log ((m:ℝ) * (N:ℝ) + 2) := by
      apply Real.log_nonneg
      have h1' : (1:ℝ) ≤ (m:ℝ) := by exact_mod_cast hm
      have h2' : (0:ℝ) ≤ (N:ℝ) := Nat.cast_nonneg N
      nlinarith
    calc ‖LStarLinear (m * k') (N / k') (grossenChar chi k)‖
        ≤ C₀ * (d:ℝ) * (|(k:ℝ)|+1) * ((((m*k').divisors.card : ℕ) : ℝ)) ^ 2
            * Real.sqrt ((m*k' : ℕ) : ℝ) * (((N/k' : ℕ)) : ℝ) ^ ((3:ℝ)/4)
            * Real.log (((m*k' : ℕ) : ℝ) * ((N/k' : ℕ) : ℝ) + 2) := h1
      _ ≤ C₀ * (d:ℝ) * (|(k:ℝ)|+1) * ((((m*k').divisors.card : ℕ) : ℝ)) ^ 2
            * (Real.sqrt (m:ℝ) * (N:ℝ) ^ ((3:ℝ)/4) * ((k':ℝ) ^ ((1:ℝ)/4))⁻¹)
            * Real.log ((m:ℝ) * (N:ℝ) + 2) := by
          have hprefix : (0:ℝ) ≤ C₀ * (d:ℝ) * (|(k:ℝ)|+1)
              * ((((m*k').divisors.card : ℕ) : ℝ)) ^ 2 := by positivity
          have hlogpos : (0:ℝ) ≤ Real.log (((m*k' : ℕ) : ℝ) * ((N/k' : ℕ) : ℝ) + 2) := by
            apply Real.log_nonneg
            have h2 : (0:ℝ) ≤ ((m*k' : ℕ) : ℝ) := Nat.cast_nonneg _
            have h3 : (0:ℝ) ≤ ((N/k' : ℕ) : ℝ) := Nat.cast_nonneg _
            nlinarith
          have hmain := mul_le_mul_of_nonneg_left hsq hprefix
          calc C₀ * (d:ℝ) * (|(k:ℝ)|+1) * ((((m*k').divisors.card : ℕ) : ℝ)) ^ 2
                * Real.sqrt ((m*k' : ℕ) : ℝ) * (((N/k' : ℕ)) : ℝ) ^ ((3:ℝ)/4)
                * Real.log (((m*k' : ℕ) : ℝ) * ((N/k' : ℕ) : ℝ) + 2)
              = (C₀ * (d:ℝ) * (|(k:ℝ)|+1) * ((((m*k').divisors.card : ℕ) : ℝ)) ^ 2
                  * (Real.sqrt ((m*k' : ℕ) : ℝ) * (((N/k' : ℕ)) : ℝ) ^ ((3:ℝ)/4)))
                * Real.log (((m*k' : ℕ) : ℝ) * ((N/k' : ℕ) : ℝ) + 2) := by ring
            _ ≤ (C₀ * (d:ℝ) * (|(k:ℝ)|+1) * ((((m*k').divisors.card : ℕ) : ℝ)) ^ 2
                  * (Real.sqrt (m:ℝ) * (N:ℝ) ^ ((3:ℝ)/4) * ((k':ℝ) ^ ((1:ℝ)/4))⁻¹))
                * Real.log ((m:ℝ) * (N:ℝ) + 2) :=
                mul_le_mul hmain hlog' hlogpos (by positivity)
            _ = C₀ * (d:ℝ) * (|(k:ℝ)|+1) * ((((m*k').divisors.card : ℕ) : ℝ)) ^ 2
                * (Real.sqrt (m:ℝ) * (N:ℝ) ^ ((3:ℝ)/4) * ((k':ℝ) ^ ((1:ℝ)/4))⁻¹)
                * Real.log ((m:ℝ) * (N:ℝ) + 2) := by ring
      _ = A * (((k':ℝ) ^ ((1:ℝ)/4))⁻¹ * (((m * k').divisors.card : ℕ) : ℝ) ^ 2) := by
          rw [hAdef]; ring
  rw [LLinear_eq_sum_LStarLinear m N hm (grossenChar chi k)]
  refine le_trans (norm_sum_le _ _) ?_
  refine le_trans (Finset.sum_le_sum hterm) ?_
  rw [← Finset.mul_sum]
  refine le_trans (mul_le_mul_of_nonneg_left (hKsum' m N N hm) hAnn) ?_
  rw [show A * (C₁ * (((m.divisors.card : ℕ) : ℝ)) ^ 4)
      = (C₀ * C₁) * (d : ℝ) * (|(k : ℝ)| + 1) * (((m.divisors.card : ℕ) : ℝ)) ^ 4
          * Real.sqrt (m : ℝ) * (N : ℝ) ^ ((3 : ℝ) / 4) * Real.log ((m : ℝ) * N + 2) from by
    rw [hAdef]; ring]

/-- `Work.FIArea7.Prop232` from the two remaining inputs. -/
theorem prop232_of (hDisc : KStarDiscHyp) (hKsum : KSumHyp) : Work.FIArea7.Prop232 := by
  obtain ⟨C₀, hC₀pos, hL⟩ := LLinear_bound hDisc hKsum
  obtain ⟨C₁, hC₁pos, hLs⟩ := LStarLinear_bound hDisc
  refine ⟨max C₀ C₁, lt_max_of_lt_left hC₀pos, ?_⟩
  intro N m d k chi hm hd hN hchi hmul hp1 hp2
  constructor
  · refine le_trans (hL m N d k chi hm hd hN hchi hmul hp1 hp2) ?_
    have h1 : (0:ℝ) ≤ (d : ℝ) * (|(k : ℝ)| + 1) * (((m.divisors.card : ℕ) : ℝ)) ^ 4
        * Real.sqrt (m : ℝ) * (N : ℝ) ^ ((3 : ℝ) / 4) * Real.log ((m : ℝ) * N + 2) := by
      have hd0 : (0:ℝ) ≤ (d : ℝ) := Nat.cast_nonneg d
      have hk0 : (0:ℝ) ≤ |(k : ℝ)| + 1 := by positivity
      have ht0 : (0:ℝ) ≤ (((m.divisors.card : ℕ) : ℝ)) ^ 4 := by positivity
      have hs0 : (0:ℝ) ≤ Real.sqrt (m : ℝ) := Real.sqrt_nonneg _
      have hp0 : (0:ℝ) ≤ (N : ℝ) ^ ((3 : ℝ) / 4) := Real.rpow_nonneg (Nat.cast_nonneg N) _
      have hl0 : (0:ℝ) ≤ Real.log ((m : ℝ) * N + 2) := by
        apply Real.log_nonneg
        have h2 : (1:ℝ) ≤ (m:ℝ) := by exact_mod_cast hm
        have h3 : (0:ℝ) ≤ (N:ℝ) := Nat.cast_nonneg N
        nlinarith
      exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hd0 hk0) ht0) hs0)
        hp0) hl0
    calc C₀ * (d : ℝ) * (|(k : ℝ)| + 1) * (((m.divisors.card : ℕ) : ℝ)) ^ 4
            * Real.sqrt (m : ℝ) * (N : ℝ) ^ ((3 : ℝ) / 4) * Real.log ((m : ℝ) * N + 2)
        = C₀ * ((d : ℝ) * (|(k : ℝ)| + 1) * (((m.divisors.card : ℕ) : ℝ)) ^ 4
            * Real.sqrt (m : ℝ) * (N : ℝ) ^ ((3 : ℝ) / 4)
            * Real.log ((m : ℝ) * N + 2)) := by ring
      _ ≤ max C₀ C₁ * ((d : ℝ) * (|(k : ℝ)| + 1) * (((m.divisors.card : ℕ) : ℝ)) ^ 4
            * Real.sqrt (m : ℝ) * (N : ℝ) ^ ((3 : ℝ) / 4)
            * Real.log ((m : ℝ) * N + 2)) :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) h1
      _ = max C₀ C₁ * (d : ℝ) * (|(k : ℝ)| + 1) * (((m.divisors.card : ℕ) : ℝ)) ^ 4
            * Real.sqrt (m : ℝ) * (N : ℝ) ^ ((3 : ℝ) / 4)
            * Real.log ((m : ℝ) * N + 2) := by ring
  · refine le_trans (hLs m N d k chi hm hN hd hchi hmul hp1 hp2) ?_
    have h1 : (0:ℝ) ≤ (d : ℝ) * (|(k : ℝ)| + 1) * (((m.divisors.card : ℕ) : ℝ)) ^ 2
        * Real.sqrt (m : ℝ) * (N : ℝ) ^ ((3 : ℝ) / 4) * Real.log ((m : ℝ) * N + 2) := by
      have hd0 : (0:ℝ) ≤ (d : ℝ) := Nat.cast_nonneg d
      have hk0 : (0:ℝ) ≤ |(k : ℝ)| + 1 := by positivity
      have ht0 : (0:ℝ) ≤ (((m.divisors.card : ℕ) : ℝ)) ^ 2 := by positivity
      have hs0 : (0:ℝ) ≤ Real.sqrt (m : ℝ) := Real.sqrt_nonneg _
      have hp0 : (0:ℝ) ≤ (N : ℝ) ^ ((3 : ℝ) / 4) := Real.rpow_nonneg (Nat.cast_nonneg N) _
      have hl0 : (0:ℝ) ≤ Real.log ((m : ℝ) * N + 2) := by
        apply Real.log_nonneg
        have h2 : (1:ℝ) ≤ (m:ℝ) := by exact_mod_cast hm
        have h3 : (0:ℝ) ≤ (N:ℝ) := Nat.cast_nonneg N
        nlinarith
      exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hd0 hk0) ht0) hs0)
        hp0) hl0
    calc C₁ * (d : ℝ) * (|(k : ℝ)| + 1) * (((m.divisors.card : ℕ) : ℝ)) ^ 2
            * Real.sqrt (m : ℝ) * (N : ℝ) ^ ((3 : ℝ) / 4) * Real.log ((m : ℝ) * N + 2)
        = C₁ * ((d : ℝ) * (|(k : ℝ)| + 1) * (((m.divisors.card : ℕ) : ℝ)) ^ 2
            * Real.sqrt (m : ℝ) * (N : ℝ) ^ ((3 : ℝ) / 4)
            * Real.log ((m : ℝ) * N + 2)) := by ring
      _ ≤ max C₀ C₁ * ((d : ℝ) * (|(k : ℝ)| + 1) * (((m.divisors.card : ℕ) : ℝ)) ^ 2
            * Real.sqrt (m : ℝ) * (N : ℝ) ^ ((3 : ℝ) / 4)
            * Real.log ((m : ℝ) * N + 2)) :=
          mul_le_mul_of_nonneg_right (le_max_right _ _) h1
      _ = max C₀ C₁ * (d : ℝ) * (|(k : ℝ)| + 1) * (((m.divisors.card : ℕ) : ℝ)) ^ 2
            * Real.sqrt (m : ℝ) * (N : ℝ) ^ ((3 : ℝ) / 4)
            * Real.log ((m : ℝ) * N + 2) := by ring

/-- **FI Proposition 23.2, (23.11)–(23.12)**: the special linear forms in the quadratic
eigenvalues at a fixed `m`.

The present result proves `Work.FIArea7.Prop232` (`Submission/Work/FIArea7/Classical172Defs.lean`).
The statement is: there is `C > 0` such that for all `N m d : ℕ` and `k : ℤ` with `1 ≤ m`, `1 ≤ d`,
`1 ≤ N` and all `χ : GaussianInt → ℂ` with `‖χ‖ ≤ 1`, multiplicative on coprime arguments and
`4d`-periodic in each coordinate (`χ ⟨a+4d, b⟩ = χ ⟨a,b⟩ = χ ⟨a, b+4d⟩`),

  `‖L(N)‖  = ‖Σ_{n ≤ N} λ(mn)‖ ≤ C d(|k|+1) τ(m)^4 √m N^{3/4} log(mN+2)`,
  `‖L∗(N)‖ = ‖Σ_{n ≤ N, (n,m)=1} λ(mn)‖ ≤ C d(|k|+1) τ(m)^2 √m N^{3/4} log(mN+2)`,

where `λ(n) = Σ^∧_{zz̄=n} ψ(z)[z]` is the quadratic eigenvalue (23.1) with
`ψ = Work.FIArea7.grossenChar χ k` the Hecke character (17.17), `[·] = Work.FIArea7.JKSym` the
Jacobi–Kubota symbol (20.1), `τ(m) = m.divisors.card`, and `LLinear`, `LStarLinear` are the
workspace's `(23.9)`/`(23.10)` (`Submission/Work/FIArea7/Classical172Defs.lean`).

Note the *exact* exponents: `τ(m)^4` for `L(N)` and `τ(m)^2` for `L∗(N)`, and `N^{3/4}` (the
`|w|N^{3/4}` of Prop. 22.1 with `|w| = √m`).

PROOF ROUTE (*FI* Prop. 23.2, p. 1033 of `REFS/FI_paper_X2Y4.pdf`):
For `(n,m) = 1` every primary `e` with `|e|² = mn` is uniquely `e = w z` with `w` primary of norm
`m`, `z` primary of norm `n`, and then `(z,w) = 1`; multiplicativity of `ψ` gives
`ψ(e) = ψ(w)ψ(z)`.  Hence

  `L∗(N) = Σ^∧_{ww̄=m} ψ(w) Σ_{z : |z|² ≤ N, (z,w)=1} ψ(z)[wz]`,

and the inner sum is the special linear form `K∗(N)` of *FI* (22.2)/(22.4), already proved in this
workspace as `Work.FIArea7.KStar_bound` (`Submission/Work/FIArea7/KStar_bound.lean`, import it):

  `‖K∗(N)‖ ≤ C d(|k|+1) |w| · τ(|w|²) · N^{3/4} · log(2 + |w|·N)`.

Summing over the primary `w` with `ww̄ = m` (at most `τ(m)` of them, each with `|w| = √m` and
`τ(|w|²) = τ(m)`) gives (23.12).  Then `L(N) = Σ_{e | m} Σ_{c | e^∞} Σ_{n ≤ N/c, (n, m)=1} …`
— the paper's decomposition `L(N) = Σ_{e|m} Σ_{c|e^∞} L∗`-type — gives (23.11) with `τ(m)^4`.
If `m` has a prime factor `≡ 3 (mod 4)` to an odd power then `λ` vanishes on all multiples of `m`
and both bounds are trivial; those cases need no work. -/
theorem prop232 : Work.FIArea7.Prop232 :=
  prop232_of KStarDisc_bound msmooth_sum_bound

end

end Work.FIArea7
