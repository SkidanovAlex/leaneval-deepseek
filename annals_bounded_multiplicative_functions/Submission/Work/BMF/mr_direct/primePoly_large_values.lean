import Mathlib
import Submission.Work.BMF.mr_direct.primePoly_defs
import Submission.Work.BMF.mr_direct.primePoly_pow_eq
import Submission.Work.BMF.mr_direct.powCoeff_energy
import Submission.Work.BMF.mr_direct.expLogLog_ineq
import Submission.Work.BMF.mr_direct.sampled_mean_value_blocks

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Large values of the prime-supported Dirichlet polynomial

Formalisation of Lemma `le:Rupest` in K. Matomäki, M. Radziwiłł, T. Tao, J. Teräväinen,
T. Ziegler, *Higher uniformity of bounded multiplicative functions in short intervals on
average* (Annals of Math. 197 (2023)), section "Mean and large value theorems for Dirichlet
polynomials":

Let `P(s) = Σ_{P ≤ p ≤ 2P} a_p p^{-s}` with `|a_p| ≤ 1` and let `𝒯 ⊆ [-T,T]` be a set of
well-spaced points with `|P(1+it)| ≥ V^{-1}` for `t ∈ 𝒯`.  Then

`|𝒯| ≪ T^{2 log V / log P} · V^2 · exp(2 (log T / log P) log log T)`.

The proof is the paper's: with `k = ⌈log T / log P⌉`, the `k`-th power `P(s)^k` is a
Dirichlet polynomial supported on `[P^k, (2P)^k]` whose coefficients have `ℓ²`-mass at most
`k^k (Σ_{P≤p≤2P} 1/p²)^k`; a sampled (large-sieve) mean-value estimate gives
`Σ_t |P(1+it)|^{2k} ≪ k (T + (2P)^k) Σ_n |b_n|²`, and `V^{2k} ≤ V^2 T^{2 log V/log P}`.
-/

set_option maxHeartbeats 1000000

namespace Work.BMF.mr_direct

open Finset
open scoped BigOperators

namespace primePoly

private lemma prod_le_prod_nat {ι : Type*} (s : Finset ι) {g h : ι → ℕ}
    (hgh : ∀ i ∈ s, g i ≤ h i) : ∏ i ∈ s, g i ≤ ∏ i ∈ s, h i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha]
    exact Nat.mul_le_mul (hgh a (Finset.mem_insert_self a s))
      (ih (fun i hi => hgh i (Finset.mem_insert_of_mem hi)))

/-- `powCoeff` vanishes off the range `[⌈P⌉₊^k, ⌊2P⌋₊^k]`. -/
lemma powCoeff_eq_zero_of_notMem (P : ℝ) (c : ℕ → ℂ) (k : ℕ) {n : ℕ}
    (hn : n ∉ Finset.Icc (⌈P⌉₊ ^ k) (⌊2 * P⌋₊ ^ k)) : powCoeff c P k n = 0 := by
  rw [powCoeff]
  apply Finset.sum_eq_zero
  intro f hf
  exfalso
  obtain ⟨hfm, hfn⟩ := Finset.mem_filter.mp hf
  have hmemj : ∀ j, f j ∈ primeSet P := fun j => (Fintype.mem_piFinset.mp hfm) j
  have hbnd : ∀ j, ⌈P⌉₊ ≤ f j ∧ f j ≤ ⌊2 * P⌋₊ :=
    fun j => Finset.mem_Icc.mp (Finset.mem_filter.mp (hmemj j)).1
  have hlo : ⌈P⌉₊ ^ k ≤ ∏ j, f j := by
    calc ⌈P⌉₊ ^ k = ∏ _j : Fin k, ⌈P⌉₊ := by simp
      _ ≤ ∏ j, f j := prod_le_prod_nat _ (fun j _ => (hbnd j).1)
  have hhi : ∏ j, f j ≤ ⌊2 * P⌋₊ ^ k := by
    calc (∏ j, f j) ≤ ∏ _j : Fin k, ⌊2 * P⌋₊ := prod_le_prod_nat _ (fun j _ => (hbnd j).2)
      _ = ⌊2 * P⌋₊ ^ k := by simp
  exact hn (Finset.mem_Icc.mpr ⟨by rw [← hfn]; exact hlo, by rw [← hfn]; exact hhi⟩)

end primePoly

/-- The reciprocal prime sum over a dyadic interval is at most `3/2`. -/
lemma primeSet_inv_sum_le {P : ℝ} (hP : 2 ≤ P) :
    (∑ p ∈ primePoly.primeSet P, (1 : ℝ) / (p : ℝ)) ≤ 3 / 2 := by
  have hPpos : 0 < P := by linarith
  have hcard : ((primePoly.primeSet P).card : ℝ) ≤ P + 1 := by
    have h1 : (primePoly.primeSet P).card ≤ ⌊2 * P⌋₊ + 1 - ⌈P⌉₊ := by
      have h0 : (primePoly.primeSet P).card ≤ (Finset.Icc ⌈P⌉₊ ⌊2 * P⌋₊).card :=
        Finset.card_le_card (Finset.filter_subset _ _)
      rwa [Nat.card_Icc] at h0
    have h3 : ((⌊2 * P⌋₊ + 1 - ⌈P⌉₊ : ℕ) : ℝ) ≤ P + 1 := by
      by_cases hlt : ⌈P⌉₊ ≤ ⌊2 * P⌋₊ + 1
      · rw [Nat.cast_sub hlt]
        have h4 : ((⌊2 * P⌋₊ : ℕ) : ℝ) ≤ 2 * P := Nat.floor_le (by linarith)
        have h5 : P ≤ (⌈P⌉₊ : ℝ) := Nat.le_ceil P
        push_cast
        linarith
      · have hz : ⌊2 * P⌋₊ + 1 - ⌈P⌉₊ = 0 := Nat.sub_eq_zero_of_le (le_of_lt (not_le.mp hlt))
        rw [hz]
        simp
        linarith
    have h1' : ((primePoly.primeSet P).card : ℝ) ≤ ((⌊2 * P⌋₊ + 1 - ⌈P⌉₊ : ℕ) : ℝ) := by
      exact_mod_cast h1
    linarith
  calc (∑ p ∈ primePoly.primeSet P, (1 : ℝ) / (p : ℝ))
      ≤ ∑ p ∈ primePoly.primeSet P, (1 : ℝ) / P := by
        apply Finset.sum_le_sum
        intro p hp
        have hpge : P ≤ (p : ℝ) := by
          have hmem := (Finset.mem_filter.mp hp).1
          have h1 : (⌈P⌉₊ : ℝ) ≤ (p : ℝ) := by
            exact_mod_cast (Finset.mem_Icc.mp hmem).1
          linarith [Nat.le_ceil P]
        exact one_div_le_one_div_of_le hPpos hpge
    _ = ((primePoly.primeSet P).card : ℝ) * (1 / P) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (P + 1) * (1 / P) := mul_le_mul_of_nonneg_right hcard (by positivity)
    _ = 1 + 1 / P := by field_simp
    _ ≤ 3 / 2 := by
        have h2 : 1 / P ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) hP
        linarith

/-- Conjugation of a complex power of a positive integer. -/
lemma conj_cpow_natCast {n : ℕ} (hn : 1 ≤ n) (z : ℂ) :
    (starRingEnd ℂ) ((n : ℂ) ^ z) = (n : ℂ) ^ ((starRingEnd ℂ) z) := by
  have harg : ((n : ℂ)).arg ≠ Real.pi := by
    have hcast : (n : ℂ) = (((n : ℝ)) : ℂ) := by push_cast; ring
    rw [hcast, Complex.arg_ofReal_of_nonneg (by positivity)]
    exact Real.pi_ne_zero.symm
  have h := Complex.cpow_conj ((n : ℂ)) z harg
  simp only [map_natCast] at h
  exact h.symm

theorem primePoly_large_values :
    ∃ C : ℝ, 0 < C ∧
      ∀ (P V T : ℝ) (R : ℕ) (t : Fin R → ℝ) (c : ℕ → ℂ),
        2 ≤ P → 3 ≤ T → 1 ≤ V →
        (∀ p, ‖c p‖ ≤ 1) →
        (∀ i j : Fin R, i ≠ j → 1 ≤ |t i - t j|) →
        (∀ i, t i ∈ Set.Icc (-T) T) →
        (∀ i, 1 / V ≤ ‖∑ p ∈ (Finset.Icc ⌈P⌉₊ ⌊2 * P⌋₊).filter Nat.Prime,
              c p * (p : ℂ) ^ (-(1 + Complex.I * (t i : ℂ)))‖) →
        (R : ℝ) ≤ C * (T ^ (2 * Real.log V / Real.log P) * V ^ 2
              * Real.exp (2 * (Real.log T / Real.log P) * Real.log (Real.log T))) := by
  obtain ⟨C₁, hC₁pos, hMV⟩ := sampled_mean_value_blocks
  obtain ⟨C₂, hC₂pos, hLL⟩ := expLogLog_ineq
  refine ⟨C₁ * C₂, by positivity, ?_⟩
  intro P V T R t c hP hT hV hc hsep hIcc hval
  have hP1 : (1 : ℝ) < P := by linarith
  have hPpos : 0 < P := by linarith
  have hT1 : (1 : ℝ) < T := by linarith
  have hTpos : 0 < T := by linarith
  have hV1 : (1 : ℝ) ≤ V := hV
  have hVpos : 0 < V := by linarith
  have hlogP : 0 < Real.log P := Real.log_pos hP1
  have hlogT : 0 < Real.log T := Real.log_pos hT1
  have hratio : 0 < Real.log T / Real.log P := div_pos hlogT hlogP
  set k : ℕ := Nat.ceil (Real.log T / Real.log P) with hkdef
  set L : ℝ := Real.log T / Real.log P with hLdef
  have hLpos : 0 < L := by rw [hLdef]; exact hratio
  have hk1 : 1 ≤ k := by rw [hkdef]; exact Nat.one_le_ceil_iff.mpr hratio
  have hkL : L ≤ (k : ℝ) := by rw [hLdef, hkdef]; exact Nat.le_ceil _
  have hkL1 : (k : ℝ) ≤ L + 1 := by
    have h := Nat.ceil_lt_add_one (le_of_lt hratio)
    rw [← hkdef] at h
    rw [hLdef] at h
    push_cast at h
    linarith
  -- `T ≤ P ^ k`
  have hTlePk : T ≤ P ^ k := by
    have h1 : Real.log T ≤ (k : ℝ) * Real.log P := by
      have h2 : Real.log T = L * Real.log P := by rw [hLdef]; field_simp
      rw [h2]
      exact mul_le_mul_of_nonneg_right hkL hlogP.le
    calc T = Real.exp (Real.log T) := (Real.exp_log hTpos).symm
      _ ≤ Real.exp ((k : ℝ) * Real.log P) := Real.exp_le_exp.mpr h1
      _ = P ^ ((k : ℝ)) := by rw [Real.rpow_def_of_pos hPpos]; ring_nf
      _ = P ^ k := Real.rpow_natCast P k
  -- lower bound from the hypothesis
  have hval2 : ∀ i : Fin R, (1 / V) ^ (2 * k) ≤ ‖primePoly.primeDirPoly c P (t i)‖ ^ (2 * k) := by
    intro i
    exact pow_le_pow_left₀ (by positivity) (hval i) (2 * k)
  have hsum_low : (R : ℝ) * (1 / V) ^ (2 * k)
      ≤ ∑ i : Fin R, ‖primePoly.primeDirPoly c P (t i)‖ ^ (2 * k) := by
    calc (R : ℝ) * (1 / V) ^ (2 * k) = ∑ _i : Fin R, (1 / V) ^ (2 * k) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      _ ≤ ∑ i : Fin R, ‖primePoly.primeDirPoly c P (t i)‖ ^ (2 * k) :=
          Finset.sum_le_sum (fun i _ => hval2 i)
  -- rewrite each term using the `k`-th power expansion and conjugation
  have hone : ∀ i : Fin R, ‖primePoly.primeDirPoly c P (t i)‖ ^ (2 * k)
      = ‖∑ n ∈ Finset.Icc (⌈P⌉₊ ^ k) (⌊2 * P⌋₊ ^ k),
            (starRingEnd ℂ) (primePoly.powCoeff c P k n) *
              (n : ℂ) ^ (Complex.I * ((t i : ℝ) : ℂ))‖ ^ 2 := by
    intro i
    have h1 : ‖primePoly.primeDirPoly c P (t i)‖ ^ (2 * k)
        = ‖(primePoly.primeDirPoly c P (t i)) ^ k‖ ^ 2 := by
      rw [norm_pow, ← pow_mul, Nat.mul_comm]
    have h2 : (primePoly.primeDirPoly c P (t i)) ^ k
        = ∑ n ∈ Finset.Icc 1 (⌊2 * P⌋₊ ^ k),
            primePoly.powCoeff c P k n * (n : ℂ) ^ (-(Complex.I * ((t i : ℝ) : ℂ))) :=
      (primePoly_pow_eq P c k hP hk1).1 (t i)
    have hN1' : 1 ≤ ⌈P⌉₊ ^ k := one_le_pow₀ (Nat.one_le_ceil_iff.mpr hPpos)
    have h3 : (∑ n ∈ Finset.Icc 1 (⌊2 * P⌋₊ ^ k),
            primePoly.powCoeff c P k n * (n : ℂ) ^ (-(Complex.I * ((t i : ℝ) : ℂ))))
        = ∑ n ∈ Finset.Icc (⌈P⌉₊ ^ k) (⌊2 * P⌋₊ ^ k),
            primePoly.powCoeff c P k n * (n : ℂ) ^ (-(Complex.I * ((t i : ℝ) : ℂ))) := by
      refine (Finset.sum_subset ?_ ?_).symm
      · intro n hn
        rw [Finset.mem_Icc] at hn ⊢
        exact ⟨le_trans hN1' hn.1, hn.2⟩
      · intro n _ hn
        rw [primePoly.powCoeff_eq_zero_of_notMem P c k hn, zero_mul]
    have h4 : (∑ n ∈ Finset.Icc (⌈P⌉₊ ^ k) (⌊2 * P⌋₊ ^ k),
            primePoly.powCoeff c P k n * (n : ℂ) ^ (-(Complex.I * ((t i : ℝ) : ℂ))))
        = (starRingEnd ℂ) (∑ n ∈ Finset.Icc (⌈P⌉₊ ^ k) (⌊2 * P⌋₊ ^ k),
            (starRingEnd ℂ) (primePoly.powCoeff c P k n) *
              (n : ℂ) ^ (Complex.I * ((t i : ℝ) : ℂ))) := by
      rw [map_sum]
      apply Finset.sum_congr rfl
      intro n hn
      have hn1 : 1 ≤ n := le_trans hN1' (Finset.mem_Icc.mp hn).1
      rw [map_mul, conj_cpow_natCast hn1]
      have hz : (starRingEnd ℂ) (Complex.I * ((t i : ℝ) : ℂ))
          = -(Complex.I * ((t i : ℝ) : ℂ)) := by simp [Complex.conj_I]
      rw [hz]
      have hbb : (starRingEnd ℂ) ((starRingEnd ℂ) (primePoly.powCoeff c P k n))
          = primePoly.powCoeff c P k n := by simp
      rw [hbb]
    rw [h1, h2, h3, h4, Complex.norm_conj]
  -- the mean value estimate
  have hN1 : 1 ≤ ⌈P⌉₊ ^ k := one_le_pow₀ (Nat.one_le_ceil_iff.mpr hPpos)
  have hK1 : 1 ≤ 2 ^ k := one_le_pow₀ (by norm_num : (1 : ℕ) ≤ 2)
  have hMK : ⌊2 * P⌋₊ ^ k ≤ ⌈P⌉₊ ^ k * 2 ^ k := by
    have hfle : ⌊2 * P⌋₊ ≤ 2 * ⌈P⌉₊ := by
      have h1 : ((⌊2 * P⌋₊ : ℕ) : ℝ) ≤ 2 * P := Nat.floor_le (by linarith)
      have h3 : P ≤ (⌈P⌉₊ : ℝ) := Nat.le_ceil P
      have h2 : ((⌊2 * P⌋₊ : ℕ) : ℝ) ≤ 2 * (⌈P⌉₊ : ℝ) := by linarith
      exact_mod_cast h2
    calc ⌊2 * P⌋₊ ^ k ≤ (2 * ⌈P⌉₊) ^ k := Nat.pow_le_pow_left hfle k
      _ = ⌈P⌉₊ ^ k * 2 ^ k := by rw [mul_pow, mul_comm]
  have hsupp_a : ∀ n, n ∉ Finset.Icc (⌈P⌉₊ ^ k) (⌊2 * P⌋₊ ^ k) →
      (fun n => (starRingEnd ℂ) (primePoly.powCoeff c P k n)) n = 0 := by
    intro n hn
    show (starRingEnd ℂ) (primePoly.powCoeff c P k n) = 0
    rw [primePoly.powCoeff_eq_zero_of_notMem P c k hn, map_zero]
  have hMV'' := hMV (⌈P⌉₊ ^ k) (⌊2 * P⌋₊ ^ k) (2 ^ k)
      (fun n => (starRingEnd ℂ) (primePoly.powCoeff c P k n)) T R t
      hN1 hK1 (le_of_lt hTpos) hMK hsupp_a hIcc hsep
  have hMV' : (∑ i : Fin R, ‖∑ n ∈ Finset.Icc (⌈P⌉₊ ^ k) (⌊2 * P⌋₊ ^ k),
        (starRingEnd ℂ) (primePoly.powCoeff c P k n) *
          (n : ℂ) ^ (Complex.I * ((t i : ℝ) : ℂ))‖ ^ 2)
      ≤ C₁ * ((2 ^ k : ℕ) + 1 : ℝ) * (T + ((⌊2 * P⌋₊ ^ k : ℕ) : ℝ))
          * (∑ n ∈ Finset.Icc (⌈P⌉₊ ^ k) (⌊2 * P⌋₊ ^ k), ‖primePoly.powCoeff c P k n‖ ^ 2) := by
    have hsum : (∑ n ∈ Finset.Icc (⌈P⌉₊ ^ k) (⌊2 * P⌋₊ ^ k),
          ‖(starRingEnd ℂ) (primePoly.powCoeff c P k n)‖ ^ 2)
        = (∑ n ∈ Finset.Icc (⌈P⌉₊ ^ k) (⌊2 * P⌋₊ ^ k), ‖primePoly.powCoeff c P k n‖ ^ 2) := by
      apply Finset.sum_congr rfl
      intro n _
      rw [Complex.norm_conj]
    rw [hsum] at hMV''
    exact hMV''
  -- energy bound
  have hσ : (∑ p ∈ primePoly.primeSet P, (1 : ℝ) / (p : ℝ) ^ 2) ≤ (3 / 2) / P := by
    have hpoint : ∀ p ∈ primePoly.primeSet P,
        (1 : ℝ) / (p : ℝ) ^ 2 ≤ (1 / P) * ((1 : ℝ) / (p : ℝ)) := by
      intro p hp
      have hpge : P ≤ (p : ℝ) := by
        have h1 : (⌈P⌉₊ : ℝ) ≤ (p : ℝ) := by
          exact_mod_cast (Finset.mem_Icc.mp (Finset.mem_filter.mp hp).1).1
        linarith [Nat.le_ceil P]
      have hppos : (0 : ℝ) < (p : ℝ) := by linarith
      have h1 : (1 : ℝ) / ((p : ℝ) ^ 2) ≤ 1 / (P * (p : ℝ)) := by
        apply one_div_le_one_div_of_le (by positivity)
        nlinarith
      have h2 : (1 : ℝ) / (P * (p : ℝ)) = (1 / P) * (1 / (p : ℝ)) := by
        field_simp
      linarith [h1, h2.symm.le, h2.le]
    calc (∑ p ∈ primePoly.primeSet P, (1 : ℝ) / (p : ℝ) ^ 2)
        ≤ ∑ p ∈ primePoly.primeSet P, (1 / P) * ((1 : ℝ) / (p : ℝ)) :=
          Finset.sum_le_sum hpoint
      _ = (1 / P) * (∑ p ∈ primePoly.primeSet P, (1 : ℝ) / (p : ℝ)) := by rw [Finset.mul_sum]
      _ ≤ (1 / P) * (3 / 2) := mul_le_mul_of_nonneg_left (primeSet_inv_sum_le hP) (by positivity)
      _ = (3 / 2) / P := by ring
  have henergy : (∑ n ∈ Finset.Icc (⌈P⌉₊ ^ k) (⌊2 * P⌋₊ ^ k), ‖primePoly.powCoeff c P k n‖ ^ 2)
      ≤ (k : ℝ) ^ k * ((3 / 2) ^ k / P ^ k) := by
    have hE := powCoeff_energy P c k hP hk1 hc
    have hswap : (∑ n ∈ Finset.Icc (⌈P⌉₊ ^ k) (⌊2 * P⌋₊ ^ k), ‖primePoly.powCoeff c P k n‖ ^ 2)
        = (∑ n ∈ Finset.Icc 1 (⌊2 * P⌋₊ ^ k), ‖primePoly.powCoeff c P k n‖ ^ 2) := by
      refine Finset.sum_subset ?_ ?_
      · intro n hn
        rw [Finset.mem_Icc] at hn ⊢
        exact ⟨le_trans hN1 hn.1, hn.2⟩
      · intro n _ hn
        rw [primePoly.powCoeff_eq_zero_of_notMem P c k hn]
        simp
    rw [hswap]
    calc (∑ n ∈ Finset.Icc 1 (⌊2 * P⌋₊ ^ k), ‖primePoly.powCoeff c P k n‖ ^ 2)
        ≤ (k : ℝ) ^ k * (∑ p ∈ primePoly.primeSet P, (1 : ℝ) / (p : ℝ) ^ 2) ^ k := hE
      _ ≤ (k : ℝ) ^ k * ((3 / 2) / P) ^ k := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          exact pow_le_pow_left₀ (Finset.sum_nonneg (fun p _ => by positivity)) hσ k
      _ = (k : ℝ) ^ k * ((3 / 2) ^ k / P ^ k) := by rw [div_pow]
  -- assemble
  have hcoef : (0 : ℝ) ≤ C₁ * ((2 ^ k : ℕ) + 1 : ℝ) * (T + ((⌊2 * P⌋₊ ^ k : ℕ) : ℝ)) :=
    mul_nonneg (mul_nonneg hC₁pos.le (by positivity)) (by positivity)
  have hmain : (R : ℝ) ≤ V ^ (2 * k) * (C₁ * ((2 ^ k : ℕ) + 1 : ℝ)
      * (T + ((⌊2 * P⌋₊ ^ k : ℕ) : ℝ)) * ((k : ℝ) ^ k * ((3 / 2) ^ k / P ^ k))) := by
    have h2 : (R : ℝ) * (1 / V) ^ (2 * k) ≤ C₁ * ((2 ^ k : ℕ) + 1 : ℝ)
        * (T + ((⌊2 * P⌋₊ ^ k : ℕ) : ℝ)) * ((k : ℝ) ^ k * ((3 / 2) ^ k / P ^ k)) := by
      calc (R : ℝ) * (1 / V) ^ (2 * k)
          ≤ ∑ i : Fin R, ‖primePoly.primeDirPoly c P (t i)‖ ^ (2 * k) := hsum_low
        _ = ∑ i : Fin R, ‖∑ n ∈ Finset.Icc (⌈P⌉₊ ^ k) (⌊2 * P⌋₊ ^ k),
              (starRingEnd ℂ) (primePoly.powCoeff c P k n) *
                (n : ℂ) ^ (Complex.I * ((t i : ℝ) : ℂ))‖ ^ 2 :=
              Finset.sum_congr rfl (fun i _ => hone i)
        _ ≤ C₁ * ((2 ^ k : ℕ) + 1 : ℝ) * (T + ((⌊2 * P⌋₊ ^ k : ℕ) : ℝ))
              * (∑ n ∈ Finset.Icc (⌈P⌉₊ ^ k) (⌊2 * P⌋₊ ^ k), ‖primePoly.powCoeff c P k n‖ ^ 2) := hMV'
        _ ≤ C₁ * ((2 ^ k : ℕ) + 1 : ℝ) * (T + ((⌊2 * P⌋₊ ^ k : ℕ) : ℝ))
              * ((k : ℝ) ^ k * ((3 / 2) ^ k / P ^ k)) :=
              mul_le_mul_of_nonneg_left henergy hcoef
    have h3 : (1 / V) ^ (2 * k) * V ^ (2 * k) = 1 := by
      rw [← mul_pow]
      have h4 : (1 / V) * V = 1 := by field_simp
      rw [h4, one_pow]
    calc (R : ℝ) = (R : ℝ) * ((1 / V) ^ (2 * k) * V ^ (2 * k)) := by rw [h3, mul_one]
      _ = ((R : ℝ) * (1 / V) ^ (2 * k)) * V ^ (2 * k) := by ring
      _ ≤ (C₁ * ((2 ^ k : ℕ) + 1 : ℝ) * (T + ((⌊2 * P⌋₊ ^ k : ℕ) : ℝ))
            * ((k : ℝ) ^ k * ((3 / 2) ^ k / P ^ k))) * V ^ (2 * k) :=
          mul_le_mul_of_nonneg_right h2 (by positivity)
      _ = V ^ (2 * k) * (C₁ * ((2 ^ k : ℕ) + 1 : ℝ)
            * (T + ((⌊2 * P⌋₊ ^ k : ℕ) : ℝ)) * ((k : ℝ) ^ k * ((3 / 2) ^ k / P ^ k))) := by ring
  -- final bounds
  have hA : (((2 ^ k : ℕ) + 1 : ℝ)) ≤ (2 : ℝ) ^ (k + 1) := by
    have h1 : (1 : ℝ) ≤ (2 : ℝ) ^ k := one_le_pow₀ (by norm_num)
    have h2 : (2 : ℝ) ^ (k + 1) = (2 : ℝ) ^ k * 2 := by rw [pow_succ]
    rw [h2]
    push_cast
    linarith
  have hB : (T + ((⌊2 * P⌋₊ ^ k : ℕ) : ℝ)) ≤ (2 : ℝ) ^ (k + 1) * P ^ k := by
    have hfl : ((⌊2 * P⌋₊ : ℕ) : ℝ) ≤ 2 * P := Nat.floor_le (by linarith)
    have h1 : ((⌊2 * P⌋₊ ^ k : ℕ) : ℝ) ≤ (2 * P) ^ k := by
      rw [Nat.cast_pow]
      exact pow_le_pow_left₀ (by positivity) hfl k
    calc T + ((⌊2 * P⌋₊ ^ k : ℕ) : ℝ) ≤ P ^ k + (2 * P) ^ k := add_le_add hTlePk h1
      _ = P ^ k + 2 ^ k * P ^ k := by rw [mul_pow]
      _ = P ^ k * (1 + 2 ^ k) := by ring
      _ ≤ P ^ k * (2 : ℝ) ^ (k + 1) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          have h2 : (1 : ℝ) ≤ (2 : ℝ) ^ k := one_le_pow₀ (by norm_num)
          have h4 : (2 : ℝ) ^ (k + 1) = (2 : ℝ) ^ k * 2 := by rw [pow_succ]
          rw [h4]
          linarith
      _ = (2 : ℝ) ^ (k + 1) * P ^ k := by ring
  have hD : V ^ (2 * k) ≤ V ^ 2 * T ^ (2 * Real.log V / Real.log P) := by
    have h1 : ((2 * k : ℕ) : ℝ) ≤ 2 * L + 2 := by
      push_cast
      linarith [hkL1]
    have h2 : V ^ (2 * k) ≤ V ^ (2 * L + 2) := by
      calc V ^ (2 * k) = V ^ (((2 * k : ℕ) : ℝ)) := (Real.rpow_natCast V (2 * k)).symm
        _ ≤ V ^ (2 * L + 2) := Real.rpow_le_rpow_of_exponent_le hV1 h1
    have h3 : V ^ (2 * L + 2) = V ^ (2 * L) * V ^ 2 := by
      rw [Real.rpow_add hVpos]
      norm_num
    have h4 : V ^ (2 * L) = T ^ (2 * Real.log V / Real.log P) := by
      rw [Real.rpow_def_of_pos hVpos, Real.rpow_def_of_pos hTpos]
      congr 1
      rw [hLdef]
      field_simp
    calc V ^ (2 * k) ≤ V ^ (2 * L + 2) := h2
      _ = V ^ (2 * L) * V ^ 2 := h3
      _ = T ^ (2 * Real.log V / Real.log P) * V ^ 2 := by rw [h4]
      _ = V ^ 2 * T ^ (2 * Real.log V / Real.log P) := by ring
  have hC : (4 : ℝ) ^ (k + 1) * (k : ℝ) ^ k * (3 / 2 : ℝ) ^ k
      ≤ C₂ * Real.exp (2 * L * Real.log (Real.log T)) := by
    have h := hLL P T hP hT
    dsimp only at h
    exact h
  -- the coefficient bracket
  have hBA : C₁ * ((2 ^ k : ℕ) + 1 : ℝ) * (T + ((⌊2 * P⌋₊ ^ k : ℕ) : ℝ))
      * ((k : ℝ) ^ k * ((3 / 2) ^ k / P ^ k))
      ≤ C₁ * ((4 : ℝ) ^ (k + 1) * (k : ℝ) ^ k * (3 / 2 : ℝ) ^ k) := by
    have hpk : (0 : ℝ) < P ^ k := pow_pos hPpos k
    have h1 : ((2 ^ k : ℕ) + 1 : ℝ) * (T + ((⌊2 * P⌋₊ ^ k : ℕ) : ℝ)) * ((3 / 2) ^ k / P ^ k)
        ≤ (4 : ℝ) ^ (k + 1) * (3 / 2 : ℝ) ^ k := by
      have h2 : ((2 ^ k : ℕ) + 1 : ℝ) * (T + ((⌊2 * P⌋₊ ^ k : ℕ) : ℝ))
          ≤ (2 : ℝ) ^ (k + 1) * ((2 : ℝ) ^ (k + 1) * P ^ k) :=
        mul_le_mul hA hB (by positivity) (by positivity)
      calc ((2 ^ k : ℕ) + 1 : ℝ) * (T + ((⌊2 * P⌋₊ ^ k : ℕ) : ℝ)) * ((3 / 2) ^ k / P ^ k)
          ≤ ((2 : ℝ) ^ (k + 1) * ((2 : ℝ) ^ (k + 1) * P ^ k)) * ((3 / 2) ^ k / P ^ k) :=
            mul_le_mul_of_nonneg_right h2 (by positivity)
        _ = (2 : ℝ) ^ (k + 1) * (2 : ℝ) ^ (k + 1) * (3 / 2 : ℝ) ^ k := by
            field_simp
        _ = (4 : ℝ) ^ (k + 1) * (3 / 2 : ℝ) ^ k := by
            rw [← mul_pow]
            norm_num
    calc C₁ * ((2 ^ k : ℕ) + 1 : ℝ) * (T + ((⌊2 * P⌋₊ ^ k : ℕ) : ℝ))
          * ((k : ℝ) ^ k * ((3 / 2) ^ k / P ^ k))
        = C₁ * (k : ℝ) ^ k * (((2 ^ k : ℕ) + 1 : ℝ) * (T + ((⌊2 * P⌋₊ ^ k : ℕ) : ℝ))
          * ((3 / 2) ^ k / P ^ k)) := by ring
      _ ≤ C₁ * (k : ℝ) ^ k * ((4 : ℝ) ^ (k + 1) * (3 / 2 : ℝ) ^ k) :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = C₁ * ((4 : ℝ) ^ (k + 1) * (k : ℝ) ^ k * (3 / 2 : ℝ) ^ k) := by ring
  have hfinal : V ^ (2 * k) * (C₁ * ((2 ^ k : ℕ) + 1 : ℝ)
      * (T + ((⌊2 * P⌋₊ ^ k : ℕ) : ℝ)) * ((k : ℝ) ^ k * ((3 / 2) ^ k / P ^ k)))
      ≤ C₁ * C₂ * (V ^ 2 * T ^ (2 * Real.log V / Real.log P)
          * Real.exp (2 * L * Real.log (Real.log T))) := by
    have hstep1 : V ^ (2 * k) * (C₁ * ((2 ^ k : ℕ) + 1 : ℝ)
          * (T + ((⌊2 * P⌋₊ ^ k : ℕ) : ℝ)) * ((k : ℝ) ^ k * ((3 / 2) ^ k / P ^ k)))
        ≤ V ^ (2 * k) * (C₁ * ((4 : ℝ) ^ (k + 1) * (k : ℝ) ^ k * (3 / 2 : ℝ) ^ k)) :=
      mul_le_mul_of_nonneg_left hBA (by positivity)
    have hstep2 : V ^ (2 * k) * (C₁ * ((4 : ℝ) ^ (k + 1) * (k : ℝ) ^ k * (3 / 2 : ℝ) ^ k))
        ≤ (V ^ 2 * T ^ (2 * Real.log V / Real.log P))
          * (C₁ * (C₂ * Real.exp (2 * L * Real.log (Real.log T)))) := by
      have h1 : V ^ (2 * k) ≤ V ^ 2 * T ^ (2 * Real.log V / Real.log P) := hD
      have h2 : C₁ * ((4 : ℝ) ^ (k + 1) * (k : ℝ) ^ k * (3 / 2 : ℝ) ^ k)
          ≤ C₁ * (C₂ * Real.exp (2 * L * Real.log (Real.log T))) :=
        mul_le_mul_of_nonneg_left hC hC₁pos.le
      exact mul_le_mul h1 h2 (by positivity) (by positivity)
    calc V ^ (2 * k) * (C₁ * ((2 ^ k : ℕ) + 1 : ℝ)
          * (T + ((⌊2 * P⌋₊ ^ k : ℕ) : ℝ)) * ((k : ℝ) ^ k * ((3 / 2) ^ k / P ^ k)))
        ≤ V ^ (2 * k) * (C₁ * ((4 : ℝ) ^ (k + 1) * (k : ℝ) ^ k * (3 / 2 : ℝ) ^ k)) := hstep1
      _ ≤ (V ^ 2 * T ^ (2 * Real.log V / Real.log P))
          * (C₁ * (C₂ * Real.exp (2 * L * Real.log (Real.log T)))) := hstep2
      _ = C₁ * C₂ * (V ^ 2 * T ^ (2 * Real.log V / Real.log P)
          * Real.exp (2 * L * Real.log (Real.log T))) := by ring
  calc (R : ℝ) ≤ V ^ (2 * k) * (C₁ * ((2 ^ k : ℕ) + 1 : ℝ)
        * (T + ((⌊2 * P⌋₊ ^ k : ℕ) : ℝ)) * ((k : ℝ) ^ k * ((3 / 2) ^ k / P ^ k))) := hmain
    _ ≤ C₁ * C₂ * (V ^ 2 * T ^ (2 * Real.log V / Real.log P)
          * Real.exp (2 * L * Real.log (Real.log T))) := hfinal
    _ = C₁ * C₂ * (T ^ (2 * Real.log V / Real.log P) * V ^ 2
          * Real.exp (2 * (Real.log T / Real.log P) * Real.log (Real.log T))) := by
        rw [hLdef]
        ring

end Work.BMF.mr_direct
