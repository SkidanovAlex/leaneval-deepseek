import Mathlib
import Submission.Work.BMF.mr_direct.primePoly_large_values
import Submission.Work.BMF.mr_direct.primePolyWindow_defs
import Submission.Work.BMF.mr_direct.winPowCoeff_energy
import Submission.Work.BMF.mr_direct.winPow_eq
import Submission.Work.BMF.mr_direct.winSet_inv_sums
import Submission.Work.BMF.mr_direct.expLogLog_ineq_win

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Large values of the prime-supported Dirichlet polynomial on a general window

This is the *window* (`[A, B]` with `A ≤ B ≤ 4A`) version of Lemma `le:Rupest` of
K. Matomäki, M. Radziwiłł, T. Tao, J. Teräväinen, T. Ziegler, *Higher uniformity of bounded
multiplicative functions in short intervals on average* (Annals of Math. 197 (2023)).

Let `P(s) = Σ_{A ≤ p ≤ B} a_p p^{-s}` with `|a_p| ≤ 1` and let `𝒯 ⊆ [-T, T]` be a set of
well-spaced points with `|P(1+it)| ≥ V^{-1}` for `t ∈ 𝒯`.  Then

`|𝒯| ≪ T^{2 log V / log A} · V^2 · exp(2 (log T / log A) log log T)`.

The proof is the paper's, with the dyadic interval `[P, 2P]` replaced by the window `[A, B]`
(`B ≤ 4A`): with `k = ⌈log T / log A⌉`, the `k`-th power `P(s)^k` is supported on
`[A^k, B^k] ⊆ [A^k, (4A)^k]`, so a sampled (large-sieve) mean-value estimate with `4^k`
blocks gives `Σ_t |P(1+it)|^{2k} ≪ 4^k (T + B^k) Σ_n |b_n|²`; the `ℓ²`-mass of `b` is at
most `k^k (Σ_{A≤p≤B} 1/p²)^k ≤ k^k (5/A)^k`, and `V^{2k} ≤ V^2 T^{2 log V/log A}`.
-/

set_option maxHeartbeats 1000000
set_option autoImplicit false

namespace Work.BMF.mr_direct

open Finset
open scoped BigOperators

theorem primePoly_large_values_window :
    ∃ C : ℝ, 0 < C ∧
      ∀ (A B V T : ℝ) (R : ℕ) (t : Fin R → ℝ) (c : ℕ → ℂ),
        2 ≤ A → A ≤ B → B ≤ 4 * A → 3 ≤ T → 1 ≤ V → (∀ p, ‖c p‖ ≤ 1) →
        (∀ i j : Fin R, i ≠ j → 1 ≤ |t i - t j|) →
        (∀ i, t i ∈ Set.Icc (-T) T) →
        (∀ i, 1 / V ≤ ‖∑ p ∈ (Finset.Icc ⌈A⌉₊ ⌊B⌋₊).filter Nat.Prime,
              c p * (p : ℂ) ^ (-(1 + Complex.I * (t i : ℂ)))‖) →
        (R : ℝ) ≤ C * (T ^ (2 * Real.log V / Real.log A) * V ^ 2
              * Real.exp (2 * (Real.log T / Real.log A) * Real.log (Real.log T))) := by
  obtain ⟨C₁, hC₁pos, hMV⟩ := sampled_mean_value_blocks
  obtain ⟨C₂, hC₂pos, hLL⟩ := expLogLog_ineq_win
  refine ⟨C₁ * C₂, by positivity, ?_⟩
  intro A B V T R t c hA hAB hB4 hT hV hc hsep hIcc hval
  have hA1 : (1 : ℝ) < A := by linarith
  have hApos : 0 < A := by linarith
  have hBpos : 0 < B := by linarith
  have hT1 : (1 : ℝ) < T := by linarith
  have hTpos : 0 < T := by linarith
  have hV1 : (1 : ℝ) ≤ V := hV
  have hVpos : 0 < V := by linarith
  have hlogA : 0 < Real.log A := Real.log_pos hA1
  have hlogT : 0 < Real.log T := Real.log_pos hT1
  have hratio : 0 < Real.log T / Real.log A := div_pos hlogT hlogA
  set k : ℕ := Nat.ceil (Real.log T / Real.log A) with hkdef
  set L : ℝ := Real.log T / Real.log A with hLdef
  have hLpos : 0 < L := by rw [hLdef]; exact hratio
  have hk1 : 1 ≤ k := by rw [hkdef]; exact Nat.one_le_ceil_iff.mpr hratio
  have hkL : L ≤ (k : ℝ) := by rw [hLdef, hkdef]; exact Nat.le_ceil _
  have hkL1 : (k : ℝ) ≤ L + 1 := by
    have h := Nat.ceil_lt_add_one (le_of_lt hratio)
    rw [← hkdef] at h
    rw [hLdef] at h
    linarith
  -- `T ≤ A ^ k`
  have hTleAk : T ≤ A ^ k := by
    have h1 : Real.log T ≤ (k : ℝ) * Real.log A := by
      have h2 : Real.log T = L * Real.log A := by rw [hLdef]; field_simp
      rw [h2]
      exact mul_le_mul_of_nonneg_right hkL hlogA.le
    calc T = Real.exp (Real.log T) := (Real.exp_log hTpos).symm
      _ ≤ Real.exp ((k : ℝ) * Real.log A) := Real.exp_le_exp.mpr h1
      _ = A ^ ((k : ℝ)) := by rw [Real.rpow_def_of_pos hApos]; ring_nf
      _ = A ^ k := Real.rpow_natCast A k
  -- the hypothesis, in terms of `winDirPoly`
  have hval' : ∀ i : Fin R, 1 / V ≤ ‖primePolyWindow.winDirPoly c A B (t i)‖ :=
    fun i => hval i
  -- lower bound coming from the large-values hypothesis
  have hval2 : ∀ i : Fin R,
      (1 / V) ^ (2 * k) ≤ ‖primePolyWindow.winDirPoly c A B (t i)‖ ^ (2 * k) := by
    intro i
    exact pow_le_pow_left₀ (by positivity) (hval' i) (2 * k)
  have hsum_low : (R : ℝ) * (1 / V) ^ (2 * k)
      ≤ ∑ i : Fin R, ‖primePolyWindow.winDirPoly c A B (t i)‖ ^ (2 * k) := by
    calc (R : ℝ) * (1 / V) ^ (2 * k) = ∑ _i : Fin R, (1 / V) ^ (2 * k) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      _ ≤ ∑ i : Fin R, ‖primePolyWindow.winDirPoly c A B (t i)‖ ^ (2 * k) :=
          Finset.sum_le_sum (fun i _ => hval2 i)
  -- the power expansion and its support
  have hpow := (winPow_eq A B c k hA hAB hk1).1
  have hsupp := (winPow_eq A B c k hA hAB hk1).2
  have hN1 : 1 ≤ ⌈A⌉₊ ^ k := one_le_pow₀ (Nat.one_le_ceil_iff.mpr hApos)
  have hsupp_zero : ∀ n : ℕ, n ∉ Finset.Icc (⌈A⌉₊ ^ k) (⌊B⌋₊ ^ k) →
      primePolyWindow.winPowCoeff c A B k n = 0 := by
    intro n hn
    by_contra hne
    exact hn (hsupp n hne)
  -- rewrite each term using the `k`-th power expansion and conjugation
  have hone : ∀ i : Fin R, ‖primePolyWindow.winDirPoly c A B (t i)‖ ^ (2 * k)
      = ‖∑ n ∈ Finset.Icc (⌈A⌉₊ ^ k) (⌊B⌋₊ ^ k),
            (starRingEnd ℂ) (primePolyWindow.winPowCoeff c A B k n) *
              (n : ℂ) ^ (Complex.I * ((t i : ℝ) : ℂ))‖ ^ 2 := by
    intro i
    have h1 : ‖primePolyWindow.winDirPoly c A B (t i)‖ ^ (2 * k)
        = ‖(primePolyWindow.winDirPoly c A B (t i)) ^ k‖ ^ 2 := by
      rw [norm_pow, ← pow_mul, Nat.mul_comm]
    have h2 : (primePolyWindow.winDirPoly c A B (t i)) ^ k
        = ∑ n ∈ Finset.Icc 1 (⌊B⌋₊ ^ k),
            primePolyWindow.winPowCoeff c A B k n *
              (n : ℂ) ^ (-(Complex.I * ((t i : ℝ) : ℂ))) := hpow (t i)
    have h3 : (∑ n ∈ Finset.Icc 1 (⌊B⌋₊ ^ k),
            primePolyWindow.winPowCoeff c A B k n *
              (n : ℂ) ^ (-(Complex.I * ((t i : ℝ) : ℂ))))
        = ∑ n ∈ Finset.Icc (⌈A⌉₊ ^ k) (⌊B⌋₊ ^ k),
            primePolyWindow.winPowCoeff c A B k n *
              (n : ℂ) ^ (-(Complex.I * ((t i : ℝ) : ℂ))) := by
      refine (Finset.sum_subset ?_ ?_).symm
      · intro n hn
        rw [Finset.mem_Icc] at hn ⊢
        exact ⟨le_trans hN1 hn.1, hn.2⟩
      · intro n _ hn
        rw [hsupp_zero n hn, zero_mul]
    have h4 : (∑ n ∈ Finset.Icc (⌈A⌉₊ ^ k) (⌊B⌋₊ ^ k),
            primePolyWindow.winPowCoeff c A B k n *
              (n : ℂ) ^ (-(Complex.I * ((t i : ℝ) : ℂ))))
        = (starRingEnd ℂ) (∑ n ∈ Finset.Icc (⌈A⌉₊ ^ k) (⌊B⌋₊ ^ k),
            (starRingEnd ℂ) (primePolyWindow.winPowCoeff c A B k n) *
              (n : ℂ) ^ (Complex.I * ((t i : ℝ) : ℂ))) := by
      rw [map_sum]
      apply Finset.sum_congr rfl
      intro n hn
      have hn1 : 1 ≤ n := le_trans hN1 (Finset.mem_Icc.mp hn).1
      rw [map_mul, conj_cpow_natCast hn1]
      have hz : (starRingEnd ℂ) (Complex.I * ((t i : ℝ) : ℂ))
          = -(Complex.I * ((t i : ℝ) : ℂ)) := by simp [Complex.conj_I]
      rw [hz]
      have hbb : (starRingEnd ℂ) ((starRingEnd ℂ) (primePolyWindow.winPowCoeff c A B k n))
          = primePolyWindow.winPowCoeff c A B k n := by simp
      rw [hbb]
    rw [h1, h2, h3, h4, Complex.norm_conj]
  -- the sampled mean value estimate
  have hK1 : 1 ≤ 4 ^ k := one_le_pow₀ (by norm_num : (1 : ℕ) ≤ 4)
  have hfle : ⌊B⌋₊ ≤ 4 * ⌈A⌉₊ := by
    have h1 : ((⌊B⌋₊ : ℕ) : ℝ) ≤ B := Nat.floor_le (le_of_lt hBpos)
    have h3 : A ≤ (⌈A⌉₊ : ℝ) := Nat.le_ceil A
    have h2 : ((⌊B⌋₊ : ℕ) : ℝ) ≤ 4 * (⌈A⌉₊ : ℝ) := by linarith
    exact_mod_cast h2
  have hMK : ⌊B⌋₊ ^ k ≤ ⌈A⌉₊ ^ k * 4 ^ k := by
    calc ⌊B⌋₊ ^ k ≤ (4 * ⌈A⌉₊) ^ k := Nat.pow_le_pow_left hfle k
      _ = ⌈A⌉₊ ^ k * 4 ^ k := by rw [mul_pow, mul_comm]
  have hsupp_a : ∀ n, n ∉ Finset.Icc (⌈A⌉₊ ^ k) (⌊B⌋₊ ^ k) →
      (fun n => (starRingEnd ℂ) (primePolyWindow.winPowCoeff c A B k n)) n = 0 := by
    intro n hn
    show (starRingEnd ℂ) (primePolyWindow.winPowCoeff c A B k n) = 0
    rw [hsupp_zero n hn, map_zero]
  have hMV'' := hMV (⌈A⌉₊ ^ k) (⌊B⌋₊ ^ k) (4 ^ k)
      (fun n => (starRingEnd ℂ) (primePolyWindow.winPowCoeff c A B k n)) T R t
      hN1 hK1 (le_of_lt hTpos) hMK hsupp_a hIcc hsep
  have hMV' : (∑ i : Fin R, ‖∑ n ∈ Finset.Icc (⌈A⌉₊ ^ k) (⌊B⌋₊ ^ k),
        (starRingEnd ℂ) (primePolyWindow.winPowCoeff c A B k n) *
          (n : ℂ) ^ (Complex.I * ((t i : ℝ) : ℂ))‖ ^ 2)
      ≤ C₁ * ((4 ^ k : ℕ) + 1 : ℝ) * (T + ((⌊B⌋₊ ^ k : ℕ) : ℝ))
          * (∑ n ∈ Finset.Icc (⌈A⌉₊ ^ k) (⌊B⌋₊ ^ k),
              ‖primePolyWindow.winPowCoeff c A B k n‖ ^ 2) := by
    have hsum : (∑ n ∈ Finset.Icc (⌈A⌉₊ ^ k) (⌊B⌋₊ ^ k),
          ‖(starRingEnd ℂ) (primePolyWindow.winPowCoeff c A B k n)‖ ^ 2)
        = (∑ n ∈ Finset.Icc (⌈A⌉₊ ^ k) (⌊B⌋₊ ^ k),
            ‖primePolyWindow.winPowCoeff c A B k n‖ ^ 2) := by
      apply Finset.sum_congr rfl
      intro n _
      rw [Complex.norm_conj]
    rw [hsum] at hMV''
    exact hMV''
  -- energy bound
  have hσ : (∑ p ∈ primePolyWindow.winSet A B, (1 : ℝ) / (p : ℝ) ^ 2) ≤ 5 / A :=
    (winSet_inv_sums A B hA hAB hB4).2
  have henergy : (∑ n ∈ Finset.Icc (⌈A⌉₊ ^ k) (⌊B⌋₊ ^ k),
        ‖primePolyWindow.winPowCoeff c A B k n‖ ^ 2) ≤ (k : ℝ) ^ k * (5 / A) ^ k := by
    have hE := winPowCoeff_energy A B c k hA hAB hk1 hc
    have hswap : (∑ n ∈ Finset.Icc (⌈A⌉₊ ^ k) (⌊B⌋₊ ^ k),
          ‖primePolyWindow.winPowCoeff c A B k n‖ ^ 2)
        = (∑ n ∈ Finset.Icc 1 (⌊B⌋₊ ^ k),
            ‖primePolyWindow.winPowCoeff c A B k n‖ ^ 2) := by
      refine Finset.sum_subset ?_ ?_
      · intro n hn
        rw [Finset.mem_Icc] at hn ⊢
        exact ⟨le_trans hN1 hn.1, hn.2⟩
      · intro n _ hn
        rw [hsupp_zero n hn]
        simp
    rw [hswap]
    calc (∑ n ∈ Finset.Icc 1 (⌊B⌋₊ ^ k), ‖primePolyWindow.winPowCoeff c A B k n‖ ^ 2)
        ≤ (k : ℝ) ^ k *
            (∑ p ∈ primePolyWindow.winSet A B, (1 : ℝ) / (p : ℝ) ^ 2) ^ k := hE
      _ ≤ (k : ℝ) ^ k * (5 / A) ^ k := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          exact pow_le_pow_left₀ (Finset.sum_nonneg (fun p _ => by positivity)) hσ k
  -- assemble the intermediate bound
  have hcoef : (0 : ℝ) ≤ C₁ * ((4 ^ k : ℕ) + 1 : ℝ) * (T + ((⌊B⌋₊ ^ k : ℕ) : ℝ)) :=
    mul_nonneg (mul_nonneg hC₁pos.le (by positivity)) (by positivity)
  have hmain : (R : ℝ) ≤ V ^ (2 * k) * (C₁ * ((4 ^ k : ℕ) + 1 : ℝ)
      * (T + ((⌊B⌋₊ ^ k : ℕ) : ℝ)) * ((k : ℝ) ^ k * (5 / A) ^ k)) := by
    have h2 : (R : ℝ) * (1 / V) ^ (2 * k) ≤ C₁ * ((4 ^ k : ℕ) + 1 : ℝ)
        * (T + ((⌊B⌋₊ ^ k : ℕ) : ℝ)) * ((k : ℝ) ^ k * (5 / A) ^ k) := by
      calc (R : ℝ) * (1 / V) ^ (2 * k)
          ≤ ∑ i : Fin R, ‖primePolyWindow.winDirPoly c A B (t i)‖ ^ (2 * k) := hsum_low
        _ = ∑ i : Fin R, ‖∑ n ∈ Finset.Icc (⌈A⌉₊ ^ k) (⌊B⌋₊ ^ k),
              (starRingEnd ℂ) (primePolyWindow.winPowCoeff c A B k n) *
                (n : ℂ) ^ (Complex.I * ((t i : ℝ) : ℂ))‖ ^ 2 :=
              Finset.sum_congr rfl (fun i _ => hone i)
        _ ≤ C₁ * ((4 ^ k : ℕ) + 1 : ℝ) * (T + ((⌊B⌋₊ ^ k : ℕ) : ℝ))
              * (∑ n ∈ Finset.Icc (⌈A⌉₊ ^ k) (⌊B⌋₊ ^ k),
                  ‖primePolyWindow.winPowCoeff c A B k n‖ ^ 2) := hMV'
        _ ≤ C₁ * ((4 ^ k : ℕ) + 1 : ℝ) * (T + ((⌊B⌋₊ ^ k : ℕ) : ℝ))
              * ((k : ℝ) ^ k * (5 / A) ^ k) :=
              mul_le_mul_of_nonneg_left henergy hcoef
    have h3 : (1 / V) ^ (2 * k) * V ^ (2 * k) = 1 := by
      rw [← mul_pow]
      have h4 : (1 / V) * V = 1 := by field_simp
      rw [h4, one_pow]
    calc (R : ℝ) = (R : ℝ) * ((1 / V) ^ (2 * k) * V ^ (2 * k)) := by rw [h3, mul_one]
      _ = ((R : ℝ) * (1 / V) ^ (2 * k)) * V ^ (2 * k) := by ring
      _ ≤ (C₁ * ((4 ^ k : ℕ) + 1 : ℝ) * (T + ((⌊B⌋₊ ^ k : ℕ) : ℝ))
            * ((k : ℝ) ^ k * (5 / A) ^ k)) * V ^ (2 * k) :=
          mul_le_mul_of_nonneg_right h2 (by positivity)
      _ = V ^ (2 * k) * (C₁ * ((4 ^ k : ℕ) + 1 : ℝ)
            * (T + ((⌊B⌋₊ ^ k : ℕ) : ℝ)) * ((k : ℝ) ^ k * (5 / A) ^ k)) := by ring
  -- numeric bounds
  have h4k : ((4 ^ k : ℕ) + 1 : ℝ) ≤ 2 * (4 : ℝ) ^ k := by
    have h1 : (1 : ℝ) ≤ (4 : ℝ) ^ k := one_le_pow₀ (by norm_num)
    have h2 : ((4 ^ k : ℕ) : ℝ) = (4 : ℝ) ^ k := by push_cast; ring
    linarith
  have hBk : (T + ((⌊B⌋₊ ^ k : ℕ) : ℝ)) ≤ 2 * (8 : ℝ) ^ k * A ^ k := by
    have h1 : ((⌊B⌋₊ ^ k : ℕ) : ℝ) ≤ (8 * A) ^ k := by
      have hfl : ((⌊B⌋₊ : ℕ) : ℝ) ≤ 8 * A := by
        have := Nat.floor_le (le_of_lt hBpos)
        linarith
      calc ((⌊B⌋₊ ^ k : ℕ) : ℝ) = ((⌊B⌋₊ : ℕ) : ℝ) ^ k := by push_cast; ring
        _ ≤ (8 * A) ^ k := pow_le_pow_left₀ (by positivity) hfl k
    have h2 : (1 : ℝ) ≤ (8 : ℝ) ^ k := one_le_pow₀ (by norm_num)
    calc T + ((⌊B⌋₊ ^ k : ℕ) : ℝ) ≤ A ^ k + (8 * A) ^ k := add_le_add hTleAk h1
      _ = A ^ k + 8 ^ k * A ^ k := by rw [mul_pow]
      _ = A ^ k * (1 + 8 ^ k) := by ring
      _ ≤ A ^ k * (2 * 8 ^ k) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          linarith
      _ = 2 * 8 ^ k * A ^ k := by ring
  have hAB2 : (((4 ^ k : ℕ) + 1 : ℝ)) * (T + ((⌊B⌋₊ ^ k : ℕ) : ℝ))
      ≤ 4 * (32 : ℝ) ^ k * A ^ k := by
    calc (((4 ^ k : ℕ) + 1 : ℝ)) * (T + ((⌊B⌋₊ ^ k : ℕ) : ℝ))
        ≤ (2 * (4 : ℝ) ^ k) * (2 * (8 : ℝ) ^ k * A ^ k) :=
          mul_le_mul h4k hBk (by positivity) (by positivity)
      _ = 4 * ((4 : ℝ) ^ k * (8 : ℝ) ^ k) * A ^ k := by ring
      _ = 4 * (32 : ℝ) ^ k * A ^ k := by
          rw [show (4 : ℝ) ^ k * (8 : ℝ) ^ k = (32 : ℝ) ^ k by
            rw [← mul_pow]; norm_num]
  have hBA : C₁ * ((4 ^ k : ℕ) + 1 : ℝ) * (T + ((⌊B⌋₊ ^ k : ℕ) : ℝ))
      * ((k : ℝ) ^ k * (5 / A) ^ k) ≤ C₁ * (4 * (160 : ℝ) ^ k * (k : ℝ) ^ k) := by
    have hstep : (((4 ^ k : ℕ) + 1 : ℝ) * (T + ((⌊B⌋₊ ^ k : ℕ) : ℝ))) * ((5 / A) ^ k)
        ≤ 4 * (160 : ℝ) ^ k := by
      have h0 : (0 : ℝ) ≤ (5 / A) ^ k := by positivity
      have h1 := mul_le_mul_of_nonneg_right hAB2 h0
      have hA5 : A ^ k * (5 / A) ^ k = (5 : ℝ) ^ k := by
        rw [← mul_pow]
        have hA5' : A * (5 / A) = 5 := by field_simp
        rw [hA5']
      have h2 : (4 * (32 : ℝ) ^ k * A ^ k) * (5 / A) ^ k = 4 * (160 : ℝ) ^ k := by
        calc (4 * (32 : ℝ) ^ k * A ^ k) * (5 / A) ^ k
            = 4 * ((32 : ℝ) ^ k * (A ^ k * (5 / A) ^ k)) := by ring
          _ = 4 * ((32 : ℝ) ^ k * (5 : ℝ) ^ k) := by rw [hA5]
          _ = 4 * (160 : ℝ) ^ k := by
              rw [show (32 : ℝ) ^ k * (5 : ℝ) ^ k = (160 : ℝ) ^ k by
                rw [← mul_pow]; norm_num]
      rwa [h2] at h1
    calc C₁ * ((4 ^ k : ℕ) + 1 : ℝ) * (T + ((⌊B⌋₊ ^ k : ℕ) : ℝ))
          * ((k : ℝ) ^ k * (5 / A) ^ k)
        = C₁ * (k : ℝ) ^ k
            * ((((4 ^ k : ℕ) + 1 : ℝ) * (T + ((⌊B⌋₊ ^ k : ℕ) : ℝ))) * ((5 / A) ^ k)) := by
          ring
      _ ≤ C₁ * (k : ℝ) ^ k * (4 * (160 : ℝ) ^ k) := by
          apply mul_le_mul_of_nonneg_left hstep
          positivity
      _ = C₁ * (4 * (160 : ℝ) ^ k * (k : ℝ) ^ k) := by ring
  have h1000 : 4 * (160 : ℝ) ^ k * (k : ℝ) ^ k ≤ (1000 : ℝ) ^ k * (k : ℝ) ^ k := by
    have h1 : (4 : ℝ) ≤ (4 : ℝ) ^ k := by
      calc (4 : ℝ) = (4 : ℝ) ^ 1 := (pow_one 4).symm
        _ ≤ (4 : ℝ) ^ k := pow_le_pow_right₀ (by norm_num) hk1
    have h2 : 4 * (160 : ℝ) ^ k ≤ (1000 : ℝ) ^ k := by
      have h4 : 4 * (160 : ℝ) ^ k ≤ (4 : ℝ) ^ k * (160 : ℝ) ^ k :=
        mul_le_mul_of_nonneg_right h1 (by positivity)
      have h5 : (4 : ℝ) ^ k * (160 : ℝ) ^ k = (640 : ℝ) ^ k := by
        rw [← mul_pow]; norm_num
      have h6 : (640 : ℝ) ^ k ≤ (1000 : ℝ) ^ k :=
        pow_le_pow_left₀ (by norm_num) (by norm_num) k
      linarith
    exact mul_le_mul_of_nonneg_right h2 (by positivity)
  have hC : C₁ * (4 * (160 : ℝ) ^ k * (k : ℝ) ^ k)
      ≤ C₁ * C₂ * Real.exp (2 * L * Real.log (Real.log T)) := by
    have hLL' := hLL A T k hA hT (by rw [← hLdef]; exact hkL)
      (by rw [← hLdef]; exact hkL1)
    calc C₁ * (4 * (160 : ℝ) ^ k * (k : ℝ) ^ k)
        ≤ C₁ * ((1000 : ℝ) ^ k * (k : ℝ) ^ k) := mul_le_mul_of_nonneg_left h1000 hC₁pos.le
      _ ≤ C₁ * (C₂ * Real.exp (2 * (Real.log T / Real.log A) * Real.log (Real.log T))) :=
            mul_le_mul_of_nonneg_left hLL' hC₁pos.le
      _ = C₁ * C₂ * Real.exp (2 * L * Real.log (Real.log T)) := by rw [hLdef]; ring
  have hD : V ^ (2 * k) ≤ V ^ 2 * T ^ (2 * Real.log V / Real.log A) := by
    have h1 : ((2 * k : ℕ) : ℝ) ≤ 2 * L + 2 := by
      push_cast
      linarith [hkL1]
    have h2 : V ^ (2 * k) ≤ V ^ (2 * L + 2) := by
      calc V ^ (2 * k) = V ^ (((2 * k : ℕ) : ℝ)) := (Real.rpow_natCast V (2 * k)).symm
        _ ≤ V ^ (2 * L + 2) := Real.rpow_le_rpow_of_exponent_le hV1 h1
    have h3 : V ^ (2 * L + 2) = V ^ (2 * L) * V ^ 2 := by
      rw [Real.rpow_add hVpos]
      norm_num
    have h4 : V ^ (2 * L) = T ^ (2 * Real.log V / Real.log A) := by
      rw [Real.rpow_def_of_pos hVpos, Real.rpow_def_of_pos hTpos]
      congr 1
      rw [hLdef]
      field_simp
    calc V ^ (2 * k) ≤ V ^ (2 * L + 2) := h2
      _ = V ^ (2 * L) * V ^ 2 := h3
      _ = T ^ (2 * Real.log V / Real.log A) * V ^ 2 := by rw [h4]
      _ = V ^ 2 * T ^ (2 * Real.log V / Real.log A) := by ring
  -- final assembly
  calc (R : ℝ)
      ≤ V ^ (2 * k) * (C₁ * ((4 ^ k : ℕ) + 1 : ℝ)
          * (T + ((⌊B⌋₊ ^ k : ℕ) : ℝ)) * ((k : ℝ) ^ k * (5 / A) ^ k)) := hmain
    _ ≤ V ^ (2 * k) * (C₁ * (4 * (160 : ℝ) ^ k * (k : ℝ) ^ k)) :=
          mul_le_mul_of_nonneg_left hBA (by positivity)
    _ ≤ (V ^ 2 * T ^ (2 * Real.log V / Real.log A))
          * (C₁ * C₂ * Real.exp (2 * L * Real.log (Real.log T))) := by
          apply mul_le_mul hD hC
          · positivity
          · positivity
    _ = C₁ * C₂ * (T ^ (2 * Real.log V / Real.log A) * V ^ 2
          * Real.exp (2 * (Real.log T / Real.log A) * Real.log (Real.log T))) := by
          rw [hLdef]
          ring

end Work.BMF.mr_direct
