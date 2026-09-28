import Mathlib
import Submission.Work.HP.MM2.Defs
import Submission.Work.HP.MM2.Sk2_short_sum_le
import Submission.Work.HP.MM2.Sk2_Tloc_le_pow
import Submission.Work.HP.MM2.iotaDN_pos
import Submission.Work.HP.MM2.locMain_lower
import Submission.Work.HP.MM2.tail_arith
import Submission.Work.HP.bigW_le_pow
import Submission.Work.HP.w_arith
import Submission.Work.HP.six_le_NN
import Submission.Work.HP.DeltaXY_gcd_detL

/-!
# The tail of the local Möbius sum (node N09, Lemma D local)

Browning--Le Boudec--Sawin, proof of Lemma D local, define `W = bigW (wOf B)`,
`α = log B` and, for a pair of independent primitive vectors `x, y`,

`𝒮₂^{*}(Γ^{loc}_{x,y}(W); 𝒯^{loc}_{x,y}(A,α)) = Σ_{ℓ ≤ A} (μ(ℓ)/ℓ²) 𝒮₂(Γ^{loc}_{x,y}(W/gcd(ℓ,W));
𝒯^{loc}_{x,y}(A/ℓ,α))`.

They split at `ℓ = A/W`.  For `ℓ > A/W` the trivial lattice-point bound ("Upper bound trivial t"
with `k = 2`, `u = A/ℓ`) gives `𝒮₂ ≪ (A/ℓ)^{N-2}`, whence

`Σ_{ℓ > A/W} (μ(ℓ)/ℓ²) 𝒮₂(…) ≪ W^{N-1}/A`.

The lemma below records this as a bound by the per-pair main term `locMain` (which dominates
`8 ι A^{N-2}/(αW)²`), with the uniform constant needed by the pair summation `Dloc_estimate`.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

noncomputable section

namespace Work.HP.MM2

open Filter Finset

/-- `𝓢_k(Λ;R) ≥ 0`: every summand is `‖a‖^{-k} ≥ 0`. -/
private lemma Sk_nonneg (d n : ℕ) [DecidableEq (Mon d n)] (k : ℕ)
    (L : Submodule ℤ (Mon d n → ℤ)) (R : Set (Mon d n → ℤ)) : 0 ≤ Sk d n k L R := by
  rw [Sk, finsum_mem_def]
  refine finsum_nonneg fun a => ?_
  by_cases h : a ∈ {a : Mon d n → ℤ | a ∈ L ∧ a ≠ 0 ∧ a ∈ R}
  · rw [Set.indicator_of_mem h]
    exact div_nonneg zero_le_one (pow_nonneg (eNorm_nonneg a) k)
  · rw [Set.indicator_of_notMem h]

/-- **The tail bound.**  Assuming

* the trivial lattice-point bound `𝒮₂(Γ(Q); 𝒯^{loc}(T,α)) ≪ T^{N-2}` (`hSk`),
* `0 < ι_{d,n}` (`hι`),
* `locMain d n A B (x,y) ≥ 8 ι_{d,n} A^{N-2}/(αW)²` (`hloc`),

* the numeric inequality `2KW^N/A ≤ C·(8ιA^{N-2}/(αW)²)/log A` (`harith`),

the `ℓ > A/W` tail of the local Möbius sum is `≤ C · locMain/log A` uniformly. -/
private theorem Sstar2_loc_tail_aux (d n : ℕ) [DecidableEq (Mon d n)] (hd : 2 ≤ d) (hdn : d ≤ n)
    (hSk : ∃ K : ℝ, 0 < K ∧ ∀ (x y : Fin (n + 1) → ℤ) (Q : ℕ) (T α : ℝ), 1 ≤ T →
      Sk d n 2 (GamLoc d n x y Q) (TlocSet d n x y T α) ≤ K * T ^ (NN d n - 2))
    (hι : 0 < iotaDN d n)
    (hloc : ∀ (A B : ℝ) (x y : Fin (n + 1) → ℤ), 0 < A → 1 < B → IsPrim x → IsPrim y →
      LinearIndependent ℤ ![x, y] →
      8 * iotaDN d n * A ^ (NN d n - 2) / ((Real.log B * (bigW (wOf B) : ℝ)) ^ 2)
        ≤ locMain d n A B (x, y))
    (harith : ∀ K ι : ℝ, 0 < K → 0 < ι → ∃ C B₀ : ℝ, 0 < C ∧ ∀ A B : ℝ, B₀ ≤ B →
      B ^ ((5 : ℝ) / 6) ≤ A → A ≤ B ^ 2 →
      2 * K * (bigW (wOf B) : ℝ) ^ (NN d n) / A
        ≤ C * (8 * ι * A ^ (NN d n - 2) / ((Real.log B * (bigW (wOf B) : ℝ)) ^ 2))
            / Real.log A) :
    ∃ C B₀ : ℝ, 0 < C ∧ ∀ A B : ℝ, B₀ ≤ B → B ^ ((5 : ℝ) / 6) ≤ A → A ≤ B ^ 2 →
      ∀ x y : Fin (n + 1) → ℤ, IsPrim x → IsPrim y → LinearIndependent ℤ ![x, y] →
      |∑ ℓ ∈ Finset.Icc (⌊A / (bigW (wOf B) : ℝ)⌋₊ + 1) ⌊A⌋₊,
          ((ArithmeticFunction.moebius ℓ : ℝ) / (ℓ : ℝ) ^ 2) *
            Sk d n 2 (GamLoc d n x y (bigW (wOf B) / Nat.gcd ℓ (bigW (wOf B))))
              (TlocSet d n x y (A / (ℓ : ℝ)) (Real.log B))|
        ≤ C * locMain d n A B (x, y) / Real.log A := by
  classical
  obtain ⟨KA, hKApos, hKA⟩ := hSk
  obtain ⟨C, B₀, hCpos, hC⟩ := harith KA (iotaDN d n) hKApos hι
  refine ⟨C, max B₀ (Real.exp 2), hCpos, ?_⟩
  intro A B hB hAB hA2 x y hx hy hxy
  have hB0 : Real.exp 2 ≤ B := le_trans (le_max_right B₀ (Real.exp 2)) hB
  have hBhi : B₀ ≤ B := le_trans (le_max_left B₀ (Real.exp 2)) hB
  have hB1 : (1 : ℝ) ≤ B := le_trans (Real.one_le_exp (by norm_num)) hB0
  have hexp2lt : (1 : ℝ) < Real.exp 2 := by
    have h := Real.exp_lt_exp.mpr (show (0 : ℝ) < 2 by norm_num)
    rwa [Real.exp_zero] at h
  have hlogB2 : (2 : ℝ) ≤ Real.log B := by
    have h := Real.log_le_log (Real.exp_pos 2) hB0
    rwa [Real.log_exp] at h
  have hlogBpos : (0 : ℝ) < Real.log B := by linarith
  have hexp_le : (Real.exp 2) ^ ((5 : ℝ) / 6) ≤ B ^ ((5 : ℝ) / 6) :=
    Real.rpow_le_rpow (Real.exp_pos 2).le hB0 (by norm_num)
  have hone_le : (1 : ℝ) ≤ (Real.exp 2) ^ ((5 : ℝ) / 6) :=
    Real.one_le_rpow (le_of_lt hexp2lt) (by norm_num)
  have hA1 : (1 : ℝ) ≤ A := le_trans (le_trans hone_le hexp_le) hAB
  have hApos : (0 : ℝ) < A := lt_of_lt_of_le one_pos hA1
  have hlogAnn : (0 : ℝ) ≤ Real.log A := Real.log_nonneg hA1
  have hBgt1 : (1 : ℝ) < B := lt_of_lt_of_le hexp2lt hB0
  have hW1 : (1 : ℝ) ≤ (bigW (wOf B) : ℝ) := by exact_mod_cast one_le_bigW (wOf B)
  have hWpos : (0 : ℝ) < (bigW (wOf B) : ℝ) := lt_of_lt_of_le one_pos hW1
  have hN2 : 2 ≤ NN d n := le_trans (by norm_num) (six_le_NN d n hd hdn)
  let W : ℝ := (bigW (wOf B) : ℝ)
  have hWpos' : (0 : ℝ) < W := hWpos
  have hWnn : (0 : ℝ) ≤ W := le_of_lt hWpos'
  -- the per-ℓ bound
  have hterm : ∀ ℓ : ℕ, ⌊A / W⌋₊ + 1 ≤ ℓ → ℓ ≤ ⌊A⌋₊ →
      |((ArithmeticFunction.moebius ℓ : ℝ) / (ℓ : ℝ) ^ 2) *
          Sk d n 2 (GamLoc d n x y (bigW (wOf B) / Nat.gcd ℓ (bigW (wOf B))))
            (TlocSet d n x y (A / (ℓ : ℝ)) (Real.log B))|
        ≤ KA / A ^ 2 * W ^ (NN d n) := by
    intro ℓ hlo hhi
    have hℓ1 : 1 ≤ ℓ := by omega
    have hℓpos : (0 : ℝ) < (ℓ : ℝ) := by exact_mod_cast (by omega : 0 < ℓ)
    have hℓA : (ℓ : ℝ) ≤ A := by
      have h1 : (ℓ : ℝ) ≤ ((⌊A⌋₊ : ℕ) : ℝ) := by exact_mod_cast hhi
      have h2 : ((⌊A⌋₊ : ℕ) : ℝ) ≤ A := Nat.floor_le hApos.le
      linarith
    have hT : (1 : ℝ) ≤ A / (ℓ : ℝ) := by
      rw [le_div_iff₀ hℓpos]
      simpa using hℓA
    have hSℓ := hKA x y (bigW (wOf B) / Nat.gcd ℓ (bigW (wOf B))) (A / (ℓ : ℝ))
      (Real.log B) hT
    have hSnn : 0 ≤ Sk d n 2 (GamLoc d n x y (bigW (wOf B) / Nat.gcd ℓ (bigW (wOf B))))
        (TlocSet d n x y (A / (ℓ : ℝ)) (Real.log B)) := Sk_nonneg _ _ _ _ _
    have hμ : |((ArithmeticFunction.moebius ℓ : ℤ) : ℝ)| ≤ 1 := by
      have h1 : |(ArithmeticFunction.moebius ℓ : ℤ)| ≤ 1 :=
        ArithmeticFunction.abs_moebius_le_one (n := ℓ)
      rw [abs_le]
      exact ⟨by exact_mod_cast (abs_le.mp h1).1, by exact_mod_cast (abs_le.mp h1).2⟩
    have hloW : A / W < (ℓ : ℝ) := by
      have h1 : A / W < ((⌊A / W⌋₊ : ℕ) : ℝ) + 1 := Nat.lt_floor_add_one (A / W)
      have h2 : ((⌊A / W⌋₊ : ℕ) : ℝ) + 1 ≤ (ℓ : ℝ) := by exact_mod_cast hlo
      linarith
    have hAle : A / (ℓ : ℝ) ≤ W := by
      have h3 : A < (ℓ : ℝ) * W := by
        have h4 := (div_lt_iff₀ hWpos').mp hloW
        linarith
      rw [div_le_iff₀ hℓpos]
      linarith
    have hall : |((ArithmeticFunction.moebius ℓ : ℝ) / (ℓ : ℝ) ^ 2) *
          Sk d n 2 (GamLoc d n x y (bigW (wOf B) / Nat.gcd ℓ (bigW (wOf B))))
            (TlocSet d n x y (A / (ℓ : ℝ)) (Real.log B))|
        = |((ArithmeticFunction.moebius ℓ : ℤ) : ℝ)| / (ℓ : ℝ) ^ 2 *
          Sk d n 2 (GamLoc d n x y (bigW (wOf B) / Nat.gcd ℓ (bigW (wOf B))))
            (TlocSet d n x y (A / (ℓ : ℝ)) (Real.log B)) := by
      rw [abs_mul, abs_div, abs_of_pos (show (0 : ℝ) < (ℓ : ℝ) ^ 2 by positivity),
        abs_of_nonneg hSnn]
    rw [hall]
    have hstep : |((ArithmeticFunction.moebius ℓ : ℤ) : ℝ)| / (ℓ : ℝ) ^ 2
          * Sk d n 2 (GamLoc d n x y (bigW (wOf B) / Nat.gcd ℓ (bigW (wOf B))))
              (TlocSet d n x y (A / (ℓ : ℝ)) (Real.log B))
        ≤ 1 / (ℓ : ℝ) ^ 2 * (KA * (A / (ℓ : ℝ)) ^ (NN d n - 2)) := by
      refine le_trans (mul_le_mul_of_nonneg_right
        (div_le_div_of_nonneg_right hμ (show (0 : ℝ) ≤ (ℓ : ℝ) ^ 2 by positivity)) hSnn) ?_
      exact mul_le_mul_of_nonneg_left hSℓ (by positivity)
    refine le_trans hstep ?_
    have hdec : (A / (ℓ : ℝ)) ^ (NN d n) =
        (A / (ℓ : ℝ)) ^ (NN d n - 2) * (A / (ℓ : ℝ)) ^ 2 := by
      rw [← pow_add]
      congr 1
      omega
    have halg : 1 / (ℓ : ℝ) ^ 2 * (KA * (A / (ℓ : ℝ)) ^ (NN d n - 2))
        = KA / A ^ 2 * (A / (ℓ : ℝ)) ^ (NN d n) := by
      rw [hdec, div_pow, div_pow]
      field_simp
    rw [halg]
    exact mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (by positivity) hAle (NN d n)) (by positivity)
  -- the cardboard bound on the number of terms
  have hcard : ((Finset.Icc (⌊A / W⌋₊ + 1) ⌊A⌋₊).card : ℝ) ≤ 2 * A := by
    have h1 : (Finset.Icc (⌊A / W⌋₊ + 1) ⌊A⌋₊).card ≤ ⌊A⌋₊ + 1 := by
      calc (Finset.Icc (⌊A / W⌋₊ + 1) ⌊A⌋₊).card ≤ (Finset.range (⌊A⌋₊ + 1)).card :=
            Finset.card_le_card (fun ℓ hℓ => by
              rw [Finset.mem_range]
              exact Nat.lt_succ_of_le (Finset.mem_Icc.mp hℓ).2)
        _ = ⌊A⌋₊ + 1 := Finset.card_range _
    have h2 : ((⌊A⌋₊ : ℕ) : ℝ) + 1 ≤ 2 * A := by
      have h3 : ((⌊A⌋₊ : ℕ) : ℝ) ≤ A := Nat.floor_le hApos.le
      linarith
    calc ((Finset.Icc (⌊A / W⌋₊ + 1) ⌊A⌋₊).card : ℝ)
        ≤ (((⌊A⌋₊ + 1 : ℕ)) : ℝ) := by exact_mod_cast h1
      _ = ((⌊A⌋₊ : ℕ) : ℝ) + 1 := by push_cast; ring
      _ ≤ 2 * A := h2
  have htail : |∑ ℓ ∈ Finset.Icc (⌊A / W⌋₊ + 1) ⌊A⌋₊,
          ((ArithmeticFunction.moebius ℓ : ℝ) / (ℓ : ℝ) ^ 2) *
            Sk d n 2 (GamLoc d n x y (bigW (wOf B) / Nat.gcd ℓ (bigW (wOf B))))
              (TlocSet d n x y (A / (ℓ : ℝ)) (Real.log B))|
        ≤ 2 * KA * W ^ (NN d n) / A := by
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
    refine le_trans (Finset.sum_le_sum fun ℓ hℓ =>
      hterm ℓ (Finset.mem_Icc.mp hℓ).1 (Finset.mem_Icc.mp hℓ).2) ?_
    rw [Finset.sum_const, nsmul_eq_mul]
    calc ((Finset.Icc (⌊A / W⌋₊ + 1) ⌊A⌋₊).card : ℝ) * (KA / A ^ 2 * W ^ (NN d n))
        ≤ (2 * A) * (KA / A ^ 2 * W ^ (NN d n)) :=
          mul_le_mul_of_nonneg_right hcard (by positivity)
      _ = 2 * KA * W ^ (NN d n) / A := by
          field_simp
  -- the numeric inequality and the lower bound for `locMain`
  have harith' := hC A B hBhi hAB hA2
  have hloc' := hloc A B x y hApos hBgt1 hx hy hxy
  calc |∑ ℓ ∈ Finset.Icc (⌊A / W⌋₊ + 1) ⌊A⌋₊,
          ((ArithmeticFunction.moebius ℓ : ℝ) / (ℓ : ℝ) ^ 2) *
            Sk d n 2 (GamLoc d n x y (bigW (wOf B) / Nat.gcd ℓ (bigW (wOf B))))
              (TlocSet d n x y (A / (ℓ : ℝ)) (Real.log B))|
      ≤ 2 * KA * W ^ (NN d n) / A := htail
    _ ≤ C * (8 * iotaDN d n * A ^ (NN d n - 2)
          / ((Real.log B * (bigW (wOf B) : ℝ)) ^ 2)) / Real.log A := harith'
    _ ≤ C * locMain d n A B (x, y) / Real.log A := by
        refine div_le_div_of_nonneg_right ?_ hlogAnn
        exact mul_le_mul_of_nonneg_left hloc' (le_of_lt hCpos)

end Work.HP.MM2

namespace Work.HP.MM2

/-- (tail of L2b) The range `A/W < ℓ ≤ A` of the local Möbius sum is bounded by
`C · locMain / log A`. -/
theorem Sstar2_loc_tail (d n : ℕ) [DecidableEq (Work.HP.Mon d n)] (hd : 2 ≤ d) (hdn : d ≤ n)
    (h22 : (d, n) ≠ (2, 2)) :
    ∃ C B₀ : ℝ, 0 < C ∧ ∀ A B : ℝ, B₀ ≤ B → B ^ ((5 : ℝ) / 6) ≤ A → A ≤ B ^ 2 →
      ∀ x y : Fin (n + 1) → ℤ, Work.HP.IsPrim x → Work.HP.IsPrim y →
        LinearIndependent ℤ ![x, y] →
      |∑ ℓ ∈ Finset.Icc (⌊A / (Work.HP.bigW (Work.HP.wOf B) : ℝ)⌋₊ + 1) ⌊A⌋₊,
          ((ArithmeticFunction.moebius ℓ : ℝ) / (ℓ : ℝ) ^ 2) *
            Work.HP.Sk d n 2 (Work.HP.GamLoc d n x y (Work.HP.bigW (Work.HP.wOf B) /
                Nat.gcd ℓ (Work.HP.bigW (Work.HP.wOf B))))
              (Work.HP.TlocSet d n x y (A / (ℓ : ℝ)) (Real.log B))|
        ≤ C * Work.HP.MM2.locMain d n A B (x, y) / Real.log A :=
  Sstar2_loc_tail_aux d n hd hdn (Sk2_Tloc_le_pow d n hd hdn) (iotaDN_pos d n hd hdn)
    (locMain_lower d n hd hdn) (tail_arith d n hd hdn)

end Work.HP.MM2
