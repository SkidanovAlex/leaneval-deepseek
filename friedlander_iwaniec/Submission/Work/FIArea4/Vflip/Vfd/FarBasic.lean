import Mathlib
import Submission.Work.FIArea4.Vflip.Vfd.FarSepDefs
import Submission.Work.FIArea4.Vflip.Vfd.coprimeSetup

/-!
# Elementary inputs for the far numerics of the flipped-moduli bound

This module collects the elementary (arithmetic and real-analytic) inputs used to bound the
numerics of the far part: the divisor bound `τ(n) ≤ 2√n`, three geometric-sum bounds for an
arbitrary finite set of exponents, the resulting bounds for the dyadic range `farJF`, pointwise
bounds for the four terms `pT1 … pT4` of the bracket (`p14T11 = pT1 + pT2 + pT3 + pT4`) at the
reduced modulus `Rred c R`, and the reindexing bound `Σ_c L2 (redA c β) ≤ p14Ener`.
-/

namespace Work.FIArea4.Vflip.Vfd

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-! ## The divisor bound `τ(n) ≤ 2√n` -/

/-- The number of divisors of `n ≥ 1` is at most `2√n`. -/
theorem divisors_card_le_two_sqrt (n : ℕ) (hn : 1 ≤ n) :
    ((n.divisors.card : ℕ) : ℝ) ≤ 2 * Real.sqrt (n : ℝ) := by
  have hn0 : n ≠ 0 := by omega
  set A : Finset ℕ := n.divisors.filter (fun d => d * d ≤ n) with hA
  set B : Finset ℕ := n.divisors.filter (fun d => ¬ (d * d ≤ n)) with hB
  have hsplit : n.divisors.card = A.card + B.card := by
    rw [hA, hB]
    exact (Finset.card_filter_add_card_filter_not (s := n.divisors) (p := fun d => d * d ≤ n)).symm
  have hAcard : A.card ≤ Nat.sqrt n := by
    have hsub : A ⊆ Finset.Icc 1 (Nat.sqrt n) := by
      intro d hd
      rw [hA, Finset.mem_filter, Nat.mem_divisors] at hd
      obtain ⟨⟨hdvd, -⟩, hdsq⟩ := hd
      exact Finset.mem_Icc.mpr ⟨Nat.pos_of_dvd_of_pos hdvd (by omega), (Nat.le_sqrt).mpr hdsq⟩
    calc A.card ≤ (Finset.Icc 1 (Nat.sqrt n)).card := Finset.card_le_card hsub
      _ = Nat.sqrt n := by rw [Nat.card_Icc]; omega
  have hBcard : B.card ≤ A.card := by
    have himg : ∀ d ∈ B, n / d ∈ A := by
      intro d hd
      rw [hB, Finset.mem_filter, Nat.mem_divisors] at hd
      obtain ⟨⟨hdvd, -⟩, hdnle⟩ := hd
      have hqd : n / d * d = n := Nat.div_mul_cancel hdvd
      have hle : n / d ≤ d := by
        have h1 : n / d * d ≤ d * d := by rw [hqd]; omega
        exact Nat.le_of_mul_le_mul_right h1 (Nat.pos_of_dvd_of_pos hdvd (by omega))
      have hqsq : n / d * (n / d) ≤ n := by
        calc n / d * (n / d) ≤ n / d * d := Nat.mul_le_mul_left _ hle
          _ = n := hqd
      rw [hA, Finset.mem_filter, Nat.mem_divisors]
      exact ⟨⟨Nat.div_dvd_of_dvd hdvd, hn0⟩, hqsq⟩
    have hinj : Set.InjOn (fun d => n / d) ↑B := by
      intro a ha b hb hab
      rw [Finset.mem_coe, hB, Finset.mem_filter, Nat.mem_divisors] at ha hb
      beta_reduce at hab
      have h1 : a = n / (n / a) := (Nat.div_div_self ha.1.1 hn0).symm
      have h2 : b = n / (n / b) := (Nat.div_div_self hb.1.1 hn0).symm
      have h3 : n / (n / a) = n / (n / b) := by rw [hab]
      exact h1.trans (h3.trans h2.symm)
    calc B.card = (B.image (fun d => n / d)).card := (Finset.card_image_of_injOn hinj).symm
      _ ≤ A.card := Finset.card_le_card (Finset.image_subset_iff.mpr himg)
  have hcard : n.divisors.card ≤ 2 * Nat.sqrt n := by rw [hsplit]; omega
  have hsqrt : (Nat.sqrt n : ℝ) ≤ Real.sqrt (n : ℝ) := by
    rw [Real.le_sqrt (by positivity) (by positivity)]
    exact_mod_cast Nat.sqrt_le' n
  calc ((n.divisors.card : ℕ) : ℝ) ≤ ((2 * Nat.sqrt n : ℕ) : ℝ) := by exact_mod_cast hcard
    _ = 2 * (Nat.sqrt n : ℝ) := by push_cast; ring
    _ ≤ 2 * Real.sqrt (n : ℝ) := by linarith

/-! ## Three geometric bounds for a finite set of exponents -/

/-- For `0 ≤ q < 1` and a finite set `S` of exponents with `q^j < c` for all `j ∈ S`,
`∑_{j ∈ S} q^j ≤ c/(1-q)`. -/
theorem sum_pow_le_of_lt_const (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1) (S : Finset ℕ) (c : ℝ)
    (hc : 0 < c) (h : ∀ j ∈ S, q ^ j < c) :
    ∑ j ∈ S, q ^ j ≤ c / (1 - q) := by
  have hq1' : 0 < 1 - q := by linarith
  have hgeom : ∀ N : ℕ, ∑ k ∈ Finset.range N, q ^ k ≤ 1 / (1 - q) := by
    intro N
    have hkey : (1 - q) * ∑ k ∈ Finset.range N, q ^ k = 1 - q ^ N := by
      have h2 := geom_sum_mul q N
      linarith
    have h3 : (1 - q) * ∑ k ∈ Finset.range N, q ^ k ≤ 1 := by
      rw [hkey]
      have : 0 ≤ q ^ N := pow_nonneg hq0 N
      linarith
    rw [le_div_iff₀ hq1']
    linarith [h3]
  rcases S.eq_empty_or_nonempty with hS | hS
  · rw [hS]; simp only [sum_empty]; positivity
  · set j0 : ℕ := S.min' hS with hj0
    set jm : ℕ := S.max' hS with hjm
    have hsub : S ⊆ Finset.Icc j0 jm := fun d hd =>
      Finset.mem_Icc.mpr ⟨Finset.min'_le S d hd, Finset.le_max' S d hd⟩
    have h1 : ∑ j ∈ S, q ^ j ≤ ∑ j ∈ Finset.Icc j0 jm, q ^ j :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun j _ _ => pow_nonneg hq0 j)
    have h2 : ∑ j ∈ Finset.Icc j0 jm, q ^ j ≤ q ^ j0 / (1 - q) := by
      rw [← Finset.Ico_succ_right_eq_Icc j0 jm, Finset.sum_Ico_eq_sum_range]
      have hstep : ∑ k ∈ Finset.range (Order.succ jm - j0), q ^ (j0 + k)
          = q ^ j0 * ∑ k ∈ Finset.range (Order.succ jm - j0), q ^ k := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl (fun k _ => by rw [pow_add])
      rw [hstep]
      have hg := hgeom (Order.succ jm - j0)
      calc q ^ j0 * ∑ k ∈ Finset.range (Order.succ jm - j0), q ^ k
          ≤ q ^ j0 * (1 / (1 - q)) := mul_le_mul_of_nonneg_left hg (pow_nonneg hq0 j0)
        _ = q ^ j0 / (1 - q) := by ring
    have h3 : q ^ j0 < c := h j0 (S.min'_mem hS)
    calc ∑ j ∈ S, q ^ j ≤ ∑ j ∈ Finset.Icc j0 jm, q ^ j := h1
      _ ≤ q ^ j0 / (1 - q) := h2
      _ ≤ c / (1 - q) := div_le_div_of_nonneg_right (le_of_lt h3) (le_of_lt hq1')

/-- For a finite set `S` of exponents with `2^j < U` for all `j ∈ S`, `∑_{j ∈ S} 2^j ≤ 2U`. -/
theorem sum_two_pow_le_of_lt_const (S : Finset ℕ) (U : ℝ) (hU : 0 < U)
    (h : ∀ j ∈ S, (2 : ℝ) ^ j < U) : ∑ j ∈ S, (2 : ℝ) ^ j ≤ 2 * U := by
  rcases S.eq_empty_or_nonempty with hS | hS
  · rw [hS]; simp only [sum_empty]; linarith
  · set jm : ℕ := S.max' hS with hjm
    have hsub : S ⊆ Finset.Icc 0 jm := fun d hd =>
      Finset.mem_Icc.mpr ⟨Nat.zero_le d, Finset.le_max' S d hd⟩
    have h1 : ∑ j ∈ S, (2 : ℝ) ^ j ≤ ∑ j ∈ Finset.Icc 0 jm, (2 : ℝ) ^ j :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun j _ _ => by positivity)
    have h2 : ∑ j ∈ Finset.Icc 0 jm, (2 : ℝ) ^ j = (2 : ℝ) ^ (jm + 1) - 1 := by
      rw [← Finset.Ico_succ_right_eq_Icc 0 jm, Finset.sum_Ico_eq_sum_range]
      simp only [zero_add, Nat.sub_zero, Order.succ_eq_add_one]
      have hkey := geom_sum_mul (2 : ℝ) (jm + 1)
      linarith
    have h3 : (2 : ℝ) ^ jm < U := h jm (S.max'_mem hS)
    have h4 : (2 : ℝ) ^ (jm + 1) = 2 * (2 : ℝ) ^ jm := by rw [pow_succ]; ring
    calc ∑ j ∈ S, (2 : ℝ) ^ j ≤ ∑ j ∈ Finset.Icc 0 jm, (2 : ℝ) ^ j := h1
      _ = (2 : ℝ) ^ (jm + 1) - 1 := h2
      _ ≤ 2 * U := by rw [h4]; linarith

/-- Cardinality bound for a finite set of exponents whose powers `2^j` all lie in the window
`(L, U)`: `#S ≤ log(U/L)/log 2 + 1`. -/
theorem card_le_log_ratio (S : Finset ℕ) (L U : ℝ) (hL : 0 < L) (hU : 0 < U)
    (h : ∀ j ∈ S, L < (2 : ℝ) ^ j ∧ (2 : ℝ) ^ j < U) :
    (S.card : ℝ) ≤ max 0 (Real.log (U / L) / Real.log 2) + 1 := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  rcases S.eq_empty_or_nonempty with hS | hS
  · rw [hS]; simp only [card_empty, Nat.cast_zero]
    have := le_max_left (0 : ℝ) (Real.log (U / L) / Real.log 2)
    linarith
  · set j0 : ℕ := S.min' hS with hj0
    set jm : ℕ := S.max' hS with hjm
    have hmem0 : j0 ∈ S := S.min'_mem hS
    have hmemm : jm ∈ S := S.max'_mem hS
    have hj0le : j0 ≤ jm := Finset.min'_le S jm hmemm
    have hLt : L < (2 : ℝ) ^ j0 := (h j0 hmem0).1
    have hUt : (2 : ℝ) ^ jm < U := (h jm hmemm).2
    have hcardsub : S ⊆ Finset.Icc j0 jm := fun d hd =>
      Finset.mem_Icc.mpr ⟨Finset.min'_le S d hd, Finset.le_max' S d hd⟩
    have hcardle : S.card ≤ jm + 1 - j0 := by
      calc S.card ≤ (Finset.Icc j0 jm).card := Finset.card_le_card hcardsub
        _ = jm + 1 - j0 := Nat.card_Icc j0 jm
    have hcardpos : 1 ≤ S.card := Finset.card_pos.mpr hS
    have hpow : (2 : ℝ) ^ (jm - j0) < U / L := by
      have h1 : (2 : ℝ) ^ jm / (2 : ℝ) ^ j0 < U / (2 : ℝ) ^ j0 :=
        div_lt_div_of_pos_right hUt (by positivity)
      have h2 : U / (2 : ℝ) ^ j0 < U / L :=
        div_lt_div_of_pos_left hU hL hLt
      have h3 : (2 : ℝ) ^ (jm - j0) = (2 : ℝ) ^ jm / (2 : ℝ) ^ j0 := by
        rw [eq_div_iff (by positivity : ((2 : ℝ) ^ j0) ≠ 0)]
        rw [← pow_add, Nat.sub_add_cancel hj0le]
      rw [h3]; linarith
    have hdle : S.card - 1 ≤ jm - j0 := by omega
    have hpow2 : (2 : ℝ) ^ (S.card - 1) ≤ (2 : ℝ) ^ (jm - j0) :=
      pow_le_pow_right₀ (by norm_num) hdle
    have hlog : ((S.card - 1 : ℕ) : ℝ) * Real.log 2 < Real.log (U / L) := by
      have h1 : Real.log ((2 : ℝ) ^ (S.card - 1)) < Real.log (U / L) :=
        Real.log_lt_log (by positivity) (lt_of_le_of_lt hpow2 hpow)
      rwa [Real.log_pow] at h1
    have hdiv : ((S.card - 1 : ℕ) : ℝ) < Real.log (U / L) / Real.log 2 := by
      rw [lt_div_iff₀ hlog2]
      exact hlog
    have hcast : (S.card : ℝ) = ((S.card - 1 : ℕ) : ℝ) + 1 := by
      rw [Nat.cast_sub hcardpos]; push_cast; ring
    have hmax : Real.log (U / L) / Real.log 2 ≤ max 0 (Real.log (U / L) / Real.log 2) :=
      le_max_right _ _
    rw [hcast]; linarith

/-! ## Bounds for the dyadic range `farJF` -/

/-! ## Pointwise bounds for the four terms of `p14T11` at the reduced modulus -/

/-- The cast of the reduced modulus: `↑(Rred c R) ≤ 2R/c`. -/
theorem Rred_cast_le (c R : ℕ) : ((Rred c R : ℕ) : ℝ) ≤ 2 * (R : ℝ) / (c : ℝ) := by
  rw [Rred]
  have h := Nat.cast_div_le (α := ℝ) (m := 2 * R) (n := c)
  push_cast at h ⊢
  exact h

/-- The first term `pT1` at `(m·2^j, Rred c R, S)`. -/
theorem pT1_le (R S c m j : ℕ) (hc : 1 ≤ c) :
    pT1 (m * 2 ^ j) (Rred c R) S
      ≤ (m : ℝ) ^ (-(1 : ℝ) / 2) * (2 : ℝ) ^ (-(j : ℝ) / 2)
          * (2 * (R : ℝ) / (c : ℝ)) * (S : ℝ) := by
  unfold pT1
  have hcast : ((m * 2 ^ j : ℕ) : ℝ) = (m : ℝ) * (2 : ℝ) ^ j := by push_cast; ring
  rw [hcast, Real.mul_rpow (by positivity) (by positivity)]
  have hpow : ((2 : ℝ) ^ j) ^ (-(1 : ℝ) / 2) = (2 : ℝ) ^ (-(j : ℝ) / 2) := by
    rw [← Real.rpow_natCast (2 : ℝ) j, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
    congr 1
    push_cast
    ring
  rw [hpow]
  have h1 : ((Rred c R : ℕ) : ℝ) ≤ 2 * (R : ℝ) / (c : ℝ) := Rred_cast_le c R
  have h0 : 0 ≤ (m : ℝ) ^ (-(1 : ℝ) / 2) * (2 : ℝ) ^ (-(j : ℝ) / 2) := by positivity
  have hS : 0 ≤ (S : ℝ) := by positivity
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h1 h0) hS

/-- The second term `pT2` at `(m·2^j, Rred c R, S)`. -/
theorem pT2_le (R S c m j : ℕ) (ε' : ℝ) (hε' : 0 ≤ ε') (hc : 1 ≤ c) :
    pT2 (m * 2 ^ j) (Rred c R) S ε'
      ≤ (m : ℝ) * (2 : ℝ) ^ j * Real.sqrt (2 * (R : ℝ) / (c : ℝ) * (S : ℝ))
          * ((2 * (R : ℝ) / (c : ℝ) * (S : ℝ)) ^ ε') := by
  unfold pT2
  have hcast : ((m * 2 ^ j : ℕ) : ℝ) = (m : ℝ) * (2 : ℝ) ^ j := by push_cast; ring
  rw [hcast]
  have hRred : ((Rred c R : ℕ) : ℝ) ≤ 2 * (R : ℝ) / (c : ℝ) := Rred_cast_le c R
  have hRS : ((Rred c R : ℕ) : ℝ) * (S : ℝ) ≤ 2 * (R : ℝ) / (c : ℝ) * (S : ℝ) :=
    mul_le_mul_of_nonneg_right hRred (by positivity)
  have hsq : Real.sqrt (((Rred c R : ℕ) : ℝ) * (S : ℝ))
      ≤ Real.sqrt (2 * (R : ℝ) / (c : ℝ) * (S : ℝ)) := Real.sqrt_le_sqrt hRS
  have hpow : (((Rred c R : ℕ) : ℝ) * (S : ℝ)) ^ ε' ≤ (2 * (R : ℝ) / (c : ℝ) * (S : ℝ)) ^ ε' :=
    Real.rpow_le_rpow (by positivity) hRS hε'
  have h3 : (m : ℝ) * (2 : ℝ) ^ j * Real.sqrt (((Rred c R : ℕ) : ℝ) * (S : ℝ))
      ≤ (m : ℝ) * (2 : ℝ) ^ j * Real.sqrt (2 * (R : ℝ) / (c : ℝ) * (S : ℝ)) :=
    mul_le_mul_of_nonneg_left hsq (by positivity)
  have h4 : 0 ≤ (m : ℝ) * (2 : ℝ) ^ j * Real.sqrt (2 * (R : ℝ) / (c : ℝ) * (S : ℝ)) := by positivity
  exact mul_le_mul h3 hpow (Real.rpow_nonneg (by positivity) _) h4

/-- The third term `pT3` at `(m·2^j, Rred c R, S)`. -/
theorem pT3_le (R S c m j : ℕ) (ε' : ℝ) (hε' : 0 ≤ ε') (hc : 1 ≤ c) :
    pT3 (m * 2 ^ j) (Rred c R) S ε'
      ≤ 2 * (R : ℝ) / (c : ℝ) * (S : ℝ) ^ ((3 : ℝ) / 4)
          * ((2 * (R : ℝ) / (c : ℝ) * (S : ℝ)) ^ ε') := by
  unfold pT3
  have hRred : ((Rred c R : ℕ) : ℝ) ≤ 2 * (R : ℝ) / (c : ℝ) := Rred_cast_le c R
  have hRS : ((Rred c R : ℕ) : ℝ) * (S : ℝ) ≤ 2 * (R : ℝ) / (c : ℝ) * (S : ℝ) :=
    mul_le_mul_of_nonneg_right hRred (by positivity)
  have hpow : (((Rred c R : ℕ) : ℝ) * (S : ℝ)) ^ ε' ≤ (2 * (R : ℝ) / (c : ℝ) * (S : ℝ)) ^ ε' :=
    Real.rpow_le_rpow (by positivity) hRS hε'
  have h3 : ((Rred c R : ℕ) : ℝ) * (S : ℝ) ^ ((3 : ℝ) / 4)
      ≤ 2 * (R : ℝ) / (c : ℝ) * (S : ℝ) ^ ((3 : ℝ) / 4) :=
    mul_le_mul_of_nonneg_right hRred (by positivity)
  exact mul_le_mul h3 hpow (Real.rpow_nonneg (by positivity) _) (by positivity)

/-- The fourth term `pT4` at `(m·2^j, Rred c R, S)`. -/
theorem pT4_le (R S c m j : ℕ) (ε' : ℝ) (hε' : 0 ≤ ε') (hc : 1 ≤ c) :
    pT4 (m * 2 ^ j) (Rred c R) S ε'
      ≤ (S : ℝ) * (2 * (R : ℝ) / (c : ℝ)) ^ ((3 : ℝ) / 4)
          * ((2 * (R : ℝ) / (c : ℝ) * (S : ℝ)) ^ ε') := by
  unfold pT4
  have hRred : ((Rred c R : ℕ) : ℝ) ≤ 2 * (R : ℝ) / (c : ℝ) := Rred_cast_le c R
  have hRS : ((Rred c R : ℕ) : ℝ) * (S : ℝ) ≤ 2 * (R : ℝ) / (c : ℝ) * (S : ℝ) :=
    mul_le_mul_of_nonneg_right hRred (by positivity)
  have hpow : (((Rred c R : ℕ) : ℝ) * (S : ℝ)) ^ ε' ≤ (2 * (R : ℝ) / (c : ℝ) * (S : ℝ)) ^ ε' :=
    Real.rpow_le_rpow (by positivity) hRS hε'
  have h34 : ((Rred c R : ℕ) : ℝ) ^ ((3 : ℝ) / 4) ≤ (2 * (R : ℝ) / (c : ℝ)) ^ ((3 : ℝ) / 4) :=
    Real.rpow_le_rpow (by positivity) hRred (by norm_num)
  have h3 : (S : ℝ) * ((Rred c R : ℕ) : ℝ) ^ ((3 : ℝ) / 4)
      ≤ (S : ℝ) * (2 * (R : ℝ) / (c : ℝ)) ^ ((3 : ℝ) / 4) :=
    mul_le_mul_of_nonneg_left h34 (by positivity)
  exact mul_le_mul h3 hpow (Real.rpow_nonneg (by positivity) _) (by positivity)

/-! ## Divisor sums over `m ∣ c` -/

/-- `∑_{m ∣ c} m^{-1/2} ≤ τ(c)`. -/
theorem sum_divisors_rpow_neg_half_le_card (c : ℕ) :
    ∑ m ∈ c.divisors, (m : ℝ) ^ (-(1 : ℝ) / 2) ≤ ((c.divisors.card : ℕ) : ℝ) := by
  calc ∑ m ∈ c.divisors, (m : ℝ) ^ (-(1 : ℝ) / 2) ≤ ∑ _m ∈ c.divisors, (1 : ℝ) := by
        apply Finset.sum_le_sum
        intro m hm
        have h1 : (1 : ℝ) ≤ (m : ℝ) := by
          have := Nat.pos_of_mem_divisors hm
          exact_mod_cast this
        exact Real.rpow_le_one_of_one_le_of_nonpos h1 (by norm_num)
    _ = ((c.divisors.card : ℕ) : ℝ) := by simp

/-- `∑_{m ∣ c} m ≤ c τ(c)`. -/
theorem sum_divisors_le_card_mul (c : ℕ) (hc : 0 < c) :
    ∑ m ∈ c.divisors, (m : ℝ) ≤ (c : ℝ) * ((c.divisors.card : ℕ) : ℝ) := by
  calc ∑ m ∈ c.divisors, (m : ℝ) ≤ ∑ _m ∈ c.divisors, (c : ℝ) := by
        apply Finset.sum_le_sum
        intro m hm
        have h : m ≤ c := Nat.le_of_dvd hc (Nat.dvd_of_mem_divisors hm)
        exact_mod_cast h
    _ = ((c.divisors.card : ℕ) : ℝ) * (c : ℝ) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ = (c : ℝ) * ((c.divisors.card : ℕ) : ℝ) := by ring

/-- `τ(c)/c ≤ 2 c^{-1/2}` for `c ≥ 1`. -/
theorem card_div_le_two_mul_rpow_neg_half (c : ℕ) (hc : 1 ≤ c) :
    ((c.divisors.card : ℕ) : ℝ) / (c : ℝ) ≤ 2 * (c : ℝ) ^ (-(1 : ℝ) / 2) := by
  have hcpos : 0 < (c : ℝ) := by positivity
  have h1 := divisors_card_le_two_sqrt c hc
  rw [Real.sqrt_eq_rpow] at h1
  rw [div_le_iff₀ hcpos]
  have h3 : (c : ℝ) ^ (-(1 : ℝ) / 2) * (c : ℝ) = (c : ℝ) ^ ((1 : ℝ) / 2) := by
    nth_rewrite 2 [← Real.rpow_one (c : ℝ)]
    rw [← Real.rpow_add hcpos]
    norm_num
  have h2 : 2 * (c : ℝ) ^ (-(1 : ℝ) / 2) * (c : ℝ) = 2 * (c : ℝ) ^ ((1 : ℝ) / 2) := by
    rw [mul_assoc, h3]
  linarith [h1, h2.le, h2.ge]

/-- `τ(c) c^{-3/4} ≤ τ(c) c^{-1/2}` for `c ≥ 1`. -/
theorem card_mul_rpow_neg_three_quarter_le (c : ℕ) (hc : 1 ≤ c) :
    ((c.divisors.card : ℕ) : ℝ) * (c : ℝ) ^ (-(3 : ℝ) / 4)
      ≤ ((c.divisors.card : ℕ) : ℝ) * (c : ℝ) ^ (-(1 : ℝ) / 2) := by
  have hcle : (1 : ℝ) ≤ (c : ℝ) := by exact_mod_cast hc
  have h2 : (c : ℝ) ^ (-(3 : ℝ) / 4) ≤ (c : ℝ) ^ (-(1 : ℝ) / 2) :=
    Real.rpow_le_rpow_of_exponent_le hcle (by norm_num)
  exact mul_le_mul_of_nonneg_left h2 (by positivity)

/-- `τ(c) c^{-1} ≤ τ(c) c^{-1/2}` for `c ≥ 1`. -/
theorem card_mul_rpow_neg_one_le (c : ℕ) (hc : 1 ≤ c) :
    ((c.divisors.card : ℕ) : ℝ) * (c : ℝ) ^ (-(1 : ℝ))
      ≤ ((c.divisors.card : ℕ) : ℝ) * (c : ℝ) ^ (-(1 : ℝ) / 2) := by
  have hcle : (1 : ℝ) ≤ (c : ℝ) := by exact_mod_cast hc
  have h2 : (c : ℝ) ^ (-(1 : ℝ)) ≤ (c : ℝ) ^ (-(1 : ℝ) / 2) :=
    Real.rpow_le_rpow_of_exponent_le hcle (by norm_num)
  exact mul_le_mul_of_nonneg_left h2 (by positivity)

/-- `τ(c) c^{-1/2} ≤ 2` for `c ≥ 1`. -/
theorem card_mul_rpow_neg_half_le_two (c : ℕ) (hc : 1 ≤ c) :
    ((c.divisors.card : ℕ) : ℝ) * (c : ℝ) ^ (-(1 : ℝ) / 2) ≤ 2 := by
  have h1 := divisors_card_le_two_sqrt c hc
  rw [Real.sqrt_eq_rpow] at h1
  calc ((c.divisors.card : ℕ) : ℝ) * (c : ℝ) ^ (-(1 : ℝ) / 2)
      ≤ (2 * (c : ℝ) ^ ((1 : ℝ) / 2)) * (c : ℝ) ^ (-(1 : ℝ) / 2) :=
        mul_le_mul_of_nonneg_right h1 (by positivity)
    _ = 2 * (c : ℝ) ^ ((1 : ℝ) / 2 + (-(1 : ℝ) / 2)) := by
        rw [mul_assoc, Real.rpow_add (by positivity : (0 : ℝ) < c)]
    _ = 2 := by norm_num

/-- `∑_{m ∣ c} (c m)^{-1/2} ≤ c^{-1/2} τ(c)`. -/
theorem sum_divisors_mul_rpow_neg_half (c : ℕ) (hc : 1 ≤ c) :
    ∑ m ∈ c.divisors, ((c : ℝ) * (m : ℝ)) ^ (-(1 : ℝ) / 2)
      ≤ (c : ℝ) ^ (-(1 : ℝ) / 2) * ((c.divisors.card : ℕ) : ℝ) := by
  calc ∑ m ∈ c.divisors, ((c : ℝ) * (m : ℝ)) ^ (-(1 : ℝ) / 2)
      = ∑ m ∈ c.divisors, (c : ℝ) ^ (-(1 : ℝ) / 2) * (m : ℝ) ^ (-(1 : ℝ) / 2) := by
        apply Finset.sum_congr rfl
        intro m _
        rw [Real.mul_rpow (by positivity) (by positivity)]
    _ = (c : ℝ) ^ (-(1 : ℝ) / 2) * ∑ m ∈ c.divisors, (m : ℝ) ^ (-(1 : ℝ) / 2) := by
        rw [Finset.mul_sum]
    _ ≤ (c : ℝ) ^ (-(1 : ℝ) / 2) * ((c.divisors.card : ℕ) : ℝ) :=
        mul_le_mul_of_nonneg_left (sum_divisors_rpow_neg_half_le_card c) (by positivity)

/-- `∑_{m ∣ c} c^{-3/2} m ≤ c^{-1/2} τ(c)`. -/
theorem sum_divisors_mul_le (c : ℕ) (hc : 1 ≤ c) :
    ∑ m ∈ c.divisors, (c : ℝ) ^ (-(3 : ℝ) / 2) * (m : ℝ)
      ≤ (c : ℝ) ^ (-(1 : ℝ) / 2) * ((c.divisors.card : ℕ) : ℝ) := by
  rw [← Finset.mul_sum]
  have h1 : ∑ m ∈ c.divisors, (m : ℝ) ≤ (c : ℝ) * ((c.divisors.card : ℕ) : ℝ) :=
    sum_divisors_le_card_mul c (by omega)
  have h2 : (c : ℝ) ^ (-(3 : ℝ) / 2) * (c : ℝ) = (c : ℝ) ^ (-(1 : ℝ) / 2) := by
    nth_rewrite 2 [← Real.rpow_one (c : ℝ)]
    rw [← Real.rpow_add (by positivity : (0 : ℝ) < (c : ℝ))]
    norm_num
  calc (c : ℝ) ^ (-(3 : ℝ) / 2) * ∑ m ∈ c.divisors, (m : ℝ)
      ≤ (c : ℝ) ^ (-(3 : ℝ) / 2) * ((c : ℝ) * ((c.divisors.card : ℕ) : ℝ)) :=
        mul_le_mul_of_nonneg_left h1 (by positivity)
    _ = (c : ℝ) ^ (-(1 : ℝ) / 2) * ((c.divisors.card : ℕ) : ℝ) := by
        rw [← mul_assoc, h2]

/-- The `m`-sum over `[1, N]` with the divisibility indicator is the divisor sum, for `c ≤ N`. -/
theorem sum_Icc_filter_dvd_eq_sum_divisors {N c : ℕ} (hc : 1 ≤ c) (hcN : c ≤ N) (g : ℕ → ℝ) :
    ∑ m ∈ Finset.Icc 1 N, (if m ∣ c then g m else 0) = ∑ m ∈ c.divisors, g m := by
  rw [← Finset.sum_filter]
  congr 1
  ext m
  simp only [Finset.mem_filter, Finset.mem_Icc, Nat.mem_divisors]
  constructor
  · rintro ⟨⟨hm1, -⟩, hd⟩
    exact ⟨hd, by omega⟩
  · rintro ⟨hd, -⟩
    have hmpos : 0 < m := Nat.pos_of_dvd_of_pos hd (by omega)
    exact ⟨⟨hmpos, le_trans (Nat.le_of_dvd (by omega) hd) hcN⟩, hd⟩

/-- **The `L²`-energies of the shifted arrays are dominated by the `τ`-weighted energy**:
`Σ_{c ≤ 2R} p14L2 (Rred c R) S (redA c β) ≤ p14Ener R S β` for `β` supported on `r ≤ 2R`.

Every index of `p14L2 (Rred c R) S (redA c β)` is a product `c·ρ` with `ρ ≤ 2·(2R/c)`, hence
`cρ ≤ 4R`; its first coordinate is a multiple of `c`, so after summing over `c ≤ 2R` each
`r ≤ 4R` is counted at most `τ(r)` times. -/
theorem sum_redL2_le_ener (R S : ℕ) (β : ℕ → ℕ → ℂ) (hR : 1 ≤ R)
    (hβ : ∀ r s, β r s ≠ 0 → r ≤ 2 * R) :
    ∑ c ∈ Finset.Icc 1 (2 * R), Work.FIArea4.p14L2 (Rred c R) S (redA c β)
      ≤ Work.FIArea4.p14Ener R S β := by
  set g : ℕ → ℝ := fun r => ∑ s ∈ Finset.Icc 1 (2 * S), Complex.normSq (β r s) with hg
  have hg0 : ∀ r, 0 ≤ g r := fun r => Finset.sum_nonneg (fun s _ => Complex.normSq_nonneg _)
  have hgv : ∀ r, 2 * R < r → g r = 0 := by
    intro r hr
    rw [hg]
    apply Finset.sum_eq_zero
    intro s _
    rw [Complex.normSq_eq_zero]
    by_contra h
    have := hβ r s h
    omega
  have hstep1 : ∑ c ∈ Finset.Icc 1 (2 * R), Work.FIArea4.p14L2 (Rred c R) S (redA c β)
      ≤ ∑ c ∈ Finset.Icc 1 (2 * R), ∑ r ∈ Finset.Icc 1 (4 * R), (if c ∣ r then g r else 0) := by
    apply Finset.sum_le_sum
    intro c hc
    obtain ⟨hc1, -⟩ := Finset.mem_Icc.mp hc
    have hcpos : 0 < c := hc1
    have himg : (Finset.Icc 1 (2 * (Rred c R))).image (fun ρ => c * ρ)
        ⊆ (Finset.Icc 1 (4 * R)).filter (fun r => c ∣ r) := by
      intro r hr
      rw [Finset.mem_image] at hr
      obtain ⟨ρ, hρ, rfl⟩ := hr
      rw [Finset.mem_Icc] at hρ
      rw [Finset.mem_filter, Finset.mem_Icc]
      refine ⟨⟨Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega)), ?_⟩,
        dvd_mul_right c ρ⟩
      calc c * ρ ≤ c * (2 * (Rred c R)) := Nat.mul_le_mul_left c hρ.2
        _ ≤ 4 * R := by
            rw [Rred]
            have h : c * (2 * R / c) ≤ 2 * R := Nat.mul_div_le (2 * R) c
            calc c * (2 * (2 * R / c)) = 2 * (c * (2 * R / c)) := by ring
              _ ≤ 2 * (2 * R) := Nat.mul_le_mul_left 2 h
              _ = 4 * R := by ring
    have hLeq : ∑ r ∈ (Finset.Icc 1 (2 * (Rred c R))).image (fun ρ => c * ρ), g r
        = Work.FIArea4.p14L2 (Rred c R) S (redA c β) := by
      rw [Work.FIArea4.p14L2, hg]
      simp only [redA_apply]
      exact Finset.sum_image (fun a _ b _ hab => Nat.mul_left_cancel hcpos hab)
    rw [← hLeq]
    calc ∑ r ∈ (Finset.Icc 1 (2 * (Rred c R))).image (fun ρ => c * ρ), g r
        ≤ ∑ r ∈ (Finset.Icc 1 (4 * R)).filter (fun r => c ∣ r), g r :=
          Finset.sum_le_sum_of_subset_of_nonneg himg (fun r _ _ => hg0 r)
      _ = ∑ r ∈ Finset.Icc 1 (4 * R), (if c ∣ r then g r else 0) := Finset.sum_filter ..
  have hstep2 : ∑ c ∈ Finset.Icc 1 (2 * R), ∑ r ∈ Finset.Icc 1 (4 * R), (if c ∣ r then g r else 0)
      ≤ ∑ r ∈ Finset.Icc 1 (4 * R), ((r.divisors.card : ℕ) : ℝ) * g r := by
    rw [Finset.sum_comm]
    apply Finset.sum_le_sum
    intro r hr
    have hr1 : 1 ≤ r := (Finset.mem_Icc.mp hr).1
    calc ∑ c ∈ Finset.Icc 1 (2 * R), (if c ∣ r then g r else 0)
        = ∑ c ∈ (Finset.Icc 1 (2 * R)).filter (fun c => c ∣ r), g r := by rw [Finset.sum_filter]
      _ = (((Finset.Icc 1 (2 * R)).filter (fun c => c ∣ r)).card : ℕ) * g r := by
            rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ((r.divisors.card : ℕ) : ℝ) * g r := by
            apply mul_le_mul_of_nonneg_right _ (hg0 r)
            apply Nat.cast_le.mpr
            apply Finset.card_le_card
            intro c hc
            rw [Finset.mem_filter, Finset.mem_Icc] at hc
            exact Nat.mem_divisors.mpr ⟨hc.2, by omega⟩
  have hstep3 : ∑ r ∈ Finset.Icc 1 (4 * R), ((r.divisors.card : ℕ) : ℝ) * g r
      = Work.FIArea4.p14Ener R S β := by
    rw [Work.FIArea4.p14Ener]
    simp only [hg, Finset.mul_sum]
    symm
    refine Finset.sum_subset ?_ ?_
    · intro r hr
      rw [Finset.mem_Icc] at hr ⊢
      exact ⟨hr.1, by omega⟩
    · intro r hr hnr
      have hr1 : 1 ≤ r := (Finset.mem_Icc.mp hr).1
      have hgt : 2 * R < r := by
        by_contra hle
        exact hnr (Finset.mem_Icc.mpr ⟨hr1, Nat.le_of_not_lt hle⟩)
      apply Finset.sum_eq_zero
      intro s _
      have hns : Complex.normSq (β r s) = 0 := by
        rw [Complex.normSq_eq_zero]
        by_contra h
        have := hβ r s h
        omega
      rw [hns, mul_zero]
  calc ∑ c ∈ Finset.Icc 1 (2 * R), Work.FIArea4.p14L2 (Rred c R) S (redA c β)
      ≤ ∑ c ∈ Finset.Icc 1 (2 * R), ∑ r ∈ Finset.Icc 1 (4 * R), (if c ∣ r then g r else 0) := hstep1
    _ ≤ ∑ r ∈ Finset.Icc 1 (4 * R), ((r.divisors.card : ℕ) : ℝ) * g r := hstep2
    _ = Work.FIArea4.p14Ener R S β := hstep3

end

end Work.FIArea4.Vflip.Vfd
