import Mathlib
import Submission.Commons.NumberTheory.DirichletCharacter.burgess_charSum_uniform_of_moment

set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
set_option exponentiation.threshold 1024

open Finset

namespace Commons.NumberTheory.DirichletCharacter

open scoped BigOperators

lemma moment_clean_of_eps {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (k : ℕ) (hk : 1 ≤ k) (C ε' : ℝ) (hC : 0 ≤ C)
    (hmom : ∀ H : ℕ, H ^ (2 * k) ≤ q →
      ∑ m ∈ Finset.range q, ‖∑ h ∈ Finset.Ioc m (m + H), χ (h : ZMod q)‖ ^ (2 * k)
        ≤ C * (q : ℝ) ^ ε' * ((q : ℝ) * (H : ℝ) ^ k + (H : ℝ) ^ (2 * k) * Real.sqrt (q : ℝ)))
    (L : ℕ) (hL : L ≤ q) :
    ∑ m ∈ Finset.range q, ‖∑ h ∈ Finset.Ioc m (m + L), χ (h : ZMod q)‖ ^ (2 * k)
      ≤ ((2:ℝ) ^ (3 * k + 1) * C) * (q : ℝ) ^ ε' *
          ((q : ℝ) * (L : ℝ) ^ k + (L : ℝ) ^ (2 * k) * Real.sqrt (q : ℝ)) := by
  have hq1 : 1 ≤ q := Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
  have hqR1 : (1:ℝ) ≤ (q:ℝ) := by exact_mod_cast hq1
  have hqpos : (0:ℝ) < (q:ℝ) := by exact_mod_cast (show 0 < q by omega)
  have hkpos : 0 < k := by omega
  have hkRne : (k:ℝ) ≠ 0 := by positivity
  set x : ℝ := (q:ℝ) ^ ((1:ℝ)/(2*(k:ℝ))) with hxdef
  have hx1 : (1:ℝ) ≤ x := Real.one_le_rpow hqR1 (by positivity)
  have hxpos : (0:ℝ) < x := lt_of_lt_of_le one_pos hx1
  have hxk : x ^ k = Real.sqrt (q:ℝ) := by
    rw [← Real.rpow_natCast x k, hxdef, ← Real.rpow_mul hqpos.le, Real.sqrt_eq_rpow]
    congr 1
    push_cast
    field_simp
  set L0 : ℕ := max 1 (Nat.floor x) with hL0def
  have hL0_1 : 1 ≤ L0 := le_max_left _ _
  have hL0posR : (0:ℝ) < (L0:ℝ) := by exact_mod_cast hL0_1
  have hL0_le_x : (L0:ℝ) ≤ x := by
    rw [hL0def]; push_cast
    exact max_le hx1 (Nat.floor_le (le_of_lt hxpos))
  have hL0pow : L0 ^ (2*k) ≤ q := by
    have h1 : ((L0:ℝ)) ^ (2*k) ≤ x ^ (2*k) :=
      pow_le_pow_left₀ (by positivity) hL0_le_x (2*k)
    have h2 : x ^ (2*k) = (q:ℝ) := by
      rw [← Real.rpow_natCast x (2*k), hxdef, ← Real.rpow_mul hqpos.le]
      have he : ((1:ℝ)/(2*(k:ℝ))) * ((2*k : ℕ):ℝ) = 1 := by
        push_cast
        field_simp
      rw [he, Real.rpow_one]
    have h3 : ((L0:ℝ)) ^ (2*k) ≤ (q:ℝ) := by rw [← h2]; exact h1
    exact_mod_cast h3
  have hL0ge_half : x/2 ≤ (L0:ℝ) := by
    by_cases hx2 : x ≤ 2
    · have h2 : x/2 ≤ 1 := by linarith only [hx2]
      have h3 : (1:ℝ) ≤ (L0:ℝ) := by exact_mod_cast hL0_1
      linarith only [hx2, h3]
    · push_neg at hx2
      have h1 : x - 1 ≤ ((Nat.floor x : ℕ) : ℝ) := by
        have := Nat.lt_floor_add_one x
        linarith only [this]
      have h2 : x/2 ≤ x - 1 := by linarith only [hx2]
      have h3 : ((Nat.floor x:ℕ):ℝ) ≤ (L0:ℝ) := by
        rw [hL0def]; push_cast; exact le_max_right _ _
      linarith only [hx2, h1, h3]
  set B : ℝ := C * (q:ℝ) ^ ε' * ((q:ℝ) * (L0:ℝ) ^ k + (L0:ℝ) ^ (2 * k) * Real.sqrt (q:ℝ)) with hBdef
  have hBnn : 0 ≤ B := by
    rw [hBdef]
    have h1 : (0:ℝ) ≤ (q:ℝ)^ε' := Real.rpow_nonneg hqpos.le _
    positivity
  have hqdiv_sqrt : (q:ℝ) / (L0:ℝ)^k ≤ 2^k * Real.sqrt (q:ℝ) := by
    have hsqpos : (0:ℝ) < Real.sqrt (q:ℝ) := Real.sqrt_pos.mpr hqpos
    have hsq2 : Real.sqrt (q:ℝ) * Real.sqrt (q:ℝ) = (q:ℝ) := Real.mul_self_sqrt hqpos.le
    have hL0kpos : (0:ℝ) < (L0:ℝ)^k := by positivity
    have h2kpos : (0:ℝ) < (2:ℝ)^k := by positivity
    have hxhalf : Real.sqrt (q:ℝ) / 2^k ≤ (L0:ℝ)^k := by
      have h := pow_le_pow_left₀ (by positivity : (0:ℝ) ≤ x/2) hL0ge_half k
      rw [div_pow, hxk] at h
      exact h
    have hxhalf2 : Real.sqrt (q:ℝ) ≤ (L0:ℝ)^k * 2^k := by
      have h := hxhalf
      rw [div_le_iff₀ h2kpos] at h
      exact h
    rw [div_le_iff₀ hL0kpos]
    conv_lhs => rw [show (q:ℝ) = Real.sqrt (q:ℝ) * Real.sqrt (q:ℝ) from hsq2.symm]
    have he : (2:ℝ)^k * Real.sqrt (q:ℝ) * (L0:ℝ)^k = Real.sqrt (q:ℝ) * ((L0:ℝ)^k * 2^k) := by ring
    rw [he]
    exact mul_le_mul_of_nonneg_left hxhalf2 (le_of_lt hsqpos)
  by_cases hcase : L ≤ L0
  · have hL2k : L ^ (2*k) ≤ q := le_trans (Nat.pow_le_pow_left hcase (2*k)) hL0pow
    have h1 := hmom L hL2k
    have hbr : (0:ℝ) ≤ (q:ℝ) ^ ε' * ((q:ℝ) * (L:ℝ) ^ k + (L:ℝ) ^ (2*k) * Real.sqrt (q:ℝ)) := by
      have h6 : (0:ℝ) ≤ (q:ℝ) ^ ε' := Real.rpow_nonneg hqpos.le _
      have h4 : (0:ℝ) ≤ (q:ℝ) * (L:ℝ) ^ k := by positivity
      have h5 : (0:ℝ) ≤ (L:ℝ) ^ (2*k) * Real.sqrt (q:ℝ) := by positivity
      positivity
    have hX : C * ((q:ℝ) ^ ε' * ((q:ℝ) * (L:ℝ) ^ k + (L:ℝ) ^ (2*k) * Real.sqrt (q:ℝ)))
        ≤ ((2:ℝ) ^ (3 * k + 1) * C) * ((q:ℝ) ^ ε'
            * ((q:ℝ) * (L:ℝ) ^ k + (L:ℝ) ^ (2*k) * Real.sqrt (q:ℝ))) := by
      apply mul_le_mul_of_nonneg_right _ hbr
      have h7 : (1:ℝ) ≤ (2:ℝ) ^ (3 * k + 1) := one_le_pow₀ (by norm_num)
      nlinarith only [hC, h7]
    calc ∑ m ∈ Finset.range q, ‖∑ h ∈ Finset.Ioc m (m + L), χ (h : ZMod q)‖ ^ (2 * k)
        ≤ C * (q:ℝ) ^ ε' * ((q:ℝ)*(L:ℝ)^k + (L:ℝ)^(2*k)*Real.sqrt (q:ℝ)) := h1
      _ = C * ((q:ℝ) ^ ε' * ((q:ℝ)*(L:ℝ)^k + (L:ℝ)^(2*k)*Real.sqrt (q:ℝ))) := by ring
      _ ≤ ((2:ℝ) ^ (3 * k + 1) * C) * (q:ℝ) ^ ε'
            * ((q:ℝ)*(L:ℝ)^k + (L:ℝ)^(2*k)*Real.sqrt (q:ℝ)) := by
          rw [mul_assoc]; exact hX
  · have hL0ltL : L0 < L := not_le.mp hcase
    set n : ℕ := L / L0 + 1 with hndef
    have hnL0 : L ≤ n * L0 := by
      have h1 : L / L0 * L0 + L % L0 = L := by
        rw [mul_comm]; exact Nat.div_add_mod L L0
      have h2 : L % L0 < L0 := Nat.mod_lt L (by omega : 0 < L0)
      calc L = L / L0 * L0 + L % L0 := h1.symm
        _ ≤ L / L0 * L0 + L0 := by omega
        _ = (L / L0 + 1) * L0 := by ring
        _ = n * L0 := by rw [hndef]
    have hncast : (n:ℝ) ≤ 2 * (L:ℝ) / (L0:ℝ) := by
      have hdiv1 : 1 ≤ L / L0 := by
        rw [Nat.one_le_div_iff (by omega : 0 < L0)]
        omega
      have hcastdiv : ((L / L0 : ℕ):ℝ) ≤ (L:ℝ)/(L0:ℝ) := Nat.cast_div_le
      have h2 : (1:ℝ) ≤ ((L / L0 : ℕ):ℝ) := by exact_mod_cast hdiv1
      rw [hndef]; push_cast
      have h4 : ((L / L0 : ℕ):ℝ) + 1 ≤ 2 * ((L / L0 : ℕ):ℝ) := by linarith only [h2]
      have h5 : 2 * ((L / L0 : ℕ):ℝ) ≤ 2 * ((L:ℝ)/(L0:ℝ)) :=
        mul_le_mul_of_nonneg_left hcastdiv (by norm_num)
      rw [mul_div_assoc]
      linarith only [h4, h5, hcastdiv, h2]
    set e : ℕ → ℕ := fun i => min (i*L0) L with hedef
    have hemono : ∀ i, e i ≤ e (i+1) := by
      intro i
      rw [hedef]; simp only
      apply min_le_min _ le_rfl
      nlinarith only [hL0_1]
    have he0 : e 0 = 0 := by rw [hedef]; simp
    have hen : e n = L := by rw [hedef]; simp only; exact min_eq_right hnL0
    have hestep : ∀ i, e (i+1) - e i ≤ L0 := by
      intro i
      rw [hedef]; simp only
      by_cases h : L ≤ i*L0
      · have h1 : min (i*L0) L = L := min_eq_right h
        have h2 : min ((i+1)*L0) L = L := by
          apply min_eq_right
          have : i*L0 ≤ (i+1)*L0 := by nlinarith only [hL0_1]
          omega
        omega
      · push_neg at h
        have h1 : min (i*L0) L = i*L0 := min_eq_left (le_of_lt h)
        have h2 : min ((i+1)*L0) L ≤ (i+1)*L0 := min_le_left _ _
        have h3 : (i+1)*L0 = i*L0 + L0 := by ring
        omega
    have htelesc : ∀ m : ℤ, cSum χ m (m + (L:ℤ))
        = ∑ i ∈ Finset.range n, cSum χ (m + (e i:ℤ)) (m + (e (i+1):ℤ)) := by
      intro m
      have hsub : ∀ i, cSum χ (m + (e i:ℤ)) (m + (e (i+1):ℤ))
          = cSum χ m (m + (e (i+1):ℤ)) - cSum χ m (m + (e i:ℤ)) := by
        intro i
        have h1 : m ≤ m + (e i:ℤ) := by
          have : (0:ℤ) ≤ (e i : ℤ) := by positivity
          linarith only []
        have h2 : m + (e i:ℤ) ≤ m + (e (i+1):ℤ) := by
          have hh : (e i : ℤ) ≤ (e (i+1) : ℤ) := by exact_mod_cast hemono i
          linarith only [hh]
        have hcomp := cSum_split χ h1 h2
        rw [hcomp]; ring
      rw [Finset.sum_congr rfl (fun i _ => hsub i),
          Finset.sum_range_sub (fun i => cSum χ m (m + (e i:ℤ))) n, hen, he0]
      simp [cSum]
    have hpoint : ∀ m : ℤ, ‖cSum χ m (m + (L:ℤ))‖ ^ (2*k)
        ≤ (n:ℝ) ^ (2*k - 1) *
            ∑ i ∈ Finset.range n, ‖cSum χ (m + (e i:ℤ)) (m + (e (i+1):ℤ))‖ ^ (2*k) := by
      intro m
      rw [htelesc m]
      have h2k : 2*k = (2*k - 1) + 1 := by omega
      have h1 : ‖∑ i ∈ Finset.range n, cSum χ (m + (e i:ℤ)) (m + (e (i+1):ℤ))‖ ^ (2*k)
          ≤ (∑ i ∈ Finset.range n, ‖cSum χ (m + (e i:ℤ)) (m + (e (i+1):ℤ))‖) ^ (2*k) :=
        pow_le_pow_left₀ (norm_nonneg _) (norm_sum_le _ _) _
      rw [h2k] at h1 ⊢
      have h3 := pow_sum_le_card_mul_sum_pow
        (s := Finset.range n) (f := fun i => ‖cSum χ (m + (e i:ℤ)) (m + (e (i+1):ℤ))‖)
        (fun i _ => norm_nonneg _) (2*k - 1)
      simpa [Finset.card_range] using h1.trans h3
    have hsum1 : ∑ m ∈ Finset.range q, ‖cSum χ (m:ℤ) ((m:ℤ) + (L:ℤ))‖^(2*k)
        ≤ (n:ℝ)^(2*k-1) * ∑ i ∈ Finset.range n,
            ∑ m ∈ Finset.range q, ‖cSum χ (m + (e i:ℤ)) (m + (e (i+1):ℤ))‖^(2*k) := by
      calc ∑ m ∈ Finset.range q, ‖cSum χ (m:ℤ) ((m:ℤ) + (L:ℤ))‖^(2*k)
          ≤ ∑ m ∈ Finset.range q, (n:ℝ)^(2*k-1) *
              ∑ i ∈ Finset.range n, ‖cSum χ (m + (e i:ℤ)) (m + (e (i+1):ℤ))‖^(2*k) :=
            Finset.sum_le_sum (fun m _ => hpoint m)
        _ = (n:ℝ)^(2*k-1) * ∑ m ∈ Finset.range q,
              ∑ i ∈ Finset.range n, ‖cSum χ (m + (e i:ℤ)) (m + (e (i+1):ℤ))‖^(2*k) := by
            rw [Finset.mul_sum]
        _ = (n:ℝ)^(2*k-1) * ∑ i ∈ Finset.range n,
              ∑ m ∈ Finset.range q, ‖cSum χ (m + (e i:ℤ)) (m + (e (i+1):ℤ))‖^(2*k) := by
            rw [Finset.sum_comm]
    have hper : ∀ i ∈ Finset.range n,
        ∑ m ∈ Finset.range q, ‖cSum χ (m + (e i:ℤ)) (m + (e (i+1):ℤ))‖^(2*k) ≤ B := by
      intro i _
      set d : ℕ := e (i+1) - e i with hddef
      have hde : e i + d = e (i+1) := by
        rw [hddef]; exact Nat.add_sub_cancel' (hemono i)
      have hdL0 : d ≤ L0 := by rw [hddef]; exact hestep i
      have hd2k : d ^ (2*k) ≤ q := le_trans (Nat.pow_le_pow_left hdL0 (2*k)) hL0pow
      have hb := hmom d hd2k
      have hb' : ∑ m ∈ Finset.range q, ‖cSum χ (m:ℤ) ((m:ℤ) + (d:ℤ))‖^(2*k)
          ≤ C * (q:ℝ)^ε' * ((q:ℝ)*(d:ℝ)^k + (d:ℝ)^(2*k)*Real.sqrt (q:ℝ)) := by
        have hsum_eq : ∑ m ∈ Finset.range q, ‖∑ h ∈ Finset.Ioc m (m + d), χ (h : ZMod q)‖^(2*k)
            = ∑ m ∈ Finset.range q, ‖cSum χ (m:ℤ) ((m:ℤ) + (d:ℤ))‖^(2*k) := by
          refine Finset.sum_congr rfl (fun m _ => ?_)
          rw [cSum_natCast]
        rw [← hsum_eq]; exact hb
      have hcongr : ∑ m ∈ Finset.range q, ‖cSum χ (m + (e i:ℤ)) (m + (e (i+1):ℤ))‖^(2*k)
          = ∑ m ∈ Finset.range q, ‖cSum χ (m + (e i:ℤ)) (m + (e i:ℤ) + (d:ℤ))‖^(2*k) := by
        refine Finset.sum_congr rfl (fun m _ => ?_)
        have hh : m + (e (i+1):ℤ) = m + (e i:ℤ) + (d:ℤ) := by
          have hcast : ((e i + d : ℕ):ℤ) = (e (i+1):ℤ) := by rw [hde]
          push_cast at hcast ⊢
          linarith only [hde]
        rw [hh]
      have hshift : ∑ m ∈ Finset.range q, ‖cSum χ (m + (e i:ℤ)) (m + (e i:ℤ) + (d:ℤ))‖^(2*k)
          = ∑ m ∈ Finset.range q, ‖cSum χ (m:ℤ) ((m:ℤ) + (d:ℤ))‖^(2*k) := by
        have hA : ∑ m ∈ Finset.range q, ‖cSum χ (m + (e i:ℤ)) (m + (e i:ℤ) + (d:ℤ))‖^(2*k)
            = ∑ m ∈ Finset.range q, ‖cSum χ ((e i:ℤ) + m) ((e i:ℤ) + m + (d:ℤ))‖^(2*k) :=
          Finset.sum_congr rfl (fun m _ => by
            have h1 : m + (e i:ℤ) = (e i:ℤ) + m := by ring
            rw [h1])
        rw [hA, ← sum_Icc_eq_sum_range (fun y => ‖cSum χ y (y + (d:ℤ))‖^(2*k)) (e i : ℤ) q,
            windowMom_eq_rangeSum χ k d (e i : ℤ)]
      rw [hcongr, hshift]
      refine hb'.trans ?_
      rw [hBdef]
      apply mul_le_mul_of_nonneg_left _ (by positivity : (0:ℝ) ≤ C * (q:ℝ)^ε')
      apply add_le_add
      · exact mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ (by positivity) (by exact_mod_cast hdL0) k) hqpos.le
      · exact mul_le_mul_of_nonneg_right
          (pow_le_pow_left₀ (by positivity) (by exact_mod_cast hdL0) (2*k)) (Real.sqrt_nonneg _)
    have hsum2 : ∑ i ∈ Finset.range n,
        ∑ m ∈ Finset.range q, ‖cSum χ (m + (e i:ℤ)) (m + (e (i+1):ℤ))‖^(2*k) ≤ n * B := by
      calc _ ≤ ∑ _i ∈ Finset.range n, B := Finset.sum_le_sum hper
        _ = n * B := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    have hstep1 : (n:ℝ)^(2*k-1) * (n * B) = (n:ℝ)^(2*k) * B := by
      rw [← mul_assoc, ← pow_succ]
      rw [show 2*k - 1 + 1 = 2*k by omega]
    have hnpow : (n:ℝ)^(2*k) ≤ (2*(L:ℝ)/(L0:ℝ))^(2*k) :=
      pow_le_pow_left₀ (by positivity) hncast (2*k)
    have hcoef : (2:ℝ)^(2*k) * (2^k + 1) ≤ 2^(3*k+1) := by
      have hp : (2:ℝ)^(2*k) * 2^k = 2^(3*k) := by
        rw [← pow_add]; congr 1; ring
      have hle : (2:ℝ)^(2*k) ≤ 2^(3*k) :=
        pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 2) (by omega)
      calc (2:ℝ)^(2*k) * (2^k + 1) = (2:ℝ)^(2*k)*2^k + (2:ℝ)^(2*k) := by ring
        _ = 2^(3*k) + (2:ℝ)^(2*k) := by rw [hp]
        _ ≤ 2^(3*k) + 2^(3*k) := by linarith only [hle]
        _ = 2^(3*k+1) := by rw [pow_succ]; ring
    have hmain : (n:ℝ)^(2*k) * B ≤ 2^(3*k+1) * C * (q:ℝ)^ε' *
        ((q:ℝ)*(L:ℝ)^k + (L:ℝ)^(2*k)*Real.sqrt (q:ℝ)) := by
      have h2k1 : (2*(L:ℝ)/(L0:ℝ))^(2*k) * B
          = 2^(2*k) * (L:ℝ)^(2*k) * C * (q:ℝ)^ε' *
              ((q:ℝ) / (L0:ℝ)^k + Real.sqrt (q:ℝ)) := by
        rw [hBdef, div_pow, mul_pow]
        field_simp
        ring
      have h3 : 2^(2*k) * (L:ℝ)^(2*k) * C * (q:ℝ)^ε' * ((q:ℝ) / (L0:ℝ)^k + Real.sqrt (q:ℝ))
          ≤ 2^(2*k) * (L:ℝ)^(2*k) * C * (q:ℝ)^ε' *
              (2^k * Real.sqrt (q:ℝ) + Real.sqrt (q:ℝ)) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        linarith only [hqdiv_sqrt]
      have h4 : 2^(2*k) * (L:ℝ)^(2*k) * C * (q:ℝ)^ε' *
            (2^k * Real.sqrt (q:ℝ) + Real.sqrt (q:ℝ))
          ≤ 2^(3*k+1) * C * (q:ℝ)^ε' * ((q:ℝ)*(L:ℝ)^k + (L:ℝ)^(2*k)*Real.sqrt (q:ℝ)) := by
        have hbracket : (2^k * Real.sqrt (q:ℝ) + Real.sqrt (q:ℝ))
            = (2^k + 1) * Real.sqrt (q:ℝ) := by ring
        rw [hbracket]
        have h5 : 2^(2*k) * (L:ℝ)^(2*k) * C * (q:ℝ)^ε' * ((2^k + 1) * Real.sqrt (q:ℝ))
            = ((2:ℝ)^(2*k) * (2^k + 1)) * ((L:ℝ)^(2*k) * Real.sqrt (q:ℝ) * C * (q:ℝ)^ε') := by
          ring
        rw [h5]
        have h6 : (0:ℝ) ≤ (L:ℝ)^(2*k) * Real.sqrt (q:ℝ) * C * (q:ℝ)^ε' := by positivity
        have h7 : ((2:ℝ)^(2*k) * (2^k + 1)) * ((L:ℝ)^(2*k) * Real.sqrt (q:ℝ) * C * (q:ℝ)^ε')
            ≤ 2^(3*k+1) * ((L:ℝ)^(2*k) * Real.sqrt (q:ℝ) * C * (q:ℝ)^ε') :=
          mul_le_mul_of_nonneg_right hcoef h6
        refine h7.trans ?_
        have h8 : (0:ℝ) ≤ 2^(3*k+1) * C * (q:ℝ)^ε' := by positivity
        have h9 : (L:ℝ)^(2*k) * Real.sqrt (q:ℝ)
            ≤ (q:ℝ)*(L:ℝ)^k + (L:ℝ)^(2*k)*Real.sqrt (q:ℝ) := by
          have := (show (0:ℝ) ≤ (q:ℝ)*(L:ℝ)^k by positivity); linarith only [this]
        calc 2^(3*k+1) * ((L:ℝ)^(2*k) * Real.sqrt (q:ℝ) * C * (q:ℝ)^ε')
            = 2^(3*k+1) * C * (q:ℝ)^ε' * ((L:ℝ)^(2*k) * Real.sqrt (q:ℝ)) := by ring
          _ ≤ 2^(3*k+1) * C * (q:ℝ)^ε' * ((q:ℝ)*(L:ℝ)^k + (L:ℝ)^(2*k)*Real.sqrt (q:ℝ)) :=
              mul_le_mul_of_nonneg_left h9 h8
      calc (n:ℝ)^(2*k) * B ≤ (2*(L:ℝ)/(L0:ℝ))^(2*k) * B :=
            mul_le_mul_of_nonneg_right hnpow hBnn
        _ = 2^(2*k) * (L:ℝ)^(2*k) * C * (q:ℝ)^ε' *
              ((q:ℝ) / (L0:ℝ)^k + Real.sqrt (q:ℝ)) := h2k1
        _ ≤ _ := h3
        _ ≤ _ := h4
    calc ∑ m ∈ Finset.range q, ‖∑ h ∈ Finset.Ioc m (m + L), χ (h : ZMod q)‖ ^ (2 * k)
        = ∑ m ∈ Finset.range q, ‖cSum χ (m:ℤ) ((m:ℤ) + (L:ℤ))‖^(2*k) := by
          refine Finset.sum_congr rfl (fun m _ => ?_)
          rw [cSum_natCast]
      _ ≤ (n:ℝ)^(2*k-1) * ∑ i ∈ Finset.range n,
            ∑ m ∈ Finset.range q, ‖cSum χ (m + (e i:ℤ)) (m + (e (i+1):ℤ))‖^(2*k) := hsum1
      _ ≤ (n:ℝ)^(2*k-1) * (n * B) := mul_le_mul_of_nonneg_left hsum2 (by positivity)
      _ = (n:ℝ)^(2*k) * B := hstep1
      _ ≤ 2^(3*k+1) * C * (q:ℝ)^ε' *
            ((q:ℝ)*(L:ℝ)^k + (L:ℝ)^(2*k)*Real.sqrt (q:ℝ)) := hmain

/-- Burgess's short-character-sum bound from a mean-value estimate, with the `q^ε` loss that the
general-modulus moment bound unavoidably carries.

The proven `Commons.NumberTheory.DirichletCharacter.burgess_charSum_uniform_of_moment` derives the
target bound (for `k = 2, 3`) from the *clean* mean-value estimate
`∑_{m<q} ‖∑_{m<n≤m+H} χ n‖^(2r) ≤ C (q H^r + H^(2r) √q)` for all `r` and all `H ≤ q`.  However
every provable general-modulus mean-value estimate carries an extra factor `q^ε` (coming from
`4^ω(q)` in the naive CRT/Weil bound; cf. `…burgess_moment_general_r2_eps` for `r = 2`), so the
needed variant takes the hypothesis

  for every `r > 0` and every `ε' > 0` there is `C` with
  `∑_{m<q} ‖∑_{m<n≤m+H} χ n‖^(2r) ≤ C * q^ε' * (q H^r + H^(2r) √q)`  for all `χ` primitive,
  non-trivial mod `q` and all `H` with `H^(2r) ≤ q`,

and concludes the target bound.  The restriction to the scales `H^(2r) ≤ q` is exactly what the
argument uses (the mean-value estimate is applied at the balanced scale `≈ q^(1/(2r))` of the
dyadic splitting; cf. D. R. Heath-Brown, arXiv:1203.5219, Lemma 3): for `r = 2` it is implied by
`…burgess_moment_general_r2_eps` (which holds for all `H ≤ q`), and for `r = 3` it is Burgess's
`r = 3` estimate (J. London Math. Soc. 33 (1986) 219-226; arXiv:1203.5219, Lemma 2 (iii)).

Proof adaptation: in the proof of `…burgess_charSum_uniform_of_moment` the mean-value constant
`Cm` enters exactly once, through `…burgess_core_gen`; instantiating `Cm := Cm0 * q^(ε/2)` there
(and `ε' := ε/2` in the hypothesis) turns every use of the estimate into one carrying `q^(ε/2)`,
and the final constant of `…burgess_core_gen` is linear in `Cm`, so the extra factor is absorbed
into the target's `q^ε`.  All the auxiliary results used by that proof
(`cSum_ap_split_gen`, `burgess_principle_gen`, `moment_W_le_gen`, `burgess_split_gen`,
`burgess_coprime_window_count_le`, `charSum_range_le_polyaVinogradov`, …) are already in the
commons and can be reused verbatim. -/
theorem burgess_charSum_uniform_of_moment_eps
    (hmom : ∀ r : ℕ, 0 < r → ∀ ε' : ℝ, 0 < ε' → ∃ C : ℝ, 0 < C ∧
      ∀ {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q), χ.IsPrimitive → χ ≠ 1 →
        ∀ H : ℕ, H ^ (2 * r) ≤ q →
          ∑ m ∈ Finset.range q, ‖∑ h ∈ Finset.Ioc m (m + H), χ (h : ZMod q)‖ ^ (2 * r)
            ≤ C * (q : ℝ) ^ ε' * ((q : ℝ) * (H : ℝ) ^ r + (H : ℝ) ^ (2 * r) * Real.sqrt (q : ℝ)))
    {ε : ℝ} (hε : 0 < ε) (k : ℕ) (hk : k = 2 ∨ k = 3) :
    ∃ C : ℝ, 0 < C ∧ ∀ {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q), χ.IsPrimitive → χ ≠ 1 →
      ∀ {N H : ℕ}, 1 ≤ N → 1 ≤ H → H ≤ q →
        ‖∑ n ∈ Finset.Ioc N (N + H), χ n‖ ≤
          C * (q : ℝ) ^ ((k + 1 : ℝ) / (4 * k ^ 2) + ε) * (H : ℝ) ^ (1 - 1 / (k : ℝ)) := by
  have hk1 : 1 ≤ k := by omega
  have hk2 : 2 ≤ k := by omega
  have hk3 : k ≤ 3 := by omega
  have hkpos : 0 < k := by omega
  have hkposR : (0:ℝ) < (k:ℝ) := by exact_mod_cast hkpos
  have hk1R : (1:ℝ) ≤ (k:ℝ) := by exact_mod_cast hk1
  have hk2R : (2:ℝ) ≤ (k:ℝ) := by exact_mod_cast hk2
  have hε2 : 0 < ε/2 := by linarith only [hε]
  obtain ⟨Ceps, hCepspos, hCeps⟩ := hmom k hkpos (ε/2) hε2
  set Cm : ℝ := max ((2:ℝ)^(3*k+1) * Ceps) 1 with hCmdef
  have hCm0le : ((2:ℝ)^(3*k+1) * Ceps) ≤ Cm := le_max_left _ _
  have hCm1 : 1 ≤ Cm := le_max_right _ _
  have hCmpos : 0 < Cm := lt_of_lt_of_le zero_lt_one hCm1
  have hCmC : ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ.IsPrimitive → χ ≠ 1 →
      ∀ L : ℕ, L ≤ q →
      ∑ m ∈ Finset.range q, ‖cSum χ (m:ℤ) ((m:ℤ) + L)‖^(2*k)
        ≤ (Cm * (q:ℝ)^(ε/2)) * ((q:ℝ) * (L:ℝ)^k + (L:ℝ)^(2*k) * Real.sqrt q) := by
    intro q _ χ hprim hχ L hL
    have h0 := moment_clean_of_eps χ k hk1 Ceps (ε/2) (le_of_lt hCepspos)
      (fun H hH => hCeps χ hprim hχ H hH) L hL
    set bracket : ℝ := (q:ℝ) * (L:ℝ)^k + (L:ℝ)^(2*k) * Real.sqrt (q:ℝ) with hbrk
    have hbrnn : 0 ≤ bracket := by
      rw [hbrk]
      have h2 : (0:ℝ) ≤ (q:ℝ) * (L:ℝ)^k := by positivity
      have h3 : (0:ℝ) ≤ (L:ℝ)^(2*k) * Real.sqrt (q:ℝ) := by positivity
      positivity
    have hqn : (0:ℝ) ≤ (q:ℝ)^(ε/2) := Real.rpow_nonneg (by positivity) _
    have hstep : ((2:ℝ)^(3*k+1) * Ceps) * (q:ℝ)^(ε/2) * bracket
        ≤ (Cm * (q:ℝ)^(ε/2)) * bracket := by
      apply mul_le_mul_of_nonneg_right _ hbrnn
      exact mul_le_mul_of_nonneg_right hCm0le hqn
    have hsum : ∑ m ∈ Finset.range q, ‖cSum χ (m:ℤ) ((m:ℤ) + L)‖^(2*k)
        = ∑ m ∈ Finset.range q, ‖∑ h ∈ Finset.Ioc m (m + L), χ (h : ZMod q)‖ ^ (2*k) := by
      refine Finset.sum_congr rfl (fun m hm => ?_)
      rw [cSum_natCast]
    rw [hsum]
    show ∑ m ∈ Finset.range q, ‖∑ h ∈ Finset.Ioc m (m + L), χ (h : ZMod q)‖ ^ (2*k)
        ≤ (Cm * (q:ℝ)^(ε/2)) * bracket
    exact h0.trans hstep
  obtain ⟨Ccs, hCcspos, hCcs⟩ := charSum_range_le_polyaVinogradov
  obtain ⟨C1, hC1pos, hC1⟩ := Commons.Analysis.Real.log_pow_le_mul_rpow
    (show (0:ℝ) < ε/2 by linarith only [hε]) (10*k+21)
  have h512nn : (0:ℝ) ≤ 2^512 := pow_nonneg (by norm_num : (0:ℝ) ≤ 2) 512
  have h512one : (1:ℝ) ≤ 2^512 := one_le_pow₀ (by norm_num : (1:ℝ) ≤ 2)
  have hBigpos : (0:ℝ) < 2^512 + 2^70 * 600 * Cm * C1 + 2 * Ccs + 1 := by
    have h5 : (0:ℝ) < 2^70 * 600 * Cm * C1 := by positivity
    have h6 : (0:ℝ) < 2 * Ccs := by linarith only [hCcspos]
    linarith only [hCcspos, h5]
  refine ⟨2^512 + 2^70 * 600 * Cm * C1 + 2 * Ccs + 1, hBigpos, ?_⟩
  intro q _ χ hχprim hχne N H hN1 hH1 hHq
  have hqposN : 0 < q := Nat.pos_of_ne_zero (NeZero.ne q)
  have hq0 : (0:ℝ) < (q:ℝ) := by exact_mod_cast hqposN
  have hq1 : (1:ℝ) ≤ (q:ℝ) := by exact_mod_cast (show 1 ≤ q by omega)
  have hHpos : (0:ℝ) < (H:ℝ) := by exact_mod_cast hH1
  have hHnn : (0:ℝ) ≤ (H:ℝ) := hHpos.le
  have hHqR : (H:ℝ) ≤ (q:ℝ) := by exact_mod_cast hHq
  have hσpos : (0:ℝ) < (k + 1 : ℝ) / (4 * k ^ 2) + ε := by
    have h1 : (0:ℝ) < (k + 1 : ℝ) / (4 * k ^ 2) := by positivity
    linarith only [hε, h1]
  have htriv : ∀ (N' H' : ℕ), ‖∑ n ∈ Finset.Ioc N' (N' + H'), χ (n : ZMod q)‖ ≤ (H':ℝ) := by
    intro N' H'
    calc ‖∑ n ∈ Finset.Ioc N' (N' + H'), χ (n : ZMod q)‖
        ≤ ∑ n ∈ Finset.Ioc N' (N' + H'), ‖χ (n : ZMod q)‖ := norm_sum_le _ _
      _ ≤ ∑ _n ∈ Finset.Ioc N' (N' + H'), (1:ℝ) :=
          Finset.sum_le_sum (fun n _ => DirichletCharacter.norm_le_one χ _)
      _ = (H':ℝ) := by
          rw [Finset.sum_const, Nat.card_Ioc, nsmul_eq_mul, mul_one,
            show N' + H' - N' = H' by omega]
  rcases lt_or_ge q (2^512) with hq512lt | hq512
  · -- ### case A: q < 2^512
    have hqexp : (q:ℝ)^((1:ℝ)/(k:ℝ) - ((k + 1 : ℝ) / (4 * k ^ 2) + ε)) ≤ 2^512 := by
      by_cases ha : (0:ℝ) ≤ (1:ℝ)/(k:ℝ) - ((k + 1 : ℝ) / (4 * k ^ 2) + ε)
      · have ha1 : (1:ℝ)/(k:ℝ) - ((k + 1 : ℝ) / (4 * k ^ 2) + ε) ≤ 1 := by
          have h1 : (1:ℝ)/(k:ℝ) ≤ 1 := by
            rw [div_le_one hkposR]; exact hk1R
          linarith only [hσpos, h1]
        calc (q:ℝ)^((1:ℝ)/(k:ℝ) - ((k + 1 : ℝ) / (4 * k ^ 2) + ε))
            ≤ (((2^512 : ℕ)):ℝ)^((1:ℝ)/(k:ℝ) - ((k + 1 : ℝ) / (4 * k ^ 2) + ε)) :=
              Real.rpow_le_rpow hq0.le (by exact_mod_cast (le_of_lt hq512lt)) ha
          _ ≤ (((2^512 : ℕ)):ℝ)^(1:ℝ) :=
              Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast Nat.one_le_two_pow) ha1
          _ = 2^512 := by rw [Real.rpow_one, Nat.cast_pow, Nat.cast_ofNat]
      · push_neg at ha
        have hqa : (1:ℝ) ≤ (q:ℝ)^(-((1:ℝ)/(k:ℝ) - ((k + 1 : ℝ) / (4 * k ^ 2) + ε))) :=
          Real.one_le_rpow hq1 (by linarith only [ha])
        calc (q:ℝ)^((1:ℝ)/(k:ℝ) - ((k + 1 : ℝ) / (4 * k ^ 2) + ε))
            = ((q:ℝ)^(-((1:ℝ)/(k:ℝ) - ((k + 1 : ℝ) / (4 * k ^ 2) + ε))))⁻¹ := by
              rw [Real.rpow_neg hq0.le, inv_inv]
          _ ≤ 1 := inv_le_one_of_one_le₀ hqa
          _ ≤ 2^512 := h512one
    have hsplit : (H:ℝ) = (H:ℝ)^((1:ℝ)/(k:ℝ)) * (H:ℝ)^(1 - 1/(k:ℝ)) := by
      rw [← Real.rpow_add hHpos]
      have he : (1:ℝ)/(k:ℝ) + (1 - 1/(k:ℝ)) = 1 := by ring
      rw [he, Real.rpow_one]
    have hHk : (H:ℝ)^((1:ℝ)/(k:ℝ)) ≤ (q:ℝ)^((1:ℝ)/(k:ℝ)) :=
      Real.rpow_le_rpow hHnn hHqR (by positivity)
    have hqσ_eq : (q:ℝ)^((1:ℝ)/(k:ℝ))
        = (q:ℝ)^((1:ℝ)/(k:ℝ) - ((k + 1 : ℝ) / (4 * k ^ 2) + ε))
          * (q:ℝ)^((k + 1 : ℝ) / (4 * k ^ 2) + ε) := by
      rw [← Real.rpow_add hq0]
      congr 1
      ring
    calc ‖∑ n ∈ Finset.Ioc N (N + H), χ (n : ZMod q)‖ ≤ (H:ℝ) := htriv N H
      _ = (H:ℝ)^((1:ℝ)/(k:ℝ)) * (H:ℝ)^(1 - 1/(k:ℝ)) := hsplit
      _ ≤ (q:ℝ)^((1:ℝ)/(k:ℝ)) * (H:ℝ)^(1 - 1/(k:ℝ)) :=
          mul_le_mul_of_nonneg_right hHk (Real.rpow_nonneg hHnn _)
      _ = (q:ℝ)^((1:ℝ)/(k:ℝ) - ((k + 1 : ℝ) / (4 * k ^ 2) + ε))
            * (q:ℝ)^((k + 1 : ℝ) / (4 * k ^ 2) + ε) * (H:ℝ)^(1 - 1/(k:ℝ)) := by
          rw [hqσ_eq]
      _ ≤ 2^512 * (q:ℝ)^((k + 1 : ℝ) / (4 * k ^ 2) + ε) * (H:ℝ)^(1 - 1/(k:ℝ)) := by
          apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hHnn _)
          exact mul_le_mul_of_nonneg_right hqexp (by positivity)
      _ ≤ (2^512 + 2^70 * 600 * Cm * C1 + 2 * Ccs + 1)
            * (q:ℝ)^((k + 1 : ℝ) / (4 * k ^ 2) + ε) * (H:ℝ)^(1 - 1/(k:ℝ)) := by
          apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hHnn _)
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          have h5 : (0:ℝ) ≤ 2^70 * 600 * Cm * C1 := by positivity
          have h6 : (0:ℝ) ≤ 2 * Ccs := by linarith only [hCcspos]
          linarith only [hCcspos, h5]
  · -- q ≥ 2^512
    have hq60 : 2^60 ≤ q :=
      le_trans (by simpa using Nat.pow_le_pow_right (by norm_num : 0 < 2) (by norm_num : 60 ≤ 512)) hq512
    have hq2 : 2 ≤ q :=
      le_trans (by simpa using Nat.pow_le_pow_right (by norm_num : 0 < 2) (by norm_num : 1 ≤ 512)) hq512
    have hq2R : (2:ℝ) ≤ (q:ℝ) := by exact_mod_cast hq2
    have hqlog : (0:ℝ) < Real.log q := Real.log_pos (by linarith only [hq2R])
    have hL20 : (20:ℝ) ≤ Real.log q := by
      have h1 : Real.log ((2:ℝ)^512) ≤ Real.log q :=
        Real.log_le_log (by positivity) (by exact_mod_cast hq512)
      have h2 : Real.log ((2:ℝ)^512) = 512 * Real.log 2 := by rw [Real.log_pow]; norm_num
      have h3 : (20:ℝ) ≤ 512 * Real.log 2 := by linarith only [Real.log_two_gt_d9]
      linarith only [h1, h2, h3]
    by_cases hB : (H:ℝ) ≤ (q:ℝ)^((k + 1 : ℝ) / (4 * k : ℝ))
    · -- ### case B: H ≤ q^((k+1)/(4k))
      have hHk : (H:ℝ)^((1:ℝ)/(k:ℝ)) ≤ (q:ℝ)^((k + 1 : ℝ) / (4 * k ^ 2)) := by
        calc (H:ℝ)^((1:ℝ)/(k:ℝ)) ≤ ((q:ℝ)^((k + 1 : ℝ) / (4 * k : ℝ)))^((1:ℝ)/(k:ℝ)) :=
              Real.rpow_le_rpow hHnn hB (by positivity)
          _ = (q:ℝ)^((k + 1 : ℝ) / (4 * k : ℝ) * ((1:ℝ)/(k:ℝ))) := by
              rw [← Real.rpow_mul hq0.le]
          _ = (q:ℝ)^((k + 1 : ℝ) / (4 * k ^ 2)) := by
              congr 1
              field_simp
      have hsplit : (H:ℝ) = (H:ℝ)^((1:ℝ)/(k:ℝ)) * (H:ℝ)^(1 - 1/(k:ℝ)) := by
        rw [← Real.rpow_add hHpos]
        have he : (1:ℝ)/(k:ℝ) + (1 - 1/(k:ℝ)) = 1 := by ring
        rw [he, Real.rpow_one]
      calc ‖∑ n ∈ Finset.Ioc N (N + H), χ (n : ZMod q)‖ ≤ (H:ℝ) := htriv N H
        _ = (H:ℝ)^((1:ℝ)/(k:ℝ)) * (H:ℝ)^(1 - 1/(k:ℝ)) := hsplit
        _ ≤ (q:ℝ)^((k + 1 : ℝ) / (4 * k ^ 2)) * (H:ℝ)^(1 - 1/(k:ℝ)) :=
            mul_le_mul_of_nonneg_right hHk (Real.rpow_nonneg hHnn _)
        _ ≤ (2^512 + 2^70 * 600 * Cm * C1 + 2 * Ccs + 1)
              * (q:ℝ)^((k + 1 : ℝ) / (4 * k ^ 2) + ε) * (H:ℝ)^(1 - 1/(k:ℝ)) := by
            have h5 : (q:ℝ)^((k + 1 : ℝ) / (4 * k ^ 2))
                ≤ (q:ℝ)^((k + 1 : ℝ) / (4 * k ^ 2) + ε) :=
              Real.rpow_le_rpow_of_exponent_le hq1 (by linarith only [hε])
            have h6 : (1:ℝ) ≤ 2^512 + 2^70 * 600 * Cm * C1 + 2 * Ccs + 1 := by
              have h7 : (0:ℝ) ≤ 2^70 * 600 * Cm * C1 := by positivity
              linarith only [hCcspos, h7, h512nn]
            calc (q:ℝ)^((k + 1 : ℝ) / (4 * k ^ 2)) * (H:ℝ)^(1 - 1/(k:ℝ))
                ≤ (q:ℝ)^((k + 1 : ℝ) / (4 * k ^ 2) + ε) * (H:ℝ)^(1 - 1/(k:ℝ)) :=
                  mul_le_mul_of_nonneg_right h5 (Real.rpow_nonneg hHnn _)
              _ ≤ (2^512 + 2^70 * 600 * Cm * C1 + 2 * Ccs + 1) * (q:ℝ)^((k + 1 : ℝ) / (4 * k ^ 2) + ε)
                    * (H:ℝ)^(1 - 1/(k:ℝ)) := by
                  rw [mul_assoc]
                  exact le_mul_of_one_le_left (by positivity) h6
    · push_neg at hB
      by_cases hC : (q:ℝ)^((2 * k + 1 : ℝ) / (4 * k : ℝ)) * (Real.log q)^(4*k+8) ≤ (H:ℝ)
      · -- ### case C: Polya-Vinogradov
        have hlog : Real.log (2*(q:ℝ) + 2) ≤ 2 * Real.log q := by
          calc Real.log (2*(q:ℝ) + 2) ≤ Real.log (4*(q:ℝ)) :=
                Real.log_le_log (by positivity) (by linarith only [hq2R])
            _ = Real.log 4 + Real.log (q:ℝ) :=
                Real.log_mul (by norm_num) (ne_of_gt hq0)
            _ = 2*Real.log 2 + Real.log q := by
                rw [show (4:ℝ) = (2:ℝ)^2 by norm_num, Real.log_pow]; norm_num
            _ ≤ 2 * Real.log q := by
                have h3 : (2:ℝ) * Real.log 2 ≤ 20 := by linarith only [Real.log_two_lt_d9]
                linarith only [hL20, h3]
        have hS : ‖∑ n ∈ Finset.Ioc N (N + H), χ (n : ZMod q)‖
            ≤ Ccs * Real.sqrt (q:ℝ) * Real.log (2*(q:ℝ) + 2) := by
          rw [Ioc_eq_Icc' hH1]
          exact hCcs q hq2 χ hχne (N+1) (N+H) (by omega)
        set Me : ℝ := ((4*k+8 : ℕ) : ℝ) * (1 - 1/(k:ℝ)) with hmdef
        have hm1 : (1:ℝ) ≤ Me := by
          have h7 : (1:ℝ)/(k:ℝ) ≤ (1:ℝ)/2 := by
            rw [div_le_div_iff₀ hkposR (by norm_num : (0:ℝ) < 2)]
            linarith only [hk2R]
          have h8 : (8:ℝ) ≤ ((4*k+8 : ℕ) : ℝ) := by push_cast; linarith only [hk1R, hk2R]
          have h9 : (1:ℝ)/2 ≤ 1 - 1/(k:ℝ) := by linarith only [h7]
          rw [hmdef]
          nlinarith only [h8, h9, h7]
        have hmnn : (0:ℝ) ≤ Me := le_trans zero_le_one hm1
        have hLpos' : (0:ℝ) ≤ Real.log q := by linarith only [hL20]
        have hL1' : (1:ℝ) ≤ Real.log q := by linarith only [hL20]
        have hHlower : (q:ℝ)^(((2*k+1:ℝ)/(4*k:ℝ)) * (1 - 1/(k:ℝ))) * (Real.log q)^Me
            ≤ (H:ℝ)^(1 - 1/(k:ℝ)) := by
          have hpow : ((q:ℝ)^((2*k+1:ℝ)/(4*k:ℝ)) * (Real.log q)^(4*k+8))^(1 - 1/(k:ℝ))
              = (q:ℝ)^(((2*k+1:ℝ)/(4*k:ℝ)) * (1 - 1/(k:ℝ))) * (Real.log q)^Me := by
            have h2 : ((Real.log q)^(4*k+8))^(1 - 1/(k:ℝ)) = (Real.log q)^Me := by
              rw [hmdef, ← Real.rpow_natCast (x := Real.log q) (n := 4*k+8),
                ← Real.rpow_mul hLpos']
            rw [Real.mul_rpow (Real.rpow_nonneg hq0.le _) (pow_nonneg hLpos' _),
              ← Real.rpow_mul hq0.le, h2]
          rw [← hpow]
          exact Real.rpow_le_rpow (by positivity : (0:ℝ) ≤ (q:ℝ)^((2*k+1:ℝ)/(4*k:ℝ)) * (Real.log q)^(4*k+8)) hC (by
            have h3 : (1:ℝ)/(k:ℝ) ≤ 1 := by rw [div_le_one hkposR]; exact hk1R
            linarith only [h3])
        have hterm : (2:ℝ)*Ccs * Real.log q ≤ (2^512 + 2^70 * 600 * Cm * C1 + 2 * Ccs + 1)
            * (q:ℝ)^ε * (Real.log q)^Me := by
          have h1 : Real.log q ≤ (Real.log q)^Me := by
            have h2 := Real.rpow_le_rpow_of_exponent_le hL1' hm1
            rwa [Real.rpow_one] at h2
          have h2 : (0:ℝ) ≤ (Real.log q)^Me := by positivity
          have h3 : (2:ℝ)*Ccs ≤ 2^512 + 2^70 * 600 * Cm * C1 + 2 * Ccs + 1 := by
            have h5 : (0:ℝ) ≤ 2^70 * 600 * Cm * C1 := by positivity
            linarith only [h5, h512nn]
          have h4 : (1:ℝ) ≤ (q:ℝ)^ε := Real.one_le_rpow hq1 hε.le
          calc (2:ℝ)*Ccs * Real.log q
              ≤ (2^512 + 2^70 * 600 * Cm * C1 + 2 * Ccs + 1) * (Real.log q)^Me := by
                calc (2:ℝ)*Ccs * Real.log q
                    ≤ (2^512 + 2^70 * 600 * Cm * C1 + 2 * Ccs + 1) * Real.log q :=
                      mul_le_mul_of_nonneg_right h3 hLpos'
                  _ ≤ (2^512 + 2^70 * 600 * Cm * C1 + 2 * Ccs + 1) * (Real.log q)^Me :=
                      mul_le_mul_of_nonneg_left h1 (by positivity)
            _ ≤ (2^512 + 2^70 * 600 * Cm * C1 + 2 * Ccs + 1) * (q:ℝ)^ε * (Real.log q)^Me := by
                have h6 : (Real.log q)^Me ≤ (q:ℝ)^ε * (Real.log q)^Me :=
                  le_mul_of_one_le_left h2 h4
                calc (2^512 + 2^70 * 600 * Cm * C1 + 2 * Ccs + 1) * (Real.log q)^Me
                    ≤ (2^512 + 2^70 * 600 * Cm * C1 + 2 * Ccs + 1) * ((q:ℝ)^ε * (Real.log q)^Me) :=
                      mul_le_mul_of_nonneg_left h6 (by positivity)
                  _ = (2^512 + 2^70 * 600 * Cm * C1 + 2 * Ccs + 1) * (q:ℝ)^ε * (Real.log q)^Me := by ring
        have hσa : (k + 1 : ℝ) / (4 * k ^ 2) + ε + ((2*k+1:ℝ)/(4*k:ℝ)) * (1 - 1/(k:ℝ))
            = (1:ℝ)/2 + ε := by
          have hkne : (k:ℝ) ≠ 0 := ne_of_gt hkposR
          field_simp
          ring
        have hmid : (q:ℝ)^((1:ℝ)/2 + ε) * (Real.log q)^Me
            ≤ (q:ℝ)^((k + 1 : ℝ) / (4 * k ^ 2) + ε) * (H:ℝ)^(1 - 1/(k:ℝ)) := by
          have h1 : (q:ℝ)^((k + 1 : ℝ) / (4 * k ^ 2) + ε
                + ((2*k+1:ℝ)/(4*k:ℝ)) * (1 - 1/(k:ℝ))) = (q:ℝ)^((1:ℝ)/2 + ε) := by
            rw [hσa]
          calc (q:ℝ)^((1:ℝ)/2 + ε) * (Real.log q)^Me
              = (q:ℝ)^((k + 1 : ℝ) / (4 * k ^ 2) + ε
                  + ((2*k+1:ℝ)/(4*k:ℝ)) * (1 - 1/(k:ℝ))) * (Real.log q)^Me := by rw [h1]
            _ = (q:ℝ)^((k + 1 : ℝ) / (4 * k ^ 2) + ε)
                  * (q:ℝ)^(((2*k+1:ℝ)/(4*k:ℝ)) * (1 - 1/(k:ℝ))) * (Real.log q)^Me := by
                rw [Real.rpow_add hq0]
            _ ≤ (q:ℝ)^((k + 1 : ℝ) / (4 * k ^ 2) + ε) * (H:ℝ)^(1 - 1/(k:ℝ)) := by
                calc (q:ℝ)^((k + 1 : ℝ) / (4 * k ^ 2) + ε)
                      * (q:ℝ)^(((2*k+1:ℝ)/(4*k:ℝ)) * (1 - 1/(k:ℝ))) * (Real.log q)^Me
                    = (q:ℝ)^((k + 1 : ℝ) / (4 * k ^ 2) + ε)
                      * ((q:ℝ)^(((2*k+1:ℝ)/(4*k:ℝ)) * (1 - 1/(k:ℝ))) * (Real.log q)^Me) := by ring
                  _ ≤ (q:ℝ)^((k + 1 : ℝ) / (4 * k ^ 2) + ε) * (H:ℝ)^(1 - 1/(k:ℝ)) :=
                      mul_le_mul_of_nonneg_left hHlower (by positivity)
        have hmain : (2:ℝ)*Ccs * (q:ℝ)^((1:ℝ)/2) * (Real.log q)
            ≤ (2^512 + 2^70 * 600 * Cm * C1 + 2 * Ccs + 1) * (q:ℝ)^((1:ℝ)/2 + ε)
              * (Real.log q)^Me := by
          have he : (q:ℝ)^ε * (q:ℝ)^((1:ℝ)/2) = (q:ℝ)^((1:ℝ)/2 + ε) := by
            rw [← Real.rpow_add hq0]
            congr 1
            ring
          have h : (2:ℝ)*Ccs * (Real.log q) ≤ (2^512 + 2^70 * 600 * Cm * C1 + 2 * Ccs + 1)
              * (q:ℝ)^ε * (Real.log q)^Me := hterm
          calc (2:ℝ)*Ccs * (q:ℝ)^((1:ℝ)/2) * (Real.log q)
              = ((2:ℝ)*Ccs * (Real.log q)) * (q:ℝ)^((1:ℝ)/2) := by ring
            _ ≤ ((2^512 + 2^70 * 600 * Cm * C1 + 2 * Ccs + 1) * (q:ℝ)^ε * (Real.log q)^Me)
                  * (q:ℝ)^((1:ℝ)/2) :=
                mul_le_mul_of_nonneg_right h (Real.rpow_nonneg hq0.le _)
            _ = (2^512 + 2^70 * 600 * Cm * C1 + 2 * Ccs + 1) * (q:ℝ)^((1:ℝ)/2 + ε)
                  * (Real.log q)^Me := by
                rw [show ((2^512 + 2^70 * 600 * Cm * C1 + 2 * Ccs + 1) * (q:ℝ)^ε * (Real.log q)^Me)
                      * (q:ℝ)^((1:ℝ)/2)
                    = (2^512 + 2^70 * 600 * Cm * C1 + 2 * Ccs + 1) * ((q:ℝ)^ε * (q:ℝ)^((1:ℝ)/2))
                      * (Real.log q)^Me from by ring]
                rw [he]
        calc ‖∑ n ∈ Finset.Ioc N (N + H), χ (n : ZMod q)‖
            ≤ Ccs * Real.sqrt (q:ℝ) * Real.log (2*(q:ℝ) + 2) := hS
          _ ≤ Ccs * Real.sqrt (q:ℝ) * (2 * Real.log q) :=
              mul_le_mul_of_nonneg_left hlog (by positivity)
          _ = (2:ℝ)*Ccs * (q:ℝ)^((1:ℝ)/2) * (Real.log q) := by
              rw [Real.sqrt_eq_rpow]; ring
          _ ≤ (2^512 + 2^70 * 600 * Cm * C1 + 2 * Ccs + 1) * (q:ℝ)^((1:ℝ)/2 + ε)
                * (Real.log q)^Me := hmain
          _ ≤ (2^512 + 2^70 * 600 * Cm * C1 + 2 * Ccs + 1)
                * (q:ℝ)^((k + 1 : ℝ) / (4 * k ^ 2) + ε) * (H:ℝ)^(1 - 1/(k:ℝ)) := by
              rw [show (2^512 + 2^70 * 600 * Cm * C1 + 2 * Ccs + 1) * (q:ℝ)^((1:ℝ)/2 + ε)
                    * (Real.log q)^Me
                  = (2^512 + 2^70 * 600 * Cm * C1 + 2 * Ccs + 1)
                    * ((q:ℝ)^((1:ℝ)/2 + ε) * (Real.log q)^Me) from by ring]
              refine (mul_le_mul_of_nonneg_left hmid
                (by positivity : (0:ℝ) ≤ 2^512 + 2^70 * 600 * Cm * C1 + 2 * Ccs + 1)).trans_eq ?_
              ring
      · -- ### case D: core
        push_neg at hC
        have hHhi : (H:ℝ) ≤ (q:ℝ)^((2 * k + 1 : ℝ) / (4 * k : ℝ)) * (Real.log q)^(4*k+8) :=
          le_of_lt hC
        have hHlo : (q:ℝ)^((k + 1 : ℝ) / (4 * k : ℝ)) ≤ (H:ℝ) := le_of_lt hB
        set A : ℝ := (H:ℝ) * (q:ℝ)^(-(1/(2*(k:ℝ)))) with hAdef
        have hA_nn : (0:ℝ) ≤ A := by
          rw [hAdef]; exact mul_nonneg hHnn (Real.rpow_nonneg hq0.le _)
        have hA_ge : (q:ℝ)^((1:ℝ)/8) ≤ A := by
          rw [hAdef]
          have h1 : (q:ℝ)^((k + 1 : ℝ) / (4 * k : ℝ)) * (q:ℝ)^(-(1/(2*(k:ℝ))))
              ≤ (H:ℝ) * (q:ℝ)^(-(1/(2*(k:ℝ)))) :=
            mul_le_mul_of_nonneg_right hHlo (Real.rpow_nonneg hq0.le _)
          have h2 : (q:ℝ)^((k + 1 : ℝ) / (4 * k : ℝ)) * (q:ℝ)^(-(1/(2*(k:ℝ))))
              = (q:ℝ)^(((k:ℝ) - 1) / (4 * k : ℝ)) := by
            rw [← Real.rpow_add hq0]
            congr 1
            field_simp
            ring
          have h3 : (1:ℝ)/8 ≤ ((k:ℝ) - 1) / (4 * k : ℝ) := by
            rw [div_le_div_iff₀ (by norm_num) (by positivity)]
            nlinarith only [hk2R]
          have h4 : (q:ℝ)^((1:ℝ)/8) ≤ (q:ℝ)^(((k:ℝ) - 1) / (4 * k : ℝ)) :=
            Real.rpow_le_rpow_of_exponent_le hq1 h3
          linarith only [h1, h2.ge, h4, h2]
        have hP1 : 1 ≤ Nat.floor A + 1 := Nat.le_add_left 1 _
        have hq512R : (2:ℝ)^512 ≤ (q:ℝ) := by
          have h1 : ((2^512 : ℕ) : ℝ) ≤ (q:ℝ) := Nat.cast_le.mpr hq512
          rwa [Nat.cast_pow, Nat.cast_ofNat] at h1
        have hP64 : 2^64 ≤ Nat.floor A + 1 := by
          have hh : (2:ℝ)^64 ≤ (q:ℝ)^((1:ℝ)/8) := by
            have h := Real.rpow_le_rpow (pow_nonneg (by norm_num : (0:ℝ) ≤ 2) 512) hq512R
              (by norm_num : (0:ℝ) ≤ 1/8)
            have h2 : ((2:ℝ)^512)^((1:ℝ)/8) = (2:ℝ)^64 := by
              rw [← Real.rpow_natCast (x := (2:ℝ)) (n := 512), ← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2)]
              norm_num
            linarith only [h, h2.le]
          have hlt : (2:ℝ)^64 < ((Nat.floor A + 1 : ℕ) : ℝ) := by
            have hcast : ((Nat.floor A + 1 : ℕ) : ℝ) = (Nat.floor A : ℝ) + 1 := by
              push_cast; ring
            rw [hcast]
            exact lt_of_le_of_lt (le_trans hh hA_ge) (Nat.lt_floor_add_one A)
          exact_mod_cast hlt.le
        have hPq8 : q ≤ (Nat.floor A + 1)^8 := by
          have h4 : ((q:ℝ)^((1:ℝ)/8))^8 = (q:ℝ) := by
            rw [← Real.rpow_natCast (x := (q:ℝ)^((1:ℝ)/8)) (n := 8), ← Real.rpow_mul hq0.le,
              show ((1:ℝ)/8) * ((8:ℕ):ℝ) = 1 by norm_num, Real.rpow_one]
          have h2 : (q:ℝ) ≤ A^8 := by
            have h := Real.rpow_le_rpow (Real.rpow_nonneg hq0.le _) hA_ge
              (by norm_num : (0:ℝ) ≤ 8)
            have eq : ((q:ℝ)^((1:ℝ)/8))^(8:ℝ) = (q:ℝ) := by
              rw [show ((q:ℝ)^((1:ℝ)/8))^(8:ℝ) = ((q:ℝ)^((1:ℝ)/8))^8 by norm_num, h4]
            have eA : A^(8:ℝ) = A^8 := by norm_num
            rw [eq, eA] at h
            exact h
          have h3 : A^8 < ((Nat.floor A + 1 : ℕ) : ℝ)^8 := by
            have hcast : ((Nat.floor A + 1 : ℕ) : ℝ) = (Nat.floor A : ℝ) + 1 := by
              push_cast; ring
            rw [hcast]
            exact pow_lt_pow_left₀ (Nat.lt_floor_add_one A) hA_nn (by norm_num : 8 ≠ 0)
          have hq8' : (q:ℝ) < (((Nat.floor A + 1)^8 : ℕ) : ℝ) := by
            rw [Nat.cast_pow]
            exact lt_of_le_of_lt h2 h3
          exact_mod_cast hq8'.le
        have hcount := burgess_coprime_window_count_le (q := q) (P := Nat.floor A + 1) hqposN hP64 hPq8
        set CL : ℝ := 300 * Real.log (2 * ((Nat.floor A + 1 : ℕ) : ℝ)) with hCLdef
        have hP1R : (1:ℝ) ≤ ((Nat.floor A + 1 : ℕ) : ℝ) := by exact_mod_cast hP1
        have hCL0 : (0:ℝ) ≤ CL := by
          rw [hCLdef]
          exact mul_nonneg (by norm_num) (Real.log_nonneg (by linarith only [hP1R]))
        set N' : ℤ := ((N % q : ℕ) : ℤ) with hNdef
        have hN'0 : (0:ℤ) ≤ N' := by rw [hNdef]; exact_mod_cast Nat.zero_le _
        have hN'q : N' < (q:ℤ) := by
          rw [hNdef]; exact_mod_cast Nat.mod_lt N (by omega)
        have hsplitP : ((Nat.floor A + 1 : ℕ) : ℝ) * ‖cSum χ N' (N' + (H:ℤ))‖
            ≤ CL * ∑ x ∈ objFinset (Nat.floor A + 1),
                ‖cSum χ (oLo N' q x.1 x.2) (oHi N' q H x.1 x.2)‖ :=
          burgess_split_gen χ N' H (Nat.floor A + 1) hP1 CL hCL0 hcount
        have hsplit' : ((Nat.floor A : ℝ) + 1) * ‖cSum χ N' (N' + (H:ℤ))‖
            ≤ CL * ∑ x ∈ objFinset (Nat.floor A + 1),
                ‖cSum χ (oLo N' q x.1 x.2) (oHi N' q H x.1 x.2)‖ := by
          rw [Nat.cast_add, Nat.cast_one] at hsplitP
          exact hsplitP
        set Cme : ℝ := Cm * (q:ℝ)^(ε/2) with hCmedef
        have hCme1 : 1 ≤ Cme := by
          have hqn : (1:ℝ) ≤ (q:ℝ)^(ε/2) := Real.one_le_rpow hq1 (by linarith only [hε])
          rw [hCmedef]
          have : (1:ℝ) * 1 ≤ Cm * (q:ℝ)^(ε/2) := mul_le_mul hCm1 hqn zero_le_one hCmpos.le
          simpa using this
        have hcore := burgess_core_gen Cme hCme1 k hk2 hk3 hq60 χ hχne
          (fun L hL => by rw [hCmedef]; exact hCmC q χ hχprim hχne L hL) N' hN'0 hN'q H hH1 hHq hHlo hHhi CL hCL0 hsplit'
        have hmod : cSum χ (N:ℤ) ((N:ℤ) + (H:ℤ)) = cSum χ N' (N' + (H:ℤ)) := by
          have hN : (N:ℤ) = N' + (q:ℤ) * ((N / q : ℕ) : ℤ) := by
            rw [hNdef]
            have h := Nat.mod_add_div N q
            exact_mod_cast h.symm
          rw [hN]
          have key := cSum_add_q_mul χ N' (N' + (H:ℤ)) (N/q)
          rw [show N' + (q:ℤ) * ((N / q : ℕ) : ℤ) + (H:ℤ)
              = N' + (H:ℤ) + (q:ℤ) * ((N / q : ℕ) : ℤ) by ring]
          exact key
        -- CL ≤ 600 log q
        have hPle : ((Nat.floor A + 1 : ℕ) : ℝ) ≤ 2*(q:ℝ) := by
          have hA1 : A ≤ (H:ℝ) := by
            rw [hAdef]
            calc (H:ℝ) * (q:ℝ)^(-(1/(2*(k:ℝ)))) ≤ (H:ℝ) * 1 := by
                  apply mul_le_mul_of_nonneg_left _ hHnn
                  rw [Real.rpow_neg hq0.le]
                  exact inv_le_one_of_one_le₀ (Real.one_le_rpow hq1 (by positivity))
              _ = (H:ℝ) := mul_one _
          have hfl : ((Nat.floor A : ℕ) : ℝ) ≤ A := Nat.floor_le hA_nn
          push_cast
          linarith only [hHqR, hq512R, hA1, hfl]
        have hlog_bound : Real.log (2 * ((Nat.floor A + 1 : ℕ) : ℝ)) ≤ 2 * Real.log q := by
          have h1 : Real.log (2 * ((Nat.floor A + 1 : ℕ) : ℝ)) ≤ Real.log (2*(2*(q:ℝ))) :=
            Real.log_le_log (by positivity) (by linarith only [hPle])
          have h2 : Real.log (2*(2*(q:ℝ))) = Real.log 4 + Real.log q := by
            rw [show (2:ℝ)*(2*(q:ℝ)) = 4 * (q:ℝ) by ring,
              Real.log_mul (by norm_num) (ne_of_gt hq0)]
          have h3 : Real.log 4 ≤ Real.log q := by
            have h4' : Real.log 4 = 2 * Real.log 2 := by
              rw [show (4:ℝ) = 2^2 by norm_num, Real.log_pow]; norm_num
            have h5' : 2 * Real.log 2 ≤ 20 := by linarith only [Real.log_two_lt_d9]
            linarith only [hL20, h4', h5']
          linarith only [h1, h2, h3]
        have hCLle : CL ≤ 600 * Real.log q := by rw [hCLdef]; linarith only [hlog_bound]
        have hLqnn : (0:ℝ) ≤ Real.log q := hqlog.le
        have hPw : (Real.log q)^(10*k+20) * Real.log q = (Real.log q)^(10*k+21) := by
          rw [← pow_succ]
        have hlogabs : (Real.log q)^(10*k+21) ≤ C1 * (q:ℝ)^(ε/2) := hC1 q hq1
        have hstep1 : 2^70 * CL * Cme * (q:ℝ)^((k+1)/(4*k^2:ℝ)) * (H:ℝ)^(1-1/(k:ℝ))
              * (Real.log q)^(10*k+20)
            ≤ 2^70 * 600 * Cme * (q:ℝ)^((k+1)/(4*k^2:ℝ)) * (H:ℝ)^(1-1/(k:ℝ))
              * (Real.log q)^(10*k+21) := by
          have hZ : (0:ℝ) ≤ 2^70 * Cme * (q:ℝ)^((k+1)/(4*k^2:ℝ)) * (H:ℝ)^(1-1/(k:ℝ))
              * (Real.log q)^(10*k+20) := by positivity
          have h := mul_le_mul_of_nonneg_right hCLle hZ
          have e2 : (600 * Real.log q) * (2^70 * Cme * (q:ℝ)^((k+1)/(4*k^2:ℝ))
                * (H:ℝ)^(1-1/(k:ℝ)) * (Real.log q)^(10*k+20))
              = 2^70 * 600 * Cme * (q:ℝ)^((k+1)/(4*k^2:ℝ)) * (H:ℝ)^(1-1/(k:ℝ))
                * (Real.log q)^(10*k+21) := by
            rw [show (600:ℝ) * Real.log q * (2^70 * Cme * (q:ℝ)^((k+1)/(4*k^2:ℝ))
                  * (H:ℝ)^(1-1/(k:ℝ)) * (Real.log q)^(10*k+20))
                = 2^70 * 600 * Cme * (q:ℝ)^((k+1)/(4*k^2:ℝ)) * (H:ℝ)^(1-1/(k:ℝ))
                  * ((Real.log q)^(10*k+20) * Real.log q) from by ring]
            rw [hPw]
          have e1 : CL * (2^70 * Cme * (q:ℝ)^((k+1)/(4*k^2:ℝ)) * (H:ℝ)^(1-1/(k:ℝ))
                * (Real.log q)^(10*k+20))
              = 2^70 * CL * Cme * (q:ℝ)^((k+1)/(4*k^2:ℝ)) * (H:ℝ)^(1-1/(k:ℝ))
                * (Real.log q)^(10*k+20) := by ring
          linarith only [h, e2.le, e1.le, e2]
        have hstep2 : 2^70 * 600 * Cme * (q:ℝ)^((k+1)/(4*k^2:ℝ)) * (H:ℝ)^(1-1/(k:ℝ))
              * (Real.log q)^(10*k+21)
            ≤ 2^70 * 600 * Cme * C1 * (q:ℝ)^((k+1)/(4*k^2:ℝ) + ε/2) * (H:ℝ)^(1-1/(k:ℝ)) := by
          have h1 : 2^70 * 600 * Cme * (q:ℝ)^((k+1)/(4*k^2:ℝ)) * (H:ℝ)^(1-1/(k:ℝ))
                * (Real.log q)^(10*k+21)
              ≤ 2^70 * 600 * Cme * (q:ℝ)^((k+1)/(4*k^2:ℝ)) * (H:ℝ)^(1-1/(k:ℝ))
                * (C1 * (q:ℝ)^(ε/2)) :=
            mul_le_mul_of_nonneg_left hlogabs (by positivity)
          have e : 2^70 * 600 * Cme * (q:ℝ)^((k+1)/(4*k^2:ℝ)) * (H:ℝ)^(1-1/(k:ℝ))
                * (C1 * (q:ℝ)^(ε/2))
              = 2^70 * 600 * Cme * C1 * (q:ℝ)^((k+1)/(4*k^2:ℝ) + ε/2)
                * (H:ℝ)^(1-1/(k:ℝ)) := by
            rw [show 2^70 * 600 * Cme * (q:ℝ)^((k+1)/(4*k^2:ℝ)) * (H:ℝ)^(1-1/(k:ℝ))
                  * (C1 * (q:ℝ)^(ε/2))
                = (2^70 * 600 * Cme * C1) * ((q:ℝ)^((k+1)/(4*k^2:ℝ)) * (q:ℝ)^(ε/2))
                  * (H:ℝ)^(1-1/(k:ℝ)) from by ring,
              ← Real.rpow_add hq0]
          linarith only [h1, e.ge, e]
        have hstep3 : 2^70 * 600 * Cme * C1 * (q:ℝ)^((k+1)/(4*k^2:ℝ) + ε/2) * (H:ℝ)^(1-1/(k:ℝ))
            ≤ (2^512 + 2^70 * 600 * Cm * C1 + 2 * Ccs + 1) * (q:ℝ)^((k+1)/(4*k^2:ℝ) + ε)
              * (H:ℝ)^(1-1/(k:ℝ)) := by
          have h4 : (2^70 * 600 * Cm * C1) ≤ 2^512 + 2^70 * 600 * Cm * C1 + 2 * Ccs + 1 := by
            have h5 : (0:ℝ) ≤ 2 * Ccs := by linarith only [hCcspos]
            linarith only [h5, h512nn, hCcspos]
          have e : 2^70 * 600 * Cme * C1 * (q:ℝ)^((k+1)/(4*k^2:ℝ) + ε/2) * (H:ℝ)^(1-1/(k:ℝ))
              = 2^70 * 600 * Cm * C1 * (q:ℝ)^((k+1)/(4*k^2:ℝ) + ε) * (H:ℝ)^(1-1/(k:ℝ)) := by
            rw [hCmedef]
            rw [show 2^70 * 600 * (Cm * (q:ℝ)^(ε/2)) * C1 * (q:ℝ)^((k+1)/(4*k^2:ℝ) + ε/2)
                  * (H:ℝ)^(1-1/(k:ℝ))
                = 2^70 * 600 * Cm * C1 * ((q:ℝ)^(ε/2) * (q:ℝ)^((k+1)/(4*k^2:ℝ) + ε/2))
                  * (H:ℝ)^(1-1/(k:ℝ)) from by ring]
            rw [← Real.rpow_add hq0]
            rw [show ε/2 + ((k+1)/(4*k^2:ℝ) + ε/2) = (k+1)/(4*k^2:ℝ) + ε by ring]
          rw [e]
          apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hHnn _)
          exact mul_le_mul_of_nonneg_right h4 (by positivity)
        calc ‖∑ n ∈ Finset.Ioc N (N + H), χ (n : ZMod q)‖
            = ‖cSum χ (N:ℤ) ((N:ℤ) + (H:ℤ))‖ := by rw [cSum_natCast]
          _ = ‖cSum χ N' (N' + (H:ℤ))‖ := by rw [hmod]
          _ ≤ 2^70 * CL * Cme * (q:ℝ)^((k+1)/(4*k^2:ℝ)) * (H:ℝ)^(1-1/(k:ℝ))
                * (Real.log q)^(10*k+20) := hcore
          _ ≤ (2^512 + 2^70 * 600 * Cm * C1 + 2 * Ccs + 1)
                * (q:ℝ)^((k+1)/(4*k^2:ℝ) + ε) * (H:ℝ)^(1-1/(k:ℝ)) :=
              le_trans hstep1 (le_trans hstep2 hstep3)

end Commons.NumberTheory.DirichletCharacter
