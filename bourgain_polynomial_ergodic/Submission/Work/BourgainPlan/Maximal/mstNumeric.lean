import Mathlib
import Submission.Work.BourgainPlan.Maximal.level_l2_mst_large_n_aux_defs
import Submission.Work.BourgainPlan.Maximal.mstU_card_le_exp

namespace Work.BourgainPlan.Maximal

open MeasureTheory Finset
open scoped BigOperators ENNReal

noncomputable section

/-! ## Elementary real-arithmetic helpers -/

private lemma four_eq_two_rpow_two : (4 : ℝ) = (2 : ℝ) ^ ((2 : ℕ) : ℝ) := by
  rw [Real.rpow_natCast]
  norm_num

/-- If `E ≥ 0`, `c ≥ 0` and `q, c ≤ 2^{E/3}` then `2^{-E}·q·c ≤ 1`. -/
private lemma rpow_neg_mul_le_one {E q c : ℝ} (hE : 0 ≤ E) (hc0 : 0 ≤ c)
    (hq : q ≤ (2 : ℝ) ^ (E / 3)) (hc : c ≤ (2 : ℝ) ^ (E / 3)) :
    (2 : ℝ) ^ (-E) * q * c ≤ 1 := by
  have h2 : (0 : ℝ) < 2 := by norm_num
  have hpos : 0 ≤ (2 : ℝ) ^ (E / 3) := Real.rpow_nonneg h2.le _
  calc (2 : ℝ) ^ (-E) * q * c = (2 : ℝ) ^ (-E) * (q * c) := by ring
    _ ≤ (2 : ℝ) ^ (-E) * ((2 : ℝ) ^ (E / 3) * (2 : ℝ) ^ (E / 3)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul hq hc hc0 hpos) (Real.rpow_nonneg h2.le _)
    _ = (2 : ℝ) ^ (-E) * (2 : ℝ) ^ (E / 3 + E / 3) := by rw [Real.rpow_add h2]
    _ = (2 : ℝ) ^ (-E + (E / 3 + E / 3)) := by rw [← Real.rpow_add h2]
    _ ≤ (2 : ℝ) ^ (0 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
    _ = 1 := Real.rpow_zero 2

/-- `e ^ 2 ≤ 16`. -/
private lemma exp_two_le_sixteen : Real.exp 2 ≤ 16 := by
  have h : Real.exp 2 = (Real.exp 1) ^ 2 := by
    rw [show (2 : ℝ) = 1 + 1 by norm_num, Real.exp_add, sq]
  rw [h]
  nlinarith [Real.exp_one_lt_three, Real.exp_pos 1]

/-- `16 = 2^4` as a real power. -/
private lemma sixteen_eq_two_rpow : (16 : ℝ) = (2 : ℝ) ^ (4 : ℝ) := by
  rw [show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  norm_num

/-- For every `C > 0` there is `s₀` with `C ≤ exp ((s+1)^{1/10})` for all `s ≥ s₀`. -/
private lemma exists_thr_exp_rpow (C : ℝ) (hC : 0 < C) :
    ∃ s₀ : ℕ, ∀ s : ℕ, s₀ ≤ s → C ≤ Real.exp (((s : ℝ) + 1) ^ (1 / 10 : ℝ)) := by
  set M : ℝ := max 1 (Real.log C) with hM
  have hM0 : 0 ≤ M := le_trans (by norm_num) (le_max_left _ _)
  have hMlog : Real.log C ≤ M := le_max_right _ _
  obtain ⟨s₀, hs₀⟩ := exists_nat_gt (M ^ 10)
  refine ⟨s₀, fun s hs => ?_⟩
  have hpow : M ≤ ((s : ℝ) + 1) ^ (1 / 10 : ℝ) := by
    have hs1 : (s₀ : ℝ) ≤ (s : ℝ) := by exact_mod_cast hs
    have hgear : (M ^ 10 : ℝ) ≤ (s : ℝ) + 1 := by
      have hlt : (M ^ 10 : ℝ) < (s₀ : ℝ) := hs₀
      linarith
    have h1 : ((M ^ 10 : ℝ)) ^ (1 / 10 : ℝ) ≤ ((s : ℝ) + 1) ^ (1 / 10 : ℝ) :=
      Real.rpow_le_rpow (pow_nonneg hM0 10) hgear (by norm_num)
    have h2 : ((M ^ 10 : ℝ)) ^ (1 / 10 : ℝ) = M := by
      rw [← Real.rpow_natCast M 10, ← Real.rpow_mul hM0,
        show (((10 : ℕ) : ℝ)) * (1 / 10 : ℝ) = 1 by norm_num, Real.rpow_one]
    linarith [h1, h2]
  calc C = Real.exp (Real.log C) := (Real.exp_log hC).symm
    _ ≤ Real.exp M := Real.exp_le_exp.mpr hMlog
    _ ≤ Real.exp (((s : ℝ) + 1) ^ (1 / 10 : ℝ)) := Real.exp_le_exp.mpr hpow

/-- `Q_s = (⌈e^{(s+1)^{1/10}}⌉)!` is at most `2^{2^{5(⌊(s+1)^{1/10}⌋+1)}}`. -/
private lemma mstQ_le_two_pow_local (s : ℕ) :
    (mstQ' s : ℝ)
      ≤ (2 : ℝ) ^ (((2 : ℕ) ^ (5 * (⌊((s : ℝ) + 1) ^ (1 / 10 : ℝ)⌋₊ + 1)) : ℕ) : ℝ) := by
  set x : ℝ := ((s : ℝ) + 1) ^ (1 / 10 : ℝ) with hx
  set K : ℕ := ⌊x⌋₊ with hK
  set n : ℕ := ⌈Real.exp x⌉₊ with hn
  have hx0 : 0 ≤ x := by rw [hx]; exact Real.rpow_nonneg (by positivity) _
  have hx1 : 1 ≤ x := by
    rw [hx]; exact Real.one_le_rpow (by simp) (by norm_num)
  have hK1 : 1 ≤ K := by
    rw [hK]
    have h := Nat.floor_pos.mpr hx1
    omega
  have hK2 : 2 ≤ K + 1 := by omega
  have hxK : x ≤ (K : ℝ) + 1 := by rw [hK]; exact le_of_lt (Nat.lt_floor_add_one x)
  have hn_le : (n : ℝ) ≤ 2 * Real.exp x := by
    have h1 : (n : ℝ) < Real.exp x + 1 := by
      rw [hn]; exact Nat.ceil_lt_add_one (Real.exp_nonneg x)
    have h2 : 1 ≤ Real.exp x := Real.one_le_exp hx0
    linarith
  have hsqu : (Real.exp x) ^ 2 = (Real.exp 2) ^ x := by
    rw [sq, ← Real.exp_add, show x + x = 2 * x by ring, Real.exp_mul]
  have h16 : (16 : ℝ) ^ x = (2 : ℝ) ^ (4 * x) := by
    rw [sixteen_eq_two_rpow, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
  have hN : (((2 : ℕ) ^ (5 * (K + 1)) : ℕ) : ℝ) = (2 : ℝ) ^ (5 * ((K : ℝ) + 1)) := by
    push_cast
    rw [← Real.rpow_natCast]
    congr 1
    push_cast
    ring
  have hsq : (n : ℝ) * (n : ℝ) ≤ (2 : ℝ) ^ (5 * ((K : ℝ) + 1)) := by
    have h3 : (n : ℝ) ^ 2 ≤ (2 * Real.exp x) ^ 2 := by
      have : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
      nlinarith [hn_le]
    calc (n : ℝ) * (n : ℝ) = (n : ℝ) ^ 2 := by ring
      _ ≤ (2 * Real.exp x) ^ 2 := h3
      _ = 4 * (Real.exp x) ^ 2 := by ring
      _ = 4 * (Real.exp 2) ^ x := by rw [hsqu]
      _ ≤ 4 * (16 : ℝ) ^ x :=
          mul_le_mul_of_nonneg_left
            (Real.rpow_le_rpow (Real.exp_nonneg 2) exp_two_le_sixteen hx0) (by norm_num)
      _ = 4 * (2 : ℝ) ^ (4 * x) := by rw [h16]
      _ = (2 : ℝ) ^ ((2 : ℕ) : ℝ) * (2 : ℝ) ^ (4 * x) := by rw [four_eq_two_rpow_two]
      _ = (2 : ℝ) ^ (((2 : ℕ) : ℝ) + 4 * x) :=
          by rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
      _ ≤ (2 : ℝ) ^ (5 * ((K : ℝ) + 1)) := by
          apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
          have hK2R : (2 : ℝ) ≤ (K : ℝ) + 1 := by exact_mod_cast hK2
          push_cast
          linarith [hxK, hK2R]
  have hn2 : ((n * n : ℕ) : ℝ) ≤ (((2 : ℕ) ^ (5 * (K + 1)) : ℕ) : ℝ) := by
    rw [hN]
    push_cast
    exact hsq
  calc (mstQ' s : ℝ) = ((n.factorial : ℕ) : ℝ) := by rw [mstQ', hn, hx]
    _ ≤ ((n ^ n : ℕ) : ℝ) := by exact_mod_cast Nat.factorial_le_pow n
    _ ≤ ((2 ^ (n * n) : ℕ) : ℝ) := by
        have h : n ^ n ≤ 2 ^ (n * n) := by
          calc n ^ n ≤ (2 ^ n) ^ n := Nat.pow_le_pow_left (le_of_lt Nat.lt_two_pow_self) n
            _ = 2 ^ (n * n) := by rw [pow_mul]
        exact_mod_cast h
    _ = (2 : ℝ) ^ ((n * n : ℕ) : ℝ) := by
        rw [Nat.cast_pow, Nat.cast_ofNat, Real.rpow_natCast]
    _ ≤ (2 : ℝ) ^ ((((2 : ℕ) ^ (5 * (K + 1)) : ℕ)) : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) hn2

/-- `#𝒰((s+1)^l)`, and hence `#mstLvl l s`, is at most `2^{2^{5(⌊(s+1)^{1/10}⌋+1)}}` as soon as the
level-set constant `C` is below `e^{(s+1)^{1/10}}`. -/
private lemma mstLvl_card_le_two_pow_local (l s : ℕ) (hl : 1 ≤ l) {C : ℝ} (_hCpos : 0 < C)
    (hC : ∀ n : ℕ, ((mstU l n).card : ℝ) ≤ C * Real.exp (((n : ℝ) ^ l) ^ (mstRho l)))
    (hthr : C ≤ Real.exp (((s : ℝ) + 1) ^ (1 / 10 : ℝ))) :
    ((mstLvl l s).card : ℝ)
      ≤ (2 : ℝ) ^ (((2 : ℕ) ^ (5 * (⌊((s : ℝ) + 1) ^ (1 / 10 : ℝ)⌋₊ + 1)) : ℕ) : ℝ) := by
  set x : ℝ := ((s : ℝ) + 1) ^ (1 / 10 : ℝ) with hx
  set K : ℕ := ⌊x⌋₊ with hK
  have hx0 : 0 ≤ x := by rw [hx]; exact Real.rpow_nonneg (by positivity) _
  have hx1 : 1 ≤ x := by rw [hx]; exact Real.one_le_rpow (by simp) (by norm_num)
  have hK1 : 1 ≤ K := by
    rw [hK]
    have h := Nat.floor_pos.mpr hx1
    omega
  have hK2 : 2 ≤ K + 1 := by omega
  have hxK : x ≤ (K : ℝ) + 1 := by rw [hK]; exact le_of_lt (Nat.lt_floor_add_one x)
  have hN : (((2 : ℕ) ^ (5 * (K + 1)) : ℕ) : ℝ) = (2 : ℝ) ^ (5 * ((K : ℝ) + 1)) := by
    push_cast
    rw [← Real.rpow_natCast]
    congr 1
    push_cast
    ring
  -- the level-`(s+1)` exponent is exactly `x`
  have h3 : ((((s + 1 : ℕ) : ℝ) ^ l) ^ (mstRho l)) = x := by
    rw [hx]
    have hlne : ((l : ℕ) : ℝ) ≠ 0 := by
      have h : (1 : ℝ) ≤ (l : ℝ) := by exact_mod_cast hl
      linarith
    push_cast
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity : (0 : ℝ) ≤ (s : ℝ) + 1), mstRho]
    congr 1
    field_simp
  have h1 : ((mstLvl l s).card : ℝ) ≤ ((mstU l (s + 1)).card : ℝ) := by
    rw [mstLvl]
    exact_mod_cast Finset.card_le_card (Finset.sdiff_subset (s := mstU l (s + 1)) (t := mstU l s))
  have h2 : ((mstU l (s + 1)).card : ℝ)
      ≤ C * Real.exp ((((s + 1 : ℕ) : ℝ) ^ l) ^ (mstRho l)) := hC (s + 1)
  have h4 : C * Real.exp x ≤ Real.exp (2 * x) := by
    have h5 : Real.exp x * Real.exp x = Real.exp (2 * x) := by
      rw [← Real.exp_add, show x + x = 2 * x by ring]
    rw [← h5]
    exact mul_le_mul_of_nonneg_right hthr (Real.exp_nonneg x)
  have h6 : Real.exp (2 * x) ≤ (2 : ℝ) ^ (4 * x) := by
    have h16' : (16 : ℝ) ^ x = (2 : ℝ) ^ (4 * x) := by
      rw [sixteen_eq_two_rpow, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
    calc Real.exp (2 * x) = (Real.exp 2) ^ x := Real.exp_mul 2 x
      _ ≤ (16 : ℝ) ^ x := Real.rpow_le_rpow (Real.exp_nonneg 2) exp_two_le_sixteen hx0
      _ = (2 : ℝ) ^ (4 * x) := h16'
  have h7 : (2 : ℝ) ^ (4 * x) ≤ (2 : ℝ) ^ (5 * ((K : ℝ) + 1)) := by
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    have hK2R : (2 : ℝ) ≤ (K : ℝ) + 1 := by exact_mod_cast hK2
    linarith [hxK, hK2R]
  have h8 : (2 : ℝ) ^ (5 * ((K : ℝ) + 1))
      ≤ (2 : ℝ) ^ (((2 : ℕ) ^ (5 * (K + 1)) : ℕ) : ℝ) := by
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    calc 5 * ((K : ℝ) + 1) = ((5 * (K + 1) : ℕ) : ℝ) := by push_cast; ring
      _ ≤ (((2 : ℕ) ^ (5 * (K + 1)) : ℕ) : ℝ) := by
          exact_mod_cast (le_of_lt (Nat.lt_two_pow_self (n := 5 * (K + 1))))
  calc ((mstLvl l s).card : ℝ) ≤ ((mstU l (s + 1)).card : ℝ) := h1
    _ ≤ C * Real.exp ((((s + 1 : ℕ) : ℝ) ^ l) ^ (mstRho l)) := h2
    _ = C * Real.exp x := by rw [h3]
    _ ≤ Real.exp (2 * x) := h4
    _ ≤ (2 : ℝ) ^ (4 * x) := h6
    _ ≤ (2 : ℝ) ^ (5 * ((K : ℝ) + 1)) := h7
    _ ≤ (2 : ℝ) ^ (((2 : ℕ) ^ (5 * (K + 1)) : ℕ) : ℝ) := h8

/-- `2^{5(⌊(s+1)^{1/10}⌋+1)} ≤ 2^{κ_s}/3` with `2^{κ_s} = mstN₀' P s`. -/
private lemma mstNexp_le_third (P : Polynomial ℤ) (hd : 2 ≤ P.natDegree) (s : ℕ) :
    (((2 : ℕ) ^ (5 * (⌊((s : ℝ) + 1) ^ (1 / 10 : ℝ)⌋₊ + 1)) : ℕ) : ℝ)
      ≤ ((mstN₀' P s : ℝ) / (P.natDegree : ℝ)) / 3 := by
  rw [mstN₀']
  set K : ℕ := ⌊((s : ℝ) + 1) ^ (1 / 10 : ℝ)⌋₊ with hK
  have hd1 : 1 ≤ P.natDegree := by omega
  have hnat : 2 ^ (5 * (K + 1)) * (3 * P.natDegree) ≤ 2 ^ (20 * P.natDegree * (K + 1)) := by
    have h1 : 3 * P.natDegree ≤ 2 ^ (15 * (P.natDegree * (K + 1))) := by
      have hle : 3 * P.natDegree ≤ 15 * (P.natDegree * (K + 1)) := by nlinarith [hd]
      exact hle.trans (le_of_lt (Nat.lt_two_pow_self (n := 15 * (P.natDegree * (K + 1)))))
    have h2 : 2 ^ (5 * (K + 1)) ≤ 2 ^ (5 * (P.natDegree * (K + 1))) :=
      Nat.pow_le_pow_right (by norm_num) (by nlinarith [hd1])
    calc 2 ^ (5 * (K + 1)) * (3 * P.natDegree)
        = (3 * P.natDegree) * 2 ^ (5 * (K + 1)) := by ring
      _ ≤ 2 ^ (15 * (P.natDegree * (K + 1))) * 2 ^ (5 * (P.natDegree * (K + 1))) :=
          Nat.mul_le_mul h1 h2
      _ = 2 ^ (15 * (P.natDegree * (K + 1)) + 5 * (P.natDegree * (K + 1))) := by rw [pow_add]
      _ = 2 ^ (20 * P.natDegree * (K + 1)) := by
          congr 1
          ring
  have hreal : (((2 : ℕ) ^ (5 * (K + 1)) : ℕ) : ℝ) * (3 * (P.natDegree : ℝ))
      ≤ (((2 : ℕ) ^ (20 * P.natDegree * (K + 1)) : ℕ) : ℝ) := by exact_mod_cast hnat
  have hD : (0 : ℝ) < (P.natDegree : ℝ) * 3 := by
    have : (0 : ℝ) < (P.natDegree : ℝ) := by exact_mod_cast (by omega : 0 < P.natDegree)
    linarith
  rw [div_div, le_div_iff₀ hD]
  have hreal' := hreal
  rw [mul_comm (3 : ℝ) ((P.natDegree : ℝ))] at hreal'
  exact hreal'

end

theorem mstNumeric (P : Polynomial ℤ) (hd : 2 ≤ P.natDegree) (l : ℕ) (hl : 1 ≤ l) :
    ∃ s₀ : ℕ, ∀ s : ℕ, s₀ ≤ s →
      (2 : ℝ) ^ (-((Work.BourgainPlan.Maximal.mstN₀' P s : ℝ) / (P.natDegree : ℝ))) * (Work.BourgainPlan.Maximal.mstQ' s : ℝ)
        * ((Work.BourgainPlan.Maximal.mstLvl l s).card : ℝ) ≤ 1 := by
  obtain ⟨C, hCpos, hC⟩ := mstU_card_le_exp l hl
  obtain ⟨s₀, hs₀⟩ := exists_thr_exp_rpow C hCpos
  refine ⟨s₀, fun s hs => ?_⟩
  set E : ℝ := (mstN₀' P s : ℝ) / (P.natDegree : ℝ) with hE
  have hE0 : 0 ≤ E := by
    rw [hE]
    exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  have hNK : (((2 : ℕ) ^ (5 * (⌊((s : ℝ) + 1) ^ (1 / 10 : ℝ)⌋₊ + 1)) : ℕ) : ℝ) ≤ E / 3 := by
    rw [hE]
    exact mstNexp_le_third P hd s
  have hQ : (mstQ' s : ℝ) ≤ (2 : ℝ) ^ (E / 3) :=
    (mstQ_le_two_pow_local s).trans (Real.rpow_le_rpow_of_exponent_le (by norm_num) hNK)
  have hCg : ((mstLvl l s).card : ℝ) ≤ (2 : ℝ) ^ (E / 3) :=
    (mstLvl_card_le_two_pow_local l s hl hCpos hC (hs₀ s hs)).trans
      (Real.rpow_le_rpow_of_exponent_le (by norm_num) hNK)
  exact rpow_neg_mul_le_one hE0 (Nat.cast_nonneg _) hQ hCg

end Work.BourgainPlan.Maximal
