import Mathlib
import Submission.Commons.NumberTheory.DirichletCharacter.LFunction_bound_third_of_burgess
import Submission.Work.LinnikAreas.Density4.LFunction_one_apply_one
import Submission.Work.LinnikAreas.OtherCharRepel.sumPrimeFactorsLogLeLog

open scoped BigOperators

namespace Work.LinnikAreas.GSum

def Lseq (j : ℕ) : ℕ := max 2 (2 * j + 1)

lemma Lseq_pos (j : ℕ) : 0 < Lseq j := by unfold Lseq; omega
lemma Lseq_two_le (j : ℕ) : 2 ≤ Lseq j := by unfold Lseq; omega

lemma primeCounting_two_mul_le (a : ℕ) (ha : a.Prime) : 2 * a.primeCounting ≤ a + 1 := by
  rcases ha.eq_two_or_odd with h | h
  · subst h
    rw [show Nat.primeCounting 2 = 1 from by decide]
    norm_num
  · have h3 : 3 ≤ a := by have := ha.two_le; omega
    have key := Nat.primeCounting_add_le (a := 2) (k := 2) (by norm_num) (le_refl 2) (a - 2)
    have h2 : 2 + (a - 2) = a := by omega
    rw [h2] at key
    rw [show Nat.primeCounting 2 = 1 from by decide,
        show Nat.totient 2 = 1 from by norm_num] at key
    simp only [one_mul] at key
    omega

lemma two_mul_card_le {S : Finset ℕ} (hS : ∀ p ∈ S, p.Prime) {a : ℕ} (ha : a.Prime)
    (hle : ∀ p ∈ S, p ≤ a) : 2 * S.card ≤ a + 1 := by
  have hsub : S ⊆ Nat.primesLE a := fun p hp => Nat.mem_primesLE.mpr ⟨hle p hp, hS p hp⟩
  have h1 : S.card ≤ (Nat.primesLE a).card := Finset.card_le_card hsub
  rw [Nat.primesLE_card_eq_primeCounting] at h1
  have h2 := primeCounting_two_mul_le a ha
  omega

lemma Lseq_card_le {S : Finset ℕ} (hS : ∀ p ∈ S, p.Prime) {a : ℕ} (ha : a.Prime)
    (hle : ∀ p ∈ S, p ≤ a) : Lseq (S.card - 1) ≤ a := by
  have h := two_mul_card_le hS ha hle
  unfold Lseq
  rcases Nat.eq_zero_or_pos S.card with hk | hk
  · rw [hk]; refine max_le ha.two_le ?_; have := ha.two_le; omega
  · apply max_le ha.two_le; omega

lemma sum_inv_sqrt_le_Lseq (S : Finset ℕ) :
    (∀ p ∈ S, p.Prime) →
      ∑ p ∈ S, (p : ℝ) ^ (-(1 / 2 : ℝ)) ≤
        ∑ j ∈ Finset.range S.card, ((Lseq j : ℕ) : ℝ) ^ (-(1 / 2 : ℝ)) := by
  induction S using Finset.induction_on_max with
  | empty => intro _; simp
  | insert a s hs ih =>
    intro hS
    have hsa : a ∉ s := fun h => absurd (hs a h) (lt_irrefl a)
    have hsp : ∀ p ∈ s, p.Prime := fun p hp => hS p (Finset.mem_insert_of_mem hp)
    have hap : a.Prime := hS a (Finset.mem_insert_self a s)
    rw [Finset.sum_insert hsa, Finset.card_insert_of_notMem hsa, Finset.sum_range_succ]
    have hLe : Lseq s.card ≤ a := by
      have h := Lseq_card_le (S := insert a s) hS hap (fun p hp => by
        rcases Finset.mem_insert.mp hp with rfl | h
        · exact le_rfl
        · exact le_of_lt (hs p h))
      simpa [Finset.card_insert_of_notMem hsa] using h
    have hterm : (a : ℝ) ^ (-(1 / 2 : ℝ)) ≤ ((Lseq s.card : ℕ) : ℝ) ^ (-(1 / 2 : ℝ)) :=
      Real.rpow_le_rpow_of_nonpos (by exact_mod_cast Lseq_pos s.card)
        (by exact_mod_cast hLe) (by norm_num)
    linarith [ih hsp]

lemma sum_log_Lseq_le (S : Finset ℕ) :
    (∀ p ∈ S, p.Prime) →
      ∑ j ∈ Finset.range S.card, Real.log ((Lseq j : ℕ) : ℝ) ≤ ∑ p ∈ S, Real.log (p : ℝ) := by
  induction S using Finset.induction_on_max with
  | empty => intro _; simp
  | insert a s hs ih =>
    intro hS
    have hsa : a ∉ s := fun h => absurd (hs a h) (lt_irrefl a)
    have hsp : ∀ p ∈ s, p.Prime := fun p hp => hS p (Finset.mem_insert_of_mem hp)
    have hap : a.Prime := hS a (Finset.mem_insert_self a s)
    rw [Finset.sum_insert hsa, Finset.card_insert_of_notMem hsa, Finset.sum_range_succ]
    have hLe : Lseq s.card ≤ a := by
      have h := Lseq_card_le (S := insert a s) hS hap (fun p hp => by
        rcases Finset.mem_insert.mp hp with rfl | h
        · exact le_rfl
        · exact le_of_lt (hs p h))
      simpa [Finset.card_insert_of_notMem hsa] using h
    have hterm : Real.log ((Lseq s.card : ℕ) : ℝ) ≤ Real.log (a : ℝ) :=
      Real.log_le_log (by exact_mod_cast Lseq_pos s.card) (by exact_mod_cast hLe)
    linarith [ih hsp]

noncomputable def Fl (k : ℕ) : ℝ := ∑ j ∈ Finset.range k, ((Lseq j : ℕ) : ℝ) ^ (-(1 / 2 : ℝ))
noncomputable def Gl (k : ℕ) : ℝ := ∑ j ∈ Finset.range k, Real.log ((Lseq j : ℕ) : ℝ)

lemma Fl_nonneg (k : ℕ) : 0 ≤ Fl k := by
  unfold Fl
  exact Finset.sum_nonneg (fun j _ => Real.rpow_nonneg (by positivity) _)

lemma rpow_neg_half_le {p : ℕ} {c : ℝ} (hc : 0 < c) (hp : 0 < p) (h : 1 ≤ c ^ 2 * p) :
    ((p : ℝ)) ^ (-(1 / 2 : ℝ)) ≤ c := by
  have hppos : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp
  have hsq : 0 < Real.sqrt (p : ℝ) := Real.sqrt_pos.mpr hppos
  have h2 : (c * Real.sqrt (p : ℝ)) ^ 2 = c ^ 2 * (p : ℝ) := by
    rw [mul_pow, Real.sq_sqrt hppos.le]
  have h3 : 1 ≤ c * Real.sqrt (p : ℝ) := by nlinarith [h, h2, mul_nonneg hc.le hsq.le]
  rw [Real.rpow_neg hppos.le, ← Real.sqrt_eq_rpow]
  calc (Real.sqrt (p : ℝ))⁻¹ = 1 * (Real.sqrt (p : ℝ))⁻¹ := (one_mul _).symm
    _ ≤ (c * Real.sqrt (p : ℝ)) * (Real.sqrt (p : ℝ))⁻¹ :=
        mul_le_mul_of_nonneg_right h3 (inv_nonneg.mpr hsq.le)
    _ = c := by field_simp

lemma log_two_ge : (0.6931 : ℝ) ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
lemma log_three_ge : (1 : ℝ) ≤ Real.log 3 :=
  (Real.le_log_iff_exp_le (by norm_num)).mpr (le_of_lt Real.exp_one_lt_three)
lemma log_five_ge : 2 * Real.log 2 ≤ Real.log 5 := by
  have h := Real.log_le_log (by norm_num : (0 : ℝ) < 4) (by norm_num : (4 : ℝ) ≤ 5)
  rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow] at h
  simpa using h
lemma log_seven_ge : Real.log 2 + Real.log 3 ≤ Real.log 7 := by
  have h := Real.log_le_log (by norm_num : (0 : ℝ) < 6) (by norm_num : (6 : ℝ) ≤ 7)
  rw [show (6 : ℝ) = 2 * 3 by norm_num, Real.log_mul (by norm_num) (by norm_num)] at h
  simpa using h
lemma log_nine_ge : (2 : ℝ) ≤ Real.log 9 := by
  have h9 : Real.log 9 = 2 * Real.log 3 := by
    rw [show (9 : ℝ) = 3 ^ 2 by norm_num, Real.log_pow]; norm_num
  have := log_three_ge
  rw [h9]; linarith
lemma Lseq_zero : Lseq 0 = 2 := by decide
lemma Lseq_one : Lseq 1 = 3 := by decide
lemma Lseq_two : Lseq 2 = 5 := by decide
lemma Lseq_three : Lseq 3 = 7 := by decide
lemma Lseq_four : Lseq 4 = 9 := by decide

lemma c2 : (442 / 625 : ℝ) ^ 2 * 2 ≥ 1 := by norm_num
lemma c3 : (5774 / 10000 : ℝ) ^ 2 * 3 ≥ 1 := by norm_num
lemma c5 : (4473 / 10000 : ℝ) ^ 2 * 5 ≥ 1 := by norm_num
lemma c7 : (378 / 1000 : ℝ) ^ 2 * 7 ≥ 1 := by norm_num
lemma c9 : (3334 / 10000 : ℝ) ^ 2 * 9 ≥ 1 := by norm_num

lemma Fl_one : Fl 1 ≤ 442 / 625 := by
  unfold Fl
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Lseq_zero]
  norm_num1
  have h := rpow_neg_half_le (p := 2) (c := (442 / 625 : ℝ))
    (by norm_num) (by norm_num) c2
  linarith

lemma Fl_two : Fl 2 ≤ 12846 / 10000 := by
  unfold Fl
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Lseq_zero, Lseq_one]
  norm_num1
  have h1 := rpow_neg_half_le (p := 2) (c := (442 / 625 : ℝ)) (by norm_num) (by norm_num) c2
  have h2 := rpow_neg_half_le (p := 3) (c := (5774 / 10000 : ℝ)) (by norm_num) (by norm_num) c3
  linarith

lemma Fl_three : Fl 3 ≤ 17319 / 10000 := by
  unfold Fl
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Lseq_zero, Lseq_one, Lseq_two]
  norm_num1
  have h1 := rpow_neg_half_le (p := 2) (c := (442 / 625 : ℝ)) (by norm_num) (by norm_num) c2
  have h2 := rpow_neg_half_le (p := 3) (c := (5774 / 10000 : ℝ)) (by norm_num) (by norm_num) c3
  have h3 := rpow_neg_half_le (p := 5) (c := (4473 / 10000 : ℝ)) (by norm_num) (by norm_num) c5
  linarith

lemma Fl_four : Fl 4 ≤ 21099 / 10000 := by
  unfold Fl
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Lseq_zero, Lseq_one, Lseq_two,
    Lseq_three]
  norm_num1
  have h1 := rpow_neg_half_le (p := 2) (c := (442 / 625 : ℝ)) (by norm_num) (by norm_num) c2
  have h2 := rpow_neg_half_le (p := 3) (c := (5774 / 10000 : ℝ)) (by norm_num) (by norm_num) c3
  have h3 := rpow_neg_half_le (p := 5) (c := (4473 / 10000 : ℝ)) (by norm_num) (by norm_num) c5
  have h4 := rpow_neg_half_le (p := 7) (c := (378 / 1000 : ℝ)) (by norm_num) (by norm_num) c7
  linarith

lemma Fl_five : Fl 5 ≤ 49 / 20 := by
  unfold Fl
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Lseq_zero, Lseq_one, Lseq_two,
    Lseq_three, Lseq_four]
  norm_num1
  have h1 := rpow_neg_half_le (p := 2) (c := (442 / 625 : ℝ)) (by norm_num) (by norm_num) c2
  have h2 := rpow_neg_half_le (p := 3) (c := (5774 / 10000 : ℝ)) (by norm_num) (by norm_num) c3
  have h3 := rpow_neg_half_le (p := 5) (c := (4473 / 10000 : ℝ)) (by norm_num) (by norm_num) c5
  have h4 := rpow_neg_half_le (p := 7) (c := (378 / 1000 : ℝ)) (by norm_num) (by norm_num) c7
  have h5 := rpow_neg_half_le (p := 9) (c := (3334 / 10000 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num)
  linarith

lemma Gl_one : 6931 / 10000 ≤ Gl 1 := by
  unfold Gl
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Lseq_zero]
  norm_num1
  have h1 : (0.6931 : ℝ) ≤ Real.log 2 := log_two_ge
  linarith

lemma Gl_two : 16931 / 10000 ≤ Gl 2 := by
  unfold Gl
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Lseq_zero, Lseq_one]
  norm_num1
  have h1 : (0.6931 : ℝ) ≤ Real.log 2 := log_two_ge
  have h2 : (1 : ℝ) ≤ Real.log 3 := log_three_ge
  linarith

lemma Gl_three : 30793 / 10000 ≤ Gl 3 := by
  unfold Gl
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Lseq_zero, Lseq_one, Lseq_two]
  norm_num1
  have h1 : (0.6931 : ℝ) ≤ Real.log 2 := log_two_ge
  have h2 : (1 : ℝ) ≤ Real.log 3 := log_three_ge
  have h3 : 2 * Real.log 2 ≤ Real.log 5 := log_five_ge
  linarith

lemma Gl_four : 47724 / 10000 ≤ Gl 4 := by
  unfold Gl
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Lseq_zero, Lseq_one, Lseq_two,
    Lseq_three]
  norm_num1
  have h1 : (0.6931 : ℝ) ≤ Real.log 2 := log_two_ge
  have h2 : (1 : ℝ) ≤ Real.log 3 := log_three_ge
  have h3 : 2 * Real.log 2 ≤ Real.log 5 := log_five_ge
  have h4 : Real.log 2 + Real.log 3 ≤ Real.log 7 := log_seven_ge
  linarith

lemma Gl_five : 67724 / 10000 ≤ Gl 5 := by
  unfold Gl
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Lseq_zero, Lseq_one, Lseq_two,
    Lseq_three, Lseq_four]
  norm_num1
  have h1 : (0.6931 : ℝ) ≤ Real.log 2 := log_two_ge
  have h2 : (1 : ℝ) ≤ Real.log 3 := log_three_ge
  have h3 : 2 * Real.log 2 ≤ Real.log 5 := log_five_ge
  have h4 : Real.log 2 + Real.log 3 ≤ Real.log 7 := log_seven_ge
  have h5 : (2 : ℝ) ≤ Real.log 9 := log_nine_ge
  linarith

lemma seq_one : (Fl 1) ^ 2 ≤ Gl 1 := by
  have h1 : (Fl 1) ^ 2 ≤ (442 / 625 : ℝ) ^ 2 := pow_le_pow_left₀ (Fl_nonneg 1) Fl_one 2
  have h2 : (442 / 625 : ℝ) ^ 2 ≤ (6931 / 10000 : ℝ) := by norm_num
  linarith [Gl_one]

lemma seq_two : (Fl 2) ^ 2 ≤ Gl 2 := by
  have h1 : (Fl 2) ^ 2 ≤ (12846 / 10000 : ℝ) ^ 2 := pow_le_pow_left₀ (Fl_nonneg 2) Fl_two 2
  have h2 : (12846 / 10000 : ℝ) ^ 2 ≤ (16931 / 10000 : ℝ) := by norm_num
  linarith [Gl_two]

lemma seq_three : (Fl 3) ^ 2 ≤ Gl 3 := by
  have h1 : (Fl 3) ^ 2 ≤ (17319 / 10000 : ℝ) ^ 2 := pow_le_pow_left₀ (Fl_nonneg 3) Fl_three 2
  have h2 : (17319 / 10000 : ℝ) ^ 2 ≤ (30793 / 10000 : ℝ) := by norm_num
  linarith [Gl_three]

lemma seq_four : (Fl 4) ^ 2 ≤ Gl 4 := by
  have h1 : (Fl 4) ^ 2 ≤ (21099 / 10000 : ℝ) ^ 2 := pow_le_pow_left₀ (Fl_nonneg 4) Fl_four 2
  have h2 : (21099 / 10000 : ℝ) ^ 2 ≤ (47724 / 10000 : ℝ) := by norm_num
  linarith [Gl_four]

lemma seq_five : (Fl 5) ^ 2 ≤ Gl 5 := by
  have h1 : (Fl 5) ^ 2 ≤ (49 / 20 : ℝ) ^ 2 := pow_le_pow_left₀ (Fl_nonneg 5) Fl_five 2
  have h2 : (49 / 20 : ℝ) ^ 2 ≤ (67724 / 10000 : ℝ) := by norm_num
  linarith [Gl_five]

lemma Lseq_eq (j : ℕ) (hj : 1 ≤ j) : Lseq j = 2 * j + 1 := by
  unfold Lseq
  exact max_eq_right (by omega)

lemma inv_sqrt_le_sqrt_sub {a b : ℝ} (ha : 0 < a) (h : 2 ≤ b - a) :
    1 / Real.sqrt b ≤ Real.sqrt b - Real.sqrt a := by
  have hb : 0 < b := by linarith
  have hsb : 0 < Real.sqrt b := Real.sqrt_pos.mpr hb
  have hle : Real.sqrt a ≤ Real.sqrt b := Real.sqrt_le_sqrt (by linarith)
  have hident : (Real.sqrt b - Real.sqrt a) * (Real.sqrt b + Real.sqrt a) = b - a := by
    have h1 : (Real.sqrt b) ^ 2 = b := Real.sq_sqrt hb.le
    have h2 : (Real.sqrt a) ^ 2 = a := Real.sq_sqrt ha.le
    nlinarith
  have hkey : 1 / Real.sqrt b ≤ (b - a) / (Real.sqrt b + Real.sqrt a) := by
    rw [div_le_div_iff₀ hsb (by positivity)]
    nlinarith [h, hsb, hle]
  calc 1 / Real.sqrt b ≤ (b - a) / (Real.sqrt b + Real.sqrt a) := hkey
    _ = Real.sqrt b - Real.sqrt a := by
        rw [div_eq_iff (by positivity : Real.sqrt b + Real.sqrt a ≠ 0)]
        linarith [hident]

lemma two_sqrt_div_le (k : ℕ) (hk : 1 ≤ k) :
    2 * Real.sqrt (2 * (k : ℝ) - 1) / Real.sqrt (2 * (k : ℝ) + 1) ≤ 2 - 2 / (2 * (k : ℝ) + 1) := by
  have hkR : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have ha : 0 < 2 * (k : ℝ) - 1 := by linarith
  have hb : 0 < 2 * (k : ℝ) + 1 := by linarith
  have hsb : 0 < Real.sqrt (2 * (k : ℝ) + 1) := Real.sqrt_pos.mpr hb
  have hrhs : 0 ≤ 2 - 2 / (2 * (k : ℝ) + 1) := by
    rw [sub_nonneg, div_le_iff₀ hb]; linarith
  rw [div_le_iff₀ hsb]
  have hsq : (2 * Real.sqrt (2 * (k : ℝ) - 1)) ^ 2 ≤
      ((2 - 2 / (2 * (k : ℝ) + 1)) * Real.sqrt (2 * (k : ℝ) + 1)) ^ 2 := by
    rw [mul_pow, mul_pow, Real.sq_sqrt ha.le, Real.sq_sqrt hb.le]
    field_simp
    nlinarith
  have := sq_le_sq.mp hsq
  rw [abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2 * Real.sqrt (2 * (k : ℝ) - 1)),
    abs_of_nonneg (mul_nonneg hrhs hsb.le)] at this
  linarith [this]

lemma Fl_le_sqrt (k : ℕ) (hk : 5 ≤ k) : Fl k ≤ Real.sqrt (2 * (k : ℝ) - 1) := by
  refine Nat.le_induction ?base ?step k hk
  · rw [show (2 * ((5 : ℕ) : ℝ) - 1) = 3 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
    linarith [Fl_five]
  · intro m hm ih
    have hm1 : 1 ≤ m := by omega
    have hmR : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm1
    have hLm : Lseq m = 2 * m + 1 := Lseq_eq m hm1
    have hFl : Fl (m + 1) = Fl m + (((Lseq m : ℕ)) : ℝ) ^ (-(1 / 2 : ℝ)) := by
      unfold Fl
      rw [Finset.sum_range_succ]
    have hcast : (((2 * m + 1 : ℕ)) : ℝ) = 2 * (m : ℝ) + 1 := by push_cast; ring
    have hgoalcast : 2 * ((m + 1 : ℕ) : ℝ) - 1 = 2 * (m : ℝ) + 1 := by push_cast; ring
    rw [hFl, hLm, hcast, hgoalcast]
    have hb : 0 < 2 * (m : ℝ) + 1 := by linarith
    have hpow : (2 * (m : ℝ) + 1) ^ (-(1 / 2 : ℝ)) = 1 / Real.sqrt (2 * (m : ℝ) + 1) := by
      rw [Real.rpow_neg (le_of_lt hb), Real.sqrt_eq_rpow, inv_eq_one_div]
    rw [hpow]
    have hkey := inv_sqrt_le_sqrt_sub (a := 2 * (m : ℝ) - 1) (b := 2 * (m : ℝ) + 1)
      (by linarith) (by linarith)
    linarith

lemma seq_ge_five (k : ℕ) (hk : 5 ≤ k) : (Fl k) ^ 2 ≤ Gl k := by
  refine Nat.le_induction ?base ?step k hk
  · exact seq_five
  · intro m hm ih
    have hm1 : 1 ≤ m := by omega
    have hmR : (5 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
    have hLm : Lseq m = 2 * m + 1 := Lseq_eq m hm1
    have hcast : (((2 * m + 1 : ℕ)) : ℝ) = 2 * (m : ℝ) + 1 := by push_cast; ring
    have hFl : Fl (m + 1) = Fl m + (((Lseq m : ℕ)) : ℝ) ^ (-(1 / 2 : ℝ)) := by
      unfold Fl
      rw [Finset.sum_range_succ]
    have hGl : Gl (m + 1) = Gl m + Real.log (((Lseq m : ℕ)) : ℝ) := by
      unfold Gl
      rw [Finset.sum_range_succ]
    rw [hFl, hGl, hLm, hcast]
    have hb : 0 < 2 * (m : ℝ) + 1 := by linarith
    have ha : 0 < 2 * (m : ℝ) - 1 := by linarith
    have ht : (2 * (m : ℝ) + 1) ^ (-(1 / 2 : ℝ)) = 1 / Real.sqrt (2 * (m : ℝ) + 1) := by
      rw [Real.rpow_neg (le_of_lt hb), Real.sqrt_eq_rpow, inv_eq_one_div]
    have ht2 : ((2 * (m : ℝ) + 1) ^ (-(1 / 2 : ℝ))) ^ 2 = 1 / (2 * (m : ℝ) + 1) := by
      rw [ht, div_pow, one_pow, Real.sq_sqrt (le_of_lt hb)]
    have hFm : Fl m ≤ Real.sqrt (2 * (m : ℝ) - 1) := Fl_le_sqrt m hm
    have h1 : 2 * Fl m * (2 * (m : ℝ) + 1) ^ (-(1 / 2 : ℝ))
        ≤ 2 * (Real.sqrt (2 * (m : ℝ) - 1) / Real.sqrt (2 * (m : ℝ) + 1)) := by
      rw [ht]
      have hpos : (0 : ℝ) ≤ 2 * (1 / Real.sqrt (2 * (m : ℝ) + 1)) := by positivity
      have hstep := mul_le_mul_of_nonneg_right hFm hpos
      have heq1 : 2 * Fl m * (1 / Real.sqrt (2 * (m : ℝ) + 1))
          = Fl m * (2 * (1 / Real.sqrt (2 * (m : ℝ) + 1))) := by ring
      have heq2 : 2 * (Real.sqrt (2 * (m : ℝ) - 1) / Real.sqrt (2 * (m : ℝ) + 1))
          = Real.sqrt (2 * (m : ℝ) - 1) * (2 * (1 / Real.sqrt (2 * (m : ℝ) + 1))) := by
        ring
      linarith [hstep, heq1, heq2]
    have h2 : 2 * (Real.sqrt (2 * (m : ℝ) - 1) / Real.sqrt (2 * (m : ℝ) + 1))
        = 2 * Real.sqrt (2 * (m : ℝ) - 1) / Real.sqrt (2 * (m : ℝ) + 1) := by ring
    have h3 := two_sqrt_div_le m hm1
    have hlog : (2 : ℝ) ≤ Real.log (2 * (m : ℝ) + 1) := by
      have h9 : (2 : ℝ) ≤ Real.log 9 := log_nine_ge
      have hle : (9 : ℝ) ≤ 2 * (m : ℝ) + 1 := by linarith
      exact le_trans h9 (Real.log_le_log (by norm_num) hle)
    have hsum : 2 * Fl m * (2 * (m : ℝ) + 1) ^ (-(1 / 2 : ℝ))
        + ((2 * (m : ℝ) + 1) ^ (-(1 / 2 : ℝ))) ^ 2 ≤ Real.log (2 * (m : ℝ) + 1) := by
      rw [ht2]
      have h4 : 1 / (2 * (m : ℝ) + 1) ≤ 2 / (2 * (m : ℝ) + 1) := by
        rw [div_le_div_iff₀ hb hb]; linarith
      linarith
    nlinarith [ih, hsum, sq_nonneg (Fl m), Fl_nonneg m]

lemma primeFactors_log_le_log (n : ℕ) (hn : 1 ≤ n) :
    ∑ p ∈ n.primeFactors, Real.log (p : ℝ) ≤ Real.log (n : ℝ) := by
  have hn0 : n ≠ 0 := by omega
  have hdvd : (∏ p ∈ n.primeFactors, p) ∣ n := Nat.prod_primeFactors_dvd n
  have hcast : ((∏ p ∈ n.primeFactors, p : ℕ) : ℝ) = ∏ p ∈ n.primeFactors, (p : ℝ) := by
    push_cast
    rfl
  calc ∑ p ∈ n.primeFactors, Real.log (p : ℝ)
      = Real.log (∏ p ∈ n.primeFactors, (p : ℝ)) := by
        rw [Real.log_prod]
        intro p hp
        exact_mod_cast (Nat.prime_of_mem_primeFactors hp).ne_zero
    _ = Real.log (((∏ p ∈ n.primeFactors, p : ℕ)) : ℝ) := by rw [hcast]
    _ ≤ Real.log (n : ℝ) := Real.log_le_log
          (by exact_mod_cast (Finset.prod_pos
            (fun p hp => (Nat.prime_of_mem_primeFactors hp).pos)))
          (by exact_mod_cast Nat.le_of_dvd (by omega : 0 < n) hdvd)

theorem sum_primeFactors_inv_sqrt_le (n : ℕ) (hn : 1 ≤ n) :
    ∑ p ∈ n.primeFactors, (p : ℝ) ^ (-(1 / 2 : ℝ)) ≤ Real.sqrt (Real.log (n : ℝ)) := by
  have hprime : ∀ p ∈ n.primeFactors, p.Prime := fun p hp => Nat.prime_of_mem_primeFactors hp
  have hsum := sum_inv_sqrt_le_Lseq n.primeFactors hprime
  have hlog := sum_log_Lseq_le n.primeFactors hprime
  have hlograd := primeFactors_log_le_log n hn
  have hG : Gl n.primeFactors.card ≤ Real.log (n : ℝ) := le_trans hlog hlograd
  have hseq : (Fl n.primeFactors.card) ^ 2 ≤ Gl n.primeFactors.card := by
    rcases Nat.lt_or_ge n.primeFactors.card 5 with hlt | hge
    · interval_cases h : n.primeFactors.card <;>
        first
        | (exact seq_one) | (exact seq_two) | (exact seq_three) | (exact seq_four)
        | (unfold Fl Gl; simp)
    · exact seq_ge_five _ hge
  have hFl : ∑ p ∈ n.primeFactors, (p : ℝ) ^ (-(1 / 2 : ℝ)) ≤ Fl n.primeFactors.card := hsum
  calc ∑ p ∈ n.primeFactors, (p : ℝ) ^ (-(1 / 2 : ℝ)) ≤ Fl n.primeFactors.card := hFl
    _ = Real.sqrt ((Fl n.primeFactors.card) ^ 2) := (Real.sqrt_sq (Fl_nonneg _)).symm
    _ ≤ Real.sqrt (Gl n.primeFactors.card) := Real.sqrt_le_sqrt hseq
    _ ≤ Real.sqrt (Real.log (n : ℝ)) := Real.sqrt_le_sqrt hG

/-- **The Euler-product correction.**  For `q > 400000` and `1/2 ≤ σ ≤ 1` the product over the
prime divisors of `q` of the local imprimitivity factors is at most `exp((log q)^{1-σ/2})`. -/
lemma prod_primeFactors_le_exp {q : ℕ} (hq : 400000 < q) {σ : ℝ}
    (hσ : 1 / 2 ≤ σ) (hσ1 : σ ≤ 1) :
    ∏ p ∈ q.primeFactors, (1 + (p : ℝ) ^ (-σ))
      ≤ Real.exp ((Real.log (q : ℝ)) ^ (1 - σ / 2)) := by
  have hqpos : (0 : ℝ) < (q : ℝ) := by
    have : (0 : ℕ) < q := by omega
    exact_mod_cast this
  have hlog1 : (1 : ℝ) < Real.log (q : ℝ) := by
    rw [Real.lt_log_iff_exp_lt hqpos]
    exact lt_of_lt_of_le Real.exp_one_lt_three (by exact_mod_cast (by omega : 3 ≤ q))
  have hstep1 : ∏ p ∈ q.primeFactors, (1 + (p : ℝ) ^ (-σ))
      ≤ ∏ p ∈ q.primeFactors, Real.exp ((p : ℝ) ^ (-σ)) := by
    refine Finset.prod_le_prod₀ (fun p _ => by positivity) (fun p _ => ?_)
    linarith [Real.add_one_le_exp ((p : ℝ) ^ (-σ))]
  rw [← Real.exp_sum] at hstep1
  have hstep2 : ∑ p ∈ q.primeFactors, (p : ℝ) ^ (-σ)
      ≤ ∑ p ∈ q.primeFactors, (p : ℝ) ^ (-(1 / 2 : ℝ)) := by
    refine Finset.sum_le_sum (fun p hp => ?_)
    have hp1 : (1 : ℝ) ≤ (p : ℝ) := by
      exact_mod_cast (Nat.prime_of_mem_primeFactors hp).one_le
    exact Real.rpow_le_rpow_of_exponent_le hp1 (by linarith)
  have hstep3 : ∑ p ∈ q.primeFactors, (p : ℝ) ^ (-(1 / 2 : ℝ))
      ≤ Real.sqrt (Real.log (q : ℝ)) := sum_primeFactors_inv_sqrt_le q (by omega)
  have hstep4 : Real.sqrt (Real.log (q : ℝ)) ≤ (Real.log (q : ℝ)) ^ (1 - σ / 2) := by
    rw [Real.sqrt_eq_rpow]
    exact Real.rpow_le_rpow_of_exponent_le hlog1.le (by linarith)
  exact hstep1.trans (le_trans (Real.exp_le_exp.mpr hstep2)
    (le_trans (Real.exp_le_exp.mpr hstep3) (Real.exp_le_exp.mpr hstep4)))

lemma log_four_pi_ge : (2.5 : ℝ) ≤ Real.log (4 * Real.pi) := by
  rw [Real.le_log_iff_exp_le (by positivity)]
  have h25 : Real.exp 2.5 = Real.exp 2 * Real.exp 0.5 := by rw [← Real.exp_add]; norm_num
  have h2 : Real.exp 2 = Real.exp 1 ^ 2 := by
    have h : (2 : ℝ) = 1 + 1 := by norm_num
    rw [h, Real.exp_add]; ring
  have hhalf : Real.exp (0.5 : ℝ) = Real.sqrt (Real.exp 1) := by
    rw [show (0.5 : ℝ) = 1 / 2 by norm_num, Real.exp_half]
  rw [h25, h2, hhalf]
  have h3 : Real.sqrt (Real.exp 1) ≤ 1.649 := by
    rw [Real.sqrt_le_left (by norm_num : (0 : ℝ) ≤ 1.649)]
    linarith [Real.exp_one_lt_d9]
  have h4 : Real.exp 1 ^ 2 ≤ 2.7182818286 ^ 2 :=
    pow_le_pow_left₀ (le_of_lt (Real.exp_pos 1)) (le_of_lt Real.exp_one_lt_d9) 2
  have h5 : (2.7182818286 : ℝ) ^ 2 * 1.649 ≤ 4 * Real.pi := by
    have := Real.pi_gt_d2
    nlinarith
  exact le_trans (mul_le_mul h4 h3 (by positivity) (by positivity)) h5

lemma log_four_pi_le : Real.log (4 * Real.pi) ≤ 2.9 := by
  rw [Real.log_le_iff_le_exp (by positivity)]
  have h25 : Real.exp 2.9 = Real.exp 2 * Real.exp 0.9 := by rw [← Real.exp_add]; norm_num
  rw [h25]
  have h2 : (7.389 : ℝ) ≤ Real.exp 2 := by
    have h : Real.exp 2 = Real.exp 1 ^ 2 := by
      have h' : (2 : ℝ) = 1 + 1 := by norm_num
      rw [h', Real.exp_add]; ring
    rw [h]
    nlinarith [Real.exp_one_gt_d9, Real.exp_pos 1]
  have h3 : (1.9 : ℝ) ≤ Real.exp 0.9 := by linarith [Real.add_one_le_exp 0.9]
  have h4 : 4 * Real.pi ≤ 12.6 := by
    have := Real.pi_lt_d2
    linarith
  nlinarith

/-- The norm of `ζ(1) = (γ - log 4π)/2` lies between `9/10` and `6/5`. -/
lemma zeta_one_norm_bounds : (9 / 10 : ℝ) ≤ ‖riemannZeta 1‖ ∧ ‖riemannZeta 1‖ ≤ 6 / 5 := by
  have hcast : Complex.log (4 * (Real.pi : ℂ))
      = ((Real.log (4 * Real.pi) : ℝ) : ℂ) := by
    rw [show (4 * (Real.pi : ℂ)) = ((4 * Real.pi : ℝ) : ℂ) by push_cast; ring]
    exact (Complex.ofReal_log (by positivity : (0 : ℝ) ≤ 4 * Real.pi)).symm
  have hγ1 : (1 / 2 : ℝ) < Real.eulerMascheroniConstant :=
    Real.one_half_lt_eulerMascheroniConstant
  have hγ2 : Real.eulerMascheroniConstant < 2 / 3 := Real.eulerMascheroniConstant_lt_two_thirds
  have hlt : Real.eulerMascheroniConstant < Real.log (4 * Real.pi) := by linarith [log_four_pi_ge]
  have hrepr : riemannZeta 1
      = (((Real.eulerMascheroniConstant - Real.log (4 * Real.pi)) : ℝ) : ℂ) / 2 := by
    rw [riemannZeta_one, hcast]
    push_cast
    ring
  have hnn : ‖(((Real.eulerMascheroniConstant - Real.log (4 * Real.pi)) : ℝ) : ℂ) / 2‖
      = (Real.log (4 * Real.pi) - Real.eulerMascheroniConstant) / 2 := by
    rw [Complex.norm_div, Complex.norm_real, Real.norm_eq_abs,
      abs_of_neg (by linarith : Real.eulerMascheroniConstant - Real.log (4 * Real.pi) < 0)]
    norm_num
  rw [hrepr, hnn]
  constructor <;> linarith [log_four_pi_ge, log_four_pi_le, hγ1, hγ2]

lemma LFunction_cast_level {M N : ℕ} [NeZero M] [NeZero N] (h : M = N)
    (χ : DirichletCharacter ℂ M) (s : ℂ) :
    DirichletCharacter.LFunction χ s = DirichletCharacter.LFunction (h ▸ χ) s := by
  subst h
  rfl

lemma cast_one_eq_one {M N : ℕ} [NeZero M] [NeZero N] (h : M = N) :
    (h ▸ (1 : DirichletCharacter ℂ M)) = (1 : DirichletCharacter ℂ N) := by
  subst h
  rfl

/-- The trivial character at the level `conductor (1 : DirichletCharacter ℂ q)` (which is `1`)
has `L`-function `ζ`. -/
lemma LFunction_one_conductor_eq (q : ℕ) [NeZero q]
    (hI : NeZero (DirichletCharacter.conductor (1 : DirichletCharacter ℂ q))) :
    ∀ s : ℂ,
      @DirichletCharacter.LFunction (DirichletCharacter.conductor (1 : DirichletCharacter ℂ q)) hI
        (1 : DirichletCharacter ℂ (DirichletCharacter.conductor (1 : DirichletCharacter ℂ q))) s
        = riemannZeta s := by
  intro s
  rw [LFunction_cast_level (M := DirichletCharacter.conductor (1 : DirichletCharacter ℂ q))
      (N := 1) (DirichletCharacter.conductor_one) (1 : DirichletCharacter ℂ _) s, cast_one_eq_one]
  simp

lemma exp_three_half_ge : (33 : ℝ) ≤ Real.exp 3.5 := by
  have h : Real.exp 3.5 = Real.exp 3 * Real.exp 0.5 := by rw [← Real.exp_add]; norm_num
  rw [h]
  have h3 : Real.exp 3 = Real.exp 1 ^ 3 := by
    rw [show (3 : ℝ) = (3 : ℕ) * 1 by norm_num, Real.exp_nat_mul 1 3]
  have hhalf : Real.exp (0.5 : ℝ) = Real.sqrt (Real.exp 1) := by
    rw [show (0.5 : ℝ) = 1 / 2 by norm_num, Real.exp_half]
  rw [h3, hhalf]
  have h1 : (20.08 : ℝ) ≤ Real.exp 1 ^ 3 := by
    have hcube : (2.7182818283 : ℝ) ^ 3 ≤ Real.exp 1 ^ 3 :=
      pow_le_pow_left₀ (by norm_num) (le_of_lt Real.exp_one_gt_d9) 3
    nlinarith [hcube]
  have h2 : (1.648 : ℝ) ≤ Real.sqrt (Real.exp 1) := by
    rw [Real.le_sqrt (by norm_num) (le_of_lt (Real.exp_pos 1))]
    linarith [Real.exp_one_gt_d9]
  nlinarith

lemma two_sq_add_le_exp (t : ℝ) (ht : 3.5 ≤ t) : 2 * t ^ 2 + 6 / 5 ≤ (9 / 10) * Real.exp t := by
  have hu : (0 : ℝ) ≤ t - 3.5 := by linarith
  have hsplit : Real.exp t = Real.exp 3.5 * Real.exp (t - 3.5) := by
    rw [← Real.exp_add]
    ring_nf
  have hsum : 1 + (t - 3.5) + (t - 3.5) ^ 2 / 2 ≤ Real.exp (t - 3.5) := by
    have := Real.sum_le_exp_of_nonneg hu 3
    simpa [Finset.sum_range_succ, Nat.factorial] using this
  have h33 := exp_three_half_ge
  nlinarith [hsplit, hsum, h33, Real.exp_pos (t - 3.5), Real.exp_pos 3.5, sq_nonneg (t - 3.5)]




lemma prodSubInvMulLogLe_aux {q : ℕ} (hq : 400000 < q) :
    Real.log (q : ℝ) + 6 / 5 + ∑ p ∈ q.primeFactors, Real.log (p : ℝ) / ((p : ℝ) - 1)
      ≤ (9 / 10) * Real.exp (Real.sqrt (Real.log (q : ℝ))) := by
  have hq1 : 1 ≤ q := by omega
  have hS : ∑ p ∈ q.primeFactors, Real.log (p : ℝ) / ((p : ℝ) - 1) ≤ Real.log (q : ℝ) := by
    refine le_trans ?_ (primeFactors_log_le_log q hq1)
    refine Finset.sum_le_sum (fun p hp => ?_)
    have hp2 : (2 : ℝ) ≤ (p : ℝ) := by
      exact_mod_cast (Nat.prime_of_mem_primeFactors hp).two_le
    have hlognn : (0 : ℝ) ≤ Real.log (p : ℝ) := Real.log_nonneg (by linarith)
    have h1 : (1 : ℝ) ≤ (p : ℝ) - 1 := by linarith
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < (p : ℝ) - 1)]
    nlinarith [hlognn, h1]
  have hx : (12.25 : ℝ) ≤ Real.log (q : ℝ) := by
    rw [Real.le_log_iff_exp_le (by positivity)]
    have h25 : Real.exp 12.25 = Real.exp 12 * Real.exp 0.25 := by rw [← Real.exp_add]; norm_num
    have h12 : Real.exp 12 = Real.exp 1 ^ 12 := by
      rw [show (12 : ℝ) = (12 : ℕ) * 1 by norm_num, Real.exp_nat_mul 1 12]
    rw [h25, h12]
    have h1 : Real.exp 1 ^ 12 ≤ 2.7182818286 ^ 12 :=
      pow_le_pow_left₀ (le_of_lt (Real.exp_pos 1)) (le_of_lt Real.exp_one_lt_d9) 12
    have h2 : Real.exp 0.25 ≤ 4 / 3 := by
      have h := Real.exp_bound_div_one_sub_of_interval (by norm_num : (0 : ℝ) ≤ 0.25)
        (by norm_num : (0.25 : ℝ) < 1)
      norm_num at h ⊢
      exact h
    have h3 : (2.7182818286 : ℝ) ^ 12 * (4 / 3) ≤ 400000 := by norm_num
    have h4 : Real.exp 1 ^ 12 * Real.exp 0.25 ≤ (2.7182818286 : ℝ) ^ 12 * (4 / 3) :=
      mul_le_mul h1 h2 (le_of_lt (Real.exp_pos _)) (by positivity)
    have hqR : (400000 : ℝ) < (q : ℝ) := by exact_mod_cast hq
    linarith [h4, h3, hqR]
  have hx' : Real.sqrt (12.25 : ℝ) ≤ Real.sqrt (Real.log (q : ℝ)) := Real.sqrt_le_sqrt hx
  have ht : (3.5 : ℝ) ≤ Real.sqrt (Real.log (q : ℝ)) := by
    have h35 : Real.sqrt (12.25 : ℝ) = 3.5 := by
      rw [show (12.25 : ℝ) = 3.5 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
    rw [h35] at hx'
    exact hx'
  have htsq : (Real.sqrt (Real.log (q : ℝ))) ^ 2 = Real.log (q : ℝ) :=
    Real.sq_sqrt (by linarith : (0 : ℝ) ≤ Real.log (q : ℝ))
  have hnum := two_sq_add_le_exp (Real.sqrt (Real.log (q : ℝ))) ht
  rw [htsq] at hnum
  linarith


/-- For the principal character mod `q` the correction factor bound holds (here the primitive
character is trivial, so `‖L(χ*, s)‖ = ‖ζ(s)‖`). -/
lemma principal_case {q : ℕ} [NeZero q] (hq : 400000 < q) :
    ∀ s : ℂ, 1 / 2 ≤ s.re → s.re ≤ 1 →
      ‖DirichletCharacter.LFunction (1 : DirichletCharacter ℂ q) s‖
        ≤ ‖riemannZeta s‖ * Real.exp ((Real.log (q : ℝ)) ^ (1 - s.re / 2)) := by
  intro s hσ hσ1
  rcases eq_or_ne s 1 with hs | hs
  · subst hs
    have hq2 : 2 ≤ q := by omega
    have hexp : ((Real.log (q : ℝ)) ^ (1 - (1 : ℂ).re / 2)) = Real.sqrt (Real.log (q : ℝ)) := by
      rw [show (1 : ℂ).re = 1 by norm_num, show (1 : ℝ) - 1 / 2 = 1 / 2 by norm_num,
        ← Real.sqrt_eq_rpow]
    rw [hexp, Work.LinnikAreas.Density4.LFunction_one_apply_one q hq2]
    set R : ℂ := ∏ p ∈ q.primeFactors, ((1 : ℂ) - (p : ℂ)⁻¹) with hR
    set B : ℂ := (Real.log (q : ℝ) : ℂ) + riemannZeta 1
      + ∑ p ∈ q.primeFactors, ((Real.log (p : ℝ) / ((p : ℝ) - 1) : ℝ) : ℂ) with hB
    have hR1 : ‖R‖ ≤ 1 := by
      rw [hR, norm_prod]
      calc ∏ p ∈ q.primeFactors, ‖(1 : ℂ) - (p : ℂ)⁻¹‖
          ≤ ∏ p ∈ q.primeFactors, (1 : ℝ) := by
            refine Finset.prod_le_prod₀ (fun p _ => norm_nonneg _) (fun p hp => ?_)
            have hp1 : (0 : ℝ) < (p : ℝ) := by
              exact_mod_cast (Nat.prime_of_mem_primeFactors hp).pos
            have hp2 : (2 : ℝ) ≤ (p : ℝ) := by
              exact_mod_cast (Nat.prime_of_mem_primeFactors hp).two_le
            have hp1' : (1 : ℕ) ≤ p := by exact_mod_cast (by linarith : (1 : ℝ) ≤ (p : ℝ))
            have hinv : ((p : ℂ)⁻¹) = (((p : ℝ)⁻¹ : ℝ) : ℂ) := by push_cast; ring
            have hle : (p : ℝ)⁻¹ ≤ 1 :=
              inv_le_one_of_one_le₀ (by exact_mod_cast hp1')
            have hpos : (0 : ℝ) ≤ (p : ℝ)⁻¹ := inv_nonneg.mpr (le_of_lt hp1)
            rw [hinv, ← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real,
              Real.norm_eq_abs, abs_of_nonneg (by linarith : (0 : ℝ) ≤ 1 - (p : ℝ)⁻¹)]
            linarith
        _ = 1 := by simp
    have hB1 : ‖B‖ ≤ Real.log (q : ℝ) + 6 / 5
        + ∑ p ∈ q.primeFactors, Real.log (p : ℝ) / ((p : ℝ) - 1) := by
      rw [hB]
      have hsum : ‖∑ p ∈ q.primeFactors,
          ((Real.log (p : ℝ) / ((p : ℝ) - 1) : ℝ) : ℂ)‖
          ≤ ∑ p ∈ q.primeFactors, Real.log (p : ℝ) / ((p : ℝ) - 1) := by
        refine le_trans (norm_sum_le _ _) (Finset.sum_le_sum (fun p hp => ?_))
        have hp1 : (0 : ℝ) < (p : ℝ) := by
          exact_mod_cast (Nat.prime_of_mem_primeFactors hp).pos
        have hp2 : (2 : ℝ) ≤ (p : ℝ) := by
          exact_mod_cast (Nat.prime_of_mem_primeFactors hp).two_le
        have hlognn : (0 : ℝ) ≤ Real.log (p : ℝ) := Real.log_nonneg (by linarith)
        rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (div_nonneg hlognn (by linarith))]
      have hlogq : ‖(Real.log (q : ℝ) : ℂ)‖ = Real.log (q : ℝ) := by
        rw [Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (Real.log_nonneg (by
            have : (1 : ℕ) ≤ q := by omega
            exact_mod_cast this))]
      calc ‖(Real.log (q : ℝ) : ℂ) + riemannZeta 1
            + ∑ p ∈ q.primeFactors, ((Real.log (p : ℝ) / ((p : ℝ) - 1) : ℝ) : ℂ)‖
          ≤ ‖(Real.log (q : ℝ) : ℂ) + riemannZeta 1‖
            + ‖∑ p ∈ q.primeFactors, ((Real.log (p : ℝ) / ((p : ℝ) - 1) : ℝ) : ℂ)‖ :=
            norm_add_le _ _
        _ ≤ (‖(Real.log (q : ℝ) : ℂ)‖ + ‖riemannZeta 1‖)
            + ∑ p ∈ q.primeFactors, Real.log (p : ℝ) / ((p : ℝ) - 1) :=
            add_le_add (norm_add_le _ _) hsum
        _ ≤ Real.log (q : ℝ) + 6 / 5
            + ∑ p ∈ q.primeFactors, Real.log (p : ℝ) / ((p : ℝ) - 1) := by
            rw [hlogq]
            linarith [zeta_one_norm_bounds.2]
    calc ‖R * B‖ = ‖R‖ * ‖B‖ := norm_mul _ _
      _ ≤ 1 * (Real.log (q : ℝ) + 6 / 5
            + ∑ p ∈ q.primeFactors, Real.log (p : ℝ) / ((p : ℝ) - 1)) :=
          mul_le_mul hR1 hB1 (norm_nonneg _) (by norm_num)
      _ ≤ (9 / 10) * Real.exp (Real.sqrt (Real.log (q : ℝ))) := by
          have h := prodSubInvMulLogLe_aux hq
          linarith
      _ ≤ ‖riemannZeta 1‖ * Real.exp (Real.sqrt (Real.log (q : ℝ))) :=
          mul_le_mul_of_nonneg_right zeta_one_norm_bounds.1 (Real.exp_pos _).le
  · rw [show DirichletCharacter.LFunction (1 : DirichletCharacter ℂ q) s
        = DirichletCharacter.LFunctionTrivChar q s from rfl,
      DirichletCharacter.LFunctionTrivChar_eq_mul_riemannZeta (N := q) hs, norm_mul]
    have hbound : ‖∏ p ∈ q.primeFactors, (1 - (p : ℂ) ^ (-s))‖
        ≤ Real.exp ((Real.log (q : ℝ)) ^ (1 - s.re / 2)) := by
      calc ‖∏ p ∈ q.primeFactors, (1 - (p : ℂ) ^ (-s))‖
        = ∏ p ∈ q.primeFactors, ‖1 - (p : ℂ) ^ (-s)‖ := norm_prod _ _
      _ ≤ ∏ p ∈ q.primeFactors, (1 + (p : ℝ) ^ (-s.re)) := by
          refine Finset.prod_le_prod₀ (fun p _ => norm_nonneg _) (fun p hp => ?_)
          have hppos : (0 : ℝ) < (p : ℝ) := by
            exact_mod_cast (Nat.prime_of_mem_primeFactors hp).pos
          calc ‖1 - (p : ℂ) ^ (-s)‖ ≤ ‖(1 : ℂ)‖ + ‖(p : ℂ) ^ (-s)‖ := norm_sub_le _ _
            _ = 1 + (p : ℝ) ^ (-s.re) := by
                rw [Complex.norm_natCast_cpow_of_pos (by exact_mod_cast hppos), norm_one,
                  Complex.neg_re]
      _ ≤ Real.exp ((Real.log (q : ℝ)) ^ (1 - s.re / 2)) :=
          prod_primeFactors_le_exp hq hσ hσ1
    calc ‖∏ p ∈ q.primeFactors, (1 - (p : ℂ) ^ (-s))‖ * ‖riemannZeta s‖
        ≤ Real.exp ((Real.log (q : ℝ)) ^ (1 - s.re / 2)) * ‖riemannZeta s‖ :=
          mul_le_mul_of_nonneg_right hbound (norm_nonneg _)
      _ = ‖riemannZeta s‖ * Real.exp ((Real.log (q : ℝ)) ^ (1 - s.re / 2)) := mul_comm _ _

theorem ImprimitiveFactor {q : ℕ} [NeZero q] (χ₁ : DirichletCharacter ℂ q)
    [NeZero χ₁.conductor] (hq : 400000 < q) :
    ∀ (s : ℂ), 1 / 2 ≤ s.re → s.re ≤ 1 →
      ‖DirichletCharacter.LFunction χ₁ s‖
        ≤ ‖DirichletCharacter.LFunction χ₁.primitiveCharacter s‖
          * Real.exp ((Real.log (q : ℝ)) ^ (1 - s.re / 2)) := by
  intro s hσ hσ1
  by_cases hχ : χ₁ = 1
  · subst hχ
    haveI hI : NeZero (DirichletCharacter.conductor (1 : DirichletCharacter ℂ q)) :=
      ⟨by rw [DirichletCharacter.conductor_one]; exact one_ne_zero⟩
    have hprim : (1 : DirichletCharacter ℂ q).primitiveCharacter
        = (1 : DirichletCharacter ℂ (DirichletCharacter.conductor (1 : DirichletCharacter ℂ q))) :=
      DirichletCharacter.primitiveCharacter_one
    rw [hprim, LFunction_one_conductor_eq q hI s]
    exact principal_case hq s hσ hσ1
  · have hrepr : s = (s.re : ℂ) + (s.im : ℂ) * Complex.I := (Complex.re_add_im s).symm
    rw [hrepr]
    have hred := Commons.NumberTheory.DirichletCharacter.LFunction_nonprimitive_le
      χ₁ hχ (σ := s.re) hσ (t := s.im)
    have hprod := prod_primeFactors_le_exp hq hσ hσ1
    have hexp : (Real.log (q : ℝ)) ^ (1 - (↑s.re + ↑s.im * Complex.I).re / 2)
        = (Real.log (q : ℝ)) ^ (1 - s.re / 2) := by
      rw [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
        Complex.I_im]
      norm_num
    rw [hexp]
    refine le_trans hred (le_trans ?_ (le_of_eq (mul_comm _ _)))
    exact mul_le_mul_of_nonneg_right hprod (norm_nonneg _)

end Work.LinnikAreas.GSum
