import Mathlib
import Submission.Commons.NumberTheory.Chebyshev.theta_le_log3_mul
import Submission.Commons.NumberTheory.Mertens.mertens_lower
import Submission.Commons.NumberTheory.Mertens.primeRecips_loglog_diff
import Submission.Commons.Data.Nat.gcd_sub_reflection
import Submission.Commons.Data.Nat.mul_div_gcd_eq_lcm
import Submission.Commons.NumberTheory.Totient.totient_mul_gcd

import Submission.Commons.NumberTheory.DuffinSchaeffer.residue_fiber_formula
import Submission.Commons.NumberTheory.Totient.totient_eq_prod_primeFactors
import Submission.Commons.NumberTheory.Totient.card_coprime_Icc_one
import Submission.Commons.NumberTheory.Nat.coprime_iff_forall_primeFactors_not_dvd
import Submission.Commons.NumberTheory.Nat.card_multiples_Icc
import Submission.Work.NumberTheory.DuffinSchaeffer.SigmaSelf
import Submission.Work.NumberTheory.DuffinSchaeffer.SigmaAux.sum_log_div_sq_le
noncomputable section
open scoped BigOperators Topology

namespace Commons.NumberTheory.DuffinSchaeffer

set_option linter.unusedVariables false
set_option linter.unusedVariables false

lemma norm_coe_sub (x y : ℝ) :
    ‖(x : UnitAddCircle) - (y : UnitAddCircle)‖ = ‖((x - y : ℝ) : UnitAddCircle)‖ := by
  rw [← AddCircle.coe_sub (p := (1 : ℝ)) x y]

lemma coe_eq_of_int_sub (x y : ℝ) (k : ℤ) (h : x - y = (k : ℝ)) :
    (x : UnitAddCircle) = (y : UnitAddCircle) := by
  rw [QuotientAddGroup.eq_iff_sub_mem]
  rw [AddSubgroup.mem_zmultiples_iff]
  refine ⟨k, ?_⟩
  simpa using h.symm


lemma norm_lt_iff_exists_int (x : ℝ) (s : ℝ) :
    ‖(x : UnitAddCircle)‖ < s ↔ ∃ k : ℤ, |x - (k : ℝ)| < s := by
  rw [UnitAddCircle.norm_eq]
  constructor
  · intro h
    refine ⟨round x, ?_⟩
    simpa using h
  · rintro ⟨k, hk⟩
    exact lt_of_le_of_lt (round_le x k) hk

lemma round_zero_or_one {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) : round x = 0 ∨ round x = 1 := by
  rw [round_eq]
  have hpos : 0 ≤ x + 1 / 2 := by linarith
  have hlt2 : x + 1 / 2 < 2 := by linarith
  have h01 : ⌊x + 1 / 2⌋ = 0 ∨ ⌊x + 1 / 2⌋ = 1 := by
    by_cases h : x + 1 / 2 < 1
    · left
      refine (Int.floor_eq_iff.mpr ?_)
      constructor <;> linarith
    · right
      refine (Int.floor_eq_iff.mpr ?_)
      constructor <;> linarith
  rcases h01 with h0 | h1
  · exact Or.inl h0
  · exact Or.inr h1

lemma norm_div_lt_iff (v L : ℕ) (Δ : ℝ) (hL : 0 < L) (hvL : v ≤ L) (hΔ : 0 ≤ Δ) :
    ‖(((v : ℝ) / (L : ℝ) : ℝ) : UnitAddCircle)‖ < Δ ↔
      (v : ℝ) < Δ * (L : ℝ) ∨ (L : ℝ) - (v : ℝ) < Δ * (L : ℝ) := by
  have hLpos : 0 < (L : ℝ) := by exact_mod_cast hL
  let x : ℝ := (v : ℝ) / (L : ℝ)
  have hx0 : 0 ≤ x := by dsimp [x]; positivity
  have hx1 : x ≤ 1 := by dsimp [x]; rw [div_le_one hLpos]; exact_mod_cast hvL
  have hx_delta : (x < Δ ∨ 1 - x < Δ) ↔ ((v : ℝ) < Δ * (L : ℝ) ∨ (L : ℝ) - (v : ℝ) < Δ * (L : ℝ)) := by
    constructor
    · rintro (h | h)
      · left
        exact (div_lt_iff₀ hLpos).mp (by simpa [x] using h)
      · right
        have h1 : 1 - x = ((L : ℝ) - (v : ℝ)) / (L : ℝ) := by
          dsimp [x]
          field_simp [hLpos.ne']
        exact (div_lt_iff₀ hLpos).mp (by simpa [h1] using h)
    · rintro (h | h)
      · left
        exact (div_lt_iff₀ hLpos).mpr (by simpa [x] using h)
      · right
        have h1 : 1 - x = ((L : ℝ) - (v : ℝ)) / (L : ℝ) := by
          dsimp [x]
          field_simp [hLpos.ne']
        have h2 : ((L : ℝ) - (v : ℝ)) / (L : ℝ) < Δ := (div_lt_iff₀ hLpos).mpr (by simpa [x] using h)
        simpa [h1] using h2
  rw [norm_lt_iff_exists_int]
  refine Iff.trans ?_ hx_delta
  constructor
  · rintro ⟨k, hk⟩
    by_cases hk0 : k ≤ 0
    · left
      have hxmk_nonneg : 0 ≤ x - (k : ℝ) := by
        have : (k : ℝ) ≤ 0 := by exact_mod_cast hk0
        linarith
      have hx_le : x ≤ |x - (k : ℝ)| := by
        rw [abs_of_nonneg hxmk_nonneg]
        have hkR : (k : ℝ) ≤ 0 := by exact_mod_cast hk0
        linarith
      exact lt_of_le_of_lt hx_le hk
    · right
      have hk1 : 1 ≤ k := by omega
      have hxmk_nonpos : x - (k : ℝ) ≤ 0 := by
        have : 1 ≤ (k : ℝ) := by exact_mod_cast hk1
        linarith
      have hle : 1 - x ≤ |x - (k : ℝ)| := by
        rw [abs_of_nonpos hxmk_nonpos]
        have : 1 ≤ (k : ℝ) := by exact_mod_cast hk1
        linarith
      exact lt_of_le_of_lt hle hk
  · rintro (h | h)
    · refine ⟨0, ?_⟩
      norm_num
      have hx0' : 0 ≤ (v : ℝ) / (L : ℝ) := by positivity
      rw [abs_of_nonneg hx0']
      exact (by simpa [x] using h)
    · refine ⟨1, ?_⟩
      norm_num
      have hnonpos : (v : ℝ) / (L : ℝ) - 1 ≤ 0 := by
        have hvle1 : (v : ℝ) / (L : ℝ) ≤ 1 := by
          rw [div_le_one hLpos]
          exact_mod_cast hvL
        linarith
      rw [abs_of_nonpos hnonpos]
      simpa [x] using h

def redPairs (q r : ℕ) : Finset (ℕ × ℕ) :=
  Finset.product ((Finset.range q).filter (fun a : ℕ => a.gcd q = 1))
    ((Finset.range r).filter (fun b : ℕ => b.gcd r = 1))

-- class of the pair: aR - bQ mod L in [0,L)
def pairVal (q r : ℕ) (ab : ℕ × ℕ) : ℕ :=
  (ab.1 * (r / q.gcd r) + (q * r / q.gcd r) - ab.2 * (q / q.gcd r)) %
    (q * r / q.gcd r)

def fiberCard (q r : ℕ) (c : ℕ) : ℕ :=
  ((redPairs q r).filter (fun ab : ℕ × ℕ =>
    pairVal q r ab = c)).card

lemma gpos (q r : ℕ) (hq : 0 < q) (hr : 0 < r) : 0 < q.gcd r :=
  Nat.gcd_pos_of_pos_left r hq

lemma Lpos (q r : ℕ) (hq : 0 < q) (hr : 0 < r) : 0 < q * r / q.gcd r := by
  have hle : q.gcd r ≤ q * r :=
    le_trans (Nat.gcd_le_left r hq) (Nat.le_mul_of_pos_right q hr)
  exact Nat.div_pos hle (gpos q r hq hr)

lemma aR_lt_L (q r a : ℕ) (hq : 0 < q) (hr : 0 < r) (ha : a < q) :
    a * (r / q.gcd r) < q * r / q.gcd r := by
  have hg : 0 < q.gcd r := gpos q r hq hr
  have hgR : q.gcd r ∣ r := Nat.gcd_dvd_right q r
  calc
    a * (r / q.gcd r) < q * (r / q.gcd r) :=
      Nat.mul_lt_mul_of_pos_right ha (Nat.div_pos (Nat.gcd_le_right q hr) hg)
    _ = q * r / q.gcd r := by rw [Nat.mul_div_assoc q hgR]

lemma bQ_lt_L (q r b : ℕ) (hq : 0 < q) (hr : 0 < r) (hb : b < r) :
    b * (q / q.gcd r) < q * r / q.gcd r := by
  have hg : 0 < q.gcd r := gpos q r hq hr
  have hgQ : q.gcd r ∣ q := Nat.gcd_dvd_left q r
  have hm : r * (q / q.gcd r) = q * r / q.gcd r := by
    calc
      r * (q / q.gcd r) = r * q / q.gcd r := (Nat.mul_div_assoc r hgQ).symm
      _ = q * r / q.gcd r := by rw [mul_comm]
  calc
    b * (q / q.gcd r) < r * (q / q.gcd r) :=
      Nat.mul_lt_mul_of_pos_right hb (Nat.div_pos (Nat.gcd_le_left r hq) hg)
    _ = q * r / q.gcd r := hm

-- pair value congruence: (bQ + pairVal) % L = aR (both < L)
lemma mod_add_sub_mod_eq (x y L : ℕ) (hx : x < L) (hy : y < L) :
    (y + (x + L - y) % L) % L = x % L := by
  by_cases hxy : y ≤ x
  · have hxLy : L ≤ x + L - y := by omega
    have hs : x + L - y - L = x - y := by omega
    have hsub : (x + L - y) % L = (x - y) % L := by
      rw [Nat.mod_eq_sub_mod hxLy]
      exact congrArg (fun t => t % L) hs
    rw [hsub]
    have hlt : x - y < L := by omega
    have hxy2 : (x - y) % L = x - y := Nat.mod_eq_of_lt hlt
    rw [hxy2]
    have h1 : (y + (x - y)) % L = x % L := by
      have : y + (x - y) = x := by omega
      rw [this]
    exact h1
  · have hlt : x + L - y < L := by omega
    have hsub : (x + L - y) % L = x + L - y := Nat.mod_eq_of_lt hlt
    rw [hsub]
    have h1 : (y + (x + L - y)) % L = (x + L) % L := by
      have : y + (x + L - y) = x + L := by omega
      rw [this]
    have h2 : (x + L) % L = x % L := by
      rw [Nat.add_mod, Nat.mod_self, add_zero, Nat.mod_mod]
    rw [h1, h2]

lemma pairVal_mod (q r : ℕ) (hq : 0 < q) (hr : 0 < r) (ab : ℕ × ℕ)
    (ha : ab.1 < q) (hb : ab.2 < r) :
    (ab.2 * (q / q.gcd r) + pairVal q r ab) % (q * r / q.gcd r) =
      ab.1 * (r / q.gcd r) % (q * r / q.gcd r) := by
  dsimp [pairVal]
  let L : ℕ := q * r / q.gcd r
  let x : ℕ := ab.1 * (r / q.gcd r)
  let y : ℕ := ab.2 * (q / q.gcd r)
  have hx : x < L := by
    dsimp [x, L]
    exact aR_lt_L q r ab.1 hq hr ha
  have hy : y < L := by
    dsimp [y, L]
    exact bQ_lt_L q r ab.2 hq hr hb
  have h1 := mod_add_sub_mod_eq x y L hx hy
  dsimp [x, y, L] at h1
  exact h1

-- pair norm equals ‖pairVal/L‖
lemma pair_norm_eq_val (q r : ℕ) (hq : 0 < q) (hr : 0 < r) (ab : ℕ × ℕ)
    (ha : ab.1 < q) (hb : ab.2 < r) :
    ‖(((ab.1 : ℝ) / (q : ℝ) : ℝ) : UnitAddCircle) -
       (((ab.2 : ℝ) / (r : ℝ) : ℝ) : UnitAddCircle)‖ =
      ‖((((pairVal q r ab : ℝ) / ((q * r / q.gcd r : ℕ) : ℝ) : ℝ) : UnitAddCircle))‖ := by
  classical
  rw [norm_coe_sub]
  -- real difference of the two arguments is an integer
  let g : ℕ := q.gcd r
  let Q : ℕ := q / g
  let R : ℕ := r / g
  let L : ℕ := q * r / g
  have hLpos : 0 < L := Lpos q r hq hr
  have hLne : (L : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hLpos)
  let x : ℕ := ab.1 * R
  let y : ℕ := ab.2 * Q
  have hx : x < L := by dsimp [x, R, L]; exact aR_lt_L q r ab.1 hq hr ha
  have hy : y < L := by dsimp [y, Q, L]; exact bQ_lt_L q r ab.2 hq hr hb
  let v : ℕ := pairVal q r ab
  let m : ℕ := (x + L - y) / L
  have hdiv : x + L - y = m * L + v := by
    dsimp [m, v, pairVal, x, y, R, Q, L, g]
    simpa [mul_comm] using (Nat.div_add_mod
      (ab.1 * (r / q.gcd r) + q * r / q.gcd r - ab.2 * (q / q.gcd r)) (q * r / q.gcd r)).symm
  have heq_circle : (↑((ab.1 : ℝ) / (q : ℝ) - (ab.2 : ℝ) / (r : ℝ)) : UnitAddCircle) =
      (↑((pairVal q r ab : ℝ) / (L : ℝ)) : UnitAddCircle) := by
    -- difference of the two real representatives is m-1
    have hqne : (q : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hq)
    have hrne : (r : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hr)
    have hqR : (q : ℝ) * (R : ℝ) = (L : ℝ) := by
      dsimp [R, L]
      have hn : q * (r / q.gcd r) = q * r / q.gcd r := (Nat.mul_div_assoc q (Nat.gcd_dvd_right q r)).symm
      exact_mod_cast hn
    have hrQ : (r : ℝ) * (Q : ℝ) = (L : ℝ) := by
      dsimp [Q, L]
      have hn : r * (q / q.gcd r) = q * r / q.gcd r := by
        calc
          r * (q / q.gcd r) = r * q / q.gcd r := (Nat.mul_div_assoc r (Nat.gcd_dvd_left q r)).symm
          _ = q * r / q.gcd r := by rw [mul_comm]
      exact_mod_cast hn
    have hfrac : (ab.1 : ℝ) / (q : ℝ) - (ab.2 : ℝ) / (r : ℝ) =
        ((x : ℝ) - (y : ℝ)) / (L : ℝ) := by
      have h1 : (ab.1 : ℝ) / (q : ℝ) = (ab.1 : ℝ) * (R : ℝ) / (L : ℝ) := by
        field_simp [hqne, hLne]
        rw [← hqR]
        ring
      have h2 : (ab.2 : ℝ) / (r : ℝ) = (ab.2 : ℝ) * (Q : ℝ) / (L : ℝ) := by
        field_simp [hrne, hLne]
        rw [← hrQ]
        ring
      rw [h1, h2]
      simp [x, y]
      ring_nf
    have hy_le : y ≤ L := le_of_lt hy
    have cast_sub_real (a b : ℕ) (h : b ≤ a) : ((a - b : ℕ) : ℝ) = (a : ℝ) - (b : ℝ) := by
      have hh : a - b + b = a := Nat.sub_add_cancel h
      have hc := congrArg (fun n : ℕ => (n : ℝ)) hh
      norm_num at hc ⊢
      linarith
    have hdiv_cast : (x : ℝ) + (L : ℝ) - (y : ℝ) = (m : ℝ) * (L : ℝ) + (pairVal q r ab : ℝ) := by
      have h1 : x + L - y = x + (L - y) := by omega
      rw [h1] at hdiv
      -- hdiv: x + (L - y) = m*L + v
      have hcastLHS : ((x + (L - y) : ℕ) : ℝ) = (x : ℝ) + (L : ℝ) - (y : ℝ) := by
        simp only [Nat.cast_add]
        rw [cast_sub_real L y hy_le]
        ring
      have hc := congrArg (fun n : ℕ => (n : ℝ)) hdiv
      change (x : ℝ) + (L : ℝ) - (y : ℝ) = (m : ℝ) * (L : ℝ) + (v : ℝ)
      rw [← hcastLHS]
      calc
        ((x + (L - y) : ℕ) : ℝ) = ((m * L + v : ℕ) : ℝ) := by simpa using hc
        _ = (m : ℝ) * (L : ℝ) + (v : ℝ) := by simp
    have hnum : (x : ℝ) - (y : ℝ) - (pairVal q r ab : ℝ) =
        ((m : ℤ) - 1 : ℝ) * (L : ℝ) := by
      have hm1 : (m : ℝ) - 1 = ((m : ℤ) - 1 : ℝ) := by norm_num
      rw [← hm1]
      nlinarith
    have hdiff : ((ab.1 : ℝ) / (q : ℝ) - (ab.2 : ℝ) / (r : ℝ)) -
        (pairVal q r ab : ℝ) / (L : ℝ) = ((m : ℤ) - 1 : ℝ) := by
      rw [hfrac]
      calc
        ((x : ℝ) - (y : ℝ)) / (L : ℝ) - (pairVal q r ab : ℝ) / (L : ℝ)
            = ((x : ℝ) - (y : ℝ) - (pairVal q r ab : ℝ)) / (L : ℝ) := by ring
        _ = (((m : ℤ) - 1 : ℝ) * (L : ℝ)) / (L : ℝ) := by rw [hnum]
        _ = ((m : ℤ) - 1 : ℝ) := by field_simp [hLne]
    have hdiff' : ((ab.1 : ℝ) / (q : ℝ) - (ab.2 : ℝ) / (r : ℝ)) -
        (pairVal q r ab : ℝ) / (L : ℝ) = (((m : ℤ) - 1 : ℤ) : ℝ) := by
      simpa using hdiff
    exact coe_eq_of_int_sub ((ab.1 : ℝ) / (q : ℝ) - (ab.2 : ℝ) / (r : ℝ))
      ((pairVal q r ab : ℝ) / (L : ℝ)) ((m : ℤ) - 1) hdiff'
  rw [heq_circle]




-- value < L
lemma pairVal_lt (q r : ℕ) (hq : 0 < q) (hr : 0 < r) (ab : ℕ × ℕ) :
    pairVal q r ab < q * r / q.gcd r := by
  dsimp [pairVal]
  exact Nat.mod_lt _ (Lpos q r hq hr)

-- value of a pair is in range L
lemma pairVal_in_range (q r : ℕ) (hq : 0 < q) (hr : 0 < r) (ab : ℕ × ℕ) :
    pairVal q r ab ∈ Finset.range (q * r / q.gcd r) := by
  exact Finset.mem_range.mpr (pairVal_lt q r hq hr ab)

-- membership facts about redPairs
lemma redPairs_mem_iff (q r : ℕ) (a b : ℕ) :
    (a, b) ∈ redPairs q r ↔ a ∈ Finset.range q ∧ b ∈ Finset.range r ∧ a.gcd q = 1 ∧ b.gcd r = 1 := by
  classical
  simp [redPairs]
  tauto

-- negation map on residues: ((q-a)%q) coprime to q iff a coprime to q (for a ≤ q)
lemma neg_residue_gcd (q a : ℕ) (hq : 0 < q) (ha : a ≤ q) :
    ((q - a) % q).gcd q = a.gcd q := by
  calc
    ((q - a) % q).gcd q = q.gcd (q - a) := by
      have hrec := Nat.gcd_rec q (q - a)
      exact hrec.symm
    _ = a.gcd q := Commons.Data.Nat.gcd_sub_reflection q a ha



-- window predicate on residues
def windowPred (q r : ℕ) (Δ : ℝ) (c : ℕ) : Prop :=
  let L : ℕ := q * r / q.gcd r
  (c : ℝ) < Δ * (L : ℝ) ∨ (L : ℝ) - (c : ℝ) < Δ * (L : ℝ)

-- counted predicate for a pair
def counted (q r : ℕ) (Δ : ℝ) (ab : ℕ × ℕ) : Prop :=
  ‖(((ab.1 : ℝ) / (q : ℝ) : ℝ) : UnitAddCircle) -
     (((ab.2 : ℝ) / (r : ℝ) : ℝ) : UnitAddCircle)‖ < Δ

noncomputable instance windowPred_dec (q r : ℕ) (Δ : ℝ) (c : ℕ) :
    Decidable (windowPred q r Δ c) := by
  dsimp [windowPred]
  infer_instance

noncomputable instance counted_dec (q r : ℕ) (Δ : ℝ) (ab : ℕ × ℕ) :
    Decidable (counted q r Δ ab) := by
  dsimp [counted]
  infer_instance

-- pair counted iff its value lies in the window
lemma counted_iff_window (q r : ℕ) (hq : 0 < q) (hr : 0 < r) (ab : ℕ × ℕ)
    (hred : ab ∈ redPairs q r) (Δ : ℝ) (hΔ : 0 ≤ Δ) (hΔ12 : Δ < 1 / 2) :
    counted q r Δ ab ↔ windowPred q r Δ (pairVal q r ab) := by
  have ha : ab.1 < q := Finset.mem_range.mp ((redPairs_mem_iff q r ab.1 ab.2).mp hred |>.1)
  have hb : ab.2 < r := Finset.mem_range.mp ((redPairs_mem_iff q r ab.1 ab.2).mp hred |>.2.1)
  have hL : 0 < q * r / q.gcd r := Lpos q r hq hr
  have hvL : pairVal q r ab ≤ q * r / q.gcd r := le_of_lt (pairVal_lt q r hq hr ab)
  unfold counted windowPred
  rw [pair_norm_eq_val q r hq hr ab ha hb]
  exact norm_div_lt_iff (pairVal q r ab) (q * r / q.gcd r) Δ hL hvL hΔ

-- the filter equals the sum over c with window(c)
lemma count_eq_window_sum (q r : ℕ) (hq : 0 < q) (hr : 0 < r) (Δ : ℝ) (hΔ : 0 ≤ Δ)
    (hΔ12 : Δ < 1 / 2) :
    ((redPairs q r).filter (fun ab : ℕ × ℕ => counted q r Δ ab)).card =
      ∑ c ∈ (Finset.range (q * r / q.gcd r)),
        (if windowPred q r Δ c then fiberCard q r c else 0) := by
  classical
  let L : ℕ := q * r / q.gcd r
  let P : ℕ × ℕ → Prop := fun ab => counted q r Δ ab
  have hcard : ((redPairs q r).filter (fun ab => P ab)).card =
      ∑ ab ∈ redPairs q r, if P ab then 1 else 0 := by
    rw [Finset.card_eq_sum_ones]
    rw [Finset.sum_filter]
  have hval : ∀ ab ∈ redPairs q r, pairVal q r ab ∈ Finset.range L := by
    intro ab hab
    dsimp [L]
    exact pairVal_in_range q r hq hr ab
  -- indicator identity: 1[P ab] = sum over c of 1[pairVal = c ∧ window c]
  have hid (ab : ℕ × ℕ) (hab : ab ∈ redPairs q r) :
      (if P ab then 1 else 0) =
        ∑ c ∈ Finset.range L, if pairVal q r ab = c then
          (if windowPred q r Δ c then 1 else 0) else 0 := by
    have hw : P ab ↔ windowPred q r Δ (pairVal q r ab) := by
      dsimp [P]
      exact counted_iff_window q r hq hr ab hab Δ hΔ hΔ12
    have hval' : pairVal q r ab ∈ Finset.range L := hval ab hab
    by_cases hP : P ab
    · have hw' : windowPred q r Δ (pairVal q r ab) := hw.mp hP
      rw [if_pos hP]
      symm
      calc
        (∑ c ∈ Finset.range L, if pairVal q r ab = c then (if windowPred q r Δ c then 1 else 0) else 0)
            = (if pairVal q r ab = pairVal q r ab then (if windowPred q r Δ (pairVal q r ab) then 1 else 0) else 0) := by
              exact Finset.sum_eq_single_of_mem (pairVal q r ab) hval'
                (by intro c hc hne; rw [if_neg]; intro he; exact hne he.symm)
        _ = 1 := by rw [if_pos rfl, if_pos hw']
    · rw [if_neg hP]
      have hw' : ¬ windowPred q r Δ (pairVal q r ab) := fun h => hP (hw.mpr h)
      symm
      calc
        (∑ c ∈ Finset.range L, if pairVal q r ab = c then (if windowPred q r Δ c then 1 else 0) else 0)
            = (if pairVal q r ab = pairVal q r ab then (if windowPred q r Δ (pairVal q r ab) then 1 else 0) else 0) := by
              exact Finset.sum_eq_single_of_mem (pairVal q r ab) hval'
                (by intro c hc hne; rw [if_neg]; intro he; exact hne he.symm)
        _ = 0 := by rw [if_pos rfl, if_neg hw']
  calc
    ((redPairs q r).filter (fun ab => P ab)).card
        = ∑ ab ∈ redPairs q r, if P ab then 1 else 0 := hcard
    _ = ∑ ab ∈ redPairs q r,
          (∑ c ∈ Finset.range L, if pairVal q r ab = c then
            (if windowPred q r Δ c then 1 else 0) else 0) := by
          refine Finset.sum_congr rfl ?_
          intro ab hab
          exact hid ab hab
    _ = ∑ c ∈ Finset.range L,
          (∑ ab ∈ redPairs q r, if pairVal q r ab = c then
            (if windowPred q r Δ c then 1 else 0) else 0) := by
          rw [Finset.sum_comm]
    _ = ∑ c ∈ Finset.range L, if windowPred q r Δ c then fiberCard q r c else 0 := by
          refine Finset.sum_congr rfl ?_
          intro c hc
          have hfib : (∑ ab ∈ redPairs q r, if pairVal q r ab = c then 1 else 0) = fiberCard q r c := by
            dsimp [fiberCard]
            rw [Finset.card_eq_sum_ones]
            rw [Finset.sum_filter]
          by_cases hw : windowPred q r Δ c
          · rw [if_pos hw]
            simpa [hw] using hfib
          · rw [if_neg hw]
            simp [hw]

lemma Q_R_coprime (q r : ℕ) (hq : 0 < q) (hr : 0 < r) :
    (q / q.gcd r).gcd (r / q.gcd r) = 1 := by
  have hcop : (q / q.gcd r).Coprime (r / q.gcd r) :=
    Nat.coprime_div_gcd_div_gcd (gpos q r hq hr)
  exact Nat.coprime_iff_gcd_eq_one.mp hcop

lemma exists_prime_dvd_QR (q r : ℕ) (hq : 0 < q) (hr : 0 < r) (hqr : q ≠ r) :
    ∃ p : ℕ, p.Prime ∧ p ∣ q * r / (q.gcd r * q.gcd r) := by
  have hgpos : 0 < q.gcd r := gpos q r hq hr
  have hg2pos : 0 < q.gcd r * q.gcd r := Nat.mul_pos hgpos hgpos
  have hQRpos : 0 < q * r / (q.gcd r * q.gcd r) := by
    have hle : q.gcd r * q.gcd r ≤ q * r :=
      Nat.mul_le_mul (Nat.gcd_le_left r hq) (Nat.gcd_le_right q hr)
    exact Nat.div_pos hle hg2pos
  have hQRne1 : q * r / (q.gcd r * q.gcd r) ≠ 1 := by
    intro h1
    let Q : ℕ := q / q.gcd r
    let R : ℕ := r / q.gcd r
    have hQR : q * r / (q.gcd r * q.gcd r) = Q * R := by
      dsimp [Q, R]
      exact (Nat.div_mul_div_comm (Nat.gcd_dvd_left q r) (Nat.gcd_dvd_right q r)).symm
    have hQR1 : Q * R = 1 := by simpa [hQR] using h1
    have hR1 : R = 1 := Nat.eq_one_of_dvd_one ⟨Q, by rw [mul_comm]; exact hQR1.symm⟩
    have hQ1 : Q = 1 := Nat.eq_one_of_dvd_one ⟨R, hQR1.symm⟩
    have hqdef : q = q.gcd r * Q := by
      have hh := (Nat.div_mul_cancel (Nat.gcd_dvd_left q r)).symm
      simpa [Q, mul_comm] using hh
    have hrdef : r = q.gcd r * R := by
      have hh := (Nat.div_mul_cancel (Nat.gcd_dvd_right q r)).symm
      simpa [R, mul_comm] using hh
    have : q = r := by
      rw [hqdef, hrdef, hQ1, hR1]
      simp
    exact hqr this
  have hgt1 : 1 < q * r / (q.gcd r * q.gcd r) := by omega
  obtain ⟨p, hpp, hpdvd⟩ := Nat.exists_prime_and_dvd (ne_of_gt hgt1)
  exact ⟨p, hpp, hpdvd⟩



lemma fiber_zero (q r : ℕ) (hq : 0 < q) (hr : 0 < r) (hqr : q ≠ r) :
    fiberCard q r 0 = 0 := by
  classical
  obtain ⟨p, hpp, hpdvd⟩ := exists_prime_dvd_QR q r hq hr hqr
  let g : ℕ := q.gcd r
  let Q : ℕ := q / g
  let R : ℕ := r / g
  let L : ℕ := q * r / g
  have hgpos : 0 < g := gpos q r hq hr
  have hQR : q * r / (g * g) = Q * R := by
    dsimp [Q, R, g]
    exact (Nat.div_mul_div_comm (Nat.gcd_dvd_left q r) (Nat.gcd_dvd_right q r)).symm
  have hQR' : q * r / (q.gcd r * q.gcd r) = (q / q.gcd r) * (r / q.gcd r) := by
    exact (Nat.div_mul_div_comm (Nat.gcd_dvd_left q r) (Nat.gcd_dvd_right q r)).symm
  have hpQR' : p ∣ (q / q.gcd r) * (r / q.gcd r) := by
    rw [← hQR']
    exact hpdvd
  have hpQR : p ∣ Q * R := by
    simpa [Q, R] using hpQR'
  have hQorR : p ∣ Q ∨ p ∣ R := (hpp.dvd_mul).mp hpQR
  have hgQR : Q.gcd R = 1 := by
    dsimp [Q, R]
    exact Q_R_coprime q r hq hr
  have hfilter : (redPairs q r).filter (fun x : ℕ × ℕ => pairVal q r x = 0) = ∅ := by
    ext ab
    constructor
    · intro hab
      have hmem := (Finset.mem_filter.mp hab).1
      have hval0 : pairVal q r ab = 0 := (Finset.mem_filter.mp hab).2
      have hred : ab ∈ redPairs q r := hmem
      have ha : ab.1 < q := Finset.mem_range.mp ((redPairs_mem_iff q r ab.1 ab.2).mp hred |>.1)
      have hb : ab.2 < r := Finset.mem_range.mp ((redPairs_mem_iff q r ab.1 ab.2).mp hred |>.2.1)
      have hcop1 : ab.1.gcd q = 1 := (redPairs_mem_iff q r ab.1 ab.2).mp hred |>.2.2.1
      have hcop2 : ab.2.gcd r = 1 := (redPairs_mem_iff q r ab.1 ab.2).mp hred |>.2.2.2
      have hcong := pairVal_mod q r hq hr ab ha hb
      have hcong' : (ab.2 * Q) % L = (ab.1 * R) % L := by
        have h := pairVal_mod q r hq hr ab ha hb
        rw [hval0] at h
        simpa using h
      have hLpos : 0 < L := by dsimp [L]; exact Lpos q r hq hr
      have hq_gQ : q = q.gcd r * (q / q.gcd r) := by
        have hh := (Nat.div_mul_cancel (Nat.gcd_dvd_left q r)).symm
        simpa [mul_comm] using hh
      have hL_qR : L = q * (r / q.gcd r) := by
        dsimp [L]
        exact (Nat.mul_div_assoc q (Nat.gcd_dvd_right q r))
      have hLdef : L = g * (Q * R) := by
        calc
          L = q * (r / q.gcd r) := hL_qR
          _ = (q.gcd r * (q / q.gcd r)) * (r / q.gcd r) := by
            exact congrArg (fun t : ℕ => t * (r / q.gcd r)) hq_gQ
          _ = q.gcd r * ((q / q.gcd r) * (r / q.gcd r)) := by rw [mul_assoc]
      have hQdvd : Q ∣ g * (Q * R) := by
        have heq : g * (Q * R) = Q * (g * R) := by ring
        rw [heq]
        exact dvd_mul_right Q (g * R)
      have hRdvd : R ∣ g * (Q * R) := by
        have heq : g * (Q * R) = R * (g * Q) := by ring
        rw [heq]
        exact dvd_mul_right R (g * Q)
      have hpL : p ∣ L := by
        rw [hLdef]
        rcases hQorR with hQ | hR
        · exact dvd_trans hQ hQdvd
        · exact dvd_trans hR hRdvd
      have hmodp : (ab.1 * R) % p = (ab.2 * Q) % p := by
        calc
          (ab.1 * R) % p = (ab.1 * R) % L % p := (Nat.mod_mod_of_dvd (ab.1 * R) hpL).symm
          _ = (ab.2 * Q) % L % p := by rw [hcong']
          _ = (ab.2 * Q) % p := Nat.mod_mod_of_dvd (ab.2 * Q) hpL
      have hqdiv : q = (q / q.gcd r) * q.gcd r := (Nat.div_mul_cancel (Nat.gcd_dvd_left q r)).symm
      have hrdiv : r = (r / q.gcd r) * q.gcd r := (Nat.div_mul_cancel (Nat.gcd_dvd_right q r)).symm
      rcases hQorR with hpQ | hpR
      · have hpnotR : ¬ p ∣ R := by
          intro hR
          have hd : p ∣ Q.gcd R := Nat.dvd_gcd hpQ hR
          rw [hgQR] at hd
          exact hpp.not_dvd_one hd
        have hpq : p ∣ q := by
          exact dvd_trans hpQ ⟨q.gcd r, hqdiv⟩
        have hpa : ¬ p ∣ ab.1 := by
          intro hpa
          have hd : p ∣ ab.1.gcd q := Nat.dvd_gcd hpa hpq
          rw [hcop1] at hd
          exact hpp.not_dvd_one hd
        have hp_aR : p ∣ ab.1 * R := by
          rw [Nat.dvd_iff_mod_eq_zero]
          have hb0 : (ab.2 * Q) % p = 0 := by
            have hp_bQ : p ∣ ab.2 * Q := dvd_trans hpQ (by simpa [mul_comm] using (dvd_mul_right Q ab.2))
            exact Nat.mod_eq_zero_of_dvd hp_bQ
          rw [hmodp]
          exact hb0
        exact False.elim ((hpp.not_dvd_mul hpa hpnotR) hp_aR)
      · have hpnotQ : ¬ p ∣ Q := by
          intro hQ
          have hd : p ∣ Q.gcd R := Nat.dvd_gcd hQ hpR
          rw [hgQR] at hd
          exact hpp.not_dvd_one hd
        have hpr : p ∣ r := by
          exact dvd_trans hpR ⟨q.gcd r, hrdiv⟩
        have hpb : ¬ p ∣ ab.2 := by
          intro hpb
          have hd : p ∣ ab.2.gcd r := Nat.dvd_gcd hpb hpr
          rw [hcop2] at hd
          exact hpp.not_dvd_one hd
        have hp_bQ : p ∣ ab.2 * Q := by
          rw [Nat.dvd_iff_mod_eq_zero]
          have ha0 : (ab.1 * R) % p = 0 := by
            have hp_aR : p ∣ ab.1 * R := dvd_trans hpR (by simpa [mul_comm] using (dvd_mul_right R ab.1))
            exact Nat.mod_eq_zero_of_dvd hp_aR
          rw [← hmodp]
          exact ha0
        exact False.elim ((hpp.not_dvd_mul hpb hpnotQ) hp_bQ)
    · intro hmn
      simp at hmn
  unfold fiberCard
  rw [hfilter]
  simp


def reducedPairs (q r : ℕ) (Δ : ℝ) : Finset (ℕ × ℕ) :=
  (Finset.product ((Finset.range q).filter (fun a : ℕ => a.gcd q = 1))
      ((Finset.range r).filter (fun b : ℕ => b.gcd r = 1))).filter
    (fun ab : ℕ × ℕ =>
      ‖(((ab.1 : ℝ) / (q : ℝ) : ℝ) : UnitAddCircle) -
         (((ab.2 : ℝ) / (r : ℝ) : ℝ) : UnitAddCircle)‖ < Δ)

/-- φ(q)·φ(r) bounds the number of reduced pairs (before the window filter). -/
lemma reducedPairs_card_le_totient_mul (q r : ℕ) (Δ : ℝ) :
    (reducedPairs q r Δ).card ≤ q.totient * r.totient := by
  classical
  unfold reducedPairs
  calc
    ((Finset.product ((Finset.range q).filter (fun a : ℕ => a.gcd q = 1))
        ((Finset.range r).filter (fun b : ℕ => b.gcd r = 1))).filter
      (fun ab : ℕ × ℕ =>
        ‖(((ab.1 : ℝ) / (q : ℝ) : ℝ) : UnitAddCircle) -
           (((ab.2 : ℝ) / (r : ℝ) : ℝ) : UnitAddCircle)‖ < Δ)).card
        ≤ ((Finset.product ((Finset.range q).filter (fun a : ℕ => a.gcd q = 1))
            ((Finset.range r).filter (fun b : ℕ => b.gcd r = 1))).card) :=
          Finset.card_le_card (Finset.filter_subset _ _)
    _ = ((Finset.range q).filter (fun a : ℕ => a.gcd q = 1)).card *
        ((Finset.range r).filter (fun b : ℕ => b.gcd r = 1)).card := by simp
    _ = q.totient * r.totient := by
      rw [Nat.totient_eq_card_coprime q, Nat.totient_eq_card_coprime r]
      congr 2
      · ext a
        simp only [Finset.mem_filter, Finset.mem_range]
        constructor <;> intro h <;> simpa [Nat.gcd_comm] using h
      · ext a
        simp only [Finset.mem_filter, Finset.mem_range]
        constructor <;> intro h <;> simpa [Nat.gcd_comm] using h

/-- Each factor `(1 − 1/p)⁻¹`, `p` a prime, is `≥ 1`; so the whole product is `≥ 1`. -/
lemma one_le_inv_prod_primeFactors (N : ℕ) (P : ℕ → Prop) [DecidablePred P] :
    (1 : ℝ) ≤ ∏ p ∈ (Nat.primeFactors N).filter P, (1 - 1 / (p : ℝ))⁻¹ := by
  classical
  refine Finset.one_le_prod₀ ?_
  intro p hp
  have hpp : Nat.Prime p := Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hp).1
  have hp0 : 0 < (p : ℝ) := by exact_mod_cast hpp.pos
  have hle1 : 1 - 1 / (p : ℝ) ≤ 1 := by
    have h0 : 0 ≤ (1 : ℝ) / (p : ℝ) := by positivity
    linarith
  have hpos : 0 < 1 - 1 / (p : ℝ) := by
    have hlt : (1 : ℝ) / (p : ℝ) < 1 := by
      have hp2 : 2 ≤ (p : ℝ) := by exact_mod_cast hpp.two_le
      rw [div_lt_one hp0]
      linarith
    linarith
  rw [one_le_inv₀ hpos]
  exact hle1

/-- The trivial regime `Δ ≥ 1/8`. -/
lemma reduced_pair_window_bound_trivial (q r : ℕ) (Δ : ℝ) (hΔ : 0 ≤ Δ) (hbig : 1 / 8 ≤ Δ) :
    let g : ℕ := q.gcd r
    let L : ℕ := q * r / g
    (((reducedPairs q r Δ).card : ℝ) ≤
      8000 * Δ * (q.totient : ℝ) * (r.totient : ℝ) *
        ∏ p ∈ (Nat.primeFactors (q * r / (g * g))).filter (fun p : ℕ => Δ * (L : ℝ) < (p : ℝ)),
          (1 - 1 / (p : ℝ))⁻¹) := by
  classical
  dsimp
  have hQ : (1 : ℝ) ≤ ∏ p ∈ (Nat.primeFactors (q * r / (q.gcd r * q.gcd r))).filter
      (fun p : ℕ => Δ * ((q * r / q.gcd r : ℕ) : ℝ) < (p : ℝ)),
        (1 - 1 / (p : ℝ))⁻¹ :=
    one_le_inv_prod_primeFactors (q * r / (q.gcd r * q.gcd r))
      (fun p : ℕ => Δ * ((q * r / q.gcd r : ℕ) : ℝ) < (p : ℝ))
  have hc : (((reducedPairs q r Δ).card : ℝ)) ≤ ((q.totient * r.totient : ℕ) : ℝ) := by
    exact_mod_cast reducedPairs_card_le_totient_mul q r Δ
  calc
    (((reducedPairs q r Δ).card : ℝ)) ≤ ((q.totient * r.totient : ℕ) : ℝ) := hc
    _ = (q.totient : ℝ) * (r.totient : ℝ) := by norm_num
    _ ≤ (q.totient : ℝ) * (r.totient : ℝ) * (8000 * Δ) := by
      have ht0 : 0 ≤ (q.totient : ℝ) := by positivity
      have ht1 : 0 ≤ (r.totient : ℝ) := by positivity
      have h8 : (1 : ℝ) ≤ 8000 * Δ := by linarith
      exact le_mul_of_one_le_right (mul_nonneg ht0 ht1) h8
    _ = 8000 * Δ * (q.totient : ℝ) * (r.totient : ℝ) * 1 := by ring
    _ ≤ 8000 * Δ * (q.totient : ℝ) * (r.totient : ℝ) *
        ∏ p ∈ (Nat.primeFactors (q * r / (q.gcd r * q.gcd r))).filter
          (fun p : ℕ => Δ * ((q * r / q.gcd r : ℕ) : ℝ) < (p : ℝ)),
            (1 - 1 / (p : ℝ))⁻¹ := by
      have hbase : 0 ≤ 8000 * Δ * (q.totient : ℝ) * (r.totient : ℝ) := by positivity
      exact mul_le_mul_of_nonneg_left hQ hbase

/-- φ(q)φ(r) = φ(g)·φ(L) with g = gcd q r, L = q·r/g (as naturals). -/
lemma phi_mul_eq_phi_gcd_mul_phi_div (q r : ℕ) (hq : 0 < q) (hr : 0 < r) :
    q.totient * r.totient =
      (q.gcd r).totient * ((q * r / (q.gcd r) : ℕ).totient) := by
  classical
  have hL : q * r / q.gcd r = q.lcm r := by
    calc
      q * r / q.gcd r = q * (r / q.gcd r) := Nat.mul_div_assoc q (Nat.gcd_dvd_right q r)
      _ = q.lcm r := by
        simpa [mul_comm] using (Commons.Data.Nat.mul_div_gcd_eq_lcm q r)
  rw [hL]
  have hφ1 := Commons.NumberTheory.Totient.totient_mul_gcd q r
  have hφ2 := Commons.NumberTheory.Totient.totient_mul_gcd (q.gcd r) (q.lcm r)
  have hgcd : (q.gcd r).gcd (q.lcm r) = q.gcd r :=
    Nat.gcd_eq_left (dvd_trans (Nat.gcd_dvd_left q r) (Nat.dvd_lcm_left q r))
  have hφ2' : Nat.totient (q * r) * Nat.totient (q.gcd r) =
      Nat.totient (q.gcd r) * Nat.totient (q.lcm r) * (q.gcd r) := by
    rw [← Nat.gcd_mul_lcm] at hφ2
    rw [hgcd] at hφ2
    simpa [mul_comm, mul_assoc, mul_left_comm] using hφ2
  have hφ1' : Nat.totient (q * r) * Nat.totient (q.gcd r) =
      Nat.totient q * Nat.totient r * (q.gcd r) := by
    simpa [mul_comm, mul_assoc, mul_left_comm] using hφ1
  have heq : Nat.totient q * Nat.totient r * (q.gcd r) =
      Nat.totient (q.gcd r) * Nat.totient (q.lcm r) * (q.gcd r) := by
    rw [← hφ1', hφ2']
  have hg : 0 < q.gcd r := Nat.gcd_pos_of_pos_left r hq
  apply Nat.mul_left_cancel hg
  simpa [mul_comm, mul_assoc, mul_left_comm] using heq

/-- Same over the reals. -/
lemma phi_mul_eq_phi_gcd_mul_phi_div_real (q r : ℕ) (hq : 0 < q) (hr : 0 < r) :
    (q.totient : ℝ) * (r.totient : ℝ) =
      ((q.gcd r).totient : ℝ) * (((q * r / (q.gcd r) : ℕ).totient : ℝ)) := by
  exact_mod_cast phi_mul_eq_phi_gcd_mul_phi_div q r hq hr

lemma prod_filter_split {α : Type} [CommMonoid α] (s : Finset ℕ) (p : ℕ → Prop) [DecidablePred p]
    (f : ℕ → α) : (∏ x ∈ s, f x) =
      (∏ x ∈ s.filter p, f x) * (∏ x ∈ s.filter (fun y => ¬ p y), f x) := by
  classical
  have hd : Disjoint (s.filter p) (s.filter (fun y : ℕ => ¬ p y)) := by
    rw [Finset.disjoint_left]
    intro x hx hy
    rw [Finset.mem_filter] at hx hy
    exact hy.2 hx.2
  have hun : s = (s.filter p) ∪ (s.filter (fun y : ℕ => ¬ p y)) := by
    ext x
    rw [Finset.mem_union, Finset.mem_filter, Finset.mem_filter]
    by_cases h : p x <;> simp [h]
  calc
    ∏ x ∈ s, f x = ∏ x ∈ ((s.filter p) ∪ (s.filter (fun y : ℕ => ¬ p y))), f x := by
      exact (congrArg (fun t : Finset ℕ => ∏ x ∈ t, f x) hun)
    _ = (∏ x ∈ s.filter p, f x) * (∏ x ∈ s.filter (fun y : ℕ => ¬ p y), f x) :=
      Finset.prod_union hd

/-- φ(q)φ(r) = φ(g)·φ(L) with g = gcd q r, L = q·r/g (as naturals). -/
lemma mul_div_gcd_eq_gcd_mul (q r : ℕ) (hq : 0 < q) :
    q * r / (q.gcd r) = (q.gcd r) * ((q / q.gcd r) * (r / q.gcd r)) := by
  classical
  let g : ℕ := q.gcd r
  let Q : ℕ := q / g
  let R : ℕ := r / g
  have hgpos : 0 < g := Nat.gcd_pos_of_pos_left r hq
  have hqdef : q = g * Q := by
    dsimp [Q, g]
    exact (by
      have hh := Nat.div_mul_cancel (Nat.gcd_dvd_left q r)  -- (q/g)*g = q
      simpa [mul_comm] using hh.symm)
  have hrdef : r = g * R := by
    dsimp [R, g]
    exact (by
      have hh := Nat.div_mul_cancel (Nat.gcd_dvd_right q r)
      simpa [mul_comm] using hh.symm)
  calc
    q * r / (q.gcd r) = q * (r / q.gcd r) := Nat.mul_div_assoc q (Nat.gcd_dvd_right q r)
    _ = (g * Q) * R := by
      have hc := congrArg (fun u : ℕ => u * (r / q.gcd r)) hqdef.symm
      simpa [R, g] using hc.symm
    _ = g * (Q * R) := by rw [mul_assoc]

lemma primeFactors_div_mul_eq (q r : ℕ) (hq : 0 < q) (hr : 0 < r) :
    (q * r / (q.gcd r)).primeFactors =
      (q * r / (q.gcd r * q.gcd r)).primeFactors ∪
        (q.gcd r).primeFactors.filter (fun p : ℕ => ¬ p ∣ q * r / (q.gcd r * q.gcd r)) := by
  classical
  let g : ℕ := q.gcd r
  let QR : ℕ := q * r / (g * g)
  let L : ℕ := q * r / g
  have hgpos : 0 < g := Nat.gcd_pos_of_pos_left r hq
  have hle2 : g * g ≤ q * r := Nat.mul_le_mul (Nat.gcd_le_left r hq) (Nat.gcd_le_right q hr)
  have hle1 : g ≤ q * r := le_trans (Nat.gcd_le_left r hq) (Nat.le_mul_of_pos_right q hr)
  have hQRpos : 0 < QR := by
    dsimp [QR]
    exact Nat.div_pos hle2 (Nat.mul_pos hgpos hgpos)
  have hLpos : 0 < L := by
    dsimp [L]
    exact Nat.div_pos hle1 hgpos
  have hQR2 : (q / q.gcd r) * (r / q.gcd r) = q * r / (g * g) := by
    dsimp [g]
    exact (Nat.div_mul_div_comm (Nat.gcd_dvd_left q r) (Nat.gcd_dvd_right q r))
  have hL_gQR : L = g * QR := by
    calc
      L = q * r / (q.gcd r) := rfl
      _ = g * ((q / q.gcd r) * (r / q.gcd r)) := mul_div_gcd_eq_gcd_mul q r hq
      _ = g * QR := by rw [hQR2]
  have hLQR : QR ∣ L := by
    rw [hL_gQR]
    simpa [mul_comm] using (dvd_mul_right QR g)
  have hgL : g ∣ L := by
    rw [hL_gQR]
    exact dvd_mul_right g QR
  ext p
  constructor
  · intro hpL
    have hpP : p.Prime := (Nat.mem_primeFactors.mp hpL).1
    have hpd : p ∣ L := (Nat.mem_primeFactors.mp hpL).2.1
    have hQor : p ∣ g ∨ p ∣ QR := by
      rw [hL_gQR] at hpd
      exact (hpP.dvd_mul).mp hpd
    rw [Finset.mem_union]
    rcases hQor with hpg | hpQR
    · have hpgpf : p ∈ g.primeFactors := (Nat.mem_primeFactors.mpr ⟨hpP, hpg, ne_of_gt hgpos⟩)
      by_cases hpQR' : p ∣ QR
      · left
        exact (Nat.mem_primeFactors.mpr ⟨hpP, hpQR', ne_of_gt hQRpos⟩)
      · right
        exact Finset.mem_filter.mpr ⟨hpgpf, hpQR'⟩
    · left
      exact (Nat.mem_primeFactors.mpr ⟨hpP, hpQR, ne_of_gt hQRpos⟩)
  · intro hp
    rw [Finset.mem_union] at hp
    rcases hp with hpQR | hshared
    · have hpP : p.Prime := (Nat.mem_primeFactors.mp hpQR).1
      have hpd : p ∣ QR := (Nat.mem_primeFactors.mp hpQR).2.1
      exact (Nat.mem_primeFactors.mpr ⟨hpP, dvd_trans hpd hLQR, ne_of_gt hLpos⟩)
    · have hgpf := (Finset.mem_filter.mp hshared).1
      have hpP : p.Prime := (Nat.mem_primeFactors.mp hgpf).1
      have hpd : p ∣ g := (Nat.mem_primeFactors.mp hgpf).2.1
      exact (Nat.mem_primeFactors.mpr ⟨hpP, dvd_trans hpd hgL, ne_of_gt hLpos⟩)

lemma primeFactors_L_disjoint (q r : ℕ) (hq : 0 < q) (hr : 0 < r) :
    Disjoint (q * r / (q.gcd r * q.gcd r)).primeFactors
      ((q.gcd r).primeFactors.filter (fun p : ℕ => ¬ p ∣ q * r / (q.gcd r * q.gcd r))) := by
  classical
  rw [Finset.disjoint_left]
  intro p hp hqmem
  have hpQR := (Nat.mem_primeFactors.mp hp).2.1
  have hnot := (Finset.mem_filter.mp hqmem).2
  exact hnot hpQR

/-- Euler product: φ(n)/n = ∏_{p | n} (1 − 1/p) over the reals, for 0 < n. -/
lemma totient_div_self_real_prod (n : ℕ) (hn : 0 < n) :
    ((n.totient : ℝ) / (n : ℝ)) = ∏ p ∈ n.primeFactors, (1 - (1 : ℝ) / (p : ℝ)) := by
  have hq : (n.totient : ℚ) / (n : ℚ) = ∏ p ∈ n.primeFactors, (1 - (p : ℚ)⁻¹) := by
    have hf := Nat.totient_eq_mul_prod_factors n
    have hn0 : (n : ℚ) ≠ 0 := by exact_mod_cast (ne_of_gt hn)
    rw [hf]
    field_simp [hn0]
  have hq' := congrArg (fun q : ℚ => (q : ℝ)) hq
  have hr : (n.totient : ℝ) / (n : ℝ) = ∏ p ∈ n.primeFactors, (1 - (p : ℝ)⁻¹) := by
    simpa using hq'
  rw [hr]
  congr 1
  ext p
  simp


/-! ## (F) the fibre formula (real σ-form) -/

lemma pairVal_eq_cong_iff (q r c : ℕ) (hq : 0 < q) (hr : 0 < r)
    (ab : ℕ × ℕ) (hab : ab ∈ redPairs q r)
    (hc : c < q * r / q.gcd r) :
    pairVal q r ab = c ↔
      ((ab.1 * (r / q.gcd r)) % (q * r / q.gcd r) =
        ((ab.2 * (q / q.gcd r) + c) % (q * r / q.gcd r))) := by
  classical
  let L : ℕ := q * r / q.gcd r
  have hpa : ab.1 < q := Finset.mem_range.mp ((redPairs_mem_iff q r ab.1 ab.2).mp hab |>.1)
  have hpb : ab.2 < r := Finset.mem_range.mp ((redPairs_mem_iff q r ab.1 ab.2).mp hab |>.2.1)
  have hpm := pairVal_mod q r hq hr ab hpa hpb
  have hpvL : pairVal q r ab < L := pairVal_lt q r hq hr ab
  have hcL : c < L := by simpa [L] using hc
  constructor
  · intro hc_eq
    rw [hc_eq] at hpm
    exact hpm.symm
  · intro hcong
    have h1 : (ab.2 * (q / q.gcd r) + pairVal q r ab) % L =
        (ab.2 * (q / q.gcd r) + c) % L := by
      rw [hpm]
      simpa [L] using hcong
    have hme : (ab.2 * (q / q.gcd r) + pairVal q r ab) ≡
        (ab.2 * (q / q.gcd r) + c) [MOD L] := h1
    have hme' : pairVal q r ab ≡ c [MOD L] :=
      Nat.ModEq.add_left_cancel' (ab.2 * (q / q.gcd r)) hme
    exact Nat.ModEq.eq_of_lt_of_lt hme' hpvL hcL

/-- fiberCard = the congruence count (c < L) -/
lemma fiberCard_eq_cong (q r c : ℕ) (hq : 0 < q) (hr : 0 < r)
    (hc : c < q * r / q.gcd r) :
    fiberCard q r c =
      ((redPairs q r).filter (fun ab : ℕ × ℕ =>
        ((ab.1 * (r / q.gcd r)) % (q * r / q.gcd r) =
          ((ab.2 * (q / q.gcd r) + c) % (q * r / q.gcd r))))).card := by
  classical
  unfold fiberCard
  congr 1
  apply Finset.filter_congr
  intro ab hab
  exact pairVal_eq_cong_iff q r c hq hr ab hab hc

/-- integer fibre formula (from residue_fiber_formula): Phi·S form -/
lemma fiberCard_eq_PhiS (q r c : ℕ) (hq : 0 < q) (hr : 0 < r) :
    let g : ℕ := q.gcd r
    let M : ℕ := q / g
    let N : ℕ := r / g
    let qq : ℕ := M * N
    let L : ℕ := q * r / g
    let K : ℕ := ∏ p ∈ (Nat.primeFactors g).filter (fun p => ¬ p ∣ qq), p ^ (g.factorization p)
    let Phi : ℕ := ∏ p ∈ Nat.primeFactors qq, (p ^ (g.factorization p)).totient
    let S : ℕ → ℕ := fun e => ∏ p ∈ Nat.primeFactors K,
        if p ∣ e then (p ^ (K.factorization p)).totient
        else p ^ (K.factorization p - 1) * (p - 2)
    (∀ c : ℕ, c < q * r / q.gcd r →
      fiberCard q r c =
        if c.gcd qq = 1 then Phi * S (c % L) else 0) := by
  classical
  intro g M N qq L K Phi S
  intro c hc
  rw [fiberCard_eq_cong q r c hq hr hc]
  have hres := residue_fiber_formula q r c hq hr
  dsimp [g, M, N, qq, L, K, Phi, S] at hres ⊢
  rw [Nat.mod_eq_of_lt hc] at hres ⊢
  exact hres

lemma totient_eq_prod_phi_pow (n : ℕ) (hn : n ≠ 0) :
    n.totient = ∏ p ∈ n.primeFactors, (p ^ (n.factorization p)).totient := by
  classical
  have ht := Commons.NumberTheory.Totient.totient_eq_prod_primeFactors n hn
  calc
    n.totient = ∏ p ∈ n.primeFactors, p ^ (n.factorization p - 1) * (p - 1) := ht
    _ = ∏ p ∈ n.primeFactors, (p ^ (n.factorization p)).totient := by
      refine Finset.prod_congr rfl ?_
      intro p hp
      have hpP : p.Prime := (Nat.mem_primeFactors.mp hp).1
      have hpd : p ∣ n := (Nat.mem_primeFactors.mp hp).2.1
      have hfac : 0 < n.factorization p := hpP.factorization_pos_of_dvd hn hpd
      rw [Nat.totient_prime_pow hpP hfac]

lemma prod_eq_of_eq_one_off (A C : Finset ℕ) (hdisj : Disjoint A C) (f : ℕ → ℕ)
    (hf : ∀ p ∈ C, f p = 1) :
    (∏ p ∈ A ∪ C, f p) = ∏ p ∈ A, f p := by
  classical
  have hC : (∏ p ∈ C, f p) = 1 := Finset.prod_eq_one hf
  calc
    (∏ p ∈ A ∪ C, f p) = (∏ p ∈ A, f p) * (∏ p ∈ C, f p) := Finset.prod_union hdisj
    _ = (∏ p ∈ A, f p) * 1 := by rw [hC]
    _ = ∏ p ∈ A, f p := by rw [mul_one]

lemma pfqq_union_F_eq (g qq : ℕ) (hqq : 0 < qq) :
    (Nat.primeFactors qq) ∪ ((Nat.primeFactors g).filter (fun p : ℕ => ¬ p ∣ qq)) =
      (Nat.primeFactors g) ∪ ((Nat.primeFactors qq) \ (Nat.primeFactors g)) := by
  classical
  ext p
  simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_sdiff]
  have hqqn : qq ≠ 0 := ne_of_gt hqq
  constructor
  · intro h
    rcases h with hpqq | hF
    · by_cases hpg : p ∈ Nat.primeFactors g
      · exact Or.inl hpg
      · exact Or.inr ⟨hpqq, hpg⟩
    · exact Or.inl hF.1
  · intro h
    rcases h with hpg | hpqg
    · by_cases hpd : p ∣ qq
      · left
        have hpp : p.Prime := (Nat.mem_primeFactors.mp hpg).1
        exact (Nat.mem_primeFactors.mpr ⟨hpp, hpd, hqqn⟩)
      · right
        exact ⟨hpg, hpd⟩
    · exact Or.inl hpqg.1

lemma phi_g_eq_Phi_mul_shared (g qq : ℕ) (hg : 0 < g) (hqq : 0 < qq) :
    (∏ p ∈ (Nat.primeFactors g), (p ^ (g.factorization p)).totient) =
      (∏ p ∈ (Nat.primeFactors qq), (p ^ (g.factorization p)).totient) *
        (∏ p ∈ (Nat.primeFactors g).filter (fun p : ℕ => ¬ p ∣ qq), (p ^ (g.factorization p)).totient) := by
  classical
  let F : Finset ℕ := (Nat.primeFactors g).filter (fun p : ℕ => ¬ p ∣ qq)
  let f : ℕ → ℕ := fun p => (p ^ (g.factorization p)).totient
  have hdisj1 : Disjoint (Nat.primeFactors qq) F := by
    rw [Finset.disjoint_left]
    intro p hp hq
    exact (Finset.mem_filter.mp hq).2 ((Nat.mem_primeFactors.mp hp).2.1)
  have hdisj2 : Disjoint (Nat.primeFactors g) ((Nat.primeFactors qq) \ (Nat.primeFactors g)) := by
    rw [Finset.disjoint_left]
    intro p hp hq
    exact (Finset.mem_sdiff.mp hq).2 hp
  have hset : (Nat.primeFactors qq) ∪ F = (Nat.primeFactors g) ∪ ((Nat.primeFactors qq) \ (Nat.primeFactors g)) := by
    simpa [F] using pfqq_union_F_eq g qq hqq
  have hf : ∀ p ∈ (Nat.primeFactors qq) \ (Nat.primeFactors g), f p = 1 := by
    intro p hp
    have hpn : p ∉ Nat.primeFactors g := (Finset.mem_sdiff.mp hp).2
    have hfac0 : g.factorization p = 0 := by
      by_contra h
      have hgt : 0 < g.factorization p := Nat.pos_of_ne_zero h
      have hpp : p.Prime := (Nat.mem_primeFactors.mp (Finset.mem_sdiff.mp hp).1).1
      have hdvd : p ∣ g := (Nat.Prime.dvd_iff_one_le_factorization hpp (ne_of_gt hg)).mpr hgt
      exact hpn (Nat.mem_primeFactors.mpr ⟨hpp, hdvd, (ne_of_gt hg)⟩)
    dsimp [f]
    rw [hfac0]
    norm_num
  calc
    (∏ p ∈ (Nat.primeFactors g), f p)
        = (∏ p ∈ (Nat.primeFactors g) ∪ ((Nat.primeFactors qq) \ (Nat.primeFactors g)), f p) := by
          symm
          exact prod_eq_of_eq_one_off (Nat.primeFactors g)
            ((Nat.primeFactors qq) \ (Nat.primeFactors g)) hdisj2 f hf
    _ = (∏ p ∈ (Nat.primeFactors qq) ∪ F, f p) := by rw [hset]
    _ = (∏ p ∈ (Nat.primeFactors qq), f p) * (∏ p ∈ F, f p) := Finset.prod_union hdisj1
    _ = (∏ p ∈ (Nat.primeFactors qq), (p ^ (g.factorization p)).totient) *
        (∏ p ∈ F, (p ^ (g.factorization p)).totient) := by simp [f]
    _ = (∏ p ∈ (Nat.primeFactors qq), (p ^ (g.factorization p)).totient) *
        (∏ p ∈ (Nat.primeFactors g).filter (fun p : ℕ => ¬ p ∣ qq), (p ^ (g.factorization p)).totient) := by simp [F]

/-- prime factors of K := ∏_{p ∈ F} p^(g.fact p) equal F -/
lemma pfK_eq_F (g qq : ℕ) (hg : 0 < g) :
    (Nat.primeFactors (∏ p ∈ (Nat.primeFactors g).filter (fun p : ℕ => ¬ p ∣ qq),
        p ^ (g.factorization p))) =
      (Nat.primeFactors g).filter (fun p : ℕ => ¬ p ∣ qq) := by
  classical
  let F := (Nat.primeFactors g).filter (fun p : ℕ => ¬ p ∣ qq)
  have hFpos : ∀ p ∈ F, p.Prime := by
    intro p hp
    exact (Nat.mem_primeFactors.mp ((Finset.mem_filter.mp hp).1)).1
  have hKf : ∀ p, ((∏ p ∈ F, p ^ (g.factorization p)).factorization) p =
      if p ∈ F then g.factorization p else 0 := by
    intro p
    exact Commons.Data.Nat.factorization_prod_prime_pow_apply F (fun q => g.factorization q) hFpos p
  have hKz : (∏ p ∈ F, p ^ (g.factorization p)) ≠ 0 := by
    rw [Finset.prod_ne_zero_iff]
    intro p hp
    exact pow_ne_zero _ (hFpos p hp).ne_zero
  ext p
  constructor
  · intro hpK
    rcases (Nat.mem_primeFactors.mp hpK) with ⟨hpp, hdvd, hKnz⟩
    have hKfpos : 0 < (∏ p ∈ F, p ^ (g.factorization p)).factorization p := by
      have h1 : 1 ≤ (∏ p ∈ F, p ^ (g.factorization p)).factorization p :=
        (Nat.Prime.dvd_iff_one_le_factorization hpp hKz).mp hdvd
      omega
    rw [hKf p] at hKfpos
    by_cases hpFin : p ∈ F
    · exact hpFin
    · rw [if_neg hpFin] at hKfpos
      simp at hKfpos
  · intro hpF
    have hpF' : p ∈ F := by simpa [F] using hpF
    rcases (Finset.mem_filter.mp hpF') with ⟨hgm, hpq⟩
    have hpp : p.Prime := (Nat.mem_primeFactors.mp hgm).1
    have hdvdg : p ∣ g := (Nat.mem_primeFactors.mp hgm).2.1
    refine Nat.mem_primeFactors.mpr ⟨hpp, ?_, hKz⟩
    have hpos : 0 < g.factorization p := by
      have h1 : 1 ≤ g.factorization p :=
        (Nat.Prime.dvd_iff_one_le_factorization hpp (ne_of_gt hg)).mp hdvdg
      omega
    have h1 : 1 ≤ (∏ p ∈ F, p ^ (g.factorization p)).factorization p := by
      rw [hKf p, if_pos hpF']
      exact hpos
    exact (Nat.Prime.dvd_iff_one_le_factorization hpp hKz).mpr h1

/-- factorization of K at p ∈ F is g.factorization p -/
lemma K_fact_eq_g (g qq p : ℕ) (hg : 0 < g)
    (hpF : p ∈ (Nat.primeFactors g).filter (fun p : ℕ => ¬ p ∣ qq)) :
    ((∏ p ∈ (Nat.primeFactors g).filter (fun p : ℕ => ¬ p ∣ qq),
        p ^ (g.factorization p)).factorization) p = g.factorization p := by
  classical
  let F := (Nat.primeFactors g).filter (fun p : ℕ => ¬ p ∣ qq)
  have hFpos : ∀ q ∈ F, q.Prime := by
    intro q hq
    exact (Nat.mem_primeFactors.mp (Finset.mem_filter.mp hq).1).1
  have hKf : ((∏ q ∈ F, q ^ (g.factorization q)).factorization) p = if p ∈ F then g.factorization p else 0 :=
    Commons.Data.Nat.factorization_prod_prime_pow_apply F (fun q => g.factorization q) hFpos p
  have hpF' : p ∈ F := by simpa [F] using hpF
  rw [hKf, if_pos hpF']


/-- K := ∏_{p | g, p ∤ qq} p^{ν_p g} -/
def Kpq (g qq : ℕ) : ℕ :=
  ∏ p ∈ (Nat.primeFactors g).filter (fun p : ℕ => ¬ p ∣ qq), p ^ (g.factorization p)

/-- Phi := ∏_{p | qq} φ(p^{ν_p g}) -/
def Phi_pq (g qq : ℕ) : ℕ :=
  ∏ p ∈ Nat.primeFactors qq, (p ^ (g.factorization p)).totient

/-- per-prime real identity: φ(p^γ)·σ_p(x) = inner term (γ = K.fact p = g.fact p) -/
lemma pair_phi_sigma (g qq p x : ℕ) (hg : 0 < g)
    (hpF : p ∈ (Nat.primeFactors g).filter (fun p : ℕ => ¬ p ∣ qq)) :
    (((p ^ (g.factorization p)).totient : ℝ) *
      (if p ∣ x then (1 : ℝ) else (((p : ℝ) - 2) / ((p : ℝ) - 1)))) =
      (((if p ∣ x then (((p ^ ((Kpq g qq).factorization p)).totient : ℕ))
        else (((p ^ ((Kpq g qq).factorization p - 1) * (p - 2) : ℕ)))) : ℕ) : ℝ) := by
  classical
  have hpP : p.Prime := (Nat.mem_primeFactors.mp (Finset.mem_filter.mp hpF).1).1
  have hdvdg : p ∣ g := (Nat.mem_primeFactors.mp (Finset.mem_filter.mp hpF).1).2.1
  have hγ : 0 < g.factorization p := by
    have h1 : 1 ≤ g.factorization p :=
      (Nat.Prime.dvd_iff_one_le_factorization hpP (ne_of_gt hg)).mp hdvdg
    omega
  have hK : (Kpq g qq).factorization p = g.factorization p := by
    dsimp [Kpq]
    exact K_fact_eq_g g qq p hg hpF
  by_cases hpx : p ∣ x
  · rw [if_pos hpx, if_pos hpx]
    simp [hK]
  · rw [if_neg hpx, if_neg hpx]
    have hφ : (p ^ (g.factorization p)).totient = p ^ (g.factorization p - 1) * (p - 1) := by
      rw [Nat.totient_prime_pow hpP hγ]
    rw [hK]
    rw [hφ]
    have hp2nat : 2 ≤ p := hpP.two_le
    have hden : (p : ℝ) - 1 ≠ 0 := by
      have hp2 : 2 ≤ (p : ℝ) := by exact_mod_cast hp2nat
      linarith
    have hsub1 : ((p - 1 : ℕ) : ℝ) = (p : ℝ) - 1 := by
      rw [Nat.cast_sub (by omega : 1 ≤ p)]
      norm_num
    have hsub2 : ((p - 2 : ℕ) : ℝ) = (p : ℝ) - 2 := by
      rw [Nat.cast_sub (by omega : 2 ≤ p)]
      norm_num
    field_simp [hden]
    rw [Nat.cast_mul, Nat.cast_mul]
    rw [hsub1, hsub2]
    ring

/-- Phi·S(x) = φ(g)·∏_{p ∈ shared} σ_p(x) as reals -/
theorem phiS_sigma_real (g qq x : ℕ) (hg : 0 < g) (hqq : 0 < qq) :
    ((Phi_pq g qq * (∏ p ∈ Nat.primeFactors (Kpq g qq),
        if p ∣ x then (p ^ ((Kpq g qq).factorization p)).totient
        else p ^ ((Kpq g qq).factorization p - 1) * (p - 2)) : ℕ) : ℝ) =
      ((g.totient : ℕ) : ℝ) *
        (∏ p ∈ (Nat.primeFactors g).filter (fun p : ℕ => ¬ p ∣ qq),
          (if p ∣ x then (1 : ℝ) else (((p : ℝ) - 2) / ((p : ℝ) - 1)))) := by
  classical
  let F : Finset ℕ := (Nat.primeFactors g).filter (fun p : ℕ => ¬ p ∣ qq)
  let inner : ℕ → ℕ := fun p =>
    if p ∣ x then (p ^ ((Kpq g qq).factorization p)).totient
    else p ^ ((Kpq g qq).factorization p - 1) * (p - 2)
  let phiN : ℕ → ℕ := fun p => (p ^ (g.factorization p)).totient
  have hpfK : (Kpq g qq).primeFactors = F := by
    dsimp [Kpq]
    exact pfK_eq_F g qq hg
  have hgne : g ≠ 0 := ne_of_gt hg
  calc
    ((Phi_pq g qq * (∏ p ∈ Nat.primeFactors (Kpq g qq),
        if p ∣ x then (p ^ ((Kpq g qq).factorization p)).totient
        else p ^ ((Kpq g qq).factorization p - 1) * (p - 2)) : ℕ) : ℝ)
        = (Phi_pq g qq : ℝ) * (∏ p ∈ Nat.primeFactors (Kpq g qq), (inner p : ℝ)) := by
          rw [Nat.cast_mul]
          simp [inner]
    _ = (Phi_pq g qq : ℝ) * (∏ p ∈ F, (inner p : ℝ)) := by
          rw [hpfK]
    _ = (Phi_pq g qq : ℝ) * (∏ p ∈ F, ((phiN p : ℝ) *
          (if p ∣ x then (1 : ℝ) else (((p : ℝ) - 2) / ((p : ℝ) - 1))))) := by
          refine congrArg (fun t : ℝ => (Phi_pq g qq : ℝ) * t) ?_
          refine Finset.prod_congr rfl ?_
          intro p hp
          have hpF : p ∈ (Nat.primeFactors g).filter (fun p : ℕ => ¬ p ∣ qq) := by simpa [F] using hp
          dsimp [inner, phiN]
          exact (pair_phi_sigma g qq p x hg hpF).symm
    _ = (Phi_pq g qq : ℝ) *
          ((∏ p ∈ F, (phiN p : ℝ)) * (∏ p ∈ F, (if p ∣ x then (1 : ℝ) else (((p : ℝ) - 2) / ((p : ℝ) - 1))))) := by
          rw [Finset.prod_mul_distrib]
    _ = ((Phi_pq g qq * (∏ p ∈ F, phiN p) : ℕ) : ℝ) *
            (∏ p ∈ F, (if p ∣ x then (1 : ℝ) else (((p : ℝ) - 2) / ((p : ℝ) - 1)))) := by
          rw [Nat.cast_mul]
          simp
          ring
    _ = ((g.totient : ℕ) : ℝ) *
            (∏ p ∈ F, (if p ∣ x then (1 : ℝ) else (((p : ℝ) - 2) / ((p : ℝ) - 1)))) := by
          congr 1
          rw [totient_eq_prod_phi_pow g hgne]
          dsimp [Phi_pq]
          exact_mod_cast (phi_g_eq_Phi_mul_shared g qq hg hqq).symm
    _ = ((g.totient : ℕ) : ℝ) *
          (∏ p ∈ (Nat.primeFactors g).filter (fun p : ℕ => ¬ p ∣ qq),
            (if p ∣ x then (1 : ℝ) else (((p : ℝ) - 2) / ((p : ℝ) - 1)))) := by
          simp [F]

lemma sigma_mod_eq (p L c : ℕ) (hpL : p ∣ L) :
    (if p ∣ c % L then (1 : ℝ) else (((p : ℝ) - 2) / ((p : ℝ) - 1))) =
      (if p ∣ c then (1 : ℝ) else (((p : ℝ) - 2) / ((p : ℝ) - 1))) := by
  have hiff : p ∣ c % L ↔ p ∣ c := rf_dvd_mod_iff_dvd p L c hpL
  by_cases h : p ∣ c
  · rw [if_pos h]
    rw [if_pos (hiff.mpr h)]
  · rw [if_neg h]
    rw [if_neg (fun h' => h (hiff.mp h'))]

/-- fiberCard in real σ-form (c < L) -/
lemma fiberCard_eq_sigma (q r c : ℕ) (hq : 0 < q) (hr : 0 < r)
    (hc : c < q * r / q.gcd r) :
    let g : ℕ := q.gcd r
    let qq : ℕ := (q / g) * (r / g)
    (fiberCard q r c : ℝ) =
      (if c.gcd qq = 1 then (1 : ℝ) else 0) * ((g.totient : ℕ) : ℝ) *
        (∏ p ∈ (Nat.primeFactors g).filter (fun p : ℕ => ¬ p ∣ qq),
          (if p ∣ c then (1 : ℝ) else (((p : ℝ) - 2) / ((p : ℝ) - 1)))) := by
  classical
  dsimp
  let g : ℕ := q.gcd r
  let qq : ℕ := (q / g) * (r / g)
  let L : ℕ := q * r / g
  have hg : 0 < g := by dsimp [g]; exact Nat.gcd_pos_of_pos_left r hq
  have hqg0 : 0 < q / g := by
    dsimp [g]
    exact Nat.div_pos (Nat.gcd_le_left r hq) (Nat.gcd_pos_of_pos_left r hq)
  have hrg0 : 0 < r / g := by
    dsimp [g]
    exact Nat.div_pos (Nat.gcd_le_right q hr) (Nat.gcd_pos_of_pos_right q hr)
  have hqq : 0 < qq := by
    dsimp [qq]
    exact Nat.mul_pos hqg0 hrg0
  have hcL : c < L := by simpa [L, g] using hc
  have hL_eq : L = g * qq := by
    dsimp [L, qq, g]
    calc
      q * r / (q.gcd r) = (q.gcd r) * ((q / (q.gcd r)) * (r / (q.gcd r))) :=
        mul_div_gcd_eq_gcd_mul q r hq
      _ = (q.gcd r) * ((q / (q.gcd r)) * (r / (q.gcd r))) := rfl
  -- integer identity from the committed residue formula
  have hfc := fiberCard_eq_PhiS q r c hq hr
  have hfcL : fiberCard q r c =
      if c.gcd qq = 1 then
        Phi_pq g qq *
          (∏ p ∈ Nat.primeFactors (Kpq g qq),
            if p ∣ c % L then (p ^ ((Kpq g qq).factorization p)).totient
            else p ^ ((Kpq g qq).factorization p - 1) * (p - 2))
      else 0 := by
    simpa [g, qq, L, Kpq, Phi_pq] using (hfc c hcL)
  let F : Finset ℕ := (Nat.primeFactors g).filter (fun p : ℕ => ¬ p ∣ qq)
  -- hPS with x := c % L
  have hPS := phiS_sigma_real g qq (c % L) hg hqq
  by_cases hgcd : c.gcd qq = 1
  · -- indicator = 1
    have hfib : (fiberCard q r c : ℝ) =
        ((Phi_pq g qq * (∏ p ∈ Nat.primeFactors (Kpq g qq),
            if p ∣ c % L then (p ^ ((Kpq g qq).factorization p)).totient
            else p ^ ((Kpq g qq).factorization p - 1) * (p - 2)) : ℕ) : ℝ) := by
      rw [hfcL, if_pos hgcd]
    have hpsigma : ((Phi_pq g qq * (∏ p ∈ Nat.primeFactors (Kpq g qq),
            if p ∣ c % L then (p ^ ((Kpq g qq).factorization p)).totient
            else p ^ ((Kpq g qq).factorization p - 1) * (p - 2)) : ℕ) : ℝ) =
        ((g.totient : ℕ) : ℝ) *
          (∏ p ∈ F, (if p ∣ c % L then (1 : ℝ) else (((p : ℝ) - 2) / ((p : ℝ) - 1)))) := by
      simpa [F] using hPS
    have hred : ((g.totient : ℕ) : ℝ) *
          (∏ p ∈ F, (if p ∣ c % L then (1 : ℝ) else (((p : ℝ) - 2) / ((p : ℝ) - 1)))) =
        ((g.totient : ℕ) : ℝ) *
          (∏ p ∈ F, (if p ∣ c then (1 : ℝ) else (((p : ℝ) - 2) / ((p : ℝ) - 1)))) := by
      refine congrArg (fun t : ℝ => ((g.totient : ℕ) : ℝ) * t) ?_
      refine Finset.prod_congr rfl ?_
      intro p hpF
      have hpg : p ∣ g := (Nat.mem_primeFactors.mp (Finset.mem_filter.mp hpF).1).2.1
      have hpL : p ∣ L := by
        rw [hL_eq]
        exact dvd_mul_of_dvd_left hpg qq
      exact sigma_mod_eq p L c hpL
    calc
      (fiberCard q r c : ℝ) = ((Phi_pq g qq * (∏ p ∈ Nat.primeFactors (Kpq g qq),
            if p ∣ c % L then (p ^ ((Kpq g qq).factorization p)).totient
            else p ^ ((Kpq g qq).factorization p - 1) * (p - 2)) : ℕ) : ℝ) := hfib
      _ = ((g.totient : ℕ) : ℝ) *
          (∏ p ∈ F, (if p ∣ c % L then (1 : ℝ) else (((p : ℝ) - 2) / ((p : ℝ) - 1)))) := hpsigma
      _ = ((g.totient : ℕ) : ℝ) *
          (∏ p ∈ F, (if p ∣ c then (1 : ℝ) else (((p : ℝ) - 2) / ((p : ℝ) - 1)))) := hred
      _ = (if c.gcd qq = 1 then (1 : ℝ) else 0) * ((g.totient : ℕ) : ℝ) *
          (∏ p ∈ (Nat.primeFactors g).filter (fun p : ℕ => ¬ p ∣ qq),
            (if p ∣ c then (1 : ℝ) else (((p : ℝ) - 2) / ((p : ℝ) - 1)))) := by
          simp [F, hgcd]
  · have hfib0 : (fiberCard q r c : ℝ) = 0 := by
      rw [hfcL, if_neg hgcd]
      norm_num
    rw [hfib0, if_neg hgcd]
    simp

/-! ## Window decomposition: count = 2·φ(g)·(σ-window sum) -/

lemma dvd_sub_iff_dvd (p L c : ℕ) (hpL : p ∣ L) (hc : c ≤ L) :
    p ∣ L - c ↔ p ∣ c := by
  constructor
  · intro h
    have hsub0 : (L - c) ≡ 0 [MOD p] := by rw [Nat.ModEq]; exact Nat.mod_eq_zero_of_dvd h
    have hL0 : L ≡ 0 [MOD p] := by rw [Nat.ModEq]; exact Nat.mod_eq_zero_of_dvd hpL
    have hLc : L ≡ c [MOD p] := by
      calc
        L ≡ (L - c) + c [MOD p] := by rw [Nat.sub_add_cancel hc]
        _ ≡ 0 + c [MOD p] := Nat.ModEq.add hsub0 (Nat.ModEq.refl c)
        _ ≡ c [MOD p] := by rw [Nat.zero_add]
    have hc0 : c ≡ 0 [MOD p] := hLc.symm.trans hL0
    have hcmod : c % p = 0 := by simpa [Nat.ModEq] using hc0
    exact Nat.dvd_iff_mod_eq_zero.mpr hcmod
  · intro h
    have hc0 : c ≡ 0 [MOD p] := by rw [Nat.ModEq]; exact Nat.mod_eq_zero_of_dvd h
    have hL0 : L ≡ 0 [MOD p] := by rw [Nat.ModEq]; exact Nat.mod_eq_zero_of_dvd hpL
    have hcL : c ≡ L [MOD p] := hc0.trans hL0.symm
    exact (Nat.modEq_iff_dvd' hc).mp hcL

/-- σ_p(L−c) = σ_p(c) when p | L and c ≤ L -/
lemma sigma_symm (p L c : ℕ) (hpL : p ∣ L) (hc : c ≤ L) :
    (if p ∣ L - c then (1 : ℝ) else (((p : ℝ) - 2) / ((p : ℝ) - 1))) =
      (if p ∣ c then (1 : ℝ) else (((p : ℝ) - 2) / ((p : ℝ) - 1))) := by
  have hiff := dvd_sub_iff_dvd p L c hpL hc
  by_cases h : p ∣ c
  · rw [if_pos h]
    rw [if_pos (hiff.mpr h)]
  · rw [if_neg h]
    rw [if_neg (fun h' => h (hiff.mp h'))]

/-- coprime indicator symmetric: [gcd(L−c,QQ)=1] = [gcd(c,QQ)=1] when QQ | L, c ≤ L -/
lemma copr_symm (L QQ c : ℕ) (hL : QQ ≠ 0) (hQQL : QQ ∣ L) (hc : c ≤ L) :
    (if (L - c).gcd QQ = 1 then (1 : ℝ) else 0) =
      (if c.gcd QQ = 1 then (1 : ℝ) else 0) := by
  have h1 : (L - c).gcd QQ = 1 ↔ c.gcd QQ = 1 := by
    rw [← Nat.coprime_iff_gcd_eq_one (m := L - c) (n := QQ),
        ← Nat.coprime_iff_gcd_eq_one (m := c) (n := QQ)]
    have hb1 : (L - c).Coprime QQ ↔ ∀ p ∈ QQ.primeFactors, ¬ p ∣ L - c := by
      exact Commons.NumberTheory.Nat.coprime_iff_forall_primeFactors_not_dvd hL
    have hb2 : c.Coprime QQ ↔ ∀ p ∈ QQ.primeFactors, ¬ p ∣ c := by
      exact Commons.NumberTheory.Nat.coprime_iff_forall_primeFactors_not_dvd hL
    rw [hb1, hb2]
    apply forall_congr'
    intro p
    apply imp_congr_right
    intro hpQQ
    have hpd : p ∣ QQ := (Nat.mem_primeFactors.mp hpQQ).2.1
    rw [dvd_sub_iff_dvd p L c (dvd_trans hpd hQQL) hc]
  by_cases h : (L - c).gcd QQ = 1
  · rw [if_pos h, if_pos (h1.mp h)]
  · rw [if_neg h, if_neg (fun h' => h (h1.mpr h'))]

/-- w-form symmetry: (ind·φ(g)·∏σ)(L−c) = (ind·φ(g)·∏σ)(c) -/
lemma sigw_symm (g QQ L c : ℕ) (hg : 0 < g) (hQQ : 0 < QQ)
    (hgL : g ∣ L) (hQQL : QQ ∣ L) (hc : c ≤ L) :
    (if (L - c).gcd QQ = 1 then (1 : ℝ) else 0) * ((g.totient : ℕ) : ℝ) *
        (∏ p ∈ (Nat.primeFactors g).filter (fun p : ℕ => ¬ p ∣ QQ),
          (if p ∣ L - c then (1 : ℝ) else (((p : ℝ) - 2) / ((p : ℝ) - 1)))) =
      (if c.gcd QQ = 1 then (1 : ℝ) else 0) * ((g.totient : ℕ) : ℝ) *
        (∏ p ∈ (Nat.primeFactors g).filter (fun p : ℕ => ¬ p ∣ QQ),
          (if p ∣ c then (1 : ℝ) else (((p : ℝ) - 2) / ((p : ℝ) - 1)))) := by
  classical
  rw [copr_symm L QQ c hQQ.ne' hQQL hc]
  refine congrArg (fun t : ℝ =>
    (if c.gcd QQ = 1 then (1 : ℝ) else 0) * ((g.totient : ℕ) : ℝ) * t) ?_
  refine Finset.prod_congr rfl ?_
  intro p hp
  have hpg : p ∈ Nat.primeFactors g := (Finset.mem_filter.mp hp).1
  have hpd : p ∣ g := (Nat.mem_primeFactors.mp hpg).2.1
  have hpL : p ∣ L := dvd_trans hpd hgL
  exact sigma_symm p L c hpL hc

lemma ceil_sub_one_lt (Y : ℝ) (hY : 0 < Y) : (((Nat.ceil Y - 1 : ℕ) : ℝ)) < Y := by
  have hceilpos : 0 < Nat.ceil Y := (Nat.ceil_pos).mpr hY
  have hcast : (((Nat.ceil Y - 1 : ℕ) : ℝ)) = (Nat.ceil Y : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ Nat.ceil Y)]
    norm_num
  have h1 : (Nat.ceil Y : ℝ) < Y + 1 := Nat.ceil_lt_add_one (le_of_lt hY)
  rw [hcast]
  linarith

/-- Y ≤ (⌈Y⌉−1 : ℝ) + 1 -/
lemma ceil_sub_one_le (Y : ℝ) : Y ≤ (((Nat.ceil Y - 1 : ℕ) : ℝ)) + 1 := by
  have hge : Y ≤ (Nat.ceil Y : ℝ) := Nat.le_ceil Y
  by_cases hp : 1 ≤ Nat.ceil Y
  · have hsucc : (Nat.ceil Y - 1) + 1 = Nat.ceil Y := Nat.sub_add_cancel hp
    have hcast : (((Nat.ceil Y - 1 : ℕ) : ℝ)) + 1 = (Nat.ceil Y : ℝ) := by
      calc
        (((Nat.ceil Y - 1 : ℕ) : ℝ)) + 1 = ((Nat.ceil Y - 1 + 1 : ℕ) : ℝ) := by norm_num
        _ = (Nat.ceil Y : ℝ) := by exact congrArg (fun n : ℕ => (n : ℝ)) hsucc
    rw [hcast]
    exact hge
  · have h0 : Nat.ceil Y = 0 := by omega
    have hY0 : Y ≤ 0 := by simpa [h0] using hge
    have hrhs : (((Nat.ceil Y - 1 : ℕ) : ℝ)) + 1 = 1 := by simp [h0]
    rw [hrhs]
    linarith

/-- naturals with (c:ℝ) < Y are exactly c ≤ ⌈Y⌉−1 (for Y > 0) -/
lemma nat_lt_Y_iff (Y : ℝ) (hY : 0 < Y) (c : ℕ) :
    (c : ℝ) < Y ↔ c ≤ Nat.ceil Y - 1 := by
  have hceilpos : 0 < Nat.ceil Y := (Nat.ceil_pos).mpr hY
  constructor
  · intro h
    have hc : c < Nat.ceil Y := Nat.lt_ceil.mpr h
    omega
  · intro h
    have hc : c < Nat.ceil Y := by omega
    exact Nat.lt_ceil.mp hc

lemma sum_if_or_split (L : ℕ) (P Q : ℕ → Prop) [DecidablePred P] [DecidablePred Q]
    (f : ℕ → ℝ) :
    (∑ c ∈ Finset.range L, (if P c ∨ Q c then f c else 0)) =
      (∑ c ∈ (Finset.range L).filter P, f c) +
      (∑ c ∈ (Finset.range L).filter (fun c => Q c ∧ ¬ P c), f c) := by
  classical
  calc
    (∑ c ∈ Finset.range L, (if P c ∨ Q c then f c else 0))
        = (∑ c ∈ (Finset.range L).filter (fun c => P c ∨ Q c), f c) := by
          rw [Finset.sum_filter]
    _ = (∑ c ∈ (Finset.range L).filter (fun c => P c ∨ Q c), f c) := rfl
    _ = (∑ c ∈ (Finset.range L).filter P, f c) +
        (∑ c ∈ (Finset.range L).filter (fun c => Q c ∧ ¬ P c), f c) := by
          -- filter (P∨Q) = filter P ∪ filter(Q∧¬P), disjoint
          let s : Finset ℕ := Finset.range L
          have h1 : (s.filter (fun c => P c ∨ Q c)) = (s.filter P) ∪ (s.filter (fun c => Q c ∧ ¬ P c)) := by
            ext c
            simp only [Finset.mem_filter, Finset.mem_union]
            by_cases hP : P c <;> simp [hP, and_comm, and_left_comm, and_assoc]
          have hd : Disjoint (s.filter P) (s.filter (fun c => Q c ∧ ¬ P c)) := by
            rw [Finset.disjoint_left]
            intro c hc1 hc2
            exact (Finset.mem_filter.mp hc2).2.2 (Finset.mem_filter.mp hc1).2
          calc
            (∑ c ∈ (s.filter (fun c => P c ∨ Q c)), f c)
                = ∑ c ∈ (s.filter P) ∪ (s.filter (fun c => Q c ∧ ¬ P c)), f c := by rw [h1]
            _ = (∑ c ∈ s.filter P, f c) + (∑ c ∈ s.filter (fun c => Q c ∧ ¬ P c), f c) :=
                Finset.sum_union hd

/-- count expressed as the real sum over the window -/
lemma count_real_window (q r : ℕ) (hq : 0 < q) (hr : 0 < r)
    (Δ : ℝ) (hΔle : 0 ≤ Δ) (hΔ12 : Δ < 1 / 2) :
    ((((Finset.product ((Finset.range q).filter (fun a : ℕ => a.gcd q = 1))
        ((Finset.range r).filter (fun b : ℕ => b.gcd r = 1))).filter
      (fun ab : ℕ × ℕ =>
        ‖(((ab.1 : ℝ) / (q : ℝ) : ℝ) : UnitAddCircle) -
           (((ab.2 : ℝ) / (r : ℝ) : ℝ) : UnitAddCircle)‖ < Δ)).card : ℝ)) =
      ∑ c ∈ Finset.range (q * r / q.gcd r),
        (if windowPred q r Δ c then (fiberCard q r c : ℝ) else 0) := by
  classical
  have hc := count_eq_window_sum q r hq hr Δ hΔle hΔ12
  have hsets : ((Finset.product ((Finset.range q).filter (fun a : ℕ => a.gcd q = 1))
        ((Finset.range r).filter (fun b : ℕ => b.gcd r = 1))).filter
      (fun ab : ℕ × ℕ =>
        ‖(((ab.1 : ℝ) / (q : ℝ) : ℝ) : UnitAddCircle) -
           (((ab.2 : ℝ) / (r : ℝ) : ℝ) : UnitAddCircle)‖ < Δ)) =
      (redPairs q r).filter (fun ab : ℕ × ℕ => counted q r Δ ab) := by
    ext ab
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range]
    simp [redPairs, counted]
  calc
    ((((Finset.product ((Finset.range q).filter (fun a : ℕ => a.gcd q = 1))
        ((Finset.range r).filter (fun b : ℕ => b.gcd r = 1))).filter
      (fun ab : ℕ × ℕ =>
        ‖(((ab.1 : ℝ) / (q : ℝ) : ℝ) : UnitAddCircle) -
           (((ab.2 : ℝ) / (r : ℝ) : ℝ) : UnitAddCircle)‖ < Δ)).card : ℕ) : ℝ)
        = ((((redPairs q r).filter (fun ab : ℕ × ℕ => counted q r Δ ab)).card : ℕ) : ℝ) := by
          rw [hsets]
    _ = ((∑ c ∈ Finset.range (q * r / q.gcd r),
          (if windowPred q r Δ c then fiberCard q r c else 0) : ℕ) : ℝ) := by
          rw [hc]
    _ = ∑ c ∈ Finset.range (q * r / q.gcd r),
          (if windowPred q r Δ c then (fiberCard q r c : ℝ) else 0) := by
          simp

lemma window1_filter_eq (Y : ℝ) (L : ℕ) (hY : 0 < Y) (hYL : Nat.ceil Y - 1 < L) :
    ((Finset.range L).filter (fun c : ℕ => (c : ℝ) < Y)) =
      Finset.Icc 0 (Nat.ceil Y - 1) := by
  classical
  ext c
  rw [Finset.mem_filter, Finset.mem_Icc]
  constructor
  · intro h
    exact ⟨by omega, (nat_lt_Y_iff Y hY c).mp h.2⟩
  · intro h
    have hclt : c < L := by
      have hcN : c ≤ Nat.ceil Y - 1 := h.2
      omega
    exact ⟨Finset.mem_range.mpr hclt, (nat_lt_Y_iff Y hY c).mpr h.2⟩

/-- second window is the image of Icc 1 N under d ↦ L−d -/
lemma window2_image_eq (Y : ℝ) (L : ℕ) (hY : 0 < Y)
    (hYL2 : 2 * Y ≤ (L : ℝ)) :
    ((Finset.range L).filter (fun c : ℕ => ¬ (c : ℝ) < Y ∧ (L : ℝ) - (c : ℝ) < Y)) =
      (Finset.Icc 1 (Nat.ceil Y - 1)).image (fun d : ℕ => L - d) := by
  classical
  ext c
  constructor
  · intro h
    rcases (Finset.mem_filter.mp h) with ⟨hcL, hrest⟩
    rw [Finset.mem_image]
    let d : ℕ := L - c
    have hcL' : c < L := Finset.mem_range.mp hcL
    have hcLe : c ≤ L := le_of_lt hcL'
    have hcast : ((L - c : ℕ) : ℝ) = (L : ℝ) - (c : ℝ) := by
      rw [Nat.cast_sub hcLe]
    have h1 : (d : ℝ) < Y := by
      dsimp [d]
      simpa [hcast] using hrest.2
    refine ⟨d, ?_, ?_⟩
    · exact Finset.mem_Icc.mpr ⟨(by omega), (nat_lt_Y_iff Y hY d).mp h1⟩
    · dsimp [d]
      exact Nat.sub_sub_self hcLe
  · intro h
    rcases (Finset.mem_image.mp h) with ⟨d, hdmem, hd_eq⟩
    have hd : d ∈ Finset.Icc 1 (Nat.ceil Y - 1) := hdmem
    have hd1 : 1 ≤ d := (Finset.mem_Icc.mp hd).1
    have hdN : d ≤ Nat.ceil Y - 1 := (Finset.mem_Icc.mp hd).2
    have hNltL : Nat.ceil Y - 1 < L := by
      have hYltL : Y < (L : ℝ) := by
        have : 2 * Y ≤ (L : ℝ) := hYL2
        nlinarith
      exact_mod_cast (lt_trans (ceil_sub_one_lt Y hY) hYltL)
    have hdle : d ≤ L := by
      have hdN' : d ≤ Nat.ceil Y - 1 := hdN
      have hNltL' : Nat.ceil Y - 1 < L := hNltL
      omega
    have hcast : ((L - d : ℕ) : ℝ) = (L : ℝ) - (d : ℝ) := by
      rw [Nat.cast_sub hdle]
    have hdY : (d : ℝ) < Y := lt_of_le_of_lt (by exact_mod_cast hdN) (ceil_sub_one_lt Y hY)
    rw [← hd_eq]
    rw [Finset.mem_filter]
    constructor
    · exact Finset.mem_range.mpr (by
        have hd1' : 1 ≤ d := hd1
        omega)
    · constructor
      · intro hlt
        have hlt' : (L : ℝ) - (d : ℝ) < Y := by rwa [hcast] at hlt
        linarith
      · have hq1 : (L : ℝ) - ((L : ℝ) - (d : ℝ)) = (d : ℝ) := by ring
        have hq : (L : ℝ) - ((L - d : ℕ) : ℝ) < Y := by
          rw [hcast, hq1]
          exact hdY
        simpa using hq

/-- L = g·qq -/
lemma L_eq_g_mul_qq (q r : ℕ) (hq : 0 < q) :
    q * r / q.gcd r = q.gcd r * ((q / q.gcd r) * (r / q.gcd r)) :=
  mul_div_gcd_eq_gcd_mul q r hq

lemma fiberCard_symm (q r c : ℕ) (hq : 0 < q) (hr : 0 < r)
    (hc1 : 1 ≤ c) (hcL : c < q * r / q.gcd r) :
    (fiberCard q r (q * r / q.gcd r - c) : ℝ) = (fiberCard q r c : ℝ) := by
  classical
  let g : ℕ := q.gcd r
  let qq : ℕ := (q / g) * (r / g)
  let L : ℕ := q * r / g
  have hg : 0 < g := by dsimp [g]; exact Nat.gcd_pos_of_pos_left r hq
  have hqq : 0 < qq := by
    dsimp [qq, g]
    exact Nat.mul_pos (Nat.div_pos (Nat.gcd_le_left r hq) (Nat.gcd_pos_of_pos_left r hq))
      (Nat.div_pos (Nat.gcd_le_right q hr) (Nat.gcd_pos_of_pos_right q hr))
  have hcL' : c < L := by simpa [L, g] using hcL
  have hcLe : c ≤ L := le_of_lt hcL'
  have hLcL : L - c < L := by
    have hc1' : 1 ≤ c := hc1
    omega
  have hLe : L = g * qq := by
    dsimp [L, qq, g]
    exact L_eq_g_mul_qq q r hq
  have hgL : g ∣ L := by
    rw [hLe]
    exact dvd_mul_right g qq
  have hqql : qq ∣ L := by
    rw [hLe]
    exact dvd_mul_left qq g
  have harg1 : L - c < q * r / q.gcd r := by simpa [L, g] using hLcL
  have harg2 : c < q * r / q.gcd r := by simpa [L, g] using hcL'
  have h1 := fiberCard_eq_sigma q r (L - c) hq hr harg1
  have h2 := fiberCard_eq_sigma q r c hq hr harg2
  have hs := sigw_symm g qq L c hg hqq hgL hqql hcLe
  have hwL : (fiberCard q r (L - c) : ℝ) =
      (if (L - c).gcd qq = 1 then (1 : ℝ) else 0) * ((g.totient : ℕ) : ℝ) *
        (∏ p ∈ (Nat.primeFactors g).filter (fun p : ℕ => ¬ p ∣ qq),
          (if p ∣ L - c then (1 : ℝ) else (((p : ℝ) - 2) / ((p : ℝ) - 1)))) := by
    simpa [g, qq] using h1
  have hwc : (fiberCard q r c : ℝ) =
      (if c.gcd qq = 1 then (1 : ℝ) else 0) * ((g.totient : ℕ) : ℝ) *
        (∏ p ∈ (Nat.primeFactors g).filter (fun p : ℕ => ¬ p ∣ qq),
          (if p ∣ c then (1 : ℝ) else (((p : ℝ) - 2) / ((p : ℝ) - 1)))) := by
    simpa [g, qq] using h2
  have hws : (if (L - c).gcd qq = 1 then (1 : ℝ) else 0) * ((g.totient : ℕ) : ℝ) *
        (∏ p ∈ (Nat.primeFactors g).filter (fun p : ℕ => ¬ p ∣ qq),
          (if p ∣ L - c then (1 : ℝ) else (((p : ℝ) - 2) / ((p : ℝ) - 1)))) =
      (if c.gcd qq = 1 then (1 : ℝ) else 0) * ((g.totient : ℕ) : ℝ) *
        (∏ p ∈ (Nat.primeFactors g).filter (fun p : ℕ => ¬ p ∣ qq),
          (if p ∣ c then (1 : ℝ) else (((p : ℝ) - 2) / ((p : ℝ) - 1)))) := by
    simpa [g, qq] using hs
  calc
    (fiberCard q r (q * r / q.gcd r - c) : ℝ)
        = (fiberCard q r (L - c) : ℝ) := by simp [L, g]
    _ = (if (L - c).gcd qq = 1 then (1 : ℝ) else 0) * ((g.totient : ℕ) : ℝ) *
        (∏ p ∈ (Nat.primeFactors g).filter (fun p : ℕ => ¬ p ∣ qq),
          (if p ∣ L - c then (1 : ℝ) else (((p : ℝ) - 2) / ((p : ℝ) - 1)))) := hwL
    _ = (if c.gcd qq = 1 then (1 : ℝ) else 0) * ((g.totient : ℕ) : ℝ) *
        (∏ p ∈ (Nat.primeFactors g).filter (fun p : ℕ => ¬ p ∣ qq),
          (if p ∣ c then (1 : ℝ) else (((p : ℝ) - 2) / ((p : ℝ) - 1)))) := hws
    _ = (fiberCard q r c : ℝ) := hwc.symm

lemma count_sigma_window (q r : ℕ) (hq : 0 < q) (hr : 0 < r) (hqr : q ≠ r)
    (Δ : ℝ) (hΔpos : 0 < Δ) (hΔs : Δ < 1 / 8) :
    let g : ℕ := q.gcd r
    let qq : ℕ := (q / g) * (r / g)
    let L : ℕ := q * r / g
    let Y : ℝ := Δ * (L : ℝ)
    ((((Finset.product ((Finset.range q).filter (fun a : ℕ => a.gcd q = 1))
        ((Finset.range r).filter (fun b : ℕ => b.gcd r = 1))).filter
      (fun ab : ℕ × ℕ =>
        ‖(((ab.1 : ℝ) / (q : ℝ) : ℝ) : UnitAddCircle) -
           (((ab.2 : ℝ) / (r : ℝ) : ℝ) : UnitAddCircle)‖ < Δ)).card : ℝ)) =
      2 * ((g.totient : ℕ) : ℝ) *
        (∑ c ∈ (Finset.Icc 1 (Nat.ceil Y - 1)).filter (fun c : ℕ => c.gcd qq = 1),
          (∏ p ∈ (Nat.primeFactors g).filter (fun p : ℕ => ¬ p ∣ qq),
            if p ∣ c then (1 : ℝ) else (((p : ℝ) - 2) / ((p : ℝ) - 1)))) := by
  classical
  dsimp
  let g : ℕ := q.gcd r
  let qq : ℕ := (q / g) * (r / g)
  let L : ℕ := q * r / g
  let Y : ℝ := Δ * (L : ℝ)
  let N : ℕ := Nat.ceil Y - 1
  let fc : ℕ → ℝ := fun c => (fiberCard q r c : ℝ)
  let sigma : ℕ → ℕ → ℝ := fun p c => if p ∣ c then (1 : ℝ) else (((p : ℝ) - 2) / ((p : ℝ) - 1))
  let shared : Finset ℕ := (Nat.primeFactors g).filter (fun p : ℕ => ¬ p ∣ qq)
  let w : ℕ → ℝ := fun c => (if c.gcd qq = 1 then (1 : ℝ) else 0) * ((g.totient : ℕ) : ℝ) *
    (∏ p ∈ shared, sigma p c)
  have hg : 0 < g := by dsimp [g]; exact Nat.gcd_pos_of_pos_left r hq
  have hqq : 0 < qq := by
    dsimp [qq, g]
    exact Nat.mul_pos (Nat.div_pos (Nat.gcd_le_left r hq) (Nat.gcd_pos_of_pos_left r hq))
      (Nat.div_pos (Nat.gcd_le_right q hr) (Nat.gcd_pos_of_pos_right q hr))
  have hL : 0 < L := by dsimp [L]; exact Lpos q r hq hr
  have hY : 0 < Y := by
    dsimp [Y]
    have hLposR : 0 < (L : ℝ) := by exact_mod_cast hL
    exact mul_pos hΔpos hLposR
  have hYL2 : 2 * Y ≤ (L : ℝ) := by
    dsimp [Y]
    have hLposR : 0 < (L : ℝ) := by exact_mod_cast hL
    have hD2 : 2 * Δ ≤ 1 := by linarith
    have hmul : (2 * Δ) * (L : ℝ) ≤ (L : ℝ) := by
      calc
        (2 * Δ) * (L : ℝ) ≤ 1 * (L : ℝ) := by
          exact mul_le_mul_of_nonneg_right hD2 (by exact_mod_cast (le_of_lt hL))
        _ = (L : ℝ) := by ring
    convert hmul using 1 <;> ring
  have hNltL : N < L := by
    dsimp [N]
    have h1 : ((Nat.ceil Y - 1 : ℕ) : ℝ) < Y := ceil_sub_one_lt Y hY
    have hYL : Y < (L : ℝ) := by
      have hLpos : 0 < (L : ℝ) := by exact_mod_cast hL
      nlinarith
    exact_mod_cast (lt_trans h1 hYL)
  -- count into windows
  have hΔle : 0 ≤ Δ := le_of_lt hΔpos
  have hΔ12 : Δ < 1 / 2 := by linarith
  have hcw := count_real_window q r hq hr Δ hΔle hΔ12
  have hwp : ∀ c : ℕ, windowPred q r Δ c ↔ ((c : ℝ) < Y ∨ (L : ℝ) - (c : ℝ) < Y) := by
    intro c
    simp [windowPred, Y, L, g]
  -- split the sum
  let P1 : ℕ → Prop := fun c => (c : ℝ) < Y
  let P2 : ℕ → Prop := fun c => (L : ℝ) - (c : ℝ) < Y
  have hsum : (∑ c ∈ Finset.range L, (if windowPred q r Δ c then fc c else 0)) =
      (∑ c ∈ (Finset.range L).filter P1, fc c) +
      (∑ c ∈ (Finset.range L).filter (fun c => P2 c ∧ ¬ P1 c), fc c) := by
    rw [← sum_if_or_split L P1 P2 fc]
    refine Finset.sum_congr rfl ?_
    intro c hc
    by_cases hw : windowPred q r Δ c
    · rw [if_pos hw]
      rw [if_pos ((hwp c).mp hw)]
    · rw [if_neg hw]
      rw [if_neg (fun h => hw ((hwp c).mpr h))]
  have hW1 : (∑ c ∈ (Finset.range L).filter P1, fc c) =
      (∑ c ∈ Finset.Icc 0 N, fc c) := by
    rw [window1_filter_eq Y L hY hNltL]
  have hW1split : (∑ c ∈ Finset.Icc 0 N, fc c) = fc 0 + (∑ c ∈ Finset.Icc 1 N, fc c) := by
    have hI : Finset.Icc 0 N = insert 0 (Finset.Icc 1 N) := by
      ext c
      rw [Finset.mem_Icc, Finset.mem_insert, Finset.mem_Icc]
      constructor
      · intro h
        by_cases hc0 : c = 0
        · exact Or.inl hc0
        · exact Or.inr ⟨by omega, h.2⟩
      · intro h
        rcases h with h | h
        · subst c
          omega
        · exact ⟨by omega, h.2⟩
    have hnotmem : 0 ∉ Finset.Icc 1 N := by
      intro h
      rw [Finset.mem_Icc] at h
      omega
    have hsi := Finset.sum_insert (s := Finset.Icc 1 N) (a := 0) (f := fc) hnotmem
    rw [hI, hsi]
  have hW2img : (∑ c ∈ (Finset.range L).filter (fun c => P2 c ∧ ¬ P1 c), fc c) =
      (∑ d ∈ Finset.Icc 1 N, fc (L - d)) := by
    have hset : ((Finset.range L).filter (fun c : ℕ => P2 c ∧ ¬ P1 c)) =
        (Finset.Icc 1 N).image (fun d : ℕ => L - d) := by
      have hre : ((Finset.range L).filter (fun c : ℕ => ¬ P1 c ∧ P2 c)) =
          ((Finset.range L).filter (fun c : ℕ => P2 c ∧ ¬ P1 c)) := by
        apply Finset.filter_congr
        intro c hc
        exact Iff.intro (fun h => ⟨h.2, h.1⟩) (fun h => ⟨h.2, h.1⟩)
      have hwi := window2_image_eq Y L hY hYL2
      have hwi2 : ((Finset.range L).filter (fun c : ℕ => ¬ P1 c ∧ P2 c)) =
          (Finset.Icc 1 N).image (fun d : ℕ => L - d) := by
        simpa [P1, P2] using hwi
      rw [← hre]
      exact hwi2
    have hInj : Set.InjOn (fun d : ℕ => L - d) ↑(Finset.Icc 1 N) := by
      intro x hx y hy h
      have hxN : x ≤ N := (Finset.mem_Icc.mp hx).2
      have hyN : y ≤ N := (Finset.mem_Icc.mp hy).2
      have hxL : x ≤ L := le_trans hxN (le_of_lt hNltL)
      have hyL : y ≤ L := le_trans hyN (le_of_lt hNltL)
      calc
        x = L - (L - x) := (Nat.sub_sub_self hxL).symm
        _ = L - (L - y) := congrArg (fun t : ℕ => L - t) h
        _ = y := Nat.sub_sub_self hyL
    rw [hset, Finset.sum_image hInj]
  have hW1w : (∑ c ∈ Finset.Icc 1 N, fc c) = (∑ c ∈ Finset.Icc 1 N, w c) := by
    refine Finset.sum_congr rfl ?_
    intro c hc
    have hcN : c ≤ N := (Finset.mem_Icc.mp hc).2
    have hcL' : c < L := by have h1 : N < L := hNltL; omega
    dsimp [fc, w, shared, sigma]
    exact fiberCard_eq_sigma q r c hq hr hcL'
  have hW2w : (∑ d ∈ Finset.Icc 1 N, fc (L - d)) = (∑ d ∈ Finset.Icc 1 N, w d) := by
    calc
      (∑ d ∈ Finset.Icc 1 N, fc (L - d)) = (∑ d ∈ Finset.Icc 1 N, fc d) := by
        refine Finset.sum_congr rfl ?_
        intro d hd
        have hd1 : 1 ≤ d := (Finset.mem_Icc.mp hd).1
        have hdN : d ≤ N := (Finset.mem_Icc.mp hd).2
        have hdL : d < L := by have h1 : N < L := hNltL; omega
        exact fiberCard_symm q r d hq hr hd1 hdL
      _ = (∑ d ∈ Finset.Icc 1 N, w d) := hW1w
  have hfc0 : (fiberCard q r 0 : ℝ) = 0 := by exact_mod_cast fiber_zero q r hq hr hqr
  have hW1tot : (∑ c ∈ (Finset.range L).filter P1, fc c) = fc 0 + (∑ c ∈ Finset.Icc 1 N, w c) := by
    rw [hW1, hW1split, hW1w]
  have hW2tot : (∑ c ∈ (Finset.range L).filter (fun c => P2 c ∧ ¬ P1 c), fc c) =
      (∑ c ∈ Finset.Icc 1 N, w c) := by
    rw [hW2img, hW2w]
  have hcountw : ((((Finset.product ((Finset.range q).filter (fun a : ℕ => a.gcd q = 1))
        ((Finset.range r).filter (fun b : ℕ => b.gcd r = 1))).filter
      (fun ab : ℕ × ℕ =>
        ‖(((ab.1 : ℝ) / (q : ℝ) : ℝ) : UnitAddCircle) -
           (((ab.2 : ℝ) / (r : ℝ) : ℝ) : UnitAddCircle)‖ < Δ)).card : ℝ)) =
      2 * (∑ c ∈ Finset.Icc 1 N, w c) := by
    calc
      ((((Finset.product ((Finset.range q).filter (fun a : ℕ => a.gcd q = 1))
        ((Finset.range r).filter (fun b : ℕ => b.gcd r = 1))).filter
      (fun ab : ℕ × ℕ =>
        ‖(((ab.1 : ℝ) / (q : ℝ) : ℝ) : UnitAddCircle) -
           (((ab.2 : ℝ) / (r : ℝ) : ℝ) : UnitAddCircle)‖ < Δ)).card : ℝ))
          = (∑ c ∈ Finset.range L, (if windowPred q r Δ c then fc c else 0)) := hcw
      _ = (∑ c ∈ (Finset.range L).filter P1, fc c) +
          (∑ c ∈ (Finset.range L).filter (fun c => P2 c ∧ ¬ P1 c), fc c) := hsum
      _ = (fc 0 + (∑ c ∈ Finset.Icc 1 N, w c)) + (∑ c ∈ Finset.Icc 1 N, w c) := by
          rw [hW1tot, hW2tot]
      _ = 2 * (∑ c ∈ Finset.Icc 1 N, w c) := by
          change (fiberCard q r 0 : ℝ) + (∑ c ∈ Finset.Icc 1 N, w c) + (∑ c ∈ Finset.Icc 1 N, w c) = 2 * (∑ c ∈ Finset.Icc 1 N, w c)
          rw [hfc0]
          ring
  have hwf : (∑ c ∈ Finset.Icc 1 N, w c) =
      ((g.totient : ℕ) : ℝ) * (∑ c ∈ (Finset.Icc 1 N).filter (fun c : ℕ => c.gcd qq = 1),
        (∏ p ∈ shared, sigma p c)) := by
    calc
      (∑ c ∈ Finset.Icc 1 N, w c)
          = ∑ c ∈ Finset.Icc 1 N, (if c.gcd qq = 1 then (1 : ℝ) else 0) * ((g.totient : ℕ) : ℝ) *
              (∏ p ∈ shared, sigma p c) := by
            refine Finset.sum_congr rfl ?_
            intro c hc
            dsimp [w]
      _ = ((g.totient : ℕ) : ℝ) * (∑ c ∈ Finset.Icc 1 N,
            (if c.gcd qq = 1 then (∏ p ∈ shared, sigma p c) else 0)) := by
            have hterm : ∀ c : ℕ, (if c.gcd qq = 1 then (1 : ℝ) else 0) * ((g.totient : ℕ) : ℝ) *
                  (∏ p ∈ shared, sigma p c) =
                ((g.totient : ℕ) : ℝ) * (if c.gcd qq = 1 then (∏ p ∈ shared, sigma p c) else 0) := by
              intro c
              by_cases h : c.gcd qq = 1 <;> simp [h]
            have hcong : (∑ c ∈ Finset.Icc 1 N, (if c.gcd qq = 1 then (1 : ℝ) else 0) * ((g.totient : ℕ) : ℝ) *
                  (∏ p ∈ shared, sigma p c)) =
                (∑ c ∈ Finset.Icc 1 N, ((g.totient : ℕ) : ℝ) *
                  (if c.gcd qq = 1 then (∏ p ∈ shared, sigma p c) else 0)) :=
              Finset.sum_congr (s₁ := Finset.Icc 1 N) (s₂ := Finset.Icc 1 N) rfl
                (by intro c hc; exact hterm c)
            rw [hcong]
            rw [← Finset.mul_sum]
      _ = ((g.totient : ℕ) : ℝ) * (∑ c ∈ (Finset.Icc 1 N).filter (fun c : ℕ => c.gcd qq = 1),
            (∏ p ∈ shared, sigma p c)) := by
            rw [← Finset.sum_filter]
  -- finish
  have hmain : ((((Finset.product ((Finset.range q).filter (fun a : ℕ => a.gcd q = 1))
        ((Finset.range r).filter (fun b : ℕ => b.gcd r = 1))).filter
      (fun ab : ℕ × ℕ =>
        ‖(((ab.1 : ℝ) / (q : ℝ) : ℝ) : UnitAddCircle) -
           (((ab.2 : ℝ) / (r : ℝ) : ℝ) : UnitAddCircle)‖ < Δ)).card : ℝ)) =
      2 * ((g.totient : ℕ) : ℝ) * (∑ c ∈ (Finset.Icc 1 N).filter (fun c : ℕ => c.gcd qq = 1),
        (∏ p ∈ shared, sigma p c)) := by
    calc
      ((((Finset.product ((Finset.range q).filter (fun a : ℕ => a.gcd q = 1))
        ((Finset.range r).filter (fun b : ℕ => b.gcd r = 1))).filter
      (fun ab : ℕ × ℕ =>
        ‖(((ab.1 : ℝ) / (q : ℝ) : ℝ) : UnitAddCircle) -
           (((ab.2 : ℝ) / (r : ℝ) : ℝ) : UnitAddCircle)‖ < Δ)).card : ℝ))
          = 2 * (∑ c ∈ Finset.Icc 1 N, w c) := hcountw
      _ = 2 * (((g.totient : ℕ) : ℝ) * (∑ c ∈ (Finset.Icc 1 N).filter (fun c : ℕ => c.gcd qq = 1),
            (∏ p ∈ shared, sigma p c))) := by
          rw [hwf]
      _ = 2 * ((g.totient : ℕ) : ℝ) * (∑ c ∈ (Finset.Icc 1 N).filter (fun c : ℕ => c.gcd qq = 1),
            (∏ p ∈ shared, sigma p c)) := by
          ring
  convert hmain using 1

theorem rpw_target_eq_smallProd (q r : ℕ) (hq : 0 < q) (hr : 0 < r) (Δ : ℝ) (hΔ : 0 ≤ Δ) :
    let g : ℕ := q.gcd r
    let QR : ℕ := q * r / (g * g)
    let L : ℕ := q * r / g
    let Y : ℝ := Δ * (L : ℝ)
    8000 * Δ * (q.totient : ℝ) * (r.totient : ℝ) *
        ∏ p ∈ (Nat.primeFactors QR).filter (fun p : ℕ => Y < (p : ℝ)),
          (1 - 1 / (p : ℝ))⁻¹
      = 8000 * Y * (g.totient : ℝ) *
        (∏ p ∈ (Nat.primeFactors QR).filter (fun p : ℕ => (p : ℝ) ≤ Y),
          (1 - 1 / (p : ℝ))) *
        (∏ p ∈ (g.primeFactors.filter (fun p : ℕ => ¬ p ∣ QR)),
          (1 - 1 / (p : ℝ))) := by
  classical
  dsimp
  let g : ℕ := q.gcd r
  let QR : ℕ := q * r / (g * g)
  let L : ℕ := q * r / g
  let Y : ℝ := Δ * (L : ℝ)
  let f : ℕ → ℝ := fun p => 1 - 1 / (p : ℝ)
  let finv : ℕ → ℝ := fun p => (1 - 1 / (p : ℝ))⁻¹
  have hgpos : 0 < g := Nat.gcd_pos_of_pos_left r hq
  have hLpos : 0 < L := by
    dsimp [L, g]
    exact Nat.div_pos (le_trans (Nat.gcd_le_left r hq) (Nat.le_mul_of_pos_right q hr)) hgpos
  have hQRpos : 0 < QR := by
    dsimp [QR]
    exact Nat.div_pos (Nat.mul_le_mul (Nat.gcd_le_left r hq) (Nat.gcd_le_right q hr))
      (Nat.mul_pos hgpos hgpos)
  have hphi : (q.totient : ℝ) * (r.totient : ℝ) =
      (g.totient : ℝ) * ((L : ℕ).totient : ℝ) := by
    dsimp [g, L]
    exact phi_mul_eq_phi_gcd_mul_phi_div_real q r hq hr
  -- φ(L) = L·∏_{p|L} f
  have hphiL : (L.totient : ℝ) = (L : ℝ) * ∏ p ∈ L.primeFactors, f p := by
    have ht := totient_div_self_real_prod L hLpos
    dsimp [f] at ht ⊢
    have hLne : (L : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hLpos)
    calc
      (L.totient : ℝ) = ((L.totient : ℝ) / (L : ℝ)) * (L : ℝ) := by field_simp [hLne]
      _ = (∏ p ∈ L.primeFactors, f p) * (L : ℝ) := by rw [ht]
      _ = (L : ℝ) * ∏ p ∈ L.primeFactors, f p := by ring
  -- product split over L
  have hsetL : L.primeFactors =
      QR.primeFactors ∪ (g.primeFactors.filter (fun p : ℕ => ¬ p ∣ QR)) := by
    dsimp [L, QR, g]
    exact primeFactors_div_mul_eq q r hq hr
  have hdisj := primeFactors_L_disjoint q r hq hr
  have hsplitL : (∏ p ∈ L.primeFactors, f p) =
      (∏ p ∈ QR.primeFactors, f p) * (∏ p ∈ g.primeFactors.filter (fun p => ¬ p ∣ QR), f p) := by
    rw [hsetL]
    rw [Finset.prod_union hdisj]
  -- split ∏_{pfQR} by p ≤ Y
  have hsplitQR : (∏ p ∈ QR.primeFactors, f p) =
      (∏ p ∈ QR.primeFactors.filter (fun p : ℕ => (p : ℝ) ≤ Y), f p) *
        (∏ p ∈ QR.primeFactors.filter (fun p : ℕ => Y < (p : ℝ)), f p) := by
    have h := prod_filter_split QR.primeFactors (fun p : ℕ => (p : ℝ) ≤ Y) f
    have hfilters : QR.primeFactors.filter (fun p : ℕ => ¬ (p : ℝ) ≤ Y) =
        QR.primeFactors.filter (fun p : ℕ => Y < (p : ℝ)) := by
      apply Finset.filter_congr
      intro p hp
      simp [not_le]
    simpa [hfilters] using h
  -- ∏ big finv = (∏ big f)⁻¹
  have hbiginv : (∏ p ∈ QR.primeFactors.filter (fun p : ℕ => Y < (p : ℝ)), finv p) =
      (∏ p ∈ QR.primeFactors.filter (fun p : ℕ => Y < (p : ℝ)), f p)⁻¹ := by
    dsimp [finv, f]
    rw [← Finset.prod_inv_distrib]
  -- each f p ≠ 0 (prime p)
  have hf_ne0 : ∀ p ∈ QR.primeFactors, f p ≠ 0 := by
    intro p hp
    have hpP : Nat.Prime p := Nat.prime_of_mem_primeFactors hp
    have hp2 : 2 ≤ (p : ℝ) := by exact_mod_cast hpP.two_le
    have hp0 : 0 < (p : ℝ) := by positivity
    have hle : 1 / (p : ℝ) ≤ 1 / 2 := by
      exact (div_le_div_iff₀ hp0 (by norm_num : 0 < (2 : ℝ))).mpr (by
        have h2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp2
        nlinarith)
    have hpos : 0 < 1 - 1 / (p : ℝ) := by linarith
    dsimp [f]
    exact ne_of_gt hpos
  have hbig_ne0 : (∏ p ∈ QR.primeFactors.filter (fun p : ℕ => Y < (p : ℝ)), f p) ≠ 0 := by
    exact (Finset.prod_ne_zero_iff).mpr (by
      intro p hp
      exact hf_ne0 p (Finset.mem_filter.mp hp).1)
  -- ∏big f · ∏big finv = 1
  have hcancel : (∏ p ∈ QR.primeFactors.filter (fun p : ℕ => Y < (p : ℝ)), f p) *
      (∏ p ∈ QR.primeFactors.filter (fun p : ℕ => Y < (p : ℝ)), finv p) = 1 := by
    rw [hbiginv]
    exact mul_inv_cancel₀ hbig_ne0
  let Pfinv : ℝ := ∏ p ∈ QR.primeFactors.filter (fun p : ℕ => Y < (p : ℝ)), finv p
  let P_all : ℝ := ∏ p ∈ L.primeFactors, f p
  let P_Q : ℝ := ∏ p ∈ QR.primeFactors, f p
  let P_S : ℝ := ∏ p ∈ g.primeFactors.filter (fun p => ¬ p ∣ QR), f p
  let P_B : ℝ := ∏ p ∈ QR.primeFactors.filter (fun p : ℕ => Y < (p : ℝ)), f p
  let P_small : ℝ := ∏ p ∈ QR.primeFactors.filter (fun p : ℕ => (p : ℝ) ≤ Y), f p
  calc
    8000 * Δ * (q.totient : ℝ) * (r.totient : ℝ) * Pfinv
        = 8000 * Δ * ((q.totient : ℝ) * (r.totient : ℝ)) * Pfinv := by ring
    _ = 8000 * Δ * ((g.totient : ℝ) * (L.totient : ℝ)) * Pfinv := by
          rw [hphi]
    _ = 8000 * Δ * ((g.totient : ℝ) * ((L : ℝ) * P_all)) * Pfinv := by
          -- (L.totient : ℝ) = (L:ℝ) * P_all: from hphiL
          dsimp [P_all, f] at hphiL ⊢
          rw [hphiL]
    _ = 8000 * Δ * (g.totient : ℝ) * (L : ℝ) * P_Q * P_S * Pfinv := by
          dsimp [P_all, P_Q, P_S] at hsplitL ⊢
          rw [hsplitL]
          ring
    _ = 8000 * Δ * (g.totient : ℝ) * (L : ℝ) * P_small * P_B * P_S * Pfinv := by
          dsimp [P_Q, P_small, P_B] at hsplitQR ⊢
          rw [hsplitQR]
          ring
    _ = 8000 * Δ * (g.totient : ℝ) * (L : ℝ) * P_small * P_S * (P_B * Pfinv) := by ring
    _ = 8000 * Δ * (g.totient : ℝ) * (L : ℝ) * P_small * P_S * 1 := by
          dsimp [P_B, Pfinv]
          rw [hcancel]
    _ = 8000 * (Δ * (L : ℝ)) * (g.totient : ℝ) * P_small * P_S := by ring
    _ = 8000 * Y * (g.totient : ℝ) *
          (∏ p ∈ (Nat.primeFactors QR).filter (fun p : ℕ => (p : ℝ) ≤ Y), f p) *
          (∏ p ∈ (g.primeFactors.filter (fun p : ℕ => ¬ p ∣ QR)), f p) := by
          dsimp [Y, P_small, P_S]
    _ = 8000 * Y * (g.totient : ℝ) *
          (∏ p ∈ (Nat.primeFactors QR).filter (fun p : ℕ => (p : ℝ) ≤ Y), (1 - 1 / (p : ℝ))) *
          (∏ p ∈ (g.primeFactors.filter (fun p : ℕ => ¬ p ∣ QR)), (1 - 1 / (p : ℝ))) := by
          dsimp [f]

/-! ## (W) window product bridge: N·∏(p≤N) ≤ Y·∏(p≤Y) for N < Y ≤ N+1 -/

lemma prime_leY_not_leN (N : ℕ) (Y : ℝ) (p : ℕ)
    (hNY : (N : ℝ) < Y) (hY1 : Y ≤ (N : ℝ) + 1)
    (hpY : (p : ℝ) ≤ Y) (hpn : ¬ (p : ℝ) ≤ (N : ℝ)) : p = N + 1 := by
  have hpN : (N : ℝ) < (p : ℝ) := lt_of_not_ge hpn
  have hpNn : N < p := by exact_mod_cast hpN
  have hpleY : (p : ℝ) ≤ (N : ℝ) + 1 := le_trans hpY hY1
  have hpN1n : p ≤ N + 1 := by exact_mod_cast hpleY
  omega

/-- Y must be exactly N+1 when N+1 itself is a prime divisor ≤ Y -/
lemma eq_Np1_of_prime (N : ℕ) (Y : ℝ) (p : ℕ)
    (hNY : (N : ℝ) < Y) (hY1 : Y ≤ (N : ℝ) + 1)
    (hpY : (p : ℝ) ≤ Y) (hpn : ¬ (p : ℝ) ≤ (N : ℝ)) (hp_eq : p = N + 1) :
    Y = (N + 1 : ℕ) := by
  subst p
  have h1 : (N : ℝ) + 1 ≤ Y := by exact_mod_cast hpY  -- hpY : ((N+1):ℝ) ≤ Y
  -- wait hpY after subst: ((N+1:ℕ):ℝ) ≤ Y: cast of N+1 = (N:ℝ)+1
  have h2 : Y ≤ (N : ℝ) + 1 := hY1
  -- h1: (N:ℝ)+1 ≤ Y
  have hc : ((N + 1 : ℕ) : ℝ) = (N : ℝ) + 1 := by norm_num
  have : (N : ℝ) + 1 ≤ Y := by simpa [hc] using hpY
  linarith


/-- bridge: N·∏_{p≤N}(1−1/p) ≤ Y·∏_{p≤Y}(1−1/p) for N < Y ≤ N+1 -/
lemma prod_window_bridge (N : ℕ) (Y : ℝ) (qq : ℕ)
    (hNY : (N : ℝ) < Y) (hY1 : Y ≤ (N : ℝ) + 1) :
    (N : ℝ) * (∏ p ∈ (Nat.primeFactors qq).filter (fun p : ℕ => (p : ℝ) ≤ (N : ℝ)),
        (1 - 1 / (p : ℝ))) ≤
      Y * (∏ p ∈ (Nat.primeFactors qq).filter (fun p : ℕ => (p : ℝ) ≤ Y),
        (1 - 1 / (p : ℝ))) := by
  classical
  let f : ℕ → ℝ := fun p => 1 - 1 / (p : ℝ)
  let A : Finset ℕ := (Nat.primeFactors qq).filter (fun p : ℕ => (p : ℝ) ≤ (N : ℝ))
  let B : Finset ℕ := (Nat.primeFactors qq).filter (fun p : ℕ => (p : ℝ) ≤ Y)
  have hAB : A ⊆ B := by
    intro p hp
    have h1 := (Finset.mem_filter.mp hp).1
    have h2 := (Finset.mem_filter.mp hp).2
    rw [Finset.mem_filter]
    exact ⟨h1, le_trans h2 (le_of_lt hNY)⟩
  by_cases hempty : B \ A = ∅
  · -- B = A, so both products over A; use N ≤ Y and ∏_A f ≥ 0
    have hBA : B = A := by
      apply le_antisymm
      · intro p hp
        by_contra hpA
        have : p ∈ B \ A := by
          rw [Finset.mem_sdiff]
          exact ⟨hp, hpA⟩
        rw [hempty] at this
        simp at this
      · exact hAB
    have hNleY : (N : ℝ) ≤ Y := le_of_lt hNY
    have hApos : 0 ≤ ∏ p ∈ A, f p := by
      refine Finset.prod_nonneg ?_
      intro p hp
      have hpP : p.Prime := Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hp).1
      have hp2 : 2 ≤ (p : ℝ) := by exact_mod_cast hpP.two_le
      have hp0 : 0 < (p : ℝ) := by positivity
      have hle : 1 / (p : ℝ) ≤ 1 / 2 := by
        exact (div_le_div_iff₀ hp0 (by norm_num)).mpr (by
          have : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hpP.two_le
          linarith)
      have : (1 : ℝ) / (p : ℝ) ≤ 1 := by linarith
      linarith
    calc
      (N : ℝ) * ∏ p ∈ A, f p ≤ Y * ∏ p ∈ A, f p := by
        exact mul_le_mul_of_nonneg_right hNleY hApos
      _ = Y * ∏ p ∈ B, f p := by rw [hBA]
  · -- B∖A nonempty: its unique element is N+1 (a prime), and Y = N+1
    have hx : ∃ p, p ∈ B \ A := by
      by_contra h
      have hBAempty : B \ A = ∅ := (Finset.not_nonempty_iff_eq_empty).mp h
      exact hempty hBAempty
    rcases hx with ⟨p0, hp0⟩
    have hp0B : p0 ∈ B := (Finset.mem_sdiff.mp hp0).1
    have hp0nA : p0 ∉ A := (Finset.mem_sdiff.mp hp0).2
    have hp0pf : p0 ∈ Nat.primeFactors qq := (Finset.mem_filter.mp hp0B).1
    have hp0Y : (p0 : ℝ) ≤ Y := (Finset.mem_filter.mp hp0B).2
    have hp0nN : ¬ (p0 : ℝ) ≤ (N : ℝ) := fun h => hp0nA (Finset.mem_filter.mpr ⟨hp0pf, h⟩)
    have hp0e : p0 = N + 1 := prime_leY_not_leN N Y p0 hNY hY1 hp0Y hp0nN
    have hYeq : Y = (N + 1 : ℕ) := eq_Np1_of_prime N Y p0 hNY hY1 hp0Y hp0nN hp0e
    have hB : B = insert p0 A := by
      ext p
      rw [Finset.mem_insert]
      constructor
      · intro hp
        by_cases hpA : p ∈ A
        · exact Or.inr hpA
        · left
          have hpm : p ∈ Nat.primeFactors qq := (Finset.mem_filter.mp hp).1
          have hpY' : (p : ℝ) ≤ Y := (Finset.mem_filter.mp hp).2
          have hpnN : ¬ (p : ℝ) ≤ (N : ℝ) := fun h => hpA (Finset.mem_filter.mpr ⟨hpm, h⟩)
          have hpe : p = N + 1 := prime_leY_not_leN N Y p hNY hY1 hpY' hpnN
          exact hpe.trans hp0e.symm
      · intro h
        rcases h with h | h
        · rw [h]
          exact hp0B
        · exact hAB h
    have hprod : (∏ p ∈ B, f p) = (∏ p ∈ A, f p) * f p0 := by
      rw [hB, Finset.prod_insert hp0nA]
      ring
    have hfp0 : f p0 = (N : ℝ) / ((N + 1 : ℕ) : ℝ) := by
      rw [hp0e]
      dsimp [f]
      have hc : (((N + 1 : ℕ) : ℝ)) = (N : ℝ) + 1 := by norm_num
      rw [hc]
      have hden : (N : ℝ) + 1 ≠ 0 := by linarith
      field_simp [hden]
      ring
    have hmain : Y * ((∏ p ∈ A, f p) * f p0) = (N : ℝ) * (∏ p ∈ A, f p) := by
      rw [hYeq, hfp0]
      have hc : (((N + 1 : ℕ) : ℝ)) = (N : ℝ) + 1 := by norm_num
      rw [hc]
      have hden : (N : ℝ) + 1 ≠ 0 := by linarith
      field_simp [hden]
    rw [hprod, hmain]

/-! ## (S0) Counting coprime integers in blocks
The block bound for the coprime count.  This is step 1 of the small-sieve input `(S)`. -/

/-- `{x ∈ Icc 1 Q | Q.Coprime x}.card = φ Q` in the `gcd`/`Coprime x Q` orientation. -/
lemma coprime_Icc_one_card (Q : ℕ) :
    (((Finset.Icc 1 Q).filter (fun d : ℕ => d.gcd Q = 1)).card) = Q.totient := by
  rw [← Commons.NumberTheory.Totient.card_coprime_Icc_one Q]
  congr 1
  ext x
  rw [Finset.mem_filter, Finset.mem_filter]
  exact ⟨fun h => ⟨h.1, Nat.coprime_iff_gcd_eq_one.mpr (by rw [Nat.gcd_comm]; exact h.2)⟩,
    fun h => ⟨h.1, by rw [Nat.gcd_comm]; exact Nat.coprime_iff_gcd_eq_one.mp h.2⟩⟩

/-- In every window `[j*Q+1, j*Q+Q]` of `Q` consecutive integers, exactly `φ Q` of them are
coprime to `Q`. -/
lemma coprime_block_card (Q j : ℕ) :
    (((Finset.Icc (j * Q + 1) (j * Q + Q)).filter (fun d : ℕ => d.gcd Q = 1)).card)
      = Q.totient := by
  have himg : (Finset.Icc (j * Q + 1) (j * Q + Q)).filter (fun d : ℕ => d.gcd Q = 1)
      = ((Finset.Icc 1 Q).filter (fun e : ℕ => e.gcd Q = 1)).image (fun e => j * Q + e) := by
    ext d
    rw [Finset.mem_filter, Finset.mem_image]
    constructor
    · rintro ⟨hdI, hdc⟩
      rw [Finset.mem_Icc] at hdI
      refine ⟨d - j * Q, ?_, ?_⟩
      · rw [Finset.mem_filter, Finset.mem_Icc]
        refine ⟨⟨by omega, by omega⟩, ?_⟩
        have hb' : d = j * Q + (d - j * Q) := (Nat.add_sub_cancel' (by omega : j * Q ≤ d)).symm
        have hdg : d.gcd Q = (d - j * Q).gcd Q := by
          conv_lhs => rw [hb']
          rw [show j * Q + (d - j * Q) = (d - j * Q) + Q * j by ring,
            Nat.gcd_add_mul_left_left]
        rw [← hdg]; exact hdc
      · omega
    · rintro ⟨e, he, rfl⟩
      rw [Finset.mem_filter, Finset.mem_Icc] at he
      obtain ⟨⟨he1, he2⟩, hec⟩ := he
      refine ⟨by rw [Finset.mem_Icc]; exact ⟨by omega, by omega⟩, ?_⟩
      have h1 : (j * Q + e).gcd Q = e.gcd Q := by
        rw [show j * Q + e = e + Q * j by ring, Nat.gcd_add_mul_left_left]
      rw [h1]; exact hec
  rw [himg, Finset.card_image_of_injective _ (fun a b h => by omega), coprime_Icc_one_card Q]

/-- The number of integers up to `(k+1)*Q` coprime to `Q` is `(k+1) * φ Q`. -/
lemma coprime_stack_card (Q : ℕ) (k : ℕ) :
    (((Finset.Icc 1 ((k + 1) * Q)).filter (fun d : ℕ => d.gcd Q = 1)).card)
      = (k + 1) * Q.totient := by
  induction k with
  | zero =>
    have h : (0 + 1) * Q = Q := by ring
    rw [h]
    simpa using coprime_Icc_one_card Q
  | succ k ih =>
    have hsplit : (k + 1 + 1) * Q = (k + 1) * Q + Q := by ring
    rw [hsplit]
    have hunion : Finset.Icc 1 ((k + 1) * Q + Q) =
        Finset.Icc 1 ((k + 1) * Q) ∪ Finset.Icc ((k + 1) * Q + 1) ((k + 1) * Q + Q) := by
      ext x
      rw [Finset.mem_Icc, Finset.mem_union, Finset.mem_Icc, Finset.mem_Icc]
      constructor
      · intro h
        by_cases hx : x ≤ (k + 1) * Q
        · exact Or.inl ⟨h.1, hx⟩
        · exact Or.inr ⟨by omega, h.2⟩
      · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
        · exact ⟨h1, by omega⟩
        · exact ⟨by omega, h2⟩
    have hdisj : Disjoint (Finset.Icc 1 ((k + 1) * Q))
        (Finset.Icc ((k + 1) * Q + 1) ((k + 1) * Q + Q)) := by
      rw [Finset.disjoint_left]
      intro x hx1 hx2
      rw [Finset.mem_Icc] at hx1 hx2
      omega
    rw [hunion, Finset.filter_union,
      Finset.card_union_of_disjoint
        (hdisj.mono (Finset.filter_subset _ _) (Finset.filter_subset _ _)),
      ih, coprime_block_card Q (k + 1)]
    ring

/-- Block bound: the number of `d ≤ x` coprime to `Q` is at most `(x/Q + 1) * φ Q`. -/
lemma coprime_count_le_div_add_one (Q x : ℕ) (hQ : 0 < Q) :
    (((Finset.Icc 1 x).filter (fun d : ℕ => d.gcd Q = 1)).card : ℝ) ≤
      ((x : ℝ) / (Q : ℝ) + 1) * (Q.totient : ℝ) := by
  have hsub : Finset.Icc 1 x ⊆ Finset.Icc 1 ((x / Q + 1) * Q) := by
    intro d hd
    rw [Finset.mem_Icc] at hd ⊢
    have hlt := Nat.lt_mul_div_succ x hQ
    have hle : x ≤ (x / Q + 1) * Q := by
      calc x ≤ Q * (x / Q + 1) := le_of_lt hlt
        _ = (x / Q + 1) * Q := by ring
    omega
  have hcard : ((Finset.Icc 1 x).filter (fun d : ℕ => d.gcd Q = 1)).card
      ≤ ((Finset.Icc 1 ((x / Q + 1) * Q)).filter (fun d : ℕ => d.gcd Q = 1)).card :=
    Finset.card_le_card (Finset.filter_subset_filter _ hsub)
  have hstack := coprime_stack_card Q (x / Q)
  have hreal : ((((x / Q + 1) * Q.totient : ℕ)) : ℝ)
      ≤ ((x : ℝ) / (Q : ℝ) + 1) * (Q.totient : ℝ) := by
    have hdiv : (((x / Q : ℕ)) : ℝ) ≤ (x : ℝ) / (Q : ℝ) := Nat.cast_div_le
    have htot : (0 : ℝ) ≤ (Q.totient : ℝ) := by positivity
    push_cast
    nlinarith
  calc (((Finset.Icc 1 x).filter (fun d : ℕ => d.gcd Q = 1)).card : ℝ)
      ≤ (((Finset.Icc 1 ((x / Q + 1) * Q)).filter (fun d : ℕ => d.gcd Q = 1)).card : ℝ) := by
        exact_mod_cast hcard
    _ = ((((x / Q + 1) * Q.totient : ℕ)) : ℝ) := by rw [hstack]
    _ ≤ ((x : ℝ) / (Q : ℝ) + 1) * (Q.totient : ℝ) := hreal

/-- The coprime count over `[1,x]` with modulus `M` only involves the prime factors of `M`
that are at most `x`. -/
lemma coprime_count_filter_eq_radical (M x : ℕ) (hM : 1 ≤ M) :
    (Finset.Icc 1 x).filter (fun d : ℕ => d.gcd M = 1)
      = (Finset.Icc 1 x).filter (fun d : ℕ =>
          d.gcd (∏ p ∈ (Nat.primeFactors M).filter (fun p : ℕ => p ≤ x), p) = 1) := by
  classical
  have hMne : M ≠ 0 := by omega
  have hQne : (∏ p ∈ (Nat.primeFactors M).filter (fun p : ℕ => p ≤ x), p) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr
      (fun p hp => (Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hp).1).ne_zero)
  refine Finset.filter_congr ?_
  intro d hd
  rw [Finset.mem_Icc] at hd
  constructor
  · intro hgcd
    have hdM : d.Coprime M := Nat.coprime_iff_gcd_eq_one.mpr hgcd
    rw [← Nat.coprime_iff_gcd_eq_one]
    rw [Commons.NumberTheory.Nat.coprime_iff_forall_primeFactors_not_dvd hQne]
    intro p hp hpd
    have hpm : p ∈ Nat.primeFactors M := by
      have h1 := hp
      rw [Nat.primeFactors_prod
        (fun q hq => Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hq).1)] at h1
      exact (Finset.mem_filter.mp h1).1
    exact (Commons.NumberTheory.Nat.coprime_iff_forall_primeFactors_not_dvd hMne).mp hdM p hpm hpd
  · intro hcop
    have hdcop : d.Coprime (∏ p ∈ (Nat.primeFactors M).filter (fun p : ℕ => p ≤ x), p) :=
      Nat.coprime_iff_gcd_eq_one.mpr hcop
    rw [← Nat.coprime_iff_gcd_eq_one]
    rw [Commons.NumberTheory.Nat.coprime_iff_forall_primeFactors_not_dvd hMne]
    rw [Commons.NumberTheory.Nat.coprime_iff_forall_primeFactors_not_dvd hQne] at hdcop
    intro p hpM hpd
    by_cases hpx : p ≤ x
    · have hpQ : p ∈ (∏ p ∈ (Nat.primeFactors M).filter (fun p : ℕ => p ≤ x), p).primeFactors := by
        rw [Nat.primeFactors_prod
          (fun q hq => Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hq).1)]
        exact Finset.mem_filter.mpr ⟨hpM, hpx⟩
      exact hdcop p hpQ hpd
    · have hple : p ≤ d := Nat.le_of_dvd (by omega : 0 < d) hpd
      omega

/-- **Count claim, case `Q ≤ x`.**  If `Q` is the product of the prime factors of `M` that are
at most `x`, and `Q ≤ x`, then the count of `d ≤ x` coprime to `M` is at most
`2·x·∏_{p | M, p ≤ x} (1 - 1/p)`. -/
lemma coprime_count_le_two_mul_of_le (M x : ℕ) (hM : 1 ≤ M) (hx : 0 < x)
    (hQle : (∏ p ∈ (Nat.primeFactors M).filter (fun p : ℕ => p ≤ x), p) ≤ x) :
    (((Finset.Icc 1 x).filter (fun d : ℕ => d.gcd M = 1)).card : ℝ) ≤
      2 * (x : ℝ) *
        ∏ p ∈ (Nat.primeFactors M).filter (fun p : ℕ => p ≤ x), (1 - 1 / (p : ℝ)) := by
  classical
  set Q : ℕ := ∏ p ∈ (Nat.primeFactors M).filter (fun p : ℕ => p ≤ x), p with hQdef
  have hQpos : 0 < Q := by
    rw [hQdef]
    exact Finset.prod_pos
      (fun q hq => (Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hq).1).pos)
  have hblock := coprime_count_le_div_add_one Q x hQpos
  have hφ : ((Q.totient : ℝ)) = (Q : ℝ) *
      ∏ p ∈ (Nat.primeFactors M).filter (fun p : ℕ => p ≤ x), (1 - 1 / (p : ℝ)) := by
    have h := totient_div_self_real_prod Q hQpos
    have hpf : Q.primeFactors = (Nat.primeFactors M).filter (fun p : ℕ => p ≤ x) := by
      rw [hQdef, Nat.primeFactors_prod]
      exact fun q hq => Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hq).1
    rw [hpf] at h
    have hQposR : (0:ℝ) < (Q : ℝ) := by exact_mod_cast hQpos
    field_simp at h
    linarith [h]
  rw [hφ] at hblock
  have hQleR : (Q : ℝ) ≤ (x : ℝ) := by exact_mod_cast hQle
  have hprod : (0:ℝ) ≤ ∏ p ∈ (Nat.primeFactors M).filter (fun p : ℕ => p ≤ x), (1 - 1 / (p : ℝ)) := by
    refine Finset.prod_nonneg ?_
    intro p hp
    have hpp : p.Prime := Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hp).1
    have hp2 : (2:ℝ) ≤ (p:ℝ) := by exact_mod_cast hpp.two_le
    have hp0 : (0:ℝ) < (p:ℝ) := by linarith
    have : (1:ℝ) / (p:ℝ) ≤ 1 := by
      rw [div_le_one hp0]; linarith
    linarith
  have hMQ : (Finset.Icc 1 x).filter (fun d : ℕ => d.gcd M = 1)
      = (Finset.Icc 1 x).filter (fun d : ℕ => d.gcd Q = 1) := by
    rw [hQdef]
    exact coprime_count_filter_eq_radical M x hM
  rw [hMQ]
  have hQneR : (Q : ℝ) ≠ 0 := by positivity
  have hxQ : (x : ℝ) + (Q : ℝ) ≤ 2 * (x : ℝ) := by linarith
  calc (((Finset.Icc 1 x).filter (fun d : ℕ => d.gcd Q = 1)).card : ℝ)
      ≤ ((x : ℝ) / (Q : ℝ) + 1) *
          ((Q : ℝ) * ∏ p ∈ (Nat.primeFactors M).filter (fun p : ℕ => p ≤ x), (1 - 1 / (p : ℝ))) := hblock
    _ = ((x : ℝ) + (Q : ℝ)) *
          ∏ p ∈ (Nat.primeFactors M).filter (fun p : ℕ => p ≤ x), (1 - 1 / (p : ℝ)) := by
        field_simp
    _ ≤ (2 * (x : ℝ)) *
          ∏ p ∈ (Nat.primeFactors M).filter (fun p : ℕ => p ≤ x), (1 - 1 / (p : ℝ)) :=
        mul_le_mul_of_nonneg_right hxQ hprod
    _ = 2 * (x : ℝ) *
          ∏ p ∈ (Nat.primeFactors M).filter (fun p : ℕ => p ≤ x), (1 - 1 / (p : ℝ)) := by ring


/-- **Union bound.**  The number of `d ≤ x` divisible by at least one prime of `R` is at
most `Σ_{p ∈ R} x/p` (each prime contributes at most `x/p` multiples). -/
lemma bad_count_le_sum_div (R : Finset ℕ) (x : ℕ) :
    (((Finset.Icc 1 x).filter (fun d : ℕ => ∃ p ∈ R, p ∣ d)).card : ℝ) ≤
      ∑ p ∈ R, (x : ℝ) / (p : ℝ) := by
  have hsub : (Finset.Icc 1 x).filter (fun d : ℕ => ∃ p ∈ R, p ∣ d) ⊆
      R.biUnion (fun p => (Finset.Icc 1 x).filter (fun d : ℕ => p ∣ d)) := by
    intro d hd
    rw [Finset.mem_filter] at hd
    obtain ⟨hdI, p, hpR, hpd⟩ := hd
    rw [Finset.mem_biUnion]
    exact ⟨p, hpR, by rw [Finset.mem_filter]; exact ⟨hdI, hpd⟩⟩
  have h1 : (((Finset.Icc 1 x).filter (fun d : ℕ => ∃ p ∈ R, p ∣ d)).card : ℝ) ≤
      ∑ p ∈ R, (((Finset.Icc 1 x).filter (fun d : ℕ => p ∣ d)).card : ℝ) := by
    have h2 := Finset.card_biUnion_le (s := R)
      (t := fun p => (Finset.Icc 1 x).filter (fun d : ℕ => p ∣ d))
    have h3 : ((Finset.Icc 1 x).filter (fun d : ℕ => ∃ p ∈ R, p ∣ d)).card
        ≤ ∑ p ∈ R, ((Finset.Icc 1 x).filter (fun d : ℕ => p ∣ d)).card :=
      le_trans (Finset.card_le_card hsub) h2
    exact_mod_cast h3
  refine le_trans h1 (Finset.sum_le_sum ?_)
  intro p hp
  rw [Commons.NumberTheory.Nat.card_multiples_Icc]
  exact Nat.cast_div_le

/-- **Complement form / lower sieve bound.**  The number of `d ≤ x` divisible by no prime
of `R` is at least `x - Σ_{p ∈ R} x/p`. -/
lemma coprime_count_ge_union_bound (R : Finset ℕ) (x : ℕ) :
    (x : ℝ) - ∑ p ∈ R, (x : ℝ) / (p : ℝ) ≤
      (((Finset.Icc 1 x).filter (fun d : ℕ => ∀ p ∈ R, ¬ p ∣ d)).card : ℝ) := by
  classical
  set G := (Finset.Icc 1 x).filter (fun d : ℕ => ∀ p ∈ R, ¬ p ∣ d) with hG
  set B := (Finset.Icc 1 x).filter (fun d : ℕ => ∃ p ∈ R, p ∣ d) with hB
  have hdisj : Disjoint G B := by
    rw [Finset.disjoint_left]
    intro d hdG hdB
    rw [hG, Finset.mem_filter] at hdG
    rw [hB, Finset.mem_filter] at hdB
    obtain ⟨p, hpR, hpd⟩ := hdB.2
    exact hdG.2 p hpR hpd
  have hunion : G ∪ B = Finset.Icc 1 x := by
    ext d
    rw [Finset.mem_union, hG, hB, Finset.mem_filter, Finset.mem_filter]
    constructor
    · rintro (⟨h1, _⟩ | ⟨h1, _⟩) <;> exact h1
    · intro hd
      by_cases h : ∃ p ∈ R, p ∣ d
      · exact Or.inr ⟨hd, h⟩
      · exact Or.inl ⟨hd, fun p hpR hpd => h (⟨p, hpR, hpd⟩ : ∃ p ∈ R, p ∣ d)⟩
  have hcard : G.card + B.card = x := by
    have h1 := Finset.card_union_of_disjoint hdisj
    rw [hunion] at h1
    have h2 : (Finset.Icc 1 x).card = x := by rw [Nat.card_Icc]; omega
    omega
  have hBle := bad_count_le_sum_div R x
  rw [← hB] at hBle
  have hGcast : (G.card : ℝ) = (x : ℝ) - (B.card : ℝ) := by
    have : (x : ℝ) = (G.card : ℝ) + (B.card : ℝ) := by exact_mod_cast hcard.symm
    linarith
  rw [hGcast]
  linarith


/-! ### Subset weights: the total-weight identity and the tail estimate -/

/-- Total weight identity: summing `(∏_{p ∈ T} β p)·(∏_{p ∈ S∖T} α p)` over all subsets
`T ⊆ S` gives `∏_{p ∈ S} (α p + β p)`. -/
lemma sum_powerset_weight_eq_prod (S : Finset ℕ) (α β : ℕ → ℝ) :
    (∑ T ∈ S.powerset, (∏ p ∈ T, β p) * (∏ p ∈ S \ T, α p)) = ∏ p ∈ S, (α p + β p) := by
  have h : (∏ p ∈ S, (α p + β p)) = ∏ p ∈ S, (β p + α p) :=
    Finset.prod_congr rfl (fun p _ => by ring)
  rw [h, Finset.prod_add β α S]

/-- **Tail weight estimate.**  For a finite set `S` of positive naturals with `α, β ≥ 0` on `S`
and `X > 0`, the total weight of the subsets `T ⊆ S` with `∏_{p ∈ T} p > X`, each weighted by
`(∏_{p ∈ T} β p)·(∏_{p ∈ S∖T} α p)/∏_{p ∈ T} p`, is at most `X⁻¹` times the total weight of
*all* subsets of `S`. -/
lemma tail_weight_le (S : Finset ℕ) (α β : ℕ → ℝ)
    (hS : ∀ p ∈ S, 0 < p) (hα : ∀ p ∈ S, 0 ≤ α p) (hβ : ∀ p ∈ S, 0 ≤ β p)
    (X : ℝ) (hX : 0 < X) :
    (∑ T ∈ S.powerset.filter (fun T : Finset ℕ => X < ∏ p ∈ T, (p : ℝ)),
        (∏ p ∈ T, β p) * (∏ p ∈ S \ T, α p) * (∏ p ∈ T, (p : ℝ))⁻¹)
      ≤ X⁻¹ * ∑ T ∈ S.powerset, (∏ p ∈ T, β p) * (∏ p ∈ S \ T, α p) := by
  have hnonneg : ∀ T ∈ S.powerset, 0 ≤ (∏ p ∈ T, β p) * (∏ p ∈ S \ T, α p) := by
    intro T hT
    rw [Finset.mem_powerset] at hT
    refine mul_nonneg (Finset.prod_nonneg (fun p hp => hβ p (hT hp)))
      (Finset.prod_nonneg (fun p hp => hα p (Finset.mem_sdiff.mp hp).1))
  have hterm : ∀ T ∈ S.powerset.filter (fun T : Finset ℕ => X < ∏ p ∈ T, (p : ℝ)),
      (∏ p ∈ T, β p) * (∏ p ∈ S \ T, α p) * (∏ p ∈ T, (p : ℝ))⁻¹
        ≤ X⁻¹ * ((∏ p ∈ T, β p) * (∏ p ∈ S \ T, α p)) := by
    intro T hT
    rw [Finset.mem_filter, Finset.mem_powerset] at hT
    obtain ⟨hTS, hXlt⟩ := hT
    have hpos : 0 < ∏ p ∈ T, (p : ℝ) :=
      Finset.prod_pos (fun p hp => by exact_mod_cast hS p (hTS hp))
    have hinv : (∏ p ∈ T, (p : ℝ))⁻¹ ≤ X⁻¹ := by
      rw [← one_div, ← one_div]
      exact one_div_le_one_div_of_le hX (le_of_lt hXlt)
    have hnn : 0 ≤ (∏ p ∈ T, β p) * (∏ p ∈ S \ T, α p) := hnonneg T (Finset.mem_powerset.mpr hTS)
    calc (∏ p ∈ T, β p) * (∏ p ∈ S \ T, α p) * (∏ p ∈ T, (p : ℝ))⁻¹
        = ((∏ p ∈ T, β p) * (∏ p ∈ S \ T, α p)) * (∏ p ∈ T, (p : ℝ))⁻¹ := by ring
      _ ≤ ((∏ p ∈ T, β p) * (∏ p ∈ S \ T, α p)) * X⁻¹ :=
          mul_le_mul_of_nonneg_left hinv hnn
      _ = X⁻¹ * ((∏ p ∈ T, β p) * (∏ p ∈ S \ T, α p)) := by ring
  calc (∑ T ∈ S.powerset.filter (fun T : Finset ℕ => X < ∏ p ∈ T, (p : ℝ)),
          (∏ p ∈ T, β p) * (∏ p ∈ S \ T, α p) * (∏ p ∈ T, (p : ℝ))⁻¹)
      ≤ ∑ T ∈ S.powerset.filter (fun T : Finset ℕ => X < ∏ p ∈ T, (p : ℝ)),
          X⁻¹ * ((∏ p ∈ T, β p) * (∏ p ∈ S \ T, α p)) := Finset.sum_le_sum hterm
    _ = X⁻¹ * ∑ T ∈ S.powerset.filter (fun T : Finset ℕ => X < ∏ p ∈ T, (p : ℝ)),
          ((∏ p ∈ T, β p) * (∏ p ∈ S \ T, α p)) := by rw [Finset.mul_sum]
    _ ≤ X⁻¹ * ∑ T ∈ S.powerset, ((∏ p ∈ T, β p) * (∏ p ∈ S \ T, α p)) := by
        refine mul_le_mul_of_nonneg_left ?_ (le_of_lt (inv_pos.mpr hX))
        refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) ?_
        intro T hT _
        exact hnonneg T hT

/-- Corollary for the sieve weights of the sigma-window sum: with
`α p = (p−2)/(p−1)`, `β p = 1/(p−1)` (so that `α p + β p = 1`), the total weight is `1` and the
tail weight is at most `X⁻¹`. -/
lemma tail_weight_le_one (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) (X : ℝ) (hX : 0 < X) :
    (∑ T ∈ S.powerset.filter (fun T : Finset ℕ => X < ∏ p ∈ T, (p : ℝ)),
        (∏ p ∈ T, (1 / ((p : ℝ) - 1))) *
          (∏ p ∈ S \ T, (((p : ℝ) - 2) / ((p : ℝ) - 1))) *
          (∏ p ∈ T, (p : ℝ))⁻¹)
      ≤ X⁻¹ := by
  have hα : ∀ p ∈ S, 0 ≤ (((p : ℝ) - 2) / ((p : ℝ) - 1)) := by
    intro p hp
    have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast (hS p hp).two_le
    exact div_nonneg (by linarith) (by linarith)
  have hβ : ∀ p ∈ S, 0 ≤ (1 / ((p : ℝ) - 1)) := by
    intro p hp
    have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast (hS p hp).two_le
    exact div_nonneg zero_le_one (by linarith)
  have hpos : ∀ p ∈ S, 0 < p := fun p hp => (hS p hp).pos
  have h := tail_weight_le S (fun p => ((p : ℝ) - 2) / ((p : ℝ) - 1))
    (fun p => 1 / ((p : ℝ) - 1)) hpos hα hβ X hX
  have hone : ∑ T ∈ S.powerset, (∏ p ∈ T, (1 / ((p : ℝ) - 1))) *
      (∏ p ∈ S \ T, (((p : ℝ) - 2) / ((p : ℝ) - 1))) = 1 := by
    rw [sum_powerset_weight_eq_prod]
    refine Finset.prod_eq_one ?_
    intro p hp
    have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast (hS p hp).two_le
    have h1 : (p : ℝ) - 1 ≠ 0 := by linarith
    field_simp
    ring
  rw [hone, mul_one] at h
  exact h

/-- The total weight `Σ_T c_T/∏T` of the sigma-window sieve weights equals `∏_{p ∈ S}(1 − 1/p)`. -/
lemma sum_weight_div_eq_prod (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) :
    (∑ T ∈ S.powerset, (∏ p ∈ T, (1 / ((p : ℝ) - 1))) *
        (∏ p ∈ S \ T, (((p : ℝ) - 2) / ((p : ℝ) - 1))) * (∏ p ∈ T, (p : ℝ))⁻¹)
      = ∏ p ∈ S, (1 - 1 / (p : ℝ)) := by
  have hterm : ∀ T : Finset ℕ, (∏ p ∈ T, (1 / ((p : ℝ) - 1))) * (∏ p ∈ T, (p : ℝ))⁻¹
      = ∏ p ∈ T, (1 / (((p : ℝ) - 1) * (p : ℝ))) := by
    intro T
    rw [← Finset.prod_inv_distrib, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl ?_
    intro p _
    rw [one_div, one_div, mul_inv]
  calc (∑ T ∈ S.powerset, (∏ p ∈ T, (1 / ((p : ℝ) - 1))) *
        (∏ p ∈ S \ T, (((p : ℝ) - 2) / ((p : ℝ) - 1))) * (∏ p ∈ T, (p : ℝ))⁻¹)
      = ∑ T ∈ S.powerset, (∏ p ∈ T, (1 / (((p : ℝ) - 1) * (p : ℝ)))) *
        (∏ p ∈ S \ T, (((p : ℝ) - 2) / ((p : ℝ) - 1))) := by
        refine Finset.sum_congr rfl ?_
        intro T _
        calc ((∏ p ∈ T, (1 / ((p : ℝ) - 1))) *
            (∏ p ∈ S \ T, (((p : ℝ) - 2) / ((p : ℝ) - 1)))) * (∏ p ∈ T, (p : ℝ))⁻¹
            = ((∏ p ∈ T, (1 / ((p : ℝ) - 1))) * (∏ p ∈ T, (p : ℝ))⁻¹) *
              (∏ p ∈ S \ T, (((p : ℝ) - 2) / ((p : ℝ) - 1))) := by ring
          _ = (∏ p ∈ T, (1 / (((p : ℝ) - 1) * (p : ℝ)))) *
              (∏ p ∈ S \ T, (((p : ℝ) - 2) / ((p : ℝ) - 1))) := by rw [hterm T]
    _ = ∏ p ∈ S, ((((p : ℝ) - 2) / ((p : ℝ) - 1)) + 1 / (((p : ℝ) - 1) * (p : ℝ))) :=
        sum_powerset_weight_eq_prod S (fun p => ((p : ℝ) - 2) / ((p : ℝ) - 1))
          (fun p => 1 / (((p : ℝ) - 1) * (p : ℝ)))
    _ = ∏ p ∈ S, (1 - 1 / (p : ℝ)) := by
        refine Finset.prod_congr rfl ?_
        intro p hp
        have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast (hS p hp).two_le
        have h1 : (p : ℝ) - 1 ≠ 0 := by linarith
        have h2 : (p : ℝ) ≠ 0 := by linarith
        field_simp
        ring


/-! ## (S1) The α/β recursion for the sigma-window sieve sum -/

/-- The sieve weight of a prime for the sigma-window sum. -/
def sw (p c : ℕ) : ℝ := if p ∣ c then (1 : ℝ) else (((p : ℝ) - 2) / ((p : ℝ) - 1))

/-- The sigma-window sieve sum. -/
def swSum (M x : ℕ) (S : Finset ℕ) : ℝ :=
  ∑ c ∈ (Finset.Icc 1 x).filter (fun c : ℕ => c.gcd M = 1), ∏ p ∈ S, sw p c

lemma sw_eq (p c : ℕ) (hp : 2 ≤ p) :
    sw p c = (((p : ℝ) - 2) / ((p : ℝ) - 1)) +
      (1 / ((p : ℝ) - 1)) * (if p ∣ c then (1 : ℝ) else 0) := by
  have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
  have hden : (p : ℝ) - 1 ≠ 0 := by linarith
  unfold sw
  by_cases h : p ∣ c
  · rw [if_pos h, if_pos h]
    field_simp
    ring
  · rw [if_neg h, if_neg h]
    field_simp
    ring

lemma sw_sum_eq (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) (q c : ℕ) (hq : q.Prime)
    (hqS : q ∉ S) : ∏ p ∈ S, sw p (q * c) = ∏ p ∈ S, sw p c := by
  refine Finset.prod_congr rfl ?_
  intro p hp
  have hpq : p ≠ q := fun h => hqS (h ▸ hp)
  have hpp : p.Prime := hS p hp
  have hiff : (p ∣ q * c) ↔ (p ∣ c) := by
    constructor
    · intro h
      rcases hpp.dvd_mul.mp h with h' | h'
      · exact absurd ((Nat.prime_dvd_prime_iff_eq hpp hq).mp h') hpq
      · exact h'
    · intro h
      exact dvd_mul_of_dvd_right h q
  unfold sw
  exact if_congr hiff rfl rfl

lemma gcd_sw (q M c : ℕ) (hq : q.Prime) (hqM : ¬ q ∣ M) : (q * c).gcd M = c.gcd M :=
  ((hq.coprime_iff_not_dvd).mpr hqM).gcd_mul_left_cancel c

/-- **The `α/β` recursion.** -/
theorem swSum_insert (M x q : ℕ) (S : Finset ℕ) (hq : q.Prime) (hqM : ¬ q ∣ M)
    (hqS : q ∉ S) (hS : ∀ p ∈ S, p.Prime) :
    swSum M x (insert q S) = (((q : ℝ) - 2) / ((q : ℝ) - 1)) * swSum M x S +
      (1 / ((q : ℝ) - 1)) * swSum M (x / q) S := by
  classical
  have hsplit : (∑ c ∈ (Finset.Icc 1 x).filter (fun c : ℕ => c.gcd M = 1),
        sw q c * ∏ p ∈ S, sw p c) =
      (((q : ℝ) - 2) / ((q : ℝ) - 1)) *
        (∑ c ∈ (Finset.Icc 1 x).filter (fun c : ℕ => c.gcd M = 1), ∏ p ∈ S, sw p c) +
      (1 / ((q : ℝ) - 1)) *
        (∑ c ∈ (Finset.Icc 1 x).filter (fun c : ℕ => c.gcd M = 1),
          (if q ∣ c then (1 : ℝ) else 0) * (∏ p ∈ S, sw p c)) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl ?_
    intro c _
    rw [sw_eq q c hq.two_le]
    ring
  have hset : (Finset.Icc 1 x).filter (fun c : ℕ => c.gcd M = 1 ∧ q ∣ c)
      = ((Finset.Icc 1 x).filter (fun c : ℕ => c.gcd M = 1)).filter (fun c : ℕ => q ∣ c) := by
    ext c
    simp only [Finset.mem_filter]
    tauto
  have h1 : (∑ c ∈ (Finset.Icc 1 x).filter (fun c : ℕ => c.gcd M = 1),
        (if q ∣ c then (1 : ℝ) else 0) * (∏ p ∈ S, sw p c)) =
      ∑ c ∈ (Finset.Icc 1 x).filter (fun c : ℕ => c.gcd M = 1 ∧ q ∣ c), ∏ p ∈ S, sw p c := by
    rw [Finset.sum_filter (fun c : ℕ => c.gcd M = 1)
      (fun c => (if q ∣ c then (1 : ℝ) else 0) * (∏ p ∈ S, sw p c))]
    rw [hset]
    rw [Finset.sum_filter (fun c : ℕ => q ∣ c) (fun c => ∏ p ∈ S, sw p c)]
    rw [Finset.sum_filter (fun c : ℕ => c.gcd M = 1)
      (fun c => if q ∣ c then (∏ p ∈ S, sw p c) else 0)]
    refine Finset.sum_congr rfl ?_
    intro c _
    by_cases hc1 : c.gcd M = 1 <;> by_cases hc2 : q ∣ c <;> simp [hc1, hc2]
  have hsub : (∑ c ∈ (Finset.Icc 1 x).filter (fun c : ℕ => c.gcd M = 1),
        (if q ∣ c then (1 : ℝ) else 0) * (∏ p ∈ S, sw p c)) =
      ∑ d ∈ (Finset.Icc 1 (x / q)).filter (fun d : ℕ => d.gcd M = 1), ∏ p ∈ S, sw p d := by
    rw [h1]
    refine Finset.sum_bij (fun c _ => c / q) ?_ ?_ ?_ ?_
    · intro c hc
      rw [Finset.mem_filter] at hc
      obtain ⟨hcI, hcg, hcq⟩ := hc
      rw [Finset.mem_Icc] at hcI
      rw [Finset.mem_filter, Finset.mem_Icc]
      refine ⟨⟨?_, Nat.div_le_div_right hcI.2⟩, ?_⟩
      · exact (Nat.one_le_div_iff hq.pos).mpr (Nat.le_of_dvd (by omega) hcq)
      · have hqeq : q * (c / q) = c := Nat.mul_div_cancel' hcq
        have h2 := gcd_sw q M (c / q) hq hqM
        rw [hqeq] at h2
        rw [← h2]
        exact hcg
    · intro c1 hc1 c2 hc2 h
      rw [Finset.mem_filter] at hc1 hc2
      obtain ⟨_, _, hq1⟩ := hc1
      obtain ⟨_, _, hq2⟩ := hc2
      have e1 : q * (c1 / q) = c1 := Nat.mul_div_cancel' hq1
      have e2 : q * (c2 / q) = c2 := Nat.mul_div_cancel' hq2
      rw [← e1, ← e2, h]
    · intro d hd
      rw [Finset.mem_filter, Finset.mem_Icc] at hd
      obtain ⟨⟨hd1, hd2⟩, hdg⟩ := hd
      refine ⟨q * d, ?_, ?_⟩
      · rw [Finset.mem_filter, Finset.mem_Icc]
        refine ⟨⟨by nlinarith [hq.two_le], ?_⟩, ?_⟩
        · have := (Nat.le_div_iff_mul_le hq.pos).mp hd2
          simpa [mul_comm] using this
        · refine ⟨?_, dvd_mul_right q d⟩
          rw [gcd_sw q M d hq hqM]
          exact hdg
      · exact Nat.mul_div_cancel_left d hq.pos
    · intro c hc
      rw [Finset.mem_filter] at hc
      obtain ⟨_, _, hcq⟩ := hc
      have hqeq : q * (c / q) = c := Nat.mul_div_cancel' hcq
      conv_lhs => rw [← hqeq]
      exact sw_sum_eq S hS q (c / q) hq hqS
  calc swSum M x (insert q S)
      = ∑ c ∈ (Finset.Icc 1 x).filter (fun c : ℕ => c.gcd M = 1), sw q c * ∏ p ∈ S, sw p c := by
        unfold swSum
        refine Finset.sum_congr rfl ?_
        intro c _
        exact Finset.prod_insert hqS
    _ = (((q : ℝ) - 2) / ((q : ℝ) - 1)) * swSum M x S +
        (1 / ((q : ℝ) - 1)) * swSum M (x / q) S := by
        rw [hsplit, hsub]
        unfold swSum
        ring


/-- **The T-expansion.** The sigma-window sieve sum is the weighted sum over the subsets of the
sieve primes of the coprime count at the corresponding argument. -/
theorem swSum_eq_sum_powerset (M : ℕ) : ∀ (S : Finset ℕ) (x : ℕ),
    (∀ p ∈ S, p.Prime) → (∀ p ∈ S, ¬ p ∣ M) →
    swSum M x S = ∑ T ∈ S.powerset,
      (∏ p ∈ T, (1 / ((p : ℝ) - 1))) *
        (∏ p ∈ S \ T, (((p : ℝ) - 2) / ((p : ℝ) - 1))) *
        (((Finset.Icc 1 (x / (∏ p ∈ T, p))).filter (fun c : ℕ => c.gcd M = 1)).card : ℝ) := by
  intro S
  refine Finset.induction_on S ?base ?step
  · intro x _ _
    simp [swSum]
  · intro q S hqS IH x hS hSM
    have hq : q.Prime := hS q (Finset.mem_insert_self q S)
    have hqM : ¬ q ∣ M := hSM q (Finset.mem_insert_self q S)
    have hS' : ∀ p ∈ S, p.Prime := fun p hp => hS p (Finset.mem_insert_of_mem hp)
    have hSM' : ∀ p ∈ S, ¬ p ∣ M := fun p hp => hSM p (Finset.mem_insert_of_mem hp)
    rw [swSum_insert M x q S hq hqM hqS hS', IH x hS' hSM', IH (x / q) hS' hSM',
      Finset.sum_powerset_insert hqS]
    have hA : (∑ T ∈ S.powerset, (∏ p ∈ T, (1 / ((p : ℝ) - 1))) *
          (∏ p ∈ insert q S \ T, (((p : ℝ) - 2) / ((p : ℝ) - 1))) *
          (((Finset.Icc 1 (x / (∏ p ∈ T, p))).filter (fun c : ℕ => c.gcd M = 1)).card : ℝ))
        = (((q : ℝ) - 2) / ((q : ℝ) - 1)) *
          (∑ T ∈ S.powerset, (∏ p ∈ T, (1 / ((p : ℝ) - 1))) *
            (∏ p ∈ S \ T, (((p : ℝ) - 2) / ((p : ℝ) - 1))) *
            (((Finset.Icc 1 (x / (∏ p ∈ T, p))).filter (fun c : ℕ => c.gcd M = 1)).card : ℝ)) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl ?_
      intro T hT
      rw [Finset.mem_powerset] at hT
      have hqT : q ∉ T := fun h => hqS (hT h)
      have hset : insert q S \ T = insert q (S \ T) := by
        ext p
        simp only [Finset.mem_sdiff, Finset.mem_insert]
        constructor
        · rintro ⟨hp, hpnT⟩
          rcases hp with rfl | hp
          · exact Or.inl rfl
          · exact Or.inr ⟨hp, hpnT⟩
        · rintro (rfl | ⟨hp, hpnT⟩)
          · exact ⟨Or.inl rfl, hqT⟩
          · exact ⟨Or.inr hp, hpnT⟩
      have hqST : q ∉ S \ T := by
        rw [Finset.mem_sdiff]
        exact fun h => hqS h.1
      rw [hset, Finset.prod_insert hqST]
      ring_nf
    have hB : (∑ T ∈ S.powerset, (∏ p ∈ insert q T, (1 / ((p : ℝ) - 1))) *
          (∏ p ∈ insert q S \ insert q T, (((p : ℝ) - 2) / ((p : ℝ) - 1))) *
          (((Finset.Icc 1 (x / (∏ p ∈ insert q T, p))).filter
            (fun c : ℕ => c.gcd M = 1)).card : ℝ))
        = (1 / ((q : ℝ) - 1)) *
          (∑ T ∈ S.powerset, (∏ p ∈ T, (1 / ((p : ℝ) - 1))) *
            (∏ p ∈ S \ T, (((p : ℝ) - 2) / ((p : ℝ) - 1))) *
            (((Finset.Icc 1 (x / q / (∏ p ∈ T, p))).filter
              (fun c : ℕ => c.gcd M = 1)).card : ℝ)) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl ?_
      intro T hT
      rw [Finset.mem_powerset] at hT
      have hqT : q ∉ T := fun h => hqS (hT h)
      have hset : insert q S \ insert q T = S \ T := by
        ext p
        simp only [Finset.mem_sdiff, Finset.mem_insert]
        constructor
        · rintro ⟨hp, hpn⟩
          refine ⟨?_, ?_⟩
          · rcases hp with rfl | hp
            · exact absurd (Or.inl rfl) hpn
            · exact hp
          · intro hpT
            exact hpn (Or.inr hpT)
        · rintro ⟨hp, hpnT⟩
          refine ⟨Or.inr hp, ?_⟩
          rintro (rfl | hpT)
          · exact hqS hp
          · exact hpnT hpT
      have hprod : (∏ p ∈ insert q T, (p : ℕ)) = q * ∏ p ∈ T, p := Finset.prod_insert hqT
      rw [hset, Finset.prod_insert hqT, hprod]
      have hdiv : x / (q * ∏ p ∈ T, p) = x / q / (∏ p ∈ T, p) :=
        (Nat.div_div_eq_div_mul x q (∏ p ∈ T, p)).symm
      rw [hdiv]
      ring_nf
    rw [hA, hB]


/-- The product of the distinct prime factors of `M ≠ 0` is at most `M`. -/
lemma prod_primeFactors_le (M : ℕ) (hM : M ≠ 0) : ∏ p ∈ Nat.primeFactors M, p ≤ M := by
  conv_rhs => rw [Nat.prod_primeFactors_pow_factorization hM]
  refine Finset.prod_le_prod₀ (fun p _ => Nat.zero_le p) ?_
  intro p hp
  obtain ⟨hpp, hpdvd, _⟩ := Nat.mem_primeFactors.mp hp
  have hp1 : 1 ≤ M.factorization p := Nat.Prime.factorization_pos_of_dvd hpp (by omega) hpdvd
  calc p = p ^ 1 := (pow_one p).symm
    _ ≤ p ^ M.factorization p := Nat.pow_le_pow_right hpp.pos hp1

/-- **Large-argument half of the threshold split (threshold at `M`).** -/
theorem swSum_large_argument_le (M x : ℕ) (S : Finset ℕ) (hM : 1 ≤ M) (hx : 0 < x)
    (hS : ∀ p ∈ S, p.Prime) (hSM : ∀ p ∈ S, ¬ p ∣ M) :
    (∑ T ∈ S.powerset.filter (fun T : Finset ℕ => M ≤ x / (∏ p ∈ T, p)),
        (∏ p ∈ T, (1 / ((p : ℝ) - 1))) *
          (∏ p ∈ S \ T, (((p : ℝ) - 2) / ((p : ℝ) - 1))) *
          (((Finset.Icc 1 (x / (∏ p ∈ T, p))).filter (fun c : ℕ => c.gcd M = 1)).card : ℝ))
      ≤ 2 * (x : ℝ) *
        (∏ p ∈ Nat.primeFactors M, (1 - 1 / (p : ℝ))) * (∏ p ∈ S, (1 - 1 / (p : ℝ))) := by
  classical
  have hM0 : M ≠ 0 := by omega
  have hP1nn : (0 : ℝ) ≤ ∏ p ∈ Nat.primeFactors M, (1 - 1 / (p : ℝ)) := by
    refine Finset.prod_nonneg ?_
    intro p hp
    have hp2 : (2 : ℝ) ≤ (p : ℝ) := by
      exact_mod_cast (Nat.prime_of_mem_primeFactors hp).two_le
    have hp0 : (0 : ℝ) < (p : ℝ) := by linarith
    have h1 : (1 : ℝ) / (p : ℝ) ≤ 1 := by
      rw [div_le_one hp0]; linarith
    linarith
  have hWnn : ∀ T ∈ S.powerset, 0 ≤ (∏ p ∈ T, (1 / ((p : ℝ) - 1))) *
      (∏ p ∈ S \ T, (((p : ℝ) - 2) / ((p : ℝ) - 1))) := by
    intro T hT
    rw [Finset.mem_powerset] at hT
    refine mul_nonneg (Finset.prod_nonneg ?_) (Finset.prod_nonneg ?_)
    · intro p hp
      have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast (hS p (hT hp)).two_le
      have hden : (0 : ℝ) < (p : ℝ) - 1 := by linarith
      positivity
    · intro p hp
      have hp2 : (2 : ℝ) ≤ (p : ℝ) :=
        by exact_mod_cast (hS p (Finset.mem_sdiff.mp hp).1).two_le
      have hden : (0 : ℝ) < (p : ℝ) - 1 := by linarith
      have hnum : (0 : ℝ) ≤ (p : ℝ) - 2 := by linarith
      positivity
  have hterm : ∀ T ∈ S.powerset.filter (fun T : Finset ℕ => M ≤ x / (∏ p ∈ T, p)),
      (∏ p ∈ T, (1 / ((p : ℝ) - 1))) *
        (∏ p ∈ S \ T, (((p : ℝ) - 2) / ((p : ℝ) - 1))) *
        (((Finset.Icc 1 (x / (∏ p ∈ T, p))).filter (fun c : ℕ => c.gcd M = 1)).card : ℝ)
      ≤ 2 * (x : ℝ) * (∏ p ∈ Nat.primeFactors M, (1 - 1 / (p : ℝ))) *
        ((∏ p ∈ T, (1 / ((p : ℝ) - 1))) *
          (∏ p ∈ S \ T, (((p : ℝ) - 2) / ((p : ℝ) - 1))) * (∏ p ∈ T, (p : ℝ))⁻¹) := by
    intro T hT
    rw [Finset.mem_filter, Finset.mem_powerset] at hT
    obtain ⟨hTS, hTM⟩ := hT
    have hW := hWnn T (Finset.mem_powerset.mpr hTS)
    have hfilter : (Nat.primeFactors M).filter (fun p : ℕ => p ≤ x / (∏ p ∈ T, p))
        = Nat.primeFactors M := by
      refine Finset.filter_true_of_mem ?_
      intro p hp
      have hpM : p ≤ M := Nat.le_of_dvd (by omega) (Nat.dvd_of_mem_primeFactors hp)
      exact le_trans hpM hTM
    have hQle : (∏ p ∈ (Nat.primeFactors M).filter (fun p : ℕ => p ≤ x / (∏ p ∈ T, p)), p)
        ≤ x / (∏ p ∈ T, p) := by
      rw [hfilter]
      exact le_trans (prod_primeFactors_le M hM0) hTM
    have hcnt := coprime_count_le_two_mul_of_le M (x / (∏ p ∈ T, p)) hM (by omega) hQle
    rw [hfilter] at hcnt
    have h2 : 2 * (((x / (∏ p ∈ T, p) : ℕ)) : ℝ) *
        (∏ p ∈ Nat.primeFactors M, (1 - 1 / (p : ℝ)))
        ≤ 2 * ((x : ℝ) / (∏ p ∈ T, (p : ℝ))) *
          (∏ p ∈ Nat.primeFactors M, (1 - 1 / (p : ℝ))) := by
      refine mul_le_mul_of_nonneg_right ?_ hP1nn
      refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
      have h := Nat.cast_div_le (α := ℝ) (m := x) (n := ∏ p ∈ T, p)
      simpa using h
    calc (∏ p ∈ T, (1 / ((p : ℝ) - 1))) *
          (∏ p ∈ S \ T, (((p : ℝ) - 2) / ((p : ℝ) - 1))) *
          (((Finset.Icc 1 (x / (∏ p ∈ T, p))).filter (fun c : ℕ => c.gcd M = 1)).card : ℝ)
        ≤ ((∏ p ∈ T, (1 / ((p : ℝ) - 1))) *
            (∏ p ∈ S \ T, (((p : ℝ) - 2) / ((p : ℝ) - 1)))) *
          (2 * (((x / (∏ p ∈ T, p) : ℕ)) : ℝ) *
            (∏ p ∈ Nat.primeFactors M, (1 - 1 / (p : ℝ)))) :=
          mul_le_mul_of_nonneg_left hcnt hW
      _ ≤ ((∏ p ∈ T, (1 / ((p : ℝ) - 1))) *
            (∏ p ∈ S \ T, (((p : ℝ) - 2) / ((p : ℝ) - 1)))) *
          (2 * ((x : ℝ) / (∏ p ∈ T, (p : ℝ))) *
            (∏ p ∈ Nat.primeFactors M, (1 - 1 / (p : ℝ)))) :=
          mul_le_mul_of_nonneg_left h2 hW
      _ = 2 * (x : ℝ) * (∏ p ∈ Nat.primeFactors M, (1 - 1 / (p : ℝ))) *
          ((∏ p ∈ T, (1 / ((p : ℝ) - 1))) *
            (∏ p ∈ S \ T, (((p : ℝ) - 2) / ((p : ℝ) - 1))) * (∏ p ∈ T, (p : ℝ))⁻¹) := by
          have hTpos : (0 : ℝ) < ∏ p ∈ T, (p : ℝ) :=
            Finset.prod_pos (fun p hp => by
              have := hS p (hTS hp)
              exact_mod_cast this.pos)
          field_simp
  calc (∑ T ∈ S.powerset.filter (fun T : Finset ℕ => M ≤ x / (∏ p ∈ T, p)),
        (∏ p ∈ T, (1 / ((p : ℝ) - 1))) *
          (∏ p ∈ S \ T, (((p : ℝ) - 2) / ((p : ℝ) - 1))) *
          (((Finset.Icc 1 (x / (∏ p ∈ T, p))).filter (fun c : ℕ => c.gcd M = 1)).card : ℝ))
      ≤ ∑ T ∈ S.powerset.filter (fun T : Finset ℕ => M ≤ x / (∏ p ∈ T, p)),
          2 * (x : ℝ) * (∏ p ∈ Nat.primeFactors M, (1 - 1 / (p : ℝ))) *
            ((∏ p ∈ T, (1 / ((p : ℝ) - 1))) *
              (∏ p ∈ S \ T, (((p : ℝ) - 2) / ((p : ℝ) - 1))) * (∏ p ∈ T, (p : ℝ))⁻¹) :=
        Finset.sum_le_sum hterm
    _ ≤ ∑ T ∈ S.powerset, 2 * (x : ℝ) * (∏ p ∈ Nat.primeFactors M, (1 - 1 / (p : ℝ))) *
            ((∏ p ∈ T, (1 / ((p : ℝ) - 1))) *
              (∏ p ∈ S \ T, (((p : ℝ) - 2) / ((p : ℝ) - 1))) * (∏ p ∈ T, (p : ℝ))⁻¹) := by
        refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) ?_
        intro T hT _
        refine mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (by positivity)) hP1nn) ?_
        refine mul_nonneg (hWnn T hT) ?_
        exact inv_nonneg.mpr (Finset.prod_nonneg (fun p hp => by positivity))
    _ = 2 * (x : ℝ) * (∏ p ∈ Nat.primeFactors M, (1 - 1 / (p : ℝ))) *
          (∑ T ∈ S.powerset, (∏ p ∈ T, (1 / ((p : ℝ) - 1))) *
              (∏ p ∈ S \ T, (((p : ℝ) - 2) / ((p : ℝ) - 1))) * (∏ p ∈ T, (p : ℝ))⁻¹) := by
        rw [Finset.mul_sum]
    _ = 2 * (x : ℝ) * (∏ p ∈ Nat.primeFactors M, (1 - 1 / (p : ℝ))) *
          (∏ p ∈ S, (1 - 1 / (p : ℝ))) := by
        rw [sum_weight_div_eq_prod S hS]


/-! ## (S2) The `R`-free (rough) count and its exact recursions -/

/-- The number of `d ≤ y` divisible by no prime of the finite set `R`. -/
def rough (R : Finset ℕ) (y : ℕ) : ℕ :=
  ((Finset.Icc 1 y).filter (fun d : ℕ => ∀ p ∈ R, ¬ p ∣ d)).card

lemma rough_le_self (R : Finset ℕ) (y : ℕ) : rough R y ≤ y := by
  unfold rough
  calc ((Finset.Icc 1 y).filter (fun d : ℕ => ∀ p ∈ R, ¬ p ∣ d)).card
      ≤ (Finset.Icc 1 y).card := Finset.card_le_card (Finset.filter_subset _ _)
    _ = y := by rw [Nat.card_Icc]; omega

/-- Monotonicity in the set of sieving primes: adding primes can only remove integers. -/
lemma rough_mono {R R' : Finset ℕ} (h : R ⊆ R') (y : ℕ) : rough R' y ≤ rough R y := by
  unfold rough
  refine Finset.card_le_card ?_
  intro d hd
  rw [Finset.mem_filter] at hd ⊢
  exact ⟨hd.1, fun p hp => hd.2 p (h hp)⟩

/-- **Largest-prime recursion** (exact).  If `p ∈ R` is the largest element of `R`, then the
`R`-free integers up to `y` are the `(R ∖ {p})`-free ones that are not divisible by `p`. -/
theorem rough_recursion_largest (R : Finset ℕ) (hR : ∀ q ∈ R, q.Prime) {p : ℕ} (hp : p ∈ R)
    (y : ℕ) :
    rough R y = rough (R.erase p) y - rough (R.erase p) (y / p) := by
  classical
  have hR' : ∀ q ∈ R.erase p, q.Prime := fun q hq => hR q (Finset.mem_of_mem_erase hq)
  have hset : (Finset.Icc 1 y).filter (fun d : ℕ => ∀ q ∈ R, ¬ q ∣ d)
      = ((Finset.Icc 1 y).filter (fun d : ℕ => ∀ q ∈ R.erase p, ¬ q ∣ d)).filter
          (fun d : ℕ => ¬ p ∣ d) := by
    ext d
    simp only [Finset.mem_filter]
    constructor
    · intro hd
      exact ⟨⟨hd.1, fun q hq => hd.2 q (Finset.mem_of_mem_erase hq)⟩, hd.2 p hp⟩
    · intro hd
      refine ⟨hd.1.1, fun q hq => ?_⟩
      rcases eq_or_ne q p with rfl | hne
      · exact hd.2
      · exact hd.1.2 q (Finset.mem_erase.mpr ⟨hne, hq⟩)
  -- the `p ∣ d` part of the `(R∖p)`-free set is in bijection with the `(R∖p)`-free `e ≤ y/p`
  have hbij : (((Finset.Icc 1 y).filter (fun d : ℕ => ∀ q ∈ R.erase p, ¬ q ∣ d)).filter
        (fun d : ℕ => p ∣ d)).card = rough (R.erase p) (y / p) := by
    unfold rough
    refine Finset.card_bij (fun d _ => d / p) ?_ ?_ ?_
    · intro d hd
      rw [Finset.mem_filter, Finset.mem_filter] at hd
      obtain ⟨⟨hdI, hdfree⟩, hpdvd⟩ := hd
      rw [Finset.mem_Icc] at hdI
      rw [Finset.mem_filter, Finset.mem_Icc]
      refine ⟨⟨?_, Nat.div_le_div_right hdI.2⟩, ?_⟩
      · exact (Nat.one_le_div_iff (hR p hp).pos).mpr (Nat.le_of_dvd (by omega) hpdvd)
      · intro q hq hqd
        have hqd' : q ∣ d := by
          have hmul : q ∣ p * (d / p) := dvd_mul_of_dvd_right hqd p
          rwa [Nat.mul_div_cancel' hpdvd] at hmul
        exact hdfree q hq hqd'
    · intro d1 hd1 d2 hd2 h
      rw [Finset.mem_filter, Finset.mem_filter] at hd1 hd2
      rw [← Nat.mul_div_cancel' hd1.2, ← Nat.mul_div_cancel' hd2.2, h]
    · intro e he
      rw [Finset.mem_filter, Finset.mem_Icc] at he
      obtain ⟨⟨he1, he2⟩, hefree⟩ := he
      refine ⟨p * e, ?_, ?_⟩
      · rw [Finset.mem_filter, Finset.mem_filter, Finset.mem_Icc]
        refine ⟨⟨⟨by nlinarith [(hR p hp).two_le], ?_⟩, ?_⟩, dvd_mul_right p e⟩
        · have hmul := (Nat.le_div_iff_mul_le (hR p hp).pos).mp he2
          simpa [mul_comm] using hmul
        · intro q hq hqpe
          have hqp : q ≠ p := fun h => Finset.notMem_erase p R (h ▸ hq)
          rcases (hR' q hq).dvd_mul.mp hqpe with h' | h'
          · exact hqp ((Nat.prime_dvd_prime_iff_eq (hR' q hq) (hR p hp)).mp h')
          · exact hefree q hq h'
      · exact Nat.mul_div_cancel_left e (hR p hp).pos
  -- assemble
  have h1 : rough R y = (((Finset.Icc 1 y).filter
      (fun d : ℕ => ∀ q ∈ R.erase p, ¬ q ∣ d)).filter (fun d : ℕ => ¬ p ∣ d)).card := by
    unfold rough
    rw [hset]
  have hsum := Finset.card_filter_add_card_filter_not
    (s := (Finset.Icc 1 y).filter (fun d : ℕ => ∀ q ∈ R.erase p, ¬ q ∣ d))
    (p := fun d : ℕ => p ∣ d)
  have hsum' : rough (R.erase p) y = rough (R.erase p) (y / p) + rough R y := by
    have hL : ((((Finset.Icc 1 y).filter (fun d : ℕ => ∀ q ∈ R.erase p, ¬ q ∣ d))).filter
        (fun d : ℕ => p ∣ d)).card = rough (R.erase p) (y / p) := hbij
    have hR2 : ((((Finset.Icc 1 y).filter (fun d : ℕ => ∀ q ∈ R.erase p, ¬ q ∣ d))).filter
        (fun d : ℕ => ¬ p ∣ d)).card = rough R y := h1.symm
    have hs : ((Finset.Icc 1 y).filter (fun d : ℕ => ∀ q ∈ R.erase p, ¬ q ∣ d)).card
        = rough (R.erase p) y := rfl
    rw [hL, hR2, hs] at hsum
    linarith
  omega

/-- **Smallest-prime (Buchstab) recursion** (exact).  Partitioning the integers `≤ y` that are
divisible by some prime of `R` according to their *smallest* `R`-divisor gives
`rough R y = y - Σ_{p ∈ R} rough (R.filter (· < p)) (y / p)`. -/
theorem rough_recursion_smallest (R : Finset ℕ) (hR : ∀ q ∈ R, q.Prime) (y : ℕ) :
    rough R y = y - ∑ p ∈ R, rough (R.filter (fun q => q < p)) (y / p) := by
  classical
  -- the set of "bad" integers and its partition by the smallest `R`-divisor
  have hBiUnion : (Finset.Icc 1 y).filter (fun d : ℕ => ¬ ∀ p ∈ R, ¬ p ∣ d)
      = R.biUnion (fun p => (Finset.Icc 1 y).filter
          (fun d : ℕ => p ∣ d ∧ ∀ q ∈ R, q < p → ¬ q ∣ d)) := by
    ext d
    constructor
    · intro hd
      rw [Finset.mem_filter] at hd
      obtain ⟨hdI, hdbad⟩ := hd
      simp only [not_forall, not_not] at hdbad
      obtain ⟨p, hpR, hpd⟩ := hdbad
      have hne : (R.filter (fun q => q ∣ d)).Nonempty :=
        ⟨p, Finset.mem_filter.mpr ⟨hpR, hpd⟩⟩
      obtain ⟨hp0R, hp0d⟩ := Finset.mem_filter.mp (Finset.min'_mem (R.filter fun q => q ∣ d) hne)
      have hmin : ∀ q ∈ R, q ∣ d → (R.filter (fun q => q ∣ d)).min' hne ≤ q :=
        fun q hq hqd => Finset.min'_le (R.filter (fun q => q ∣ d)) q
          (Finset.mem_filter.mpr ⟨hq, hqd⟩)
      rw [Finset.mem_biUnion]
      refine ⟨(R.filter (fun q => q ∣ d)).min' hne, hp0R, ?_⟩
      rw [Finset.mem_filter]
      exact ⟨hdI, hp0d, fun q hqR hqlt hqd => absurd (hmin q hqR hqd) (by omega)⟩
    · intro hd
      rw [Finset.mem_biUnion] at hd
      obtain ⟨p, hpR, hdmem⟩ := hd
      rw [Finset.mem_filter] at hdmem ⊢
      exact ⟨hdmem.1, by simp only [not_forall, not_not]; exact ⟨p, hpR, hdmem.2.1⟩⟩
  -- disjointness of the pieces
  have hdisj : ∀ x ∈ R, ∀ z ∈ R, x ≠ z →
      Disjoint ((Finset.Icc 1 y).filter (fun d : ℕ => x ∣ d ∧ ∀ q ∈ R, q < x → ¬ q ∣ d))
        ((Finset.Icc 1 y).filter (fun d : ℕ => z ∣ d ∧ ∀ q ∈ R, q < z → ¬ q ∣ d)) := by
    intro x hx z hz hxz
    rw [Finset.disjoint_left]
    intro d hdx hdz
    rw [Finset.mem_filter] at hdx hdz
    rcases lt_or_gt_of_ne hxz with hlt | hlt
    · exact hdz.2.2 x hx hlt hdx.2.1
    · exact hdx.2.2 z hz hlt hdz.2.1
  -- per-prime count via the bijection `d ↦ d / p`
  have hterm : ∀ p ∈ R, ((Finset.Icc 1 y).filter
        (fun d : ℕ => p ∣ d ∧ ∀ q ∈ R, q < p → ¬ q ∣ d)).card
      = rough (R.filter (fun q => q < p)) (y / p) := by
    intro p hp
    have hpp : p.Prime := hR p hp
    unfold rough
    refine Finset.card_bij (fun d _ => d / p) ?_ ?_ ?_
    · intro d hd
      rw [Finset.mem_filter] at hd
      obtain ⟨hdI, hpd, hdfree⟩ := hd
      rw [Finset.mem_Icc] at hdI
      rw [Finset.mem_filter, Finset.mem_Icc]
      refine ⟨⟨?_, Nat.div_le_div_right hdI.2⟩, ?_⟩
      · exact (Nat.one_le_div_iff hpp.pos).mpr (Nat.le_of_dvd (by omega) hpd)
      · intro q hq hqd
        have hqR : q ∈ R := (Finset.mem_filter.mp hq).1
        have hqp : q < p := (Finset.mem_filter.mp hq).2
        have hqd' : q ∣ d := by
          have hmul : q ∣ p * (d / p) := dvd_mul_of_dvd_right hqd p
          rwa [Nat.mul_div_cancel' hpd] at hmul
        exact hdfree q hqR hqp hqd'
    · intro d1 hd1 d2 hd2 h
      rw [Finset.mem_filter] at hd1 hd2
      rw [← Nat.mul_div_cancel' hd1.2.1, ← Nat.mul_div_cancel' hd2.2.1, h]
    · intro e he
      rw [Finset.mem_filter, Finset.mem_Icc] at he
      obtain ⟨⟨he1, he2⟩, hefree⟩ := he
      refine ⟨p * e, ?_, ?_⟩
      · rw [Finset.mem_filter, Finset.mem_Icc]
        refine ⟨⟨by nlinarith [hpp.two_le], ?_⟩, dvd_mul_right p e, ?_⟩
        · have hmul := (Nat.le_div_iff_mul_le hpp.pos).mp he2
          simpa [mul_comm] using hmul
        · intro q hqR hqp hqpe
          have hqne : q ≠ p := by omega
          rcases (hR q hqR).dvd_mul.mp hqpe with h' | h'
          · exact hqne ((Nat.prime_dvd_prime_iff_eq (hR q hqR) hpp).mp h')
          · exact hefree q (Finset.mem_filter.mpr ⟨hqR, hqp⟩) h'
      · exact Nat.mul_div_cancel_left e hpp.pos
  -- complement: `rough R y + (bad).card = y`
  have hsum : (∑ p ∈ R, ((Finset.Icc 1 y).filter
      (fun d : ℕ => p ∣ d ∧ ∀ q ∈ R, q < p → ¬ q ∣ d)).card)
      = ∑ p ∈ R, rough (R.filter (fun q => q < p)) (y / p) :=
    Finset.sum_congr rfl hterm
  have hcompl := Finset.card_filter_add_card_filter_not
    (s := Finset.Icc 1 y) (p := fun d : ℕ => ∀ p ∈ R, ¬ p ∣ d)
  rw [Nat.card_Icc] at hcompl
  rw [hBiUnion, Finset.card_biUnion hdisj, hsum] at hcompl
  have hgood : ((Finset.Icc 1 y).filter (fun d : ℕ => ∀ p ∈ R, ¬ p ∣ d)).card = rough R y := rfl
  rw [hgood] at hcompl
  omega

/-- **Band prime count (Chebyshev).**  For `x ≥ 100` the number of primes in `(√x, x]`
is at most `(1 - log 2 - 1/50)·x`.  Proof: `#(band)·(log x / 2) ≤ ∑_{p∈band} log p ≤ θ(x)`
and `θ(x) ≤ log 3 · x` (`Commons.NumberTheory.Chebyshev.theta_le_log3_mul`), while
`log x ≥ log 2200 ≥ 11 log 2 + 152/2200 ≥ 7.69` for `x ≥ 2200`; the finite front
`100 ≤ x ≤ 2199` is checked with `native_decide` over `ℚ`. -/
lemma band_prime_count_le (x : ℕ) (hx : 100 ≤ x) :
    (((Finset.Ioc (Nat.sqrt x) x).filter (fun p : ℕ => p.Prime)).card : ℝ) ≤
      (1 - Real.log 2 - 1 / 50) * (x : ℝ) := by
  by_cases hsmall : x ≤ 2199
  · have hcheck : ∀ y ∈ Finset.Icc 100 2199,
        (((Finset.Ioc (Nat.sqrt y) y).filter (fun p : ℕ => p.Prime)).card : ℚ) ≤
          (2868528192 / 10 ^ 10) * (y : ℚ) := by native_decide
    have hcast : (((Finset.Ioc (Nat.sqrt x) x).filter (fun p : ℕ => p.Prime)).card : ℝ) ≤
        (2868528192 / 10 ^ 10 : ℝ) * (x : ℝ) := by
      have hQ := hcheck x (Finset.mem_Icc.mpr ⟨hx, hsmall⟩)
      have h1 : ((((Finset.Ioc (Nat.sqrt x) x).filter (fun p : ℕ => p.Prime)).card : ℚ) : ℝ) ≤
          (((2868528192 : ℚ) / 10 ^ 10 : ℚ) : ℝ) * ((x : ℚ) : ℝ) := by
        exact_mod_cast hQ
      simpa using h1
    have hcoef : (2868528192 / 10 ^ 10 : ℝ) ≤ 1 - Real.log 2 - 1 / 50 := by
      have h2 := Real.log_two_lt_d9
      have hnum : (2868528192 : ℝ) / 10 ^ 10 = 0.2868528192 := by norm_num
      rw [hnum]
      linarith
    calc (((Finset.Ioc (Nat.sqrt x) x).filter (fun p : ℕ => p.Prime)).card : ℝ)
        ≤ (2868528192 / 10 ^ 10 : ℝ) * (x : ℝ) := hcast
      _ ≤ (1 - Real.log 2 - 1 / 50) * (x : ℝ) :=
          mul_le_mul_of_nonneg_right hcoef (by positivity)
  · push_neg at hsmall
    have hx2200 : 2200 ≤ x := by omega
    have hstep1 : (((Finset.Ioc (Nat.sqrt x) x).filter (fun p : ℕ => p.Prime)).card : ℝ) *
        (Real.log (x : ℝ) / 2) ≤ Chebyshev.theta (x : ℝ) := by
      have hterm : ∀ p ∈ (Finset.Ioc (Nat.sqrt x) x).filter (fun p : ℕ => p.Prime),
          Real.log (x : ℝ) / 2 ≤ Real.log (p : ℝ) := by
        intro p hp
        rw [Finset.mem_filter] at hp
        obtain ⟨hpI, hpp⟩ := hp
        rw [Finset.mem_Ioc] at hpI
        have hsp : Nat.sqrt x < p := hpI.1
        have hpx : p ≤ x := hpI.2
        have hlt : Real.sqrt (x : ℝ) < (p : ℝ) := by
          rw [Real.sqrt_lt' (by exact_mod_cast hpp.pos)]
          have hnat : x < p * p := Nat.sqrt_lt.mp hsp
          have hreal : (x : ℝ) < (p : ℝ) * (p : ℝ) := by exact_mod_cast hnat
          simpa [pow_two] using hreal
        have h := Real.log_le_log (Real.sqrt_pos.mpr (by positivity)) (le_of_lt hlt)
        rwa [Real.log_sqrt (by positivity)] at h
      calc (((Finset.Ioc (Nat.sqrt x) x).filter (fun p : ℕ => p.Prime)).card : ℝ) *
              (Real.log (x : ℝ) / 2)
          = ∑ p ∈ (Finset.Ioc (Nat.sqrt x) x).filter (fun p : ℕ => p.Prime),
              (Real.log (x : ℝ) / 2) := by
            rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ ∑ p ∈ (Finset.Ioc (Nat.sqrt x) x).filter (fun p : ℕ => p.Prime),
              Real.log (p : ℝ) := Finset.sum_le_sum hterm
        _ ≤ Chebyshev.theta (x : ℝ) := by
            rw [Chebyshev.theta, Nat.floor_natCast]
            refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
            · intro p hp
              rw [Finset.mem_filter] at hp ⊢
              obtain ⟨hpI, hpp⟩ := hp
              have hmem := Finset.mem_Ioc.mp hpI
              exact ⟨Finset.mem_Ioc.mpr ⟨Nat.lt_of_le_of_lt (Nat.zero_le _) hmem.1, hmem.2⟩, hpp⟩
            · intro p hp _
              exact Real.log_nonneg (by exact_mod_cast (Nat.Prime.one_le (Finset.mem_filter.mp hp).2))
    have hstep2 : Chebyshev.theta (x : ℝ) ≤ Real.log 3 * (x : ℝ) :=
      Commons.NumberTheory.Chebyshev.theta_le_log3_mul x
    have hlogx : (7.69 : ℝ) ≤ Real.log (x : ℝ) := by
      have hmono : Real.log (2200 : ℝ) ≤ Real.log (x : ℝ) :=
        Real.log_le_log (by norm_num) (by exact_mod_cast hx2200)
      have hsplit : Real.log (2200 : ℝ) = Real.log (2048 : ℝ) + Real.log ((2200 : ℝ) / 2048) := by
        rw [← Real.log_mul (by norm_num) (by norm_num)]
        norm_num
      have h2048 : Real.log (2048 : ℝ) = 11 * Real.log 2 := by
        rw [show (2048 : ℝ) = 2 ^ 11 by norm_num, Real.log_pow]
        norm_num
      have hlow2 : 11 * (0.6931471803 : ℝ) ≤ Real.log (2048 : ℝ) := by
        rw [h2048]
        linarith [Real.log_two_gt_d9]
      have hfrac : (0.069 : ℝ) ≤ Real.log ((2200 : ℝ) / 2048) := by
        have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2048 / 2200 by norm_num)
        rw [show ((2200 : ℝ) / 2048) = ((2048 : ℝ) / 2200)⁻¹ by norm_num, Real.log_inv]
        linarith
      linarith
    have hlogxpos : 0 < Real.log (x : ℝ) := by linarith
    have hcard_le : (((Finset.Ioc (Nat.sqrt x) x).filter (fun p : ℕ => p.Prime)).card : ℝ) ≤
        2 * Real.log 3 * (x : ℝ) / Real.log (x : ℝ) := by
      have h := le_trans hstep1 hstep2
      have h2 : (((Finset.Ioc (Nat.sqrt x) x).filter (fun p : ℕ => p.Prime)).card : ℝ) *
          Real.log (x : ℝ) ≤ 2 * Real.log 3 * (x : ℝ) := by linarith
      rw [le_div_iff₀ hlogxpos]
      linarith
    calc (((Finset.Ioc (Nat.sqrt x) x).filter (fun p : ℕ => p.Prime)).card : ℝ)
        ≤ 2 * Real.log 3 * (x : ℝ) / Real.log (x : ℝ) := hcard_le
      _ = (2 * Real.log 3 / Real.log (x : ℝ)) * (x : ℝ) := by ring
      _ ≤ (1 - Real.log 2 - 1 / 50) * (x : ℝ) := by
          refine mul_le_mul_of_nonneg_right ?_ (by positivity)
          rw [div_le_iff₀ hlogxpos]
          have h3 := Real.log_three_lt_d9
          have h2 := Real.log_two_lt_d9
          nlinarith [hlogx, h3, h2]

/-- **Finite front of brick B.**  For `100 ≤ x ≤ 3000` the reciprocal sum over primes in
`(√x, x]` is at most `7131/10000`, verified exactly over `ℚ` by `native_decide`. -/
lemma band_recip_le_front (x : ℕ) (hx : 100 ≤ x) (hx3 : x ≤ 3000) :
    (∑ p ∈ (Finset.Ioc (Nat.sqrt x) x).filter (fun p : ℕ => p.Prime), (1 : ℝ) / (p : ℝ)) ≤
      7131 / 10000 := by
  have hcheck : ∀ y ∈ Finset.Icc 100 3000,
      (∑ p ∈ (Finset.Ioc (Nat.sqrt y) y).filter (fun p : ℕ => p.Prime), (1 : ℚ) / (p : ℚ)) ≤
        7131 / 10000 := by native_decide
  have hQ := hcheck x (Finset.mem_Icc.mpr ⟨hx, hx3⟩)
  have hcast : ((∑ p ∈ (Finset.Ioc (Nat.sqrt x) x).filter (fun p : ℕ => p.Prime),
      (1 : ℚ) / (p : ℚ)) : ℝ) =
      (∑ p ∈ (Finset.Ioc (Nat.sqrt x) x).filter (fun p : ℕ => p.Prime), (1 : ℝ) / (p : ℝ)) := by
    push_cast
    ring
  rw [← hcast]
  have hQ' : ((∑ p ∈ (Finset.Ioc (Nat.sqrt x) x).filter (fun p : ℕ => p.Prime),
      (1 : ℚ) / (p : ℚ)) : ℝ) ≤ ((7131 / 10000 : ℚ) : ℝ) := by exact_mod_cast hQ
  have hnum : ((7131 / 10000 : ℚ) : ℝ) = 7131 / 10000 := by norm_num
  rw [hnum] at hQ'
  exact hQ'

/-- **θ-squeeze for the band count.**  `#(band)·(log x / 2) ≤ ∑_{p ∈ band} log p ≤ θ(x)`:
every prime of the band exceeds `√x`, so its logarithm is at least `log x / 2`. -/
lemma band_card_mul_half_log_le_theta (x : ℕ) (hx : 0 < x) :
    (((Finset.Ioc (Nat.sqrt x) x).filter (fun p : ℕ => p.Prime)).card : ℝ) *
        (Real.log (x : ℝ) / 2) ≤ Chebyshev.theta (x : ℝ) := by
  have hterm : ∀ p ∈ (Finset.Ioc (Nat.sqrt x) x).filter (fun p : ℕ => p.Prime),
      Real.log (x : ℝ) / 2 ≤ Real.log (p : ℝ) := by
    intro p hp
    rw [Finset.mem_filter] at hp
    obtain ⟨hpI, hpp⟩ := hp
    rw [Finset.mem_Ioc] at hpI
    have hsp : Nat.sqrt x < p := hpI.1
    have hlt : Real.sqrt (x : ℝ) < (p : ℝ) := by
      rw [Real.sqrt_lt' (by exact_mod_cast hpp.pos)]
      have hnat : x < p * p := Nat.sqrt_lt.mp hsp
      have hreal : (x : ℝ) < (p : ℝ) * (p : ℝ) := by exact_mod_cast hnat
      simpa [pow_two] using hreal
    have h := Real.log_le_log (Real.sqrt_pos.mpr (by exact_mod_cast hx)) (le_of_lt hlt)
    rwa [Real.log_sqrt (by positivity)] at h
  calc (((Finset.Ioc (Nat.sqrt x) x).filter (fun p : ℕ => p.Prime)).card : ℝ) *
          (Real.log (x : ℝ) / 2)
      = ∑ p ∈ (Finset.Ioc (Nat.sqrt x) x).filter (fun p : ℕ => p.Prime),
          (Real.log (x : ℝ) / 2) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ∑ p ∈ (Finset.Ioc (Nat.sqrt x) x).filter (fun p : ℕ => p.Prime),
          Real.log (p : ℝ) := Finset.sum_le_sum hterm
    _ ≤ Chebyshev.theta (x : ℝ) := by
        rw [Chebyshev.theta, Nat.floor_natCast]
        refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
        · intro p hp
          rw [Finset.mem_filter] at hp ⊢
          obtain ⟨hpI, hpp⟩ := hp
          have hmem := Finset.mem_Ioc.mp hpI
          exact ⟨Finset.mem_Ioc.mpr ⟨Nat.lt_of_le_of_lt (Nat.zero_le _) hmem.1, hmem.2⟩, hpp⟩
        · intro p hp _
          exact Real.log_nonneg (by exact_mod_cast (Nat.Prime.one_le (Finset.mem_filter.mp hp).2))

/-- **Sharpened brick A, asymptotic half.**  For `x ≥ 6600` the number of primes in
`(√x, x]` is at most `x/4`: `#(band) ≤ 2 log 3 · x / log x ≤ x/4` since
`log x ≥ log 6600 ≥ 8 log 3` (as `6600 = 3^8·1.00594…`). -/
lemma band_prime_count_le'_tail (x : ℕ) (hx : 6600 ≤ x) :
    (((Finset.Ioc (Nat.sqrt x) x).filter (fun p : ℕ => p.Prime)).card : ℝ) ≤ (1 / 4) * (x : ℝ) := by
  have h1 := band_card_mul_half_log_le_theta x (by omega)
  have h2 : Chebyshev.theta (x : ℝ) ≤ Real.log 3 * (x : ℝ) :=
    Commons.NumberTheory.Chebyshev.theta_le_log3_mul x
  have hlogx : (8 * Real.log 3 : ℝ) ≤ Real.log (x : ℝ) := by
    have hmono : Real.log (6600 : ℝ) ≤ Real.log (x : ℝ) :=
      Real.log_le_log (by norm_num) (by exact_mod_cast hx)
    have hsplit : Real.log (6600 : ℝ) = Real.log (6561 : ℝ) + Real.log ((6600 : ℝ) / 6561) := by
      rw [← Real.log_mul (by norm_num) (by norm_num)]
      norm_num
    have h6561 : Real.log (6561 : ℝ) = 8 * Real.log 3 := by
      rw [show (6561 : ℝ) = 3 ^ 8 by norm_num, Real.log_pow]
      norm_num
    have hfrac : (0 : ℝ) ≤ Real.log ((6600 : ℝ) / 6561) := by
      apply Real.log_nonneg
      norm_num
    linarith
  have hlogxpos : 0 < Real.log (x : ℝ) := by
    have := Real.log_three_gt_d9
    linarith
  have hcard_le : (((Finset.Ioc (Nat.sqrt x) x).filter (fun p : ℕ => p.Prime)).card : ℝ) ≤
      2 * Real.log 3 * (x : ℝ) / Real.log (x : ℝ) := by
    rw [le_div_iff₀ hlogxpos]
    linarith
  have hratio : 2 * Real.log 3 / Real.log (x : ℝ) ≤ 1 / 4 := by
    rw [div_le_iff₀ hlogxpos]
    linarith
  calc (((Finset.Ioc (Nat.sqrt x) x).filter (fun p : ℕ => p.Prime)).card : ℝ)
      ≤ 2 * Real.log 3 * (x : ℝ) / Real.log (x : ℝ) := hcard_le
    _ = (2 * Real.log 3 / Real.log (x : ℝ)) * (x : ℝ) := by ring
    _ ≤ (1 / 4) * (x : ℝ) := mul_le_mul_of_nonneg_right hratio (by positivity)


/-- **Sharpened brick A, finite front.**  For `100 ≤ x ≤ 6599` the band count is at most `x/4`,
checked exactly over `ℚ` by `native_decide` (equivalently `4·#(band) ≤ x`). -/
lemma band_prime_count_le'_front (x : ℕ) (hx : 100 ≤ x) (hx6 : x ≤ 6599) :
    (((Finset.Ioc (Nat.sqrt x) x).filter (fun p : ℕ => p.Prime)).card : ℝ) ≤ (1 / 4) * (x : ℝ) := by
  have hcheck : ∀ y ∈ Finset.Icc 100 6599,
      4 * (((Finset.Ioc (Nat.sqrt y) y).filter (fun p : ℕ => p.Prime)).card : ℚ) ≤ (y : ℚ) := by
    native_decide
  have hQ := hcheck x (Finset.mem_Icc.mpr ⟨hx, hx6⟩)
  have hR : ((4 : ℝ) * (((Finset.Ioc (Nat.sqrt x) x).filter (fun p : ℕ => p.Prime)).card : ℝ) ≤
      (x : ℝ)) := by exact_mod_cast hQ
  linarith

/-- **Sharpened brick A**: `#(primes in (√x, x]) ≤ x/4` for all `x ≥ 100`. -/
lemma band_prime_count_le' (x : ℕ) (hx : 100 ≤ x) :
    (((Finset.Ioc (Nat.sqrt x) x).filter (fun p : ℕ => p.Prime)).card : ℝ) ≤ (1 / 4) * (x : ℝ) := by
  by_cases h : x ≤ 6599
  · exact band_prime_count_le'_front x hx h
  · exact band_prime_count_le'_tail x (by omega)

/-- **The `log 2` of brick B.**  `log log x − log log √x = log 2` for `x > 1`
(since `log √x = log x / 2`). -/
lemma log_log_sub_log_log_sqrt {x : ℝ} (hx : 1 < x) :
    Real.log (Real.log x) - Real.log (Real.log (Real.sqrt x)) = Real.log 2 := by
  have hx0 : 0 < x := by linarith
  have hlogx : 0 < Real.log x := Real.log_pos hx
  rw [Real.log_sqrt (le_of_lt hx0)]
  rw [Real.log_div (ne_of_gt hlogx) (by norm_num : (2 : ℝ) ≠ 0)]
  ring

/-- **The band is the difference of the two prime prefixes.**  For `x ≥ 1`,
`Σ_{p ≤ x} 1/p = Σ_{p ≤ √x} 1/p + Σ_{p ∈ (√x, x], p prime} 1/p`
(as Finset sums over `Nat.primesLE` and the band). -/
lemma primesLE_sum_eq_add_band (x : ℕ) :
    (∑ p ∈ Nat.primesLE x, (1 : ℝ) / (p : ℝ)) =
      (∑ p ∈ Nat.primesLE (Nat.sqrt x), (1 : ℝ) / (p : ℝ)) +
        ∑ p ∈ (Finset.Ioc (Nat.sqrt x) x).filter (fun p : ℕ => p.Prime), (1 : ℝ) / (p : ℝ) := by
  have hsq : Nat.sqrt x ≤ x := Nat.sqrt_le_self x
  have h1 : (Nat.primesLE x).filter (fun p : ℕ => p ≤ Nat.sqrt x) = Nat.primesLE (Nat.sqrt x) := by
    ext p
    simp only [Finset.mem_filter, Nat.mem_primesLE]
    constructor
    · rintro ⟨⟨hpx, hpp⟩, hps⟩
      exact ⟨hps, hpp⟩
    · rintro ⟨hps, hpp⟩
      exact ⟨⟨le_trans hps hsq, hpp⟩, hps⟩
  have h2 : (Nat.primesLE x).filter (fun p : ℕ => ¬ p ≤ Nat.sqrt x) =
      (Finset.Ioc (Nat.sqrt x) x).filter (fun p : ℕ => p.Prime) := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_Ioc, Nat.mem_primesLE]
    constructor
    · rintro ⟨⟨hpx, hpp⟩, hps⟩
      exact ⟨⟨not_le.mp hps, hpx⟩, hpp⟩
    · rintro ⟨⟨hsp, hpx⟩, hpp⟩
      exact ⟨⟨hpx, hpp⟩, not_le.mpr hsp⟩
  rw [← Finset.sum_filter_add_sum_filter_not (s := Nat.primesLE x)
        (p := fun p : ℕ => p ≤ Nat.sqrt x) (f := fun p : ℕ => (1 : ℝ) / (p : ℝ)), h1, h2]

/-- **Tail of brick B, conditional on the two-point second-Mertens oscillator.**
The exact split `Σ_{p ≤ x} 1/p = Σ_{p ≤ √x} 1/p + Σ_{band} 1/p` (`primesLE_sum_eq_add_band`)
turns the band sum into `log 2 + (E(x) − E(√x))`; hence any bound on the renormalised
oscillator `(Σ_{p≤x}1/p − Σ_{p≤√x}1/p) − log 2` of size `(13/100)/log x` gives the band
bound `≤ 3/4` for `x ≥ 10⁴` (where `log x ≥ 8 log 3`). -/
lemma band_recip_le_tail_of_osc (x : ℕ) (hx : 10000 ≤ x)
    (hosc : ((∑ p ∈ Nat.primesLE x, (1 : ℝ) / (p : ℝ)) -
              (∑ p ∈ Nat.primesLE (Nat.sqrt x), (1 : ℝ) / (p : ℝ))) - Real.log 2 ≤
            (13 / 100) / Real.log (x : ℝ)) :
    (∑ p ∈ (Finset.Ioc (Nat.sqrt x) x).filter (fun p : ℕ => p.Prime), (1 : ℝ) / (p : ℝ)) ≤ 3 / 4 := by
  have hsplit := primesLE_sum_eq_add_band x
  have hlogx : (8 * Real.log 3 : ℝ) ≤ Real.log (x : ℝ) := by
    have hmono : Real.log (6561 : ℝ) ≤ Real.log (x : ℝ) :=
      Real.log_le_log (by norm_num) (by exact_mod_cast (by omega : 6561 ≤ x))
    have h6561 : Real.log (6561 : ℝ) = 8 * Real.log 3 := by
      rw [show (6561 : ℝ) = 3 ^ 8 by norm_num, Real.log_pow]
      norm_num
    linarith
  have hlogxpos : 0 < Real.log (x : ℝ) := by
    have := Real.log_three_gt_d9
    linarith
  have hnum : (13 / 100) / Real.log (x : ℝ) ≤ 3 / 4 - Real.log 2 := by
    rw [div_le_iff₀ hlogxpos]
    have h3 := Real.log_three_gt_d9
    have h2 := Real.log_two_lt_d9
    have hlogx' : (8.78 : ℝ) ≤ Real.log (x : ℝ) := by linarith
    have hcoef : (0.0568 : ℝ) ≤ 3 / 4 - Real.log 2 := by linarith
    nlinarith [hlogx', hcoef]
  linarith

/-- Integrability of `u ↦ u⁻¹` on `[s,t]` for `2 ≤ s ≤ t`. -/
private lemma intervalIntegrable_inv_Icc {s t : ℝ} (hs : 2 ≤ s) (hst : s ≤ t) :
    IntervalIntegrable (fun u : ℝ => u⁻¹) MeasureTheory.volume s t := by
  refine ContinuousOn.intervalIntegrable ?_
  refine ContinuousOn.inv₀ continuousOn_id ?_
  intro u hu
  rw [Set.uIcc_of_le hst] at hu
  have : s ≤ u := hu.1
  linarith

/-- `(θ u − u)/u² = θ u/u² − u⁻¹` as integrals on `[s,t]`. -/
private lemma integral_sub_inv {s t : ℝ} (hs : 2 ≤ s) (hst : s ≤ t) :
    (∫ u in s..t, (Chebyshev.theta u - u) / (u * u))
      = (∫ u in s..t, Chebyshev.theta u / (u * u)) - ∫ u in s..t, u⁻¹ := by
  rw [← intervalIntegral.integral_sub]
  · apply intervalIntegral.integral_congr
    intro u hu
    rw [Set.uIcc_of_le hst] at hu
    have hu0 : u ≠ 0 := by
      have : s ≤ u := hu.1
      linarith
    field_simp
  · exact Commons.NumberTheory.Mertens.intervalIntegrable_theta_div_id_sq_gen hs hst
  · exact intervalIntegrable_inv_Icc hs hst

/-- **Variation identity for the first-Mertens error.**  For `2 ≤ s ≤ t`,
`(logDiv t − log t) − (logDiv s − log s) = (θ t/t − θ s/s) + ∫_s^t (θ u − u)/u² du`.
This is the two-point form of `Commons.NumberTheory.Mertens.logDiv_eq_theta_div_add_integral`
(`logDiv x = θ x/x + ∫_2^x θ u/u² du`): the additive constant cancels in the difference, the
interval splits as `∫_2^t = ∫_2^s + ∫_s^t`, and `∫_s^t du/u = log t − log s` supplies the `−u`
part of the integrand. -/
theorem logDiv_variation {s t : ℝ} (hs : 2 ≤ s) (hst : s ≤ t) :
    (Commons.NumberTheory.Mertens.logDiv t - Real.log t) -
        (Commons.NumberTheory.Mertens.logDiv s - Real.log s)
      = (Chebyshev.theta t / t - Chebyshev.theta s / s) +
        ∫ u in s..t, (Chebyshev.theta u - u) / (u * u) := by
  have ht : 2 ≤ t := le_trans hs hst
  have h1 := Commons.NumberTheory.Mertens.logDiv_eq_theta_div_add_integral ht
  have h2 := Commons.NumberTheory.Mertens.logDiv_eq_theta_div_add_integral hs
  have hsplit : (∫ u in (2 : ℝ)..t, Chebyshev.theta u / (u * u)) =
      (∫ u in (2 : ℝ)..s, Chebyshev.theta u / (u * u)) +
        ∫ u in s..t, Chebyshev.theta u / (u * u) :=
    (intervalIntegral.integral_add_adjacent_intervals
      (Commons.NumberTheory.Mertens.intervalIntegrable_theta_div_id_sq hs)
      (Commons.NumberTheory.Mertens.intervalIntegrable_theta_div_id_sq_gen hs hst)).symm
  have huIcc : (0 : ℝ) ∉ Set.uIcc s t := by
    rw [Set.uIcc_of_le hst]
    intro h
    have hs0 : s ≤ (0 : ℝ) := h.1
    linarith
  have hlog : (∫ u in s..t, u⁻¹) = Real.log t - Real.log s := by
    rw [integral_inv huIcc, Real.log_div (by linarith : t ≠ 0) (by linarith : s ≠ 0)]
  have hsub := integral_sub_inv hs hst
  rw [h1, h2, hsub]
  linarith [hsplit, hlog]

/-- **Bracket bound (step 2a).**  Under the envelope `|θ u − u| ≤ εu` on `[s,t]` (`2 ≤ s ≤ t`),
`|θ t/t − θ s/s| ≤ 2ε`, since `θ u/u − 1 = (θ u − u)/u`. -/
lemma theta_div_sub_div_le {s t : ℝ} (hs : 2 ≤ s) (hst : s ≤ t) {ε : ℝ}
    (hθ : ∀ u : ℝ, s ≤ u → u ≤ t → |Chebyshev.theta u - u| ≤ ε * u) :
    |Chebyshev.theta t / t - Chebyshev.theta s / s| ≤ 2 * ε := by
  have hs0 : (0 : ℝ) < s := by linarith
  have ht0 : (0 : ℝ) < t := by linarith
  have ht' : |Chebyshev.theta t / t - 1| ≤ ε := by
    have h := hθ t hst le_rfl
    rw [div_sub_one ht0.ne', abs_div, abs_of_pos ht0, div_le_iff₀ ht0]
    exact h
  have hs' : |Chebyshev.theta s / s - 1| ≤ ε := by
    have h := hθ s le_rfl hst
    rw [div_sub_one hs0.ne', abs_div, abs_of_pos hs0, div_le_iff₀ hs0]
    exact h
  have hsplit : Chebyshev.theta t / t - Chebyshev.theta s / s
      = (Chebyshev.theta t / t - 1) - (Chebyshev.theta s / s - 1) := by ring
  rw [hsplit]
  have htri : |(Chebyshev.theta t / t - 1) - (Chebyshev.theta s / s - 1)| ≤
      |Chebyshev.theta t / t - 1| + |Chebyshev.theta s / s - 1| := by
    rw [abs_sub_le_iff]
    constructor <;>
      linarith [le_abs_self (Chebyshev.theta t / t - 1),
        le_abs_self (Chebyshev.theta s / s - 1), neg_abs_le (Chebyshev.theta t / t - 1),
        neg_abs_le (Chebyshev.theta s / s - 1)]
  linarith [htri, ht', hs']

/-- **Step 1 of the `osc_of_theta_envelope` plan.**  Instantiate
`Commons.NumberTheory.Mertens.primeRecips_loglog_diff` at `(√x, x)` with `B₁ = 0`: the two-point
difference of `primeRecips − log log` is the two bracket terms `(logDiv − log)/log` at the endpoints
plus `∫_{√x}^{x} (logDiv t − log t)/(t (log t)²) dt`. -/
lemma primeRecips_loglog_two_point_zero {x : ℝ} (hx : 10000 ≤ x) :
    (Commons.NumberTheory.Mertens.primeRecips x - Real.log (Real.log x)) -
        (Commons.NumberTheory.Mertens.primeRecips (Real.sqrt x) -
          Real.log (Real.log (Real.sqrt x))) =
      ((Commons.NumberTheory.Mertens.logDiv x - Real.log x) / Real.log x -
        (Commons.NumberTheory.Mertens.logDiv (Real.sqrt x) - Real.log (Real.sqrt x)) /
          Real.log (Real.sqrt x)) +
      ∫ t in (Real.sqrt x)..x,
        (Commons.NumberTheory.Mertens.logDiv t - Real.log t) / (t * (Real.log t) ^ 2) := by
  have hx0 : (0 : ℝ) < x := by linarith
  have hs : (2 : ℝ) ≤ Real.sqrt x := by
    have h4 : Real.sqrt 4 ≤ Real.sqrt x := Real.sqrt_le_sqrt (by linarith : (4 : ℝ) ≤ x)
    have h42 : Real.sqrt 4 = 2 := by rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
    linarith [h4, h42.symm.le, h42.le]
  have hle : Real.sqrt x ≤ x := by
    have := Real.sqrt_le_sqrt (le_of_lt hx0)
    nlinarith [Real.sq_sqrt (le_of_lt hx0), hx0]
  have h := Commons.NumberTheory.Mertens.primeRecips_loglog_diff (B₁ := 0) hs hle
  simpa using h

/-- **Integral half of step 2b.**  Under the envelope `|θ u − u| ≤ εu` on `[s,t]` (`2 ≤ s ≤ t`),
`|∫_s^t (θ u − u)/u² du| ≤ ε(log t − log s)`: the integrand splits as `θ u/u² − u⁻¹`, the triangle
inequality for integrals reduces it to `∫ ε/u`, and `∫_s^t du/u = log t − log s`. -/
theorem integral_theta_sub_div_le {s t : ℝ} (hs : 2 ≤ s) (hst : s ≤ t) {ε : ℝ}
    (hθ : ∀ u : ℝ, s ≤ u → u ≤ t → |Chebyshev.theta u - u| ≤ ε * u) :
    |∫ u in s..t, (Chebyshev.theta u - u) / (u * u)| ≤ ε * (Real.log t - Real.log s) := by
  have hs0 : (0 : ℝ) < s := by linarith
  have huIcc : (0 : ℝ) ∉ Set.uIcc s t := by
    rw [Set.uIcc_of_le hst]
    intro h
    linarith [h.1]
  have hIθ : IntervalIntegrable (fun u : ℝ => Chebyshev.theta u / (u * u)) MeasureTheory.volume s t :=
    Commons.NumberTheory.Mertens.intervalIntegrable_theta_div_id_sq_gen hs hst
  have hIinv : IntervalIntegrable (fun u : ℝ => u⁻¹) MeasureTheory.volume s t :=
    intervalIntegrable_inv_Icc hs hst
  have hfun : (fun u : ℝ => (Chebyshev.theta u - u) / (u * u))
      = fun u : ℝ => Chebyshev.theta u / (u * u) - u⁻¹ := by
    funext u
    by_cases hu0 : u = 0
    · subst hu0
      simp
    · field_simp
  have hIf : IntervalIntegrable (fun u : ℝ => (Chebyshev.theta u - u) / (u * u))
      MeasureTheory.volume s t := by
    rw [hfun]
    exact hIθ.sub hIinv
  have hIε : IntervalIntegrable (fun u : ℝ => ε / u) MeasureTheory.volume s t := by
    have h := hIinv.const_mul ε
    simpa [div_eq_mul_inv] using h
  calc |∫ u in s..t, (Chebyshev.theta u - u) / (u * u)|
      ≤ ∫ u in s..t, |(Chebyshev.theta u - u) / (u * u)| :=
        intervalIntegral.abs_integral_le_integral_abs hst
    _ ≤ ∫ u in s..t, ε / u := by
        refine intervalIntegral.integral_mono_on hst hIf.abs hIε ?_
        intro u hu
        have hu0 : (0 : ℝ) < u := by linarith [hu.1]
        have h := hθ u hu.1 hu.2
        rw [abs_div, abs_mul, abs_of_pos hu0]
        rw [div_le_div_iff₀ (mul_pos hu0 hu0) hu0]
        nlinarith [h, hu0]
    _ = ε * (Real.log t - Real.log s) := by
        rw [show (fun u : ℝ => ε / u) = fun u => ε * u⁻¹ by
          funext u; rw [div_eq_mul_inv]]
        rw [intervalIntegral.integral_const_mul, integral_inv huIcc,
            Real.log_div (by linarith : t ≠ 0) (by linarith : s ≠ 0)]

/-- **Step 2 in full: the variation bound.**  Under the envelope `|θ u − u| ≤ εu` on `[s,t]`
(`2 ≤ s ≤ t`), the first-Mertens error has variation at most `2ε + ε(log t − log s)`:
combining `logDiv_variation` with the bracket bound `theta_div_sub_div_le` and the integral bound
`integral_theta_sub_div_le` via the triangle inequality. -/
theorem logDiv_variation_bound {s t : ℝ} (hs : 2 ≤ s) (hst : s ≤ t) {ε : ℝ}
    (hθ : ∀ u : ℝ, s ≤ u → u ≤ t → |Chebyshev.theta u - u| ≤ ε * u) :
    |(Commons.NumberTheory.Mertens.logDiv t - Real.log t) -
        (Commons.NumberTheory.Mertens.logDiv s - Real.log s)|
      ≤ 2 * ε + ε * (Real.log t - Real.log s) := by
  rw [logDiv_variation hs hst]
  have h1 := theta_div_sub_div_le hs hst hθ
  have h2 := integral_theta_sub_div_le hs hst hθ
  calc |(Chebyshev.theta t / t - Chebyshev.theta s / s) +
        ∫ u in s..t, (Chebyshev.theta u - u) / (u * u)|
      ≤ |Chebyshev.theta t / t - Chebyshev.theta s / s| +
        |∫ u in s..t, (Chebyshev.theta u - u) / (u * u)| := by
        rw [abs_le]
        constructor <;>
          linarith [le_abs_self (Chebyshev.theta t / t - Chebyshev.theta s / s),
            neg_abs_le (Chebyshev.theta t / t - Chebyshev.theta s / s),
            le_abs_self (∫ u in s..t, (Chebyshev.theta u - u) / (u * u)),
            neg_abs_le (∫ u in s..t, (Chebyshev.theta u - u) / (u * u))]
    _ ≤ 2 * ε + ε * (Real.log t - Real.log s) := by linarith

/-- `1/log √x = 2/log x` for `x > 1` (used to merge the two endpoint brackets of
`primeRecips_loglog_two_point_zero`, which carry `1/log √x` resp. `1/log x`). -/
lemma inv_log_sqrt {x : ℝ} (hx : 1 < x) : 1 / Real.log (Real.sqrt x) = 2 / Real.log x := by
  have hx0 : (0 : ℝ) < x := by linarith
  have hlog : Real.log x ≠ 0 := ne_of_gt (Real.log_pos hx)
  rw [Real.log_sqrt (le_of_lt hx0)]
  field_simp

/-- Positivity of the two logarithms appearing in the assembly, for `x ≥ 10⁴`. -/
lemma log_pos_of_ge_ten_thousand {x : ℝ} (hx : 10000 ≤ x) :
    0 < Real.log x ∧ 0 < Real.log (Real.sqrt x) := by
  have hx1 : (1 : ℝ) < x := by linarith
  have hx0 : (0 : ℝ) < x := by linarith
  refine ⟨Real.log_pos hx1, ?_⟩
  rw [Real.log_sqrt (le_of_lt hx0)]
  have := Real.log_pos hx1
  linarith

/-- **Bridge B.**  `⌊√x⌋₊ = Nat.sqrt x` for natural `x` (there is no `Nat.floor_sqrt` in Mathlib).
Both sides are pinned by `n² ≤ x < (n+1)²`: `Nat.sqrt_le'` / `Nat.lt_succ_sqrt` on the left,
`Nat.le_floor` / `Nat.floor_lt` + `Real.le_sqrt'` / `Real.sqrt_lt'` on the right.  Note the
argument-position asymmetry: `Real.le_sqrt'`'s explicit argument is the *left*-hand side (with `0 < a`),
whereas `Real.sqrt_lt'`'s is the *bound* `y` — hence the positivity obligations differ. -/
lemma floor_sqrt_eq_sqrt (x : ℕ) : ⌊Real.sqrt (x : ℝ)⌋₊ = Nat.sqrt x := by
  rcases x with _ | x
  · simp
  · have h1 : (Nat.sqrt (x + 1) : ℝ) ≤ Real.sqrt ((x + 1 : ℕ) : ℝ) := by
      have hpos : (0 : ℝ) < (Nat.sqrt (x + 1) : ℝ) := by
        exact_mod_cast Nat.sqrt_pos.mpr (by omega : 0 < x + 1)
      rw [Real.le_sqrt' hpos]
      exact_mod_cast Nat.sqrt_le' (x + 1)
    have h2 : Real.sqrt ((x + 1 : ℕ) : ℝ) < ((Nat.sqrt (x + 1) + 1 : ℕ) : ℝ) := by
      rw [Real.sqrt_lt' (by positivity : (0 : ℝ) < ((Nat.sqrt (x + 1) + 1 : ℕ) : ℝ)), pow_two]
      push_cast
      have h := Nat.lt_succ_sqrt (x + 1)
      simp only [Nat.succ_eq_add_one] at h
      exact_mod_cast h
    have h3 : Nat.sqrt (x + 1) ≤ ⌊Real.sqrt ((x + 1 : ℕ) : ℝ)⌋₊ := Nat.le_floor h1
    have h4 : ⌊Real.sqrt ((x + 1 : ℕ) : ℝ)⌋₊ < Nat.sqrt (x + 1) + 1 :=
      (Nat.floor_lt (Real.sqrt_nonneg _)).mpr h2
    omega

/-- **Bridge A (ℕ → ℝ).**  For a natural number the `Nat.primesLE` reciprocal sum agrees with
`Commons.NumberTheory.Mertens.primeRecips`, whose definition is `∑ p ∈ (⌊X⌋₊).primesLE, 1/p`, using
`Nat.floor_natCast`.  This is the bridge from the `Nat.primesLE`-form of `osc_of_theta_envelope`
to the `primeRecips`-form of every proved Mertens ingredient. -/
lemma primeRecips_nat_eq_sum (x : ℕ) :
    (∑ p ∈ Nat.primesLE x, (1 : ℝ) / (p : ℝ)) =
      Commons.NumberTheory.Mertens.primeRecips (x : ℝ) := by
  rw [Commons.NumberTheory.Mertens.primeRecips, Nat.floor_natCast]

/-- **Route A at `(√x, x)`.**  The variation bound `logDiv_variation_bound` specialised to
`(s,t) = (√x, x)`: the right-hand side is `2ε + ε(log x − log √x) = 2ε + (ε/2)·log x` (since
`log √x = (log x)/2`).  Note: **no `log 2` here** — the `log 2` of the socket's target comes solely
from `log log x − log log √x = log 2` (`log_log_sub_log_log_sqrt`), through the `primeRecips − log log`
combination of `primeRecips_loglog_two_point_zero`. -/
lemma logDiv_variation_bound_sqrt {x : ℝ} (hx : 10000 ≤ x) {ε : ℝ}
    (hθ : ∀ u : ℝ, Real.sqrt x ≤ u → u ≤ x → |Chebyshev.theta u - u| ≤ ε * u) :
    |(Commons.NumberTheory.Mertens.logDiv x - Real.log x) -
        (Commons.NumberTheory.Mertens.logDiv (Real.sqrt x) - Real.log (Real.sqrt x))|
      ≤ 2 * ε + ε * (Real.log x - Real.log (Real.sqrt x)) := by
  have hx0 : (0 : ℝ) < x := by linarith
  have hs : (2 : ℝ) ≤ Real.sqrt x := by
    have h4 : Real.sqrt 4 ≤ Real.sqrt x := Real.sqrt_le_sqrt (by linarith : (4 : ℝ) ≤ x)
    have h42 : Real.sqrt 4 = 2 := by rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
    linarith [h4, h42.symm.le, h42.le]
  have hle : Real.sqrt x ≤ x := by
    have := Real.sqrt_le_sqrt (le_of_lt hx0)
    nlinarith [Real.sq_sqrt (le_of_lt hx0), hx0]
  exact logDiv_variation_bound hs hle hθ

/-- **Route A at `(√x, u)`** for `√x ≤ u ≤ x` — the pointwise estimate needed to bound the
integral term of `primeRecips_loglog_two_point_zero` in `osc_of_theta_envelope`.  Instantiation of
`logDiv_variation_bound` at `(s,t) = (√x, u)`, with the socket's envelope restricted to `[√x, u]`. -/
lemma logDiv_variation_bound_sqrt_le {x u : ℝ} (hx : 10000 ≤ x) {ε : ℝ}
    (hu : Real.sqrt x ≤ u) (hux : u ≤ x)
    (hθ : ∀ v : ℝ, Real.sqrt x ≤ v → v ≤ x → |Chebyshev.theta v - v| ≤ ε * v) :
    |(Commons.NumberTheory.Mertens.logDiv u - Real.log u) -
        (Commons.NumberTheory.Mertens.logDiv (Real.sqrt x) - Real.log (Real.sqrt x))|
      ≤ 2 * ε + ε * (Real.log u - Real.log (Real.sqrt x)) := by
  have hx0 : (0 : ℝ) < x := by linarith
  have hs : (2 : ℝ) ≤ Real.sqrt x := by
    have h4 : Real.sqrt 4 ≤ Real.sqrt x := Real.sqrt_le_sqrt (by linarith : (4 : ℝ) ≤ x)
    have h42 : Real.sqrt 4 = 2 := by rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
    linarith [h4, h42.symm.le, h42.le]
  exact logDiv_variation_bound hs hu (fun v hv hvu => hθ v hv (le_trans hvu hux))

/-! ## (S00) Bernoulli product bound

`1 - Σ_{i∈s} f i ≤ ∏_{i∈s} (1 - f i)` for `0 ≤ f i ≤ 1`.  This is the product bound
that turns the crude sieve identity `prefixCount ≤ x + |S| - x·Σ 1/p` into the
shell estimate `prefixCount ≤ 2x·∏(1-1/p)`. -/

lemma one_sub_sum_le_prod_one_sub {ι : Type*} (s : Finset ι) (f : ι → ℝ)
    (h0 : ∀ i ∈ s, 0 ≤ f i) (h1 : ∀ i ∈ s, f i ≤ 1) :
    1 - ∑ i ∈ s, f i ≤ ∏ i ∈ s, (1 - f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
      have ha0 : 0 ≤ f a := h0 a (Finset.mem_insert_self a s)
      have ha1 : f a ≤ 1 := h1 a (Finset.mem_insert_self a s)
      have h0' : ∀ i ∈ s, 0 ≤ f i := fun i hi => h0 i (Finset.mem_insert_of_mem hi)
      have h1' : ∀ i ∈ s, f i ≤ 1 := fun i hi => h1 i (Finset.mem_insert_of_mem hi)
      have hih := ih h0' h1'
      rw [Finset.sum_insert ha, Finset.prod_insert ha]
      have hs0 : 0 ≤ ∑ i ∈ s, f i := Finset.sum_nonneg h0'
      have hmul : (1 - f a) * (1 - ∑ i ∈ s, f i) ≤ (1 - f a) * ∏ i ∈ s, (1 - f i) :=
        mul_le_mul_of_nonneg_left hih (by linarith)
      nlinarith [mul_nonneg ha0 hs0]

/-- The count of `c ∈ [1,x]` divisible by none of the primes of `S`. -/
def prefixCount (x : ℕ) (S : Finset ℕ) : ℕ :=
  ((Finset.Icc 1 x).filter (fun c : ℕ => ∀ p ∈ S, ¬ p ∣ c)).card

/-- **Disjoint-multiples count.**  If every `p ∈ S` is a prime exceeding `y` and `x < y*y`,
then no `c ≤ x` is divisible by two distinct elements of `S` (their product exceeds `y*y > x`),
so the set of `c ≤ x` divisible by some `p ∈ S` is a disjoint union of the sets of multiples,
of cardinality `∑_{p ∈ S} x / p`. -/
lemma shell_bad_card (x : ℕ) (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) {y : ℕ}
    (hyy : x < y * y) (hy : ∀ p ∈ S, y < p) :
    ((Finset.Icc 1 x).filter (fun c : ℕ => ∃ p ∈ S, p ∣ c)).card = ∑ p ∈ S, x / p := by
  classical
  have hdisj : (S : Set ℕ).PairwiseDisjoint
      (fun p : ℕ => (Finset.Icc 1 x).filter (fun c : ℕ => p ∣ c)) := by
    intro p hp q hq hpq
    rw [Function.onFun, Finset.disjoint_left]
    intro c hcp hcq
    rw [Finset.mem_filter] at hcp hcq
    have hcop : p.Coprime q := (Nat.coprime_primes (hS p hp) (hS q hq)).mpr hpq
    have hpqc : p * q ∣ c := hcop.mul_dvd_of_dvd_of_dvd hcp.2 hcq.2
    have hc1 : 1 ≤ c := (Finset.mem_Icc.mp hcp.1).1
    have hc1x : c ≤ x := (Finset.mem_Icc.mp hcp.1).2
    have hle : p * q ≤ x := le_trans (Nat.le_of_dvd (by omega) hpqc) hc1x
    have h1 : y < p := hy p hp
    have h2 : y < q := hy q hq
    nlinarith
  have hBunion : (Finset.Icc 1 x).filter (fun c : ℕ => ∃ p ∈ S, p ∣ c)
      = S.biUnion (fun p : ℕ => (Finset.Icc 1 x).filter (fun c : ℕ => p ∣ c)) := by
    ext c
    simp only [Finset.mem_filter, Finset.mem_biUnion]
    constructor
    · rintro ⟨hc, p, hpS, hpc⟩
      exact ⟨p, hpS, hc, hpc⟩
    · rintro ⟨p, hpS, hc, hpc⟩
      exact ⟨hc, p, hpS, hpc⟩
  rw [hBunion, Finset.card_biUnion hdisj]
  refine Finset.sum_congr rfl ?_
  intro p _
  exact Commons.NumberTheory.Nat.card_multiples_Icc x p

/-- **Crude shell identity**: `prefixCount x S = x - ∑_{p ∈ S} x / p`. -/
lemma prefixCount_eq_sub_sum (x : ℕ) (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) {y : ℕ}
    (hyy : x < y * y) (hy : ∀ p ∈ S, y < p) :
    prefixCount x S = x - ∑ p ∈ S, x / p := by
  classical
  have hcard := shell_bad_card x S hS hyy hy
  have hcompl := Finset.card_filter_add_card_filter_not
    (s := Finset.Icc 1 x) (p := fun c : ℕ => ∀ p ∈ S, ¬ p ∣ c)
  rw [Nat.card_Icc] at hcompl
  have hset : (Finset.Icc 1 x).filter (fun c : ℕ => ¬ ∀ p ∈ S, ¬ p ∣ c)
      = (Finset.Icc 1 x).filter (fun c : ℕ => ∃ p ∈ S, p ∣ c) := by
    refine Finset.filter_congr ?_
    intro c _
    constructor
    · intro h
      by_contra hcon
      exact h (fun p hp hpc => hcon ⟨p, hp, hpc⟩)
    · rintro ⟨p, hp, hpc⟩ h
      exact h p hp hpc
  rw [hset, hcard] at hcompl
  rw [prefixCount]
  omega

/-- The sum of the multiples counts is at most `x` (it counts a subset of `[1,x]`). -/
lemma sum_div_le_self (x : ℕ) (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) {y : ℕ}
    (hyy : x < y * y) (hy : ∀ p ∈ S, y < p) :
    ∑ p ∈ S, x / p ≤ x := by
  have h := shell_bad_card x S hS hyy hy
  calc ∑ p ∈ S, x / p = ((Finset.Icc 1 x).filter (fun c : ℕ => ∃ p ∈ S, p ∣ c)).card := h.symm
    _ ≤ (Finset.Icc 1 x).card := Finset.card_le_card (Finset.filter_subset _ _)
    _ = x := by rw [Nat.card_Icc]; omega

/-- **Conditional u = 2 shell bound** (the two band bricks are the only input). -/
theorem prefixCount_shell_le_of_bricks (x : ℕ) (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime)
    {y : ℕ} (hyy : x < y * y) (hy : ∀ p ∈ S, y < p)
    (hcard : (S.card : ℝ) ≤ (1 - Real.log 2 - 1 / 50) * (x : ℝ))
    (hrecip : (∑ p ∈ S, (1 : ℝ) / (p : ℝ)) ≤ Real.log 2 + 1 / 50) :
    (prefixCount x S : ℝ) ≤ 2 * (x : ℝ) * ∏ p ∈ S, (1 - 1 / (p : ℝ)) := by
  classical
  have hsub := prefixCount_eq_sub_sum x S hS hyy hy
  have hsumx := sum_div_le_self x S hS hyy hy
  -- per-term: `(x/p : ℕ) ≥ x/p - 1`
  have hterm : ∀ p ∈ S, (x : ℝ) / (p : ℝ) - 1 ≤ ((x / p : ℕ) : ℝ) := by
    intro p hp
    have hp0 : (0 : ℝ) < (p : ℝ) := by
      have := hS p hp; exact_mod_cast this.pos
    have hnat : x < p * (x / p) + p := by
      have h := Nat.div_add_mod x p
      have hmod := Nat.mod_lt x (by have := hS p hp; exact this.pos)
      omega
    have hreal : (x : ℝ) < (p : ℝ) * ((x / p : ℕ) : ℝ) + (p : ℝ) := by
      have : ((x : ℕ) : ℝ) < ((p * (x / p) + p : ℕ) : ℝ) := by exact_mod_cast hnat
      push_cast at this ⊢
      linarith
    rw [div_sub_one hp0.ne']
    rw [div_le_iff₀ hp0]
    linarith
  have hcast : ((∑ p ∈ S, x / p : ℕ) : ℝ) = ∑ p ∈ S, ((x / p : ℕ) : ℝ) := by push_cast; ring
  have hsum_ge : (∑ p ∈ S, (x : ℝ) / (p : ℝ)) - (S.card : ℝ) ≤ ((∑ p ∈ S, x / p : ℕ) : ℝ) := by
    have hcard1 : (S.card : ℝ) = ∑ p ∈ S, (1 : ℝ) := by simp
    rw [hcard1, ← Finset.sum_sub_distrib, hcast]
    refine Finset.sum_le_sum ?_
    intro p hp
    have := hterm p hp
    linarith
  have hxsum : (∑ p ∈ S, (x : ℝ) / (p : ℝ)) = (x : ℝ) * ∑ p ∈ S, (1 : ℝ) / (p : ℝ) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro p hp
    ring
  have hpre : (prefixCount x S : ℝ) = (x : ℝ) - ((∑ p ∈ S, x / p : ℕ) : ℝ) := by
    rw [hsub]
    exact Nat.cast_sub hsumx
  have hA : (S.card : ℝ) + (x : ℝ) * (∑ p ∈ S, (1 : ℝ) / (p : ℝ)) ≤ (x : ℝ) := by
    have hx0 : (0 : ℝ) ≤ (x : ℝ) := by positivity
    have := mul_le_mul_of_nonneg_left hrecip hx0
    linarith
  have hbern : 1 - (∑ p ∈ S, (1 : ℝ) / (p : ℝ)) ≤ ∏ p ∈ S, (1 - 1 / (p : ℝ)) := by
    refine one_sub_sum_le_prod_one_sub S (fun p => (1 : ℝ) / (p : ℝ)) ?_ ?_
    · intro p hp
      positivity
    · intro p hp
      have hp2 : (2 : ℝ) ≤ (p : ℝ) := by
        have := hS p hp; exact_mod_cast this.two_le
      rw [div_le_one (by linarith)]
      linarith
  have hx0 : (0 : ℝ) ≤ (x : ℝ) := by positivity
  calc (prefixCount x S : ℝ) = (x : ℝ) - ((∑ p ∈ S, x / p : ℕ) : ℝ) := hpre
    _ ≤ (x : ℝ) - ((x : ℝ) * (∑ p ∈ S, (1 : ℝ) / (p : ℝ)) - (S.card : ℝ)) := by
          linarith [hsum_ge, hxsum]
    _ ≤ 2 * (x : ℝ) - 2 * ((x : ℝ) * (∑ p ∈ S, (1 : ℝ) / (p : ℝ))) := by linarith
    _ = 2 * (x : ℝ) * (1 - (∑ p ∈ S, (1 : ℝ) / (p : ℝ))) := by ring
    _ ≤ 2 * (x : ℝ) * ∏ p ∈ S, (1 - 1 / (p : ℝ)) :=
          mul_le_mul_of_nonneg_left hbern (by positivity)

/-! ## (S0) Reduction of the sigma-window sum to a weighted divisor sum

For each `c` and each prime `p ≥ 2`,
`sw p c ≤ (1 - 1/p) * (1 + 1/(p-1))^{[p ∣ c]}`, and consequently
`∏_{p ∈ S} sw p c ≤ (∏_{p ∈ S}(1 - 1/p)) * ∏_{p ∈ S, p ∣ c}(1 + 1/(p-1))`.
This reduces the sigma-window sum to a sum of the (multiplicative, divisor-supported)
weight `∏_{p ∣ c, p ∈ S}(1 + 1/(p-1))`. -/

lemma sw_prod_le (c : ℕ) (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) :
    (∏ p ∈ S, sw p c) ≤
      (∏ p ∈ S, (1 - 1 / (p : ℝ))) *
        ∏ p ∈ S.filter (fun p : ℕ => p ∣ c), (1 + 1 / ((p : ℝ) - 1)) := by
  classical
  set T : Finset ℕ := S.filter (fun p : ℕ => p ∣ c) with hT
  set U : Finset ℕ := S.filter (fun p : ℕ => ¬ p ∣ c) with hU
  have hsplit : (∏ p ∈ S, sw p c) = (∏ p ∈ T, sw p c) * (∏ p ∈ U, sw p c) := by
    rw [hT, hU, ← Finset.prod_filter_mul_prod_filter_not (s := S) (p := fun p : ℕ => p ∣ c)]
  have hsplit2 : (∏ p ∈ S, (1 - 1 / (p : ℝ))) =
      (∏ p ∈ T, (1 - 1 / (p : ℝ))) * (∏ p ∈ U, (1 - 1 / (p : ℝ))) := by
    rw [hT, hU, ← Finset.prod_filter_mul_prod_filter_not (s := S) (p := fun p : ℕ => p ∣ c)]
  have hT1 : (∏ p ∈ T, sw p c) = 1 := by
    refine Finset.prod_eq_one ?_
    intro p hp
    rw [hT, Finset.mem_filter] at hp
    unfold sw
    rw [if_pos hp.2]
  have hT3 : (∏ p ∈ T, (1 - 1 / (p : ℝ)) * (1 + 1 / ((p : ℝ) - 1))) = 1 := by
    refine Finset.prod_eq_one ?_
    intro p hp
    rw [hT, Finset.mem_filter] at hp
    have hpp : p.Prime := hS p hp.1
    have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hpp.two_le
    have hp0 : (p : ℝ) ≠ 0 := by linarith
    have hp1 : (p : ℝ) - 1 ≠ 0 := by linarith
    field_simp
    ring
  have hU_le : (∏ p ∈ U, sw p c) ≤ ∏ p ∈ U, (1 - 1 / (p : ℝ)) := by
    refine Finset.prod_le_prod₀ ?_ ?_
    · intro p hp
      rw [hU, Finset.mem_filter] at hp
      have hpp : p.Prime := hS p hp.1
      have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hpp.two_le
      unfold sw
      rw [if_neg hp.2]
      have hden : (0 : ℝ) < (p : ℝ) - 1 := by linarith
      have hnum : (0 : ℝ) ≤ (p : ℝ) - 2 := by linarith
      positivity
    · intro p hp
      rw [hU, Finset.mem_filter] at hp
      have hpp : p.Prime := hS p hp.1
      have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hpp.two_le
      have hp0 : (0 : ℝ) < (p : ℝ) := by linarith
      have hle : (1 : ℝ) / (p : ℝ) ≤ 1 := by rw [div_le_one hp0]; linarith
      unfold sw
      rw [if_neg hp.2]
      have hp0 : (0 : ℝ) < (p : ℝ) := by linarith
      have hden : (0 : ℝ) < (p : ℝ) - 1 := by linarith
      rw [show (1 : ℝ) - 1 / (p : ℝ) = ((p : ℝ) - 1) / (p : ℝ) by field_simp]
      rw [div_le_div_iff₀ hden hp0]
      ring_nf
      nlinarith [hp2]
  calc (∏ p ∈ S, sw p c) = (∏ p ∈ T, sw p c) * (∏ p ∈ U, sw p c) := hsplit
    _ = (∏ p ∈ U, sw p c) := by rw [hT1, one_mul]
    _ ≤ ∏ p ∈ U, (1 - 1 / (p : ℝ)) := hU_le
    _ = (∏ p ∈ T, (1 - 1 / (p : ℝ)) * (1 + 1 / ((p : ℝ) - 1))) *
          (∏ p ∈ U, (1 - 1 / (p : ℝ))) := by rw [hT3, one_mul]
    _ = (∏ p ∈ T, (1 - 1 / (p : ℝ))) * (∏ p ∈ U, (1 - 1 / (p : ℝ))) *
          ∏ p ∈ T, (1 + 1 / ((p : ℝ) - 1)) := by rw [Finset.prod_mul_distrib]; ring
    _ = (∏ p ∈ S, (1 - 1 / (p : ℝ))) * ∏ p ∈ T, (1 + 1 / ((p : ℝ) - 1)) := by rw [hsplit2]
    _ = (∏ p ∈ S, (1 - 1 / (p : ℝ))) *
          ∏ p ∈ S.filter (fun p : ℕ => p ∣ c), (1 + 1 / ((p : ℝ) - 1)) := by rw [hT]

/-- Summed form of `sw_prod_le`. -/
lemma swSum_le_weightSum (M N : ℕ) (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) :
    swSum M N S ≤ (∏ p ∈ S, (1 - 1 / (p : ℝ))) *
      ∑ c ∈ (Finset.Icc 1 N).filter (fun c : ℕ => c.gcd M = 1),
        ∏ p ∈ S.filter (fun p : ℕ => p ∣ c), (1 + 1 / ((p : ℝ) - 1)) := by
  rw [swSum, Finset.mul_sum]
  refine Finset.sum_le_sum ?_
  intro c _
  exact sw_prod_le c S hS

/-! ## (S) the analytic sigma-window bound (small sieve).
Open: needs the small-sieve core bound (rough-number machinery). N may be 0 (then both sides are 0). -/
lemma rpw_sigma_window_sum_le (N QR : ℕ) (S : Finset ℕ) (hQR : QR ≠ 0)
    (hS : ∀ p ∈ S, p.Prime) (hSQR : ∀ p ∈ S, ¬ p ∣ QR) :
    (∑ c ∈ (Finset.Icc 1 N).filter (fun c : ℕ => c.gcd QR = 1),
        (∏ p ∈ S, (if p ∣ c then (1 : ℝ) else (((p : ℝ) - 2) / ((p : ℝ) - 1))))) ≤
      4000 * (N : ℝ) *
        (∏ p ∈ (Nat.primeFactors QR).filter (fun p : ℕ => (p : ℝ) ≤ (N : ℝ)), (1 - 1 / (p : ℝ))) *
        (∏ p ∈ S, (1 - 1 / (p : ℝ))) := by
  have h2 := SigmaSelfWin.sigma_window_bound N QR S hQR hS hSQR
    (Work.NumberTheory.DuffinSchaeffer.SigmaAux.sum_log_div_sq_le S hS)
  have h3 : SigmaSelfWin.eprod QR (N : ℝ) =
      ∏ p ∈ (Nat.primeFactors QR).filter (fun p : ℕ => (p : ℝ) ≤ (N : ℝ)), (1 - 1 / (p : ℝ)) := rfl
  rw [h3] at h2
  exact h2

theorem reduced_pair_window_bound (q r : ℕ) (hq : 0 < q) (hr : 0 < r) (hqr : q ≠ r)
    (Δ : ℝ) (hΔ : 0 ≤ Δ) :
    let g : ℕ := q.gcd r
    let L : ℕ := q * r / g
    ((((Finset.product ((Finset.range q).filter (fun a : ℕ => a.gcd q = 1))
        ((Finset.range r).filter (fun b : ℕ => b.gcd r = 1))).filter
      (fun ab : ℕ × ℕ =>
        ‖(((ab.1 : ℝ) / (q : ℝ) : ℝ) : UnitAddCircle) -
           (((ab.2 : ℝ) / (r : ℝ) : ℝ) : UnitAddCircle)‖ < Δ)).card : ℝ) ≤
      8000 * Δ * (q.totient : ℝ) * (r.totient : ℝ) *
        ∏ p ∈ (Nat.primeFactors (q * r / (g * g))).filter (fun p : ℕ => Δ * (L : ℝ) < (p : ℝ)),
          (1 - 1 / (p : ℝ))⁻¹) := by
  classical
  dsimp
  by_cases hbig : 1 / 8 ≤ Δ
  · exact reduced_pair_window_bound_trivial q r Δ hΔ hbig
  · have hΔlt : Δ < 1 / 8 := by linarith
    by_cases hΔz : Δ = 0
    · subst Δ
      have hcnt0 : ((((Finset.product ((Finset.range q).filter (fun a : ℕ => a.gcd q = 1))
            ((Finset.range r).filter (fun b : ℕ => b.gcd r = 1))).filter
          (fun ab : ℕ × ℕ =>
            ‖(((ab.1 : ℝ) / (q : ℝ) : ℝ) : UnitAddCircle) -
               (((ab.2 : ℝ) / (r : ℝ) : ℝ) : UnitAddCircle)‖ < 0))).card) = 0 := by
        have hem : (((Finset.product ((Finset.range q).filter (fun a : ℕ => a.gcd q = 1))
            ((Finset.range r).filter (fun b : ℕ => b.gcd r = 1))).filter
          (fun ab : ℕ × ℕ =>
            ‖(((ab.1 : ℝ) / (q : ℝ) : ℝ) : UnitAddCircle) -
               (((ab.2 : ℝ) / (r : ℝ) : ℝ) : UnitAddCircle)‖ < 0))) = ∅ := by
          ext ab
          simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range]
          constructor
          · intro h
            have hlt : ‖(((ab.1 : ℝ) / (q : ℝ) : ℝ) : UnitAddCircle) -
               (((ab.2 : ℝ) / (r : ℝ) : ℝ) : UnitAddCircle)‖ < (0 : ℝ) := h.2
            have nn : (0 : ℝ) ≤ ‖(((ab.1 : ℝ) / (q : ℝ) : ℝ) : UnitAddCircle) -
               (((ab.2 : ℝ) / (r : ℝ) : ℝ) : UnitAddCircle)‖ := norm_nonneg _
            linarith
          · intro h
            simp at h
        rw [hem]
        simp
      simpa [hcnt0]

    · have hΔp : 0 < Δ := by
        exact lt_of_le_of_ne hΔ (by intro h; exact hΔz h.symm)
      let g : ℕ := q.gcd r
      let qq : ℕ := (q / g) * (r / g)
      let L : ℕ := q * r / g
      let Y : ℝ := Δ * (L : ℝ)
      let N : ℕ := Nat.ceil Y - 1
      let f : ℕ → ℝ := fun p => 1 - 1 / (p : ℝ)
      let shared : Finset ℕ := (Nat.primeFactors g).filter (fun p : ℕ => ¬ p ∣ qq)
      have hLpos : 0 < L := by dsimp [L]; exact Lpos q r hq hr
      have hYpos : 0 < Y := by dsimp [Y]; exact mul_pos hΔp (by exact_mod_cast hLpos)
      have hg : 0 < g := by dsimp [g]; exact Nat.gcd_pos_of_pos_left r hq
      have hqqn : qq ≠ 0 := by
        dsimp [qq, g]
        exact ne_of_gt (Nat.mul_pos (Nat.div_pos (Nat.gcd_le_left r hq) (Nat.gcd_pos_of_pos_left r hq))
          (Nat.div_pos (Nat.gcd_le_right q hr) (Nat.gcd_pos_of_pos_right q hr)))
      have hshared1 : ∀ p ∈ shared, p.Prime := by
        intro p hp
        exact (Nat.mem_primeFactors.mp (Finset.mem_filter.mp hp).1).1
      have hshared2 : ∀ p ∈ shared, ¬ p ∣ qq := by
        intro p hp
        exact (Finset.mem_filter.mp hp).2
      have hNltY : (N : ℝ) < Y := by dsimp [N]; exact ceil_sub_one_lt Y hYpos
      have hYleN : Y ≤ (N : ℝ) + 1 := by dsimp [N]; exact ceil_sub_one_le Y
      have hcw := count_sigma_window q r hq hr hqr Δ hΔp hΔlt
      have hcw' : ((((Finset.product ((Finset.range q).filter (fun a : ℕ => a.gcd q = 1))
            ((Finset.range r).filter (fun b : ℕ => b.gcd r = 1))).filter
          (fun ab : ℕ × ℕ =>
            ‖(((ab.1 : ℝ) / (q : ℝ) : ℝ) : UnitAddCircle) -
               (((ab.2 : ℝ) / (r : ℝ) : ℝ) : UnitAddCircle)‖ < Δ)).card : ℝ)) =
          2 * ((g.totient : ℕ) : ℝ) * (∑ c ∈ (Finset.Icc 1 N).filter (fun c : ℕ => c.gcd qq = 1),
            (∏ p ∈ shared, (if p ∣ c then (1 : ℝ) else (((p : ℝ) - 2) / ((p : ℝ) - 1))))) := by
          simpa [g, qq, L, Y, N, shared] using hcw
      have hS := rpw_sigma_window_sum_le N qq shared hqqn hshared1 hshared2
      have hSwb : (∑ c ∈ (Finset.Icc 1 N).filter (fun c : ℕ => c.gcd qq = 1),
            (∏ p ∈ shared, (if p ∣ c then (1 : ℝ) else (((p : ℝ) - 2) / ((p : ℝ) - 1))))) ≤
            4000 * (N : ℝ) * (∏ p ∈ (Nat.primeFactors qq).filter (fun p : ℕ => (p : ℝ) ≤ (N : ℝ)), f p) *
              (∏ p ∈ shared, f p) := by
          simpa [f] using hS
      have h2g : 0 ≤ 2 * ((g.totient : ℕ) : ℝ) := by positivity
      have hc1 : ((((Finset.product ((Finset.range q).filter (fun a : ℕ => a.gcd q = 1))
            ((Finset.range r).filter (fun b : ℕ => b.gcd r = 1))).filter
          (fun ab : ℕ × ℕ =>
            ‖(((ab.1 : ℝ) / (q : ℝ) : ℝ) : UnitAddCircle) -
               (((ab.2 : ℝ) / (r : ℝ) : ℝ) : UnitAddCircle)‖ < Δ)).card : ℝ)) ≤
          8000 * ((g.totient : ℕ) : ℝ) * (N : ℝ) *
            (∏ p ∈ (Nat.primeFactors qq).filter (fun p : ℕ => (p : ℝ) ≤ (N : ℝ)), f p) *
            (∏ p ∈ shared, f p) := by
          calc
            ((((Finset.product ((Finset.range q).filter (fun a : ℕ => a.gcd q = 1))
            ((Finset.range r).filter (fun b : ℕ => b.gcd r = 1))).filter
          (fun ab : ℕ × ℕ =>
            ‖(((ab.1 : ℝ) / (q : ℝ) : ℝ) : UnitAddCircle) -
               (((ab.2 : ℝ) / (r : ℝ) : ℝ) : UnitAddCircle)‖ < Δ)).card : ℝ))
              = 2 * ((g.totient : ℕ) : ℝ) * (∑ c ∈ (Finset.Icc 1 N).filter (fun c : ℕ => c.gcd qq = 1),
                  (∏ p ∈ shared, (if p ∣ c then (1 : ℝ) else (((p : ℝ) - 2) / ((p : ℝ) - 1))))) := hcw'
            _ ≤ 2 * ((g.totient : ℕ) : ℝ) * (4000 * (N : ℝ) *
                  (∏ p ∈ (Nat.primeFactors qq).filter (fun p : ℕ => (p : ℝ) ≤ (N : ℝ)), f p) *
                  (∏ p ∈ shared, f p)) := by
                  exact mul_le_mul_of_nonneg_left hSwb h2g
            _ = 8000 * ((g.totient : ℕ) : ℝ) * (N : ℝ) *
                  (∏ p ∈ (Nat.primeFactors qq).filter (fun p : ℕ => (p : ℝ) ≤ (N : ℝ)), f p) *
                  (∏ p ∈ shared, f p) := by ring
      -- products ∏f ≥ 0 (each prime ≥ 2)
      have hfpos : ∀ p ∈ Nat.primeFactors qq, 0 ≤ f p := by
        intro p hp
        have hpP : p.Prime := Nat.prime_of_mem_primeFactors hp
        have hp2 : 2 ≤ (p : ℝ) := by exact_mod_cast hpP.two_le
        dsimp [f]
        have hp0 : 0 < (p : ℝ) := by positivity
        have hle : (1 : ℝ) / (p : ℝ) ≤ 1 := by
          have : (1 : ℝ) / (p : ℝ) ≤ 1 / 2 := by
            exact (div_le_div_iff₀ hp0 (by norm_num)).mpr (by linarith)
          linarith
        linarith
      have hfposS : ∀ p ∈ shared, 0 ≤ f p := by
        intro p hp
        have hpP : p.Prime := hshared1 p hp
        have hp2 : 2 ≤ (p : ℝ) := by exact_mod_cast hpP.two_le
        dsimp [f]
        have hp0 : 0 < (p : ℝ) := by positivity
        have hle : (1 : ℝ) / (p : ℝ) ≤ 1 := by
          have : (1 : ℝ) / (p : ℝ) ≤ 1 / 2 := by
            exact (div_le_div_iff₀ hp0 (by norm_num)).mpr (by linarith)
          linarith
        linarith
      let P1 : ℝ := ∏ p ∈ (Nat.primeFactors qq).filter (fun p : ℕ => (p : ℝ) ≤ (N : ℝ)), f p
      let P2 : ℝ := ∏ p ∈ (Nat.primeFactors qq).filter (fun p : ℕ => (p : ℝ) ≤ Y), f p
      let Ps : ℝ := ∏ p ∈ shared, f p
      have hc1b : ((((Finset.product ((Finset.range q).filter (fun a : ℕ => a.gcd q = 1))
            ((Finset.range r).filter (fun b : ℕ => b.gcd r = 1))).filter
          (fun ab : ℕ × ℕ =>
            ‖(((ab.1 : ℝ) / (q : ℝ) : ℝ) : UnitAddCircle) -
               (((ab.2 : ℝ) / (r : ℝ) : ℝ) : UnitAddCircle)‖ < Δ)).card : ℝ)) ≤
          8000 * ((g.totient : ℕ) : ℝ) * (N : ℝ) * P1 * Ps := by
          simpa [P1, Ps] using hc1
      have hbr := prod_window_bridge N Y qq hNltY hYleN
      have hmbr : (N : ℝ) * P1 ≤ Y * P2 := by
        have hh : (N : ℝ) * (∏ p ∈ (Nat.primeFactors qq).filter (fun p : ℕ => (p : ℝ) ≤ (N : ℝ)), f p) ≤
            Y * (∏ p ∈ (Nat.primeFactors qq).filter (fun p : ℕ => (p : ℝ) ≤ Y), f p) := by
          simpa [f] using hbr
        simpa [P1, P2] using hh
      have hnon3 : 0 ≤ 8000 * ((g.totient : ℕ) : ℝ) * Ps := by
        have ht : 0 ≤ ((g.totient : ℕ) : ℝ) := by exact_mod_cast (Nat.zero_le (g.totient))
        have hs : 0 ≤ Ps := by
          dsimp [Ps]
          exact Finset.prod_nonneg hfposS
        exact mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 8000) ht) hs
      have hb1 : (8000 * ((g.totient : ℕ) : ℝ) * (N : ℝ) * P1 * Ps) ≤ (8000 * ((g.totient : ℕ) : ℝ) * Ps) * (Y * P2) := by
        calc
          (8000 * ((g.totient : ℕ) : ℝ) * (N : ℝ) * P1 * Ps) = (8000 * ((g.totient : ℕ) : ℝ) * Ps) * ((N : ℝ) * P1) := by ring
          _ ≤ (8000 * ((g.totient : ℕ) : ℝ) * Ps) * (Y * P2) := by
            exact mul_le_mul_of_nonneg_left hmbr hnon3
      have hc2 : ((((Finset.product ((Finset.range q).filter (fun a : ℕ => a.gcd q = 1))
            ((Finset.range r).filter (fun b : ℕ => b.gcd r = 1))).filter
          (fun ab : ℕ × ℕ =>
            ‖(((ab.1 : ℝ) / (q : ℝ) : ℝ) : UnitAddCircle) -
               (((ab.2 : ℝ) / (r : ℝ) : ℝ) : UnitAddCircle)‖ < Δ)).card : ℝ)) ≤
          8000 * Y * ((g.totient : ℕ) : ℝ) * P2 * Ps := by
          exact le_trans hc1b (by
            calc
              (8000 * ((g.totient : ℕ) : ℝ) * (N : ℝ) * P1 * Ps) ≤ (8000 * ((g.totient : ℕ) : ℝ) * Ps) * (Y * P2) := hb1
              _ = 8000 * Y * ((g.totient : ℕ) : ℝ) * P2 * Ps := by ring)
      -- numeric identity: (q/g)(r/g) = q·r/(g·g)
      have hqr2 : q * r / (g * g) = (q / g) * (r / g) := by
        dsimp [g]
        exact (Nat.div_mul_div_comm (Nat.gcd_dvd_left q r) (Nat.gcd_dvd_right q r)).symm
      -- numeric identity: (q/g)(r/g) = q·r/(g·g)
      have hqr2 : q * r / (g * g) = (q / g) * (r / g) := by
        dsimp [g]
        exact (Nat.div_mul_div_comm (Nat.gcd_dvd_left q r) (Nat.gcd_dvd_right q r)).symm
      -- index-set equalities
      have hset1 : (Nat.primeFactors qq).filter (fun p : ℕ => (p : ℝ) ≤ Y) =
          (Nat.primeFactors (q * r / (g * g))).filter (fun p : ℕ => (p : ℝ) ≤ Y) := by
        dsimp [qq]
        rw [hqr2]
      have hset2 : shared = g.primeFactors.filter (fun p : ℕ => ¬ p ∣ q * r / (g * g)) := by
        dsimp [shared, qq]
        rw [hqr2]
      have hprod_eq : P2 * Ps =
          (∏ p ∈ (Nat.primeFactors (q * r / (g * g))).filter (fun p : ℕ => (p : ℝ) ≤ Y), f p) *
            (∏ p ∈ g.primeFactors.filter (fun p : ℕ => ¬ p ∣ q * r / (g * g)), f p) := by
        dsimp [P2, Ps]
        rw [hset1, hset2]
      have hc2b : ((((Finset.product ((Finset.range q).filter (fun a : ℕ => a.gcd q = 1))
            ((Finset.range r).filter (fun b : ℕ => b.gcd r = 1))).filter
          (fun ab : ℕ × ℕ =>
            ‖(((ab.1 : ℝ) / (q : ℝ) : ℝ) : UnitAddCircle) -
               (((ab.2 : ℝ) / (r : ℝ) : ℝ) : UnitAddCircle)‖ < Δ)).card : ℝ)) ≤
          8000 * Y * ((g.totient : ℕ) : ℝ) *
            (∏ p ∈ (Nat.primeFactors (q * r / (g * g))).filter (fun p : ℕ => (p : ℝ) ≤ Y), f p) *
            (∏ p ∈ g.primeFactors.filter (fun p : ℕ => ¬ p ∣ q * r / (g * g)), f p) := by
          have hc2r : ((((Finset.product ((Finset.range q).filter (fun a : ℕ => a.gcd q = 1))
            ((Finset.range r).filter (fun b : ℕ => b.gcd r = 1))).filter
          (fun ab : ℕ × ℕ =>
            ‖(((ab.1 : ℝ) / (q : ℝ) : ℝ) : UnitAddCircle) -
               (((ab.2 : ℝ) / (r : ℝ) : ℝ) : UnitAddCircle)‖ < Δ)).card : ℝ)) ≤
            8000 * Y * ((g.totient : ℕ) : ℝ) * (P2 * Ps) := by
            simpa [mul_assoc] using hc2
          convert hc2r using 1
          rw [hprod_eq]
          ring
      -- (A): target RHS equals the same product expression
      have hA := rpw_target_eq_smallProd q r hq hr Δ hΔ
      have hAt : 8000 * Δ * (q.totient : ℝ) * (r.totient : ℝ) *
          (∏ p ∈ (Nat.primeFactors (q * r / (g * g))).filter (fun p : ℕ => Δ * ((q * r / g : ℕ) : ℝ) < (p : ℝ)),
            (1 - 1 / (p : ℝ))⁻¹) =
          8000 * Y * ((g.totient : ℕ) : ℝ) *
            (∏ p ∈ (Nat.primeFactors (q * r / (g * g))).filter (fun p : ℕ => (p : ℝ) ≤ Y), f p) *
            (∏ p ∈ g.primeFactors.filter (fun p : ℕ => ¬ p ∣ q * r / (g * g)), f p) := by
          simpa [Y, L, g, f] using hA
      exact le_trans hc2b (le_of_eq hAt.symm)




end Commons.NumberTheory.DuffinSchaeffer
