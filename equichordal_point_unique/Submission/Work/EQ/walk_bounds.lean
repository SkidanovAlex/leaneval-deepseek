import Mathlib
import Submission.Work.EQ.DefsCore
import Submission.Work.EQ.charValDefs
import Submission.Work.EQ.fan_base
import Submission.Work.EQ.charVal_aux

namespace Work.EQ

/-! # Auxiliary lemmas for `Work.EQ.walk_bounds`

Elementary lemmas about the fan walk of `charValDefs.lean`: the centres `stCtr` of the states,
the distances `stQ`, the step weights `upW`/`dnW`, the potential `Phi`, and the potential
invariant for `wtAux`/`stAux` (`wtAux a l n * Phi a n ≤ Phi a (stAux l n)`).
-/

/-! ## The centres of the states -/

lemma wb_stCtr_two_mul (k : ℕ) : stCtr (2 * k) = -1 / 2 - 2 * k := by
  rw [stCtr, stIdx_even]
  push_cast
  ring

lemma wb_stCtr_two_mul_add_one (k : ℕ) : stCtr (2 * k + 1) = 3 / 2 + 2 * k := by
  rw [stCtr, stIdx_odd]
  push_cast
  ring

lemma wb_stCtr_mem (n : ℕ) : ∃ k : ℤ, stCtr n = -1 / 2 + 2 * (k : ℝ) :=
  ⟨stIdx n, rfl⟩

lemma wb_stCtr_add_ne {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) (n : ℕ) :
    stCtr n + a / 2 ≠ 0 := by
  intro h
  have hk : stCtr n = -1 / 2 + 2 * (stIdx n : ℝ) := rfl
  have hgt : 0 < 4 * (stIdx n : ℝ) := by linarith
  have hlt : 4 * (stIdx n : ℝ) < 1 := by linarith
  have h1 : (0 : ℤ) < 4 * stIdx n := by exact_mod_cast hgt
  have h2 : 4 * stIdx n < 1 := by exact_mod_cast hlt
  omega

/-! ## The distances `stQ` -/

lemma wb_stQ_two_mul {a : ℝ} (ha1 : a < 1) (k : ℕ) :
    stQ a (2 * k) = 2 * k + (1 - a) / 2 := by
  rw [stQ, wb_stCtr_two_mul]
  have hk : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
  have h : -1 / 2 - 2 * k + a / 2 < 0 := by
    linarith
  rw [abs_of_neg h]
  ring

lemma wb_stQ_two_mul_add_one {a : ℝ} (ha0 : 0 < a) (k : ℕ) :
    stQ a (2 * k + 1) = 2 * k + (3 + a) / 2 := by
  rw [stQ, wb_stCtr_two_mul_add_one]
  have hk : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
  have h : 0 < 3 / 2 + 2 * k + a / 2 := by
    linarith
  rw [abs_of_pos h]
  ring

lemma wb_stQ_pos {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) (n : ℕ) : 0 < stQ a n := by
  rcases Nat.even_or_odd n with ⟨k, hk⟩ | ⟨k, hk⟩
  · have hk2 : k + k = 2 * k := by omega
    rw [hk, hk2, wb_stQ_two_mul ha1 k]
    have hk' : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
    linarith
  · rw [hk, wb_stQ_two_mul_add_one ha0 k]
    have hk' : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
    linarith

lemma wb_stQ_gt_one {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {n : ℕ} (hn : 1 ≤ n) :
    1 < stQ a n := by
  rcases Nat.even_or_odd n with ⟨k, hk⟩ | ⟨k, hk⟩
  · have hk2 : k + k = 2 * k := by omega
    have hk1 : 1 ≤ k := by omega
    rw [hk, hk2, wb_stQ_two_mul ha1 k]
    have h2 : (2 : ℝ) ≤ 2 * (k : ℝ) := by
      have h3 : (2 : ℕ) ≤ 2 * k := by omega
      exact_mod_cast h3
    linarith
  · rw [hk, wb_stQ_two_mul_add_one ha0 k]
    have hk' : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
    linarith

/-! ## Positivity of the weights and of the potential -/

lemma wb_upW_pos {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) (n : ℕ) : 0 < upW a n := by
  have hlam : 0 < eqLam a := eqLam_pos' ha0 ha1
  have hq : 0 < stQ a n := wb_stQ_pos ha0 ha1 n
  rw [upW]
  positivity

lemma wb_dnW_pos {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {n : ℕ} (hn : 1 ≤ n) :
    0 < dnW a n := by
  have hlam : 0 < eqLam a := eqLam_pos' ha0 ha1
  have hq : 1 < stQ a n := wb_stQ_gt_one ha0 ha1 hn
  have hq0 : 0 < stQ a n := lt_trans zero_lt_one hq
  have h1 : 0 < 1 - 1 / stQ a n := by
    rw [sub_pos, div_lt_one hq0]
    exact hq
  rw [dnW]
  exact mul_pos hlam h1

lemma wb_abs_dnW_pos {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) (n : ℕ) : 0 < |dnW a n| := by
  rw [abs_pos]
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    rw [dnW_zero ha0 ha1]
    norm_num
  · exact ne_of_gt (wb_dnW_pos ha0 ha1 hn)

lemma wb_Phi_zero (a : ℝ) : Phi a 0 = 1 := by
  simp [Phi]

lemma wb_Phi_succ (a : ℝ) (n : ℕ) : Phi a (n + 1) = Phi a n * upW a n := by
  simp [Phi, Finset.prod_range_succ]

lemma wb_Phi_pos {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) (n : ℕ) : 0 < Phi a n := by
  unfold Phi
  exact Finset.prod_pos (fun j _ => wb_upW_pos ha0 ha1 j)

lemma wb_wtAux_pos {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) :
    ∀ (l : List Bool) (n : ℕ), 0 < wtAux a l n := by
  intro l
  induction l with
  | nil => intro n; simp
  | cons c l ih =>
    intro n
    rw [wtAux_cons]
    refine mul_pos ?_ (ih (stp c n))
    cases c with
    | true => simpa [stW] using wb_abs_dnW_pos ha0 ha1 n
    | false => simpa [stW] using wb_upW_pos ha0 ha1 n

/-! ## The extreme property `upW a n * dnW a (n+1) < 1` -/

lemma wb_key_even {b A : ℝ} (hb0 : 0 < b) (hb1 : b < 1 / 2) (hA : 0 ≤ A) :
    (b / (1 - b)) * (1 + 1 / (A + b)) * ((b / (1 - b)) * (1 - 1 / (A + 2 - b))) < 1 := by
  have h1 : 0 < 1 - b := by linarith
  have h2 : 0 < A + b := by linarith
  have h3 : 0 < A + 2 - b := by linarith
  have hnum : 0 < (1 - 2 * b) * ((A + 1) ^ 2 - b ^ 2 - (1 - b) ^ 2) := by
    have h4 : 1 ≤ (A + 1) ^ 2 := by nlinarith
    have h5 : b ^ 2 + (1 - b) ^ 2 < 1 := by nlinarith
    have h6 : 0 < 1 - 2 * b := by linarith
    nlinarith
  have hiden : 1 - (b / (1 - b)) * (1 + 1 / (A + b)) * ((b / (1 - b)) * (1 - 1 / (A + 2 - b)))
      = ((1 - 2 * b) * ((A + 1) ^ 2 - b ^ 2 - (1 - b) ^ 2))
        / ((1 - b) ^ 2 * (A + b) * (A + 2 - b)) := by
    field_simp
    ring_nf
  have hden : 0 < (1 - b) ^ 2 * (A + b) * (A + 2 - b) := by positivity
  have hpos := div_pos hnum hden
  linarith [hiden]

lemma wb_key_odd {b u : ℝ} (hb0 : 0 < b) (hb1 : b < 1 / 2) (hu : 2 ≤ u) :
    (b / (1 - b)) * (1 + 1 / (u - b)) * ((b / (1 - b)) * (1 - 1 / (u + b))) < 1 := by
  have h1 : 0 < 1 - b := by linarith
  have h2 : 0 < u - b := by linarith
  have h3 : 0 < u + b := by linarith
  have hnum : 0 < u ^ 2 * ((1 - b) ^ 2 - b ^ 2) := by
    have h4 : b ^ 2 < (1 - b) ^ 2 := by nlinarith
    have h5 : 0 < u ^ 2 := by nlinarith
    nlinarith
  have hiden : 1 - (b / (1 - b)) * (1 + 1 / (u - b)) * ((b / (1 - b)) * (1 - 1 / (u + b)))
      = u ^ 2 * ((1 - b) ^ 2 - b ^ 2) / ((1 - b) ^ 2 * (u - b) * (u + b)) := by
    field_simp
    ring
  have hden : 0 < (1 - b) ^ 2 * (u - b) * (u + b) := by positivity
  have hpos := div_pos hnum hden
  linarith [hiden]

lemma wb_upW_dnW_lt_one {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) (n : ℕ) :
    upW a n * dnW a (n + 1) < 1 := by
  set b : ℝ := (1 - a) / 2 with hb
  have hb0 : 0 < b := by rw [hb]; linarith
  have hb1 : b < 1 / 2 := by rw [hb]; linarith
  have hlam : eqLam a = b / (1 - b) := by
    have h1b : (1 : ℝ) - b = (1 + a) / 2 := by rw [hb]; ring
    rw [eqLam, hb, h1b]
    have h1a : (1 : ℝ) + a ≠ 0 := by linarith
    field_simp
  rcases Nat.even_or_odd n with ⟨k, hk⟩ | ⟨k, hk⟩
  · have hk2 : k + k = 2 * k := by omega
    rw [hk, hk2]
    have hq1 : stQ a (2 * k) = 2 * (k : ℝ) + b := by
      rw [wb_stQ_two_mul ha1 k, hb]
    have hq2 : stQ a (2 * k + 1) = 2 * (k : ℝ) + 2 - b := by
      rw [wb_stQ_two_mul_add_one ha0 k, hb]; ring
    rw [upW, dnW, hq1, hq2, hlam]
    refine wb_key_even hb0 hb1 ?_
    have hk' : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
    linarith
  · rw [hk]
    have hq1 : stQ a (2 * k + 1) = 2 * (k : ℝ) + 2 - b := by
      rw [wb_stQ_two_mul_add_one ha0 k, hb]; ring
    have hq2 : stQ a (2 * (k + 1)) = 2 * (k : ℝ) + 2 + b := by
      rw [wb_stQ_two_mul ha1 (k + 1), hb]
      push_cast
      ring
    rw [show (2 * k + 1) + 1 = 2 * (k + 1) from by omega]
    rw [upW, dnW, hq1, hq2, hlam]
    refine wb_key_odd hb0 hb1 ?_
    have hk' : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
    linarith

/-! ## The reflection formula for the centres -/

lemma wb_quot_neg {a : ℝ} {n : ℕ} (h : stCtr n + a / 2 < 0) :
    (stCtr n + a / 2) / |stCtr n + a / 2| = -1 := by
  rw [abs_of_neg h, div_neg, div_self (ne_of_lt h)]

lemma wb_quot_pos {a : ℝ} {n : ℕ} (h : 0 < stCtr n + a / 2) :
    (stCtr n + a / 2) / |stCtr n + a / 2| = 1 := by
  rw [abs_of_pos h, div_self (ne_of_gt h)]

lemma wb_stCtr_two_mul_add_neg {a : ℝ} (ha1 : a < 1) (k : ℕ) :
    stCtr (2 * k) + a / 2 < 0 := by
  rw [wb_stCtr_two_mul]
  have hk : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
  linarith

lemma wb_stCtr_two_mul_add_one_add_pos {a : ℝ} (ha0 : 0 < a) (k : ℕ) :
    0 < stCtr (2 * k + 1) + a / 2 := by
  rw [wb_stCtr_two_mul_add_one]
  have hk : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
  linarith

lemma wb_stCtr_zero_add_neg {a : ℝ} (ha1 : a < 1) : stCtr 0 + a / 2 < 0 := by
  rw [stCtr_zero]
  linarith

lemma wb_stCtr_stp_false {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) (n : ℕ) :
    stCtr (stp false n) = -stCtr n - (stCtr n + a / 2) / |stCtr n + a / 2| := by
  rcases Nat.even_or_odd n with ⟨k, hk⟩ | ⟨k, hk⟩
  · have hk2 : k + k = 2 * k := by omega
    rw [hk, hk2, stp_false, wb_quot_neg (wb_stCtr_two_mul_add_neg ha1 k),
      wb_stCtr_two_mul_add_one k, wb_stCtr_two_mul k]
    ring
  · rw [hk, stp_false, show 2 * k + 1 + 1 = 2 * (k + 1) from by omega,
      wb_quot_pos (wb_stCtr_two_mul_add_one_add_pos ha0 k),
      wb_stCtr_two_mul (k + 1), wb_stCtr_two_mul_add_one k]
    push_cast
    ring

lemma wb_stCtr_stp_true {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) (n : ℕ) :
    stCtr (stp true n) = -stCtr n + (stCtr n + a / 2) / |stCtr n + a / 2| := by
  rcases Nat.even_or_odd n with ⟨k, hk⟩ | ⟨k, hk⟩
  · have hk2 : k + k = 2 * k := by omega
    rw [hk, hk2]
    cases k with
    | zero =>
      rw [show (2 : ℕ) * 0 = 0 from rfl, show stp true 0 = 0 from rfl,
        wb_quot_neg (wb_stCtr_zero_add_neg ha1), stCtr_zero]
      norm_num
    | succ j =>
      rw [show stp true (2 * (j + 1)) = 2 * j + 1 from by
            rw [show 2 * (j + 1) = (2 * j + 1) + 1 from by omega, stp_true_succ],
          wb_quot_neg (wb_stCtr_two_mul_add_neg ha1 (j + 1)),
          wb_stCtr_two_mul_add_one j, wb_stCtr_two_mul (j + 1)]
      push_cast
      ring
  · rw [hk, show stp true (2 * k + 1) = 2 * k from stp_true_succ (2 * k),
      wb_quot_pos (wb_stCtr_two_mul_add_one_add_pos ha0 k),
      wb_stCtr_two_mul k, wb_stCtr_two_mul_add_one k]
    ring

lemma wb_stCtr_stp {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) (n : ℕ) (c : Bool) :
    stCtr (stp c n) =
      -stCtr n + (if c then 1 else -1) * (stCtr n + a / 2) / |stCtr n + a / 2| := by
  cases c with
  | false =>
    rw [wb_stCtr_stp_false ha0 ha1 n]
    simp only [Bool.false_eq_true, ↓reduceIte]
    ring
  | true =>
    rw [wb_stCtr_stp_true ha0 ha1 n]
    simp only [↓reduceIte]
    ring

/-! ## The potential invariant -/

lemma wb_step_le {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1)
    (hC : ∀ n : ℕ, upW a n * dnW a (n + 1) ≤ 1) (m : ℕ) :
    |dnW a (m + 1)| * (Phi a m * upW a m) ≤ Phi a m := by
  have hdn : 0 < dnW a (m + 1) := wb_dnW_pos ha0 ha1 (by omega)
  have hPhi : 0 < Phi a m := wb_Phi_pos ha0 ha1 m
  have h1 : upW a m * dnW a (m + 1) ≤ 1 := hC m
  have h2 : Phi a m * (upW a m * dnW a (m + 1)) ≤ Phi a m * 1 :=
    mul_le_mul_of_nonneg_left h1 (le_of_lt hPhi)
  rw [abs_of_pos hdn]
  linarith [h2]

lemma wb_step_lt {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1)
    (hC : ∀ n : ℕ, upW a n * dnW a (n + 1) < 1) (m : ℕ) :
    |dnW a (m + 1)| * (Phi a m * upW a m) < Phi a m := by
  have hdn : 0 < dnW a (m + 1) := wb_dnW_pos ha0 ha1 (by omega)
  have hPhi : 0 < Phi a m := wb_Phi_pos ha0 ha1 m
  have h1 : upW a m * dnW a (m + 1) < 1 := hC m
  have h2 : Phi a m * (upW a m * dnW a (m + 1)) < Phi a m * 1 :=
    mul_lt_mul_of_pos_left h1 hPhi
  rw [abs_of_pos hdn]
  linarith [h2]

lemma wb_wtPhi_le {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1)
    (hC : ∀ n : ℕ, upW a n * dnW a (n + 1) ≤ 1) :
    ∀ (l : List Bool) (n : ℕ), wtAux a l n * Phi a n ≤ Phi a (stAux l n) := by
  intro l
  induction l with
  | nil => intro n; simp
  | cons c l ih =>
    intro n
    cases c with
    | false =>
      have hih := ih (n + 1)
      rw [wb_Phi_succ] at hih
      simp only [wtAux_cons, stAux_cons, stW, Bool.false_eq_true, if_false, stp_false]
      linarith
    | true =>
      cases n with
      | zero =>
        have hih := ih 0
        simpa [wtAux_cons, stAux_cons, stW, stp_true_zero, dnW_zero ha0 ha1] using hih
      | succ m =>
        have hih := ih m
        have hstep := wb_step_le ha0 ha1 hC m
        have hwt : 0 < wtAux a l m := wb_wtAux_pos ha0 ha1 l m
        have h1 := mul_le_mul_of_nonneg_left hstep (le_of_lt hwt)
        simp only [wtAux_cons, stAux_cons, stW, if_true, stp_true_succ, wb_Phi_succ]
        linarith

/-! ## Words all of whose steps are non-stationary or down steps -/

/-- `wb_hasStrict l n` holds when the word `l`, read from state `n`, contains a `true` letter
(a principal step) read in a state `≥ 1`, i.e. a step for which the potential inequality is
strict. -/
def wb_hasStrict : List Bool → ℕ → Prop
  | [], _ => False
  | c :: l, n => (c = true ∧ 1 ≤ n) ∨ wb_hasStrict l (stp c n)

lemma wb_step_le_all {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1)
    (hC : ∀ n : ℕ, upW a n * dnW a (n + 1) ≤ 1) :
    ∀ (l : List Bool) (n : ℕ), wtAux a l n * Phi a n ≤ Phi a (stAux l n) :=
  wb_wtPhi_le ha0 ha1 hC

lemma wb_hasStrict_lt {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1)
    (hC : ∀ n : ℕ, upW a n * dnW a (n + 1) < 1) :
    ∀ (l : List Bool) (n : ℕ), wb_hasStrict l n →
      wtAux a l n * Phi a n < Phi a (stAux l n) := by
  intro l
  induction l with
  | nil => intro n h; exact absurd h (by simp [wb_hasStrict])
  | cons c l ih =>
    intro n h
    cases c with
    | false =>
      have h' : wb_hasStrict l (n + 1) := by
        rcases h with ⟨h1, _⟩ | h2
        · exact absurd h1 (by simp)
        · exact h2
      have hih := ih (n + 1) h'
      rw [wb_Phi_succ] at hih
      simp only [wtAux_cons, stAux_cons, stW, Bool.false_eq_true, if_false, stp_false]
      linarith
    | true =>
      cases n with
      | zero =>
        have h' : wb_hasStrict l 0 := by
          rcases h with ⟨_, h2⟩ | h2
          · exact absurd h2 (by omega)
          · simpa [stp_true_zero] using h2
        have hih := ih 0 h'
        simpa [wtAux_cons, stAux_cons, stW, stp_true_zero, dnW_zero ha0 ha1] using hih
      | succ m =>
        have hstep := wb_step_lt ha0 ha1 hC m
        have hwt : 0 < wtAux a l m := wb_wtAux_pos ha0 ha1 l m
        have h1 := mul_lt_mul_of_pos_left hstep hwt
        have h2 := wb_wtPhi_le ha0 ha1 (fun n => le_of_lt (hC n)) l m
        simp only [wtAux_cons, stAux_cons, stW, if_true, stp_true_succ, wb_Phi_succ]
        linarith

/-! ## Closed walks: a non-principal letter forces a strict step -/

lemma wb_eq_true_of_count_eq_zero {l : List Bool} (h : l.count false = 0) :
    ∀ c ∈ l, c = true := by
  intro c hc
  have hmem : false ∉ l := List.count_eq_zero.mp h
  cases c with
  | false => exact absurd hc hmem
  | true => rfl

lemma wb_hasStrict_of_le {l : List Bool} {n : ℕ} (hf : l.count false ≠ 0)
    (h : stAux l n ≤ n) : wb_hasStrict l n := by
  induction l generalizing n with
  | nil => simp at hf
  | cons c l ih =>
    cases c with
    | true =>
      cases n with
      | zero =>
        have hf' : l.count false ≠ 0 := by
          rw [count_false_true_cons] at hf; exact hf
        have h' : stAux l 0 ≤ 0 := by simpa [stAux_cons, stp_true_zero] using h
        exact Or.inr (ih hf' h')
      | succ m => exact Or.inl ⟨rfl, by omega⟩
    | false =>
      have h' : stAux l (n + 1) ≤ n := by simpa [stAux_cons, stp_false] using h
      by_cases hf' : l.count false = 0
      · have hall : ∀ c ∈ l, c = true := wb_eq_true_of_count_eq_zero hf'
        cases l with
        | nil =>
          have h'' : n + 1 ≤ n := h'
          exact absurd h'' (by omega)
        | cons c l =>
          have hc : c = true := hall c (by simp)
          subst hc
          exact Or.inr (Or.inl ⟨rfl, by rw [stp_false]; omega⟩)
      · exact Or.inr (ih hf' (by rw [stp_false]; omega))

lemma wb_closed_le_one {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) (l : List Bool)
    (hcl : stAux l 0 = 0) : wtAux a l 0 ≤ 1 := by
  have h := wb_wtPhi_le ha0 ha1 (fun n => le_of_lt (wb_upW_dnW_lt_one ha0 ha1 n)) l 0
  rw [hcl, wb_Phi_zero] at h
  simpa using h

lemma wb_closed_eq_one_all_true {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) (l : List Bool)
    (hcl : stAux l 0 = 0) (hwt : wtAux a l 0 = 1) : ∀ c ∈ l, c = true := by
  intro c hc
  by_contra hne
  have hcf : c = false := by cases c with | false => rfl | true => exact absurd rfl hne
  have hmem : false ∈ l := by rwa [hcf] at hc
  have hcount : l.count false ≠ 0 := fun h => (List.count_eq_zero.mp h) hmem
  have hs : wb_hasStrict l 0 := wb_hasStrict_of_le hcount (by rw [hcl])
  have hlt := wb_hasStrict_lt ha0 ha1 (wb_upW_dnW_lt_one ha0 ha1) l 0 hs
  rw [hcl, wb_Phi_zero, hwt, one_mul] at hlt
  linarith

/-! ## The signed step weights -/

lemma wb_sgnAux_eq {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) :
    ∀ (l : List Bool) (n : ℕ), sgnAux a l n = (-1 : ℝ) ^ nsAux l n * wtAux a l n := by
  intro l
  induction l with
  | nil => intro n; simp
  | cons c l ih =>
    intro n
    have hstep : sgW a c n = (-1 : ℝ) ^ (if c ∧ n = 0 then 0 else 1) * stW a c n := by
      cases c with
      | false => simp [sgW, stW]
      | true =>
        cases n with
        | zero => simp [sgW, stW, dnW_zero ha0 ha1]
        | succ m =>
          have h : 0 < dnW a (m + 1) := wb_dnW_pos ha0 ha1 (by omega)
          simp [sgW, stW, abs_of_pos h]
    rw [sgnAux_cons, wtAux_cons, nsAux_cons, ih (stp c n), hstep, pow_add]
    ring

lemma wb_nsAux_stAux_even (l : List Bool) (n : ℕ) :
    Even (nsAux l n + stAux l n + n) := by
  induction l generalizing n with
  | nil =>
    simp only [nsAux_nil, stAux_nil]
    exact ⟨n, by ring⟩
  | cons c l ih =>
    cases c with
    | false =>
      obtain ⟨t, ht⟩ := ih (n + 1)
      simp only [nsAux_cons, stAux_cons, stp_false, Bool.false_eq_true, false_and,
        ↓reduceIte, Nat.add_zero]
      exact ⟨t, by omega⟩
    | true =>
      cases n with
      | zero =>
        obtain ⟨t, ht⟩ := ih 0
        simp only [nsAux_cons, stAux_cons, stp_true_zero, and_self, ↓reduceIte,
          Nat.zero_add]
        exact ⟨t, by omega⟩
      | succ m =>
        obtain ⟨t, ht⟩ := ih m
        simp only [nsAux_cons, stAux_cons, stp_true_succ, Nat.succ_ne_zero, and_false,
          ↓reduceIte, Nat.add_zero]
        exact ⟨t + 1, by omega⟩

/-- **The weight combinatorics of the fan walk (Rychlik Lemma 13, Lemma 14).**

`charValDefs.lean` encodes the walk of fan centres on the axis `-1/2 + 2ℤ` as a nearest
neighbour walk on `ℕ`: state `n` carries the centre `stCtr n` (`stCtr 0 = -1/2`, `stCtr 1 = 3/2`,
`stCtr 2 = -5/2`, `stCtr 3 = 7/2`, ...), reading the letter `c = true` (principal step `T`) or
`c = false` (non-principal step `F`) moves to `stp c n`, and the step weight has modulus
`stW a c n` (`upW a n` for `F`, `|dnW a n|` for `T`) and signed value `sgW a c n`
(`-upW a n` resp. `-dnW a n`; the stationary step at `A₁` has signed weight `+1`).

With `q = stQ a n`, `λ = eqLam a ∈ (0,1)`, `upW a n = λ(1 + 1/q)` and `dnW a n = λ(1 - 1/q)`
(note `Work.EQ.dnW_zero`: `dnW a 0 = -1`, and `dnW a n > 0` for every `n ≥ 1`, since
`q = (1-a)/2 < 1` only at `n = 0`), and `Phi a n = ∏_{j<n} upW a j`, the content is:
1. `stCtr (stp c n) = -stCtr n + (±1)(stCtr n + a/2)/|stCtr n + a/2|`, every `stCtr n` lies in
`-1/2 + 2ℤ`, and `stCtr n ≠ -a/2`;
2. positivity of the weights and of the potential;
3. Rychlik's extreme property `upW a n * dnW a (n+1) < 1` (strict contraction);
4. the potential invariant `wtAux a l n * Phi a n ≤ Phi a (stAux l n)`; hence a closed walk
(`stAux l 0 = 0`) has `wtAux a l 0 ≤ 1`, with equality **only** when every letter is `true`
(the principal leaf);
5. `sgnAux a l n = (-1) ^ nsAux l n * wtAux a l n` (note: `nsAux` takes no `a`) and
`nsAux l 0 + stAux l 0` is even, so for a closed walk the signed product equals `wtAux a l 0`.

Sketch of 1: `stIdx (2k) = -k` and `stIdx (2k+1) = k+1` (both in
`Submission.Work.EQ.charVal_aux`), so `stCtr (2k) = -1/2 - 2k` and `stCtr (2k+1) = -1/2 + 2k + 2`;
a case check against `stp` gives the reflection formula.
Sketch of 3: with `β = (1-a)/2 ∈ (0,1/2)` and `λ = β/(1-β)`, for `n = 2k` the pair is
`(q, q') = (2k+β, 2k+2-β)` and `upW·dnW < 1` becomes `(A+1)² > β² + (1-β)²` with `A = 2k`, for
`n = 2k+1` it is `(2k+2-β, 2k+2+β)` and becomes `β² < (1-β)²`; both hold.
Sketch of 4: induct on the word; the `false` step and the stationary step are equalities and the
`true` step at `n ≥ 1` is strict by 3; a closed walk with a `false` letter must contain a
non-stationary `true` letter, which is strict. -/
theorem walk_bounds {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) :
    (∀ (n : ℕ) (c : Bool),
        stCtr (stp c n) = -stCtr n + (if c then 1 else -1) * (stCtr n + a / 2) / |stCtr n + a / 2|) ∧
    (∀ n : ℕ, ∃ k : ℤ, stCtr n = -1 / 2 + 2 * (k : ℝ)) ∧
    (∀ n : ℕ, stCtr n + a / 2 ≠ 0) ∧
    (∀ n : ℕ, 0 < upW a n) ∧
    dnW a 0 = -1 ∧
    (∀ n : ℕ, 1 ≤ n → 0 < dnW a n) ∧
    (∀ n : ℕ, upW a n * dnW a (n + 1) < 1) ∧
    (∀ n : ℕ, 0 < Phi a n) ∧
    Phi a 0 = 1 ∧
    (∀ (l : List Bool) (n : ℕ), 0 < wtAux a l n) ∧
    (∀ (l : List Bool) (n : ℕ), wtAux a l n * Phi a n ≤ Phi a (stAux l n)) ∧
    (∀ l : List Bool, stAux l 0 = 0 → wtAux a l 0 ≤ 1) ∧
    (∀ l : List Bool, stAux l 0 = 0 → wtAux a l 0 = 1 → ∀ c ∈ l, c = true) ∧
    (∀ (l : List Bool) (n : ℕ), sgnAux a l n = (-1 : ℝ) ^ nsAux l n * wtAux a l n) ∧
    (∀ l : List Bool, Even (nsAux l 0 + stAux l 0)) := by
  have hC : ∀ n : ℕ, upW a n * dnW a (n + 1) < 1 := wb_upW_dnW_lt_one ha0 ha1
  refine ⟨fun n c => wb_stCtr_stp ha0 ha1 n c, wb_stCtr_mem, wb_stCtr_add_ne ha0 ha1,
    wb_upW_pos ha0 ha1, dnW_zero ha0 ha1, fun n hn => wb_dnW_pos ha0 ha1 hn, hC,
    wb_Phi_pos ha0 ha1, wb_Phi_zero a, wb_wtAux_pos ha0 ha1,
    fun l n => wb_wtPhi_le ha0 ha1 (fun n => le_of_lt (hC n)) l n,
    fun l hcl => wb_closed_le_one ha0 ha1 l hcl,
    fun l hcl hwt => wb_closed_eq_one_all_true ha0 ha1 l hcl hwt,
    fun l n => wb_sgnAux_eq ha0 ha1 l n, fun l => by simpa using wb_nsAux_stAux_even l 0⟩

end Work.EQ
