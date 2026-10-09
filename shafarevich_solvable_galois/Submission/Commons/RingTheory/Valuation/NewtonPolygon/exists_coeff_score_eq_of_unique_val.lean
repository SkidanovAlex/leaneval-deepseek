import Mathlib.Algebra.Polynomial.Splits
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.Valuation.Basic
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Newton polygon: a value attained by exactly one root

For a monic polynomial `f` that splits in a valued field `F`, and a nonzero value `γ` attained by
exactly one root of `f`, two consecutive coefficients have equal `γ`-scores
`w (f.coeff i) * γ ^ i`, and both are nonzero.

The mathematical content is the classical Newton polygon statement, proved here for an arbitrary
multiset `s` of roots: for the polynomial `P = ∏_{a ∈ s} (X - C a)` and any `0 ≠ x ∈ Γ₀`, the
`x`-score `i ↦ w (P.coeff i) * x ^ i` is bounded by `M = ∏_{a ∈ s} max (w a) x`, is strictly below
`M` off the interval `[#{a | w a < x}, #{a | w a ≤ x}]`, and equals `M` at the two endpoints
(`newtonPolygonScore_score_good` below). The proof is an induction on the multiset: for
`P' = (X - C a) * P` one has `(P').coeff (j+1) = P.coeff j - a * P.coeff (j+1)`, and the three cases
`w a < x`, `w a = x`, `x < w a` decide which of the two terms of the recurrence strictly dominates,
hence where the maximizers sit.
-/


namespace Commons.RingTheory.Valuation.NewtonPolygon

namespace NewtonPolygonScore

open Polynomial

noncomputable section

variable {F : Type*} [Field F] {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀]

/-- Strict monotonicity of left multiplication by a nonzero element in a
`LinearOrderedCommGroupWithZero`. -/
lemma mul_lt_mul_ne_left {a b c : Γ₀} (h : a < b) (hc : c ≠ 0) : c * a < c * b :=
  (mul_lt_mul_iff_right₀ (zero_lt_iff.mpr hc)).mpr h

/-- Strict monotonicity of right multiplication by a nonzero element in a
`LinearOrderedCommGroupWithZero`. -/
lemma mul_lt_mul_ne_right {a b c : Γ₀} (h : a < b) (hc : c ≠ 0) : a * c < b * c :=
  (mul_lt_mul_iff_left₀ (zero_lt_iff.mpr hc)).mpr h

/-- `w₀ * A` is strictly below `M * max w₀ x` as soon as `A < M` and `M`, `x` are nonzero. -/
lemma mul_lt_mul_max_of_lt {w₀ A M x : Γ₀} (hA : A < M) (hM : M ≠ 0) (hx : x ≠ 0) :
    w₀ * A < M * max w₀ x := by
  by_cases hw : w₀ = 0
  · subst hw
    rw [zero_mul, max_eq_right (zero_le : (0 : Γ₀) ≤ x)]
    exact mul_pos (zero_lt_iff.mpr hM) (zero_lt_iff.mpr hx)
  · calc w₀ * A < w₀ * M := mul_lt_mul_ne_left hA hw
      _ ≤ max w₀ x * M := mul_le_mul_left (le_max_left _ _) _
      _ = M * max w₀ x := mul_comm _ _

/-- `A * x` is strictly below `M * max w₀ x` as soon as `A < M` and `x` is nonzero. -/
lemma mul_x_lt_mul_max_of_lt {w₀ A M x : Γ₀} (hA : A < M) (hx : x ≠ 0) :
    A * x < M * max w₀ x := by
  calc A * x < M * x := mul_lt_mul_ne_right hA hx
    _ ≤ M * max w₀ x := mul_le_mul_right (le_max_right _ _) _

/-- `A * x` is strictly below `M * max w₀ x` as soon as `A ≤ M`, `M ≠ 0` and `x < max w₀ x`. -/
lemma mul_x_lt_mul_max_of_le {w₀ A M x : Γ₀} (hA : A ≤ M) (hM : M ≠ 0)
    (h : x < max w₀ x) : A * x < M * max w₀ x := by
  calc A * x ≤ M * x := mul_le_mul_left hA x
    _ < M * max w₀ x := mul_lt_mul_ne_left h hM

/-- `w₀ * A` is strictly below `M * max w₀ x` as soon as `A ≤ M`, `M ≠ 0` and `w₀ < max w₀ x`. -/
lemma lt_mul_mul_max_of_le {w₀ A M x : Γ₀} (hA : A ≤ M) (hM : M ≠ 0)
    (h : w₀ < max w₀ x) : w₀ * A < M * max w₀ x := by
  calc w₀ * A ≤ w₀ * M := mul_le_mul_right hA w₀
    _ < max w₀ x * M := mul_lt_mul_ne_right h hM
    _ = M * max w₀ x := mul_comm _ _

/-- The monic polynomial `∏_{a ∈ s} (X - C a)` attached to a multiset of roots. -/
def rootsPoly (s : Multiset F) : Polynomial F :=
  (s.map (fun a => Polynomial.X - Polynomial.C a)).prod

/-- The upper bound `∏_{a ∈ s} max (w a) x` for the `x`-scores of the coefficients. -/
def scoreMax (w : Valuation F Γ₀) (s : Multiset F) (x : Γ₀) : Γ₀ :=
  (s.map (fun a => max (w a) x)).prod

/-- The `x`-score of the `i`-th coefficient. -/
def score (w : Valuation F Γ₀) (s : Multiset F) (x : Γ₀) (i : ℕ) : Γ₀ :=
  w ((rootsPoly s).coeff i) * x ^ i

/-- Number of roots of value `< x`. -/
def lowerIdx (w : Valuation F Γ₀) (s : Multiset F) (x : Γ₀) : ℕ :=
  (s.filter (fun a => w a < x)).card

/-- Number of roots of value `≤ x`. -/
def upperIdx (w : Valuation F Γ₀) (s : Multiset F) (x : Γ₀) : ℕ :=
  (s.filter (fun a => w a ≤ x)).card

@[simp] lemma rootsPoly_zero : rootsPoly (0 : Multiset F) = 1 := rfl

lemma rootsPoly_cons (a : F) (s : Multiset F) :
    rootsPoly (a ::ₘ s) = (Polynomial.X - Polynomial.C a) * rootsPoly s := by
  simp [rootsPoly]

lemma scoreMax_cons (w : Valuation F Γ₀) (a : F) (s : Multiset F) (x : Γ₀) :
    scoreMax w (a ::ₘ s) x = max (w a) x * scoreMax w s x := by
  simp [scoreMax]

lemma lowerIdx_cons (w : Valuation F Γ₀) (a : F) (s : Multiset F) (x : Γ₀) :
    lowerIdx w (a ::ₘ s) x = (if w a < x then 1 else 0) + lowerIdx w s x := by
  simp only [lowerIdx, Multiset.filter_cons, Multiset.card_add]
  split_ifs <;> simp

lemma upperIdx_cons (w : Valuation F Γ₀) (a : F) (s : Multiset F) (x : Γ₀) :
    upperIdx w (a ::ₘ s) x = (if w a ≤ x then 1 else 0) + upperIdx w s x := by
  simp only [upperIdx, Multiset.filter_cons, Multiset.card_add]
  split_ifs <;> simp

lemma coeff_cons_succ (a : F) (s : Multiset F) (i : ℕ) :
    (rootsPoly (a ::ₘ s)).coeff (i + 1) = (rootsPoly s).coeff i - a * (rootsPoly s).coeff (i+1) := by
  rw [rootsPoly_cons, sub_mul, coeff_sub, coeff_C_mul, coeff_X_mul]

lemma coeff_cons_zero (a : F) (s : Multiset F) :
    (rootsPoly (a ::ₘ s)).coeff 0 = -a * (rootsPoly s).coeff 0 := by
  rw [rootsPoly_cons]; simp [sub_mul]

lemma score_cons_zero (w : Valuation F Γ₀) (a : F) (s : Multiset F) (x : Γ₀) :
    score w (a ::ₘ s) x 0 = w a * score w s x 0 := by
  simp [score, coeff_cons_zero, Valuation.map_mul]

/-- `scoreMax` is a product of nonzero factors, hence nonzero. -/
lemma scoreMax_ne_zero (w : Valuation F Γ₀) (s : Multiset F) {x : Γ₀} (hx : x ≠ 0) :
    scoreMax w s x ≠ 0 := by
  rw [scoreMax]
  refine Multiset.prod_ne_zero ?_
  simp only [Multiset.mem_map, not_exists, not_and]
  intro a _ hcontra
  have hpos : (0 : Γ₀) < max (w a) x :=
    lt_of_lt_of_le (zero_lt_iff.mpr hx) (le_max_right _ _)
  rw [hcontra] at hpos
  exact lt_irrefl 0 hpos

/-- The score of `score w s x j * x` rewritten with `j + 1`. -/
lemma score_mul_x (w : Valuation F Γ₀) (s : Multiset F) (x : Γ₀) (j : ℕ) :
    score w s x j * x = w ((rootsPoly s).coeff j) * x ^ (j + 1) := by
  rw [score, pow_succ, ← mul_assoc]

/-- The score of `w a * score w s x (j+1)` rewritten with `j + 1`. -/
lemma mul_score_succ (w : Valuation F Γ₀) (a : F) (s : Multiset F) (x : Γ₀) (j : ℕ) :
    (w a * w ((rootsPoly s).coeff (j+1))) * x ^ (j + 1) = w a * score w s x (j + 1) := by
  rw [score, pow_succ, mul_assoc]

/-- If the `a * c_{j+1}` term strictly dominates, then the score of the extended multiset at
`j + 1` is `w a` times the score of `s` at `j + 1`. -/
lemma score_cons_succ_eq_of_dominated_left (w : Valuation F Γ₀) (a : F) (s : Multiset F) {x : Γ₀}
    (hx : x ≠ 0) (j : ℕ) (h : score w s x j * x < w a * score w s x (j + 1)) :
    score w (a ::ₘ s) x (j + 1) = w a * score w s x (j + 1) := by
  have hx' : (0 : Γ₀) < x ^ (j + 1) := pow_pos (zero_lt_iff.mpr hx) _
  have h' : w ((rootsPoly s).coeff j) * x ^ (j+1)
      < (w a * w ((rootsPoly s).coeff (j+1))) * x ^ (j+1) := by
    rw [score_mul_x w s x j, ← mul_score_succ w a s x j] at h
    exact h
  have key : w ((rootsPoly s).coeff j) < w a * w ((rootsPoly s).coeff (j+1)) :=
    (mul_lt_mul_iff_left₀ hx').mp h'
  have hlt : w ((rootsPoly s).coeff j) < w (-(a * (rootsPoly s).coeff (j+1))) := by
    rw [Valuation.map_neg, Valuation.map_mul]; exact key
  have hcoe : w ((rootsPoly s).coeff j - a * (rootsPoly s).coeff (j+1))
      = w (-(a * (rootsPoly s).coeff (j+1))) := by
    rw [sub_eq_add_neg]
    exact w.map_add_eq_of_lt_right hlt
  calc score w (a ::ₘ s) x (j + 1)
      = w ((rootsPoly (a ::ₘ s)).coeff (j+1)) * x ^ (j+1) := rfl
    _ = w (-(a * (rootsPoly s).coeff (j+1))) * x ^ (j+1) := by rw [coeff_cons_succ, hcoe]
    _ = w (a * (rootsPoly s).coeff (j+1)) * x ^ (j+1) := by rw [Valuation.map_neg]
    _ = (w a * w ((rootsPoly s).coeff (j+1))) * x ^ (j+1) := by rw [Valuation.map_mul]
    _ = w a * score w s x (j + 1) := mul_score_succ w a s x j

/-- If the `c_j` term strictly dominates, then the score of the extended multiset at `j + 1` is
`score w s x j * x`. -/
lemma score_cons_succ_eq_of_dominated_right (w : Valuation F Γ₀) (a : F) (s : Multiset F) {x : Γ₀}
    (hx : x ≠ 0) (j : ℕ) (h : w a * score w s x (j + 1) < score w s x j * x) :
    score w (a ::ₘ s) x (j + 1) = score w s x j * x := by
  have hx' : (0 : Γ₀) < x ^ (j + 1) := pow_pos (zero_lt_iff.mpr hx) _
  have h' : (w a * w ((rootsPoly s).coeff (j+1))) * x ^ (j+1)
      < w ((rootsPoly s).coeff j) * x ^ (j+1) := by
    rw [score_mul_x w s x j, ← mul_score_succ w a s x j] at h
    exact h
  have key : w a * w ((rootsPoly s).coeff (j+1)) < w ((rootsPoly s).coeff j) :=
    (mul_lt_mul_iff_left₀ hx').mp h'
  have hlt : w (-(a * (rootsPoly s).coeff (j+1))) < w ((rootsPoly s).coeff j) := by
    rw [Valuation.map_neg, Valuation.map_mul]; exact key
  have hcoe : w ((rootsPoly s).coeff j - a * (rootsPoly s).coeff (j+1))
      = w ((rootsPoly s).coeff j) := by
    rw [sub_eq_add_neg]
    exact w.map_add_eq_of_lt_left hlt
  calc score w (a ::ₘ s) x (j + 1)
      = w ((rootsPoly (a ::ₘ s)).coeff (j+1)) * x ^ (j+1) := rfl
    _ = w ((rootsPoly s).coeff j) * x ^ (j+1) := by rw [coeff_cons_succ, hcoe]
    _ = score w s x j * x := (score_mul_x w s x j).symm

/-- **Newton polygon, coefficient scores.** For a multiset `s` of roots, a nonzero value `x`, the
`x`-scores `i ↦ w (P.coeff i) * x ^ i` of the coefficients of `P = ∏_{a ∈ s} (X - a)` are bounded
by `M = ∏_{a ∈ s} max (w a) x`; they are strictly below `M` for `i < #{a | w a < x}` and for
`#{a | w a ≤ x} < i`, and equal to `M` at those two indices. -/
lemma score_good (w : Valuation F Γ₀) (s : Multiset F) {x : Γ₀} (hx : x ≠ 0) :
    (∀ i, score w s x i ≤ scoreMax w s x) ∧
    (∀ i, i < lowerIdx w s x → score w s x i < scoreMax w s x) ∧
    score w s x (lowerIdx w s x) = scoreMax w s x ∧
    score w s x (upperIdx w s x) = scoreMax w s x ∧
    (∀ i, upperIdx w s x < i → score w s x i < scoreMax w s x) := by
  induction s using Multiset.induction_on with
  | empty =>
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro i; cases i with
      | zero => simp [score, scoreMax, Polynomial.coeff_one]
      | succ i => simp [score, scoreMax, Polynomial.coeff_one]
    · intro i hi; simp [lowerIdx] at hi
    · simp [score, scoreMax, lowerIdx, Polynomial.coeff_one]
    · simp [score, scoreMax, upperIdx, Polynomial.coeff_one]
    · intro i hi; simp [upperIdx] at hi
      cases i with
      | zero => omega
      | succ i => simp [score, scoreMax, Polynomial.coeff_one]
  | cons a s ih =>
    obtain ⟨ih_le, ih_lt_lo, ih_lo, ih_hi, ih_lt_hi⟩ := ih
    have hx0 : (0 : Γ₀) < x := zero_lt_iff.mpr hx
    have hMb : scoreMax w s x ≠ 0 := scoreMax_ne_zero w s hx
    have boundsucc : ∀ j, score w (a ::ₘ s) x (j + 1)
        ≤ max (score w s x j * x) (w a * score w s x (j + 1)) := by
      intro j
      have h1 : w ((rootsPoly (a ::ₘ s)).coeff (j + 1))
          ≤ max (w ((rootsPoly s).coeff j)) (w a * w ((rootsPoly s).coeff (j + 1))) := by
        rw [coeff_cons_succ]
        refine (w.map_sub _ _).trans (max_le_max le_rfl ?_)
        rw [Valuation.map_mul]
      have h2 := mul_le_mul_left h1 (x ^ (j + 1))
      calc score w (a ::ₘ s) x (j + 1)
          = w ((rootsPoly (a ::ₘ s)).coeff (j + 1)) * x ^ (j + 1) := rfl
        _ ≤ max (w ((rootsPoly s).coeff j)) (w a * w ((rootsPoly s).coeff (j + 1))) * x ^ (j + 1) := h2
        _ = max (score w s x j * x) (w a * score w s x (j + 1)) := by
            rw [max_mul, ← score_mul_x w s x j, ← mul_score_succ w a s x j]
    have bound0 : score w (a ::ₘ s) x 0 ≤ scoreMax w (a ::ₘ s) x := by
      rw [score_cons_zero, scoreMax_cons]
      calc w a * score w s x 0 ≤ w a * scoreMax w s x := mul_le_mul_right (ih_le 0) _
        _ ≤ max (w a) x * scoreMax w s x := mul_le_mul_left (le_max_left _ _) _
    have hbound : ∀ i, score w (a ::ₘ s) x i ≤ scoreMax w (a ::ₘ s) x := by
      intro i
      cases i with
      | zero => exact bound0
      | succ j =>
        rw [scoreMax_cons]
        refine (boundsucc j).trans (max_le ?_ ?_)
        · calc score w s x j * x ≤ scoreMax w s x * x := mul_le_mul_left (ih_le j) x
            _ ≤ scoreMax w s x * max (w a) x := mul_le_mul_right (le_max_right _ _) _
            _ = max (w a) x * scoreMax w s x := mul_comm _ _
        · calc w a * score w s x (j+1) ≤ w a * scoreMax w s x := mul_le_mul_right (ih_le (j+1)) _
            _ ≤ max (w a) x * scoreMax w s x := mul_le_mul_left (le_max_left _ _) _
    rcases lt_trichotomy (w a) x with hlt | heq | hgt
    · -- Case B: `w a < x`
      have hlo' : lowerIdx w (a ::ₘ s) x = lowerIdx w s x + 1 := by
        rw [lowerIdx_cons, if_pos hlt, Nat.one_add]
      have hhi' : upperIdx w (a ::ₘ s) x = upperIdx w s x + 1 := by
        rw [upperIdx_cons, if_pos hlt.le, Nat.one_add]
      have hM' : scoreMax w (a ::ₘ s) x = scoreMax w s x * max (w a) x := by
        rw [scoreMax_cons, mul_comm]
      refine ⟨hbound, ?_, ?_, ?_, ?_⟩
      · intro i hi
        rw [hlo'] at hi
        rw [hM']
        cases i with
        | zero =>
          rw [score_cons_zero]
          calc w a * score w s x 0 ≤ w a * scoreMax w s x := mul_le_mul_right (ih_le 0) _
            _ < x * scoreMax w s x := mul_lt_mul_ne_right hlt hMb
            _ = scoreMax w s x * max (w a) x := by rw [max_eq_right hlt.le, mul_comm]
        | succ j =>
          refine (boundsucc j).trans_lt (max_lt ?_ ?_)
          · exact mul_x_lt_mul_max_of_lt (ih_lt_lo j (by omega)) hx
          · calc w a * score w s x (j+1) ≤ w a * scoreMax w s x := mul_le_mul_right (ih_le (j+1)) _
              _ < x * scoreMax w s x := mul_lt_mul_ne_right hlt hMb
              _ = scoreMax w s x * max (w a) x := by rw [max_eq_right hlt.le, mul_comm]
      · rw [hlo', hM']
        refine (score_cons_succ_eq_of_dominated_right w a s hx (lowerIdx w s x) ?_).trans ?_
        · calc w a * score w s x (lowerIdx w s x + 1)
              ≤ w a * scoreMax w s x := mul_le_mul_right (ih_le _) _
            _ < x * scoreMax w s x := mul_lt_mul_ne_right hlt hMb
            _ = scoreMax w s x * x := mul_comm _ _
            _ = score w s x (lowerIdx w s x) * x := by rw [ih_lo]
        · rw [ih_lo, max_eq_right hlt.le]
      · rw [hhi', hM']
        refine (score_cons_succ_eq_of_dominated_right w a s hx (upperIdx w s x) ?_).trans ?_
        · calc w a * score w s x (upperIdx w s x + 1)
              ≤ w a * scoreMax w s x := mul_le_mul_right (ih_le _) _
            _ < x * scoreMax w s x := mul_lt_mul_ne_right hlt hMb
            _ = scoreMax w s x * x := mul_comm _ _
            _ = score w s x (upperIdx w s x) * x := by rw [ih_hi]
        · rw [ih_hi, max_eq_right hlt.le]
      · intro i hi
        rw [hhi'] at hi
        rw [hM']
        cases i with
        | zero => omega
        | succ j =>
          refine (boundsucc j).trans_lt (max_lt ?_ ?_)
          · exact mul_x_lt_mul_max_of_lt (ih_lt_hi j (by omega)) hx
          · calc w a * score w s x (j+1) ≤ w a * scoreMax w s x := mul_le_mul_right (ih_le (j+1)) _
              _ < x * scoreMax w s x := mul_lt_mul_ne_right hlt hMb
              _ = scoreMax w s x * max (w a) x := by rw [max_eq_right hlt.le, mul_comm]
    · -- Case C: `w a = x`
      have hlo' : lowerIdx w (a ::ₘ s) x = lowerIdx w s x := by
        rw [lowerIdx_cons, if_neg (not_lt.mpr heq.ge), Nat.zero_add]
      have hhi' : upperIdx w (a ::ₘ s) x = upperIdx w s x + 1 := by
        rw [upperIdx_cons, if_pos heq.le, Nat.one_add]
      have hM' : scoreMax w (a ::ₘ s) x = scoreMax w s x * max (w a) x := by
        rw [scoreMax_cons, mul_comm]
      have hmax : max (w a) x = x := by rw [heq, max_self]
      refine ⟨hbound, ?_, ?_, ?_, ?_⟩
      · intro i hi
        rw [hlo'] at hi
        rw [hM']
        cases i with
        | zero =>
          rw [score_cons_zero]
          calc w a * score w s x 0 = x * score w s x 0 := by rw [heq]
            _ < x * scoreMax w s x := mul_lt_mul_ne_left (ih_lt_lo 0 hi) hx
            _ = scoreMax w s x * x := mul_comm _ _
            _ = scoreMax w s x * max (w a) x := by rw [hmax]
        | succ j =>
          refine (boundsucc j).trans_lt (max_lt ?_ ?_)
          · calc score w s x j * x < scoreMax w s x * x := mul_lt_mul_ne_right (ih_lt_lo j (by omega)) hx
              _ ≤ scoreMax w s x * max (w a) x := mul_le_mul_right (le_max_right _ _) _
          · calc w a * score w s x (j+1) = x * score w s x (j+1) := by rw [heq]
              _ < x * scoreMax w s x := mul_lt_mul_ne_left (ih_lt_lo (j+1) (by omega)) hx
              _ = scoreMax w s x * x := mul_comm _ _
              _ ≤ scoreMax w s x * max (w a) x := mul_le_mul_right (le_max_right _ _) _
      · rw [hlo', hM']
        cases hlocase : lowerIdx w s x with
        | zero =>
          have hT : score w s x 0 = scoreMax w s x := by rw [← hlocase]; exact ih_lo
          rw [score_cons_zero, hT, heq, max_self, mul_comm]
        | succ k =>
          have hk1 : score w s x (k+1) = scoreMax w s x := by rw [← hlocase]; exact ih_lo
          have hklt : score w s x k < scoreMax w s x := ih_lt_lo k (by omega)
          refine (score_cons_succ_eq_of_dominated_left w a s hx k ?_).trans ?_
          · calc score w s x k * x < scoreMax w s x * x := mul_lt_mul_ne_right hklt hx
              _ = x * scoreMax w s x := mul_comm _ _
              _ = w a * score w s x (k+1) := by rw [heq, hk1]
          · rw [hk1, heq, max_self, mul_comm]
      · rw [hhi', hM']
        refine (score_cons_succ_eq_of_dominated_right w a s hx (upperIdx w s x) ?_).trans ?_
        · calc w a * score w s x (upperIdx w s x + 1)
              = x * score w s x (upperIdx w s x + 1) := by rw [heq]
            _ < x * scoreMax w s x := mul_lt_mul_ne_left (ih_lt_hi (upperIdx w s x + 1) (by omega)) hx
            _ = scoreMax w s x * x := mul_comm _ _
            _ = score w s x (upperIdx w s x) * x := by rw [ih_hi]
        · rw [ih_hi, hmax]
      · intro i hi
        rw [hhi'] at hi
        rw [hM']
        cases i with
        | zero => omega
        | succ j =>
          refine (boundsucc j).trans_lt (max_lt ?_ ?_)
          · calc score w s x j * x < scoreMax w s x * x := mul_lt_mul_ne_right (ih_lt_hi j (by omega)) hx
              _ ≤ scoreMax w s x * max (w a) x := mul_le_mul_right (le_max_right _ _) _
          · calc w a * score w s x (j+1) = x * score w s x (j+1) := by rw [heq]
              _ < x * scoreMax w s x := mul_lt_mul_ne_left (ih_lt_hi (j+1) (by omega)) hx
              _ = scoreMax w s x * x := mul_comm _ _
              _ ≤ scoreMax w s x * max (w a) x := mul_le_mul_right (le_max_right _ _) _
    · -- Case A: `x < w a`
      have hlo' : lowerIdx w (a ::ₘ s) x = lowerIdx w s x := by
        rw [lowerIdx_cons, if_neg (not_lt.mpr hgt.le), Nat.zero_add]
      have hhi' : upperIdx w (a ::ₘ s) x = upperIdx w s x := by
        rw [upperIdx_cons, if_neg (not_le.mpr hgt), Nat.zero_add]
      have hM' : scoreMax w (a ::ₘ s) x = scoreMax w s x * max (w a) x := by
        rw [scoreMax_cons, mul_comm]
      have hmax : max (w a) x = w a := max_eq_left hgt.le
      have hwane : w a ≠ 0 := ne_of_gt (lt_trans hx0 hgt)
      refine ⟨hbound, ?_, ?_, ?_, ?_⟩
      · intro i hi
        rw [hlo'] at hi
        rw [hM']
        cases i with
        | zero =>
          rw [score_cons_zero]
          exact mul_lt_mul_max_of_lt (ih_lt_lo 0 (by omega)) hMb hx
        | succ j =>
          refine (boundsucc j).trans_lt (max_lt ?_ ?_)
          · calc score w s x j * x < scoreMax w s x * x := mul_lt_mul_ne_right (ih_lt_lo j (by omega)) hx
              _ < scoreMax w s x * max (w a) x := mul_lt_mul_ne_left (by rw [hmax]; exact hgt) hMb
          · calc w a * score w s x (j+1) < w a * scoreMax w s x :=
                mul_lt_mul_ne_left (ih_lt_lo (j+1) (by omega)) hwane
              _ ≤ max (w a) x * scoreMax w s x := mul_le_mul_left (le_max_left _ _) _
              _ = scoreMax w s x * max (w a) x := mul_comm _ _
      · rw [hlo', hM']
        cases hlocase : lowerIdx w s x with
        | zero =>
          have hT : score w s x 0 = scoreMax w s x := by rw [← hlocase]; exact ih_lo
          rw [score_cons_zero, hT, hmax, mul_comm]
        | succ k =>
          have hk1 : score w s x (k+1) = scoreMax w s x := by rw [← hlocase]; exact ih_lo
          have hklt : score w s x k < scoreMax w s x := ih_lt_lo k (by omega)
          refine (score_cons_succ_eq_of_dominated_left w a s hx k ?_).trans ?_
          · calc score w s x k * x < scoreMax w s x * x := mul_lt_mul_ne_right hklt hx
              _ < scoreMax w s x * w a := mul_lt_mul_ne_left hgt hMb
              _ = w a * score w s x (k+1) := by rw [hk1, mul_comm]
          · rw [hk1, hmax, mul_comm]
      · rw [hhi', hM']
        cases hhicase : upperIdx w s x with
        | zero =>
          have hT : score w s x 0 = scoreMax w s x := by rw [← hhicase]; exact ih_hi
          rw [score_cons_zero, hT, hmax, mul_comm]
        | succ k =>
          have hk1 : score w s x (k+1) = scoreMax w s x := by rw [← hhicase]; exact ih_hi
          refine (score_cons_succ_eq_of_dominated_left w a s hx k ?_).trans ?_
          · calc score w s x k * x ≤ scoreMax w s x * x := mul_le_mul_left (ih_le k) x
              _ < scoreMax w s x * w a := mul_lt_mul_ne_left hgt hMb
              _ = w a * score w s x (k+1) := by rw [hk1, mul_comm]
          · rw [hk1, hmax, mul_comm]
      · intro i hi
        rw [hhi'] at hi
        rw [hM']
        cases i with
        | zero => omega
        | succ j =>
          refine (boundsucc j).trans_lt (max_lt ?_ ?_)
          · refine mul_x_lt_mul_max_of_le (ih_le j) hMb ?_
            exact lt_of_lt_of_le hgt (le_max_left _ _)
          · calc w a * score w s x (j+1) < w a * scoreMax w s x :=
                mul_lt_mul_ne_left (ih_lt_hi (j+1) (by omega)) hwane
              _ ≤ max (w a) x * scoreMax w s x := mul_le_mul_left (le_max_left _ _) _
              _ = scoreMax w s x * max (w a) x := mul_comm _ _

end

end NewtonPolygonScore

open NewtonPolygonScore in
/-- **Newton polygon, coefficient scores of a splitting polynomial.** Let `f` be monic and split
in `F`, and let `0 ≠ x ∈ Γ₀`. Then every `x`-score `i ↦ w (f.coeff i) * x ^ i` of a coefficient of
`f` is bounded by `M = ∏_{C ∈ f.roots} max (w C) x`; the score is strictly below `M` at all indices
outside the interval `[#{C ∈ f.roots | w C < x}, #{C ∈ f.roots | w C ≤ x}]`, and equals `M` at the
two endpoints. In other words, the `x`-scores are maximal exactly at (at least) those two indices,
and nowhere outside that interval. -/
theorem newtonPolygon_coeff_score {F : Type*} [Field F] {Γ₀ : Type*}
    [LinearOrderedCommGroupWithZero Γ₀] (w : Valuation F Γ₀) {f : Polynomial F} (hf : f.Monic)
    (hsp : f.Splits) {x : Γ₀} (hx : x ≠ 0) :
    (∀ i, w (f.coeff i) * x ^ i ≤ (f.roots.map (fun C => max (w C) x)).prod) ∧
    (∀ i, i < (f.roots.filter (fun C => w C < x)).card →
      w (f.coeff i) * x ^ i < (f.roots.map (fun C => max (w C) x)).prod) ∧
    w (f.coeff (f.roots.filter (fun C => w C < x)).card)
        * x ^ (f.roots.filter (fun C => w C < x)).card
      = (f.roots.map (fun C => max (w C) x)).prod ∧
    w (f.coeff (f.roots.filter (fun C => w C ≤ x)).card)
        * x ^ (f.roots.filter (fun C => w C ≤ x)).card
      = (f.roots.map (fun C => max (w C) x)).prod ∧
    (∀ i, (f.roots.filter (fun C => w C ≤ x)).card < i →
      w (f.coeff i) * x ^ i < (f.roots.map (fun C => max (w C) x)).prod) := by
  have hpoly : rootsPoly f.roots = f := (hsp.eq_prod_roots_of_monic hf).symm
  obtain ⟨h1, h2, h3, h4, h5⟩ := score_good w f.roots hx
  exact ⟨fun i => by simpa only [score, scoreMax, hpoly] using h1 i,
    fun i hi => by simpa only [score, scoreMax, lowerIdx, hpoly] using h2 i hi,
    by simpa only [score, scoreMax, lowerIdx, hpoly] using h3,
    by simpa only [score, scoreMax, upperIdx, hpoly] using h4,
    fun i hi => by simpa only [score, scoreMax, upperIdx, hpoly] using h5 i hi⟩


open NewtonPolygonScore in
/-- **Newton polygon, isolated root value.** Let `f ∈ F[X]` be monic and split in `F`, and let `γ ≠ 0`
be a value that is attained by exactly one root of `f`. Then two consecutive coefficient
"`γ`-scores" `w (f.coeff i) * γ ^ i` agree, both coefficients being nonzero.

Proof plan: for a monic `f` splitting in `F` with root multiset `s`, and `x ≠ 0`, one proves by
induction on the multiset (using the product rules for the largest/smallest index attaining the
maximum of the score `i ↦ w (f.coeff i) * x ^ i`) that
`max {i | score i maximal} = #{C ∈ s | w C ≤ x}` and
`min {i | score i maximal} = #{C ∈ s | w C < x}`;
with the hypothesis `(f.roots.filter (fun C => w C = γ)).card = 1` the two differ by `1`, so
consecutive indices attain the maximum, giving the equation. -/
theorem exists_coeff_score_eq_of_unique_val {F : Type*} [Field F] {Γ₀ : Type*}
    [LinearOrderedCommGroupWithZero Γ₀] (w : Valuation F Γ₀) {f : Polynomial F} (hf : f.Monic)
    (hsp : f.Splits) {γ : Γ₀} (hγ : γ ≠ 0)
    (hcard : (f.roots.filter (fun C => w C = γ)).card = 1) :
    ∃ i, i < f.natDegree ∧ f.coeff i ≠ 0 ∧ f.coeff (i + 1) ≠ 0 ∧
      w (f.coeff i) * γ ^ i = w (f.coeff (i + 1)) * γ ^ (i + 1) := by
  have hpoly : rootsPoly f.roots = f := (hsp.eq_prod_roots_of_monic hf).symm
  obtain ⟨hle, hltlo, hlo, hhi, hlthi⟩ := score_good w f.roots hγ
  have hcount : upperIdx w f.roots γ = lowerIdx w f.roots γ + 1 := by
    have hdisj : (f.roots.filter (fun C => w C < γ ∧ w C = γ)) = 0 := by
      rw [Multiset.filter_eq_nil]
      intro C _ h
      exact absurd h.2 (ne_of_lt h.1)
    have hcongr : (f.roots.filter (fun C => w C < γ ∨ w C = γ))
        = (f.roots.filter (fun C => w C ≤ γ)) := by
      refine Multiset.filter_congr ?_
      intro C _
      exact ⟨fun h => h.elim le_of_lt le_of_eq,
        fun h => le_iff_lt_or_eq.mp h⟩
    have key := Multiset.filter_add_filter (p := fun C => w C < γ) (q := fun C => w C = γ) f.roots
    have key2 : (f.roots.filter (fun C => w C < γ)) + (f.roots.filter (fun C => w C = γ))
        = (f.roots.filter (fun C => w C ≤ γ)) := by
      rw [key, hdisj, add_zero, hcongr]
    have hcard_le : (f.roots.filter (fun C => w C ≤ γ)).card
        = (f.roots.filter (fun C => w C < γ)).card + 1 := by
      rw [← key2, Multiset.card_add, hcard]
    simpa only [upperIdx, lowerIdx] using hcard_le
  have hMne : scoreMax w f.roots γ ≠ 0 := scoreMax_ne_zero w f.roots hγ
  refine ⟨lowerIdx w f.roots γ, ?_, ?_, ?_, ?_⟩
  · have h1 : lowerIdx w f.roots γ < upperIdx w f.roots γ := by omega
    have h2 : upperIdx w f.roots γ ≤ f.natDegree := by
      rw [hsp.natDegree_eq_card_roots, upperIdx]
      exact Multiset.card_le_card (Multiset.filter_le _ _)
    exact lt_of_lt_of_le h1 h2
  · intro hzero
    have hz : score w f.roots γ (lowerIdx w f.roots γ) = 0 := by
      rw [score, hpoly, hzero, Valuation.map_zero, zero_mul]
    rw [hlo] at hz
    exact hMne hz
  · have hscore_hi : score w f.roots γ (lowerIdx w f.roots γ + 1) = scoreMax w f.roots γ := by
      rw [← hcount]; exact hhi
    intro hzero
    have hz : score w f.roots γ (lowerIdx w f.roots γ + 1) = 0 := by
      rw [score, hpoly, hzero, Valuation.map_zero, zero_mul]
    rw [hscore_hi] at hz
    exact hMne hz
  · have hscore_hi : score w f.roots γ (lowerIdx w f.roots γ + 1) = scoreMax w f.roots γ := by
      rw [← hcount]; exact hhi
    calc w (f.coeff (lowerIdx w f.roots γ)) * γ ^ (lowerIdx w f.roots γ)
        = score w f.roots γ (lowerIdx w f.roots γ) := by rw [score, hpoly]
      _ = scoreMax w f.roots γ := hlo
      _ = score w f.roots γ (lowerIdx w f.roots γ + 1) := hscore_hi.symm
      _ = w (f.coeff (lowerIdx w f.roots γ + 1)) * γ ^ (lowerIdx w f.roots γ + 1) := by
            rw [score, hpoly]

end Commons.RingTheory.Valuation.NewtonPolygon