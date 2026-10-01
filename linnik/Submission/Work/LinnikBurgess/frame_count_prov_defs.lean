import Mathlib
import Submission.Work.LinnikBurgess.burgess_lead_defs
import Submission.Work.LinnikBurgess.DdBits
import Submission.Work.LinnikBurgess.frame_step_defs
import Submission.Work.LinnikBurgess.frameSum_eq_zero

/-!
# Definitions for the proof of Theorem F (`frame_count`)

This file sets up the "master sum" form of the frame count and the case predicates used in
its proof.

* `box3 H` is the box `[1,H]^3` of `ℕ`-triples;
* `del x y = |x - y|` and `wg m x y = √(gcd m |x-y|)` are the elementary weight factors;
* `wtAB m a b` is the full weight `∏_{l ≠ 0} √(gcd m |a 0 - v_l|)` of the shift vector
  `v = (a 0,a 1,a 2,b 0,b 1,b 2)`;
* `condAB d g a b` is the conjunction of the singleton condition at the index `0`, `DLd d a b`
  and `g ∣ contAB a b`;
* `masterSum H m d g` is the frame sum in these coordinates, `masterSum2` its iterated form.

The case predicates `CaseI`, `CaseS`, `CaseT` implement the exhaustive case split of the proof
(the frame-step case, the "one shared value" case and the "two shared values" case).
-/

open scoped BigOperators

namespace Work.LinnikBurgess

open Classical

/-- The box `[1,H]^3` of triples of integers in `[1,H]`. -/
def box3 (H : ℕ) : Finset (Fin 3 → ℕ) := Fintype.piFinset (fun _ : Fin 3 => Finset.Icc 1 H)

/-- `δ x y = |x - y|`. -/
def del (x y : ℕ) : ℕ := ((x : ℤ) - (y : ℤ)).natAbs

/-- The elementary weight factor `√(gcd m |x - y|)`. -/
noncomputable def wg (m : ℕ) (x y : ℕ) : ℝ := Real.sqrt (((Nat.gcd m (del x y) : ℕ) : ℝ))

/-- The full weight of the pair `(a,b)` with pivot `a 0`. -/
noncomputable def wtAB (m : ℕ) (a b : Fin 3 → ℕ) : ℝ :=
  wg m (a 0) (a 1) * wg m (a 0) (a 2) * (wg m (a 0) (b 0) * wg m (a 0) (b 1) * wg m (a 0) (b 2))

/-- `a 0` is not one of the entries of `b`. -/
def NotInB (a b : Fin 3 → ℕ) : Prop := ∀ l : Fin 3, a 0 ≠ b l

/-- `x` occurs among the entries of `b`. -/
def inB (x : ℕ) (b : Fin 3 → ℕ) : Prop := b 0 = x ∨ b 1 = x ∨ b 2 = x

/-- The number of occurrences of `x` among the entries of `b`. -/
def multB (x : ℕ) (b : Fin 3 → ℕ) : ℕ := (Finset.univ.filter (fun l : Fin 3 => b l = x)).card

/-- The conditions of the frame count at the singleton index `0`. -/
def condAB (d g : ℕ) (a b : Fin 3 → ℕ) : Prop :=
  NotInB a b ∧ a 0 ≠ a 1 ∧ a 0 ≠ a 2 ∧ DLd d a b ∧ g ∣ contAB a b

/-- **Case I** (frame-step case): at least one of the two other `a`-entries is not a `b`-entry. -/
def CaseI (a b : Fin 3 → ℕ) : Prop := ¬ inB (a 1) b ∨ ¬ inB (a 2) b

/-- **Case S** (collapsed case): the two non-pivot `a`-entries coincide. -/
def CaseS (a b : Fin 3 → ℕ) : Prop := a 1 = a 2

/-- **Case T** (distinct shared values): both non-pivot `a`-entries occur in `b` and are distinct. -/
def CaseT (a b : Fin 3 → ℕ) : Prop := inB (a 1) b ∧ inB (a 2) b ∧ a 1 ≠ a 2

/-- The frame sum in `ℕ`-coordinates. -/
noncomputable def masterSum (H m d g : ℕ) : ℝ :=
  ∑ a ∈ box3 H, ∑ b ∈ box3 H, (if condAB d g a b then wtAB m a b else 0)

/-- The frame sum with the two triples expanded into coordinates. -/
noncomputable def masterSum2 (H m d g : ℕ) : ℝ :=
  ∑ x0 ∈ Finset.Icc 1 H, ∑ x1 ∈ Finset.Icc 1 H, ∑ x2 ∈ Finset.Icc 1 H,
    ∑ y0 ∈ Finset.Icc 1 H, ∑ y1 ∈ Finset.Icc 1 H, ∑ y2 ∈ Finset.Icc 1 H,
      (if condAB d g ![x0, x1, x2] ![y0, y1, y2]
        then wtAB m ![x0, x1, x2] ![y0, y1, y2] else 0)

/-- The part of the master sum in case I. -/
noncomputable def sumI (H m d g : ℕ) : ℝ :=
  ∑ a ∈ box3 H, ∑ b ∈ box3 H,
    (if condAB d g a b ∧ CaseI a b then wtAB m a b else 0)

/-- The part of the master sum in case S. -/
noncomputable def sumS (H m d g : ℕ) : ℝ :=
  ∑ a ∈ box3 H, ∑ b ∈ box3 H,
    (if condAB d g a b ∧ CaseS a b then wtAB m a b else 0)

/-- The part of the master sum in case T. -/
noncomputable def sumT (H m d g : ℕ) : ℝ :=
  ∑ a ∈ box3 H, ∑ b ∈ box3 H,
    (if condAB d g a b ∧ CaseT a b then wtAB m a b else 0)

/-- The right-hand side of the frame count, with the constant `10^5` replaced by a smaller
budget `C` (the three case estimates each get such a budget). -/
noncomputable def rhsC (C H m d g : ℕ) : ℝ :=
  (C : ℝ) * ((m * d * g).divisors.card : ℝ) ^ 8
    * ((H : ℝ) ^ 6 / ((d : ℝ) * (g : ℝ)) + (H : ℝ) ^ 5 / (g : ℝ))

/-! ### Elementary facts -/

lemma wg_nonneg (m x y : ℕ) : 0 ≤ wg m x y := Real.sqrt_nonneg _

lemma del_comm (x y : ℕ) : del x y = del y x := by
  rw [del, del, show ((x : ℤ) - (y : ℤ)) = -((y : ℤ) - (x : ℤ)) by ring, Int.natAbs_neg]

lemma del_eq_zero_iff {x y : ℕ} : del x y = 0 ↔ x = y := by
  rw [del, Int.natAbs_eq_zero, sub_eq_zero]
  exact_mod_cast Iff.rfl

lemma del_pos {x y : ℕ} (h : x ≠ y) : 0 < del x y :=
  Nat.pos_of_ne_zero (fun hz => h (del_eq_zero_iff.mp hz))

lemma del_le_max (x y : ℕ) : del x y ≤ max x y := by
  rcases le_total x y with h | h
  · have h' : (x : ℤ) - (y : ℤ) = -(((y - x : ℕ)) : ℤ) := by
      rw [Nat.cast_sub h]; ring
    rw [del, h', Int.natAbs_neg, Int.natAbs_natCast]
    exact (Nat.sub_le y x).trans (le_max_right x y)
  · have h' : (x : ℤ) - (y : ℤ) = (((x - y : ℕ)) : ℤ) := by
      rw [Nat.cast_sub h]
    rw [del, h', Int.natAbs_natCast]
    exact (Nat.sub_le x y).trans (le_max_left x y)

lemma wg_le_sqrt_del {m x y : ℕ} (h : x ≠ y) :
    wg m x y ≤ Real.sqrt ((del x y : ℕ) : ℝ) := by
  rw [wg]
  apply Real.sqrt_le_sqrt
  exact_mod_cast Nat.gcd_le_right m (del_pos h)

lemma wg_pos {m : ℕ} (hm : 0 < m) {x y : ℕ} (h : x ≠ y) : 0 < wg m x y := by
  rw [wg]
  apply Real.sqrt_pos.mpr
  have h2 : 0 < Nat.gcd m (del x y) := Nat.gcd_pos_of_pos_left (del x y) hm
  exact_mod_cast h2

/-- `√(gcd m |x-y|) ≤ √H` for `x, y ∈ [1,H]` and `x ≠ y`. -/
lemma wg_le_sqrt_H {m x y H : ℕ} (hx : x ≤ H) (hy : y ≤ H) (h : x ≠ y) :
    wg m x y ≤ Real.sqrt (H : ℝ) := by
  refine (wg_le_sqrt_del h).trans ?_
  apply Real.sqrt_le_sqrt
  exact_mod_cast (del_le_max x y).trans (max_le hx hy)

lemma wg_one_le {m : ℕ} (hm : 0 < m) (x y : ℕ) : 1 ≤ wg m x y := by
  rw [wg]
  apply Real.one_le_sqrt.mpr
  have h2 : 1 ≤ Nat.gcd m (del x y) :=
    Nat.one_le_iff_ne_zero.mpr
      (Nat.pos_iff_ne_zero.mp (Nat.gcd_pos_of_pos_left (del x y) hm))
  exact_mod_cast h2

/-- `√(gcd m |x-y|) ≤ gcd m |x-y|` (for `m > 0`). -/
lemma wg_le_gcd {m : ℕ} (hm : 0 < m) (x y : ℕ) :
    wg m x y ≤ ((Nat.gcd m (del x y) : ℕ) : ℝ) := by
  have h1 : 1 ≤ wg m x y := wg_one_le hm x y
  have h2 : wg m x y * wg m x y = ((Nat.gcd m (del x y) : ℕ) : ℝ) := by
    rw [wg, Real.mul_self_sqrt (Nat.cast_nonneg _)]
  calc wg m x y ≤ wg m x y * wg m x y :=
        le_mul_of_one_le_right (wg_nonneg m x y) h1
    _ = ((Nat.gcd m (del x y) : ℕ) : ℝ) := h2

/-- Divisor-count monotonicity. -/
lemma card_divisors_le_of_dvd {a b : ℕ} (h : a ∣ b) (hb : b ≠ 0) :
    a.divisors.card ≤ b.divisors.card :=
  Finset.card_le_card (Nat.divisors_subset_of_dvd hb h)


/-- The frame sum restricted to a case predicate `P`, in iterated coordinates. -/
noncomputable def sum2 (H m d g : ℕ) (P : (Fin 3 → ℕ) → (Fin 3 → ℕ) → Prop) : ℝ :=
  ∑ x0 ∈ Finset.Icc 1 H, ∑ x1 ∈ Finset.Icc 1 H, ∑ x2 ∈ Finset.Icc 1 H,
    ∑ y0 ∈ Finset.Icc 1 H, ∑ y1 ∈ Finset.Icc 1 H, ∑ y2 ∈ Finset.Icc 1 H,
      (if condAB d g ![x0, x1, x2] ![y0, y1, y2] ∧ P ![x0, x1, x2] ![y0, y1, y2]
        then wtAB m ![x0, x1, x2] ![y0, y1, y2] else 0)

/-- The three relaxed cases cover every pair. -/
lemma case_cover (a b : Fin 3 → ℕ) : CaseI a b ∨ CaseS a b ∨ CaseT a b := by
  by_cases h : CaseI a b
  · exact Or.inl h
  · rw [CaseI] at h
    push_neg at h
    by_cases h2 : a 1 = a 2
    · exact Or.inr (Or.inl (by rw [CaseS]; exact h2))
    · exact Or.inr (Or.inr (by rw [CaseT]; exact ⟨h.1, h.2, h2⟩))


/-!
## Proof plan for the three case estimates

Everything below this point is a *plan* (the lemmas are established elsewhere).  Fix
`x0, x1, x2 ∈ [1,H]` (the entries of `a`) and `y0, y1, y2 ∈ [1,H]` (the entries of `b`), write
`x = (x0,x1,x2)`, `y = (y0,y1,y2)`, and recall

* `wtAB m x y = wg x0 x1 * wg x0 x2 * (wg x0 y0 * wg x0 y1 * wg x0 y2)`,
* `condAB d g x y = NotInB x y ∧ x0 ≠ x1 ∧ x0 ≠ x2 ∧ DLd d x y ∧ g ∣ contAB x y`,
* `wg m u v = √(gcd m |u-v|)`, so `(wg m u v)^2 = gcd m |u-v|` and `wg ≥ 1` for `m > 0`.

Two auxiliary inputs are used everywhere.

* (`bsum_expansion`) if `g > 0` then for any `F : Fin 3 → ℕ → ℝ` with `F k y ≥ 0`,
  `∑_{y ∈ box3 H} [g ∣ ∏_k |y_k - x0|] * ∏_k [y_k ≠ x0] * F k (y_k)`
  `≤ ∑_{g = g0g1g2} ∏_k ∑_{y ≠ x0, g_k ∣ |y - x0|} F k y`, and each inner sum is bounded by
  the lemmas in `frame_count_prov_aux/wg_sum_filtered` and `.../sum_frame_weight`.
* `contAB x y ∣ ∏_k |y_k - x0|` (from `contAB_dvd_cubicZ_eval_neg`), so `g ∣ contAB x y`
  implies `g ∣ ∏_k |y_k - x0|`, which is what the expansion needs.

**Case S** (`x1 = x2`).  The weight is `(wg x0 x1)^2 * ∏_k wg x0 y_k`.  The constraint
`g ∣ ∏_k |y_k - x0|` is expanded with exponents `(1,1,1)`, giving
`τ(g)^2 * (2H/g_0)(2H/g_1)(2H/g_2) τ(m)^3 = 8 τ(g)^2 H^3 τ(m)^3 / g`; the factor
`(wg x0 x1)^2 = gcd m |x0 - x1|` summed over `x1 ≠ x0` is `≤ 2H τ(m)`; and `x0` runs over
`H` values.  Total `≤ 16 τ(g)^2 τ(m)^4 H^4 / g`, which is below `30000 τ(m d g)^8 H^5/g` because
`τ(m d g)^8 ≥ τ(m)^4 τ(g)^2` and `H ≥ 1`.

**Case T** (`x1 ≠ x2`, `x1 ∈ {y_0,y_1,y_2}`, `x2 ∈ {y_0,y_1,y_2}`).  Choose the two distinct
slots `l1 ≠ l2` with `y_{l1} = x1`, `y_{l2} = x2` (at most `6` choices, and the remaining slot
holds a free value `γ ∈ [1,H]`); the weight then equals `(wg x0 x1)^2 (wg x0 x2)^2 wg x0 γ`
(`wtAB_caseT`).  Expanding `g ∣ |x1-x0| |x2-x0| |γ-x0|` with exponents `(2,2,1)` gives
`τ(g)^2 (2H/g_0)(2H/g_1)(2H/g_2) τ(m)^3`; the sums over `x1, x2, γ` and the `H` choices of
`x0` and the `6` slot choices give `≤ 48 τ(g)^2 τ(m)^4 H^4 /g`, again below the budget.

**Case I** (`x1 ∉ {y_k}` or `x2 ∉ {y_k}`).  By symmetry of the sum in `x1 ↔ x2` (`DLd_perm`) it
suffices to treat `x1 ∉ {y_k}`.  For fixed `x0, y` the double sum over `(x1,x2)` is split into
three parts: (i) `x2 ∉ {y_k}`, (ii) `x2 ∈ {y_k}`; in part (i) one uses the elementary inequality
`wg x0 x1 * wg x0 x2 ≤ ((wg x0 x1)^2 + (wg x0 x2)^2)/2` and the *frame step*
`frame_step_card_D`: for `x1 ∉ {y_k}` the number of `x2 ∈ [1,H]` with `DLd d ![x0,x1,x2] y` is at
most `3^{ω(d)} (2H gcd(d,|x0-x1|)/d + 1)` — and symmetrically with `x1` and `x2` interchanged
(using `DLd_perm` to reorder the triple).  In part (ii), `x2` is one of the three `y_k`, so
`wg x0 x2 ≤ ∏_k wg x0 y_k`, and the number of admissible `x2` is again bounded by the frame step.
The remaining sums are bounded by `sum_frame_weight` (giving `≤ 3^{ω(d)} (4H^2 τ(m) τ(d)/d + 2H τ(m))`)
and by `bsum_expansion` with exponents `(1,1,1)` resp. `(2,2,2)`, i.e. by `8τ(g)^2H^3τ(m)^3/g`.
The total is `≤ 3^{ω(d)} · 128 · τ(g)^2 τ(m)^4 τ(d) · H^6/(dg) + 3^{ω(d)} · 64 · τ(g)^2 τ(m)^4 · H^5/g`,
which is below `30000 τ(m d g)^8 (H^6/(dg) + H^5/g)` because `3^{ω(d)} τ(d) ≤ τ(d)^2` and
`τ(m d g)^8 ≥ τ(m)^4 τ(d)^2 τ(g)^2`.
-/

open Polynomial

lemma int_dvd_of_nat_dvd_natAbs {n : ℕ} {z : ℤ} (h : n ∣ z.natAbs) : (n:ℤ) ∣ z := by
  have h2 : ((n:ℤ).natAbs) ∣ z.natAbs := by rw [Int.natAbs_natCast]; exact h
  exact Int.natAbs_dvd_natAbs.mp h2

/-- `contAB a b` divides `f_b(-a_i) = ∏_l (b_l - a_i)`. -/
theorem contAB_dvd_cubicZ_eval_neg (a b : Fin 3 → ℕ) (i : Fin 3) :
    ((contAB a b : ℕ) : ℤ) ∣ (cubicZ b).eval (-(((a i : ℕ) : ℤ))) := by
  have h0 : contAB a b ∣ (esymm3 a 0 - esymm3 b 0).natAbs := by
    unfold contAB; exact Nat.gcd_dvd_left _ _
  have h1 : contAB a b ∣ (esymm3 a 1 - esymm3 b 1).natAbs := by
    unfold contAB; exact Nat.dvd_trans (Nat.gcd_dvd_right _ _) (Nat.gcd_dvd_left _ _)
  have h2 : contAB a b ∣ (esymm3 a 2 - esymm3 b 2).natAbs := by
    unfold contAB; exact Nat.dvd_trans (Nat.gcd_dvd_right _ _) (Nat.gcd_dvd_right _ _)
  have hdvd0 := int_dvd_of_nat_dvd_natAbs h0
  have hdvd1 := int_dvd_of_nat_dvd_natAbs h1
  have hdvd2 := int_dvd_of_nat_dvd_natAbs h2
  have hz : (cubicZ a - cubicZ b)
      = C (esymm3 a 0 - esymm3 b 0) * X ^ 2 + C (esymm3 a 1 - esymm3 b 1) * X
          + C (esymm3 a 2 - esymm3 b 2) := by
    rw [cubicZ, cubicZ, Fin.prod_univ_three, Fin.prod_univ_three]
    simp only [esymm3, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
    simp only [map_add, map_mul, map_sub]
    ring
  have hev : ∀ z : ℤ, ((contAB a b : ℕ) : ℤ) ∣ (cubicZ a - cubicZ b).eval z := by
    intro z
    rw [hz]
    simp only [eval_add, eval_mul, eval_C, eval_pow, eval_X]
    exact dvd_add (dvd_add (dvd_mul_of_dvd_left hdvd0 (z^2)) (dvd_mul_of_dvd_left hdvd1 z)) hdvd2
  have hzero : (cubicZ a).eval (-(((a i : ℕ) : ℤ))) = 0 := by
    rw [cubicZ, eval_prod]
    refine Finset.prod_eq_zero (Finset.mem_univ i) ?_
    simp only [eval_add, eval_X, eval_C]
    ring
  have hsplit : (cubicZ b).eval (-(((a i : ℕ) : ℤ)))
      = (cubicZ a).eval (-(((a i : ℕ) : ℤ)))
        - (cubicZ a - cubicZ b).eval (-(((a i : ℕ) : ℤ))) := by
    rw [eval_sub]; ring
  rw [hsplit, hzero, zero_sub]
  exact dvd_neg.mpr (hev _)


end Work.LinnikBurgess
