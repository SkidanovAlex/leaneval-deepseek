import Mathlib
import Submission.Work.Genus.Defs
import Submission.Work.Genus.Deriv.deriv_aeval
import Submission.Work.Genus.Deriv.deriv_add
import Submission.Work.Genus.Deriv.deriv_mul
import Submission.Work.Genus.OrderInf.ordInf_aeval_of_neg
import Submission.Work.Genus.OrderInf.ordInf_deriv_ge
import Submission.Work.Genus.OrderInf.min_ordInf_le_ordInf_add
import Submission.Work.Genus.OrderInf.ordInf_mul
import Submission.Work.Genus.OrderInf.ordInf_pow
import Submission.Work.Genus.OrderInf.ordInf_add_eq_of_lt
import Submission.Work.Genus.OrderInf.ordInf_C_mul
import Submission.Work.Reflect.PolyId
set_option maxRecDepth 100000

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The pole at infinity of an Artin–Schreier relation in characteristic `5`

A function `r : M(t)` with a pole at infinity (`ordInf r < 0`) that satisfies an Artin–Schreier
type relation `A(r) ≡ u⁵ - u` modulo functions without a pole at infinity, with `2 ≤ deg A` and
`5 ∤ deg A` (characteristic `5`), must have a derivative vanishing to order at least `2` at
infinity.

The mechanism: writing `s = A(r) - (u⁵ - u)`, the two "leading term" computations at infinity
force the ramification equation `deg A · ordInf r = 5 · ordInf u`, which in turn forces
`5 ∣ ordInf r` (because `5 ∤ deg A`) and hence `ordInf r ≤ -5`.  Differentiating the relation gives
`A'(r) · r' = -u' + s'` (the derivative of `u⁵ - u` is `-u'` in characteristic `5`); taking orders
at infinity produces the estimate `ordInf r' ≥ ordInf u + 1 - (deg A - 1) · ordInf r`, which the
ramification equation turns into `ordInf r' ≥ 4`.
-/

set_option autoImplicit false

namespace Work.MotV5

open Polynomial

noncomputable section

/-! ## Elementary order-at-infinity helpers -/

/-- The order at infinity of `0` is `0` (the convention `RatFunc.intDegree 0 = 0`). -/
theorem ordInf_zero (F : Type*) [Field F] : Work.Genus.ordInf (0 : RatFunc F) = 0 := by
  simp [Work.Genus.ordInf, RatFunc.intDegree_zero]

/-- The order at infinity is unchanged by negation. -/
theorem ordInf_neg {F : Type*} [Field F] (f : RatFunc F) :
    Work.Genus.ordInf (-f) = Work.Genus.ordInf f := by
  simp [Work.Genus.ordInf, RatFunc.intDegree_neg]

/-- The formal derivative kills `0`. -/
theorem deriv_zero (F : Type*) [Field F] : Work.Genus.deriv (0 : RatFunc F) = 0 := by
  simp [Work.Genus.deriv]

/-- **The non-archimedean triangle inequality at infinity, in lower-bound form.**  If a
*non-positive* integer `c` bounds the orders at infinity of `f` and of `g` from below, it also
bounds the order of `f + g`.  (The hypothesis `c ≤ 0` is needed only in the degenerate case
`f + g = 0`, where `ordInf 0 = 0`; the other degenerate cases are immediate.) -/
theorem le_ordInf_add {F : Type*} [Field F] {f g : RatFunc F} {c : ℤ} (hc : c ≤ 0)
    (hf : c ≤ Work.Genus.ordInf f) (hg : c ≤ Work.Genus.ordInf g) :
    c ≤ Work.Genus.ordInf (f + g) := by
  rcases eq_or_ne f 0 with rfl | hf0
  · rw [zero_add]; exact hg
  rcases eq_or_ne g 0 with rfl | hg0
  · rw [add_zero]; exact hf
  rcases eq_or_ne (f + g) 0 with hfg | hfg
  · rw [hfg, ordInf_zero]; exact hc
  · exact le_trans (le_min hf hg)
      (Work.Genus.OrderInf.min_ordInf_le_ordInf_add hf0 hg0 hfg)

/-- If `u` has no pole at infinity (`0 ≤ ordInf u`) then neither has `u⁵`. -/
theorem ordInf_pow_five_nonneg {F : Type*} [Field F] {u : RatFunc F}
    (hu : 0 ≤ Work.Genus.ordInf u) : 0 ≤ Work.Genus.ordInf (u ^ 5) := by
  rcases eq_or_ne u 0 with rfl | hu0
  · rw [zero_pow (by norm_num : 5 ≠ 0), ordInf_zero]
  · rw [Work.Genus.OrderInf.ordInf_pow hu0 5]; nlinarith

/-- If `u` has a pole at infinity (`ordInf u < 0`) then `ordInf (u⁵ - u) = 5 * ordInf u`: the `u⁵`
term strictly dominates the `u` term. -/
theorem ordInf_pow_five_sub_self_of_neg {F : Type*} [Field F] {u : RatFunc F}
    (hu : Work.Genus.ordInf u < 0) :
    Work.Genus.ordInf (u ^ 5 - u) = 5 * Work.Genus.ordInf u := by
  have hu0 : u ≠ 0 := by
    intro h0
    rw [h0, ordInf_zero] at hu
    exact lt_irrefl 0 hu
  have hp : Work.Genus.ordInf (u ^ 5) = 5 * Work.Genus.ordInf u :=
    Work.Genus.OrderInf.ordInf_pow hu0 5
  have hlt : Work.Genus.ordInf (u ^ 5) < Work.Genus.ordInf (-u) := by
    rw [hp, ordInf_neg]
    linarith
  rw [sub_eq_add_neg, Work.Genus.OrderInf.ordInf_add_eq_of_lt (pow_ne_zero 5 hu0) hlt, hp]

/-! ## Two facts in characteristic `5` -/

/-- **The degree of the derivative.**  Over a field of characteristic `5`, if `5 ∤ deg A` then
`deriv A` really has degree `deg A - 1`: the top coefficient of `A'` is `deg A · (leading coeff A)`,
and `(deg A : M) ≠ 0` precisely because `5 ∤ deg A`. -/
theorem natDegree_derivative_eq_of_not_dvd {M : Type*} [Field M] [CharP M 5] {A : Polynomial M}
    (hA5 : ¬ 5 ∣ A.natDegree) : (Polynomial.derivative A).natDegree = A.natDegree - 1 := by
  rcases Nat.eq_zero_or_pos A.natDegree with h0 | hpos
  · rw [Polynomial.derivative_of_natDegree_zero h0, h0, Polynomial.natDegree_zero]
  · have hA0 : A ≠ 0 := by
      intro hA
      rw [hA, Polynomial.natDegree_zero] at hA5
      exact hA5 (dvd_zero 5)
    have hcoeff : (Polynomial.derivative A).coeff (A.natDegree - 1) ≠ 0 := by
      rw [Polynomial.coeff_derivative]
      have hsucc : A.natDegree - 1 + 1 = A.natDegree := Nat.succ_pred_eq_of_pos hpos
      rw [hsucc]
      have hlead : A.coeff A.natDegree ≠ 0 := by
        simpa only [Polynomial.leadingCoeff] using Polynomial.leadingCoeff_ne_zero.mpr hA0
      have hn : ((A.natDegree - 1 : ℕ) : M) + 1 ≠ 0 := by
        have hone : ((A.natDegree - 1 : ℕ) : M) + 1 = (A.natDegree : M) := by
          rw [← hsucc]
          push_cast
          first | refl_ring1 | ring
        rw [hone]
        exact fun hz => hA5 ((CharP.cast_eq_zero_iff M 5 A.natDegree).mp hz)
      exact mul_ne_zero hlead hn
    exact Polynomial.natDegree_eq_of_le_of_coeff_ne_zero
      (Polynomial.natDegree_derivative_le A) hcoeff

/-- **The derivative of `u⁵ - u` in characteristic `5`.**  Differentiating the polynomial
`X⁵ - X` and evaluating at `u` gives `(5 u⁴ - 1) · u' = -u'`. -/
theorem deriv_pow_five_sub_self {M : Type*} [Field M] [CharP M 5] (u : RatFunc M) :
    Work.Genus.deriv (u ^ 5 - u) = - Work.Genus.deriv u := by
  have h1 : u ^ 5 - u = Polynomial.aeval u (Polynomial.X ^ 5 - Polynomial.X : Polynomial M) := by
    rw [map_sub, map_pow, Polynomial.aeval_X]
  rw [h1, Work.Genus.Deriv.deriv_aeval]
  have h2 : Polynomial.aeval u
      (Polynomial.derivative (Polynomial.X ^ 5 - Polynomial.X : Polynomial M)) = -1 := by
    rw [Polynomial.derivative_sub, Polynomial.derivative_X_pow, Polynomial.derivative_X]
    rw [map_sub, map_mul, map_pow, Polynomial.aeval_X, map_one]
    rw [Polynomial.aeval_C, map_natCast]
    rw [show ((5 : ℕ) : RatFunc M) = 0 from CharP.cast_eq_zero (RatFunc M) 5]
    norm_num
  rw [h2]; ring

/-! ## The main theorem -/

theorem two_le_ordInf_deriv_of_pole {M : Type*} [Field M] [CharP M 5]
    {A : Polynomial M} (hA2 : 2 ≤ A.natDegree) (hA5 : ¬ 5 ∣ A.natDegree)
    {r u : RatFunc M} (hr : Work.Genus.ordInf r < 0)
    (h : 0 ≤ Work.Genus.ordInf (Polynomial.aeval r A - (u ^ 5 - u)))
    (hd : Work.Genus.deriv r ≠ 0) :
    2 ≤ Work.Genus.ordInf (Work.Genus.deriv r) := by
  have hr0 : r ≠ 0 := by
    intro h0
    rw [h0, ordInf_zero] at hr
    exact lt_irrefl 0 hr
  have hApos : 0 < A.natDegree := by omega
  have hd2 : (2 : ℤ) ≤ (A.natDegree : ℤ) := by exact_mod_cast hA2
  have h5d : ¬ (5 : ℤ) ∣ (A.natDegree : ℤ) := fun hc => hA5 (Int.natCast_dvd_natCast.mp hc)
  set s : RatFunc M := Polynomial.aeval r A - (u ^ 5 - u) with hs
  have hs' : 0 ≤ Work.Genus.ordInf s := h
  -- `A(r)` has a pole of order `deg A · ordInf r` at infinity.
  have hAord : Work.Genus.ordInf (Polynomial.aeval r A)
      = (A.natDegree : ℤ) * Work.Genus.ordInf r :=
    Work.Genus.OrderInf.ordInf_aeval_of_neg hApos hr0 hr
  have hAeval : Polynomial.aeval r A = (u ^ 5 - u) + s := by
    rw [hs]; ring
  rcases lt_or_ge (Work.Genus.ordInf u) 0 with hu | hu
  · -- ## Case 1: `u` also has a pole at infinity.
    have hu0 : u ≠ 0 := by
      intro h0
      rw [h0, ordInf_zero] at hu
      exact lt_irrefl 0 hu
    have hu5ord : Work.Genus.ordInf (u ^ 5 - u) = 5 * Work.Genus.ordInf u :=
      ordInf_pow_five_sub_self_of_neg hu
    -- **The ramification equation** `deg A · ordInf r = 5 · ordInf u`.
    have hkey : (A.natDegree : ℤ) * Work.Genus.ordInf r = 5 * Work.Genus.ordInf u := by
      refine le_antisymm ?_ ?_
      · -- `deg A · ordInf r ≤ 5 · ordInf u`, from `u⁵ - u = A(r) + (-s)`.
        have hsplit : u ^ 5 - u = Polynomial.aeval r A + (-s) := by
          rw [hAeval]; ring
        rw [← hu5ord, hsplit]
        exact le_ordInf_add (c := (A.natDegree : ℤ) * Work.Genus.ordInf r)
          (mul_nonpos_of_nonneg_of_nonpos (Int.natCast_nonneg _) hr.le)
          (le_of_eq hAord.symm)
          (by rw [ordInf_neg]
              exact le_trans (mul_nonpos_of_nonneg_of_nonpos (Int.natCast_nonneg _) hr.le)
                hs')
      · -- `5 · ordInf u ≤ deg A · ordInf r`, from `A(r) = (u⁵ - u) + s`.
        rw [← hAord, hAeval]
        exact le_ordInf_add (c := 5 * Work.Genus.ordInf u)
          (mul_nonpos_of_nonneg_of_nonpos (by norm_num) hu.le)
          (le_of_eq hu5ord.symm)
          (le_trans (mul_nonpos_of_nonneg_of_nonpos (by norm_num) hu.le) hs')
    -- Consequently `5 ∣ ordInf r` and `ordInf r ≤ -5`.
    have h5a : (5 : ℤ) ∣ Work.Genus.ordInf r := by
      have hdvd : (5 : ℤ) ∣ (A.natDegree : ℤ) * Work.Genus.ordInf r := by
        rw [hkey]; exact ⟨Work.Genus.ordInf u, rfl⟩
      rcases (show Prime (5 : ℤ) by norm_num).dvd_mul.mp hdvd with h' | h'
      · exact absurd h' h5d
      · exact h'
    have ha5 : Work.Genus.ordInf r ≤ -5 := by
      obtain ⟨k, hk⟩ := h5a
      have hklt : k < 0 := by nlinarith [hk, hr]
      omega
    have hub2 : Work.Genus.ordInf u ≤ -2 := by nlinarith [hkey, ha5, hd2]
    -- **The differentiated relation** `A'(r) · r' = -u' + s'`.
    have hnd : ((Polynomial.derivative A).natDegree : ℤ) = (A.natDegree : ℤ) - 1 := by
      rw [natDegree_derivative_eq_of_not_dvd hA5]
      omega
    have hpos : 0 < (Polynomial.derivative A).natDegree := by
      rw [natDegree_derivative_eq_of_not_dvd hA5]; omega
    have hA'ord : Work.Genus.ordInf (Polynomial.aeval r (Polynomial.derivative A))
        = ((Polynomial.derivative A).natDegree : ℤ) * Work.Genus.ordInf r :=
      Work.Genus.OrderInf.ordInf_aeval_of_neg hpos hr0 hr
    have hA'ne : Polynomial.aeval r (Polynomial.derivative A) ≠ 0 := by
      intro h0
      rw [h0, ordInf_zero] at hA'ord
      have hneg : ((Polynomial.derivative A).natDegree : ℤ) * Work.Genus.ordInf r < 0 :=
        mul_neg_of_pos_of_neg (by exact_mod_cast hpos) hr
      omega
    have hder : Polynomial.aeval r (Polynomial.derivative A) * Work.Genus.deriv r
        = - Work.Genus.deriv u + Work.Genus.deriv s := by
      conv_lhs => rw [← Work.Genus.Deriv.deriv_aeval (A := A) (x := r)]
      rw [hAeval, Work.Genus.Deriv.deriv_add, deriv_pow_five_sub_self]
    -- `-u' + s'` has order at infinity at least `ordInf u + 1`.
    have hrhs : Work.Genus.ordInf u + 1
        ≤ Work.Genus.ordInf (- Work.Genus.deriv u + Work.Genus.deriv s) := by
      refine le_ordInf_add (c := Work.Genus.ordInf u + 1) (by linarith) ?_ ?_
      · rw [ordInf_neg]
        rcases eq_or_ne (Work.Genus.deriv u) 0 with h0 | h0
        · rw [h0, ordInf_zero]; linarith
        · have := Work.Genus.OrderInf.ordInf_deriv_ge hu0 h0; linarith
      · rcases eq_or_ne (Work.Genus.deriv s) 0 with h0 | h0
        · rw [h0, ordInf_zero]; linarith
        · have hs0 : s ≠ 0 := fun hz => h0 (by rw [hz, deriv_zero])
          have := Work.Genus.OrderInf.ordInf_deriv_ge hs0 h0; linarith
    have hX : Work.Genus.ordInf u + 1
        - ((Polynomial.derivative A).natDegree : ℤ) * Work.Genus.ordInf r
        ≤ Work.Genus.ordInf (Work.Genus.deriv r) := by
      have h1 : Work.Genus.ordInf u + 1
          ≤ ((Polynomial.derivative A).natDegree : ℤ) * Work.Genus.ordInf r
            + Work.Genus.ordInf (Work.Genus.deriv r) := by
        rw [← hA'ord, ← Work.Genus.OrderInf.ordInf_mul hA'ne hd, hder]
        exact hrhs
      linarith
    rw [hnd] at hX
    nlinarith [hkey, ha5, hd2, hX]
  · -- ## Case 2: `u` has no pole at infinity — impossible.
    exfalso
    have hu5 : 0 ≤ Work.Genus.ordInf (u ^ 5 - u) := by
      rw [sub_eq_add_neg]
      exact le_ordInf_add (c := 0) le_rfl (ordInf_pow_five_nonneg hu)
        (by rw [ordInf_neg]; exact hu)
    have h0 : 0 ≤ Work.Genus.ordInf (Polynomial.aeval r A) := by
      rw [hAeval]
      exact le_ordInf_add (c := 0) le_rfl hu5 hs'
    rw [hAord] at h0
    have hneg : (A.natDegree : ℤ) * Work.Genus.ordInf r < 0 :=
      mul_neg_of_pos_of_neg (by exact_mod_cast hApos) hr
    omega

end

end Work.MotV5
