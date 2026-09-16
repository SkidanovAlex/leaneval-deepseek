import Mathlib.FieldTheory.Finite.Basic
import Submission.ZagierHoffmanProof.StepA3
import Submission.ZagierHoffmanProof.Carlitz
import Submission.ZagierHoffmanProof.StepK4
import Submission.ZagierHoffmanProof.StepK5
import Submission.ZagierHoffmanProof.StepK6
import Submission.ZagierHoffmanProof.StepL199
import Submission.ZagierHoffmanProof.ThakurDeg2
import Submission.Commons.Combinatorics.ThakurPoly.thakurPoly_rec

set_option autoImplicit false
set_option maxHeartbeats 2000000

open Polynomial
open scoped BigOperators

/-!
# Carlitz's expansion for the level-one power-sum polynomials `A_n`

This file develops the explicit formula (Carlitz 1935; Thakur, *Power sums* 2009) for the
level-one power-sum polynomials

  `A_n = ∑_{c : F} Q_c ^ n`,  `Q_c = ∏_{b ≠ c} (X + C b) = [1] / (X + C c)`,

namely

  `A_n = (-1)^n * ∑_{m ≥ 0} (-1)^m * C(n - 1 - m(q-1), m) * [1] ^ (m(q-1))`,   `q = |F|`,

equivalently `A_n = (-1)^n b_n(a)` for the Thakur polynomials
`b_n(T) = ∑_m (-1)^m C(n-1-m(q-1),m) T^m` at `a = [1]^(q-1)`.
These `A_n` are the numerators of Thakur's power sums `P_1(n) = A_n / [1]^n`; the formula
resolves the cancellation at the top degree of Carlitz's expansion of `S_1(k+1)` and is the
`d = 1` case of Hypothesis H1 of Thakur (2009).

## The two structural inputs

* `qPoly_pow_add` : `Q_c ^ q + Q_c ^ (q-1) = [1] ^ (q-1)` for every `c`
  (a rewriting of `[1] = (X+Cc)^q - (X+Cc)`);
* the Thakur–Pascal recursion for the polynomials `b_n` (commons lemma
  `Commons.Combinatorics.ThakurPoly.thakurPoly_rec`, requested separately).

## Consequences

* `A_recursion` : `A_n + A_{n-1} = [1]^(q-1) * A_{n-q}` for `n ≥ q`;
* `A_eq_neg_one_pow` : `A_n = (-1)^n` for `1 ≤ n ≤ q` (from the Thakur–Chen purity
  `P_d(n) = P_d(1)^n` for `n ≤ q`);
* `A_thakur_formula` : the explicit formula above.
-/

namespace ZagierHoffmanPositiveChar

variable (F : Type*) [Field F] [Finite F] [DecidableEq (RatFunc F)]

/-- `(X + C c) ^ q = X ^ q + C c` over a finite field of cardinality `q` (Freshman's dream
plus `c ^ q = c`). -/
lemma poly_X_add_C_pow_card (c : F) :
    (X + C c : F[X]) ^ Nat.card F = X ^ Nat.card F + C c := by
  classical
  rw [carlitz_add_pow_card F]
  have hc : c ^ Nat.card F = c := by
    letI : Fintype F := Fintype.ofFinite F
    rw [← Fintype.card_eq_nat_card]
    exact FiniteField.pow_card c
  rw [← Polynomial.C_pow, hc]

/-- `X + C c ≠ 0`. -/
lemma poly_X_add_C_ne_zero (c : F) : (X + C c : F[X]) ≠ 0 := by
  intro h
  have h2 : (X + C c : F[X]).natDegree = 1 := Polynomial.natDegree_X_add_C c
  rw [h, Polynomial.natDegree_zero] at h2
  exact one_ne_zero h2.symm

/-- ★ For each `c`, `Q_c ^ q + Q_c ^ (q-1) = [1] ^ (q-1)`. -/
lemma qPoly_pow_add (c : F) :
    (qPoly F c) ^ (Nat.card F) + (qPoly F c) ^ (Nat.card F - 1) =
      (carlitzOne F) ^ (Nat.card F - 1) := by
  classical
  have hq : 2 ≤ Nat.card F := card_ge_two F
  have hqpos : 0 < Nat.card F := by omega
  set y : F[X] := X + C c with hydef
  have hyne : y ≠ 0 := by rw [hydef]; exact poly_X_add_C_ne_zero F c
  have hy : y * qPoly F c = carlitzOne F := by
    rw [hydef]
    exact (carlitzOne_eq_mul_qPoly F c).symm
  have hyq : y ^ Nat.card F = y + carlitzOne F := by
    rw [hydef, poly_X_add_C_pow_card F, carlitzOne]
    ring
  have hpowy : y ^ Nat.card F = y ^ (Nat.card F - 1) * y := by
    conv_lhs => rw [← Nat.succ_pred_eq_of_pos hqpos]
    rw [pow_succ, Nat.pred_eq_sub_one]
  have h1 : qPoly F c + 1 = y ^ (Nat.card F - 1) := by
    apply mul_left_cancel₀ hyne
    rw [mul_add, mul_one, hy, add_comm, ← hyq, hpowy, mul_comm]
  have hpowq : (qPoly F c) ^ Nat.card F = (qPoly F c) ^ (Nat.card F - 1) * qPoly F c := by
    conv_lhs => rw [← Nat.succ_pred_eq_of_pos hqpos]
    rw [pow_succ, Nat.pred_eq_sub_one]
  calc (qPoly F c) ^ Nat.card F + (qPoly F c) ^ (Nat.card F - 1)
      = (qPoly F c) ^ (Nat.card F - 1) * (qPoly F c + 1) := by rw [hpowq, mul_add, mul_one]
    _ = (qPoly F c) ^ (Nat.card F - 1) * y ^ (Nat.card F - 1) := by rw [h1]
    _ = (carlitzOne F) ^ (Nat.card F - 1) := by
        rw [← mul_pow]
        congr 1
        rw [mul_comm]
        exact hy

/-- ★ `A_n + A_{n-1} = [1]^(q-1) * A_{n-q}` for `n ≥ q` (Carlitz's recursion, first form). -/
lemma A_recursion (n : ℕ) (hn : Nat.card F ≤ n) :
    A F n + A F (n - 1) =
      (carlitzOne F) ^ (Nat.card F - 1) * A F (n - Nat.card F) := by
  classical
  letI : Fintype F := Fintype.ofFinite F
  have hq2 : 2 ≤ Nat.card F := card_ge_two F
  have key : ∀ c : F, (qPoly F c) ^ n + (qPoly F c) ^ (n - 1) =
      (carlitzOne F) ^ (Nat.card F - 1) * (qPoly F c) ^ (n - Nat.card F) := by
    intro c
    have h2 : (Nat.card F - 1) + (n - Nat.card F) = n - 1 := by omega
    have h := qPoly_pow_add F c
    have h' := congrArg (fun z : F[X] => z * (qPoly F c) ^ (n - Nat.card F)) h
    rw [add_mul] at h'
    rw [← pow_add, ← pow_add] at h'
    rw [Nat.add_sub_cancel' hn, h2] at h'
    exact h'
  have hA : ∀ m : ℕ, (A F m : F[X]) = ∑ c : F, (qPoly F c) ^ m := fun m => rfl
  rw [hA n, hA (n - 1), hA (n - Nat.card F), Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl (fun c _ => key c)

/-- The composite `F[X] → F(X) → F((1/t))`. -/
noncomputable def polyToK : F[X] →+* RatFunc.CompletionAtInfty F :=
  (toK F).comp (algebraMap F[X] (RatFunc F))

lemma polyToK_apply (p : F[X]) :
    polyToK F p = (((p : F[X]) : RatFunc F) : RatFunc.CompletionAtInfty F) := rfl

/-- A nonzero polynomial does not vanish in the completion. -/
lemma polyToK_ne_zero {p : F[X]} (hp : p ≠ 0) : polyToK F p ≠ 0 := by
  change (((p : F[X]) : RatFunc F) : RatFunc.CompletionAtInfty F) ≠ 0
  intro h
  have hv := inftyValued_v_polynomial F p hp
  rw [h, map_zero] at hv
  exact WithZero.exp_ne_zero hv.symm

/-- The composite `F[X] → F((1/t))` is injective. -/
lemma polyToK_injective : Function.Injective (polyToK F) := by
  intro p r hpr
  have h : polyToK F (p - r) = 0 := by rw [map_sub, hpr, sub_self]
  by_contra hne
  exact polyToK_ne_zero F (sub_ne_zero.mpr hne) h

/-- ★ `A_n` in `K∞ = F((1/t))` is `[1]^n · P_1(n)` (Thakur's power-sum form). -/
lemma polyToK_A_eq (n : ℕ) (hn : 1 ≤ n) :
    polyToK F (A F n) =
      (polyToK F (carlitzOne F)) ^ n * P F 1 ⟨n, hn⟩ := by
  classical
  letI : Fintype F := Fintype.ofFinite F
  show toK F (algebraMap F[X] (RatFunc F) (A F n)) = _
  rw [A_RatFunc_eq F n, map_mul, map_pow, P_one_eq_coe_P1rat F ⟨n, hn⟩]
  rfl

/-- ★ `A_n = (-1)^n` for `1 ≤ n ≤ q` (the easy range, via Thakur–Chen purity). -/
lemma A_eq_neg_one_pow (n : ℕ) (hn1 : 1 ≤ n) (hnq : n ≤ Nat.card F) :
    A F n = (-1 : F[X]) ^ n := by
  classical
  letI : Fintype F := Fintype.ofFinite F
  have hP : P F 1 ⟨n, hn1⟩ = (P F 1 ⟨1, le_refl 1⟩) ^ n := P_eq_pow_of_le_card F 1 ⟨n, hn1⟩ hnq
  have hone : polyToK F (carlitzOne F) * P F 1 ⟨1, le_refl 1⟩
      = polyToK F ((-1 : F[X])) := by
    have h1 := polyToK_A_eq F 1 le_rfl
    rw [pow_one] at h1
    rw [show A F 1 = (-1 : F[X]) from A_one_eq_neg_one F] at h1
    exact h1.symm
  refine polyToK_injective F ?_
  rw [map_pow, polyToK_A_eq F n hn1, hP, ← mul_pow, hone]

/-- The Thakur polynomial sequence evaluated at `[1]^(q-1)`, organised as the candidate
formula for `A_n`: `thakurB n := (-1)^n * ∑_{m ≤ n} (-1)^m C(n-1-m(q-1), m) [1]^{m(q-1)}`. -/
noncomputable def thakurB (n : ℕ) : F[X] :=
  (-1 : F[X]) ^ n *
    ∑ m ∈ Finset.range (n + 1),
      (-1 : F[X]) ^ m *
        Polynomial.C ((Nat.choose ((n - 1) - m * (Nat.card F - 1)) m : ℕ) : F) *
          ((carlitzOne F) ^ (Nat.card F - 1)) ^ m

/-- `thakurB n = (-1)^n` in the easy range `1 ≤ n ≤ q`. -/
lemma thakurB_eq_neg_one_pow (n : ℕ) (hn1 : 1 ≤ n) (hnq : n ≤ Nat.card F) :
    thakurB F n = (-1 : F[X]) ^ n := by
  classical
  have hq : 2 ≤ Nat.card F := card_ge_two F
  have hsum : (∑ m ∈ Finset.range (n + 1),
      (-1 : F[X]) ^ m *
        Polynomial.C ((Nat.choose ((n - 1) - m * (Nat.card F - 1)) m : ℕ) : F) *
          ((carlitzOne F) ^ (Nat.card F - 1)) ^ m) = 1 := by
    rw [Finset.sum_eq_single 0]
    · simp
    · intro m hm hm0
      have hm1 : 1 ≤ m := Nat.one_le_iff_ne_zero.mpr hm0
      have hlt : (n - 1) - m * (Nat.card F - 1) < m := by
        have hkey : m * Nat.card F = m * (Nat.card F - 1) + m := by
          have h1 : Nat.card F - 1 + 1 = Nat.card F := by omega
          conv_lhs => rw [← h1]
          ring
        have hlt' : n - 1 < m * (Nat.card F - 1) + m := by
          rw [← hkey]
          have hA : n - 1 < Nat.card F := by omega
          have hB : Nat.card F ≤ m * Nat.card F := by
            have h2 := mul_le_mul_right hm1 (Nat.card F)
            simpa using h2
          omega
        by_cases h : m * (Nat.card F - 1) ≤ n - 1
        · omega
        · rw [Nat.sub_eq_zero_of_le (le_of_lt (not_le.mp h))]
          exact hm1
      rw [Nat.choose_eq_zero_of_lt hlt]
      simp
    · intro hmem
      exact absurd (Finset.mem_range.mpr (by omega)) hmem
  rw [thakurB, hsum, mul_one]

/-- The recursion for `thakurB` (proved from the commons binomial recursion
`Commons.Combinatorics.ThakurPoly.thakurPoly_rec`; stated here as an auxiliary hypothesis-free
form to keep the induction below independent of it). -/
lemma A_eq_thakurB_of_rec
    (hrec : ∀ n : ℕ, Nat.card F + 1 ≤ n →
      thakurB F n + thakurB F (n - 1)
        = (carlitzOne F) ^ (Nat.card F - 1) * thakurB F (n - Nat.card F)) :
    ∀ n : ℕ, 1 ≤ n → A F n = thakurB F n := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hn1
    rcases le_or_gt n (Nat.card F) with hnq | hnq
    · rw [A_eq_neg_one_pow F n hn1 hnq, thakurB_eq_neg_one_pow F n hn1 hnq]
    · have hq : 2 ≤ Nat.card F := card_ge_two F
      have hge : Nat.card F + 1 ≤ n := by omega
      have hA := A_recursion F n (by omega)
      have hB := hrec n hge
      have h1 : A F (n - 1) = thakurB F (n - 1) := ih (n - 1) (by omega) (by omega)
      have h2 : A F (n - Nat.card F) = thakurB F (n - Nat.card F) :=
        ih (n - Nat.card F) (by omega) (by omega)
      rw [h1, h2] at hA
      have hAn : A F n = (carlitzOne F) ^ (Nat.card F - 1) * thakurB F (n - Nat.card F)
          - thakurB F (n - 1) := eq_sub_of_add_eq hA
      have hBn : thakurB F n = (carlitzOne F) ^ (Nat.card F - 1) * thakurB F (n - Nat.card F)
          - thakurB F (n - 1) := eq_sub_of_add_eq hB
      rw [hAn, hBn]

/-- The inner sum of the Thakur polynomial at `T = [1]^(q-1)` (the sequence `b_n`). -/
noncomputable def thakurSum (k : ℕ) : F[X] :=
  ∑ m ∈ Finset.range (k + 1),
    (-1 : F[X]) ^ m *
      Polynomial.C ((Nat.choose ((k - 1) - m * (Nat.card F - 1)) m : ℕ) : F) *
        ((carlitzOne F) ^ (Nat.card F - 1)) ^ m

lemma thakurB_eq (k : ℕ) : thakurB F k = (-1 : F[X]) ^ k * thakurSum F k := rfl

/-- `thakurSum (n-1)` is the sum over `range n`. -/
lemma thakurSum_pred_eq (n : ℕ) (hn : 1 ≤ n) :
    thakurSum F (n - 1) =
      ∑ m ∈ Finset.range n,
        (-1 : F[X]) ^ m *
          Polynomial.C ((Nat.choose ((n - 2) - m * (Nat.card F - 1)) m : ℕ) : F) *
            ((carlitzOne F) ^ (Nat.card F - 1)) ^ m := by
  rw [thakurSum, Nat.sub_add_cancel hn]
  apply Finset.sum_congr rfl
  intro m _
  rw [show (n - 1) - 1 - m * (Nat.card F - 1) = (n - 2) - m * (Nat.card F - 1) by omega]

/-- `(-1)^(2q) = 1` in `F[X]`. -/
lemma neg_one_pow_two_mul_card : (-1 : F[X]) ^ (2 * Nat.card F) = 1 := by
  rw [pow_mul]
  norm_num

/-- In `F[X]` either `2 = 0` (characteristic two) or `q = |F|` is odd. -/
lemma two_eq_zero_or_odd_card : (2 : F[X]) = 0 ∨ Odd (Nat.card F) := by
  obtain ⟨n, hprime, hcard⟩ := card_eq_ringChar_pow F
  by_cases h : ringChar F = 2
  · left
    haveI : CharP F (ringChar F) := inferInstance
    haveI : CharP F[X] (ringChar F) := inferInstance
    rw [h] at this
    exact CharP.cast_eq_zero F[X] 2
  · right
    rw [hcard]
    exact (hprime.odd_of_ne_two h).pow

/-- `thakurSum (n - q)` is the sum over `range (n + 1 - q)`. -/
lemma thakurSum_sub_eq (n : ℕ) (hn : Nat.card F ≤ n) :
    thakurSum F (n - Nat.card F) =
      ∑ m ∈ Finset.range (n + 1 - Nat.card F),
        (-1 : F[X]) ^ m *
          Polynomial.C ((Nat.choose (n - Nat.card F - 1 - m * (Nat.card F - 1)) m : ℕ) : F) *
            ((carlitzOne F) ^ (Nat.card F - 1)) ^ m := by
  rw [thakurSum, show n - Nat.card F + 1 = n + 1 - Nat.card F by omega]

/-- The recursion for `thakurSum` (from the commons Thakur–Pascal recursion). -/
lemma thakurSum_rec (n : ℕ) (hn : Nat.card F + 1 ≤ n) :
    thakurSum F n = thakurSum F (n - 1)
      + (-1 : F[X]) ^ Nat.card F * ((carlitzOne F) ^ (Nat.card F - 1))
        * thakurSum F (n - Nat.card F) := by
  have hn1 : 1 ≤ n := by omega
  have hnq : Nat.card F ≤ n := by omega
  rw [thakurSum_pred_eq F n hn1, thakurSum_sub_eq F n hnq]
  exact Commons.Combinatorics.ThakurPoly.thakurPoly_rec (R := F[X]) (Nat.card F)
    (card_ge_two F) (two_eq_zero_or_odd_card F) ((carlitzOne F) ^ (Nat.card F - 1)) n hn

/-- ★ The recursion for `thakurB`: `thakurB n + thakurB (n-1) = [1]^(q-1) * thakurB (n-q)`. -/
lemma thakurB_rec (n : ℕ) (hn : Nat.card F + 1 ≤ n) :
    thakurB F n + thakurB F (n - 1)
      = (carlitzOne F) ^ (Nat.card F - 1) * thakurB F (n - Nat.card F) := by
  have hn1 : 1 ≤ n := by omega
  have hnq : Nat.card F ≤ n := by omega
  have hq : 2 ≤ Nat.card F := card_ge_two F
  have hrec := thakurSum_rec F n hn
  have hd : thakurSum F n - thakurSum F (n - 1)
      = (-1 : F[X]) ^ Nat.card F * ((carlitzOne F) ^ (Nat.card F - 1))
        * thakurSum F (n - Nat.card F) := by
    rw [hrec]; ring
  have hs : (-1 : F[X]) ^ (n - 1) = -(-1 : F[X]) ^ n := by
    have hp : (-1 : F[X]) ^ n = (-1 : F[X]) ^ (n - 1) * (-1) := by
      conv_lhs => rw [← Nat.succ_pred_eq_of_pos (by omega : 0 < n)]
      rw [pow_succ, Nat.pred_eq_sub_one]
    rw [hp]; ring
  have hsign : (-1 : F[X]) ^ (n + Nat.card F) = (-1 : F[X]) ^ (n - Nat.card F) := by
    have h2 : n - Nat.card F + 2 * Nat.card F = n + Nat.card F := by omega
    rw [← h2, pow_add, neg_one_pow_two_mul_card F, mul_one]
  rw [thakurB_eq F n, thakurB_eq F (n - 1), thakurB_eq F (n - Nat.card F)]
  have hgoal : (-1 : F[X]) ^ n * thakurSum F n + (-1 : F[X]) ^ (n - 1) * thakurSum F (n - 1)
      = (-1 : F[X]) ^ n * (thakurSum F n - thakurSum F (n - 1)) := by
    rw [hs]; ring
  rw [hgoal, hd]
  rw [← mul_assoc, ← mul_assoc, ← pow_add, hsign]
  ring

/-- ★★★ **Carlitz's expansion for the level-one power-sum polynomials** (Thakur 2009, §2.3):
for `n ≥ 1`,
`A_n = (-1)^n ∑_{m ≤ n} (-1)^m C(n-1-m(q-1), m) [1]^{m(q-1)}`. -/
theorem A_thakur_formula (n : ℕ) (hn : 1 ≤ n) : A F n = thakurB F n :=
  A_eq_thakurB_of_rec F (fun m hm => thakurB_rec F m hm) n hn

/-- The formula unfolded (the form found in the literature). -/
theorem A_thakur_formula' (n : ℕ) (hn : 1 ≤ n) :
    A F n = (-1 : F[X]) ^ n *
      ∑ m ∈ Finset.range (n + 1),
        (-1 : F[X]) ^ m *
          Polynomial.C ((Nat.choose ((n - 1) - m * (Nat.card F - 1)) m : ℕ) : F) *
            ((carlitzOne F) ^ (Nat.card F - 1)) ^ m :=
  A_thakur_formula F n hn

end ZagierHoffmanPositiveChar
