import Mathlib
import Submission.Work.HP.NA.Setup
import Submission.Work.HP.density_aux
import Submission.Work.HP.lift.line_setup

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# `Work.HP.NA.sigQ_lower_Rset`

Lower bound `σ(a;p^r) ≥ p^{-(e+1)n}` for `a ∈ R^{(e)}(p^r)`, following the proof of the
"Lemma lower bound sigma" of Browning–Le Boudec–Sawin.
-/

noncomputable section
set_option autoImplicit false

namespace Work.HP.NA
open Work.HP

/-! ## Cast compatibility of `fev`/`dfev` with `formEval`/`pderivEval` -/

lemma fev_intCast (d n N : ℕ) (A : Mon d n → ℤ) (X : Fin (n + 1) → ℤ) :
    fev d n (fun m => ((A m : ℤ) : ZMod N)) (fun i => ((X i : ℤ) : ZMod N))
      = ((formEval d n A X : ℤ) : ZMod N) := by
  rw [fev, formEval]
  simp [veronese]

lemma dfev_intCast (d n N : ℕ) (A : Mon d n → ℤ) (X : Fin (n + 1) → ℤ) (j : Fin (n + 1)) :
    dfev d n (fun m => ((A m : ℤ) : ZMod N)) (fun i => ((X i : ℤ) : ZMod N)) j
      = ((pderivEval d n A j X : ℤ) : ZMod N) := by
  rw [dfev, pderivEval]
  simp only [Int.cast_sum, Int.cast_mul, Int.cast_prod, Int.cast_pow, Int.cast_natCast]
  apply Finset.sum_congr rfl
  intro m _
  have hprod : ∏ i, ((X i : ℤ) : ZMod N) ^ (if i = j then (m.1 i : ℕ) - 1 else (m.1 i : ℕ))
      = ∏ i, ((X i : ℤ) : ZMod N) ^ ((m.1 i : ℕ) - if i = j then 1 else 0) := by
    apply Finset.prod_congr rfl
    intro i _
    by_cases h : i = j
    · simp [h]
    · simp [h]
  rw [hprod]

/-! ## One-variable second-order Taylor congruence -/

/-- `(Z+t)^k - Z^k - t·k·Z^{k-1}` is divisible by `t²`. -/
lemma sq_dvd_pow_sub (Z t : ℤ) (k : ℕ) :
    ∃ c : ℤ, (Z + t) ^ k - Z ^ k - t * ((k : ℤ) * Z ^ (k - 1)) = c * t ^ 2 := by
  have h := Work.HP.lift.sq_dvd_eval_sub_eval_sub_mul_derivative
      ((Polynomial.X + Polynomial.C Z) ^ k) 0 t
  have h1 : Polynomial.eval t ((Polynomial.X + Polynomial.C Z) ^ k : Polynomial ℤ) = (Z + t) ^ k := by
    simp only [Polynomial.eval_pow, Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C]
    ring
  have h2 : Polynomial.eval 0 ((Polynomial.X + Polynomial.C Z) ^ k : Polynomial ℤ) = Z ^ k := by
    simp only [Polynomial.eval_pow, Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C,
      zero_add]
  have h3 : Polynomial.eval 0 (Polynomial.derivative
        ((Polynomial.X + Polynomial.C Z) ^ k : Polynomial ℤ)) = (k : ℤ) * Z ^ (k - 1) := by
    rw [Polynomial.derivative_X_add_C_pow]
    simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow,
      Polynomial.eval_add, Polynomial.eval_X, zero_add]
  rw [zero_add, h1, h2, h3] at h
  obtain ⟨c, hc⟩ := h
  exact ⟨c, by rw [hc, mul_comm]⟩

/-! ## Product-difference lemmas -/

/-- First-order product difference: `∏(X_i+H_i)^{k_i} - ∏X_i^{k_i}` is a `ℤ`-linear
combination of the `H_i`. -/
lemma prod_diff_mem {ι : Type*} [DecidableEq ι] (s : Finset ι) (X H : ι → ℤ) (k : ι → ℕ) :
    ∃ c : ι → ℤ, ∏ i ∈ s, (X i + H i) ^ (k i) - ∏ i ∈ s, X i ^ (k i) = ∑ i ∈ s, c i * H i := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨fun _ => 0, by simp⟩
  | insert i s hi ih =>
      obtain ⟨c, hc⟩ := ih
      obtain ⟨e, he⟩ := sub_dvd_pow_sub_pow (X i + H i) (X i) (k i)
      rw [show (X i + H i) - X i = H i from by ring] at he
      have hkey : (X i + H i) ^ (k i) = X i ^ (k i) + H i * e := by linarith [he]
      have hmem : ∀ l ∈ s, l ≠ i := fun l hl hli => hi (hli ▸ hl)
      refine ⟨fun l => if l = i then e * (∏ l ∈ s, (X l + H l) ^ (k l)) else X i ^ (k i) * c l, ?_⟩
      rw [Finset.prod_insert hi, Finset.prod_insert hi, Finset.sum_insert hi]
      simp only [if_pos rfl, ite_true]
      have hsplit : ∑ x ∈ s,
            (if x = i then e * ∏ l ∈ s, (X l + H l) ^ (k l) else X i ^ (k i) * c x) * H x
          = X i ^ (k i) * ∑ x ∈ s, c x * H x := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro x hx
        rw [if_neg (hmem x hx)]
        ring
      rw [hsplit, ← hc, hkey]
      ring

/-- Second-order product difference: the remainder of the first-order Taylor formula is a
combination of pairwise products `H_i·H_j`. -/
lemma prod_diff_taylor2 {ι : Type*} [DecidableEq ι] (s : Finset ι) (X H : ι → ℤ) (k : ι → ℕ) :
    ∃ C : ι → ι → ℤ,
      ∏ i ∈ s, (X i + H i) ^ (k i) - ∏ i ∈ s, X i ^ (k i)
        - ∑ i ∈ s, H i * ((k i : ℤ) * ∏ l ∈ s, X l ^ (k l - (if l = i then 1 else 0)))
      = ∑ i ∈ s, ∑ j ∈ s, C i j * (H i * H j) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨fun _ _ => 0, by simp⟩
  | insert i0 s hi ih =>
      obtain ⟨C, hC⟩ := ih
      obtain ⟨d, hd⟩ := prod_diff_mem s X H k
      obtain ⟨c2, hc2⟩ := sq_dvd_pow_sub (X i0) (H i0) (k i0)
      have hmem : ∀ l ∈ s, l ≠ i0 := fun l hl hli => hi (hli ▸ hl)
      set P : ℤ := ∏ l ∈ s, (X l + H l) ^ (k l) with hP
      set Q : ℤ := ∏ l ∈ s, X l ^ (k l) with hQ
      set T : ℤ := ∑ l ∈ s, H l * ((k l : ℤ) * ∏ m ∈ s, X m ^ (k m - (if m = l then 1 else 0)))
        with hT
      have hPQt : P - Q - T = ∑ l ∈ s, ∑ m ∈ s, C l m * (H l * H m) := by rw [hP, hQ, hT]; exact hC
      have hPQ : P - Q = ∑ l ∈ s, d l * H l := by rw [hP, hQ]; exact hd
      refine ⟨fun a b => if a = i0 then (if b = i0 then c2 * P
              else (k i0 : ℤ) * X i0 ^ (k i0 - 1) * d b)
            else (if b = i0 then 0 else X i0 ^ (k i0) * C a b), ?_⟩
      have hUi : (X i0 + H i0) ^ (k i0)
          = X i0 ^ (k i0) + H i0 * ((k i0 : ℤ) * X i0 ^ (k i0 - 1)) + c2 * (H i0 * H i0) := by
        linarith [hc2]
      have hprod0 : ∏ m ∈ insert i0 s, X m ^ (k m - (if m = i0 then 1 else 0))
          = X i0 ^ (k i0 - 1) * Q := by
        rw [hQ, Finset.prod_insert hi, if_pos rfl]
        congr 1
        apply Finset.prod_congr rfl
        intro m hm
        rw [if_neg (hmem m hm), Nat.sub_zero]
      have hprod1 : ∀ l ∈ s, ∏ m ∈ insert i0 s, X m ^ (k m - (if m = l then 1 else 0))
          = X i0 ^ (k i0) * ∏ m ∈ s, X m ^ (k m - (if m = l then 1 else 0)) := by
        intro l hl
        rw [Finset.prod_insert hi, if_neg (hmem l hl).symm, Nat.sub_zero]
      rw [Finset.prod_insert hi, Finset.prod_insert hi]
      have hsum : ∑ l ∈ insert i0 s,
            H l * ((k l : ℤ) * ∏ m ∈ insert i0 s, X m ^ (k m - (if m = l then 1 else 0)))
          = H i0 * ((k i0 : ℤ) * X i0 ^ (k i0 - 1)) * Q
            + X i0 ^ (k i0) * T := by
        rw [Finset.sum_insert hi, hprod0, hT]
        have hstep : ∀ l ∈ s, H l * ((k l : ℤ) * ∏ m ∈ insert i0 s, X m ^ (k m - (if m = l then 1 else 0)))
            = X i0 ^ (k i0) * (H l * ((k l : ℤ) * ∏ m ∈ s, X m ^ (k m - (if m = l then 1 else 0)))) := by
          intro l hl
          rw [hprod1 l hl]
          ring
        rw [Finset.sum_congr rfl hstep, Finset.mul_sum]
        congr 1
        ring
      rw [hsum, hUi]
      have hmain : (X i0 ^ (k i0) + H i0 * ((k i0 : ℤ) * X i0 ^ (k i0 - 1)) + c2 * (H i0 * H i0))
              * P - X i0 ^ (k i0) * Q
            - (H i0 * ((k i0 : ℤ) * X i0 ^ (k i0 - 1)) * Q + X i0 ^ (k i0) * T)
          = X i0 ^ (k i0) * (P - Q - T)
            + (H i0 * ((k i0 : ℤ) * X i0 ^ (k i0 - 1))) * (P - Q)
            + (c2 * (H i0 * H i0)) * P := by ring
      rw [hmain, hPQt, hPQ]
      have hdouble : ∑ a ∈ insert i0 s, ∑ b ∈ insert i0 s,
            (if a = i0 then (if b = i0 then c2 * P
                else (k i0 : ℤ) * X i0 ^ (k i0 - 1) * d b)
             else (if b = i0 then 0 else X i0 ^ (k i0) * C a b)) * (H a * H b)
          = c2 * P * (H i0 * H i0)
            + ∑ b ∈ s, ((k i0 : ℤ) * X i0 ^ (k i0 - 1) * d b) * (H i0 * H b)
            + ∑ a ∈ s, ∑ b ∈ s, (X i0 ^ (k i0) * C a b) * (H a * H b) := by
        rw [Finset.sum_insert hi]
        have hterm1 : ∀ b, (if i0 = i0 then (if b = i0 then c2 * P
                else (k i0 : ℤ) * X i0 ^ (k i0 - 1) * d b)
              else (if b = i0 then 0 else X i0 ^ (k i0) * C i0 b)) * (H i0 * H b)
            = (if b = i0 then c2 * P else (k i0 : ℤ) * X i0 ^ (k i0 - 1) * d b) * (H i0 * H b) := by
          intro b; rw [if_pos rfl]
        have hsplit1 : ∑ b ∈ insert i0 s,
              (if b = i0 then c2 * P else (k i0 : ℤ) * X i0 ^ (k i0 - 1) * d b) * (H i0 * H b)
            = c2 * P * (H i0 * H i0)
              + ∑ b ∈ s, ((k i0 : ℤ) * X i0 ^ (k i0 - 1) * d b) * (H i0 * H b) := by
          have hS : ∑ b ∈ s,
                (if b = i0 then c2 * P else (k i0 : ℤ) * X i0 ^ (k i0 - 1) * d b) * (H i0 * H b)
              = ∑ b ∈ s, ((k i0 : ℤ) * X i0 ^ (k i0 - 1) * d b) * (H i0 * H b) := by
            apply Finset.sum_congr rfl
            intro b hb
            rw [if_neg (hmem b hb)]
          rw [Finset.sum_insert hi, if_pos rfl, hS]
        have hCC : ∀ a ∈ s, ∑ b ∈ insert i0 s,
              (if a = i0 then (if b = i0 then c2 * P
                  else (k i0 : ℤ) * X i0 ^ (k i0 - 1) * d b)
                else (if b = i0 then 0 else X i0 ^ (k i0) * C a b)) * (H a * H b)
            = ∑ b ∈ s, (X i0 ^ (k i0) * C a b) * (H a * H b) := by
          intro a ha
          have hstep : ∀ b, (if a = i0 then (if b = i0 then c2 * P
                  else (k i0 : ℤ) * X i0 ^ (k i0 - 1) * d b)
                else (if b = i0 then 0 else X i0 ^ (k i0) * C a b)) * (H a * H b)
              = (if b = i0 then 0 else X i0 ^ (k i0) * C a b) * (H a * H b) := by
            intro b; rw [if_neg (hmem a ha)]
          rw [Finset.sum_congr rfl (fun b _ => hstep b)]
          rw [Finset.sum_insert hi, if_pos rfl, zero_mul, zero_add]
          apply Finset.sum_congr rfl
          intro b hb
          rw [if_neg (hmem b hb)]
        rw [Finset.sum_congr rfl (fun b _ => hterm1 b), hsplit1,
          Finset.sum_congr rfl hCC]

      rw [hdouble]
      have hfin : c2 * P * (H i0 * H i0)
            + ∑ b ∈ s, ((k i0 : ℤ) * X i0 ^ (k i0 - 1) * d b) * (H i0 * H b)
            + ∑ a ∈ s, ∑ b ∈ s, (X i0 ^ (k i0) * C a b) * (H a * H b)
          = X i0 ^ (k i0) * (∑ a ∈ s, ∑ b ∈ s, C a b * (H a * H b))
            + (H i0 * ((k i0 : ℤ) * X i0 ^ (k i0 - 1))) * (∑ b ∈ s, d b * H b)
            + (c2 * (H i0 * H i0)) * P := by
        have hA : ∑ a ∈ s, ∑ b ∈ s, (X i0 ^ (k i0) * C a b) * (H a * H b)
            = X i0 ^ (k i0) * (∑ a ∈ s, ∑ b ∈ s, C a b * (H a * H b)) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro a _
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro b _
          ring
        have hB : ∑ b ∈ s, ((k i0 : ℤ) * X i0 ^ (k i0 - 1) * d b) * (H i0 * H b)
            = (H i0 * ((k i0 : ℤ) * X i0 ^ (k i0 - 1))) * (∑ b ∈ s, d b * H b) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro b _
          ring
        rw [hA, hB]
        ring
      rw [hfin]


/-! ## The Taylor congruence for `formEval` -/

/-- Unfolding of `formEval` over `ℤ` (no coercion remains). -/
lemma formEval_eq_sum (d n : ℕ) (A : Mon d n → ℤ) (x : Fin (n + 1) → ℤ) :
    formEval d n A x = ∑ m, A m * veronese d n x m := by
  rw [formEval]
  apply Finset.sum_congr rfl
  intro m _
  simp

/-- Second-order Taylor expansion of `f_A`: the remainder after the first-order part is a
combination of products of the shift coordinates. -/
lemma formEval_taylor2_rem (d n : ℕ) (A : Mon d n → ℤ) (X H : Fin (n + 1) → ℤ) :
    ∃ D : Fin (n + 1) → Fin (n + 1) → ℤ,
      formEval d n A (X + H) - formEval d n A X - ∑ i, H i * pderivEval d n A i X
        = ∑ i, ∑ l, D i l * (H i * H l) := by
  classical
  have hper : ∀ m : Mon d n, ∃ Cm : Fin (n + 1) → Fin (n + 1) → ℤ,
      (∏ i, (X i + H i) ^ (m.1 i : ℕ)) - (∏ i, X i ^ (m.1 i : ℕ))
        - ∑ i, H i * ((m.1 i : ℤ) * ∏ l, X l ^ ((m.1 l : ℕ) - (if l = i then 1 else 0)))
      = ∑ i, ∑ l, Cm i l * (H i * H l) := by
    intro m
    exact prod_diff_taylor2 Finset.univ X H (fun i => (m.1 i : ℕ))
  choose Cm hCm using hper
  have hdiff : formEval d n A (X + H) - formEval d n A X
      = ∑ m, A m * ((∏ i, (X i + H i) ^ (m.1 i : ℕ)) - (∏ i, X i ^ (m.1 i : ℕ))) := by
    rw [formEval_eq_sum, formEval_eq_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro m _
    simp only [veronese, Pi.add_apply]
    ring
  rw [hdiff]
  have hrewrite : ∑ m, A m * ((∏ i, (X i + H i) ^ (m.1 i : ℕ)) - (∏ i, X i ^ (m.1 i : ℕ)))
      = (∑ m, A m * (∑ i, H i * ((m.1 i : ℤ) * ∏ l, X l ^ ((m.1 l : ℕ) - (if l = i then 1 else 0)))))
        + ∑ m, A m * (∑ i, ∑ l, Cm m i l * (H i * H l)) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro m _
    have hm : (∏ i, (X i + H i) ^ (m.1 i : ℕ)) - (∏ i, X i ^ (m.1 i : ℕ))
        = (∑ i, H i * ((m.1 i : ℤ) * ∏ l, X l ^ ((m.1 l : ℕ) - (if l = i then 1 else 0))))
          + ∑ i, ∑ l, Cm m i l * (H i * H l) := by linarith [hCm m]
    rw [hm]
    ring
  rw [hrewrite]
  have hlin : ∑ m, A m * (∑ i, H i * ((m.1 i : ℤ) * ∏ l, X l ^ ((m.1 l : ℕ) - (if l = i then 1 else 0))))
      = ∑ i, H i * pderivEval d n A i X := by
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    rw [pderivEval, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro m _
    ring
  rw [hlin]
  have hquad : ∑ m, A m * (∑ i, ∑ l, Cm m i l * (H i * H l))
      = ∑ i, ∑ l, (∑ m, A m * Cm m i l) * (H i * H l) := by
    have h1 : ∑ m, A m * (∑ i, ∑ l, Cm m i l * (H i * H l))
        = ∑ i, ∑ l, ∑ m, A m * (Cm m i l * (H i * H l)) := by
      simp only [Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.sum_comm]
    rw [h1]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro l _
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro m _
    ring
  rw [hquad]
  refine ⟨fun i l => ∑ m, A m * Cm m i l, ?_⟩
  rw [add_sub_cancel_left]

/-- Second-order Taylor congruence: perturbing `X` by `H` inside `p^{e+1}ℤ^{n+1}` changes
`formEval` by a multiple of `p^{2e+1}`, provided the gradient at `X` is `p^e`-divisible. -/
theorem formEval_taylor2 (d n e p : ℕ) (A : Mon d n → ℤ) (X H : Fin (n + 1) → ℤ)
    (hH : ∀ i, (p : ℤ) ^ (e + 1) ∣ H i) (hD : ∀ i, (p : ℤ) ^ e ∣ pderivEval d n A i X) :
    (p : ℤ) ^ (2 * e + 1) ∣ formEval d n A (X + H) - formEval d n A X := by
  obtain ⟨D, hD'⟩ := formEval_taylor2_rem d n A X H
  have h1 : (p : ℤ) ^ (2 * e + 1) ∣ ∑ i, H i * pderivEval d n A i X := by
    apply Finset.dvd_sum
    intro i _
    obtain ⟨a, ha⟩ := hH i
    obtain ⟨b, hb⟩ := hD i
    refine ⟨a * b, ?_⟩
    rw [hb, ha]
    have hexp : (p : ℤ) ^ (e + 1) * (p : ℤ) ^ e = (p : ℤ) ^ (2 * e + 1) := by
      rw [← pow_add]
      congr 1
      omega
    rw [show (p : ℤ) ^ (e + 1) * a * ((p : ℤ) ^ e * b)
        = ((p : ℤ) ^ (e + 1) * (p : ℤ) ^ e) * (a * b) from by ring, hexp]
  have h2 : (p : ℤ) ^ (2 * e + 1) ∣ ∑ i, ∑ l, D i l * (H i * H l) := by
    apply Finset.dvd_sum
    intro i _
    apply Finset.dvd_sum
    intro l _
    obtain ⟨a, ha⟩ := hH i
    obtain ⟨b, hb⟩ := hH l
    refine ⟨D i l * (a * b) * (p : ℤ), ?_⟩
    rw [ha, hb]
    have hexp : (p : ℤ) ^ (e + 1) * (p : ℤ) ^ (e + 1)
        = (p : ℤ) ^ (2 * e + 1) * (p : ℤ) := by
      rw [← pow_add, ← pow_succ]
      congr 1
      omega
    rw [show (p : ℤ) ^ (e + 1) * a * ((p : ℤ) ^ (e + 1) * b)
        = ((p : ℤ) ^ (e + 1) * (p : ℤ) ^ (e + 1)) * (a * b) from by ring, hexp]
    ring
  have hsum := dvd_add h1 h2
  have heq : formEval d n A (X + H) - formEval d n A X
      = (∑ i, H i * pderivEval d n A i X) + ∑ i, ∑ l, D i l * (H i * H l) := by
    linarith [hD']
  rw [heq]
  exact hsum

/-- First-order (Lipschitz) congruence for the gradient: perturbing `X` by `H` inside
`p^{e+1}ℤ^{n+1}` changes each `pderivEval` by a multiple of `p^{e+1}`. -/
theorem pderivEval_lipschitz (d n e p : ℕ) (A : Mon d n → ℤ) (X H : Fin (n + 1) → ℤ)
    (j : Fin (n + 1)) (hH : ∀ i, (p : ℤ) ^ (e + 1) ∣ H i) :
    (p : ℤ) ^ (e + 1) ∣ pderivEval d n A j (X + H) - pderivEval d n A j X := by
  classical
  have key : ∀ m : Mon d n, (p : ℤ) ^ (e + 1) ∣ (A m * (m.1 j : ℤ)) *
      ((∏ i, (X i + H i) ^ ((m.1 i : ℕ) - (if i = j then 1 else 0)))
        - (∏ i, X i ^ ((m.1 i : ℕ) - (if i = j then 1 else 0)))) := by
    intro m
    obtain ⟨c, hc⟩ := prod_diff_mem Finset.univ X H
      (fun i => (m.1 i : ℕ) - (if i = j then 1 else 0))
    rw [hc]
    apply dvd_mul_of_dvd_right
    apply Finset.dvd_sum
    intro i _
    exact dvd_mul_of_dvd_right (hH i) (c i)
  rw [pderivEval, pderivEval, ← Finset.sum_sub_distrib]
  apply Finset.dvd_sum
  intro m _
  rw [← mul_sub]
  exact key m


/-! ## One-coordinate Taylor facts and the Hensel step -/

/-- Lipschitz property of `pderivEval` under a shift in a single coordinate. -/
lemma pderivEval_update_lipschitz (d n : ℕ) (A : Mon d n → ℤ) (Y : Fin (n + 1) → ℤ)
    (j0 : Fin (n + 1)) (h : ℤ) :
    h ∣ pderivEval d n A j0 (Function.update Y j0 (Y j0 + h)) - pderivEval d n A j0 Y := by
  classical
  have hEH : Function.update Y j0 (Y j0 + h) = Y + (fun i => h * (if i = j0 then 1 else 0)) := by
    funext i
    by_cases hi : i = j0 <;> simp [Function.update_apply, hi]
  rw [hEH]
  have key : ∀ m : Mon d n, h ∣ (A m * (m.1 j0 : ℤ)) *
      ((∏ i, (Y i + h * (if i = j0 then 1 else 0)) ^ ((m.1 i : ℕ) - (if i = j0 then 1 else 0)))
        - (∏ i, Y i ^ ((m.1 i : ℕ) - (if i = j0 then 1 else 0)))) := by
    intro m
    obtain ⟨c, hc⟩ := prod_diff_mem Finset.univ Y (fun i => h * (if i = j0 then 1 else 0))
      (fun i => (m.1 i : ℕ) - (if i = j0 then 1 else 0))
    rw [hc]
    apply dvd_mul_of_dvd_right
    apply Finset.dvd_sum
    intro i _
    exact ⟨c i * (if i = j0 then (1 : ℤ) else 0), by ring⟩
  rw [pderivEval, pderivEval, ← Finset.sum_sub_distrib]
  apply Finset.dvd_sum
  intro m _
  rw [← mul_sub]
  exact key m

/-- Second-order Taylor expansion of `formEval` for a shift in a single coordinate. -/
lemma formEval_update_taylor2 (d n : ℕ) (A : Mon d n → ℤ) (Y : Fin (n + 1) → ℤ)
    (j0 : Fin (n + 1)) (h : ℤ) :
    ∃ c : ℤ, formEval d n A (Function.update Y j0 (Y j0 + h)) - formEval d n A Y
        - h * pderivEval d n A j0 Y = c * (h * h) := by
  classical
  obtain ⟨D, hD⟩ := formEval_taylor2_rem d n A Y (fun i => h * (if i = j0 then 1 else 0))
  refine ⟨D j0 j0, ?_⟩
  have hY : Y + (fun i => h * (if i = j0 then 1 else 0)) = Function.update Y j0 (Y j0 + h) := by
    funext i
    by_cases hi : i = j0 <;> simp [Function.update_apply, hi]
  have hsum1 : ∑ i, (h * (if i = j0 then 1 else 0)) * pderivEval d n A i Y
      = h * pderivEval d n A j0 Y := by
    rw [Finset.sum_eq_single j0]
    · simp
    · intro b _ hb
      simp [hb]
    · intro h0
      exact absurd (Finset.mem_univ j0) h0
  have hsum2 : ∑ i, ∑ l, D i l * ((h * (if i = j0 then 1 else 0)) * (h * (if l = j0 then 1 else 0)))
      = D j0 j0 * (h * h) := by
    rw [Finset.sum_eq_single j0]
    · rw [Finset.sum_eq_single j0]
      · simp
      · intro b _ hb
        simp [hb]
      · intro h0
        exact absurd (Finset.mem_univ j0) h0
    · intro a _ ha
      apply Finset.sum_eq_zero
      intro b _
      by_cases hb : b = j0
      · subst hb; simp [ha]
      · simp [hb]
    · intro h0
      exact absurd (Finset.mem_univ j0) h0
  rw [hY, hsum1, hsum2] at hD
  exact hD

/-- Solvability of `s + d·t ≡ 0 (mod p)` when `p ∤ d`. -/
lemma exists_t_mul_add_dvd (p : ℕ) (hp : p.Prime) {s dd : ℤ} (hdd : ¬ (p : ℤ) ∣ dd) :
    ∃ t : ℤ, (p : ℤ) ∣ s + dd * t := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : NeZero p := ⟨hp.ne_zero⟩
  have hdd0 : (dd : ZMod p) ≠ 0 := fun h => hdd ((ZMod.intCast_zmod_eq_zero_iff_dvd dd p).mp h)
  refine ⟨((( -(s : ZMod p) * (dd : ZMod p)⁻¹).val : ℕ) : ℤ), ?_⟩
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
  push_cast
  rw [ZMod.natCast_zmod_val]
  have hc : (dd : ZMod p) * (dd : ZMod p)⁻¹ = 1 := mul_inv_cancel₀ hdd0
  calc (s : ZMod p) + (dd : ZMod p) * (-(s : ZMod p) * (dd : ZMod p)⁻¹)
      = (s : ZMod p) + (-(s : ZMod p)) * ((dd : ZMod p) * (dd : ZMod p)⁻¹) := by ring
    _ = (s : ZMod p) + (-(s : ZMod p)) * 1 := by rw [hc]
    _ = 0 := by ring

/-- One Newton/Hensel step: if `f_A` at a point of the form `update X j0 w` is divisible by
`p^{n0}` with `2e+1 ≤ n0` and its `j0`-derivative is `p^e·dd` with `p ∤ dd`, then one can
move the `j0`-coordinate (by a multiple of `p^{n0-e}`) so as to gain one more power of `p`,
keeping the derivative's valuation equal to `e`. -/
lemma hensel_step (d n : ℕ) (A : Mon d n → ℤ) (X : Fin (n + 1) → ℤ) (j0 : Fin (n + 1))
    (p : ℕ) (hp : p.Prime) (e n0 : ℕ) (hn0 : 2 * e + 1 ≤ n0) (w s dd : ℤ)
    (hW : formEval d n A (Function.update X j0 w) = (p : ℤ) ^ n0 * s)
    (hDp : pderivEval d n A j0 (Function.update X j0 w) = (p : ℤ) ^ e * dd)
    (hdd : ¬ (p : ℤ) ∣ dd) :
    ∃ w' s' dd', (p : ℤ) ^ (n0 - e) ∣ w' - w
      ∧ formEval d n A (Function.update X j0 w') = (p : ℤ) ^ (n0 + 1) * s'
      ∧ pderivEval d n A j0 (Function.update X j0 w') = (p : ℤ) ^ e * dd'
      ∧ ¬ (p : ℤ) ∣ dd' := by
  classical
  obtain ⟨t, ht⟩ := exists_t_mul_add_dvd (s := s) p hp hdd
  obtain ⟨s1, hs1⟩ := ht
  obtain ⟨c, hc⟩ := formEval_update_taylor2 d n A (Function.update X j0 w) j0
    ((p : ℤ) ^ (n0 - e) * t)
  obtain ⟨m0, hm0⟩ := pderivEval_update_lipschitz d n A (Function.update X j0 w) j0
    ((p : ℤ) ^ (n0 - e) * t)
  have hupd : Function.update (Function.update X j0 w) j0
        (Function.update X j0 w j0 + (p : ℤ) ^ (n0 - e) * t)
      = Function.update X j0 (w + (p : ℤ) ^ (n0 - e) * t) := by
    funext i
    by_cases hi : i = j0 <;> simp [Function.update_apply, hi]
  rw [hupd] at hc hm0
  have hpowe : (p : ℤ) ^ (n0 - e) * (p : ℤ) ^ e = (p : ℤ) ^ n0 := by
    rw [← pow_add]; congr 1; omega
  have hexp2 : (p : ℤ) ^ (n0 - e) * (p : ℤ) ^ (n0 - e)
      = (p : ℤ) ^ (n0 + 1) * (p : ℤ) ^ (n0 - 2 * e - 1) := by
    rw [← pow_add, ← pow_add]; congr 1; omega
  have hpowe3 : (p : ℤ) ^ (n0 - e) = (p : ℤ) ^ (e + 1) * (p : ℤ) ^ (n0 - 2 * e - 1) := by
    rw [← pow_add]; congr 1; omega
  refine ⟨w + (p : ℤ) ^ (n0 - e) * t, s1 + c * t * t * (p : ℤ) ^ (n0 - 2 * e - 1),
    dd + (p : ℤ) * ((p : ℤ) ^ (n0 - 2 * e - 1) * t * m0), ⟨t, by ring⟩, ?_, ?_, ?_⟩
  · have hval : formEval d n A (Function.update X j0 (w + (p : ℤ) ^ (n0 - e) * t))
        = (p : ℤ) ^ n0 * s + ((p : ℤ) ^ (n0 - e) * t) * ((p : ℤ) ^ e * dd)
          + c * (((p : ℤ) ^ (n0 - e) * t) * ((p : ℤ) ^ (n0 - e) * t)) := by
      rw [hDp] at hc
      linarith [hc, hW]
    rw [hval]
    have h2 : ((p : ℤ) ^ (n0 - e) * t) * ((p : ℤ) ^ e * dd) = (p : ℤ) ^ n0 * (dd * t) := by
      rw [show ((p : ℤ) ^ (n0 - e) * t) * ((p : ℤ) ^ e * dd)
          = ((p : ℤ) ^ (n0 - e) * (p : ℤ) ^ e) * (t * dd) from by ring, hpowe]
      ring
    have h3 : c * (((p : ℤ) ^ (n0 - e) * t) * ((p : ℤ) ^ (n0 - e) * t))
        = (p : ℤ) ^ (n0 + 1) * (c * t * t * (p : ℤ) ^ (n0 - 2 * e - 1)) := by
      rw [show ((p : ℤ) ^ (n0 - e) * t) * ((p : ℤ) ^ (n0 - e) * t)
          = ((p : ℤ) ^ (n0 - e) * (p : ℤ) ^ (n0 - e)) * (t * t) from by ring, hexp2]
      ring
    rw [h2, h3]
    have h5 : (p : ℤ) ^ n0 * s + (p : ℤ) ^ n0 * (dd * t) = (p : ℤ) ^ n0 * (s + dd * t) := by
      rw [mul_add]
    rw [h5, hs1]
    ring
  · have hval2 : pderivEval d n A j0 (Function.update X j0 (w + (p : ℤ) ^ (n0 - e) * t))
        = (p : ℤ) ^ e * dd + ((p : ℤ) ^ (n0 - e) * t) * m0 := by
      linarith [hm0]
    rw [hval2, hpowe3]
    have hps : (p : ℤ) ^ (e + 1) = (p : ℤ) ^ e * (p : ℤ) := by rw [pow_succ]
    rw [hps]
    ring
  · intro hdiv
    obtain ⟨z, hz⟩ := hdiv
    exact hdd ⟨z - (p : ℤ) ^ (n0 - 2 * e - 1) * t * m0, by linarith [hz]⟩

/-- **Hensel lifting for a form along a coordinate direction.**  If `f_A` vanishes at `X`
modulo `p^{2e+1}`, its gradient at `X` is `p^e`-divisible, and the `j0`-th partial derivative is
not divisible by `p^{e+1}`, then one can shift the `j0`-coordinate by a multiple of `p^{e+1}`
so that `f_A` vanishes modulo `p^r`, for any `r ≥ 2e+1`. -/
theorem hensel_line (d n : ℕ) (A : Mon d n → ℤ) (X : Fin (n + 1) → ℤ) (j0 : Fin (n + 1))
    (p : ℕ) (hp : p.Prime) (e r : ℕ) (hr : 2 * e + 1 ≤ r)
    (h0 : (p : ℤ) ^ (2 * e + 1) ∣ formEval d n A X)
    (h1 : (p : ℤ) ^ e ∣ pderivEval d n A j0 X)
    (h2 : ¬ (p : ℤ) ^ (e + 1) ∣ pderivEval d n A j0 X) :
    ∃ u : ℤ, (p : ℤ) ^ (e + 1) ∣ u ∧
      (p : ℤ) ^ r ∣ formEval d n A (Function.update X j0 (X j0 + u)) := by
  classical
  obtain ⟨s0, hs0⟩ := h0
  obtain ⟨d0, hd0⟩ := h1
  have hd0' : ¬ (p : ℤ) ∣ d0 := by
    intro hdiv
    obtain ⟨z, hz⟩ := hdiv
    refine h2 ⟨z, ?_⟩
    rw [hd0, hz, pow_succ]
    ring
  have main : ∀ k : ℕ, ∃ (w s dd : ℤ), (p : ℤ) ^ (e + 1) ∣ w - X j0
      ∧ formEval d n A (Function.update X j0 w) = (p : ℤ) ^ (2 * e + 1 + k) * s
      ∧ pderivEval d n A j0 (Function.update X j0 w) = (p : ℤ) ^ e * dd
      ∧ ¬ (p : ℤ) ∣ dd := by
    intro k
    induction k with
    | zero =>
        have hupd : Function.update X j0 (X j0) = X := by
          funext i
          by_cases hi : i = j0 <;> simp [Function.update_apply, hi]
        refine ⟨X j0, s0, d0, ⟨0, by simp⟩, ?_, ?_, hd0'⟩
        · rw [hupd, hs0]
        · rw [hupd, hd0]
    | succ k ih =>
        obtain ⟨w, s, dd, hw, hW, hD, hdd⟩ := ih
        obtain ⟨w', s', dd', hw', hW', hD', hdd'⟩ :=
          hensel_step d n A X j0 p hp e (2 * e + 1 + k) (by omega) w s dd hW hD hdd
        refine ⟨w', s', dd', ?_, ?_, hD', hdd'⟩
        · have hk : (p : ℤ) ^ (e + 1) ∣ w' - w :=
            dvd_trans (pow_dvd_pow (p : ℤ) (by omega : e + 1 ≤ 2 * e + 1 + k - e)) hw'
          have hsum := dvd_add hk hw
          rwa [show (w' - w) + (w - X j0) = w' - X j0 from by ring] at hsum
        · rw [hW']
          congr 1
  obtain ⟨w, s, dd, hw, hW, hD, hdd⟩ := main (r - (2 * e + 1))
  refine ⟨w - X j0, hw, ?_⟩
  rw [show X j0 + (w - X j0) = w from by ring, hW]
  have hexp : 2 * e + 1 + (r - (2 * e + 1)) = r := by omega
  rw [hexp]
  exact dvd_mul_right ((p : ℤ) ^ r) s


/-! ## Primitivity of integer vectors modulo `p^r` -/

/-- The number of coordinates of `Fin (n+1)` different from a fixed one is `n`. -/
lemma card_ne_fin (n : ℕ) (j0 : Fin (n + 1)) : Fintype.card {i : Fin (n + 1) // i ≠ j0} = n := by
  have h := Fintype.card_subtype_compl (fun i : Fin (n + 1) => i = j0)
  rw [Fintype.card_fin] at h
  have h1 : Fintype.card {i : Fin (n + 1) // i = j0} = 1 := Fintype.card_subtype_eq j0
  rw [h1] at h
  rw [Nat.add_sub_cancel] at h
  exact h

/-- An integer vector is primitive modulo `p^r` iff some coordinate is not divisible by `p`. -/
theorem isPrimGen_intCast_iff {n p r : ℕ} (hp : p.Prime) (hr : 1 ≤ r) (X : Fin (n + 1) → ℤ) :
    IsPrimGen (p ^ r) (fun i => ((X i : ℤ) : ZMod (p ^ r))) ↔ ∃ i, ¬ (p : ℤ) ∣ X i := by
  constructor
  · intro h
    by_contra hc
    push_neg at hc
    have hle : Ideal.span (Set.range fun i => ((X i : ℤ) : ZMod (p ^ r)))
        ≤ Ideal.span {(p : ZMod (p ^ r))} := by
      rw [Ideal.span_le]
      rintro y ⟨i, rfl⟩
      obtain ⟨c, hc'⟩ := hc i
      change (((X i : ℤ)) : ZMod (p ^ r)) ∈ Ideal.span {(p : ZMod (p ^ r))}
      rw [hc']
      push_cast
      rw [mul_comm]
      exact Ideal.mul_mem_left _ _ (Ideal.subset_span (Set.mem_singleton _))
    have htop : Ideal.span {(p : ZMod (p ^ r))} = ⊤ := le_antisymm le_top (h ▸ hle)
    exact absurd (Ideal.span_singleton_eq_top.mp htop)
      (ZMod.prime_natCast_not_isUnit_pow hp (by omega))
  · rintro ⟨i, hi⟩
    change Ideal.span (Set.range fun i => ((X i : ℤ) : ZMod (p ^ r))) = ⊤
    haveI : NeZero (p ^ r) := ⟨pow_ne_zero r hp.ne_zero⟩
    have hunit : IsUnit (((X i : ℤ) : ZMod (p ^ r))) := by
      rw [← ZMod.natCast_zmod_val (((X i : ℤ) : ZMod (p ^ r))), ZMod.isUnit_iff_coprime,
        Nat.coprime_pow_right_iff (by omega : 0 < r), Nat.coprime_comm, hp.coprime_iff_not_dvd]
      have hpr : ((p ^ r : ℕ) : ℤ) ≠ 0 := by
        have h0 : 0 < p ^ r := pow_pos hp.pos r
        exact_mod_cast h0.ne'
      have hpos : (0 : ℤ) ≤ X i % ((p ^ r : ℕ) : ℤ) := Int.emod_nonneg _ hpr
      have hval : ((X i : ℤ) : ZMod (p ^ r)).val = (X i % ((p ^ r : ℕ) : ℤ)).toNat :=
        Nat.cast_injective (by
          rw [ZMod.val_intCast, Int.toNat_of_nonneg hpos])
      rw [hval]
      intro hdiv
      apply hi
      have h1 : (p : ℤ) ∣ ((X i % ((p ^ r : ℕ) : ℤ)).toNat : ℤ) := by
        exact_mod_cast hdiv
      rw [Int.toNat_of_nonneg hpos] at h1
      have hmod : (p : ℤ) ∣ X i - (X i % ((p ^ r : ℕ) : ℤ)) := by
        have h1 : (p : ℤ) ^ 1 ∣ (p : ℤ) ^ r := pow_dvd_pow (p : ℤ) hr
        rw [pow_one] at h1
        have h2 : ((p ^ r : ℕ) : ℤ) ∣ X i - (X i % ((p ^ r : ℕ) : ℤ)) :=
          (ZMod.intCast_eq_intCast_iff_dvd_sub (X i % ((p ^ r : ℕ) : ℤ)) (X i) (p ^ r)).mp
            (by rw [ZMod.intCast_mod])
        exact dvd_trans h1 h2
      have hsum := dvd_add hmod h1
      rwa [sub_add_cancel] at hsum
    have htop : Ideal.span {((X i : ℤ) : ZMod (p ^ r))} = ⊤ := Ideal.span_singleton_eq_top.mpr hunit
    have hle : Ideal.span {((X i : ℤ) : ZMod (p ^ r))}
        ≤ Ideal.span (Set.range fun j => ((X j : ℤ) : ZMod (p ^ r))) :=
      Ideal.span_mono (by rintro y rfl; exact Set.mem_range_self i)
    exact le_antisymm le_top (htop ▸ hle)


/-! ## The main theorem -/

theorem sigQ_lower_Rset (d n p r e : ℕ) (hd : 1 ≤ d) (hp : p.Prime) (hr : 1 ≤ r) (he : e ≤ r)
    (a : Work.HP.Mon d n → ZMod (p ^ r)) (ha : Work.HP.NA.Rset d n p r e a) :
    1 / (p : ℝ) ^ ((e + 1) * n) ≤ Work.HP.NA.sigQ d n (p ^ r) a := by
  classical
  obtain ⟨hapr, x, hxpr, hfx, hgr, hex⟩ := ha
  set S : Set (Fin (n + 1) → ZMod (p ^ r)) :=
    {b | IsPrimGen (p ^ r) b ∧ fev d n a b = 0} with hS
  have hsigQ : Work.HP.NA.sigQ d n (p ^ r) a
      = ((S.ncard : ℕ) : ℝ) / (((p ^ r : ℕ)) : ℝ) ^ n := rfl
  haveI : NeZero (p ^ r) := ⟨pow_ne_zero r hp.ne_zero⟩
  rcases lt_or_ge e r with hlt | hge
  · -- main case: `e < r`
    obtain ⟨j0, hj0⟩ : ∃ j0 : Fin (n + 1), ¬ vpDvd p r (e + 1) (gradv d n a x j0) := by
      by_contra hcon
      push_neg at hcon
      exact hex hlt hcon
    set A : Mon d n → ℤ := fun m => (a m).val with hAdef
    set X : Fin (n + 1) → ℤ := fun i => (x i).val with hXdef
    have hAa : (fun m => ((A m : ℤ) : ZMod (p ^ r))) = a := by
      funext m
      simp only [hAdef, Int.cast_natCast, ZMod.natCast_zmod_val]
    have hXx : (fun i => ((X i : ℤ) : ZMod (p ^ r))) = x := by
      funext i
      simp only [hXdef, Int.cast_natCast, ZMod.natCast_zmod_val]
    have hbaseForm : (p : ℤ) ^ r ∣ formEval d n A X := by
      have h0 : ((formEval d n A X : ℤ) : ZMod (p ^ r)) = 0 := by
        rw [← fev_intCast d n (p ^ r) A X, hAa, hXx, hfx]
      exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp h0
    have hbaseGrad : ∀ i, (p : ℤ) ^ e ∣ pderivEval d n A i X := by
      intro i
      obtain ⟨c, hc⟩ := hgr i
      have hc' : dfev d n a x i = (p : ZMod (p ^ r)) ^ e * c := hc
      have h1 : ((pderivEval d n A i X : ℤ) : ZMod (p ^ r))
          = ((p : ℤ) ^ e * ((c.val : ℕ) : ℤ) : ℤ) := by
        rw [← dfev_intCast d n (p ^ r) A X i, hAa, hXx, hc']
        push_cast
        rw [ZMod.natCast_zmod_val]
      have h3 : (p : ℤ) ^ r ∣ pderivEval d n A i X - (p : ℤ) ^ e * ((c.val : ℕ) : ℤ) := by
        have hzero : (((pderivEval d n A i X - (p : ℤ) ^ e * ((c.val : ℕ) : ℤ)) : ℤ) : ZMod (p ^ r)) = 0 := by
          rw [Int.cast_sub, h1, sub_self]
        have h4 := (ZMod.intCast_zmod_eq_zero_iff_dvd
          (pderivEval d n A i X - (p : ℤ) ^ e * ((c.val : ℕ) : ℤ)) (p ^ r)).mp hzero
        rwa [Nat.cast_pow] at h4
      have h4 : (p : ℤ) ^ e ∣ pderivEval d n A i X - (p : ℤ) ^ e * ((c.val : ℕ) : ℤ) :=
        dvd_trans (pow_dvd_pow (p : ℤ) he) h3
      have h5 : (p : ℤ) ^ e ∣ (p : ℤ) ^ e * ((c.val : ℕ) : ℤ) := dvd_mul_right _ _
      have hsum := dvd_add h4 h5
      rwa [sub_add_cancel] at hsum
    have hj0Grad : ¬ (p : ℤ) ^ (e + 1) ∣ pderivEval d n A j0 X := by
      intro hdiv
      apply hj0
      obtain ⟨c, hc⟩ := hdiv
      refine ⟨((c : ℤ) : ZMod (p ^ r)), ?_⟩
      change dfev d n a x j0 = (p : ZMod (p ^ r)) ^ (e + 1) * ((c : ℤ) : ZMod (p ^ r))
      rw [← hAa, ← hXx, dfev_intCast d n (p ^ r) A X j0, hc]
      push_cast
      ring
    have hxprim : ∃ i, ¬ (p : ℤ) ∣ X i := by
      rw [← isPrimGen_intCast_iff hp hr X]
      rwa [← hXx] at hxpr
    -- parametrisation of the auxiliary solutions
    let L : ℕ := r - e - 1
    let Idx : Type := {i : Fin (n + 1) // i ≠ j0}
    haveI : NeZero (p ^ L) := ⟨pow_ne_zero L hp.ne_zero⟩
    let V : (Idx → ZMod (p ^ L)) → Fin (n + 1) → ℤ :=
      fun v i => if h : i = j0 then 0 else ((v ⟨i, h⟩).val : ℤ)
    let Hv : (Idx → ZMod (p ^ L)) → Fin (n + 1) → ℤ := fun v i => (p : ℤ) ^ (e + 1) * V v i
    let Xv : (Idx → ZMod (p ^ L)) → Fin (n + 1) → ℤ := fun v => X + Hv v
    have hH : ∀ (v : Idx → ZMod (p ^ L)) (i : Fin (n + 1)), (p : ℤ) ^ (e + 1) ∣ Hv v i :=
      fun v i => dvd_mul_right _ _
    have h0v : ∀ v : Idx → ZMod (p ^ L),
        (p : ℤ) ^ (2 * e + 1) ∣ formEval d n A (Xv v) - formEval d n A X :=
      fun v => formEval_taylor2 d n e p A X (Hv v) (hH v) hbaseGrad
    have h1v : ∀ v : Idx → ZMod (p ^ L),
        (p : ℤ) ^ (e + 1) ∣ pderivEval d n A j0 (Xv v) - pderivEval d n A j0 X :=
      fun v => pderivEval_lipschitz d n e p A X (Hv v) j0 (hH v)
    have hXvForm : ∀ v : Idx → ZMod (p ^ L),
        (p : ℤ) ^ min r (2 * e + 1) ∣ formEval d n A (Xv v) := by
      intro v
      have h1 : (p : ℤ) ^ min r (2 * e + 1) ∣ formEval d n A (Xv v) - formEval d n A X :=
        dvd_trans (pow_dvd_pow (p : ℤ) (min_le_right _ _)) (h0v v)
      have h2 : (p : ℤ) ^ min r (2 * e + 1) ∣ formEval d n A X :=
        dvd_trans (pow_dvd_pow (p : ℤ) (min_le_left _ _)) hbaseForm
      have hsum := dvd_add h1 h2
      rwa [sub_add_cancel] at hsum
    have hXvGrad1 : ∀ v : Idx → ZMod (p ^ L), (p : ℤ) ^ e ∣ pderivEval d n A j0 (Xv v) := by
      intro v
      have h2 : (p : ℤ) ^ e ∣ pderivEval d n A j0 (Xv v) - pderivEval d n A j0 X :=
        dvd_trans (pow_dvd_pow (p : ℤ) (by omega : e ≤ e + 1)) (h1v v)
      have hsum := dvd_add h2 (hbaseGrad j0)
      rwa [sub_add_cancel] at hsum
    have hXvGrad2 : ∀ v : Idx → ZMod (p ^ L), ¬ (p : ℤ) ^ (e + 1) ∣ pderivEval d n A j0 (Xv v) := by
      intro v hdiv
      have hsum := dvd_sub hdiv (h1v v)
      rw [sub_sub_cancel] at hsum
      exact hj0Grad hsum
    have hsol : ∀ v : Idx → ZMod (p ^ L), ∃ U : ℤ, (p : ℤ) ^ (e + 1) ∣ U ∧
        (p : ℤ) ^ r ∣ formEval d n A (Function.update (Xv v) j0 ((Xv v) j0 + U)) := by
      intro v
      by_cases h2e : 2 * e + 1 ≤ r
      · have hmin : min r (2 * e + 1) = 2 * e + 1 := min_eq_right h2e
        have hv : (p : ℤ) ^ (2 * e + 1) ∣ formEval d n A (Xv v) := by
          rw [← hmin]; exact hXvForm v
        exact hensel_line d n A (Xv v) j0 p hp e r h2e hv (hXvGrad1 v) (hXvGrad2 v)
      · have hle : r ≤ 2 * e + 1 := by omega
        have hmin : min r (2 * e + 1) = r := min_eq_left hle
        refine ⟨0, by simp, ?_⟩
        rw [show (Xv v) j0 + 0 = (Xv v) j0 from by ring, Function.update_eq_self]
        rw [← hmin]
        exact hXvForm v
    let Uv : (Idx → ZMod (p ^ L)) → ℤ := fun v => (hsol v).choose
    have hUv1 : ∀ v, (p : ℤ) ^ (e + 1) ∣ Uv v := fun v => (hsol v).choose_spec.1
    have hUv2 : ∀ v, (p : ℤ) ^ r ∣ formEval d n A (Function.update (Xv v) j0 ((Xv v) j0 + Uv v)) :=
      fun v => (hsol v).choose_spec.2
    let b : (Idx → ZMod (p ^ L)) → Fin (n + 1) → ℤ :=
      fun v => Function.update (Xv v) j0 ((Xv v) j0 + Uv v)
    -- the coordinate formula for `b`
    have hb_ne : ∀ (v : Idx → ZMod (p ^ L)) (i : Fin (n + 1)), i ≠ j0 →
        b v i = X i + (p : ℤ) ^ (e + 1) * V v i := by
      intro v i hi
      show Function.update (Xv v) j0 ((Xv v) j0 + Uv v) i = X i + (p : ℤ) ^ (e + 1) * V v i
      rw [Function.update_apply, if_neg hi]
      show X i + Hv v i = X i + (p : ℤ) ^ (e + 1) * V v i
      rfl
    have hb_eq : ∀ (v : Idx → ZMod (p ^ L)),
        b v j0 = X j0 + Uv v := by
      intro v
      show Function.update (Xv v) j0 ((Xv v) j0 + Uv v) j0 = X j0 + Uv v
      rw [Function.update_apply, if_pos rfl]
      show X j0 + Hv v j0 + Uv v = X j0 + Uv v
      rw [show Hv v j0 = 0 from by
        show (p : ℤ) ^ (e + 1) * V v j0 = 0
        rw [show V v j0 = 0 from dif_pos rfl, mul_zero]]
      ring
    have hbForm : ∀ v, ((formEval d n A (b v) : ℤ) : ZMod (p ^ r)) = 0 :=
      fun v => (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr (hUv2 v)
    have hbfev : ∀ v, fev d n a (fun i => ((b v i : ℤ) : ZMod (p ^ r))) = 0 := by
      intro v
      rw [← hAa, fev_intCast d n (p ^ r) A (b v)]
      exact hbForm v
    have hbprim : ∀ v, IsPrimGen (p ^ r) (fun i => ((b v i : ℤ) : ZMod (p ^ r))) := by
      intro v
      rw [isPrimGen_intCast_iff hp hr]
      obtain ⟨i, hi⟩ := hxprim
      refine ⟨i, ?_⟩
      intro hdiv
      apply hi
      have hdiff : (p : ℤ) ∣ b v i - X i := by
        by_cases hi0 : i = j0
        · subst hi0
          have hp1 : (p : ℤ) ^ 1 ∣ (p : ℤ) ^ (e + 1) := pow_dvd_pow (p : ℤ) (by omega : 1 ≤ e + 1)
          rw [pow_one] at hp1
          rw [hb_eq v, show X i + Uv v - X i = Uv v from by ring]
          exact dvd_trans hp1 (hUv1 v)
        · have hp1 : (p : ℤ) ^ 1 ∣ (p : ℤ) ^ (e + 1) := pow_dvd_pow (p : ℤ) (by omega : 1 ≤ e + 1)
          rw [pow_one] at hp1
          rw [hb_ne v i hi0, show X i + (p : ℤ) ^ (e + 1) * V v i - X i
              = (p : ℤ) ^ (e + 1) * V v i from by ring]
          exact dvd_mul_of_dvd_left hp1 (V v i)
      have hsum := dvd_sub hdiv hdiff
      rwa [sub_sub_cancel] at hsum
    have hinj : Function.Injective
        (fun v : Idx → ZMod (p ^ L) => fun i => ((b v i : ℤ) : ZMod (p ^ r))) := by
      intro v v' hvv
      funext i
      have hcoord : ((b v i.1 : ℤ) : ZMod (p ^ r)) = ((b v' i.1 : ℤ) : ZMod (p ^ r)) :=
        congrFun hvv i.1
      have hpr : (p : ℤ) ^ r ∣ b v i.1 - b v' i.1 := by
        have h := (ZMod.intCast_eq_intCast_iff_dvd_sub (b v i.1) (b v' i.1) (p ^ r)).mp hcoord
        rw [show b v i.1 - b v' i.1 = -(b v' i.1 - b v i.1) from by ring]
        exact dvd_neg.mpr h
      rw [hb_ne v i.1 i.2, hb_ne v' i.1 i.2] at hpr
      have hpr' : (p : ℤ) ^ r ∣ (p : ℤ) ^ (e + 1) * (V v i.1 - V v' i.1) := by
        rwa [show X i.1 + (p : ℤ) ^ (e + 1) * V v i.1 - (X i.1 + (p : ℤ) ^ (e + 1) * V v' i.1)
            = (p : ℤ) ^ (e + 1) * (V v i.1 - V v' i.1) from by ring] at hpr
      have hLdiv : (p : ℤ) ^ L ∣ V v i.1 - V v' i.1 := by
        have hpe0 : (p : ℤ) ^ (e + 1) ≠ 0 := pow_ne_zero _ (by exact_mod_cast hp.ne_zero)
        rw [show (p : ℤ) ^ r = (p : ℤ) ^ (e + 1) * (p : ℤ) ^ L from by
          rw [← pow_add]; congr 1; omega] at hpr'
        exact (mul_dvd_mul_iff_left hpe0).mp hpr'
      have hvv : V v i.1 = ((v i).val : ℤ) := by
        show (if h : i.1 = j0 then 0 else ((v ⟨i.1, h⟩).val : ℤ)) = ((v i).val : ℤ)
        rw [dif_neg i.2, show (⟨i.1, i.2⟩ : Idx) = i from Subtype.ext rfl]
      have hvv' : V v' i.1 = ((v' i).val : ℤ) := by
        show (if h : i.1 = j0 then 0 else ((v' ⟨i.1, h⟩).val : ℤ)) = ((v' i).val : ℤ)
        rw [dif_neg i.2, show (⟨i.1, i.2⟩ : Idx) = i from Subtype.ext rfl]
      rw [hvv, hvv'] at hLdiv
      have hZ : ((v i).val : ZMod (p ^ L)) = ((v' i).val : ZMod (p ^ L)) := by
        have h3 : (p : ℤ) ^ L ∣ ((v' i).val : ℤ) - ((v i).val : ℤ) := by
          rw [show ((v' i).val : ℤ) - ((v i).val : ℤ)
              = -(((v i).val : ℤ) - ((v' i).val : ℤ)) from by ring]
          exact dvd_neg.mpr hLdiv
        have h := (ZMod.intCast_eq_intCast_iff_dvd_sub (((v i).val : ℕ) : ℤ)
          (((v' i).val : ℕ) : ℤ) (p ^ L)).mpr h3
        rw [Int.cast_natCast, Int.cast_natCast] at h
        exact h
      rwa [ZMod.natCast_zmod_val, ZMod.natCast_zmod_val] at hZ
    have hcard_idx : Fintype.card (Idx → ZMod (p ^ L)) = (p ^ L) ^ n := by
      rw [Fintype.card_fun]
      have h1 : Fintype.card (ZMod (p ^ L)) = p ^ L := ZMod.card (p ^ L)
      have h2 : Fintype.card Idx = n := card_ne_fin n j0
      rw [h1, h2]
    have hfinal : (p ^ L) ^ n ≤ S.ncard := by
      have hsub : Set.range (fun v : Idx → ZMod (p ^ L) =>
            (fun i => ((b v i : ℤ) : ZMod (p ^ r)))) ⊆ S := by
        rintro f ⟨v, rfl⟩
        exact ⟨hbprim v, hbfev v⟩
      have hfin : (Set.range fun v : Idx → ZMod (p ^ L) =>
            (fun i => ((b v i : ℤ) : ZMod (p ^ r)))).Finite := Set.finite_range _
      have h1 := Set.ncard_le_ncard hsub
      rw [Set.ncard_range_of_injective hinj, Nat.card_eq_fintype_card, hcard_idx] at h1
      exact h1
    have hcast : (((p ^ L) ^ n : ℕ) : ℝ) ≤ (S.ncard : ℝ) := by exact_mod_cast hfinal
    have hLcast : (((p ^ L) ^ n : ℕ) : ℝ) = (p : ℝ) ^ (L * n) := by
      push_cast
      rw [← pow_mul]
    have hden : (((p ^ r : ℕ)) : ℝ) ^ n = (p : ℝ) ^ (r * n) := by
      push_cast
      rw [← pow_mul]
    have harith : (p : ℝ) ^ (L * n) / (p : ℝ) ^ (r * n) = 1 / (p : ℝ) ^ ((e + 1) * n) := by
      have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne_zero
      have hLr : r * n = L * n + (e + 1) * n := by
        rw [← add_mul]
        congr 1
        show r = L + (e + 1)
        rw [show L = r - e - 1 from rfl]
        omega
      rw [hLr, pow_add]
      field_simp
    rw [hsigQ, hden]
    calc (1 : ℝ) / (p : ℝ) ^ ((e + 1) * n)
        = (p : ℝ) ^ (L * n) / (p : ℝ) ^ (r * n) := harith.symm
      _ = (((p ^ L) ^ n : ℕ) : ℝ) / (p : ℝ) ^ (r * n) := by rw [hLcast]
      _ ≤ (S.ncard : ℝ) / (p : ℝ) ^ (r * n) := div_le_div_of_nonneg_right hcast (by positivity)
  · -- case `e = r`
    have her : e = r := le_antisymm he hge
    have hmem : x ∈ S := ⟨hxpr, hfx⟩
    have hcard : 1 ≤ S.ncard := by
      have h1 := Set.ncard_le_ncard (Set.singleton_subset_iff.mpr hmem)
      rwa [Set.ncard_singleton] at h1
    have hcast : (1 : ℝ) ≤ (S.ncard : ℝ) := by exact_mod_cast hcard
    have hp1 : (1 : ℝ) ≤ (p : ℝ) := by
      exact_mod_cast (le_of_lt hp.one_lt)
    have hpow : (p : ℝ) ^ (r * n) ≤ (p : ℝ) ^ ((r + 1) * n) :=
      pow_le_pow_right₀ hp1 (by nlinarith)
    have hden : (((p ^ r : ℕ)) : ℝ) ^ n = (p : ℝ) ^ (r * n) := by
      push_cast
      rw [← pow_mul]
    rw [hsigQ, hden, her]
    calc (1 : ℝ) / (p : ℝ) ^ ((r + 1) * n)
        ≤ 1 / (p : ℝ) ^ (r * n) := by
          apply one_div_le_one_div_of_le (by positivity)
          exact hpow
      _ ≤ (S.ncard : ℝ) / (p : ℝ) ^ (r * n) :=
          div_le_div_of_nonneg_right hcast (by positivity)

end Work.HP.NA
