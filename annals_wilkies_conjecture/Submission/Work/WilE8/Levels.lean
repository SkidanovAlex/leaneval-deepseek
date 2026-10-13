/-
  WilE8 — the level data `(A, P)` for the reduction `Gen ⊆ StarR` (E8a).

  Given the "closure data" `Close` (which is what the E7/E2 theorems of area E provide, see
  `Assemble.lean`), we build

  * `A F n` — the `*`-format bound at `Gen`-level `F` and dimension `n`,
  * `P F n  = c F n * X ^ e F n` — the `*`-degree bound, always a monomial `c·X^e`, `e ≥ 1`,

  so that the induction of `E8_reduce` goes through:
  `Gen F D n X → StarR (A F n) (P F n |>.eval D) n X`.
  All the requirements on `(A, P)` are proved in this file.
-/
import Submission.Work.Wilkies.E.Spec
import Submission.Work.WilE8.Basic
import Submission.Work.WilE8.Poly.exists_dom
import Submission.Work.WilE8.Poly.sum_pow_le

set_option autoImplicit false
noncomputable section
open Classical Topology
namespace Work.WilE8
open WilkiesDesign WilkiesDesign.E

/-! ## A monomial dominating a polynomial on `D ≥ 1` -/

/-- The `(c, e)` from `Work.WilE8.Poly.exists_dom`, normalised so that `e ≥ 1`. -/
theorem exists_pow_dom (p : Polynomial ℕ) :
    ∃ (c e : ℕ), 1 ≤ e ∧ ∀ D : ℕ, 1 ≤ D → p.eval D ≤ c * D ^ e := by
  obtain ⟨c, e, h⟩ := Poly.exists_dom (fun _ : Fin 1 => p)
  have hc : ∀ D : ℕ, 1 ≤ D → p.eval D ≤ c * D ^ e := fun D hD => h D hD 0
  rcases Nat.eq_zero_or_pos e with he | he
  · subst he
    refine ⟨c, 1, le_rfl, fun D hD => ?_⟩
    rw [pow_one]
    refine le_trans (hc D hD) ?_
    simpa using Nat.le_mul_of_pos_right c hD
  · exact ⟨c, e, he, hc⟩

/-! ## Closure data -/

/-- The closure data for the reduction, extracted from the E7/E2 theorems of area E.
`complA/complP` are the `*`-format/`*`-degree cost of complement, etc. -/
structure Close where
  complA : ℕ → ℕ → ℕ
  complP : ℕ → ℕ → Polynomial ℕ
  hcompl : ∀ (a0 n : ℕ) (D : ℕ) (X : Set (Fin n → ℝ)),
    StarR a0 D n X → StarR (complA a0 n) ((complP a0 n).eval D) n Xᶜ
  interA : ℕ → ℕ → ℕ
  interP : ℕ → ℕ → Polynomial ℕ
  hinter : ∀ (a0 n k : ℕ) (D : Fin k → ℕ) (X : Fin k → Set (Fin n → ℝ)),
    (∀ i, StarR a0 (D i) n (X i)) →
      StarR (interA a0 n) ((interP a0 n).eval (∑ i, D i)) n (⋂ i, X i)
  projA : ℕ → ℕ → ℕ
  projP : ℕ → ℕ → Polynomial ℕ
  hproj : ∀ (a0 n : ℕ) (D : ℕ) (X : Set (Fin (n + 1) → ℝ)),
    StarR a0 D (n + 1) X → StarR (projA a0 n) ((projP a0 n).eval D) n (projLast X)
  hypP : ℕ → Polynomial ℕ
  hhyp : ∀ (n : ℕ) (Q : MvPolynomial (Fin n) ℝ), 1 ≤ Q.totalDegree →
    StarR (2 * n) ((hypP n).eval Q.totalDegree) n {x : Fin n → ℝ | MvPolynomial.eval x Q = 0}

namespace Close

variable (C : Close)

/-- The polynomial that the level `F+1` degree bound must dominate, given the level `F` data
`Aprev` (format) and `Pprev` (degree). -/
def targetOf (F : ℕ) (Aprev : ℕ → ℕ) (Pprev : ℕ → Polynomial ℕ) (n : ℕ) : Polynomial ℕ :=
  Polynomial.X + Polynomial.C 1 + Pprev n + Pprev (n - 1) + C.hypP n +
    (C.complP (Aprev n) n).comp (Pprev n) +
    (C.interP (Aprev n) n).comp (Pprev n) +
    (C.projP (Aprev (n + 1)) n).comp (Pprev (n + 1))

/-- The format bound at the next level: the sum of all format requirements (any upper bound
for the requirements suffices, so a sum keeps the arithmetic simple). -/
def stepA (F : ℕ) (Aprev : ℕ → ℕ) (n : ℕ) : ℕ :=
  Aprev n + (F + 1) + n + (2 * n + 1) + C.complA (Aprev n) n + C.interA (Aprev n) n +
    C.projA (Aprev (n + 1)) n + (Aprev (n - 1) + 1)

/-- One level of the recursive data: format bound `A`, and the monomial data `c`, `e ≥ 1`. -/
structure Dat where
  A : ℕ → ℕ
  c : ℕ → ℕ
  e : ℕ → ℕ
  he : ∀ n, 1 ≤ e n

/-- The next level. -/
def step (F : ℕ) (d : Dat) : Dat :=
  let Pprev : ℕ → Polynomial ℕ := fun m => Polynomial.C (d.c m) * Polynomial.X ^ (d.e m)
  let tgt : ℕ → Polynomial ℕ := C.targetOf F d.A Pprev
  ⟨C.stepA F d.A, (fun n => (exists_pow_dom (tgt n)).choose),
   (fun n => (exists_pow_dom (tgt n)).choose_spec.choose),
   fun n => (exists_pow_dom (tgt n)).choose_spec.choose_spec.1⟩

/-- The recursive level data. -/
def dat : ℕ → Dat
  | 0 => ⟨fun n => 2 * n + 1,
      (fun n => (exists_pow_dom (C.hypP n + Polynomial.X + Polynomial.C 1)).choose),
      (fun n => (exists_pow_dom (C.hypP n + Polynomial.X + Polynomial.C 1)).choose_spec.choose),
      fun n =>
        (exists_pow_dom (C.hypP n + Polynomial.X + Polynomial.C 1)).choose_spec.choose_spec.1⟩
  | F + 1 => C.step F (dat F)

/-- The `*`-format bound. -/
def lvlA (F n : ℕ) : ℕ := (C.dat F).A n

/-- The `*`-degree bound polynomial; always a monomial `c · X^e` with `e ≥ 1`. -/
def lvlP (F n : ℕ) : Polynomial ℕ :=
  Polynomial.C ((C.dat F).c n) * Polynomial.X ^ ((C.dat F).e n)

lemma lvlP_eval (F n D : ℕ) :
    (C.lvlP F n).eval D = (C.dat F).c n * D ^ (C.dat F).e n := by
  simp [lvlP]

lemma lvlP_e_ge (F n : ℕ) : 1 ≤ (C.dat F).e n := (C.dat F).he n

lemma lvlP_eval_zero (F n : ℕ) : (C.lvlP F n).eval 0 = 0 := by
  rw [lvlP_eval]
  have : (0 : ℕ) ^ (C.dat F).e n = 0 := zero_pow (by have := lvlP_e_ge C F n; omega)
  rw [this, mul_zero]

lemma lvlP_mono_D (F n D D' : ℕ) (h : D ≤ D') :
    (C.lvlP F n).eval D ≤ (C.lvlP F n).eval D' := by
  rw [lvlP_eval, lvlP_eval]
  exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left h _)

lemma lvlP_superadd (F n k : ℕ) (D : Fin k → ℕ) :
    (∑ i, (C.lvlP F n).eval (D i)) ≤ (C.lvlP F n).eval (∑ i, D i) := by
  simp only [lvlP_eval]
  rw [← Finset.mul_sum]
  exact Nat.mul_le_mul_left _ (Poly.sum_pow_le _ (lvlP_e_ge C F n) D)

/-! ### Format requirements -/

lemma le_stepA_self (F : ℕ) (Aprev : ℕ → ℕ) (n : ℕ) : Aprev n ≤ C.stepA F Aprev n := by
  simp only [stepA]; omega

lemma le_stepA_F (F : ℕ) (Aprev : ℕ → ℕ) (n : ℕ) : F + 1 ≤ C.stepA F Aprev n := by
  simp only [stepA]; omega

lemma le_stepA_n (F : ℕ) (Aprev : ℕ → ℕ) (n : ℕ) : n ≤ C.stepA F Aprev n := by
  simp only [stepA]; omega

lemma le_stepA_hyp (F : ℕ) (Aprev : ℕ → ℕ) (n : ℕ) : 2 * n + 1 ≤ C.stepA F Aprev n := by
  simp only [stepA]; omega

lemma le_stepA_compl (F : ℕ) (Aprev : ℕ → ℕ) (n : ℕ) :
    C.complA (Aprev n) n ≤ C.stepA F Aprev n := by
  simp only [stepA]; omega

lemma le_stepA_inter (F : ℕ) (Aprev : ℕ → ℕ) (n : ℕ) :
    C.interA (Aprev n) n ≤ C.stepA F Aprev n := by
  simp only [stepA]; omega

lemma le_stepA_proj (F : ℕ) (Aprev : ℕ → ℕ) (n : ℕ) :
    C.projA (Aprev (n + 1)) n ≤ C.stepA F Aprev n := by
  simp only [stepA]; omega

lemma le_stepA_prod (F : ℕ) (Aprev : ℕ → ℕ) (n : ℕ) :
    Aprev (n - 1) + 1 ≤ C.stepA F Aprev n := by
  simp only [stepA]; omega

lemma lvlA_ge_n (F n : ℕ) : n ≤ C.lvlA F n := by
  cases F with
  | zero => simp only [lvlA, dat]; omega
  | succ F => exact le_stepA_n C F _ n

lemma lvlA_ge_F (F n : ℕ) : F ≤ C.lvlA F n := by
  cases F with
  | zero => exact Nat.zero_le _
  | succ F => exact le_stepA_F C F _ n

lemma lvlA_ge_hyp (F n : ℕ) : 2 * n + 1 ≤ C.lvlA F n := by
  cases F with
  | zero => simp only [lvlA, dat]; omega
  | succ F => exact le_stepA_hyp C F _ n

lemma lvlA_mono (F n : ℕ) : C.lvlA F n ≤ C.lvlA (F + 1) n := le_stepA_self C F _ n

lemma lvlA_compl (F n : ℕ) : C.complA (C.lvlA F n) n ≤ C.lvlA (F + 1) n :=
  le_stepA_compl C F _ n

lemma lvlA_inter (F n : ℕ) : C.interA (C.lvlA F n) n ≤ C.lvlA (F + 1) n :=
  le_stepA_inter C F _ n

lemma lvlA_proj (F n : ℕ) : C.projA (C.lvlA F (n + 1)) n ≤ C.lvlA (F + 1) n :=
  le_stepA_proj C F _ n

lemma lvlA_prod (F n : ℕ) : C.lvlA F (n - 1) + 1 ≤ C.lvlA (F + 1) n :=
  le_stepA_prod C F _ n

/-! ### Degree requirements -/

lemma target_le_lvlP_succ (F n D : ℕ) (hD : 1 ≤ D) :
    (C.targetOf F (C.lvlA F) (C.lvlP F) n).eval D ≤ (C.lvlP (F + 1) n).eval D := by
  have h := (exists_pow_dom (C.targetOf F (C.lvlA F) (C.lvlP F) n)).choose_spec.choose_spec.2 D hD
  have h2 : (C.lvlP (F + 1) n).eval D =
      (exists_pow_dom (C.targetOf F (C.lvlA F) (C.lvlP F) n)).choose *
        D ^ (exists_pow_dom (C.targetOf F (C.lvlA F) (C.lvlP F) n)).choose_spec.choose := by
    rw [lvlP]
    simp only [dat, step, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_pow, Polynomial.eval_X]
    try rfl
  rw [h2]
  exact h

/-- The level-`0` degree bound dominates its own target. -/
lemma base_target (n D : ℕ) :
    (C.lvlP 0 n).eval D =
      (exists_pow_dom (C.hypP n + Polynomial.X + Polynomial.C 1)).choose *
        D ^ (exists_pow_dom (C.hypP n + Polynomial.X + Polynomial.C 1)).choose_spec.choose := by
  simp only [lvlP, dat, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow,
    Polynomial.eval_X]

lemma le_base_target_X (n D : ℕ) :
    D ≤ (C.hypP n + Polynomial.X + Polynomial.C 1).eval D := by
  simp only [Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C]; omega

lemma le_base_target_hyp (n d : ℕ) :
    (C.hypP n).eval d ≤ (C.hypP n + Polynomial.X + Polynomial.C 1).eval d := by
  simp only [Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C]; omega

lemma lvlP_dom_compl (F n D : ℕ) (hD : 1 ≤ D) :
    (C.complP (C.lvlA F n) n).eval ((C.lvlP F n).eval D) ≤ (C.lvlP (F + 1) n).eval D := by
  refine le_trans ?_ (C.target_le_lvlP_succ F n D hD)
  simp only [targetOf, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_comp,
    Polynomial.eval_X, Polynomial.eval_C]
  omega

lemma lvlP_dom_inter (F n D : ℕ) (hD : 1 ≤ D) :
    (C.interP (C.lvlA F n) n).eval ((C.lvlP F n).eval D) ≤ (C.lvlP (F + 1) n).eval D := by
  refine le_trans ?_ (C.target_le_lvlP_succ F n D hD)
  simp only [targetOf, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_comp,
    Polynomial.eval_X, Polynomial.eval_C]
  omega

lemma lvlP_dom_prod (F n D : ℕ) (hD : 1 ≤ D) :
    (C.lvlP F (n - 1)).eval D ≤ (C.lvlP (F + 1) n).eval D := by
  refine le_trans ?_ (C.target_le_lvlP_succ F n D hD)
  simp only [targetOf, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_comp,
    Polynomial.eval_X, Polynomial.eval_C]
  omega

lemma lvlP_dom_proj (F n D : ℕ) (hD : 1 ≤ D) :
    (C.projP (C.lvlA F (n + 1)) n).eval ((C.lvlP F (n + 1)).eval D) ≤
      (C.lvlP (F + 1) n).eval D := by
  refine le_trans ?_ (C.target_le_lvlP_succ F n D hD)
  simp only [targetOf, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_comp,
    Polynomial.eval_X, Polynomial.eval_C]
  omega

lemma lvlP_mono_F (F n D : ℕ) :
    (C.lvlP F n).eval D ≤ (C.lvlP (F + 1) n).eval D := by
  rcases Nat.eq_zero_or_pos D with hD | hD
  · subst hD; rw [lvlP_eval_zero, lvlP_eval_zero]
  · refine le_trans ?_ (C.target_le_lvlP_succ F n D hD)
    simp only [targetOf, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_comp,
      Polynomial.eval_X, Polynomial.eval_C]
    omega

lemma lvlP_ge_id (F n D : ℕ) : D ≤ (C.lvlP F n).eval D := by
  cases F with
  | zero =>
    rcases Nat.eq_zero_or_pos D with hD | hD
    · subst hD; rw [lvlP_eval_zero]
    · rw [C.base_target n D]
      exact le_trans (C.le_base_target_X n D)
        ((exists_pow_dom (C.hypP n + Polynomial.X + Polynomial.C 1)).choose_spec.choose_spec.2 D
          (by omega))
  | succ F =>
    rcases Nat.eq_zero_or_pos D with hD | hD
    · subst hD; rw [lvlP_eval_zero]
    · refine le_trans ?_ (C.target_le_lvlP_succ F n D hD)
      simp only [targetOf, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_comp,
        Polynomial.eval_X, Polynomial.eval_C]
      omega

lemma lvlP_dom_hyp (F n d : ℕ) (hd : 1 ≤ d) : (C.hypP n).eval d ≤ (C.lvlP F n).eval d := by
  cases F with
  | zero =>
    rw [C.base_target n d]
    exact le_trans (C.le_base_target_hyp n d)
      ((exists_pow_dom (C.hypP n + Polynomial.X + Polynomial.C 1)).choose_spec.choose_spec.2 d hd)
  | succ F =>
    refine le_trans ?_ (C.target_le_lvlP_succ F n d hd)
    simp only [targetOf, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_comp,
      Polynomial.eval_X, Polynomial.eval_C]
    omega

end Close

end Work.WilE8
