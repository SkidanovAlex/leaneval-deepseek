/-
  E9 / `Gen` — semialgebraic sets are in the filtration.

  `gen_SA`: with `a` and `b` depending only on the number of variables `n`, every semialgebraic
  set `X ⊆ ℝⁿ` (in DNF over `EAPoly n 0`) lies in `Gen a (b.eval X.deg) n`.

  The three ingredients, and the cost they incur (per atom `P`, `D := atomDeg P = P.totalDegree+1`):

  * an equation `eaEval P = 0` is the zero set of the collapsed polynomial `saCol P`
    (`MvPolynomial (Fin n) ℝ`), which is `Gen.hyp` of degree `≤ D` and format `n`;
  * a strict inequality `eaEval P > 0` is the projection along the last coordinate of the
    quadric `w ^ 2 * collapse P = 1`; that is `Gen.proj` of a `Gen.hyp` of degree `≤ 2D` and
    format `n + 2`;
  * `Gen.inter` (one format) over the `Fin`-indexed atoms of a basic set, and `Gen.union`
    (no format) over the DNF alternatives.

  The degree budget is `2 * X.deg`.
-/
import Mathlib
import Submission.Work.WilE9.Defs

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section

open Classical Topology
namespace Work.WilE9.Gen

open WilkiesDesign WilkiesDesign.E

/-! ## The collapse `EAPoly n 0 → MvPolynomial (Fin n) ℝ` -/

/-- `EAPoly n 0` has no exponential variables (`Fin 0` is empty), so an EA polynomial in `n + 0`
variables *is* an ordinary polynomial in `n` variables: `saCol` sends the variable `Sum.inl i` to
`X i`. (The variable `Sum.inr j` does not exist.) -/
noncomputable def saCol {n : ℕ} (P : MvPolynomial (Fin n ⊕ Fin 0) ℝ) : MvPolynomial (Fin n) ℝ :=
  MvPolynomial.rename (Sum.elim id (Fin.elim0)) P

/-- Evaluation of a `0`-chain EA polynomial is evaluation of the collapsed polynomial. -/
lemma eaEval_nil_col {n : ℕ} (P : MvPolynomial (Fin n ⊕ Fin 0) ℝ) (x : Fin n → ℝ) :
    eaEval (EAChain.nil n) P x = MvPolynomial.eval x (saCol P) := by
  unfold saCol eaEval
  rw [MvPolynomial.eval_rename]
  rw [show (Sum.elim x (fun j : Fin 0 => Real.exp ((EAChain.nil n).ell j x))) =
      (x ∘ Sum.elim id (Fin.elim0)) from by
    funext z
    rcases z with i | j
    · rfl
    · exact j.elim0]

/-- Summing a function of the entries of a list, over the `Fin`-indexed positions. -/
lemma sum_get {α M : Type*} [AddCommMonoid M] (l : List α) (f : α → M) :
    (∑ i : Fin l.length, f (l.get i)) = (l.map f).sum := by
  rw [← List.sum_ofFn, List.ofFn_comp', List.ofFn_get]

/-! ## Atoms: equations and strict inequalities -/

/-- The quadratic equation `w ^ 2 * saCol P - 1 = 0` in the extra variable `w` (the last one).
Its projection along `w` is the strict inequality `eaEval P > 0`. -/
noncomputable def quad {n : ℕ} (P : MvPolynomial (Fin n ⊕ Fin 0) ℝ) :
    MvPolynomial (Fin (n + 1)) ℝ :=
  MvPolynomial.X (Fin.last n) ^ 2 * MvPolynomial.rename Fin.castSucc (saCol P) -
    MvPolynomial.C 1

/-- The value of `quad P` at `Fin.snoc x t`. -/
lemma eval_quad {n : ℕ} (P : MvPolynomial (Fin n ⊕ Fin 0) ℝ) (x : Fin n → ℝ) (t : ℝ) :
    MvPolynomial.eval (Fin.snoc x t) (quad P) = t ^ 2 * eaEval (EAChain.nil n) P x - 1 := by
  unfold quad
  rw [MvPolynomial.eval_sub, MvPolynomial.eval_mul, MvPolynomial.eval_pow,
      MvPolynomial.eval_X, MvPolynomial.eval_C, Fin.snoc_last,
      MvPolynomial.eval_rename]
  rw [show (Fin.snoc x t ∘ Fin.castSucc) = x from Fin.snoc_comp_castSucc]
  rw [eaEval_nil_col]

/-- An equation of an EA polynomial is in `Gen`, with degree `atomDeg P` and format `n`. -/
lemma gen_eq_eaEval {n : ℕ} (P : MvPolynomial (Fin n ⊕ Fin 0) ℝ) :
    Gen n (atomDeg P) n {x : Fin n → ℝ | eaEval (EAChain.nil n) P x = 0} := by
  have h := Gen.hyp n (saCol P)
  have hle : (saCol P).totalDegree ≤ atomDeg P :=
    le_trans (MvPolynomial.totalDegree_rename_le _ _) (Nat.le_succ _)
  have hset : {x : Fin n → ℝ | MvPolynomial.eval x (saCol P) = 0} =
      {x : Fin n → ℝ | eaEval (EAChain.nil n) P x = 0} := by
    ext x
    change (MvPolynomial.eval x (saCol P) = 0) ↔ (eaEval (EAChain.nil n) P x = 0)
    rw [eaEval_nil_col]
  rw [hset] at h
  exact Work.WilE9.Gen.monoD hle h

/-- A strict inequality of an EA polynomial is in `Gen`, with degree `2 * atomDeg P` and format
`n + 2`: `∃ w, w ^ 2 * g = 1 ↔ g > 0`. -/
lemma gen_pos_eaEval {n : ℕ} (P : MvPolynomial (Fin n ⊕ Fin 0) ℝ) :
    Gen (n + 2) (2 * atomDeg P) n {x : Fin n → ℝ | 0 < eaEval (EAChain.nil n) P x} := by
  have hA : Gen (n + 1) (quad P).totalDegree (n + 1)
      {z : Fin (n + 1) → ℝ | MvPolynomial.eval z (quad P) = 0} := Gen.hyp (n + 1) (quad P)
  have hproj : Gen ((n + 1) + 1) (quad P).totalDegree n
      (projLast {z : Fin (n + 1) → ℝ | MvPolynomial.eval z (quad P) = 0}) := Gen.proj hA
  have hset : projLast {z : Fin (n + 1) → ℝ | MvPolynomial.eval z (quad P) = 0} =
      {x : Fin n → ℝ | 0 < eaEval (EAChain.nil n) P x} := by
    ext x
    show (∃ t : ℝ, MvPolynomial.eval (Fin.snoc x t) (quad P) = 0) ↔
      0 < eaEval (EAChain.nil n) P x
    constructor
    · rintro ⟨t, ht⟩
      rw [eval_quad] at ht
      have h1 : t ^ 2 * eaEval (EAChain.nil n) P x = 1 := by linarith
      have ht0 : t ≠ 0 := by
        intro h0
        rw [h0] at h1
        simp at h1
      have ht2 : 0 < t ^ 2 := pow_pos (abs_pos.mpr ht0) 2 |> fun h => by rwa [sq_abs] at h
      have hy : eaEval (EAChain.nil n) P x = 1 / t ^ 2 := by
        rw [eq_div_iff (ne_of_gt ht2)]
        linarith
      rw [hy]
      exact div_pos one_pos ht2
    · intro hy
      refine ⟨1 / Real.sqrt (eaEval (EAChain.nil n) P x), ?_⟩
      rw [eval_quad]
      have hsq : Real.sqrt (eaEval (EAChain.nil n) P x) ^ 2 = eaEval (EAChain.nil n) P x :=
        Real.sq_sqrt hy.le
      rw [div_pow, one_pow, hsq]
      rw [one_div, inv_mul_cancel₀ (ne_of_gt hy), sub_self]
  rw [hset] at hproj
  have hdeg : (quad P).totalDegree ≤ 2 * atomDeg P := by
    unfold quad
    rw [atomDeg]
    have h1 := MvPolynomial.totalDegree_sub_C_le
      (MvPolynomial.X (Fin.last n) ^ 2 * MvPolynomial.rename Fin.castSucc (saCol P)) (1 : ℝ)
    have h2 := MvPolynomial.totalDegree_mul
      (MvPolynomial.X (Fin.last n) ^ 2 : MvPolynomial (Fin (n + 1)) ℝ)
      (MvPolynomial.rename Fin.castSucc (saCol P))
    have h3 : (MvPolynomial.X (Fin.last n) ^ 2 : MvPolynomial (Fin (n + 1)) ℝ).totalDegree = 2 :=
      MvPolynomial.totalDegree_X_pow _ _
    have h4 : (MvPolynomial.rename Fin.castSucc (saCol P)).totalDegree ≤ P.totalDegree :=
      le_trans (MvPolynomial.totalDegree_rename_le _ _) (MvPolynomial.totalDegree_rename_le _ _)
    omega
  exact Work.WilE9.Gen.monoD hdeg hproj

/-! ## Basic sets and the DNF assembly -/

/-- A basic set of the DNF is in `Gen`, with format `n + 4` and degree `2 * B.deg`. -/
lemma gen_basic {n : ℕ} (B : Basic n 0) :
    Gen (n + 4) (2 * B.deg) n {x : Fin n → ℝ | B.holds (EAChain.nil n) x} := by
  have heq : Gen (n + 1) (B.eqs.map atomDeg).sum n
      (⋂ i : Fin B.eqs.length, {x : Fin n → ℝ | eaEval (EAChain.nil n) (B.eqs.get i) x = 0}) := by
    have h := Gen.inter (fun i : Fin B.eqs.length => atomDeg (B.eqs.get i))
      (fun i => {x : Fin n → ℝ | eaEval (EAChain.nil n) (B.eqs.get i) x = 0})
      (fun i => gen_eq_eaEval (B.eqs.get i))
    rwa [sum_get] at h
  have hpos : Gen ((n + 2) + 1) (2 * (B.pos.map atomDeg).sum) n
      (⋂ i : Fin B.pos.length, {x : Fin n → ℝ | 0 < eaEval (EAChain.nil n) (B.pos.get i) x}) := by
    have h := Gen.inter (fun i : Fin B.pos.length => 2 * atomDeg (B.pos.get i))
      (fun i => {x : Fin n → ℝ | 0 < eaEval (EAChain.nil n) (B.pos.get i) x})
      (fun i => gen_pos_eaEval (B.pos.get i))
    rwa [show (∑ i : Fin B.pos.length, 2 * atomDeg (B.pos.get i)) = 2 * (B.pos.map atomDeg).sum
      from by rw [← Finset.mul_sum, sum_get]] at h
  have hboth := Work.WilE9.Gen.inter₂ heq hpos
  have hset :
      (⋂ i : Fin B.eqs.length, {x : Fin n → ℝ | eaEval (EAChain.nil n) (B.eqs.get i) x = 0}) ∩
        (⋂ i : Fin B.pos.length, {x : Fin n → ℝ | 0 < eaEval (EAChain.nil n) (B.pos.get i) x}) =
      {x : Fin n → ℝ | B.holds (EAChain.nil n) x} := by
    ext x
    simp only [Set.mem_inter_iff, Set.mem_iInter, Set.mem_ofPred_eq, Basic.holds]
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨?_, ?_⟩
      · intro f hf
        obtain ⟨i, hi⟩ := List.mem_iff_get.mp hf
        rw [← hi]
        exact h1 i
      · intro g hg
        obtain ⟨i, hi⟩ := List.mem_iff_get.mp hg
        rw [← hi]
        exact h2 i
    · rintro ⟨h1, h2⟩
      exact ⟨fun i => h1 _ (List.get_mem _ _), fun i => h2 _ (List.get_mem _ _)⟩
  rw [hset] at hboth
  have hdeg : (B.eqs.map atomDeg).sum + 2 * (B.pos.map atomDeg).sum ≤ 2 * B.deg := by
    rw [Basic.deg, List.map_append, List.sum_append]
    omega
  exact Work.WilE9.Gen.mono (by omega) hdeg hboth

/-- **Every semialgebraic set is in `Gen`**, with constant format budget and degree bound linear
in the DNF-degree.  (Equations are `Gen.hyp`; a strict inequality `g > 0` is the projection of
`{w : w^2 g = 1}`; the DNF union costs nothing in format and adds degrees.) -/
theorem gen_SA (n : ℕ) : ∃ (a : ℕ) (b : Polynomial ℕ), ∀ (X : WilkiesDesign.E.SA n),
    WilkiesDesign.E.Gen a (b.eval X.deg) n X.set := by
  refine ⟨n + 4, Polynomial.C 2 * Polynomial.X, fun X => ?_⟩
  have h : Gen (n + 4) (∑ i : Fin X.basics.length, 2 * (X.basics.get i).deg) n
      (⋃ i : Fin X.basics.length,
        {x : Fin n → ℝ | (X.basics.get i).holds (EAChain.nil n) x}) :=
    Gen.union (fun i : Fin X.basics.length => 2 * (X.basics.get i).deg)
      (fun i => {x : Fin n → ℝ | (X.basics.get i).holds (EAChain.nil n) x})
      (fun i => gen_basic (X.basics.get i))
  have hset : (⋃ i : Fin X.basics.length,
        {x : Fin n → ℝ | (X.basics.get i).holds (EAChain.nil n) x}) = X.set := by
    ext x
    simp only [Set.mem_iUnion, Set.mem_ofPred_eq, SA.set]
    constructor
    · rintro ⟨i, hi⟩
      exact ⟨X.basics.get i, List.get_mem _ _, hi⟩
    · rintro ⟨B, hB, hx⟩
      obtain ⟨i, hi⟩ := List.mem_iff_get.mp hB
      exact ⟨i, by rw [hi]; exact hx⟩
  rw [hset] at h
  have hdeg : (∑ i : Fin X.basics.length, 2 * (X.basics.get i).deg) = 2 * X.deg := by
    rw [← Finset.mul_sum, sum_get]
    rfl
  rw [hdeg] at h
  have hb : (Polynomial.C 2 * Polynomial.X).eval X.deg = 2 * X.deg := by simp
  rw [hb]
  exact h

end Work.WilE9.Gen
