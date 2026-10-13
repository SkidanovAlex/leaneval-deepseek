import Mathlib
import Submission.Work.WilE9.Ift.OneShotDefs

namespace Work.WilE9.Ift.OneShot

open WilkiesDesign WilkiesDesign.E

/-! ## The point set of the one-shot construction

`oneShotSet c F L Y` is the semi-Pfaffian set over the concatenated chain
`EAChain.cat (EAChain.extend (oneShotInj n m) Y.c) (EAChain.extend (oneShotInj n m) c)`,
whose disjuncts are built from a disjunct `B` of `Y` and the single new equation
`z * Q ^ (2|L|) - P_L = 0` (`oneShotEq`), the new condition being conjoined to every
disjunct of `Y` (`Work.WilE5.conj`).  The purpose of this file is the semantic
counterpart of that construction: the point set of `oneShotSet c F L Y` is exactly the
set of `p` in the cube whose projection to the old coordinates lies in `Y.set` and
which satisfies the new equation.

The mathematical content is entirely a matter of *evaluation*: the extended polynomial
`EAPoly.extend (oneShotInj n m) Q` evaluates at `p` as `Q` does at `p ∘ oneShotInj`
(`extend_eaEval_inj`), and the concatenated chain separates into its two halves
(`eaEval_cat_inl` / `eaEval_cat_inr`, `Basic.holds_cat_inl` / `Basic.holds_cat_inr`).
The only genuine computation is `oneShotEq_eval` below, where the new coordinate `z`
appears *not* in the image of `oneShotInj` and therefore has to be evaluated by hand. -/

/-- Evaluation of the single new equation `z * Q^(2|L|) - P_L` of the one-shot
construction: the variable `z` at position `oneShotNew n m` contributes `p (oneShotNew n m)`
while the two extended polynomials contribute the evaluation of `Q = jQ c F` and
`P_L = iftP c F 0 L` at the old coordinates `p ∘ oneShotInj`. -/
lemma oneShotEq_eval {n m r : ℕ} (c : EAChain (n + (1 + m)) r)
    (F : Fin (1 + m) → EAPoly (n + (1 + m)) r) (L : List (Fin n))
    (p : Fin (n + 1 + (1 + m)) → ℝ) :
    eaEval (Work.WilE8.EAChain.extend (oneShotInj n m) c) (oneShotEq c F L) p =
      p (oneShotNew n m) *
          (eaEval c (Work.WilE9.jQ c F) (fun i => p (oneShotInj n m i))) ^ (2 * L.length)
        - eaEval c (Work.WilE9.iftP c F (0 : Fin (1 + m)) L)
            (fun i => p (oneShotInj n m i)) := by
  have hinj := oneShotInj_injective n m
  -- The evaluation functional of the extended chain agrees with that of `c` on the range of
  -- `oneShotInj`, and the `exp`-atoms are exactly the atoms of `c` (`extend_ell_inj`).
  have hfun : (Sum.elim p fun j =>
        Real.exp ((Work.WilE8.EAChain.extend (oneShotInj n m) c).ell j p)) ∘
        (Sum.map (oneShotInj n m) id) =
      (Sum.elim (fun i => p (oneShotInj n m i)) fun j =>
        Real.exp (c.ell j fun i => p (oneShotInj n m i))) := by
    funext v
    rcases v with i | j
    · rfl
    · simp only [Function.comp_apply, Sum.map_inr, Sum.elim_inr, id_eq]
      rw [Work.WilE8.Extend.extend_ell_inj hinj c j p]
  unfold oneShotEq eaEval Work.WilE8.EAPoly.extend
  rw [MvPolynomial.eval_sub, MvPolynomial.eval_mul, MvPolynomial.eval_pow, MvPolynomial.eval_X,
      MvPolynomial.eval_rename, MvPolynomial.eval_rename, hfun]
  rfl

/-- The single new basic condition `z * Q^(2|L|) - P_L = 0` holds at `p` exactly when `p`
satisfies the new equation in the form used by `oneShotTarget`. -/
lemma oneShotBasic_holds {n m r : ℕ} (c : EAChain (n + (1 + m)) r)
    (F : Fin (1 + m) → EAPoly (n + (1 + m)) r) (L : List (Fin n))
    (p : Fin (n + 1 + (1 + m)) → ℝ) :
    (oneShotBasic c F L).holds (Work.WilE8.EAChain.extend (oneShotInj n m) c) p ↔
      p (oneShotNew n m) *
          (eaEval c (Work.WilE9.jQ c F) (fun i => p (oneShotInj n m i))) ^ (2 * L.length)
        = eaEval c (Work.WilE9.iftP c F (0 : Fin (1 + m)) L)
            (fun i => p (oneShotInj n m i)) := by
  simp only [oneShotBasic, Basic.holds, List.mem_nil_iff, IsEmpty.forall_iff, forall_const,
    List.mem_cons, or_false, forall_eq, and_true]
  rw [oneShotEq_eval c F L p]
  exact sub_eq_zero

/-- A disjunct of `oneShotSet c F L Y` holds at `p` exactly when some disjunct `B` of `Y`
holds at the old coordinates `p ∘ oneShotInj` and `p` satisfies the new equation. -/
lemma oneShot_mem_basics {n m r : ℕ} (c : EAChain (n + (1 + m)) r)
    (F : Fin (1 + m) → EAPoly (n + (1 + m)) r) (L : List (Fin n))
    (Y : SemiPf (n + (1 + m))) (p : Fin (n + 1 + (1 + m)) → ℝ) :
    (∃ A ∈ Y.basics.map (fun B => Work.WilE5.conj
        (Work.WilE7.Basic.inl (Work.WilE8.Basic.extend (oneShotInj n m) B))
        (Work.WilE7.Basic.inr (oneShotBasic c F L))),
      A.holds (oneShotChain c Y) p) ↔
      (∃ B ∈ Y.basics, B.holds Y.c (fun i => p (oneShotInj n m i))) ∧
      (p (oneShotNew n m) *
          (eaEval c (Work.WilE9.jQ c F) (fun i => p (oneShotInj n m i))) ^ (2 * L.length)
        = eaEval c (Work.WilE9.iftP c F (0 : Fin (1 + m)) L)
            (fun i => p (oneShotInj n m i))) := by
  constructor
  · rintro ⟨A, hA, hAh⟩
    obtain ⟨B, hB, rfl⟩ := List.mem_map.mp hA
    unfold oneShotChain at hAh
    rw [Work.WilE5.conj_holds] at hAh
    obtain ⟨h1, h2⟩ := hAh
    rw [Work.WilE7.SubPfAux.Basic.holds_cat_inl] at h1
    rw [Work.WilE7.SubPfAux.Basic.holds_cat_inr] at h2
    rw [Work.WilE8.Extend.extend_basic_holds_inj (oneShotInj_injective n m)] at h1
    exact ⟨⟨B, hB, h1⟩, (oneShotBasic_holds c F L p).mp h2⟩
  · rintro ⟨⟨B, hB, h1⟩, h2⟩
    refine ⟨Work.WilE5.conj (Work.WilE7.Basic.inl (Work.WilE8.Basic.extend (oneShotInj n m) B))
      (Work.WilE7.Basic.inr (oneShotBasic c F L)), List.mem_map.mpr ⟨B, hB, rfl⟩, ?_⟩
    unfold oneShotChain
    rw [Work.WilE5.conj_holds]
    refine ⟨?_, ?_⟩
    · rw [Work.WilE7.SubPfAux.Basic.holds_cat_inl,
        Work.WilE8.Extend.extend_basic_holds_inj (oneShotInj_injective n m)]
      exact h1
    · rw [Work.WilE7.SubPfAux.Basic.holds_cat_inr]
      exact (oneShotBasic_holds c F L p).mpr h2

/-- The point set of the semi-Pfaffian set of the one-shot construction: the lifted `Y`
(intersected with the cube, in the new coordinate) together with the single new equation. -/
theorem oneShotSet_set {n m r : ℕ} (c : WilkiesDesign.E.EAChain (n + (1 + m)) r)
    (F : Fin (1 + m) → WilkiesDesign.E.EAPoly (n + (1 + m)) r) (L : List (Fin n))
    (Y : WilkiesDesign.E.SemiPf (n + (1 + m))) :
    (Work.WilE9.Ift.oneShotSet c F L Y).set =
      {p : Fin (n + 1 + (1 + m)) → ℝ |
        p ∈ WilkiesDesign.E.cubeC (n + 1 + (1 + m)) ∧
        (fun i => p (Work.WilE9.Ift.oneShotInj n m i)) ∈ Y.set ∧
        p (Work.WilE9.Ift.oneShotNew n m) *
            (WilkiesDesign.E.eaEval c (Work.WilE9.jQ c F)
              (fun i => p (Work.WilE9.Ift.oneShotInj n m i))) ^ (2 * L.length) =
          WilkiesDesign.E.eaEval c (Work.WilE9.iftP c F (0 : Fin (1 + m)) L)
            (fun i => p (Work.WilE9.Ift.oneShotInj n m i))} := by
  ext p
  -- Unfold the two point sets (`oneShotSet` is `mkSemiPf` over the concatenated chain, whose
  -- `r`-field must be computed before the membership instances are elaborated).
  rw [show (oneShotSet c F L Y).set = {q : Fin (n + 1 + (1 + m)) → ℝ |
      q ∈ cubeC (n + 1 + (1 + m)) ∧
      ∃ A ∈ Y.basics.map (fun B => Work.WilE5.conj
        (Work.WilE7.Basic.inl (Work.WilE8.Basic.extend (oneShotInj n m) B))
        (Work.WilE7.Basic.inr (oneShotBasic c F L))),
        A.holds (oneShotChain c Y) q} from rfl]
  rw [show Y.set = {x : Fin (n + (1 + m)) → ℝ |
      x ∈ cubeC (n + (1 + m)) ∧ ∃ B ∈ Y.basics, B.holds Y.c x} from rfl]
  simp only [Set.mem_ofPred_eq, oneShot_mem_basics c F L Y p]
  constructor
  · rintro ⟨hc, hP, hAp⟩
    exact ⟨hc, ⟨fun i => hc (oneShotInj n m i), hP⟩, hAp⟩
  · rintro ⟨hc, ⟨_, hP⟩, hAp⟩
    exact ⟨hc, hP, hAp⟩

end Work.WilE9.Ift.OneShot
