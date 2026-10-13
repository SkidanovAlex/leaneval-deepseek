/-
  The constraint polynomial `constrPoly c L B` is the sum of the squares of the seven blocks of
  "atoms" describing a branch `B` of the restricted semi-Pfaffian encoding (the `u`-relation, the
  `v`-relation, the `w`-bound, the definition of `t_j = ell_j z / L_j`, the `t`-bound, the equations
  of the branch, and its positivity atoms).

  Being a sum of squares of real numbers, its value at a point `p` vanishes exactly when every atom
  vanishes.  This file proves that decomposition, together with the evaluation of each atom, and
  assembles the equivalence `constrPoly_iff`.
-/
import Mathlib
import Submission.Work.WilE10.SubPfRexp.Defs

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open Classical

namespace Work.WilE10.SubPfRexp

open WilkiesDesign WilkiesDesign.E
open Work.WilC0 (rexpEval RExPoly RExpExistI)

variable {n m r : ℕ}

/-! ## Sums of squares -/

/-- A sum of squares of real values vanishes iff every summand vanishes. -/
theorem cp_sum_sq_eq_zero {κ : Type} (p : κ → ℝ) {ι : Type} [Fintype ι]
    (g : ι → MvPolynomial (κ ⊕ κ) ℝ) :
    rexpEval p (∑ i, g i ^ 2) = 0 ↔ ∀ i, rexpEval p (g i) = 0 := by
  have h : rexpEval p (∑ i, g i ^ 2) = ∑ i, (rexpEval p (g i)) ^ 2 := by
    simp only [rexpEval, map_sum, map_pow]
  rw [h, Finset.sum_eq_zero_iff_of_nonneg (fun i _ => sq_nonneg _)]
  simp

/-- The constraint polynomial vanishes iff every atom vanishes. -/
theorem cp_constrPoly_eq_zero_iff (c : EAChain (n + m) r) (L : Fin r → ℕ)
    (B : Basic (n + m) r) (p : Fin n ⊕ Wit n m r B.pos.length → ℝ) :
    rexpEval p (constrPoly c L B) = 0 ↔
      ∀ k : ConstrIdx n m r B, rexpEval p (constrAtom c L B k) = 0 := by
  show rexpEval p (∑ k : ConstrIdx n m r B, constrAtom c L B k ^ 2) = 0 ↔ _
  exact cp_sum_sq_eq_zero p (constrAtom c L B)

/-! ## Splitting the universal quantifier over the index of the constraints -/

/-- The seven blocks of the constraint index, in order. -/
theorem cp_forall_constrIdx (c : EAChain (n + m) r) (L : Fin r → ℕ) (B : Basic (n + m) r)
    (p : Fin n ⊕ Wit n m r B.pos.length → ℝ) :
    (∀ k : ConstrIdx n m r B, rexpEval p (constrAtom c L B k) = 0) ↔
      (∀ a : Fin n, rexpEval p (constrAtom c L B (Sum.inl a)) = 0) ∧
      (∀ a : Fin n, rexpEval p (constrAtom c L B (Sum.inr (Sum.inl a))) = 0) ∧
      (∀ b : Fin m, rexpEval p (constrAtom c L B (Sum.inr (Sum.inr (Sum.inl b)))) = 0) ∧
      (∀ j : Fin r,
        rexpEval p (constrAtom c L B (Sum.inr (Sum.inr (Sum.inr (Sum.inl j))))) = 0) ∧
      (∀ j : Fin r,
        rexpEval p (constrAtom c L B (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl j))))))
          = 0) ∧
      (∀ k : Fin B.eqs.length,
        rexpEval p (constrAtom c L B (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr
          (Sum.inl k))))))) = 0) ∧
      (∀ l : Fin B.pos.length,
        rexpEval p (constrAtom c L B (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr
          l))))))) = 0) := by
  simp only [ConstrIdx, Sum.forall]

/-! ## Evaluation of the atoms -/

theorem cp_atom_u (c : EAChain (n + m) r) (L : Fin r → ℕ) (B : Basic (n + m) r)
    (p : Fin n ⊕ Wit n m r B.pos.length → ℝ) (a : Fin n) :
    rexpEval p (constrAtom c L B (Sum.inl a)) =
      p (Sum.inr (Wit.uIdx a)) ^ 2 * (1 + p (Sum.inl a) ^ 2) - p (Sum.inl a) ^ 2 := by
  simp [constrAtom, Xc]

theorem cp_atom_v (c : EAChain (n + m) r) (L : Fin r → ℕ) (B : Basic (n + m) r)
    (p : Fin n ⊕ Wit n m r B.pos.length → ℝ) (a : Fin n) :
    rexpEval p (constrAtom c L B (Sum.inr (Sum.inl a))) =
      p (Sum.inr (Wit.uIdx a)) * p (Sum.inl a) - p (Sum.inr (Wit.vIdx a)) ^ 2 := by
  simp [constrAtom, Xc]

theorem cp_atom_w (c : EAChain (n + m) r) (L : Fin r → ℕ) (B : Basic (n + m) r)
    (p : Fin n ⊕ Wit n m r B.pos.length → ℝ) (b : Fin m) :
    rexpEval p (constrAtom c L B (Sum.inr (Sum.inr (Sum.inl b)))) =
      1 - p (Sum.inr (Wit.wIdx b)) ^ 2 - p (Sum.inr (Wit.qqIdx b)) ^ 2 := by
  simp [constrAtom, Xc]

theorem cp_atom_t (c : EAChain (n + m) r) (L : Fin r → ℕ) (B : Basic (n + m) r)
    (p : Fin n ⊕ Wit n m r B.pos.length → ℝ) (j : Fin r) :
    rexpEval p (constrAtom c L B (Sum.inr (Sum.inr (Sum.inr (Sum.inl j))))) =
      (L j : ℝ) * p (Sum.inr (Wit.tIdx j)) -
        c.ell j (fun i => p (coordIdx (P := B.pos.length) i)) := by
  simp [constrAtom, Xc, ellPoly, EAChain.ell, rexpEval]

theorem cp_atom_s (c : EAChain (n + m) r) (L : Fin r → ℕ) (B : Basic (n + m) r)
    (p : Fin n ⊕ Wit n m r B.pos.length → ℝ) (j : Fin r) :
    rexpEval p (constrAtom c L B (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl j)))))) =
      1 - p (Sum.inr (Wit.tIdx j)) ^ 2 - p (Sum.inr (Wit.sIdx j)) ^ 2 := by
  simp [constrAtom, Xc]

theorem cp_atom_e (c : EAChain (n + m) r) (L : Fin r → ℕ) (B : Basic (n + m) r)
    (p : Fin n ⊕ Wit n m r B.pos.length → ℝ) (k : Fin B.eqs.length) :
    rexpEval p (constrAtom c L B (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr
        (Sum.inl k))))))) = rexpEval p (subst c L (B.eqs.get k)) := by
  simp [constrAtom]

theorem cp_atom_p (c : EAChain (n + m) r) (L : Fin r → ℕ) (B : Basic (n + m) r)
    (p : Fin n ⊕ Wit n m r B.pos.length → ℝ) (l : Fin B.pos.length) :
    rexpEval p (constrAtom c L B (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr
        l))))))) = rexpEval p (subst c L (B.pos.get l)) * p (Sum.inr (Wit.pwIdx l)) ^ 2 - 1 := by
  simp [constrAtom, Xc]

/-! ## The main equivalence -/

theorem constrPoly_iff {n m r : ℕ} (c : WilkiesDesign.E.EAChain (n + m) r)
    (L : Fin r → ℕ) (B : WilkiesDesign.E.Basic (n + m) r)
    (p : Fin n ⊕ Work.WilE10.SubPfRexp.Wit n m r B.pos.length → ℝ) :
    Work.WilC0.rexpEval p (Work.WilE10.SubPfRexp.constrPoly c L B) = 0 ↔
      (∀ a : Fin n, p (Sum.inr (Work.WilE10.SubPfRexp.Wit.uIdx a)) ^ 2 *
          (1 + p (Sum.inl a) ^ 2) - p (Sum.inl a) ^ 2 = 0) ∧
      (∀ a : Fin n, p (Sum.inr (Work.WilE10.SubPfRexp.Wit.uIdx a)) * p (Sum.inl a) -
          p (Sum.inr (Work.WilE10.SubPfRexp.Wit.vIdx a)) ^ 2 = 0) ∧
      (∀ b : Fin m, 1 - p (Sum.inr (Work.WilE10.SubPfRexp.Wit.wIdx b)) ^ 2 -
          p (Sum.inr (Work.WilE10.SubPfRexp.Wit.qqIdx b)) ^ 2 = 0) ∧
      (∀ j : Fin r, (L j : ℝ) * p (Sum.inr (Work.WilE10.SubPfRexp.Wit.tIdx j)) -
          c.ell j (fun i => p (Work.WilE10.SubPfRexp.coordIdx (P := B.pos.length) i)) = 0) ∧
      (∀ j : Fin r, 1 - p (Sum.inr (Work.WilE10.SubPfRexp.Wit.tIdx j)) ^ 2 -
          p (Sum.inr (Work.WilE10.SubPfRexp.Wit.sIdx j)) ^ 2 = 0) ∧
      (∀ k : Fin B.eqs.length,
          Work.WilC0.rexpEval p (Work.WilE10.SubPfRexp.subst c L (B.eqs.get k)) = 0) ∧
      (∀ l : Fin B.pos.length,
          Work.WilC0.rexpEval p (Work.WilE10.SubPfRexp.subst c L (B.pos.get l)) *
            p (Sum.inr (Work.WilE10.SubPfRexp.Wit.pwIdx l)) ^ 2 - 1 = 0) := by
  rw [cp_constrPoly_eq_zero_iff, cp_forall_constrIdx]
  simp only [cp_atom_u, cp_atom_v, cp_atom_w, cp_atom_t, cp_atom_s, cp_atom_e, cp_atom_p]

end Work.WilE10.SubPfRexp
