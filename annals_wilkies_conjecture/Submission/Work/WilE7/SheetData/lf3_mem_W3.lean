import Mathlib
import Submission.Work.WilE7.SheetData.NonstrictLevelFibre

set_option autoImplicit false
noncomputable section
open Classical
open scoped BigOperators

namespace Work.WilE7.SheetData

open WilkiesConjecture WilkiesDesign WilkiesDesign.E
open Work.WilE7.LevelFibre

/-! ## §1. The atom lists `lf3Eqs`, `lf3SlackEqs` in coordinates

These are the analogues, for the non-strict construction, of `mem_lfEqs` / `mem_lfPoss` in
`Work.WilE7.LevelFibre.lf_mem_W2`. -/

/-- Membership in the base atoms `lf3Eqs`: the atoms are exactly
`X (lf3BIdx l (castAdd (q+1) a)) - X (lf3XIdx a)`. -/
theorem mem_lf3Eqs {p q M k : ℕ} (Q : MvPolynomial (Fin (lfD p (q + 1) M k)) ℝ) :
    Q ∈ lf3Eqs (p := p) (q := q) (M := M) (k := k) ↔
      ∃ (l : Fin k) (a : Fin p),
        Q = MvPolynomial.X (lf3BIdx l (Fin.castAdd (q + 1) a)) - MvPolynomial.X (lf3XIdx a) := by
  constructor
  · intro h
    obtain ⟨la, hla, hQ⟩ := List.mem_map.mp h
    obtain ⟨hl, ha⟩ := List.mem_product.mp hla
    exact ⟨la.1, la.2, hQ.symm⟩
  · rintro ⟨l, a, rfl⟩
    exact List.mem_map.mpr ⟨(l, a),
      List.mem_product.mpr ⟨List.mem_finRange l, List.mem_finRange a⟩, rfl⟩

/-- Membership in the slack atoms `lf3SlackEqs`: the atoms are exactly
`X (z_{l+1} level) - X (z_l level) - C 1 - X (ε_l)` for `l : Fin (k-1)`. -/
theorem mem_lf3SlackEqs {p q M k : ℕ} (j : Fin q)
    (Q : MvPolynomial (Fin (lfD p (q + 1) M k)) ℝ) :
    Q ∈ lf3SlackEqs (p := p) (q := q) (M := M) (k := k) j ↔
      ∃ (l : Fin (k - 1)),
        Q = MvPolynomial.X (lf3LvIdx j ⟨l.val + 1, by omega⟩) -
          MvPolynomial.X (lf3LvIdx j ⟨l.val, by omega⟩) - MvPolynomial.C 1 -
          MvPolynomial.X (lf3SlkIdx ⟨l.val, by omega⟩) := by
  constructor
  · intro h
    obtain ⟨l, hl, hQ⟩ := List.mem_map.mp h
    exact ⟨l, hQ.symm⟩
  · rintro ⟨l, rfl⟩
    exact List.mem_map.mpr ⟨l, List.mem_finRange l, rfl⟩

/-- The `lf3Eqs`-condition of `addAtoms`, in coordinates. -/
theorem forall_mem_lf3Eqs {p q M k r : ℕ} (c : EAChain (lfD p (q + 1) M k) r)
    (U : Fin (lfD p (q + 1) M k) → ℝ) :
    (∀ Q ∈ lf3Eqs (p := p) (q := q) (M := M) (k := k), eaEval c (eaEmbed Q) U = 0) ↔
      (∀ (l : Fin k) (a : Fin p), U (lf3BIdx l (Fin.castAdd (q + 1) a)) = U (lf3XIdx a)) := by
  constructor
  · intro h l a
    have hmem := (mem_lf3Eqs (p := p) (q := q) (M := M) (k := k)
      (MvPolynomial.X (lf3BIdx l (Fin.castAdd (q + 1) a)) - MvPolynomial.X (lf3XIdx a))).mpr
      ⟨l, a, rfl⟩
    have := h _ hmem
    rwa [eaEval_eaEmbed, MvPolynomial.eval_sub, MvPolynomial.eval_X, MvPolynomial.eval_X,
      sub_eq_zero] at this
  · intro h Q hQ
    obtain ⟨l, a, hQ'⟩ := (mem_lf3Eqs (p := p) (q := q) (M := M) (k := k) Q).mp hQ
    rw [hQ', eaEval_eaEmbed, MvPolynomial.eval_sub, MvPolynomial.eval_X, MvPolynomial.eval_X,
      sub_eq_zero]
    exact h l a

/-- The `lf3SlackEqs`-condition of `addAtoms`, in coordinates. -/
theorem forall_mem_lf3SlackEqs {p q M k r : ℕ} (c : EAChain (lfD p (q + 1) M k) r)
    (j : Fin q) (U : Fin (lfD p (q + 1) M k) → ℝ) :
    (∀ Q ∈ lf3SlackEqs (p := p) (q := q) (M := M) (k := k) j, eaEval c (eaEmbed Q) U = 0) ↔
      (∀ l : Fin (k - 1),
        U (lf3LvIdx j ⟨l.val + 1, by omega⟩) - U (lf3LvIdx j ⟨l.val, by omega⟩) - 1 -
          U (lf3SlkIdx ⟨l.val, by omega⟩) = 0) := by
  constructor
  · intro h l
    have hmem := (mem_lf3SlackEqs (p := p) (q := q) (M := M) (k := k) j
      (MvPolynomial.X (lf3LvIdx j ⟨l.val + 1, by omega⟩) -
          MvPolynomial.X (lf3LvIdx j ⟨l.val, by omega⟩) - MvPolynomial.C 1 -
          MvPolynomial.X (lf3SlkIdx ⟨l.val, by omega⟩))).mpr ⟨l, rfl⟩
    have := h _ hmem
    rw [eaEval_eaEmbed, MvPolynomial.eval_sub, MvPolynomial.eval_sub, MvPolynomial.eval_sub,
      MvPolynomial.eval_X, MvPolynomial.eval_X, MvPolynomial.eval_C, MvPolynomial.eval_X] at this
    simpa using this
  · intro h Q hQ
    obtain ⟨l, hQ'⟩ := (mem_lf3SlackEqs (p := p) (q := q) (M := M) (k := k) j Q).mp hQ
    rw [hQ', eaEval_eaEmbed, MvPolynomial.eval_sub, MvPolynomial.eval_sub, MvPolynomial.eval_sub,
      MvPolynomial.eval_X, MvPolynomial.eval_X, MvPolynomial.eval_C, MvPolynomial.eval_X]
    simpa using h l

/-! ## §2. The point set of `lfW3` -/

theorem lf3_mem_W3 {p q M k : ℕ} (j : Fin q) (X : WilkiesDesign.E.SemiPf (p + q))
    (XC : WilkiesDesign.E.SemiPf (p + M))
    (U : Fin (Work.WilE7.LevelFibre.lfD p (q + 1) M k) → ℝ) :
    U ∈ (Work.WilE7.SheetData.lfW3 j X XC).set ↔
      WilkiesDesign.E.projFirst (p + M) ((p + (q + 1)) * k) U ∈ XC.set ∧
      (∀ l : Fin k,
        WilkiesDesign.E.projFirst (p + q) 1
          (Work.WilE7.LevelFibre.blk (WilkiesDesign.E.projSnd (p + M) ((p + (q + 1)) * k) U) l)
          ∈ X.set) ∧
      (∀ l : Fin k,
        WilkiesDesign.E.projSnd (p + q) 1
          (Work.WilE7.LevelFibre.blk (WilkiesDesign.E.projSnd (p + M) ((p + (q + 1)) * k) U) l)
          ∈ WilkiesDesign.E.cubeC 1) ∧
      (∀ (l : Fin k) (a : Fin p),
        U (Work.WilE7.SheetData.lf3BIdx l (Fin.castAdd (q + 1) a))
          = U (Work.WilE7.SheetData.lf3XIdx a)) ∧
      (∀ l : Fin (k - 1),
        U (Work.WilE7.SheetData.lf3LvIdx j ⟨l.val + 1, by omega⟩) -
          U (Work.WilE7.SheetData.lf3LvIdx j ⟨l.val, by omega⟩) - 1 -
          U (Work.WilE7.SheetData.lf3SlkIdx ⟨l.val, by omega⟩) = 0) ∧
      (0 < MvPolynomial.eval U
        (Work.WilE7.SheetData.lf3DistAtom (p := p) (q := q) (M := M) (k := k))) := by
  have hE := forall_mem_lf3Eqs (c := (lfW1 (q := q + 1) (lfBlk p q X) XC).c) (U := U)
  have hS := forall_mem_lf3SlackEqs (c := (lfW1 (q := q + 1) (lfBlk p q X) XC).c) (j := j) (U := U)
  -- `lfW1` is the product `XC × (lfBlk p q X)^k`; identify its point set with the product set.
  have h1 : (lfW1 (q := q + 1) (lfBlk p q X) XC).set =
      (Work.WilE7.SemiPf.prod XC
        (Work.WilE7.LevelFibre.SemiPf.blocks (lfBlk p q X) k)).set := rfl
  have hprod : (Work.WilE7.SemiPf.prod XC
        (Work.WilE7.LevelFibre.SemiPf.blocks (lfBlk p q X) k)).set =
      {z : Fin (lfD p (q + 1) M k) → ℝ |
        WilkiesDesign.E.projFirst (p + M) ((p + (q + 1)) * k) z ∈ XC.set ∧
        WilkiesDesign.E.projSnd (p + M) ((p + (q + 1)) * k) z ∈
          (Work.WilE7.LevelFibre.SemiPf.blocks (lfBlk p q X) k).set} :=
    Work.WilE7.prodSet XC (Work.WilE7.LevelFibre.SemiPf.blocks (lfBlk p q X) k)
  rw [lfW3, addAtoms_set]
  simp only [Set.mem_inter_iff, Set.mem_ofPred_eq]
  rw [List.forall_mem_map, List.forall_mem_append, hE, hS, h1, hprod,
    blocks_set (lfBlk p q X) k]
  simp only [Set.mem_ofPred_eq, forall_and, lfBlk_set, List.mem_singleton, forall_eq,
    eaEval_eaEmbed]
  tauto

end Work.WilE7.SheetData
