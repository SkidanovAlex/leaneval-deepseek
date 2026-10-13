/-
  Area E7: the point set of the semi-Pfaffian set `lfW2` (`Work.WilE7.LevelFibre.lf_mem_W2`).

  `lfW2 j X XC` is the product `XC × X^k` in the layout `(x, w, blocks)` of `ℝ^{lfD p q M k}`,
  cut by the polynomial (semialgebraic) atoms

  * `z_l (castAdd q a) = x_a` for `l : Fin k`, `a : Fin p`   (`lfEqs`),
  * `z_l (level j) < z_l' (level j)` for `l < l'`             (`lfPoss`).

  This file computes its point set.  The two `∀ f ∈ atoms` conditions produced by
  `addAtoms_set` are turned into the coordinatewise equations/inequalities of the statement
  (`forall_mem_lfEqs`, `forall_mem_lfPoss`, via `mem_lfEqs`, `mem_lfPoss`), and the product
  `lfW1 X XC = SemiPf.prod XC (SemiPf.blocks X k)` is split with `prodSet` and `blocks_set`.
-/
import Mathlib
import Submission.Work.WilE7.LevelFibre.lfDefs
import Submission.Work.WilE7.LevelFibre.blocks_set

set_option autoImplicit false
noncomputable section
open Classical
open WilkiesConjecture WilkiesDesign WilkiesDesign.E

namespace Work.WilE7.LevelFibre

/-! ## §1. The two atom lists, in coordinates -/

/-- Membership in the equation atoms `lfEqs`: the atoms are exactly
`X (lfBIdx l (castAdd q a)) - X (lfXIdx a)`. -/
theorem mem_lfEqs {p q M k : ℕ} (Q : MvPolynomial (Fin (lfD p q M k)) ℝ) :
    Q ∈ lfEqs (p := p) (q := q) (M := M) (k := k) ↔
      ∃ (l : Fin k) (a : Fin p),
        Q = MvPolynomial.X (lfBIdx l (Fin.castAdd q a)) - MvPolynomial.X (lfXIdx a) := by
  constructor
  · intro h
    obtain ⟨la, hla, hQ⟩ := List.mem_map.mp h
    obtain ⟨hl, ha⟩ := List.mem_product.mp hla
    exact ⟨la.1, la.2, hQ.symm⟩
  · rintro ⟨l, a, rfl⟩
    exact List.mem_map.mpr ⟨(l, a),
      List.mem_product.mpr ⟨List.mem_finRange l, List.mem_finRange a⟩, rfl⟩

/-- Membership in the inequality atoms `lfPoss`: the atoms are exactly
`X (lfLvIdx j l') - X (lfLvIdx j l)` for `l < l'`. -/
theorem mem_lfPoss {p q M k : ℕ} (j : Fin q) (P : MvPolynomial (Fin (lfD p q M k)) ℝ) :
    P ∈ lfPoss (p := p) (q := q) (M := M) (k := k) j ↔
      ∃ (l l' : Fin k), l < l' ∧
        P = MvPolynomial.X (lfLvIdx (p := p) (M := M) j l') -
          MvPolynomial.X (lfLvIdx (p := p) (M := M) j l) := by
  constructor
  · intro h
    obtain ⟨ll, hll, hf⟩ := List.mem_filterMap.mp h
    obtain ⟨hl, hl'⟩ := List.mem_product.mp hll
    by_cases hlt : ll.1 < ll.2
    · rw [ite_eq_left hlt] at hf
      exact ⟨ll.1, ll.2, hlt, (Option.some.inj hf).symm⟩
    · rw [ite_eq_right hlt] at hf
      exact absurd hf (by simp)
  · rintro ⟨l, l', hlt, rfl⟩
    refine List.mem_filterMap.mpr ⟨(l, l'),
      List.mem_product.mpr ⟨List.mem_finRange l, List.mem_finRange l'⟩, ?_⟩
    simp only [hlt, ↓reduceIte]

/-- The `lfEqs`-condition of `addAtoms`, in coordinates. -/
theorem forall_mem_lfEqs {p q M k r : ℕ} (c : EAChain (lfD p q M k) r)
    (U : Fin (lfD p q M k) → ℝ) :
    (∀ f ∈ (lfEqs (p := p) (q := q) (M := M) (k := k)).map (@eaEmbed (lfD p q M k) r),
        eaEval c f U = 0) ↔
      (∀ (l : Fin k) (a : Fin p), U (lfBIdx l (Fin.castAdd q a)) = U (lfXIdx a)) := by
  rw [List.forall_mem_map]
  constructor
  · intro h l a
    have hmem := (mem_lfEqs (p := p) (q := q) (M := M) (k := k)
      (MvPolynomial.X (lfBIdx l (Fin.castAdd q a)) - MvPolynomial.X (lfXIdx a))).mpr
      ⟨l, a, rfl⟩
    have := h _ hmem
    rwa [eaEval_eaEmbed, MvPolynomial.eval_sub, MvPolynomial.eval_X, MvPolynomial.eval_X,
      sub_eq_zero] at this
  · intro h Q hQ
    obtain ⟨l, a, hQ'⟩ := (mem_lfEqs (p := p) (q := q) (M := M) (k := k) Q).mp hQ
    rw [hQ', eaEval_eaEmbed, MvPolynomial.eval_sub, MvPolynomial.eval_X, MvPolynomial.eval_X,
      sub_eq_zero]
    exact h l a

/-- The `lfPoss`-condition of `addAtoms`, in coordinates. -/
theorem forall_mem_lfPoss {p q M k r : ℕ} (c : EAChain (lfD p q M k) r) (j : Fin q)
    (U : Fin (lfD p q M k) → ℝ) :
    (∀ f ∈ (lfPoss (p := p) (q := q) (M := M) (k := k) j).map (@eaEmbed (lfD p q M k) r),
        0 < eaEval c f U) ↔
      (∀ l l' : Fin k, l < l' → U (lfLvIdx j l) < U (lfLvIdx j l')) := by
  rw [List.forall_mem_map]
  constructor
  · intro h l l' hlt
    have hmem := (mem_lfPoss (p := p) (q := q) (M := M) (k := k) j
      (MvPolynomial.X (lfLvIdx j l') - MvPolynomial.X (lfLvIdx j l))).mpr ⟨l, l', hlt, rfl⟩
    have := h _ hmem
    rwa [eaEval_eaEmbed, MvPolynomial.eval_sub, MvPolynomial.eval_X, MvPolynomial.eval_X,
      sub_pos] at this
  · intro h P hP
    obtain ⟨l, l', hlt, hP'⟩ := (mem_lfPoss (p := p) (q := q) (M := M) (k := k) j P).mp hP
    rw [hP', eaEval_eaEmbed, MvPolynomial.eval_sub, MvPolynomial.eval_X, MvPolynomial.eval_X,
      sub_pos]
    exact h l l' hlt

/-! ## §2. The point set of `lfW2` -/

theorem lf_mem_W2 {p q M k : ℕ} (j : Fin q) (X : WilkiesDesign.E.SemiPf (p + q))
    (XC : WilkiesDesign.E.SemiPf (p + M)) (U : Fin (lfD p q M k) → ℝ) :
    U ∈ (lfW2 j X XC).set ↔
      WilkiesDesign.E.projFirst (p + M) ((p + q) * k) U ∈ XC.set ∧
      (∀ l : Fin k, blk (WilkiesDesign.E.projSnd (p + M) ((p + q) * k) U) l ∈ X.set) ∧
      (∀ (l : Fin k) (a : Fin p), U (lfBIdx l (Fin.castAdd q a)) = U (lfXIdx a)) ∧
      (∀ l l' : Fin k, l < l' → U (lfLvIdx j l) < U (lfLvIdx j l')) := by
  have hE := forall_mem_lfEqs (c := (lfW1 X XC).c) (U := U)
  have hP := forall_mem_lfPoss (c := (lfW1 X XC).c) (j := j) (U := U)
  -- `lfW1 X XC` is the product `XC × X^k`; identify its point set with the product set.
  have h1 : (lfW1 X XC).set = (Work.WilE7.SemiPf.prod XC (SemiPf.blocks X k)).set := rfl
  have hprod : (Work.WilE7.SemiPf.prod XC (SemiPf.blocks X k)).set =
      {z : Fin (lfD p q M k) → ℝ |
        WilkiesDesign.E.projFirst (p + M) ((p + q) * k) z ∈ XC.set ∧
        WilkiesDesign.E.projSnd (p + M) ((p + q) * k) z ∈ (SemiPf.blocks X k).set} :=
    Work.WilE7.prodSet XC (SemiPf.blocks X k)
  rw [lfW2, addAtoms_set]
  simp only [Set.mem_inter_iff, Set.mem_ofPred_eq]
  rw [hE, hP, h1, hprod, blocks_set X k]
  simp only [Set.mem_ofPred_eq]
  tauto

end Work.WilE7.LevelFibre
