import Mathlib
import Submission.Work.Q44Geom.FacDefs
import Submission.Work.Q44Geom.sum_fin_getD
import Submission.Work.Q44Geom.exists_fin_getD
import Submission.Work.Q44Geom.list_prod_isHomogeneous
import Submission.Work.Q44Geom.isHomogeneous_of_isUnit

set_option autoImplicit false

noncomputable section

namespace Work.Q44Geom

open MvPolynomial in
theorem factorizationHomogeneous {d : ℕ} {G : MvPolynomial (Fin 3) ℚ} (hG : G ≠ 0)
    (hd : G.IsHomogeneous d) :
    ∃ (q : Fin d → MvPolynomial (Fin 3) ℚ) (e : Fin d → ℕ),
      (∀ s, (q s).IsHomogeneous (e s)) ∧ (∑ s, e s = d) ∧
      (∀ x : Fin 3 → ℚ, MvPolynomial.eval x G = 0 ↔ ∃ s, MvPolynomial.eval x (q s) = 0) ∧
      (∀ s, (q s = 1 ∧ e s = 0) ∨ (Irreducible (q s) ∧ 1 ≤ e s)) := by
  classical
  by_cases hunit : IsUnit G
  · -- `G` is a nonzero constant, hence `d = 0` and the list of factors is empty
    obtain ⟨c, hc, hcu⟩ := (MvPolynomial.isUnit_iff_eq_C_of_isReduced).mp hunit
    subst hcu
    have hd0 : d = 0 :=
      MvPolynomial.IsHomogeneous.inj_right hd (MvPolynomial.isHomogeneous_C (Fin 3) c) hG
    subst hd0
    refine ⟨Fin.elim0, Fin.elim0, ?_, ?_, ?_, ?_⟩
    · intro s; exact s.elim0
    · simp
    · intro x
      constructor
      · intro h
        have hc0 : c = 0 := by simpa using h
        exact absurd hc0 hc.ne_zero
      · intro h
        obtain ⟨s, _⟩ := h
        exact s.elim0
    · intro s; exact s.elim0
  · -- main case: factor `G` into irreducibles
    obtain ⟨u, hueq⟩ := UniqueFactorizationMonoid.factors_prod hG
    obtain ⟨c, hc, hcu⟩ := (MvPolynomial.isUnit_iff_eq_C_of_isReduced).mp u.isUnit
    set f : Multiset (MvPolynomial (Fin 3) ℚ) := UniqueFactorizationMonoid.factors G with hf
    set l : List (MvPolynomial (Fin 3) ℚ) := f.toList with hl
    have hlprod : l.prod = f.prod := by rw [hl]; exact Multiset.prod_toList f
    have hGeq : G = MvPolynomial.C c * l.prod := by
      have h1 : f.prod * MvPolynomial.C c = G := by rw [hf, ← hcu]; exact hueq
      rw [← h1, hlprod, mul_comm]
    have hprod_ne : l.prod ≠ 0 := by
      intro h0
      exact hG (by rw [hGeq, h0, mul_zero])
    have hprodh : l.prod.IsHomogeneous d := by
      have h1 : l.prod = MvPolynomial.C c⁻¹ * G := by
        rw [hGeq, ← mul_assoc, ← MvPolynomial.C_mul, inv_mul_cancel₀ hc.ne_zero]
        simp
      rw [h1]
      simpa using (MvPolynomial.isHomogeneous_C (Fin 3) c⁻¹).mul hd
    have hmem : ∀ p, p ∈ l ↔ p ∈ UniqueFactorizationMonoid.factors G := by
      intro p
      rw [hl, hf, Multiset.mem_toList]
    have hirr : ∀ p ∈ l, Irreducible p :=
      fun p hp => UniqueFactorizationMonoid.irreducible_of_factor p ((hmem p).mp hp)
    have hne0 : ∀ p ∈ l, p ≠ 0 := fun p hp => (hirr p hp).ne_zero
    have hhom : ∀ p ∈ l, p.IsHomogeneous p.totalDegree :=
      Work.Q44Geom.Fac.list_factor_isHomogeneous hne0 hprodh
    have hsum : (l.map (fun p => p.totalDegree)).sum = d :=
      MvPolynomial.IsHomogeneous.inj_right
        (Work.Q44Geom.list_prod_isHomogeneous l (fun p => p.totalDegree) hhom) hprodh hprod_ne
    have hge : ∀ p ∈ l, 1 ≤ p.totalDegree := by
      intro p hp
      rcases Nat.eq_zero_or_pos p.totalDegree with h0 | hpos
      · exfalso
        have hh0 : p.IsHomogeneous 0 := h0 ▸ hhom p hp
        exact (hirr p hp).not_isUnit
          (Work.Q44Geom.Fac.isUnit_of_isHomogeneous_zero hh0 (hne0 p hp))
      · exact hpos
    have hlen : l.length ≤ d := by
      have h1 : l.length = (l.map (fun _ => (1 : ℕ))).sum := by
        rw [List.map_const', List.sum_const_nat, Nat.mul_one]
      rw [h1, ← hsum]
      exact List.sum_le_sum (fun p hp => hge p hp)
    refine ⟨fun i : Fin d => l.getD (i : ℕ) 1, fun i : Fin d => (l.getD (i : ℕ) 1).totalDegree,
      ?_, ?_, ?_, ?_⟩
    · intro i
      show (l.getD (i : ℕ) 1).IsHomogeneous ((l.getD (i : ℕ) 1).totalDegree)
      by_cases hi : (i : ℕ) < l.length
      · rw [List.getD_eq_getElem l 1 hi]
        exact hhom _ (List.getElem_mem hi)
      · rw [List.getD_eq_default l 1 (Nat.le_of_not_lt hi)]
        simpa using (MvPolynomial.isHomogeneous_one (σ := Fin 3) (R := ℚ))
    · show ∑ i : Fin d, (l.getD (i : ℕ) 1).totalDegree = d
      rw [Work.Q44Geom.sum_fin_getD l d 1 (fun p => p.totalDegree) (by simp) hlen]
      exact hsum
    · intro x
      show MvPolynomial.eval x G = 0 ↔
        ∃ i : Fin d, MvPolynomial.eval x (l.getD (i : ℕ) 1) = 0
      have hGv : MvPolynomial.eval x G = 0 ↔ MvPolynomial.eval x l.prod = 0 := by
        rw [hGeq, MvPolynomial.eval_mul, MvPolynomial.eval_C, mul_eq_zero]
        constructor
        · rintro (h | h)
          · exact absurd h hc.ne_zero
          · exact h
        · intro h; exact Or.inr h
      have hlv : MvPolynomial.eval x l.prod = 0 ↔ ∃ p ∈ l, MvPolynomial.eval x p = 0 := by
        rw [map_list_prod (MvPolynomial.eval x) l, List.prod_eq_zero_iff, List.mem_map]
      have hfin : (∃ i : Fin d, MvPolynomial.eval x (l.getD (i : ℕ) 1) = 0) ↔
          ∃ p ∈ l, MvPolynomial.eval x p = 0 :=
        Work.Q44Geom.exists_fin_getD l d 1 (fun m => MvPolynomial.eval x m = 0) (fun p => p)
          (by simp) hlen
      exact hGv.trans (hlv.trans hfin.symm)
    · intro i
      show (l.getD (i : ℕ) 1 = 1 ∧ (l.getD (i : ℕ) 1).totalDegree = 0) ∨
        (Irreducible (l.getD (i : ℕ) 1) ∧ 1 ≤ (l.getD (i : ℕ) 1).totalDegree)
      by_cases hi : (i : ℕ) < l.length
      · right
        rw [List.getD_eq_getElem l 1 hi]
        exact ⟨hirr _ (List.getElem_mem hi), hge _ (List.getElem_mem hi)⟩
      · left
        rw [List.getD_eq_default l 1 (Nat.le_of_not_lt hi)]
        simp

end Work.Q44Geom
