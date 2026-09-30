import Mathlib
import Submission.Work.KeyLemma.Sum

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


set_option autoImplicit false

namespace Work.KeyLemma.Sum

universe u

/-- Every finitely supported `ℕ`-valued function on a type `α` is the sum of one-point
functions, one for each element counted with multiplicity: if the total mass is `n`, then it is
`∑_{m : Fin n} single (x m) 1` for a suitable enumeration `x`. -/
private theorem exists_enum_aux {α : Type*} :
    ∀ (n : ℕ) (s : α →₀ ℕ), Finsupp.degree s = n →
      ∃ x : Fin n → α, (∑ m : Fin n, Finsupp.single (x m) 1) = s := by
  intro n
  induction n with
  | zero =>
      intro s hs
      refine ⟨Fin.elim0, ?_⟩
      rw [Fin.sum_univ_zero, (Finsupp.degree_eq_zero_iff s).mp hs]
  | succ n ih =>
      intro s hs
      -- `s` is nonzero, so some coefficient is positive
      have hsne : s ≠ 0 := by
        intro h
        rw [h, map_zero] at hs
        exact Nat.succ_ne_zero n hs.symm
      obtain ⟨p, hp⟩ : ∃ p, s p ≠ 0 := by
        by_contra h
        push Not at h
        exact hsne (Finsupp.ext fun a => by simp [h a])
      -- peel off one copy of the point `p`
      set t : α →₀ ℕ := s - Finsupp.single p 1 with ht
      have hst : Finsupp.single p 1 + t = s := by
        rw [ht, add_comm (Finsupp.single p 1), Finsupp.sub_add_single_one_cancel hp]
      have hdeg : Finsupp.degree t = n := by
        have h2 : Finsupp.degree s = Finsupp.degree (Finsupp.single p 1) + Finsupp.degree t := by
          rw [← hst, map_add]
        rw [Finsupp.degree_single] at h2
        omega
      obtain ⟨x', hx'⟩ := ih t hdeg
      refine ⟨Fin.cons p x', ?_⟩
      rw [Fin.sum_univ_succ]
      simp only [Fin.cons_zero, Fin.cons_succ]
      rw [hx', hst]

theorem exists_enum {k : Type u} [Field k] {C : Work.CurveBasics.Curve k} {n : ℕ}
    (s : Work.KeyLemma.Curve.SumDiv C) (hs : Work.KeyLemma.Curve.SumDiv.deg s = n) :
    ∃ x : Fin n → Work.KeyLemma.Curve.Point C,
      (∑ m : Fin n, Finsupp.single (x m) 1) = s :=
  exists_enum_aux n s hs

end Work.KeyLemma.Sum
