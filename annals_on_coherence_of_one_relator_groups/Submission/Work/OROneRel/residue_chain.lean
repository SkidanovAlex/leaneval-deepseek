import Mathlib
import Submission.Work.OROneRel.interval_defs

namespace Work.OROneRel

/-- Repeated subtraction of `A`: if `n * A ≤ x` and `x ∈ [0, M]`, then `x` reaches `x - n * A`
along the relation `S 0 M A B`; every intermediate point stays in `[0, M]`. -/
lemma residue_chain_aux {A B : ℤ} (hA : 1 ≤ A) (M : ℤ) :
    ∀ n : ℕ, ∀ x : ℤ, (n : ℤ) * A ≤ x → 0 ≤ x → x ≤ M →
      Relation.ReflTransGen (S 0 M A B) x (x - (n : ℤ) * A) := by
  have hA0 : 0 ≤ A := by omega
  intro n
  induction n with
  | zero =>
    intro x _ hx0 hxM
    simpa using Relation.ReflTransGen.refl (a := x)
  | succ n ih =>
    intro x hn hx0 hxM
    have hn1 : ((n : ℤ) + 1) * A ≤ x := by
      push_cast at hn ⊢
      linarith [hA0]
    have hn' : (n : ℤ) * A ≤ x := by nlinarith [hA0]
    have hprev := ih x hn' hx0 hxM
    have hy0 : 0 ≤ x - (n : ℤ) * A := by nlinarith [hn1, hA0]
    have hyM : x - (n : ℤ) * A ≤ M := by
      have : (0 : ℤ) ≤ (n : ℤ) * A := by positivity
      nlinarith
    have hny : x - ((n : ℤ) + 1) * A = (x - (n : ℤ) * A) - A := by ring
    have hnext : Relation.ReflTransGen (S 0 M A B) (x - (n : ℤ) * A)
        (x - ((n : ℤ) + 1) * A) := by
      refine Relation.ReflTransGen.single ?_
      exact ⟨hy0, hyM, by nlinarith [hn1], by nlinarith [hA0], Or.inr (Or.inl hny)⟩
    have hfin := hprev.trans hnext
    push_cast
    exact hfin

theorem residue_chain {A B : ℤ} (hA : 1 ≤ A) (M : ℤ) :
    ∀ x : ℤ, 0 ≤ x → x ≤ M → Relation.ReflTransGen (S 0 M A B) x (x % A) := by
  intro x hx0 hxM
  have hq : ((x / A).toNat : ℤ) = x / A :=
    Int.toNat_of_nonneg (Int.ediv_nonneg hx0 (by omega))
  have hle : ((x / A).toNat : ℤ) * A ≤ x := by
    rw [hq]
    have hmod := Int.emod_nonneg x (by omega : A ≠ 0)
    have := Int.emod_add_mul_ediv x A
    nlinarith [this]
  have hres : x - ((x / A).toNat : ℤ) * A = x % A := by
    rw [hq]
    have := Int.emod_add_mul_ediv x A
    nlinarith [this]
  have hfin := residue_chain_aux (B := B) hA M ((x / A).toNat) x hle hx0 hxM
  rwa [hres] at hfin

end Work.OROneRel
