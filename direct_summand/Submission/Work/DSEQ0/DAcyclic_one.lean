import Mathlib
import Submission.Work.DSEQ0.SurjBasic

/-!
# Acyclicity of the full complex `D` above degree `1`

The full complex `D k = ((Fin (k+1) → ι) → M)` with the alternating coboundary `cob` is
acyclic in degrees `≥ 1`: every cocycle `f` in degree `k + 1 ≥ 1` is a coboundary.

The proof is the classical "extra degeneracy" contraction: fix a base point `a : ι` and put
`h g = f (Fin.cons a g)`, i.e. `h` evaluates `f` on the tuple obtained by inserting `a` in
front of `g`.  The key combinatorial identity `cob_cons` below says
`cob k h x = f x - cob (k+1) f (Fin.cons a x)`, so on a cocycle `f` this is exactly `f x`.
-/

open Classical Finset

namespace Work.DSEQ0

universe u

/-- The "extra degeneracy" identity: inserting the base point `a` in front of `x` turns the
degree-`k+1` coboundary of `f` into `f x` minus the degree-`k` coboundary of the contraction
`g ↦ f (Fin.cons a g)`. -/
theorem cob_cons {ι : Type u} {M : Type u} [AddCommGroup M] (k : ℕ) (a : ι)
    (f : (Fin (k + 2) → ι) → M) (x : Fin (k + 2) → ι) :
    cob (k + 1) f (Fin.cons a x)
      = f x - cob k (fun g => f (Fin.cons a g)) x := by
  simp only [cob]
  rw [Fin.sum_univ_succ]
  simp only [Fin.val_zero, pow_zero, one_smul, Fin.succAbove_zero, Fin.cons_comp_succ]
  have hterm : ∀ i : Fin (k + 2),
      (-1 : ℤ) ^ ((i.succ : ℕ)) • f (Fin.cons a x ∘ i.succ.succAbove)
        = - ((-1 : ℤ) ^ ((i : ℕ)) • f (Fin.cons a (x ∘ i.succAbove))) := by
    intro i
    rw [Fin.cons_comp_succ_succAbove, Fin.val_succ, pow_succ, mul_neg_one, neg_smul]
    rfl
  rw [Finset.sum_congr rfl (fun i _ => hterm i), Finset.sum_neg_distrib, sub_eq_add_neg]

theorem DAcyclic_one {ι : Type u} [Fintype ι] (hι : Nonempty ι) {M : Type u} [AddCommGroup M] :
    @DAcyclic ι M _ 1 := by
  intro k _ f hf
  obtain ⟨a⟩ := hι
  refine ⟨fun g => f (Fin.cons a g), ?_⟩
  funext x
  have h := congrFun hf (Fin.cons a x)
  rw [cob_cons k a f x] at h
  exact (sub_eq_zero.mp h).symm

end Work.DSEQ0
