import Mathlib
import Submission.Work.DSM5b.HCF.Surj

/-!
# Helper vocabulary for the top-degree injectivity of the surjection complex

The target `Work.DSM5b.HCF.surjD_top_injective` states that in the top degree `p+1`
(with `p + 2 = ♯S₀`) of the surjection complex `Work.DSM5b.SurjTerm S₀ N`, a cocycle is
determined by its value at the increasing enumeration `Work.DSM5b.incTupleE S₀ (p+1) hp`.

In degree `p+1` the tuples are the bijections `Fin (p+2) → S₀`.  The proof strategy is:

* an elementary computation with the cocycle condition (`surjD_step`) shows that for a
  cocycle `z` and an adjacent transposition of the entries of `σ : SurjIdx S₀ (p+1)`,
  `z σ + z (swapEntry σ i) = 0`;
* hence `F π := z ⟨e.1 ∘ π, _⟩` (`e := incTupleE S₀ (p+1) hp`) satisfies
  `F (π * swap i.castSucc i.succ) = - F π`, and since the adjacent transpositions generate
  `Equiv.Perm (Fin (p+2))` (`Equiv.Perm.mclosure_swap_castSucc_succ`) we get `F = 0`
  provided `F 1 = 0` (`perm_eq_zero_of_step`);
* finally every `σ` is in the orbit of `e` under composition of positions
  (`surjIdx_orbit`), so `z = 0`.

This file contains the shared definitions and the statement-level pieces.
-/

namespace Work.DSM5b.HCF

open Work.DSM5b

universe u

variable {n : ℕ} {S₀ : Finset (Fin n)}

/-- The range of a tuple is unchanged by permuting the positions. -/
lemma tupRng_comp_perm {m : ℕ} (e : Equiv.Perm (Fin (m + 1))) (f : Fin (m + 1) → Fin n) :
    Work.DSM5b.tupRng (f ∘ e) = Work.DSM5b.tupRng f := by
  ext x
  simp only [Work.DSM5b.tupRng, Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨i, rfl⟩
    exact ⟨e i, rfl⟩
  · rintro ⟨i, rfl⟩
    exact ⟨e.symm i, by simp⟩

/-- Swap two adjacent entries (`i`-th and `(i+1)`-st) of a surjective tuple.

Here `σ : SurjIdx S₀ m` is a tuple of length `m+1`, so the adjacent positions are
`i.castSucc` and `i.succ` for `i : Fin m`. -/
noncomputable def swapEntry {m : ℕ} (σ : SurjIdx S₀ m) (i : Fin m) : SurjIdx S₀ m :=
  ⟨σ.1 ∘ Equiv.swap i.castSucc i.succ,
    (tupRng_comp_perm (Equiv.swap i.castSucc i.succ) σ.1).trans σ.2⟩

@[simp] lemma swapEntry_val {m : ℕ} (σ : SurjIdx S₀ m) (i : Fin m) :
    (swapEntry σ i).1 = σ.1 ∘ Equiv.swap i.castSucc i.succ := rfl

end Work.DSM5b.HCF
