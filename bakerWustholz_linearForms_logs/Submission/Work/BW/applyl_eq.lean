import Mathlib
import Submission.Work.BW.extract_defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW

/-- `foldl` along the constant word `List.replicate n i` is the `n`-fold iterate of `Λ i`. -/
lemma foldl_replicate_iterate {R : Type*} {ℓ : ℕ} (Λ : Fin ℓ → R → R) (i : Fin ℓ) :
    ∀ (n : ℕ) (x : R), (List.replicate n i).foldl (fun q j => Λ j q) x = (Λ i)^[n] x := by
  intro n
  induction n with
  | zero => intro x; rfl
  | succ n ih =>
    intro x
    rw [List.replicate_succ, List.foldl_cons, ih, Function.iterate_succ_apply]

/-- The `foldr`-composition of iterates of the operators agrees with the `foldl` along the word
that lists them index-block by index-block, the last index first. -/
lemma foldr_iterate_eq_foldl_words {R : Type*} {ℓ : ℕ} (Λ : Fin ℓ → R → R) (g : Fin ℓ → ℕ)
    (L : List (Fin ℓ)) (x : R) :
    L.foldr (fun i q => (Λ i)^[g i] q) x
      = (L.foldr (fun i acc => acc ++ List.replicate (g i) i) []).foldl (fun q j => Λ j q) x := by
  induction L generalizing x with
  | nil => rfl
  | cons a t ih =>
    have h1 : (a :: t).foldr (fun i q => (Λ i)^[g i] q) x
        = (Λ a)^[g a] (t.foldr (fun i q => (Λ i)^[g i] q) x) := rfl
    have h2 : (a :: t).foldr (fun i acc => acc ++ List.replicate (g i) i) []
        = (t.foldr (fun i acc => acc ++ List.replicate (g i) i) [])
            ++ List.replicate (g a) a := rfl
    rw [h1, h2, List.foldl_append, foldl_replicate_iterate, ih x]

/-- `applyL` (the `foldr`-composition from `Work.BW.wuestholzDefs`) agrees with `applyWord` applied
to the word `wordOf α` of operators. -/
theorem applyl_eq {R : Type*} [CommRing R] {ℓ : ℕ} (Λ : Fin ℓ → R → R)
    (α : Fin ℓ → ℕ) (x : R) : applyL Λ α x = applyWord Λ (wordOf α) x := by
  unfold applyL applyWord wordOf
  exact foldr_iterate_eq_foldl_words Λ α (List.finRange ℓ) x

end Work.BW
