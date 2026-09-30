import Mathlib
import Submission.Work.BW.wuestholzDefs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW

/-- Recursion for `applyL` at index `0`: peeling off the first index of `Fin (m+1)`. -/
lemma applyL_succ {R : Type*} {m : ℕ} (Λ : Fin (m + 1) → R → R) (α : Fin (m + 1) → ℕ)
    (x : R) :
    applyL Λ α x =
      (Λ 0)^[α 0] (applyL (fun j : Fin m => Λ j.succ) (fun j : Fin m => α j.succ) x) := by
  simp only [applyL, List.finRange_succ, List.foldr_cons, List.foldr_map]

/-- A function `f` commuting with every `Λ j` for `j ∈ l` commutes with the `foldr`-composition
of the iterates `(Λ j)^[α j]` over `l`. -/
lemma foldr_commute {R : Type*} {ℓ : ℕ} (Λ : Fin ℓ → R → R) (α : Fin ℓ → ℕ)
    (f : R → R) (hf : ∀ j : Fin ℓ, Function.Commute f (Λ j))
    (l : List (Fin ℓ)) (x : R) :
    f ((l.foldr (fun j q => (Λ j)^[α j] q)) x) =
      (l.foldr (fun j q => (Λ j)^[α j] q)) (f x) := by
  induction l generalizing x with
  | nil => rfl
  | cons j t ih =>
      simp only [List.foldr_cons]
      have h := (hf j).iterate_right (α j) (List.foldr (fun j q => (Λ j)^[α j] q) x t)
      rw [ih x] at h
      exact h

/-- Folding over a `Nodup` list whose exponents are `1` at `i` and `0` elsewhere picks out the
single operator `Λ i`. -/
lemma foldr_single_exp {R : Type*} {ι : Type*} [DecidableEq ι] (Λ : ι → R → R) (i : ι)
    (l : List ι) (hnd : l.Nodup) (x : R) :
    (l.foldr (fun j q => (Λ j)^[(Pi.single i 1 : ι → ℕ) j] q) x) =
      if i ∈ l then Λ i x else x := by
  induction l generalizing x with
  | nil => simp
  | cons a t ih =>
      rw [List.nodup_cons] at hnd
      obtain ⟨ha, hnd_t⟩ := hnd
      rw [List.foldr_cons]
      by_cases h : a = i
      · subst h
        rw [Pi.single_eq_same, Function.iterate_one]
        rw [ih hnd_t x]
        simp [ha]
      · have h' : ¬i = a := fun hh => h hh.symm
        rw [Pi.single_eq_of_ne h, Function.iterate_zero]
        rw [ih hnd_t x]
        simp [h']

/-- `applyL` is additive in the multi-index: `Λ^{α+β} = Λ^α ∘ Λ^β`. -/
lemma applyL_add {R : Type*} [CommRing R] (ℓ : ℕ) (Λ : Fin ℓ → R → R)
    (hcomm : ∀ (i j : Fin ℓ) (x : R), Λ i (Λ j x) = Λ j (Λ i x)) (α β : Fin ℓ → ℕ) (x : R) :
    applyL Λ (α + β) x = applyL Λ α (applyL Λ β x) := by
  induction ℓ with
  | zero => simp [applyL]
  | succ m ih =>
      rw [applyL_succ Λ (α + β) x, applyL_succ Λ α (applyL Λ β x), applyL_succ Λ β x]
      rw [Pi.add_apply,
        show (fun j : Fin m => (α + β) j.succ) =
            (fun j : Fin m => α j.succ) + (fun j : Fin m => β j.succ)
          from by funext j; simp [Pi.add_apply]]
      rw [ih (fun j : Fin m => Λ j.succ) (fun i j x => hcomm i.succ j.succ x)
            (fun j => α j.succ) (fun j => β j.succ)]
      rw [Function.iterate_add_apply]
      congr 1
      have hcomm2 : Function.Commute ((Λ 0)^[β 0])
          (applyL (fun j : Fin m => Λ j.succ) (fun j => α j.succ)) := by
        intro y
        simp only [applyL]
        exact foldr_commute (fun j : Fin m => Λ j.succ) (fun j => α j.succ) ((Λ 0)^[β 0])
          (fun j => Function.Commute.iterate_left (hcomm 0 j.succ) (β 0)) (List.finRange m) y
      exact hcomm2 _

/-- The multi-index `Pi.single i 1` selects the single operator `Λ i`. -/
lemma applyL_single {R : Type*} {ℓ : ℕ} (Λ : Fin ℓ → R → R) (i : Fin ℓ) (x : R) :
    applyL Λ (Pi.single i 1) x = Λ i x := by
  unfold applyL
  rw [foldr_single_exp Λ i (List.finRange ℓ) (List.nodup_finRange ℓ) x]
  simp [List.mem_finRange]

/-- `applyL Λ α` is the composition `Λ 0^{α 0} ∘ Λ 1^{α 1} ∘ ⋯`; for pairwise commuting
operators the composition is additive in `α`, the single-index case is `Λ i`, and multiplying
`applyL Λ α` on the left by `Λ i` raises `α i` by one. -/
theorem applyL_compose {R : Type*} [CommRing R] {ℓ : ℕ} (Λ : Fin ℓ → R → R)
    (hcomm : ∀ (i j : Fin ℓ) (x : R), Λ i (Λ j x) = Λ j (Λ i x)) :
    (∀ (α β : Fin ℓ → ℕ) (x : R), applyL Λ (α + β) x = applyL Λ α (applyL Λ β x)) ∧
    (∀ (i : Fin ℓ) (x : R), applyL Λ (Pi.single i 1) x = Λ i x) ∧
    (∀ (α : Fin ℓ → ℕ) (i : Fin ℓ) (x : R),
      applyL Λ (α + Pi.single i 1) x = Λ i (applyL Λ α x)) ∧
    (∀ (α : Fin ℓ → ℕ) (i : Fin ℓ) (x : R),
      applyL Λ (α + Pi.single i 1) x = applyL Λ α (Λ i x)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro α β x
    exact applyL_add ℓ Λ hcomm α β x
  · intro i x
    exact applyL_single Λ i x
  · intro α i x
    rw [add_comm α (Pi.single i 1)]
    rw [applyL_add ℓ Λ hcomm (Pi.single i 1) α x]
    rw [applyL_single Λ i (applyL Λ α x)]
  · intro α i x
    rw [applyL_add ℓ Λ hcomm α (Pi.single i 1) x]
    rw [applyL_single Λ i x]

end Work.BW
