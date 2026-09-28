import Mathlib
import Submission.Work.HP.GonLib
import Submission.Work.HP.FM.RecDefs

/-!
# Auxiliary families for `Work.HP.Sig2.latCovol_latStep`

The covolume identity

`latCovol Φ = ‖Φ u‖ * latCovol (latStep Φ u v)`

is a statement about Gram determinants.  Both sides are determinants of Gram matrices: the
left one of the family `i ↦ Φ (eᵢ)` (the standard coefficient basis) and the right one of the
family `i ↦ projU (Φ u) (Φ vᵢ)`.  To compare them one reads both as Gram matrices of the family

`(u, v₀, …, v_{R-2})`,

which is a `ℤ`-basis of `ℤ^R` by hypothesis.  This file contains the index bookkeeping for that
family.

* `idxEquiv R hR` is the equivalence `Fin 1 ⊕ Fin (R-1) ≃ Fin R` used to reindex it.
* `famZ u v` is the family `(u, v₀, …, v_{R-2})` indexed by `Fin 1 ⊕ Fin (R-1)`, i.e.
  `Sum.elim (fun _ => u) v`, and `famR u v` its entrywise realification.
* `bfam hR u v` and `bfamR hR u v` are the same families reindexed along `idxEquiv`.
-/

set_option autoImplicit false

noncomputable section

open Finset Matrix
open scoped BigOperators

namespace Work.HP.Sig2

/-- The index equivalence `Fin 1 ⊕ Fin (R - 1) ≃ Fin R` (available for `1 ≤ R`). -/
def idxEquiv (R : ℕ) (hR : 1 ≤ R) : Fin 1 ⊕ Fin (R - 1) ≃ Fin R :=
  finSumFinEquiv.trans (finCongr (by omega))

/-- The family `(u, v₀, …, v_{R-2})` of integer coefficient vectors, indexed by
`Fin 1 ⊕ Fin (R - 1)`. -/
def famZ {R : ℕ} (u : Fin R → ℤ) (v : Fin (R - 1) → (Fin R → ℤ)) :
    Fin 1 ⊕ Fin (R - 1) → (Fin R → ℤ) :=
  Sum.elim (fun _ => u) v

/-- Entrywise realification of `famZ u v`. -/
def famR {R : ℕ} (u : Fin R → ℤ) (v : Fin (R - 1) → (Fin R → ℤ)) :
    Fin 1 ⊕ Fin (R - 1) → (Fin R → ℝ) :=
  fun c k => (famZ u v c k : ℝ)

/-- The `Fin R`-indexed version of `famZ`: `bfam hR u v j = famZ u v (idxEquiv R hR).symm j`. -/
def bfam {R : ℕ} (hR : 1 ≤ R) (u : Fin R → ℤ) (v : Fin (R - 1) → (Fin R → ℤ)) :
    Fin R → (Fin R → ℤ) :=
  fun j => famZ u v ((idxEquiv R hR).symm j)

/-- Entrywise realification of `bfam hR u v`. -/
def bfamR {R : ℕ} (hR : 1 ≤ R) (u : Fin R → ℤ) (v : Fin (R - 1) → (Fin R → ℤ)) :
    Fin R → (Fin R → ℝ) :=
  fun j k => (bfam hR u v j k : ℝ)

@[simp] lemma famZ_inl {R : ℕ} (u : Fin R → ℤ) (v : Fin (R - 1) → (Fin R → ℤ)) (i : Fin 1) :
    famZ u v (Sum.inl i) = u := rfl

@[simp] lemma famZ_inr {R : ℕ} (u : Fin R → ℤ) (v : Fin (R - 1) → (Fin R → ℤ))
    (i : Fin (R - 1)) : famZ u v (Sum.inr i) = v i := rfl

@[simp] lemma famR_inl {R : ℕ} (u : Fin R → ℤ) (v : Fin (R - 1) → (Fin R → ℤ)) (i : Fin 1) :
    famR u v (Sum.inl i) = fun k => (u k : ℝ) := rfl

@[simp] lemma famR_inr {R : ℕ} (u : Fin R → ℤ) (v : Fin (R - 1) → (Fin R → ℤ))
    (i : Fin (R - 1)) : famR u v (Sum.inr i) = fun k => (v i k : ℝ) := rfl

lemma bfam_eq {R : ℕ} (hR : 1 ≤ R) (u : Fin R → ℤ) (v : Fin (R - 1) → (Fin R → ℤ)) :
    bfam hR u v = famZ u v ∘ (idxEquiv R hR).symm := rfl

lemma bfamR_eq {R : ℕ} (hR : 1 ≤ R) (u : Fin R → ℤ) (v : Fin (R - 1) → (Fin R → ℤ)) :
    bfamR hR u v = famR u v ∘ (idxEquiv R hR).symm := rfl

end Work.HP.Sig2
