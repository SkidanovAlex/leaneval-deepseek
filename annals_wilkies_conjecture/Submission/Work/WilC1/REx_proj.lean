import Mathlib
import Submission.Work.WilC1.Defs

set_option autoImplicit false
set_option linter.style.haveILetI false
noncomputable section
open Classical FirstOrder FirstOrder.Language
namespace Work.WilC1

open WilkiesDesign WilkiesDesign.CG WilkiesConjecture

/-! ## Reindexing a witness block: the associativity map

`REx (ι ⊕ μ) X` witnesses live in a block `((ι ⊕ μ) ⊕ ν)`. To project `μ` away while keeping the
witnesses of `X` we move to the index type `ι ⊕ (μ ⊕ ν)` via the associativity map, and the whole
argument turns on how `Sum.elim` composes with it. -/

/-- The associativity map `(ι ⊕ μ) ⊕ ν → ι ⊕ (μ ⊕ ν)`. -/
def sumAssocMap (ι μ ν : Type*) : (ι ⊕ μ) ⊕ ν → ι ⊕ (μ ⊕ ν) :=
  Sum.elim (Sum.map id (Sum.inl : μ → μ ⊕ ν)) (fun k => Sum.inr (Sum.inr k))

theorem sumElim_comp_sumAssocMap {ι μ ν : Type*} (z : ι → ℝ) (w : μ ⊕ ν → ℝ) :
    (Sum.elim z w) ∘ sumAssocMap ι μ ν
      = Sum.elim (Sum.elim z (w ∘ Sum.inl)) (w ∘ Sum.inr) := by
  funext q
  rcases q with q | k
  · rcases q with a | j <;> rfl
  · rfl

theorem sumElim_assoc_inv {ι μ ν : Type*} (z : ι → ℝ) (u : μ → ℝ) (y : ν → ℝ) :
    Sum.elim (Sum.elim z (Sum.elim u y ∘ Sum.inl)) (Sum.elim u y ∘ Sum.inr)
      = Sum.elim (Sum.elim z u) y := by
  funext q
  rcases q with q | k
  · rcases q with a | j <;> rfl
  · rfl

/-- The master lemma for the associativity reindexing: evaluating a renamed polynomial at
`Sum.elim z w` is evaluation of the original at the reassociated tuple. -/
theorem rexpEval_rename_sumAssoc {ι μ ν : Type*} (z : ι → ℝ) (w : μ ⊕ ν → ℝ)
    (P : MvPolynomial (((ι ⊕ μ) ⊕ ν) ⊕ ((ι ⊕ μ) ⊕ ν)) ℝ) :
    rexpEval (Sum.elim z w)
        (MvPolynomial.rename (polyMap (sumAssocMap ι μ ν)) P)
      = rexpEval (Sum.elim (Sum.elim z (w ∘ Sum.inl)) (w ∘ Sum.inr)) P := by
  rw [rexpEval_rename (ι := (ι ⊕ μ) ⊕ ν) (ι' := ι ⊕ (μ ⊕ ν))
        (Sum.elim z w) (sumAssocMap ι μ ν) P, sumElim_comp_sumAssocMap]

/-! ## Projection over a block of witnesses -/

/-- Projecting a block `μ` of coordinates away is existential quantification over them. -/
theorem REx.existsBlock {ι : Type*} {μ : Type} [Fintype μ] {X : Set ((ι ⊕ μ) → ℝ)}
    (hX : REx (ι ⊕ μ) X) :
    REx ι {x : ι → ℝ | ∃ u : μ → ℝ, Sum.elim x u ∈ X} := by
  obtain ⟨ν, hν, P, rfl⟩ := hX
  letI := hν
  refine ⟨μ ⊕ ν, inferInstance,
    MvPolynomial.rename (polyMap (sumAssocMap ι μ ν)) P, ?_⟩
  ext x
  constructor
  · rintro ⟨u, y, hy⟩
    exact ⟨Sum.elim u y, by rw [rexpEval_rename_sumAssoc, sumElim_assoc_inv]; exact hy⟩
  · rintro ⟨w, hw⟩
    exact ⟨w ∘ Sum.inl, w ∘ Sum.inr, by rw [rexpEval_rename_sumAssoc] at hw; exact hw⟩

theorem REx_proj {ι : Type*} (k : ℕ) {X : Set ((ι ⊕ Fin k) → ℝ)} (hX : REx (ι ⊕ Fin k) X) :
    REx ι {x : ι → ℝ | ∃ y : Fin k → ℝ, Sum.elim x y ∈ X} :=
  hX.existsBlock (μ := Fin k)

end Work.WilC1
