import Mathlib
import Submission.Work.WilC1.Defs

set_option linter.style.haveILetI false

namespace Work.WilC1

/-! ## Reindexing the witness block

`REx` witnesses are indexed by an arbitrary finite type.  To combine two `REx` presentations of
`X` and `Y` into one presentation of `X ∪ Y` we push the two witness types `γ₁`, `γ₂` into the
common block `γ₁ ⊕ γ₂` and rename the polynomials accordingly.  The lemmas below are the
bookkeeping for that renaming, phrased for the `polyMap`/`rexpEval` vocabulary of `Defs.lean`. -/

/-- Reindexing the *witness* block of a tuple: `Sum.elim z y ∘ Sum.map id g = Sum.elim z (y ∘ g)`. -/
private theorem sumElim_comp_map_id {κ μ ν : Type*} (z : κ → ℝ) (y : ν → ℝ) (g : μ → ν) :
    Sum.elim z y ∘ Sum.map id g = Sum.elim z (y ∘ g) := by
  funext q
  rcases q with i | i <;> rfl

/-- **Master lemma for the union.**  Renaming the witness block of a rexp-polynomial along
`Sum.map id g` composes the witness tuple with `g`. -/
private theorem rexpEval_rename_sumMap {ι γ γ' : Type*} (v : ι → ℝ) (y : γ' → ℝ) (g : γ → γ')
    (P : MvPolynomial ((ι ⊕ γ) ⊕ (ι ⊕ γ)) ℝ) :
    rexpEval (Sum.elim v y) (MvPolynomial.rename (polyMap (Sum.map id g)) P)
      = rexpEval (Sum.elim v (y ∘ g)) P := by
  rw [rexpEval_rename (Sum.elim v y) (Sum.map id g) P, sumElim_comp_map_id]

/-- Splitting off the first component of a witness block: `Sum.elim z y ∘ Sum.inl = z`. -/
private theorem sumElim_comp_inl {κ μ : Type*} (z : κ → ℝ) (y : μ → ℝ) :
    Sum.elim z y ∘ (Sum.inl : κ → κ ⊕ μ) = z := by
  funext a
  rfl

/-- Splitting off the second component of a witness block: `Sum.elim z y ∘ Sum.inr = y`. -/
private theorem sumElim_comp_inr {κ μ : Type*} (z : κ → ℝ) (y : μ → ℝ) :
    Sum.elim z y ∘ (Sum.inr : μ → κ ⊕ μ) = y := by
  funext a
  rfl

/-- `REx` is closed under finite unions: the union of two projections of zero sets is again the
projection of a zero set, namely that of the product of the two polynomials, after pushing both
witness blocks into the common block `γ₁ ⊕ γ₂`. -/
theorem REx_union {ι : Type*} {X Y : Set (ι → ℝ)} (hX : REx ι X) (hY : REx ι Y) :
    REx ι (X ∪ Y) := by
  obtain ⟨γ₁, hγ₁, P, hP⟩ := hX
  obtain ⟨γ₂, hγ₂, Q, hQ⟩ := hY
  haveI := hγ₁
  haveI := hγ₂
  refine ⟨γ₁ ⊕ γ₂, inferInstance,
    MvPolynomial.rename (polyMap (Sum.map id (Sum.inl : γ₁ → γ₁ ⊕ γ₂))) P *
      MvPolynomial.rename (polyMap (Sum.map id (Sum.inr : γ₂ → γ₁ ⊕ γ₂))) Q, ?_⟩
  rw [hP, hQ]
  ext x
  simp only [Set.mem_union, Set.mem_ofPred_eq]
  constructor
  · -- `X` (or `Y`) gives a witness: fill the other half of the block with zeros.
    rintro (⟨u, hu⟩ | ⟨v, hv⟩)
    · refine ⟨Sum.elim u (0 : γ₂ → ℝ), ?_⟩
      rw [rexpEval_mul, rexpEval_rename_sumMap x (Sum.elim u (0 : γ₂ → ℝ)) Sum.inl P,
        rexpEval_rename_sumMap x (Sum.elim u (0 : γ₂ → ℝ)) Sum.inr Q,
        sumElim_comp_inl u (0 : γ₂ → ℝ), sumElim_comp_inr u (0 : γ₂ → ℝ), hu, zero_mul]
    · refine ⟨Sum.elim (0 : γ₁ → ℝ) v, ?_⟩
      rw [rexpEval_mul, rexpEval_rename_sumMap x (Sum.elim (0 : γ₁ → ℝ) v) Sum.inl P,
        rexpEval_rename_sumMap x (Sum.elim (0 : γ₁ → ℝ) v) Sum.inr Q,
        sumElim_comp_inl (0 : γ₁ → ℝ) v, sumElim_comp_inr (0 : γ₁ → ℝ) v, hv, mul_zero]
  · -- a witness of the product forces one of the factors to vanish, i.e. a witness of `X` or `Y`.
    rintro ⟨y, hy⟩
    rw [rexpEval_mul, rexpEval_rename_sumMap x y Sum.inl P,
      rexpEval_rename_sumMap x y Sum.inr Q] at hy
    rcases mul_eq_zero.mp hy with h | h
    · exact Or.inl ⟨y ∘ Sum.inl, h⟩
    · exact Or.inr ⟨y ∘ Sum.inr, h⟩

end Work.WilC1
