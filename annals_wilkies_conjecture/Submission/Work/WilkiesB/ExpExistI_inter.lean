import Mathlib
import Submission.Work.WilkiesB.Defs

set_option linter.style.haveILetI false

namespace Work.WilkiesB

/-- The master renaming lemma, specialised to embedding a witness block into the `Sum.inl` half of
a larger witness block. -/
theorem expEval_rename_inl {κ μ ν : Type*} (z : κ → ℝ) (y : μ ⊕ ν → ℝ)
    (P : MvPolynomial ((κ ⊕ μ) ⊕ (κ ⊕ μ)) ℝ) :
    expEval (Sum.elim z y)
        (MvPolynomial.rename (Sum.map (Sum.map id (Sum.inl : μ → μ ⊕ ν))
          (Sum.map id (Sum.inl : μ → μ ⊕ ν))) P)
      = expEval (Sum.elim z (y ∘ Sum.inl)) P := by
  have h := expEval_rename (Sum.map id (Sum.inl : μ → μ ⊕ ν)) (Sum.elim z y) P
  simp only [polyMap] at h
  rw [h, sumElim_comp_map_id]

/-- The master renaming lemma, specialised to embedding a witness block into the `Sum.inr` half of
a larger witness block. -/
theorem expEval_rename_inr {κ μ ν : Type*} (z : κ → ℝ) (y : μ ⊕ ν → ℝ)
    (P : MvPolynomial ((κ ⊕ ν) ⊕ (κ ⊕ ν)) ℝ) :
    expEval (Sum.elim z y)
        (MvPolynomial.rename (Sum.map (Sum.map id (Sum.inr : ν → μ ⊕ ν))
          (Sum.map id (Sum.inr : ν → μ ⊕ ν))) P)
      = expEval (Sum.elim z (y ∘ Sum.inr)) P := by
  have h := expEval_rename (Sum.map id (Sum.inr : ν → μ ⊕ ν)) (Sum.elim z y) P
  simp only [polyMap] at h
  rw [h, sumElim_comp_map_id]

@[simp] theorem mem_ExpZero {κ : Type*} (μ : Type)
    (P : MvPolynomial ((κ ⊕ μ) ⊕ (κ ⊕ μ)) ℝ) (z : κ → ℝ) :
    z ∈ ExpZero μ P ↔ ∃ y : μ → ℝ, expEval (Sum.elim z y) P = 0 := Iff.rfl

/-- The intersection of two existentially definable sets is again existentially definable: take
the disjoint union of the two witness types and the sum of squares of the two defining
exp-polynomials (after re-indexing them into the common witness block). Over `ℝ` the sum of
squares vanishes iff both summands do. -/
theorem ExpExistI_inter {κ : Type*} {X Y : Set (κ → ℝ)} (hX : ExpExistI X) (hY : ExpExistI Y) :
    ExpExistI (X ∩ Y) := by
  obtain ⟨μ, hμ, P, rfl⟩ := hX
  obtain ⟨ν, hν, Q, rfl⟩ := hY
  letI := hμ
  letI := hν
  refine ⟨μ ⊕ ν, inferInstance,
    MvPolynomial.rename (Sum.map (Sum.map id (Sum.inl : μ → μ ⊕ ν))
        (Sum.map id (Sum.inl : μ → μ ⊕ ν))) P ^ 2 +
    MvPolynomial.rename (Sum.map (Sum.map id (Sum.inr : ν → μ ⊕ ν))
        (Sum.map id (Sum.inr : ν → μ ⊕ ν))) Q ^ 2, ?_⟩
  ext z
  simp only [mem_ExpZero, Set.mem_inter_iff]
  constructor
  · rintro ⟨⟨u, hu⟩, ⟨v, hv⟩⟩
    refine ⟨Sum.elim u v, ?_⟩
    rw [expEval_add, expEval_pow, expEval_pow, expEval_rename_inl, expEval_rename_inr,
      sumElim_comp_inl, sumElim_comp_inr, hu, hv]
    ring
  · rintro ⟨y, hy⟩
    rw [expEval_add, expEval_pow, expEval_pow, expEval_rename_inl, expEval_rename_inr] at hy
    have h1 : expEval (Sum.elim z (y ∘ Sum.inl)) P = 0 := by
      have h2 : expEval (Sum.elim z (y ∘ Sum.inl)) P ^ 2 = 0 := by
        linarith [sq_nonneg (expEval (Sum.elim z (y ∘ Sum.inl)) P),
          sq_nonneg (expEval (Sum.elim z (y ∘ Sum.inr)) Q), hy]
      exact sq_eq_zero_iff.mp h2
    have h3 : expEval (Sum.elim z (y ∘ Sum.inr)) Q = 0 := by
      have h2 : expEval (Sum.elim z (y ∘ Sum.inr)) Q ^ 2 = 0 := by
        linarith [sq_nonneg (expEval (Sum.elim z (y ∘ Sum.inl)) P),
          sq_nonneg (expEval (Sum.elim z (y ∘ Sum.inr)) Q), hy]
      exact sq_eq_zero_iff.mp h2
    exact ⟨⟨y ∘ Sum.inl, h1⟩, ⟨y ∘ Sum.inr, h3⟩⟩

end Work.WilkiesB
