import Mathlib
import Submission.Work.WilkiesB.Defs

set_option linter.style.haveILetI false

namespace Work.WilkiesB

/-- The union of two `ExpExistI` sets is `ExpExistI`: take the product of the two defining
exp-polynomials, the witnesses being the sum of the two witness blocks. -/
theorem ExpExistI_union {κ : Type*} {X Y : Set (κ → ℝ)} (hX : ExpExistI X) (hY : ExpExistI Y) :
    ExpExistI (X ∪ Y) := by
  obtain ⟨μ, hμ, P, rfl⟩ := hX
  obtain ⟨ν, hν, Q, rfl⟩ := hY
  classical
  letI := hμ
  letI := hν
  refine ⟨μ ⊕ ν, inferInstance,
    MvPolynomial.rename (polyMap (Sum.map id (Sum.inl : μ → μ ⊕ ν))) P *
      MvPolynomial.rename (polyMap (Sum.map id (Sum.inr : ν → μ ⊕ ν))) Q, ?_⟩
  ext x
  simp only [ExpZero, Set.mem_union, Set.mem_ofPred_eq]
  constructor
  · rintro (⟨u, hu⟩ | ⟨v, hv⟩)
    · refine ⟨Sum.elim u (fun _ : ν => (0 : ℝ)), ?_⟩
      have h1 : (Sum.elim u (fun _ : ν => (0 : ℝ))) ∘ Sum.inl = u := by
        funext i; rfl
      simp only [expEval_mul, expEval_rename, sumElim_comp_map_id, h1, hu, zero_mul]
    · refine ⟨Sum.elim (fun _ : μ => (0 : ℝ)) v, ?_⟩
      have h2 : (Sum.elim (fun _ : μ => (0 : ℝ)) v) ∘ Sum.inr = v := by
        funext i; rfl
      simp only [expEval_mul, expEval_rename, sumElim_comp_map_id, h2, hv, mul_zero]
  · rintro ⟨w, hw⟩
    simp only [expEval_mul, expEval_rename, sumElim_comp_map_id] at hw
    rcases mul_eq_zero.mp hw with h | h
    · exact Or.inl ⟨w ∘ Sum.inl, h⟩
    · exact Or.inr ⟨w ∘ Sum.inr, h⟩

end Work.WilkiesB
