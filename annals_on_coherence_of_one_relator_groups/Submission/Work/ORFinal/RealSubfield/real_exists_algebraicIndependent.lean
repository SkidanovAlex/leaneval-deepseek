import Mathlib

set_option linter.style.haveILetI false

namespace Work.ORFinal.RealSubfield

/-- `ℝ` contains `n` algebraically independent elements over `ℚ`. -/
theorem real_exists_algebraicIndependent (n : ℕ) :
    ∃ y : Fin n → ℝ, AlgebraicIndependent ℚ y := by
  induction n with
  | zero => exact ⟨Fin.elim0, algebraicIndependent_empty_type⟩
  | succ n ih =>
    obtain ⟨y, hy⟩ := ih
    haveI : Countable (MvPolynomial (Fin n) ℚ) := by
      rw [← Cardinal.mk_le_aleph0_iff]
      refine (MvPolynomial.cardinalMk_le_max_lift (σ := Fin n) (R := ℚ)).trans ?_
      simp
    haveI hFc : Countable ↥(Algebra.adjoin ℚ (Set.range y)) := by
      rw [Algebra.adjoin_range_eq_range_aeval]
      exact (Set.countable_range (MvPolynomial.aeval y)).to_subtype
    obtain ⟨z, hz⟩ : ∃ z : ℝ, ¬ IsAlgebraic ↥(Algebra.adjoin ℚ (Set.range y)) z := by
      by_contra h
      simp only [not_exists, not_not] at h
      exact Cardinal.not_countable_real
        ((Algebraic.countable ↥(Algebra.adjoin ℚ (Set.range y)) ℝ).mono (fun z _ => h z))
    let f : Fin (n + 1) → Option (Fin n) :=
      fun i => if h : (i : ℕ) < n then some ⟨i, h⟩ else none
    let g : Option (Fin n) → Fin (n + 1) := fun o => o.elim (Fin.last n) Fin.castSucc
    have hgf : Function.LeftInverse g f := by
      intro i
      simp only [f, g]
      split_ifs with hi
      · exact Fin.ext (by simp)
      · have hlast : i = Fin.last n := by
          apply Fin.ext
          simp only [Fin.val_last]
          have := i.isLt
          omega
        rw [hlast]
        rfl
    have hf : Function.Injective f := hgf.injective
    exact ⟨(fun o : Option (Fin n) => o.elim z y) ∘ f,
      ((AlgebraicIndependent.option_iff (R := ℚ) (x := y) (a := z)).mpr ⟨hy, hz⟩).comp f hf⟩

end Work.ORFinal.RealSubfield
