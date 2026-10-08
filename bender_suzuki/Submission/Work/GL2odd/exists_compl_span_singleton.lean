import Mathlib

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.GL2odd

/-- Every nonzero vector `e` of `(ZMod p)²` (`p` prime) has a "complementary" vector `f`
whose span is a complement of the span of `e`.  Concretely, if `e 1 ≠ 0` take `f` to be the
first standard basis vector, and if `e 1 = 0` (so `e 0 ≠ 0`) take `f` to be the second one. -/
theorem exists_compl_span_singleton {p : ℕ} [Fact p.Prime] (e : Fin 2 → ZMod p)
    (he : e ≠ 0) : ∃ f : Fin 2 → ZMod p,
      Submodule.span (ZMod p) {e} ⊔ Submodule.span (ZMod p) {f} = ⊤ := by
  classical
  by_cases h1 : e 1 = 0
  · refine ⟨Pi.single (1 : Fin 2) (1 : ZMod p), ?_⟩
    have h0 : e 0 ≠ 0 := by
      intro h
      apply he
      funext i
      fin_cases i
      · exact h
      · exact h1
    rw [Submodule.eq_top_iff']
    intro v
    have hs0 : Pi.single (0 : Fin 2) (1 : ZMod p) ∈
        Submodule.span (ZMod p) {e} ⊔
          Submodule.span (ZMod p) {Pi.single (1 : Fin 2) (1 : ZMod p)} := by
      apply Submodule.mem_sup_left
      have key : (e 0)⁻¹ • e = Pi.single (0 : Fin 2) (1 : ZMod p) := by
        funext i; fin_cases i <;> simp [h1, h0]
      rw [← key]
      exact Submodule.smul_mem _ _ (Submodule.subset_span (by simp))
    have hs1 : Pi.single (1 : Fin 2) (1 : ZMod p) ∈
        Submodule.span (ZMod p) {e} ⊔
          Submodule.span (ZMod p) {Pi.single (1 : Fin 2) (1 : ZMod p)} :=
      Submodule.mem_sup_right (Submodule.subset_span (by simp))
    rw [show v = v 0 • Pi.single (0 : Fin 2) (1 : ZMod p)
        + v 1 • Pi.single (1 : Fin 2) (1 : ZMod p) from by
      funext i; fin_cases i <;> simp]
    exact Submodule.add_mem _
      (Submodule.smul_mem _ _ hs0)
      (Submodule.smul_mem _ _ hs1)
  · refine ⟨Pi.single (0 : Fin 2) (1 : ZMod p), ?_⟩
    rw [Submodule.eq_top_iff']
    intro v
    have hs0 : Pi.single (0 : Fin 2) (1 : ZMod p) ∈
        Submodule.span (ZMod p) {e} ⊔
          Submodule.span (ZMod p) {Pi.single (0 : Fin 2) (1 : ZMod p)} :=
      Submodule.mem_sup_right (Submodule.subset_span (by simp))
    have hs1 : Pi.single (1 : Fin 2) (1 : ZMod p) ∈
        Submodule.span (ZMod p) {e} ⊔
          Submodule.span (ZMod p) {Pi.single (0 : Fin 2) (1 : ZMod p)} := by
      have key : (e 1)⁻¹ • (e - (e 0) • Pi.single (0 : Fin 2) (1 : ZMod p))
          = Pi.single (1 : Fin 2) (1 : ZMod p) := by
        funext i; fin_cases i <;> simp [h1]
      rw [← key]
      exact Submodule.smul_mem _ _ (Submodule.sub_mem _
        (Submodule.mem_sup_left (Submodule.subset_span (by simp)))
        (Submodule.smul_mem _ _
          (Submodule.mem_sup_right (Submodule.subset_span (by simp)))))
    rw [show v = v 0 • Pi.single (0 : Fin 2) (1 : ZMod p)
        + v 1 • Pi.single (1 : Fin 2) (1 : ZMod p) from by
      funext i; fin_cases i <;> simp]
    exact Submodule.add_mem _
      (Submodule.smul_mem _ _ hs0)
      (Submodule.smul_mem _ _ hs1)

end Work.GL2odd
