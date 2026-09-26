import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.FreeModule.StrongRankCondition

/-!
# Surjectivity of a linear map whose range contains two independent vectors

If a real-linear map `T : E →ₗ[ℝ] F` into a two-dimensional real vector space
`F` has two linearly independent vectors `x y : F` in its range, then `T` is
surjective: its range is the whole space.

Proof: the span of `{x, y}` is contained in the range of `T`, and since
`x, y` are linearly independent the span of the two of them has finrank `2`,
which is the finrank of `F`; hence that span equals `⊤` and therefore so does
the range of `T`.
-/

namespace Commons.LinearAlgebra.Span

/-- The two-element set `{x, y}` equals the range of the family `![x, y]`. -/
lemma range_matrix_cons_two {F : Type*} [AddCommGroup F] [Module ℝ F] (x y : F) :
    Set.range (![x, y] : Fin 2 → F) = ({x, y} : Set F) := by
  ext z
  constructor
  · rintro ⟨i, rfl⟩
    fin_cases i <;> simp
  · intro hz
    rcases hz with rfl | rfl
    · exact ⟨0, rfl⟩
    · exact ⟨1, rfl⟩

theorem surjective_of_two_independent_in_range {E F : Type*}
    [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F] [FiniteDimensional ℝ F]
    (T : E →ₗ[ℝ] F) {x y : F}
    (hx : x ∈ LinearMap.range T) (hy : y ∈ LinearMap.range T)
    (hxy : LinearIndependent ℝ ![x, y])
    (hfin : Module.finrank ℝ F = 2) : LinearMap.range T = ⊤ := by
  -- The span of {x, y} has finrank two: `![x, y]` is an independent family
  -- indexed by `Fin 2`, so the finrank of its span equals `2`.
  have hfin_span : Module.finrank ℝ (Submodule.span ℝ ({x, y} : Set F)) = 2 := by
    rw [← range_matrix_cons_two x y]
    simpa using (finrank_span_eq_card hxy)
  -- hence it is the whole space, since `F` itself has finrank two.
  have hspan_top : Submodule.span ℝ ({x, y} : Set F) = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    rw [hfin_span, hfin]
  -- and it is contained in the range of `T`, because `x` and `y` are in it.
  have hspan_le : Submodule.span ℝ ({x, y} : Set F) ≤ LinearMap.range T := by
    rw [Submodule.span_le]
    intro z hz
    rcases hz with rfl | rfl
    · exact hx
    · exact hy
  -- putting these together, the range of `T` is `⊤`.
  exact le_antisymm le_top (by
    rw [← hspan_top]
    exact hspan_le)

end Commons.LinearAlgebra.Span