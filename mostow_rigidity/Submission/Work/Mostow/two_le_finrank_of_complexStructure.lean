import Mathlib

namespace Work.Mostow

/-- **A nonzero subspace carrying a complex structure has dimension at least two.**

Let `W ≠ ⊥` be a submodule of a finite-dimensional real inner product space `V`, `J : V →ₗ[ℝ] V`
with `J x ∈ W` and `J (J x) = -x` for all `x ∈ W`.  Then `2 ≤ Module.finrank ℝ ↥W`.

Route.  Pick `x ∈ W`, `x ≠ 0` (from `W ≠ ⊥`).  Then `x` and `J x` are linearly independent: if
`J x = t • x` for some real `t`, then `-x = J (J x) = t • (J x) = t^2 • x`, so `t^2 = -1` (as
`x ≠ 0`), impossible.  Hence `Submodule.span ℝ {x, J x} ≤ W` has `Module.finrank` two
(`finrank_span_eq_card` for the independent family `![x, J x]`, `Fintype.card (Fin 2) = 2`), and
`Submodule.finrank_mono` gives `2 ≤ Module.finrank ℝ ↥W`.-/
theorem two_le_finrank_of_complexStructure {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] (W : Submodule ℝ V) (J : V →ₗ[ℝ] V)
    (hW : W ≠ ⊥) (hJmem : ∀ x ∈ W, J x ∈ W) (hJ2 : ∀ x ∈ W, J (J x) = -x) :
    2 ≤ Module.finrank ℝ ↥W := by
  -- Extract a nonzero vector of `W`.
  obtain ⟨x, hxW, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hW
  -- `x` and `J x` are linearly independent, witnessed by `![J x, x]`.
  have hli : LinearIndependent ℝ ![J x, x] := by
    rw [linearIndependent_fin2]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    refine ⟨hx0, ?_⟩
    -- If `a • x = J x` for some real `a`, then `a ^ 2 + 1 = 0`, impossible.
    intro a ha
    have h1 : J (a • x) = -x := by rw [ha, hJ2 x hxW]
    have h2 : a • J x = -x := by rw [map_smul] at h1; exact h1
    have h3 : a • (a • x) = -x := by rw [ha]; exact h2
    rw [smul_smul] at h3
    have h5 : (a * a + 1) • x = 0 := by
      rw [add_smul, one_smul, h3, neg_add_cancel]
    have h6 : a * a + 1 = 0 := by
      rcases smul_eq_zero.mp h5 with h | h
      · exact h
      · exact absurd h hx0
    nlinarith [sq_nonneg a]
  -- The span of `{J x, x}` lies inside `W`.
  have hle : Submodule.span ℝ (Set.range ![J x, x]) ≤ W := by
    rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    fin_cases i
    · simpa using hJmem x hxW
    · simpa using hxW
  -- That span is two-dimensional.
  have hfin : Module.finrank ℝ ↥(Submodule.span ℝ (Set.range ![J x, x])) = 2 := by
    rw [finrank_span_eq_card hli, Fintype.card_fin]
  have hmono := Submodule.finrank_mono hle
  omega

end Work.Mostow
