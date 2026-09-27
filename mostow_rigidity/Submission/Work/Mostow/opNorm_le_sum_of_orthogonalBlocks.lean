import Mathlib

set_option linter.unusedVariables false

namespace Work.Mostow

/-- **The operator norm of a map that is block diagonal for an orthogonal decomposition is bounded
by the sum of its block bounds.**

Let `P : η → Submodule ℝ V` be a finite family of pairwise orthogonal submodules of a real inner
product space spanning it (`⨆ i, P i = ⊤`), let `T : V →L[ℝ] V` preserve each `P i`, and let
`c : η → ℝ` be nonnegative with `‖T x‖ ≤ c i * ‖x‖` for every `x ∈ P i`.  Then
`‖T x‖ ≤ (∑ i, c i) * ‖x‖` for every `x`.

Route.  Write `x = ∑ i, x_i` with `x_i ∈ P i` (from `x ∈ ⨆ i, P i` by
`Submodule.iSup_induction`/`Submodule.mem_iSup_of_mem`; `η` is finite, so the sup is a finite sum of
the pieces — alternatively use `Submodule.starProjection` and the fact that the star projections
onto pairwise orthogonal submodules with `⨆ i, P i = ⊤` sum to the identity).  Then
`T x = ∑ i, T x_i` with `T x_i ∈ P i`, so `‖T x‖ ≤ ∑ i ‖T x_i‖ ≤ ∑ i c i ‖x_i‖ ≤ (∑ i c i) * M`
where `M := max_i ‖x_i‖` (using `c i ≥ 0`), and `M ≤ ‖x‖` since `x` is an orthogonal sum:
`‖x‖² = ∑ i ‖x_i‖²` (from pairwise orthogonality) so `‖x_i‖ ≤ ‖x‖` for each `i`
(and `η` nonempty; the `η = ∅` case is trivial since then `⨆ i, P i = ⊥ = ⊤` forces `x = 0`).
No finite-dimensionality of `V` is needed. -/
theorem opNorm_le_sum_of_orthogonalBlocks {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    {η : Type*} [Fintype η] (P : η → Submodule ℝ V)
    (horth : ∀ i j : η, i ≠ j → ∀ x ∈ P i, ∀ y ∈ P j, inner ℝ x y = 0)
    (hspan : ⨆ i, P i = ⊤)
    (T : V →L[ℝ] V) (hT : ∀ i, ∀ x ∈ P i, T x ∈ P i) (c : η → ℝ) (hc : ∀ i, 0 ≤ c i)
    (hTc : ∀ i, ∀ x ∈ P i, ‖T x‖ ≤ c i * ‖x‖) :
    ∀ x : V, ‖T x‖ ≤ (∑ i, c i) * ‖x‖ := by
  classical
  intro x
  -- Decompose `x = ∑ i, a i` with `a i ∈ P i`.
  have hxsup : x ∈ (⨆ i, P i : Submodule ℝ V) := by rw [hspan]; exact Submodule.mem_top
  obtain ⟨a, ha, hax⟩ :=
    Submodule.iSup_induction P
      (motive := fun y : V => ∃ a : η → V, (∀ i, a i ∈ P i) ∧ ∑ i, a i = y)
      hxsup
      (fun i y hy => ⟨Function.update (0 : η → V) i y,
        fun j => by
          rcases eq_or_ne j i with h | h
          · rw [h, Function.update_self]; exact hy
          · rw [Function.update_of_ne h]; exact (P j).zero_mem,
        by
          rw [Finset.sum_eq_single_of_mem i (Finset.mem_univ i)
            (fun j _ hj => by rw [Function.update_of_ne hj]; rfl)]
          simp⟩)
      ⟨0, fun i => (P i).zero_mem, by simp⟩
      (fun y z ⟨b, hb, hby⟩ ⟨d, hd, hdz⟩ =>
        ⟨fun i => b i + d i, fun i => (P i).add_mem (hb i) (hd i),
          by rw [Finset.sum_add_distrib, hby, hdz]⟩)
  have hTx : T x = ∑ i, T (a i) := by rw [← hax, map_sum]
  -- Each block of the decomposition is dominated by `‖x‖`.
  have hbound : ∀ i, ‖a i‖ ≤ ‖x‖ := by
    intro i
    have hsplit : a i + ∑ j ∈ Finset.univ.erase i, a j = x := by
      rw [Finset.add_sum_erase Finset.univ (fun j => a j) (Finset.mem_univ i), hax]
    have hinner : inner ℝ (a i) (∑ j ∈ Finset.univ.erase i, a j) = 0 := by
      rw [inner_sum]
      refine Finset.sum_eq_zero (fun j hj => ?_)
      rw [Finset.mem_erase] at hj
      exact horth i j (Ne.symm hj.1) (a i) (ha i) (a j) (ha j)
    have hnorm : ‖x‖ * ‖x‖ = ‖a i‖ * ‖a i‖
        + ‖∑ j ∈ Finset.univ.erase i, a j‖ * ‖∑ j ∈ Finset.univ.erase i, a j‖ := by
      have := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero (a i)
        (∑ j ∈ Finset.univ.erase i, a j) hinner
      rw [hsplit] at this
      exact this
    have h2 : ‖a i‖ ^ 2 ≤ ‖x‖ ^ 2 := by
      calc ‖a i‖ ^ 2 = ‖a i‖ * ‖a i‖ := pow_two _
        _ ≤ ‖a i‖ * ‖a i‖ + ‖∑ j ∈ Finset.univ.erase i, a j‖ * ‖∑ j ∈ Finset.univ.erase i, a j‖ :=
            le_add_of_nonneg_right (mul_self_nonneg _)
        _ = ‖x‖ * ‖x‖ := hnorm.symm
        _ = ‖x‖ ^ 2 := (pow_two _).symm
    have h3 := sq_le_sq.mp h2
    simpa using h3
  calc ‖T x‖ = ‖∑ i, T (a i)‖ := by rw [hTx]
    _ ≤ ∑ i, ‖T (a i)‖ := norm_sum_le Finset.univ (fun i => T (a i))
    _ ≤ ∑ i, c i * ‖a i‖ := Finset.sum_le_sum (fun i _ => hTc i (a i) (ha i))
    _ ≤ ∑ i, c i * ‖x‖ :=
        Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (hbound i) (hc i))
    _ = (∑ i, c i) * ‖x‖ := by rw [Finset.sum_mul]

end Work.Mostow
