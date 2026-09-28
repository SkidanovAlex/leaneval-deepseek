import Mathlib

set_option autoImplicit false

namespace Work.Q44Geom

open Module

/-- Prepending a vector `x` to a family `Fin.append w u` (giving the family `[x, w..., u...]`
indexed by `Fin (m + 1 + n)`) and then rewriting it as `Fin.append (Fin.cons x w) u`
(indexed by `Fin ((m + 1) + n)`) is only a reindexing of the index set: the two families
differ by the bijection `Fin.cast (Nat.add_right_comm m 1 n)`.

This is the "one-step extension" interface used to build an extended basis in
`complBasis`: the extension lemmas produce linear independence of `Fin.cons x (Fin.append w u)`,
and this lemma transports it to the `Fin.append`-shaped family. -/
private lemma linearIndependent_append_cons {K V : Type*} [Semiring K] [AddCommMonoid V]
    [Module K V] {m n : ℕ} {x : V} {w : Fin m → V} {u : Fin n → V}
    (h : LinearIndependent K (Fin.cons x (Fin.append w u))) :
    LinearIndependent K (Fin.append (Fin.cons x w) u) := by
  rw [Fin.append_cons]
  exact h.comp _ (Fin.cast_injective _)

/-- Any linearly independent pair of vectors of `ℚ^5` can be completed to a basis of `ℚ^5`,
with the two given vectors placed last. -/
theorem complBasis (b₁ b₂ : Fin 5 → ℚ) (hb : LinearIndependent ℚ ![b₁, b₂]) :
    ∃ w : Fin 3 → (Fin 5 → ℚ),
      LinearIndependent ℚ (Fin.append w ![b₁, b₂]) ∧
      Submodule.span ℚ (Set.range (Fin.append w ![b₁, b₂])) = ⊤ := by
  have hfr : Module.finrank ℚ (Fin 5 → ℚ) = 5 := by
    rw [Module.finrank_fintype_fun_eq_card]; simp
  -- Start with the empty extension: `![b₁, b₂]` is linearly independent.
  have hbase : LinearIndependent ℚ
      (Fin.append (Fin.elim0 : Fin 0 → (Fin 5 → ℚ)) ![b₁, b₂]) := by
    rw [Fin.elim0_append]
    exact hb.comp _ (Fin.cast_injective _)
  -- Repeatedly prepend a new vector, keeping the family of the shape `Fin.append w ![b₁, b₂]`.
  obtain ⟨x₁, hx₁⟩ := exists_linearIndependent_cons_of_lt_finrank hbase (by rw [hfr]; norm_num)
  have h₁ : LinearIndependent ℚ
      (Fin.append (Fin.cons x₁ (Fin.elim0 : Fin 0 → (Fin 5 → ℚ))) ![b₁, b₂]) :=
    linearIndependent_append_cons hx₁
  obtain ⟨x₂, hx₂⟩ := exists_linearIndependent_cons_of_lt_finrank h₁ (by rw [hfr]; norm_num)
  have h₂ : LinearIndependent ℚ
      (Fin.append (Fin.cons x₂ (Fin.cons x₁ (Fin.elim0 : Fin 0 → (Fin 5 → ℚ))))
        ![b₁, b₂]) :=
    linearIndependent_append_cons hx₂
  obtain ⟨x₃, hx₃⟩ := exists_linearIndependent_cons_of_lt_finrank h₂ (by rw [hfr]; norm_num)
  have h₃ : LinearIndependent ℚ
      (Fin.append (Fin.cons x₃ (Fin.cons x₂ (Fin.cons x₁ (Fin.elim0 : Fin 0 → (Fin 5 → ℚ)))))
        ![b₁, b₂]) :=
    linearIndependent_append_cons hx₃
  refine ⟨Fin.cons x₃ (Fin.cons x₂ (Fin.cons x₁ (Fin.elim0 : Fin 0 → (Fin 5 → ℚ)))), h₃, ?_⟩
  -- Five linearly independent vectors in a five-dimensional space span it.
  exact LinearIndependent.span_eq_top_of_card_eq_finrank h₃ (by rw [Fintype.card_fin, hfr])

end Work.Q44Geom
