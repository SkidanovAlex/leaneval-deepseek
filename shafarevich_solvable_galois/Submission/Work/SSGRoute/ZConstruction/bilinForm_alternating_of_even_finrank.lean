import Mathlib
import Submission.Work.SSGRoute.ZDataMup.exists_leftNondegenerate_bilinearForm
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute.ZConstruction

/-- Over a field `ZMod p`, a finite-dimensional vector space of **even** dimension carries a
non-degenerate alternating bilinear form.

Construction: since `finrank = m + m`, a basis indexed by `Fin m ⊕ Fin m` exists; let `g i` and
`h i` be the coordinate functionals of the `i`-th "left" resp. "right" basis vector (these are
`b.coord (Sum.inl i)` and `b.coord (Sum.inr i)`).  Set
`F := ∑ i, (g i) ⊗ (h i) - (h i) ⊗ (g i)`, the sum of the hyperbolic forms of the pairs
`(b (Sum.inl i), b (Sum.inr i))`.  Each summand is alternating (`a * b - b * a = 0`), so `F` is
alternating; and `F` is non-degenerate because `(F x) (b (Sum.inr j)) = g j x` and
`(F x) (b (Sum.inl j)) = -(h j x)`, so vanishing of `F x` forces all basis coordinates of `x` to
vanish.  (The hypothesis `p ≠ 2` is not needed for this construction.) -/
theorem bilinForm_alternating_of_even_finrank (p : ℕ) [Fact p.Prime] (hp : p ≠ 2) {V : Type}
    [AddCommGroup V] [Module (ZMod p) V] [FiniteDimensional (ZMod p) V]
    (heven : Even (Module.finrank (ZMod p) V)) :
    ∃ F : V →ₗ[ZMod p] V →ₗ[ZMod p] ZMod p,
      (∀ x : V, (∀ y : V, F x y = 0) → x = 0) ∧ ∀ x : V, F x x = 0 := by
  classical
  obtain ⟨m, hm⟩ := heven
  -- A basis indexed by the "hyperbolic" index set `Fin m ⊕ Fin m`.
  let b := (Module.finBasis (ZMod p) V).reindex
    (Fintype.equivOfCardEq (α := Fin (Module.finrank (ZMod p) V)) (β := Fin m ⊕ Fin m) (by
      simp [Fintype.card_sum, hm]))
  -- The two families of dual coordinate functionals.
  let g : Fin m → (V →ₗ[ZMod p] ZMod p) := fun i => b.coord (Sum.inl i)
  let h : Fin m → (V →ₗ[ZMod p] ZMod p) := fun i => b.coord (Sum.inr i)
  -- The alternating form: sum of the hyperbolic forms on the pairs `(b (inl i), b (inr i))`.
  let F : V →ₗ[ZMod p] V →ₗ[ZMod p] ZMod p :=
    ∑ i, ((g i).smulRight (h i) - (h i).smulRight (g i))
  refine ⟨F, ?_, ?_⟩
  · -- Non-degeneracy in the first variable.
    intro x hx
    have hF : ∀ (x y : V), F x y = ∑ i : Fin m, ((g i x) * (h i y) - (h i x) * (g i y)) := by
      intro x y
      simp only [F, LinearMap.sum_apply, LinearMap.sub_apply, LinearMap.smulRight_apply,
        LinearMap.smul_apply, smul_eq_mul]
    -- Evaluating `F x` on a "right" basis vector recovers the "left" coordinate.
    have hg : ∀ j : Fin m, g j x = 0 := by
      intro j
      have h0 : F x (b (Sum.inr j)) = 0 := hx (b (Sum.inr j))
      rw [hF x (b (Sum.inr j))] at h0
      have h1 : ∀ i ∈ (Finset.univ : Finset (Fin m)), i ≠ j →
          ((g i x) * (h i (b (Sum.inr j))) - (h i x) * (g i (b (Sum.inr j)))) = 0 := by
        intro i _ hij
        simp [h, g, Module.Basis.coord_apply, hij]
      have h2 : j ∉ (Finset.univ : Finset (Fin m)) →
          ((g j x) * (h j (b (Sum.inr j))) - (h j x) * (g j (b (Sum.inr j)))) = 0 :=
        fun hj => absurd (Finset.mem_univ j) hj
      have hsum : (∑ i : Fin m,
          ((g i x) * (h i (b (Sum.inr j))) - (h i x) * (g i (b (Sum.inr j))))) = g j x := by
        rw [Finset.sum_eq_single j h1 h2]
        simp [h, g, Module.Basis.coord_apply]
      rw [hsum] at h0
      exact h0
    -- Evaluating `F x` on a "left" basis vector recovers the (negated) "right" coordinate.
    have hh : ∀ j : Fin m, h j x = 0 := by
      intro j
      have h0 : F x (b (Sum.inl j)) = 0 := hx (b (Sum.inl j))
      rw [hF x (b (Sum.inl j))] at h0
      have h1 : ∀ i ∈ (Finset.univ : Finset (Fin m)), i ≠ j →
          ((g i x) * (h i (b (Sum.inl j))) - (h i x) * (g i (b (Sum.inl j)))) = 0 := by
        intro i _ hij
        simp [h, g, Module.Basis.coord_apply, hij]
      have h2 : j ∉ (Finset.univ : Finset (Fin m)) →
          ((g j x) * (h j (b (Sum.inl j))) - (h j x) * (g j (b (Sum.inl j)))) = 0 :=
        fun hj => absurd (Finset.mem_univ j) hj
      have hsum : (∑ i : Fin m,
          ((g i x) * (h i (b (Sum.inl j))) - (h i x) * (g i (b (Sum.inl j))))) = -(h j x) := by
        rw [Finset.sum_eq_single j h1 h2]
        simp [h, g, Module.Basis.coord_apply]
      rw [hsum] at h0
      exact neg_eq_zero.mp h0
    -- All basis coordinates of `x` vanish.
    have hrepr : b.repr x = 0 := by
      ext i
      rcases i with i | i
      · rw [← Module.Basis.coord_apply]; exact hg i
      · rw [← Module.Basis.coord_apply]; exact hh i
    exact b.repr.map_eq_zero_iff.mp hrepr
  · -- Alternation: `F x x = ∑ i, ((g i x) * (h i x) - (h i x) * (g i x)) = 0`.
    intro x
    simp only [F, LinearMap.sum_apply, LinearMap.sub_apply, LinearMap.smulRight_apply,
      LinearMap.smul_apply, smul_eq_mul]
    exact Finset.sum_eq_zero (fun i _ => sub_eq_zero.mpr (mul_comm _ _))

end Work.SSGRoute.ZConstruction
