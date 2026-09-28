import Mathlib

set_option autoImplicit false

namespace Work.Q44Geom

/-- Two `ℤ`-linearly independent vectors `f 0, f 1` of an arbitrary `ℤ`-module of the form
`ι → ℤ` cannot both be integer multiples of a common vector `x` (in particular neither of
them lies in the `ℤ`-span `ℤ • x` of `x`).

Concretely, if `f 0 = c₀ • x` and `f 1 = c₁ • x` then the nontrivial combination
`c₁ • f 0 - c₀ • f 1 = 0` forces `c₀ = c₁ = 0`; hence `f 0 = 0`, contradicting linear
independence via the relation `1 • f 0 = 0`. -/
lemma not_mem_zspan_of_linIndep_two {ι : Type*} [Fintype ι] (x : ι → ℤ) {f : Fin 2 → (ι → ℤ)}
    (hf : LinearIndependent ℤ f) :
    (∀ c : ℤ, f 0 ≠ c • x) ∨ (∀ c : ℤ, f 1 ≠ c • x) := by
  by_contra h
  push Not at h
  obtain ⟨⟨c0, hc0⟩, ⟨c1, hc1⟩⟩ := h
  have key := Fintype.linearIndependent_iff.mp hf
  -- The nontrivial relation `c₁ • f 0 - c₀ • f 1 = 0` obtained from `f 0 = c₀ • x`,
  -- `f 1 = c₁ • x`, whence linear independence forces `c₀ = c₁ = 0`.
  have hrel : (∑ i : Fin 2, (![c1, -c0] : Fin 2 → ℤ) i • f i) = 0 := by
    rw [Fin.sum_univ_two]
    rw [hc0, hc1]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [smul_smul, smul_smul, ← add_smul]
    have : c1 * c0 + -c0 * c1 = 0 := by ring
    rw [this, zero_smul]
  have hc1' : c1 = 0 := by
    have := key (![c1, -c0] : Fin 2 → ℤ) hrel 0
    simpa using this
  have hc0' : c0 = 0 := by
    have h : -c0 = 0 := by
      have := key (![c1, -c0] : Fin 2 → ℤ) hrel 1
      simpa using this
    exact neg_eq_zero.mp h
  -- Now `f 0 = c₀ • x = 0`, and `1 • f 0 = 0` again contradicts linear independence.
  have hf0 : f 0 = 0 := by rw [hc0, hc0', zero_smul]
  have hrel2 : (∑ i : Fin 2, (![1, 0] : Fin 2 → ℤ) i • f i) = 0 := by
    rw [Fin.sum_univ_two]
    simp [hf0]
  have hone : (1 : ℤ) = 0 := key (![1, 0] : Fin 2 → ℤ) hrel2 0
  exact one_ne_zero hone

end Work.Q44Geom
