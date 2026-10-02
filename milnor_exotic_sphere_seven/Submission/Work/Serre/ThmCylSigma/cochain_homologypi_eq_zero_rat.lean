import Mathlib

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Statement C: a cycle of a cochain complex of `ℚ`-modules with vanishing class is a coboundary

For a cochain complex `K` of `ℚ`-modules, a cycle `z ∈ K.cycles (n+1)` whose homology class
`K.homologyπ (n+1) z` vanishes is the image of an `n`-cochain under the differential
`K.d n (n+1)`.

This is the elementwise form of the exactness of

  `K.X n --K.d n (n+1)--> K.cycles (n+1) --K.homologyπ (n+1)--> K.homology (n+1)`,

which holds because `K.homologyπ (n+1)` is a cokernel of `K.toCycles n (n+1)`
(`HomologicalComplex.homologyIsCokernel`), so that the associated short complex is exact
(`ShortComplex.exact_of_g_is_cokernel`); exactness is then read off on elements using
`ShortComplex.exact_iff_of_hasForget` in the concrete category `ModuleCat ℚ`.
-/

namespace Work.Serre.ThmCylSigma

open CategoryTheory

/-- In a short complex `S` of `R`-modules, the morphism `S.homologyπ` is the cokernel of
`S.toCycles`; consequently a cycle of `S` whose homology class vanishes is a boundary.
This is stated for an arbitrary ring `R`; the case needed below is `R = ℚ`. -/
lemma exists_toCycles_eq_of_homologyπ_eq_zero {R : Type*} [Ring R]
    (S : ShortComplex (ModuleCat R)) (z : S.cycles) (h : S.homologyπ z = 0) :
    ∃ y : S.X₁, S.toCycles y = z := by
  have hT : (ShortComplex.mk S.toCycles S.homologyπ S.toCycles_comp_homologyπ).Exact :=
    ShortComplex.exact_of_g_is_cokernel _ S.homologyIsCokernel
  obtain ⟨y, hy⟩ := (ShortComplex.exact_iff_of_hasForget
    (ShortComplex.mk S.toCycles S.homologyπ S.toCycles_comp_homologyπ)).mp hT z (by simpa using h)
  exact ⟨y, by simpa using hy⟩

theorem cochain_homologypi_eq_zero_rat (K : CochainComplex (ModuleCat ℚ) ℕ) (n : ℕ)
    (z : K.cycles (n + 1)) (h : K.homologyπ (n + 1) z = 0) :
    ∃ y : K.X n, (K.d n (n + 1)).hom y = (K.iCycles (n + 1)).hom z := by
  -- `K.homologyπ (n+1)` is the cokernel of `K.toCycles n (n+1)`: the short complex
  -- `K.X n ⟶ K.cycles (n+1) ⟶ K.homology (n+1)` is exact in the middle.
  have hi : (ComplexShape.up ℕ).prev (n + 1) = n :=
    ComplexShape.prev_eq' _ (ComplexShape.up_mk n (n + 1) rfl)
  have hT : (ShortComplex.mk (K.toCycles n (n + 1)) (K.homologyπ (n + 1))
      (K.toCycles_comp_homologyπ n (n + 1))).Exact :=
    ShortComplex.exact_of_g_is_cokernel _ (K.homologyIsCokernel n (n + 1) hi)
  -- Exactness, read on elements: `z` lifts along `K.toCycles n (n+1)`.
  obtain ⟨y, hy⟩ := (ShortComplex.exact_iff_of_hasForget
      (ShortComplex.mk (K.toCycles n (n + 1)) (K.homologyπ (n + 1))
        (K.toCycles_comp_homologyπ n (n + 1)))).mp hT z (by simpa using h)
  have hy' : (ConcreteCategory.hom (K.toCycles n (n + 1))) y = z := by simpa using hy
  refine ⟨y, ?_⟩
  -- `K.toCycles n (n+1) ≫ K.iCycles (n+1) = K.d n (n+1)`
  have h3 := congrArg (fun f => (ConcreteCategory.hom f) y) (K.toCycles_i n (n + 1))
  simp only [ConcreteCategory.comp_apply] at h3
  rw [← hy']
  exact h3.symm

end Work.Serre.ThmCylSigma
