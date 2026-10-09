import Mathlib
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

set_option linter.style.haveILetI false

open IntermediateField

namespace NK.TameStructureDeep.Degree

/-- A finite (separable) extension `F'` of `F` that contains a primitive `n`-th root of unity
witnesses the degree bound: any primitive `n`-th root of unity in a separable closure `E` of `F`
has minimal polynomial of degree at most `[F' : F]`.

Proof route: `IsSepClosed.lift : F' →ₐ[F] E` (via
`Commons.FieldTheory.SeparableClosure.nonempty_algHom_of_isSepClosure`), and every primitive
`n`-th root in `E` is a power of the image of `ψ` (`IsPrimitiveRoot.eq_pow_of_pow_eq_one`), so
`F⟮ζ⟯ ≤ F⟮φ ψ⟯`; use `IntermediateField.adjoin.finrank`, `Submodule.finrank_mono`, and
`minpoly.algHom_eq`;
`Commons.LinearAlgebra.FiniteDimensional.natDegree_minpoly_le_finrank` gives the last step. -/
theorem primitiveRoot_natDegree_le_finrank {F E F' : Type*} [Field F] [Field E] [Algebra F E]
    [IsSepClosure F E] [Field F'] [Algebra F F'] [FiniteDimensional F F']
    [Algebra.IsSeparable F F'] {n : ℕ} (hn : n ≠ 0) {ζ : E} (hζ : IsPrimitiveRoot ζ n)
    {ψ : F'} (hψ : IsPrimitiveRoot ψ n) :
    (minpoly F ζ).natDegree ≤ Module.finrank F F' := by
  haveI : IsSepClosed E := IsSepClosure.sep_closed F
  haveI : NeZero n := ⟨hn⟩
  have hnpos : 0 < n := Nat.pos_of_ne_zero hn
  -- An `F`-embedding of the finite separable extension `F'` into the separable closure `E`.
  let φ : F' →ₐ[F] E := IsSepClosed.lift
  have hφψ : IsPrimitiveRoot (φ ψ) n := hψ.map_of_injective φ.injective
  -- `ζ` is a power of `φ ψ`, hence lies in `F⟮φ ψ⟯`.
  obtain ⟨i, -, hzi⟩ := hφψ.eq_pow_of_pow_eq_one hζ.pow_eq_one
  have hmem : ζ ∈ IntermediateField.adjoin F ({φ ψ} : Set E) := by
    rw [← hzi]
    exact pow_mem (IntermediateField.mem_adjoin_simple_self F (φ ψ)) i
  have hintζ : IsIntegral F ζ :=
    IsIntegral.of_pow hnpos (by rw [hζ.pow_eq_one]; exact isIntegral_one)
  have hintφψ : IsIntegral F (φ ψ) :=
    IsIntegral.of_pow hnpos (by rw [hφψ.pow_eq_one]; exact isIntegral_one)
  have hle : F⟮ζ⟯ ≤ F⟮φ ψ⟯ := IntermediateField.adjoin_simple_le_iff.mpr hmem
  haveI : FiniteDimensional F F⟮φ ψ⟯ := IntermediateField.adjoin.finiteDimensional hintφψ
  calc (minpoly F ζ).natDegree
      = Module.finrank F F⟮ζ⟯ := (IntermediateField.adjoin.finrank hintζ).symm
    _ ≤ Module.finrank F F⟮φ ψ⟯ := IntermediateField.finrank_le_of_le_right hle
    _ = (minpoly F (φ ψ)).natDegree := IntermediateField.adjoin.finrank hintφψ
    _ = (minpoly F ψ).natDegree := by rw [minpoly.algHom_eq φ φ.injective ψ]
    _ ≤ Module.finrank F F' := minpoly.natDegree_le ψ

end NK.TameStructureDeep.Degree
