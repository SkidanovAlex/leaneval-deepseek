import Mathlib
import Submission.NK.Reconstruct.Basic

/-!
# Agreement on the finite normal intermediate fields forces equality of `K`-automorphisms

Let `K` be a number field and let `K'/K` be a Galois extension (not necessarily finite).  If two
elements `u`, `v` of `Gal(K'/K)` restrict to the same `K`-automorphism of every intermediate
field `L` which is finite, normal over `K` and a number field, then `u = v`.

The point is that the finite *Galois* intermediate fields are cofinal in `K'`.  Indeed, by
infinite Galois theory (`Mathlib.FieldTheory.Galois.GaloisClosure`) every element `x : K'` lies
in `FiniteGaloisIntermediateField.adjoin K {x}`, the normal closure of `K(x)` inside `K'`, which
is finite and Galois over `K`; being a finite extension of the number field `K` it is itself a
number field (`NumberField.of_module_finite`).  This is the only place where `K` being a number
field is used: it supplies the `NumberField` instance required by the hypothesis, in order that
`L` may be regarded as a (finite) level of the reconstruction argument.
-/

namespace NK.Reconstruct

theorem eq_of_restrictNormalHom_eq {K K' : Type*} [Field K] [NumberField K] [Field K']
    [Algebra K K'] [IsGalois K K'] {u v : Gal(K'/K)}
    (h : ∀ (L : IntermediateField K K') [FiniteDimensional K L] [Normal K L] [NumberField ↥L],
      AlgEquiv.restrictNormalHom L u = AlgEquiv.restrictNormalHom L v) : u = v := by
  ext x
  -- the finite Galois level containing `x`
  let M : FiniteGaloisIntermediateField K K' := FiniteGaloisIntermediateField.adjoin K ({x} : Set K')
  let L : IntermediateField K K' := M.toIntermediateField
  have hx : x ∈ L :=
    FiniteGaloisIntermediateField.subset_adjoin K ({x} : Set K') (Set.mem_singleton x)
  have hfin : FiniteDimensional K L := M.finiteDimensional
  have hgal : IsGalois K L := M.isGalois
  have hnum : NumberField ↥L := NumberField.of_module_finite K ↥L
  -- `u` and `v` agree on `L`, hence on `x`
  have hh := h L
  have h4 := congrArg (fun f : Gal(L/K) => (f ⟨x, hx⟩ : K')) hh
  simpa [AlgEquiv.restrictNormalHom_apply] using h4

end NK.Reconstruct
