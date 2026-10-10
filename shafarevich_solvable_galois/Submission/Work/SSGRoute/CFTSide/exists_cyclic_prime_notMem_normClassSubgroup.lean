import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.Topology.Algebra.Group.Quotient
import Submission.Work.SSGRoute.classField_exists_ramified
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# A non-`p`-th-power of `C_k` is a non-norm from some cyclic degree-`p` extension

The contrapositive of the `p`-power criterion in the idèle class group (`PTW`), combined with the
existence theorem of global class field theory at prime index
(`Work.SSGRoute.classField_exists_ramified`, which is unconditional given the two class-field
inputs `NK.CFTLib.artinReciprocityIdeal_proved` and `NK.CFTLib.fundamentalClassElement`).

This is the arithmetic input of the base case `φ¹` (nodes `E3` / `E3Ω`): if `a ∈ C_k` is not a
`p`-th power, then `a` is not a norm from some cyclic degree-`p` extension of `k`.
-/

namespace Work.SSGRoute

open scoped Classical

/-- **A non-`p`-th-power in `C_k` is not a norm from some cyclic degree-`p` extension.**

The `p`-power criterion `hPTW` (an element lying in every open index-`p` subgroup is a `p`-th
power) provides an open subgroup `V ≤ C_k` of index `p` with `a ∉ V`; the existence theorem
`Work.SSGRoute.classField_exists_ramified` realises `V = N_{L/k}C_L` for a Galois `L/k` of degree
`p`. -/
theorem exists_cyclic_prime_notMem_normClassSubgroup (k : Type) [Field k] [NumberField k]
    (p : ℕ) [Fact p.Prime] (a : NK.GlobalCFT.IdeleClassGroup k)
    (hPTW : ∀ x : NK.GlobalCFT.IdeleClassGroup k,
      (∀ V : Subgroup (NK.GlobalCFT.IdeleClassGroup k), V.FiniteIndex →
        IsOpen (V : Set (NK.GlobalCFT.IdeleClassGroup k)) → V.index = p → x ∈ V) →
      ∃ y : NK.GlobalCFT.IdeleClassGroup k, y ^ p = x)
    (ha : ¬ ∃ y : NK.GlobalCFT.IdeleClassGroup k, y ^ p = a) :
    ∃ (L : Type) (_ : Field L) (_ : NumberField L) (_ : Algebra k L) (_ : FiniteDimensional k L),
      IsGalois k L ∧ Module.finrank k L = p ∧
        a ∉ NK.GlobalCFT.Idele.normClassSubgroup k L := by
  have hV : ∃ V : Subgroup (NK.GlobalCFT.IdeleClassGroup k), V.FiniteIndex ∧
      IsOpen (V : Set (NK.GlobalCFT.IdeleClassGroup k)) ∧ V.index = p ∧ a ∉ V := by
    by_contra hcon
    push_neg at hcon
    exact ha (hPTW a (fun V h1 h2 h3 => hcon V h1 h2 h3))
  obtain ⟨V, hVfin, hVopen, hVindex, hVnot⟩ := hV
  obtain ⟨L, hFL, hNL, hAL, hfdL, hgal, hnorm, hdeg⟩ :=
    classField_exists_ramified NK.CFTLib.artinReciprocityIdeal_proved
      NK.CFTLib.fundamentalClassElement (K := k) p V hVfin hVopen hVindex
  exact ⟨L, hFL, hNL, hAL, hfdL, hgal, hdeg, by rw [hnorm]; exact hVnot⟩

end Work.SSGRoute
