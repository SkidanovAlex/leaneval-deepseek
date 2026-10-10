import Mathlib.NumberTheory.NumberField.Basic
import Submission.Work.SSGRoute.ELFDefs
import Submission.Work.SSGRoute.localField_units_pTorsion_finite

namespace Work.SSGRoute

/-- The `p`-torsion of the additive group `Additive (K_w)ˣ` of the units of a local field is
finite.

Indeed, `p • a = 0` in `Additive (K_w)ˣ` means `(ofMul a) ^ p = 1`, i.e. `ofMul a` is a `p`-th
root of unity in the field `K_w`.  The set of those is finite: it is contained in the root set of
the nonzero polynomial `X ^ p - 1`, and Mathlib's `rootsOfUnity p K_w` (the `p`-th roots of unity
in the domain `K_w`) is finite.  The transport along `Additive.ofMul` is the explicit equivalence
`e` below. -/
theorem localUnits_additive_pTorsion_finite (K : Type) [Field K] [NumberField K]
    (w : NK.GlobalCFT.Place K) (p : ℕ) [Fact p.Prime] :
    Finite ↥(Work.SSGRoute.nsmulAddHom p (Additive ((NK.GlobalCFT.Place.localField K w)ˣ))).ker := by
  have h := localField_units_pTorsion_finite K w p
  let e : {u : (NK.GlobalCFT.Place.localField K w)ˣ // u ^ p = 1} ≃
      ↥(Work.SSGRoute.nsmulAddHom p (Additive ((NK.GlobalCFT.Place.localField K w)ˣ))).ker :=
    { toFun := fun u => ⟨Additive.ofMul u.1, by
        rw [AddMonoidHom.mem_ker, nsmulAddHom_apply]
        apply Additive.toMul.injective
        simp [u.2]⟩
      invFun := fun a => ⟨Additive.toMul a.1, by
        have ha : p • a.1 = 0 := a.2
        have := congrArg Additive.toMul ha
        simpa using this⟩
      left_inv := fun u => by simp
      right_inv := fun a => by simp }
  exact @Finite.of_equiv _ _ h e

end Work.SSGRoute
