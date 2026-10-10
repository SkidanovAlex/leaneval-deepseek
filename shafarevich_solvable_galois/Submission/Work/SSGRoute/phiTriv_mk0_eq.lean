import Mathlib.Combinatorics.Quiver.ReflQuiver
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RepresentationTheory.Rep.Res
import Mathlib.Algebra.Homology.DerivedCategory.Ext.Map
import Submission.Work.SSGRoute.PTDefsOmega
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute

open SSGRoute.PTExt CategoryTheory

/-- `phiTriv` of a degree-zero coefficient class `mk₀ c` is the Yoneda pairing of `h` with the
pushed-forward coefficient map `trivRes _ V ≫ res c ≫ classIncl`.  Both sides are composite `Ext`
classes: the equality is the associativity of Yoneda composition together with the functoriality
of `Ext.mk₀` (and of `Ext.mapExactFunctor`). -/
theorem phiTriv_mk0_eq {k K L : Type} [Field k] [NumberField k] [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra k K] [Algebra k L] [Algebra K L] [IsScalarTower k K L]
    [IsGalois k K] (V : Type) [AddCommGroup V] [Module Coeff V]
    (c : Rep.trivial Coeff (K ≃ₐ[k] K) V ⟶ classesK k K) {s : ℕ}
    (h : extH (Rep.trivial Coeff (L ≃ₐ[k] L) V) s) :
    phiTriv (k := k) (K := K) (L := L) V (Abelian.Ext.mk₀ c) h =
      h.comp (Abelian.Ext.mk₀ (trivRes (galRes k K L) V ≫
        (Rep.resFunctor (galRes k K L)).map c ≫ classIncl k K L)) (add_zero s) := by
  simp only [phiTriv, phiAt, levelPair, extRes, Abelian.Ext.mapExactFunctor_mk₀,
    Abelian.Ext.mk₀_comp_mk₀, Abelian.Ext.comp_assoc_of_second_deg_zero]

end Work.SSGRoute
