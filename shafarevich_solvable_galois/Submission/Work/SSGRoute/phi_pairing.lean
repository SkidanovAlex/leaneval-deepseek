import Mathlib
import Submission.Work.SSGRoute.PTDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Pairing relations for the `φ¹` pairing of the Poitou–Tate `Ext` core

The pairing at level `L` (`SSGRoute.PTExt.phiAt`) is the Yoneda product of an inflated `Ext`-class
with a Galois cohomology class. This file records the two functoriality relations of that pairing,
which are used by the dévissage `Work.SSGRoute.phi1_mono_pgroup`:

* `phiAt_mk₀_comp`: contravariance in the first (`Ext`) variable;
* `phiAt_comp_mk₀`: covariance in the second (cohomology) variable.

Both are formal consequences of `Ext.mapExactFunctor`-functoriality and associativity of the Yoneda
product (`Ext.comp_assoc`), and hold with no sign.
-/

namespace Work.SSGRoute

open SSGRoute.PTExt CategoryTheory

section Relations

variable {k K : Type} [Field k] [NumberField k] [Field K] [NumberField K] [Algebra k K]
  [FiniteDimensional k K] [IsGalois k K]

/-- **Pairing relation (contravariance in the first variable).** For `i : M' ⟶ M` a morphism of
`Gal(K/k)`-modules and `x ∈ Ext¹_G(M, C_K)`, pulling `x` back along `i` and pairing with
`h ∈ H¹(Gal(L/k), M')` equals pairing `x` with the push-forward of `h` along `i`. -/
theorem phiAt_mk₀_comp {M M' : Rep Coeff (K ≃ₐ[k] K)} (i : M' ⟶ M)
    (x : Abelian.Ext M (classesK k K) 1)
    (L : Type) [Field L] [NumberField L] [Algebra k L] [Algebra K L] [IsScalarTower k K L]
    [FiniteDimensional k L] [IsGalois k L]
    (h : extH (Rep.res (galRes k K L) M') 1) :
    phiAt (k := k) (K := K) (L := L) ((Abelian.Ext.mk₀ i).comp x (zero_add 1)) h =
      phiAt (k := k) (K := K) (L := L) x
        (h.comp (Abelian.Ext.mk₀ ((Rep.resFunctor (galRes k K L)).map i)) (add_zero 1)) := by
  simp only [phiAt, levelPair, extRes, Abelian.Ext.mapExactFunctor_comp,
    Abelian.Ext.mapExactFunctor_mk₀, Abelian.Ext.comp_assoc_of_second_deg_zero,
    Abelian.Ext.comp_assoc_of_third_deg_zero]

/-- **Pairing relation (covariance in the second variable).** For `π : M ⟶ M₂` and
`y ∈ Ext¹_G(M₂, C_K)`, pushing `y` forward along `π` and pairing with `h ∈ H¹(Gal(L/k), M)` equals
pairing `y` with the image of `h` under `H¹(Gal(L/k), M) → H¹(Gal(L/k), M₂)`. -/
theorem phiAt_comp_mk₀ {M M₂ : Rep Coeff (K ≃ₐ[k] K)} (π : M ⟶ M₂)
    (y : Abelian.Ext M₂ (classesK k K) 1)
    (L : Type) [Field L] [NumberField L] [Algebra k L] [Algebra K L] [IsScalarTower k K L]
    [FiniteDimensional k L] [IsGalois k L]
    (h : extH (Rep.res (galRes k K L) M) 1) :
    phiAt (k := k) (K := K) (L := L) ((Abelian.Ext.mk₀ π).comp y (zero_add 1)) h =
      phiAt (k := k) (K := K) (L := L) y
        (h.comp (Abelian.Ext.mk₀ ((Rep.resFunctor (galRes k K L)).map π)) (add_zero 1)) := by
  simp only [phiAt, levelPair, extRes, Abelian.Ext.mapExactFunctor_comp,
    Abelian.Ext.mapExactFunctor_mk₀, Abelian.Ext.comp_assoc_of_second_deg_zero,
    Abelian.Ext.comp_assoc_of_third_deg_zero]

end Relations

end Work.SSGRoute
