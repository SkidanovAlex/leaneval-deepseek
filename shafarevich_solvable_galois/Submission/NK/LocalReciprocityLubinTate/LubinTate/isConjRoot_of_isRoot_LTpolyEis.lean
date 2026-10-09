import Mathlib
import Submission.NK.LocalReciprocityLubinTate.LubinTate.DivisionPoints
import Submission.NK.LocalReciprocityLubinTate.LubinTate.LTpolyEis_shape
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace NK.LocalReciprocityLubinTate.LubinTate

universe u

open Polynomial

/-- **Two roots of the Eisenstein factor `f^{[n]}` are conjugate over `F`.**

The `n`-th Eisenstein factor `f^{[n]}(T) = f^{(n-1)}(T)^{q-1} + π` of the standard Lubin–Tate
polynomial is Eisenstein at the uniformiser `π`, hence irreducible over `F` and monic
(`NK.LocalReciprocityLubinTate.irreducible_LTpolyEis`,
`NK.LocalReciprocityLubinTate.LubinTate.LTpolyEis_shape`).  It is therefore the minimal
polynomial over `F` of each of its roots, so any two roots have the same minimal polynomial,
i.e. are conjugate (Milne, *CFT*, §I.3: the roots of `f^{[n]}` are exactly the primitive
`π^{n+1}`-division points, and `F(Λ_n)/F` is totally ramified of degree `(q-1)q^n` with the
primitive division points conjugate). -/
theorem isConjRoot_of_isRoot_LTpolyEis (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] (π : (↥(ValuativeRel.valuation F).integer)) (hπ : Irreducible π)
    (q n : ℕ) (hq : 2 ≤ q) {x y : AlgebraicClosure F}
    (hx : (Polynomial.aeval x) (NK.LocalReciprocityLubinTate.LTpolyEis (π : F) q n) = 0)
    (hy : (Polynomial.aeval y) (NK.LocalReciprocityLubinTate.LTpolyEis (π : F) q n) = 0) :
    IsConjRoot F x y :=
  -- `f^{[n]}` is irreducible over `F` (it is Eisenstein at `π`)
  have hirr : Irreducible (NK.LocalReciprocityLubinTate.LTpolyEis (π : F) q n) :=
    NK.LocalReciprocityLubinTate.irreducible_LTpolyEis F π hπ q n hq
  -- and monic, of degree `(q-1)q^n`
  have hmonic : (NK.LocalReciprocityLubinTate.LTpolyEis (π : F) q n).Monic :=
    (LTpolyEis_shape (π : F) q n hq).1
  -- so it is the minimal polynomial of each of its roots
  (minpoly.eq_of_irreducible_of_monic hirr hx hmonic).symm.trans
    (minpoly.eq_of_irreducible_of_monic hirr hy hmonic)

end NK.LocalReciprocityLubinTate.LubinTate
