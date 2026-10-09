import Mathlib.FieldTheory.Separable
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Commons.FieldTheory.Galois

theorem isSeparable_of_ringEquiv {k E k' E' : Type*} [Field k] [Field E] [Algebra k E] [Field k']
    [Field E'] [Algebra k' E'] (φ : k' ≃+* k) (ψ : E' ≃+* E)
    (hψ : ∀ x : k', ψ (algebraMap k' E' x) = algebraMap k E (φ x))
    [Algebra.IsSeparable k E] : Algebra.IsSeparable k' E' :=
  (Algebra.IsSeparable.iff_of_equiv_equiv φ ψ (RingHom.ext fun x => (hψ x).symm)).mpr
    (inferInstance : Algebra.IsSeparable k E)

end Commons.FieldTheory.Galois