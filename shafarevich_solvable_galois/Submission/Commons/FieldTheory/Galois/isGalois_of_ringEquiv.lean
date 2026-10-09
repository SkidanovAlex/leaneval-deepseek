import Mathlib.FieldTheory.Galois.Basic
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Commons.FieldTheory.Galois

/-- **Galois-ness is transported along a compatible pair of ring isomorphisms.**

If `E / B` is a finite Galois extension and `eB : B ≃+* B₀`, `eE : E ≃+* E₀` are ring
isomorphisms compatible with the algebra maps (`eE (algebraMap B E x) = algebraMap B₀ E₀ (eB x)`),
then `E₀ / B₀` is Galois. -/
theorem isGalois_of_ringEquiv {B E B₀ E₀ : Type*} [Field B] [Field E] [Field B₀] [Field E₀]
    [Algebra B E] [Algebra B₀ E₀] (eB : B ≃+* B₀) (eE : E ≃+* E₀)
    (h : ∀ x : B, eE (algebraMap B E x) = algebraMap B₀ E₀ (eB x)) [IsGalois B E] :
    IsGalois B₀ E₀ := by
  -- `IsGalois` is separable together with normal; both are preserved when the pair of
  -- ring isomorphisms is compatible with the structure maps.
  exact IsGalois.of_equiv_equiv (f := eB) (g := eE) (RingHom.ext fun x => (h x).symm)

end Commons.FieldTheory.Galois