import Mathlib.Combinatorics.Quiver.ReflQuiver
import Mathlib.RepresentationTheory.Rep.Basic
import Submission.NK.NUV2.RouteC.val_sequence

/-!
# The explicit `H⁰ × H² → H²` cup product (Route C, the character formula)

For a field extension `E / F` and `a ∈ Fˣ` the `H⁰ × H²` cup product `a ∪ c` of `a` with a class
`c ∈ H²(Gal(E/F), ℤ)` is the class obtained from `c` by the change of coefficients
`ℤ → Eˣ`, `n ↦ aⁿ` (a `G`-module map because `a` is fixed by `Gal(E/F)`).  This file provides it as
`NK.NUV2.RouteC.powHom`, together with its multiplicativity in `a`.

No general cup-product library is needed: `groupCohomology.map` is functorial.
-/

open CategoryTheory

namespace NK.NUV2.RouteC

variable {F E : Type} [Field F] [Field E] [Algebra F E]

/-- **The `H⁰ × H²` cup product with `a ∈ Fˣ`**, as a change of coefficients: the `ℤ[Gal(E/F)]`-module
map `ℤ → Eˣ`, `n ↦ aⁿ` (well defined because `a` is fixed by `Gal(E/F)`). -/
noncomputable def powHom (a : Fˣ) :
    Rep.trivial ℤ (E ≃ₐ[F] E) ℤ ⟶ Rep.ofAlgebraAutOnUnits F E :=
  Rep.ofHom
    { toLinearMap := AddMonoidHom.toIntLinearMap
        { toFun := fun n => n • (Additive.ofMul (Units.map (algebraMap F E).toMonoidHom a) :
            Additive Eˣ)
          map_zero' := by simp
          map_add' := fun m n => add_zsmul _ m n }
      isIntertwining' := fun σ => by
        have hfix : (Rep.ofAlgebraAutOnUnits F E).ρ σ
            (Additive.ofMul (Units.map (algebraMap F E).toMonoidHom a) : Additive Eˣ)
            = (Additive.ofMul (Units.map (algebraMap F E).toMonoidHom a) : Additive Eˣ) := by
          apply Additive.ofMul.injective
          apply Units.ext
          show σ ((Units.map (algebraMap F E).toMonoidHom a : Eˣ) : E)
            = ((Units.map (algebraMap F E).toMonoidHom a : Eˣ) : E)
          rw [show ((Units.map (algebraMap F E).toMonoidHom a : Eˣ) : E) = algebraMap F E a from
            rfl]
          exact σ.commutes a
        apply LinearMap.ext
        intro n
        rw [LinearMap.comp_apply, LinearMap.comp_apply, Rep.trivial_ρ, LinearMap.id_apply]
        show n • (Additive.ofMul (Units.map (algebraMap F E).toMonoidHom a) : Additive Eˣ)
          = (Rep.ofAlgebraAutOnUnits F E).ρ σ
              (n • (Additive.ofMul (Units.map (algebraMap F E).toMonoidHom a) : Additive Eˣ))
        have h1 : (Rep.ofAlgebraAutOnUnits F E).ρ σ
            (n • (Additive.ofMul (Units.map (algebraMap F E).toMonoidHom a) : Additive Eˣ))
            = n • ((Rep.ofAlgebraAutOnUnits F E).ρ σ
                (Additive.ofMul (Units.map (algebraMap F E).toMonoidHom a) : Additive Eˣ)) :=
          map_zsmul ((Rep.ofAlgebraAutOnUnits F E).ρ σ) n _
        rw [h1, hfix]
        rfl }

/-- **The underlying linear-map form of the multiplicativity** of the cup product in its `H⁰`-slot:
`(ab) ∪ - = (a ∪ -) + (b ∪ -)`. -/
theorem powHom_hom_mul (a b : Fˣ) :
    (powHom (E := E) (a * b)).hom.toLinearMap
      = (powHom (E := E) a).hom.toLinearMap + (powHom (E := E) b).hom.toLinearMap := by
  unfold powHom
  simp only [Rep.hom_ofHom]
  apply LinearMap.ext
  intro n
  show n • (Additive.ofMul (Units.map (algebraMap F E).toMonoidHom (a * b)) : Additive Eˣ)
    = n • (Additive.ofMul (Units.map (algebraMap F E).toMonoidHom a) : Additive Eˣ)
      + n • (Additive.ofMul (Units.map (algebraMap F E).toMonoidHom b) : Additive Eˣ)
  rw [map_mul, ofMul_mul, zsmul_add]

/-- **Multiplicativity of the cup product in its `H⁰`-slot.** -/
theorem powHom_mul (a b : Fˣ) :
    powHom (E := E) (a * b) = powHom (E := E) a + powHom (E := E) b := by
  apply Rep.hom_ext
  apply Representation.IntertwiningMap.ext
  rw [powHom_hom_mul]
  rfl

end NK.NUV2.RouteC
