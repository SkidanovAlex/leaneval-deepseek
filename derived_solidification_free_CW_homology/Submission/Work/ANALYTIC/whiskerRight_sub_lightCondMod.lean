import Mathlib

namespace Work.ANALYTIC

open CategoryTheory Limits MonoidalCategory MonoidalClosed LightCondensed

/-! ## Additivity of the tensor product of light condensed `R`-modules

Mathlib does not currently provide a `MonoidalPreadditive` instance for `LightCondMod R`, i.e. the
statement that the monoidal structure is additive in each variable.  We only need the case that
matters here, tensoring with `𝟙 V` on the right: `(f - g) ▷ V = f ▷ V - g ▷ V`.

The proof does not need to know anything about how the monoidal structure on `LightCondMod R` is
built.  It uses only that it is (symmetric) monoidal closed:

* `tensorLeft V` has a right adjoint (`ihom V`, from the `Closed V` structure coming from
  `MonoidalClosed (LightCondMod R)`), hence preserves colimits, hence preserves binary coproducts,
  hence preserves binary biproducts, hence is additive
  (`Functor.additive_of_preservesBinaryBiproducts`).
* In a braided monoidal category the braiding identifies `tensorRight V` with `tensorLeft V`
  (`BraidedCategory.tensorLeftIsoTensorRight`), and additivity is invariant under isomorphism of
  functors (`Functor.additive_of_iso`).
* Finally an additive functor commutes with subtraction (`Functor.map_sub`).

This is the exact analogue for a general ring `R` of the already proved statement for `ℤ`
(`Work.ANALYTIC.Work.ANALYTIC.whiskerRight_sub` in
`Submission/Work/ANALYTIC/solidNull_of_unit_action.lean`). -/

theorem whiskerRight_sub_lightCondMod (R : Type*) [CommRing R] (V : LightCondMod R)
    {X Y : LightCondMod R} (f g : X ⟶ Y) :
    (f - g) ▷ V = f ▷ V - g ▷ V := by
  -- `tensorLeft V` is a left adjoint, hence additive
  have hleft : (tensorLeft V).Additive := by
    have h : PreservesColimitsOfSize.{0, 0} (tensorLeft V) :=
      (ihom.adjunction V).leftAdjoint_preservesColimits
    have h2 : PreservesColimitsOfShape (Discrete WalkingPair) (tensorLeft V) :=
      h.preservesColimitsOfShape
    have h3 : PreservesBinaryBiproducts (tensorLeft V) :=
      preservesBinaryBiproducts_of_preservesBinaryCoproducts _
    exact Functor.additive_of_preservesBinaryBiproducts _
  -- the braiding identifies `tensorRight V` with `tensorLeft V`, so it is additive too
  have hright : (tensorRight V).Additive :=
    haveI := hleft
    Functor.additive_of_iso (BraidedCategory.tensorLeftIsoTensorRight V)
  -- additivity gives compatibility with subtraction
  exact @Functor.map_sub _ _ _ _ _ _ (tensorRight V) hright _ _ f g

end Work.ANALYTIC
