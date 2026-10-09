import Mathlib
import Submission.Work.SSGRoute.PTDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# E7cΩ / C6: `ℚ` and `ℚ/ℤ` as trivial `Coeff`-representations (definitions)

Local-duality infrastructure for `Work.SSGRoute.E7cOmega.exists_level_unramified_detecting_class`.
Nothing of this kind exists in the workspace: there is no `ℚ`- or `ℚ/ℤ`-valued representation, and
therefore no `ℚ/ℤ`-coefficient short exact sequence.

Design notes (this is the version that works):

* `ℤ ⊆ ℚ` is taken to be the **range** of the coefficient inclusion `unitToRatLin : ℤ →ₗ ℚ`, as a
  `Coeff`-submodule.  Using `Submodule.span ℤ {1}` instead forces every later step through
  `Submodule.mem_span_singleton`-style rewrites, which do not match through the coercion of
  `ShortComplex` objects; with the range, membership is `LinearMap.mem_range` and the quotient map
  `zSpan.mkQ` is *`Coeff`-linear by construction* (no `QuotientAddGroup.mk'` `smul`-compatibility
  lemma is needed at all).
* `RatDivZ := ℚ ⧸ zSpan` is then the usual `ℚ/ℤ`, and it carries its quotient `Coeff`-module
  structure directly.

The substantive lemma is `Work.SSGRoute.E7cOmega.ratDivSES_shortExact` (in `ratDivSES.lean`), and
the duality `Ext¹_G(M,ℤ) ≅ Hom_G(M,ℚ/ℤ)` is its long-exact-sequence consequence.
-/

open CategoryTheory

namespace Work.SSGRoute.E7cOmega

/-- The `Coeff = ULift ℤ`-module structure on `ℚ`, transported from the `ℤ`-module structure. -/
instance instModuleCoeffRat : Module SSGRoute.PTExt.Coeff ℚ :=
  Module.compHom ℚ (ULift.ringEquiv (R := ℤ)).toRingHom

/-- The coefficient inclusion `ℤ ↪ ℚ` (`ULift ℤ`-linear). -/
noncomputable def unitToRatLin : SSGRoute.PTExt.Coeff →ₗ[SSGRoute.PTExt.Coeff] ℚ where
  toFun c := ((c.down : ℤ) : ℚ)
  map_add' := by intro a b; simp [Int.cast_add]
  map_smul' := by
    intro r a
    show ((r.down * a.down : ℤ) : ℚ) = r • ((a.down : ℤ) : ℚ)
    rw [show r • ((a.down : ℤ) : ℚ) = (r.down : ℤ) • ((a.down : ℤ) : ℚ) from rfl,
      zsmul_eq_mul]
    push_cast
    ring

/-- `ℤ ⊆ ℚ` as a `Coeff`-submodule, namely the range of the coefficient inclusion. -/
noncomputable def zSpan : Submodule SSGRoute.PTExt.Coeff ℚ := LinearMap.range unitToRatLin

/-- `ℚ/ℤ` as a type (`ℚ` modulo `ℤ`). -/
noncomputable abbrev RatDivZ : Type := ℚ ⧸ zSpan

/-- `ℚ` as the trivial `Coeff`-representation of `G`. -/
noncomputable abbrev ratRep (G : Type) [Group G] : Rep.{0} SSGRoute.PTExt.Coeff G :=
  Rep.trivial SSGRoute.PTExt.Coeff G ℚ

/-- `ℚ/ℤ` as the trivial `Coeff`-representation of `G`. -/
noncomputable abbrev divRep (G : Type) [Group G] : Rep.{0} SSGRoute.PTExt.Coeff G :=
  Rep.trivial SSGRoute.PTExt.Coeff G RatDivZ

end Work.SSGRoute.E7cOmega
