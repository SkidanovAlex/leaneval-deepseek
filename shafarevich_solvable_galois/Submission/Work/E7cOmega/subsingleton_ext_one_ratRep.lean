import Mathlib.Combinatorics.Quiver.ReflQuiver
import Mathlib.RepresentationTheory.Rep.Basic
import Mathlib.Analysis.Normed.Field.Lemmas
import Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic
import Submission.Work.SSGRoute.SSGStage.extRatRep_vanish
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Ext¹_G(M, ℚ) = 0` for a `G`-module `M` of exponent `p`

For a group `G`, a prime `p` and a `G`-module `M` killed by `p`, the first `Ext`-group of `M` with
coefficients in the trivial module `ℚ` vanishes:

  `Subsingleton (Ext¹_G(M, ratRep G))`.

`ℚ` is divisible, so the dictionary of `Work.SSGRoute.ext_one_iso_divisible_cohomology` applies:
`Ext¹_G(M,ℚ) ≅ Ext¹_G(ℤ, Hom_ℤ(M,ℚ))`.  As `M` has exponent `p` (in particular is torsion) while
`ℚ` is torsion-free, every `ℤ`-linear map `M → ℚ` is zero, so the coefficient module `Hom_ℤ(M,ℚ)`
has a subsingleton underlying type, hence zero identity, hence every `Ext`-group with coefficients
in it is a subsingleton.

This is the statement of the sibling file `Submission/Work/E7cOmega/ext_one_unitRep_iso_divRep.lean`
(and of `Submission/Work/SSGRoute/SSGStage/divRep_detecting_class.lean`), where it appears as a
`private` auxiliary lemma; here it is exposed as the requested public statement.

## Formalisation note

`Work.SSGRoute.SSGStage.extRatRep_vanish` proves its zero-results under the local instance
`Rep.hV2` (priority `10000`), which is the instance those lemmas are *stated* with.  The object
`Work.SSGRoute.homRep M ℚ` stores the *default* `Coeff`-module structure on `M.V →ₗ[Coeff] ℚ`,
which is not definitionally equal to the `Rep.hV2` one.  The "honest" zero-lemma
`linearMap_ratRep_zero_of_exponent` below is therefore proved in the ambient (default) instance,
matching `homRep`; the instance-sensitive `hom`-level lemma that does need `Rep.hV2` is confined to
the section `HomVanishing`.
-/

open CategoryTheory

namespace Work.E7cOmega

noncomputable section

variable {G : Type} [Group G] {p : ℕ} [Fact p.Prime]

section HomVanishing

attribute [local instance 10000] Rep.hV2 Rep.hV1

/-- A representation whose underlying type is a subsingleton has a subsingleton endomorphism
monoid. -/
private lemma subsingleton_self_hom_of_subsingleton (Y : Rep.{0} SSGRoute.PTExt.Coeff G)
    (h : Subsingleton Y.V) : Subsingleton (Y ⟶ Y) := by
  refine ⟨fun f g => ?_⟩
  apply Rep.hom_ext
  rw [Representation.IntertwiningMap.ext_iff]
  apply LinearMap.ext
  intro m
  exact h.elim _ _

end HomVanishing

/-- If the identity of `Y` is zero then every `Ext`-group with coefficients in `Y` is a
subsingleton (composing an `Ext`-class with `mk₀ 𝟙` is the identity). -/
private lemma subsingleton_ext_of_id_eq_zero {C : Type*} [Category C] [Abelian C] [HasExt C]
    {X Y : C} (h : 𝟙 Y = 0) (n : ℕ) : Subsingleton (Abelian.Ext X Y n) := by
  refine ⟨fun y z => ?_⟩
  have hy : y = 0 := by rw [← Abelian.Ext.comp_mk₀_id y, h]; simp
  have hz : z = 0 := by rw [← Abelian.Ext.comp_mk₀_id z, h]; simp
  rw [hy, hz]

/-- **Every `Coeff`-linear map `M → ℚ` is zero** when `M` has exponent `p` (in the ambient
`Coeff`-module structure on `M.V`, matching the one stored in `Work.SSGRoute.homRep`): the map
kills `p • m = 0`, and `p ≠ 0` in the torsion-free group `ℚ`. -/
private lemma linearMap_ratRep_zero_of_exponent (M : Rep.{0} SSGRoute.PTExt.Coeff G)
    (hM : ∀ m : M, p • m = 0)
    (f : M.V →ₗ[SSGRoute.PTExt.Coeff] (Work.SSGRoute.E7cOmega.ratRep G).V) : f = 0 := by
  ext m
  have hz : f ((p : ℤ) • m) = 0 := by
    have h0 : (p : ℤ) • m = 0 := by simpa using hM m
    rw [h0, map_zero]
  have h2 := map_zsmul f (p : ℤ) m
  rw [h2] at hz
  exact (mul_eq_zero.mp (by rw [zsmul_eq_mul] at hz; exact hz)).resolve_left
    (by rw [Int.cast_natCast]; exact_mod_cast (Fact.out : p.Prime).ne_zero)

/-- The requested statement: **`Ext¹_G(M, ℚ) = 0` for `M` of exponent `p`**.  Since `ℚ` is
divisible, the dictionary `Ext¹_G(M,ℚ) ≅ H¹(G, Hom_ℤ(M,ℚ))` applies, and `Hom_ℤ(M,ℚ) = 0` because
`M` is torsion while `ℚ` is torsion-free; a representation with a subsingleton underlying type has
zero identity, so every `Ext`-group with coefficients in it is a subsingleton. -/
theorem subsingleton_ext_one_ratRep (G : Type) [Group G] (p : ℕ) [Fact p.Prime]
    (M : Rep.{0} SSGRoute.PTExt.Coeff G) (hM : ∀ m : M, p • m = 0) :
    Subsingleton (CategoryTheory.Abelian.Ext M (Work.SSGRoute.E7cOmega.ratRep G) 1) := by
  obtain ⟨e₁⟩ := Work.SSGRoute.ext_one_iso_divisible_cohomology G M
    (Work.SSGRoute.E7cOmega.ratRep G) (Work.SSGRoute.SSGStage.rat_divisible)
  have hY : Subsingleton (Work.SSGRoute.homRep M (Work.SSGRoute.E7cOmega.ratRep G)).V :=
    show Subsingleton (M.V →ₗ[SSGRoute.PTExt.Coeff] (Work.SSGRoute.E7cOmega.ratRep G).V) from
      ⟨fun f g => by
        rw [linearMap_ratRep_zero_of_exponent M hM f, linearMap_ratRep_zero_of_exponent M hM g]⟩
  have h2 : Subsingleton
      (Abelian.Ext (SSGRoute.PTExt.unitRep G)
        (Work.SSGRoute.homRep M (Work.SSGRoute.E7cOmega.ratRep G)) 1) :=
    subsingleton_ext_of_id_eq_zero
      ((subsingleton_self_hom_of_subsingleton _ hY).elim _ _) 1
  exact ⟨fun a b => e₁.injective (h2.elim (e₁ a) (e₁ b))⟩

end

end Work.E7cOmega
