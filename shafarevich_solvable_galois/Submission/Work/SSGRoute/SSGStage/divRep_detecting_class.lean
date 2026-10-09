import Mathlib
import Submission.Work.SSGRoute.E7cOmega.ratDivSES
import Submission.Work.SSGRoute.E7cOmega.ratDivDefs
import Submission.Work.SSGRoute.PTDefs
import Submission.Work.SSGRoute.ext_one_iso_divisible_cohomology
import Submission.Work.SSGRoute.ExtOneAux
import Submission.Work.SSGRoute.homRep
import Submission.Work.SSGRoute.SSGStage.extRatRep_vanish
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The connecting map `Hom_G(M, ℚ/ℤ) → Ext¹_G(M, ℤ)` is onto for `M` of exponent `p`

For a group `G`, a prime `p` and a `G`-module `M` killed by `p`, the connecting map of the
coefficient short exact sequence `0 → ℤ → ℚ → ℚ/ℤ → 0` of trivial `Coeff`-representations
(`Work.SSGRoute.E7cOmega.ratDivSES`)

  `δ : Hom_G(M, ℚ/ℤ) = Ext⁰_G(M, ℚ/ℤ) → Ext¹_G(M, ℤ)`,  `μ ↦ (mk₀ μ).comp extClass`

is surjective.  The long exact sequence of `Ext` shows that the image of `δ` is the kernel of the
change-of-coefficients map `Ext¹_G(M, ℤ) → Ext¹_G(M, ℚ)`, and this is everything because
`Ext¹_G(M, ℚ) = 0` (`subsingleton_ext_one_ratRep` below): `ℚ` is divisible, so the dictionary
`Ext¹_G(M,ℚ) ≅ H¹(G, Hom_ℤ(M,ℚ))` of `Work.SSGRoute.ext_one_iso_divisible_cohomology` applies,
while `Hom_ℤ(M,ℚ) = 0` because `M` is torsion and `ℚ` is torsion-free.  Concretely the connecting
map `δ` is the map `(hS.extClass).postcomp M (zero_add 1)` of the short exact short complex `S`,
and the exactness statement `Abelian.Ext.covariant_sequence_exact₁` produces the preimage `x₃`
of `φ` in `Ext⁰_G(M, ℚ/ℤ)` as soon as `φ` lands in the kernel of the change-of-coefficients map,
which holds because that target is a subsingleton.

The statement `divRep_detecting_class` is the "every nonzero `φ ∈ Ext¹_G(M, ℤ)` has a nonzero
coefficient map `μ : M ⟶ ℚ/ℤ` with `φ = δ(μ)`" form of this surjectivity, i.e. the local
Tate-duality input of the E7cΩ node `C6` (`Work.SSGRoute.SSGStage.unramifiedDetector`).

## Formalisation note

`Work.SSGRoute.SSGStage.extRatRep_vanish` proves the vanishing of `Hom_G(M, ℚ)` and `Ext⁰_G(M, ℚ)`
*under the local instance* `Rep.hV2` (priority `10000`), which is the instance its lemmas are
stated with.  The object `Work.SSGRoute.homRep M ℚ`, on the other hand, stores the *default*
`Coeff`-module structure on `M.V →ₗ[ℤ] ℚ`, and the two are not definitionally equal.  The
"honest" zero-lemma `linearMap_ratRep_zero_of_exponent` below is therefore proved in the ambient
(default) instance, matching `homRep`; the instance-sensitive `hom`-level lemmas that do need
`Rep.hV2` are confined to the section `HomVanishing`.
-/

open CategoryTheory

namespace Work.SSGRoute.SSGStage

set_option linter.style.haveILetI false

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

/-- **Every `Coeff`-linear map `M → ℚ` is zero** when `M` has exponent `p` (the ambient
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

/-- **`Ext¹_G(M, ℚ) = 0` for `M` of exponent `p`.**  Since `ℚ` is divisible, the dictionary
`Ext¹_G(M,ℚ) ≅ H¹(G, Hom_ℤ(M,ℚ))` applies, and `Hom_ℤ(M,ℚ) = 0` because `M` is torsion while `ℚ`
is torsion-free; a representation with a subsingleton underlying type has zero identity, so every
`Ext`-group with coefficients in it is a subsingleton. -/
private lemma subsingleton_ext_one_ratRep (M : Rep.{0} SSGRoute.PTExt.Coeff G)
    (hM : ∀ m : M, p • m = 0) :
    Subsingleton (Abelian.Ext M (Work.SSGRoute.E7cOmega.ratRep G) 1) := by
  obtain ⟨e₁⟩ := Work.SSGRoute.ext_one_iso_divisible_cohomology G M
    (Work.SSGRoute.E7cOmega.ratRep G) rat_divisible
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

theorem divRep_detecting_class (p : ℕ) [Fact p.Prime] {G : Type} [Group G]
    (M : Rep.{0} SSGRoute.PTExt.Coeff G) (hM : ∀ m : M, p • m = 0)
    (φ : CategoryTheory.Abelian.Ext M (SSGRoute.PTExt.unitRep G) 1) (hφ : φ ≠ 0) :
    ∃ μ : M ⟶ Work.SSGRoute.E7cOmega.divRep G, μ ≠ 0 ∧
      φ = (CategoryTheory.Abelian.Ext.mk₀ μ).comp
        (CategoryTheory.ShortComplex.ShortExact.extClass
          (Work.SSGRoute.E7cOmega.ratDivSES_shortExact (G := G))) (zero_add 1) := by
  let S := Work.SSGRoute.E7cOmega.ratDivSES (G := G)
  let hS : S.ShortExact := Work.SSGRoute.E7cOmega.ratDivSES_shortExact (G := G)
  -- `Ext¹_G(M,ℚ) = 0`, so `φ` lies in the kernel of the change-of-coefficients map
  haveI hS1 : Subsingleton (Abelian.Ext M S.X₂ 1) := subsingleton_ext_one_ratRep M hM
  have hx₁ : φ.comp (Abelian.Ext.mk₀ S.f) (add_zero 1) = 0 := Subsingleton.elim _ _
  -- exactness of the long exact sequence at `Ext¹_G(M,ℤ)` exhibits `φ` as `δ x₃`
  obtain ⟨x₃, hx₃⟩ := Abelian.Ext.covariant_sequence_exact₁ M hS φ hx₁ (n₀ := 0) (zero_add 1)
  -- work with the objects of the short complex `S`, which are definitionally `ℤ`, `ℚ`, `ℚ/ℤ`
  show ∃ μ : M ⟶ S.X₃, μ ≠ 0 ∧
      φ = (Abelian.Ext.mk₀ μ).comp
        (CategoryTheory.ShortComplex.ShortExact.extClass
          (Work.SSGRoute.E7cOmega.ratDivSES_shortExact (G := G))) (zero_add 1)
  refine ⟨Abelian.Ext.addEquiv₀ x₃, ?_, ?_⟩
  · -- the coefficient map is nonzero because `φ ≠ 0`
    intro hμ
    have hx₃0 : x₃ = 0 := by
      rw [← Abelian.Ext.mk₀_addEquiv₀_apply x₃, hμ, Abelian.Ext.mk₀_zero]
    exact hφ (hx₃.symm.trans
      (by rw [hx₃0]; exact Abelian.Ext.zero_comp M 0 hS.extClass 1 (zero_add 1)))
  · -- the class equation `φ = δ μ`
    rw [Abelian.Ext.mk₀_addEquiv₀_apply x₃]
    exact hx₃.symm

end

end Work.SSGRoute.SSGStage
