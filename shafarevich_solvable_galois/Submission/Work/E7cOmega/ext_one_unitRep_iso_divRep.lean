import Mathlib
import Submission.Work.SSGRoute.E7cOmega.ratDivDefs
import Submission.Work.SSGRoute.E7cOmega.ratDivSES
import Submission.Work.SSGRoute.ExtOneAux
import Submission.Work.SSGRoute.homRep
import Submission.Work.SSGRoute.ext_one_iso_divisible_cohomology
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Ext¹_G(M, ℤ) ≅ Hom_G(M, ℚ/ℤ)` for `M` of exponent `p`

For a group `G`, a prime `p` and a `G`-module `M` killed by `p`, the connecting map of the
coefficient short exact sequence `0 → ℤ → ℚ → ℚ/ℤ → 0` of trivial representations
(`Work.SSGRoute.E7cOmega.ratDivSES`) is an isomorphism

`Hom_G(M, ℚ/ℤ) ≅ Ext¹_G(M, ℤ)`,

because both `Hom_G(M, ℚ)` and `Ext¹_G(M, ℚ)` vanish: `ℚ` is torsion-free, and `Ext¹`-classes out of
a torsion module into a divisible module vanish (the divisible `ℚ` makes `Hom_ℤ(M, ℚ)` exact, so
`Ext¹_G(M,ℚ) ≅ H¹(G, Hom_ℤ(M,ℚ)) = 0`, by
`Work.SSGRoute.ext_one_iso_divisible_cohomology`).

The statement `ext_one_unitRep_iso_divRep` is the `Nonempty`-form of this isomorphism.
-/

open CategoryTheory

namespace Work.E7cOmega

noncomputable section

variable {G : Type} [Group G] {p : ℕ} [Fact p.Prime]

section HomVanishing

attribute [local instance 10000] Rep.hV2 Rep.hV1

/-- **A morphism `M ⟶ ℚ` (trivial `G`-action) with `M` of exponent `p` is zero.**  Indeed,
`p • f m = f (p • m) = f 0 = 0` and `p ≠ 0` in the torsion-free group `ℚ`. -/
private lemma hom_ratRep_eq_zero (M : Rep.{0} SSGRoute.PTExt.Coeff G)
    (hM : ∀ m : M, p • m = 0) (f : M ⟶ Work.SSGRoute.E7cOmega.ratRep G) : f = 0 := by
  apply Rep.hom_ext
  rw [Rep.zero_hom]
  rw [Representation.IntertwiningMap.ext_iff]
  apply LinearMap.ext
  intro m
  have hz : (Rep.Hom.hom f).toLinearMap ((p : ℤ) • m) = 0 := by
    have h0 : (p : ℤ) • m = 0 := by simpa using hM m
    rw [h0, map_zero]
  have h2 := map_zsmul (Rep.Hom.hom f).toLinearMap (p : ℤ) m
  rw [h2] at hz
  exact (mul_eq_zero.mp (by rw [zsmul_eq_mul] at hz; exact hz)).resolve_left
    (by rw [Int.cast_natCast]; exact_mod_cast (Fact.out : p.Prime).ne_zero)

/-- `Hom_G(M, ℚ) = 0` for `M` of exponent `p`. -/
private lemma subsingleton_hom_ratRep (M : Rep.{0} SSGRoute.PTExt.Coeff G)
    (hM : ∀ m : M, p • m = 0) : Subsingleton (M ⟶ Work.SSGRoute.E7cOmega.ratRep G) :=
  ⟨fun f g => by rw [hom_ratRep_eq_zero M hM f, hom_ratRep_eq_zero M hM g]⟩

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

/-- **Every `Coeff`-linear map `M → ℚ` is zero** when `M` has exponent `p`. -/
private lemma linearMap_ratRep_eq_zero (M : Rep.{0} SSGRoute.PTExt.Coeff G)
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

/-- `Hom_ℤ(M, ℚ) = 0` (as a `Coeff`-module) for `M` of exponent `p`. -/
private lemma subsingleton_linearMap_ratRep (M : Rep.{0} SSGRoute.PTExt.Coeff G)
    (hM : ∀ m : M, p • m = 0) :
    Subsingleton (M.V →ₗ[SSGRoute.PTExt.Coeff] (Work.SSGRoute.E7cOmega.ratRep G).V) :=
  ⟨fun f g => by rw [linearMap_ratRep_eq_zero M hM f, linearMap_ratRep_eq_zero M hM g]⟩

/-- `Ext⁰_G(M, ℚ) = Hom_G(M, ℚ) = 0` for `M` of exponent `p`. -/
private lemma subsingleton_ext_zero_ratRep (M : Rep.{0} SSGRoute.PTExt.Coeff G)
    (hM : ∀ m : M, p • m = 0) :
    Subsingleton (Abelian.Ext M (Work.SSGRoute.E7cOmega.ratRep G) 0) := by
  refine ⟨fun a b => ?_⟩
  apply (Abelian.Ext.addEquiv₀ (X := M) (Y := Work.SSGRoute.E7cOmega.ratRep G)).injective
  exact (subsingleton_hom_ratRep M hM).elim _ _

/-- `ℚ` is divisible. -/
private lemma rat_divisible (n : ℕ) (hn : 0 < n) (y : ℚ) : ∃ x : ℚ, n • x = y := by
  have hn' : (n : ℚ) ≠ 0 := by
    rw [Nat.cast_ne_zero]
    exact Nat.pos_iff_ne_zero.mp hn
  exact ⟨y / n, by rw [nsmul_eq_mul, mul_div_cancel₀ (b := (n : ℚ)) y hn']⟩

/-- If the identity of `Y` is zero then every `Ext`-group with coefficients in `Y` is a
subsingleton. -/
private lemma subsingleton_ext_of_id_eq_zero {C : Type*} [Category C] [Abelian C] [HasExt C]
    {X Y : C} (h : 𝟙 Y = 0) (n : ℕ) : Subsingleton (Abelian.Ext X Y n) := by
  refine ⟨fun y z => ?_⟩
  have hy : y = 0 := by rw [← Abelian.Ext.comp_mk₀_id y, h]; simp
  have hz : z = 0 := by rw [← Abelian.Ext.comp_mk₀_id z, h]; simp
  rw [hy, hz]

/-- **`Ext¹_G(M, ℚ) = 0` for `M` of exponent `p`.**  Since `ℚ` is divisible, the dictionary
`Ext¹_G(M,ℚ) ≅ H¹(G, Hom_ℤ(M,ℚ))` applies, and `Hom_ℤ(M,ℚ) = 0` because `M` is torsion while `ℚ`
is torsion-free. -/
private lemma subsingleton_ext_one_ratRep (M : Rep.{0} SSGRoute.PTExt.Coeff G)
    (hM : ∀ m : M, p • m = 0) :
    Subsingleton (Abelian.Ext M (Work.SSGRoute.E7cOmega.ratRep G) 1) := by
  obtain ⟨e₁⟩ := Work.SSGRoute.ext_one_iso_divisible_cohomology G M
    (Work.SSGRoute.E7cOmega.ratRep G) rat_divisible
  have hY : Subsingleton (Work.SSGRoute.homRep M (Work.SSGRoute.E7cOmega.ratRep G)).V :=
    show Subsingleton (M.V →ₗ[SSGRoute.PTExt.Coeff] (Work.SSGRoute.E7cOmega.ratRep G).V) from
      subsingleton_linearMap_ratRep M hM
  have h2 : Subsingleton
      (Abelian.Ext (SSGRoute.PTExt.unitRep G)
        (Work.SSGRoute.homRep M (Work.SSGRoute.E7cOmega.ratRep G)) 1) :=
    subsingleton_ext_of_id_eq_zero
      ((subsingleton_self_hom_of_subsingleton
        (Work.SSGRoute.homRep M (Work.SSGRoute.E7cOmega.ratRep G)) hY).elim _ _) 1
  exact ⟨fun a b => e₁.injective (h2.elim (e₁ a) (e₁ b))⟩

theorem ext_one_unitRep_iso_divRep (G : Type) [Group G] (p : ℕ) [Fact p.Prime]
    (M : Rep.{0} SSGRoute.PTExt.Coeff G) (hM : ∀ m : M, p • m = 0) :
    Nonempty (CategoryTheory.Abelian.Ext M (SSGRoute.PTExt.unitRep G) 1 ≃+
      (M ⟶ Work.SSGRoute.E7cOmega.divRep G)) := by
  let S := Work.SSGRoute.E7cOmega.ratDivSES (G := G)
  have hS : S.ShortExact := Work.SSGRoute.E7cOmega.ratDivSES_shortExact (G := G)
  haveI hS0 : Subsingleton (Abelian.Ext M S.X₂ 0) := subsingleton_ext_zero_ratRep M hM
  haveI hS1 : Subsingleton (Abelian.Ext M S.X₂ 1) := subsingleton_ext_one_ratRep M hM
  let δ : Abelian.Ext M S.X₃ 0 →+ Abelian.Ext M S.X₁ 1 :=
    hS.extClass.postcomp M (zero_add 1)
  have hδ : ∀ x, δ x = x.comp hS.extClass (zero_add 1) := fun x =>
    Work.SSGRoute.ext_postcomp_apply hS.extClass M (zero_add 1) x
  have hbij : Function.Bijective δ := by
    constructor
    · intro x y hxy
      have h0 : δ (x - y) = 0 := by rw [map_sub, hxy, sub_self]
      rw [hδ] at h0
      obtain ⟨x₂, hx₂⟩ :=
        Abelian.Ext.covariant_sequence_exact₃ M hS (x - y) (zero_add 1) h0
      have hx₂' : x₂ = 0 := Subsingleton.elim x₂ 0
      have hxy0 : x - y = 0 := by
        rw [← hx₂, hx₂']
        simp
      exact sub_eq_zero.mp hxy0
    · intro y
      have hy : y.comp (Abelian.Ext.mk₀ S.f) (add_zero 1) = 0 := Subsingleton.elim _ _
      obtain ⟨x₃, hx₃⟩ :=
        Abelian.Ext.covariant_sequence_exact₁ M hS y hy (n₀ := 0) (zero_add 1)
      exact ⟨x₃, by rw [hδ]; exact hx₃⟩
  exact ⟨(AddEquiv.ofBijective δ hbij).symm.trans
    (Abelian.Ext.addEquiv₀ (X := M) (Y := S.X₃))⟩

end

end Work.E7cOmega
