import Mathlib
import Submission.Work.SSGRoute.ext_one_iso_divisible_cohomology
import Submission.Work.SSGRoute.ExtOnePre
import Submission.Work.SSGRoute.homRep
import Submission.Work.SSGRoute.ExtOneSES
import Submission.Work.SSGRoute.ExtH1Iso
import Submission.Work.SSGRoute.gammaHom_natural_coeff
import Submission.Work.SSGRoute.ExtChain.FreeCover
import Submission.Work.SSGRoute.freeLift_id_epi
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Naturality of the two cokernel descriptions of `Ext¹`

`Work.SSGRoute.ext_one_iso_divisible_cohomology` computes `Ext¹_G(M,N)` (`N` divisible) as a
composite of two cokernel descriptions obtained from the long exact sequences of `Ext`:

* contravariantly, for a short exact complex `S : 0 → S.X₁ → S.X₂ → M → 0` with `S.X₂` projective,
  `Ext¹(M,Y) ≅ Ext⁰(S.X₁,Y) / im(Ext⁰(S.X₂,Y) → Ext⁰(S.X₁,Y))`;
* covariantly, for a short exact complex `Σ : 0 → Hom(M,N) → Hom(F,N) → Hom(R,N) → 0` with
  `Ext¹(X, Σ.X₂) = 0`,
  `Ext¹(X, Hom(M,N)) ≅ Ext⁰(X, Σ.X₃) / im(Ext⁰(X, Σ.X₂) → Ext⁰(X, Σ.X₃))`.

Both descriptions are *canonical* (no `Classical.choice`), and this file proves that both are
**natural** in a morphism of short exact complexes, which is what the naturality clause of
`Work.SSGRoute.ArchDictionary.extOneDictNaturalH1` needs.  Unlike
`ext_coker_LES`/`ext_coker_LES_covariant` (which only produce a `Nonempty`), the maps here are
`def`s with computation rules `cokerIso_symm_mk` / `cokerIso_apply_connMap`.

The second half of the file provides the *functorial* canonical free presentation of a
representation `M` (the `[Fintype G]`-free version of the comparison square of
`Submission/Work/SSGRoute/ExtChain/FreeCover.lean`) together with the induced morphisms of short
complexes.
-/

open CategoryTheory CategoryTheory.Limits
open SSGRoute.PTExt

universe u v w

namespace Work.SSGRoute
namespace CokerNat

section Generic

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C]

variable {S S₁ S₂ : ShortComplex C}

/-! ## The contravariant cokernel description -/

/-- The precomposition `Ext S.X₂ Y 0 →+ Ext S.X₁ Y 0` whose cokernel is `Ext¹ S.X₃ Y`. -/
noncomputable def preMap (S : ShortComplex C) (Y : C) :
    Abelian.Ext S.X₂ Y 0 →+ Abelian.Ext S.X₁ Y 0 :=
  (Abelian.Ext.mk₀ S.f).precomp Y (zero_add 0)

lemma preMap_apply (S : ShortComplex C) (Y : C) (a : Abelian.Ext S.X₂ Y 0) :
    preMap S Y a = (Abelian.Ext.mk₀ S.f).comp a (zero_add 0) :=
  ext_precomp_apply (Abelian.Ext.mk₀ S.f) Y (zero_add 0) a

/-- The connecting map `Ext S.X₁ Y 0 →+ Ext S.X₃ Y 1`. -/
noncomputable def connMap (hS : S.ShortExact) (Y : C) :
    Abelian.Ext S.X₁ Y 0 →+ Abelian.Ext S.X₃ Y 1 :=
  hS.extClass.precomp Y (add_zero 1)

lemma connMap_apply (hS : S.ShortExact) (Y : C) (a : Abelian.Ext S.X₁ Y 0) :
    connMap hS Y a = hS.extClass.comp a (add_zero 1) :=
  ext_precomp_apply hS.extClass Y (add_zero 1) a

lemma connMap_ker_eq_range_preMap (hS : S.ShortExact) (Y : C) :
    (connMap hS Y).ker = (preMap S Y).range := by
  apply le_antisymm
  · intro x hx
    rw [AddMonoidHom.mem_ker, connMap_apply] at hx
    obtain ⟨w, hw⟩ := Abelian.Ext.contravariant_sequence_exact₁ hS Y x (n₁ := 1) (add_zero 1) hx
    exact ⟨w, by rw [preMap_apply]; exact hw⟩
  · rintro x ⟨w, rfl⟩
    rw [AddMonoidHom.mem_ker, connMap_apply, preMap_apply]
    exact hS.extClass_comp_assoc (Y := Y) w

lemma connMap_range_eq_top (hS : S.ShortExact) [Projective S.X₂] (Y : C) :
    (connMap hS Y).range = ⊤ := by
  have hsub : Subsingleton (Abelian.Ext S.X₂ Y 1) :=
    Abelian.Ext.subsingleton_of_projective S.X₂ Y 0
  rw [AddMonoidHom.range_eq_top]
  intro z
  obtain ⟨a, ha⟩ := Abelian.Ext.contravariant_sequence_exact₃ hS Y z (hsub.elim _ _)
    (n₀ := 0) (add_zero 1)
  exact ⟨a, by rw [connMap_apply]; exact ha⟩

/-- The map `Ext S.X₁ Y 0 ⧸ im →+ Ext S.X₃ Y 1` descending the connecting map. -/
noncomputable def cokerIsoHom (hS : S.ShortExact) (Y : C) :
    (Abelian.Ext S.X₁ Y 0 ⧸ (preMap S Y).range) →+ Abelian.Ext S.X₃ Y 1 :=
  QuotientAddGroup.lift (preMap S Y).range (connMap hS Y)
    (by rw [connMap_ker_eq_range_preMap hS Y])

lemma cokerIsoHom_mk (hS : S.ShortExact) (Y : C) (a : Abelian.Ext S.X₁ Y 0) :
    cokerIsoHom hS Y (QuotientAddGroup.mk' (preMap S Y).range a) = connMap hS Y a :=
  QuotientAddGroup.lift_mk' _ _ a

lemma cokerIsoHom_bijective (hS : S.ShortExact) [Projective S.X₂] (Y : C) :
    Function.Bijective (cokerIsoHom hS Y) := by
  constructor
  · rw [← AddMonoidHom.ker_eq_bot_iff, AddSubgroup.eq_bot_iff_forall]
    intro x hx
    obtain ⟨a, rfl⟩ := QuotientAddGroup.mk'_surjective (preMap S Y).range x
    rw [AddMonoidHom.mem_ker, cokerIsoHom_mk] at hx
    have hmem : a ∈ (preMap S Y).range := by
      rw [← connMap_ker_eq_range_preMap hS Y, AddMonoidHom.mem_ker]; exact hx
    exact (QuotientAddGroup.eq_zero_iff a).mpr hmem
  · intro y
    have hy : y ∈ (connMap hS Y).range := by
      rw [connMap_range_eq_top hS Y]; exact AddSubgroup.mem_top y
    obtain ⟨a, ha⟩ := hy
    exact ⟨QuotientAddGroup.mk' _ a, by rw [cokerIsoHom_mk]; exact ha⟩

/-- **The contravariant cokernel description of `Ext¹ S.X₃ Y`.** -/
noncomputable def cokerIso (hS : S.ShortExact) [Projective S.X₂] (Y : C) :
    Abelian.Ext S.X₃ Y 1 ≃+ (Abelian.Ext S.X₁ Y 0 ⧸ (preMap S Y).range) :=
  (AddEquiv.ofBijective (cokerIsoHom hS Y) (cokerIsoHom_bijective hS Y)).symm

lemma cokerIso_symm_mk (hS : S.ShortExact) [Projective S.X₂] (Y : C)
    (a : Abelian.Ext S.X₁ Y 0) :
    (cokerIso hS Y).symm (QuotientAddGroup.mk' (preMap S Y).range a) = connMap hS Y a :=
  cokerIsoHom_mk hS Y a

lemma cokerIso_apply_connMap (hS : S.ShortExact) [Projective S.X₂] (Y : C)
    (a : Abelian.Ext S.X₁ Y 0) :
    cokerIso hS Y (connMap hS Y a) = QuotientAddGroup.mk' (preMap S Y).range a := by
  rw [← cokerIso_symm_mk hS Y a]
  exact AddEquiv.apply_symm_apply _ _

/-! ## Naturality in a morphism of short exact complexes (contravariant) -/

/-- Naturality of `extClass` in the `precomp` formulation. -/
lemma extClass_precomp_natural (h₁ : S₁.ShortExact) (h₂ : S₂.ShortExact) (f : S₁ ⟶ S₂) (Y : C) :
    (h₁.extClass.precomp Y (add_zero 1)).comp ((Abelian.Ext.mk₀ f.τ₁).precomp Y (zero_add 0))
      = ((Abelian.Ext.mk₀ f.τ₃).precomp Y (zero_add 1)).comp
          (h₂.extClass.precomp Y (add_zero 1)) := by
  apply AddMonoidHom.ext
  intro a
  simp only [AddMonoidHom.comp_apply, ext_precomp_apply]
  rw [← Abelian.Ext.comp_assoc_of_third_deg_zero h₁.extClass (Abelian.Ext.mk₀ f.τ₁) a
    (add_zero 1)]
  rw [ShortComplex.ShortExact.extClass_naturality h₁ h₂ f]
  rw [Abelian.Ext.comp_assoc_of_third_deg_zero (Abelian.Ext.mk₀ f.τ₃) h₂.extClass a
    (zero_add 1)]

/-- The comparison of the connecting maps induced by a morphism of short exact complexes. -/
lemma connMap_precomp_natural (h₁ : S₁.ShortExact) (h₂ : S₂.ShortExact) (f : S₁ ⟶ S₂) (Y : C)
    (a : Abelian.Ext S₂.X₁ Y 0) :
    (Abelian.Ext.mk₀ f.τ₃).precomp Y (zero_add 1) (connMap h₂ Y a)
      = connMap h₁ Y ((Abelian.Ext.mk₀ f.τ₁).precomp Y (zero_add 0) a) := by
  simp only [connMap_apply, ext_precomp_apply]
  rw [← Abelian.Ext.comp_assoc_of_third_deg_zero h₁.extClass (Abelian.Ext.mk₀ f.τ₁) a
    (add_zero 1), ShortComplex.ShortExact.extClass_naturality h₁ h₂ f]
  rw [← Abelian.Ext.comp_assoc_of_third_deg_zero (Abelian.Ext.mk₀ f.τ₃) h₂.extClass a
    (zero_add 1)]

lemma preMap_range_le (f : S₁ ⟶ S₂) (Y : C) :
    (preMap S₂ Y).range ≤ AddSubgroup.comap ((Abelian.Ext.mk₀ f.τ₁).precomp Y (zero_add 0))
      (preMap S₁ Y).range := by
  intro b hb
  rw [AddSubgroup.mem_comap]
  obtain ⟨c, hc⟩ := hb
  rw [← hc]
  refine ⟨(Abelian.Ext.mk₀ f.τ₂).precomp Y (zero_add 0) c, ?_⟩
  simp only [preMap_apply, ext_precomp_apply]
  rw [← Abelian.Ext.comp_assoc_of_third_deg_zero (Abelian.Ext.mk₀ S₁.f)
    (Abelian.Ext.mk₀ f.τ₂) c (zero_add 0)]
  rw [Abelian.Ext.mk₀_comp_mk₀, ← f.comm₁₂, ← Abelian.Ext.mk₀_comp_mk₀]
  rw [Abelian.Ext.comp_assoc_of_third_deg_zero (Abelian.Ext.mk₀ f.τ₁)
    (Abelian.Ext.mk₀ S₂.f) c (zero_add 0)]

/-- **Naturality of the contravariant cokernel description of `Ext¹`.** -/
lemma cokerIso_natural (h₁ : S₁.ShortExact) (h₂ : S₂.ShortExact) [Projective S₁.X₂]
    [Projective S₂.X₂] (f : S₁ ⟶ S₂) (Y : C) (x : Abelian.Ext S₂.X₃ Y 1) :
    cokerIso h₁ Y ((Abelian.Ext.mk₀ f.τ₃).precomp Y (zero_add 1) x)
      = QuotientAddGroup.map (preMap S₂ Y).range (preMap S₁ Y).range
          ((Abelian.Ext.mk₀ f.τ₁).precomp Y (zero_add 0)) (preMap_range_le f Y)
          (cokerIso h₂ Y x) := by
  have hx : x ∈ (connMap h₂ Y).range := by
    rw [connMap_range_eq_top h₂ Y]; exact AddSubgroup.mem_top x
  obtain ⟨a, ha⟩ := hx
  rw [← ha, connMap_precomp_natural h₁ h₂ f Y a]
  rw [cokerIso_apply_connMap, cokerIso_apply_connMap, QuotientAddGroup.map_mk']
  rw [QuotientAddGroup.mk'_apply] <;> rfl

/-! ## The covariant cokernel description -/

/-- The postcomposition `Ext X S.X₂ 0 →+ Ext X S.X₃ 0`. -/
noncomputable def postMap (S : ShortComplex C) (X : C) :
    Abelian.Ext X S.X₂ 0 →+ Abelian.Ext X S.X₃ 0 :=
  (Abelian.Ext.mk₀ S.g).postcomp X (zero_add 0)

lemma postMap_apply (S : ShortComplex C) (X : C) (a : Abelian.Ext X S.X₂ 0) :
    postMap S X a = a.comp (Abelian.Ext.mk₀ S.g) (zero_add 0) :=
  ext_postcomp_apply (Abelian.Ext.mk₀ S.g) X (zero_add 0) a

/-- The connecting map `Ext X S.X₃ 0 →+ Ext X S.X₁ 1`. -/
noncomputable def connMapCov (hS : S.ShortExact) (X : C) :
    Abelian.Ext X S.X₃ 0 →+ Abelian.Ext X S.X₁ 1 :=
  hS.extClass.postcomp X (add_zero 1)

lemma connMapCov_apply (hS : S.ShortExact) (X : C) (a : Abelian.Ext X S.X₃ 0) :
    connMapCov hS X a = a.comp hS.extClass (add_zero 1) :=
  ext_postcomp_apply hS.extClass X (add_zero 1) a

lemma connMapCov_ker_eq_range_postMap (hS : S.ShortExact) (X : C) :
    (connMapCov hS X).ker = (postMap S X).range := by
  apply le_antisymm
  · intro x hx
    rw [AddMonoidHom.mem_ker, connMapCov_apply] at hx
    obtain ⟨w, hw⟩ := Abelian.Ext.covariant_sequence_exact₃ X hS x (n₁ := 1) (zero_add 1) hx
    exact ⟨w, by rw [postMap_apply]; exact hw⟩
  · rintro x ⟨w, rfl⟩
    rw [AddMonoidHom.mem_ker]
    have h3 : 0 + 0 + 1 = 1 := by omega
    show (w.comp (Abelian.Ext.mk₀ S.g) (zero_add 0)).comp hS.extClass h3 = 0
    rw [Abelian.Ext.comp_assoc (α := w) (β := Abelian.Ext.mk₀ S.g) (γ := hS.extClass)]
    · rw [hS.comp_extClass, Abelian.Ext.comp_zero]
    · rfl
    · rfl

lemma connMapCov_range_eq_top (hS : S.ShortExact) (X : C)
    [hsub : Subsingleton (Abelian.Ext X S.X₂ 1)] :
    (connMapCov hS X).range = ⊤ := by
  rw [AddMonoidHom.range_eq_top]
  intro y
  have hzero : y.comp (Abelian.Ext.mk₀ S.f) (add_zero 1) = 0 := hsub.elim _ _
  obtain ⟨x, hx⟩ := Abelian.Ext.covariant_sequence_exact₁ X hS y hzero (n₀ := 0) (zero_add 1)
  exact ⟨x, by rw [connMapCov_apply]; exact hx⟩

/-- The map `Ext X S.X₃ 0 ⧸ im →+ Ext X S.X₁ 1` descending the connecting map. -/
noncomputable def cokerIsoCovHom (hS : S.ShortExact) (X : C) :
    (Abelian.Ext X S.X₃ 0 ⧸ (postMap S X).range) →+ Abelian.Ext X S.X₁ 1 :=
  QuotientAddGroup.lift (postMap S X).range (connMapCov hS X)
    (by rw [connMapCov_ker_eq_range_postMap hS X])

lemma cokerIsoCovHom_mk (hS : S.ShortExact) (X : C) (a : Abelian.Ext X S.X₃ 0) :
    cokerIsoCovHom hS X (QuotientAddGroup.mk' (postMap S X).range a) = connMapCov hS X a :=
  QuotientAddGroup.lift_mk' _ _ a

lemma cokerIsoCovHom_bijective (hS : S.ShortExact) (X : C)
    [Subsingleton (Abelian.Ext X S.X₂ 1)] : Function.Bijective (cokerIsoCovHom hS X) := by
  constructor
  · rw [← AddMonoidHom.ker_eq_bot_iff, AddSubgroup.eq_bot_iff_forall]
    intro x hx
    obtain ⟨a, rfl⟩ := QuotientAddGroup.mk'_surjective (postMap S X).range x
    rw [AddMonoidHom.mem_ker, cokerIsoCovHom_mk] at hx
    have hmem : a ∈ (postMap S X).range := by
      rw [← connMapCov_ker_eq_range_postMap hS X, AddMonoidHom.mem_ker]; exact hx
    exact (QuotientAddGroup.eq_zero_iff a).mpr hmem
  · intro y
    have hy : y ∈ (connMapCov hS X).range := by
      rw [connMapCov_range_eq_top hS X]; exact AddSubgroup.mem_top y
    obtain ⟨a, ha⟩ := hy
    exact ⟨QuotientAddGroup.mk' _ a, by rw [cokerIsoCovHom_mk]; exact ha⟩

/-- **The covariant cokernel description of `Ext¹ X S.X₁`.** -/
noncomputable def cokerIsoCov (hS : S.ShortExact) (X : C) [Subsingleton (Abelian.Ext X S.X₂ 1)] :
    Abelian.Ext X S.X₁ 1 ≃+ (Abelian.Ext X S.X₃ 0 ⧸ (postMap S X).range) :=
  (AddEquiv.ofBijective (cokerIsoCovHom hS X) (cokerIsoCovHom_bijective hS X)).symm

lemma cokerIsoCov_symm_mk (hS : S.ShortExact) (X : C) [Subsingleton (Abelian.Ext X S.X₂ 1)]
    (a : Abelian.Ext X S.X₃ 0) :
    (cokerIsoCov hS X).symm (QuotientAddGroup.mk' (postMap S X).range a) = connMapCov hS X a :=
  cokerIsoCovHom_mk hS X a

lemma cokerIsoCov_apply_connMap (hS : S.ShortExact) (X : C)
    [Subsingleton (Abelian.Ext X S.X₂ 1)] (a : Abelian.Ext X S.X₃ 0) :
    cokerIsoCov hS X (connMapCov hS X a) = QuotientAddGroup.mk' (postMap S X).range a := by
  rw [← cokerIsoCov_symm_mk hS X a]
  exact AddEquiv.apply_symm_apply _ _

/-! ## Naturality in a morphism of short exact complexes (covariant) -/

/-- Naturality of `extClass` in the `postcomp` formulation. -/
lemma extClass_postcomp_natural (h₁ : S₁.ShortExact) (h₂ : S₂.ShortExact) (f : S₁ ⟶ S₂) (X : C) :
    (h₂.extClass.postcomp X (add_zero 1)).comp ((Abelian.Ext.mk₀ f.τ₃).postcomp X (zero_add 0))
      = ((Abelian.Ext.mk₀ f.τ₁).postcomp X (add_zero 1)).comp
          (h₁.extClass.postcomp X (add_zero 1)) := by
  apply AddMonoidHom.ext
  intro a
  simp only [AddMonoidHom.comp_apply, ext_postcomp_apply]
  rw [Abelian.Ext.comp_assoc_of_second_deg_zero a (Abelian.Ext.mk₀ f.τ₃) h₂.extClass
    (add_zero 1)]
  rw [← ShortComplex.ShortExact.extClass_naturality h₁ h₂ f]
  rw [← Abelian.Ext.comp_assoc_of_third_deg_zero a h₁.extClass (Abelian.Ext.mk₀ f.τ₁)
    (add_zero 1)]

/-- The comparison of the covariant connecting maps induced by a morphism of short exact
complexes. -/
lemma connMapCov_postcomp_natural (h₁ : S₁.ShortExact) (h₂ : S₂.ShortExact) (f : S₁ ⟶ S₂) (X : C)
    (a : Abelian.Ext X S₁.X₃ 0) :
    (Abelian.Ext.mk₀ f.τ₁).postcomp X (add_zero 1) (connMapCov h₁ X a)
      = connMapCov h₂ X ((Abelian.Ext.mk₀ f.τ₃).postcomp X (zero_add 0) a) := by
  simp only [connMapCov_apply, ext_postcomp_apply]
  rw [Abelian.Ext.comp_assoc_of_second_deg_zero a (Abelian.Ext.mk₀ f.τ₃) h₂.extClass
    (add_zero 1)]
  rw [← ShortComplex.ShortExact.extClass_naturality h₁ h₂ f]
  rw [← Abelian.Ext.comp_assoc_of_third_deg_zero a h₁.extClass (Abelian.Ext.mk₀ f.τ₁)
    (add_zero 1)]

lemma postMap_range_le (f : S₁ ⟶ S₂) (X : C) :
    (postMap S₁ X).range ≤ AddSubgroup.comap ((Abelian.Ext.mk₀ f.τ₃).postcomp X (zero_add 0))
      (postMap S₂ X).range := by
  intro b hb
  rw [AddSubgroup.mem_comap]
  obtain ⟨c, hc⟩ := hb
  rw [← hc]
  refine ⟨(Abelian.Ext.mk₀ f.τ₂).postcomp X (zero_add 0) c, ?_⟩
  simp only [postMap_apply, ext_postcomp_apply]
  rw [Abelian.Ext.comp_assoc_of_second_deg_zero c (Abelian.Ext.mk₀ f.τ₂)
    (Abelian.Ext.mk₀ S₂.g) (zero_add 0)]
  rw [Abelian.Ext.mk₀_comp_mk₀, f.comm₂₃, ← Abelian.Ext.mk₀_comp_mk₀]
  rw [← Abelian.Ext.comp_assoc_of_second_deg_zero c (Abelian.Ext.mk₀ S₁.g)
    (Abelian.Ext.mk₀ f.τ₃) (zero_add 0)]

/-- **Naturality of the covariant cokernel description of `Ext¹`.** -/
lemma cokerIsoCov_natural (h₁ : S₁.ShortExact) (h₂ : S₂.ShortExact) (f : S₁ ⟶ S₂) (X : C)
    [Subsingleton (Abelian.Ext X S₁.X₂ 1)] [Subsingleton (Abelian.Ext X S₂.X₂ 1)]
    (x : Abelian.Ext X S₁.X₁ 1) :
    cokerIsoCov h₂ X ((Abelian.Ext.mk₀ f.τ₁).postcomp X (add_zero 1) x)
      = QuotientAddGroup.map (postMap S₁ X).range (postMap S₂ X).range
          ((Abelian.Ext.mk₀ f.τ₃).postcomp X (zero_add 0)) (postMap_range_le f X)
          (cokerIsoCov h₁ X x) := by
  have hy : x ∈ (connMapCov h₁ X).range := by
    rw [connMapCov_range_eq_top h₁ X]; exact AddSubgroup.mem_top x
  obtain ⟨a, ha⟩ := hy
  rw [← ha, connMapCov_postcomp_natural h₁ h₂ f X a]
  rw [cokerIsoCov_apply_connMap, cokerIsoCov_apply_connMap, QuotientAddGroup.map_mk']
  rw [QuotientAddGroup.mk'_apply] <;> rfl

end Generic

end CokerNat

/-! ## The functorial canonical free presentation -/

section FreeCoverSq

variable {G : Type} [Group G]

attribute [local instance 10000] Rep.hV2 Rep.hV1 Submodule.module

/-- Evaluation of the canonical free cover at a free generator (`freeCover` is `freeLift` with
`id`, `freeLift_id_apply` with `fun m => m`). -/
theorem freeCover_apply_single_gen (X : Rep.{0} Coeff G) (x : X.V) :
    ConcreteCategory.hom (freeCover X) (Finsupp.single x (MonoidAlgebra.single 1 1)) = x :=
  freeLift_id_apply G X x

/-- Evaluation of `freeMap` at a free generator. -/
theorem freeMap_apply_single_gen {X Y : Rep.{0} Coeff G} (h : X ⟶ Y) (x : X.V) :
    ConcreteCategory.hom (freeMap h) (Finsupp.single x (MonoidAlgebra.single 1 1))
      = Finsupp.single (Rep.Hom.hom h x) (MonoidAlgebra.single 1 1) := by
  change ((Rep.free Coeff G Y.V).ρ.freeLift
      (fun x => Finsupp.single (Rep.Hom.hom h x) (MonoidAlgebra.single 1 1)))
      (Finsupp.single x (MonoidAlgebra.single 1 1))
    = Finsupp.single (Rep.Hom.hom h x) (MonoidAlgebra.single 1 1)
  rw [Representation.freeLift_single_single]
  simpa only [map_one, Module.End.one_apply] using
    @one_smul Coeff (Rep.free Coeff G Y.V).V _ ((Rep.free Coeff G Y.V).hV2.toMulAction)
      (Finsupp.single (Rep.Hom.hom h x) (MonoidAlgebra.single 1 1))

/-- **The comparison square of the canonical free covers**, with no finiteness hypothesis on `G`. -/
theorem freeMap_freeCover_gen {X Y : Rep.{0} Coeff G} (h : X ⟶ Y) :
    freeMap h ≫ freeCover Y = freeCover X ≫ h := by
  refine Rep.free_ext (k := Coeff) (G := G) (α := X.V) (A := Y) _ _ ?_
  intro x
  show ConcreteCategory.hom (freeMap h ≫ freeCover Y)
      (Finsupp.single x (MonoidAlgebra.single 1 1))
    = ConcreteCategory.hom (freeCover X ≫ h) (Finsupp.single x (MonoidAlgebra.single 1 1))
  rw [Rep.comp_apply, Rep.comp_apply, freeMap_apply_single_gen, freeCover_apply_single_gen,
    freeCover_apply_single_gen]

/-- The canonical presentation `0 → R → F → M → 0` of a representation `M`, built from the
*canonical* (choice-free) free cover `freeCover M`. -/
@[reducible] noncomputable def ses (M : Rep.{0} Coeff G) : ShortComplex (Rep.{0} Coeff G) :=
  ShortComplex.mk (Limits.kernel.ι (freeCover M)) (freeCover M) (Limits.kernel.condition _)

/-- The canonical presentation is short exact. -/
theorem ses_shortExact (M : Rep.{0} Coeff G) : (ses M).ShortExact :=
  ShortComplex.ShortExact.mk' (ShortComplex.exact_kernel (freeCover M)) inferInstance
    (show Epi (freeCover M) from freeLift_id_epi G M)

/-- The canonical syzygy map `R_X → R_Y` induced by `h : X ⟶ Y`, with no finiteness
hypothesis on `G` (the version in `ExtChain/FreeCover.lean` carries an unused `[Fintype G]`). -/
noncomputable def freeMapKernelGen {X Y : Rep.{0} Coeff G} (h : X ⟶ Y) :
    Limits.kernel (freeCover X) ⟶ Limits.kernel (freeCover Y) :=
  Limits.kernel.lift (freeCover Y) (Limits.kernel.ι (freeCover X) ≫ freeMap h) (by
    rw [Category.assoc, freeMap_freeCover_gen, ← Category.assoc, Limits.kernel.condition,
      Limits.zero_comp])

/-- The defining square of `freeMapKernelGen`. -/
theorem freeMapKernelGen_ι {X Y : Rep.{0} Coeff G} (h : X ⟶ Y) :
    freeMapKernelGen h ≫ Limits.kernel.ι (freeCover Y) =
      Limits.kernel.ι (freeCover X) ≫ freeMap h :=
  Limits.kernel.lift_ι _ _ _

/-- The morphism of canonical presentations induced by `u : M' ⟶ M`. -/
noncomputable def sesMap {M' M : Rep.{0} Coeff G} (u : M' ⟶ M) : ses M' ⟶ ses M :=
  ShortComplex.Hom.mk (freeMapKernelGen u) (freeMap u) u (freeMapKernelGen_ι u)
    (freeMap_freeCover_gen u)

@[simp] lemma sesMap_τ₁ {M' M : Rep.{0} Coeff G} (u : M' ⟶ M) :
    (sesMap u).τ₁ = freeMapKernelGen u := rfl

@[simp] lemma sesMap_τ₂ {M' M : Rep.{0} Coeff G} (u : M' ⟶ M) : (sesMap u).τ₂ = freeMap u := rfl

@[simp] lemma sesMap_τ₃ {M' M : Rep.{0} Coeff G} (u : M' ⟶ M) : (sesMap u).τ₃ = u := rfl

end FreeCoverSq

end Work.SSGRoute
