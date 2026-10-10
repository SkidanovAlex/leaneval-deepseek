import Mathlib
import Submission.Work.Motivic.Defs
import Submission.Work.Motivic.CompMorph
import Submission.Work.Motivic.exists_partialIso_toRationalMap_eq
import Submission.Work.Motivic.comp_isOver

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

set_option autoImplicit false
set_option linter.style.haveILetI false

namespace Work.Motivic

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme

theorem isIsoAt_of_mutual_inverse {X Y S : AlgebraicGeometry.Scheme.{0}} [IrreducibleSpace X]
    [IrreducibleSpace Y] [X.Over S] [Y.Over S] [AlgebraicGeometry.IsReduced X]
    [AlgebraicGeometry.IsReduced Y] [AlgebraicGeometry.IsSeparated (Y ↘ S)]
    [AlgebraicGeometry.IsSeparated (X ↘ S)]
    (φ : X.BirationalMap Y) [φ.hom.IsOver S] [φ.inv.IsOver S] {x : X}
    (g : X.PartialMap Y) [g.IsOver S] (hg : g.toRationalMap = φ.hom) (hx : x ∈ g.domain)
    (k : Y.PartialMap X) [k.IsOver S] (hk : k.toRationalMap = φ.inv)
    (hy : g.hom ⟨x, hx⟩ ∈ k.domain) : IsIsoAt φ x := by
  haveI hgd : IsDominant g.hom :=
    (PartialMap.isDominant_toRationalMap_iff g).mp (by rw [hg]; infer_instance)
  haveI hkd : IsDominant k.hom :=
    (PartialMap.isDominant_toRationalMap_iff k).mp (by rw [hk]; infer_instance)
  haveI hioU : (g.comp k).IsOver S := comp_isOver g k
  haveI hioV : (k.comp g).IsOver S := comp_isOver k g
  -- The two opens: `U` is the domain of the composite `g ∘ k`, `V` the domain of the preimage
  -- of `U` under `k` inside `k.domain`.  The point `x` lies in `U`.
  let U : X.Opens := g.domain.ι ''ᵁ (g.hom ⁻¹ᵁ k.domain)
  let V : Y.Opens := k.domain.ι ''ᵁ (k.hom ⁻¹ᵁ U)
  have hUle : U ≤ g.domain := Opens.ι_image_le g.domain (g.hom ⁻¹ᵁ k.domain)
  have hVle : V ≤ k.domain := Opens.ι_image_le k.domain (k.hom ⁻¹ᵁ U)
  have hUd : Dense (U : Set X) := by
    have h := (g.comp k).dense_domain
    rwa [PartialMap.comp_domain] at h
  have hVd : Dense (V : Set Y) := aux_dense_image_preimage k (W := U) hUd
  have hUE : U ≤ g.domain.ι ''ᵁ (g.hom ⁻¹ᵁ k.domain) := le_rfl
  have hVc : V ≤ k.domain.ι ''ᵁ (k.hom ⁻¹ᵁ g.domain) :=
    k.domain.ι.image_mono (k.hom.preimage_mono hUle)
  -- `g ∘ k` and `k ∘ g` are equivalent to the identities, since `g` and `k` represent the two
  -- directions of the birational map `φ`.
  have heqU : (g.comp k).equiv (PartialMap.id X) := by
    have hc : g.toRationalMap.comp k.toRationalMap = φ.hom.comp φ.inv := by simp only [hg, hk]
    rw [← PartialMap.toRationalMap_eq_iff, ← RationalMap.toRationalMap_comp (f := g) (g := k), hc,
      BirationalMap.hom_comp_inv_id]
  have heqV : (k.comp g).equiv (PartialMap.id Y) := by
    have hc : k.toRationalMap.comp g.toRationalMap = φ.inv.comp φ.hom := by simp only [hk, hg]
    rw [← PartialMap.toRationalMap_eq_iff, ← RationalMap.toRationalMap_comp (f := k) (g := g), hc,
      BirationalMap.inv_comp_hom_id]
  -- On the dense opens `U`, `V` the composites are the identity *morphisms*.
  have hUtop : U ≤ (PartialMap.id X).domain := le_top
  have hwU : X.homOfLE hUE ≫ (g.comp k).hom = U.ι := by
    have h := (PartialMap.equiv_iff_of_isSeparated_of_le (S := S) (f := g.comp k)
      (g := PartialMap.id X) (W := U) hUd hUE hUtop).mp heqU
    have h2 : ((PartialMap.id X).restrict U hUd hUtop).hom = U.ι := by
      simp only [PartialMap.restrict_hom, PartialMap.id_hom, Scheme.topIso_hom]
      exact Scheme.homOfLE_ι X hUtop
    exact h.trans h2
  have hVtop : V ≤ (PartialMap.id Y).domain := le_top
  have hwV : Y.homOfLE hVc ≫ (k.comp g).hom = V.ι := by
    have h := (PartialMap.equiv_iff_of_isSeparated_of_le (S := S) (f := k.comp g)
      (g := PartialMap.id Y) (W := V) hVd hVc hVtop).mp heqV
    have h2 : ((PartialMap.id Y).restrict V hVd hVtop).hom = V.ι := by
      simp only [PartialMap.restrict_hom, PartialMap.id_hom, Scheme.topIso_hom]
      exact Scheme.homOfLE_ι Y hVtop
    exact h.trans h2
  -- The two "first halves" of the composites, as morphisms.
  let p : U.toScheme ⟶ k.domain.toScheme := compMorphInv g k hUE
  have hp1 : p ≫ k.hom = U.ι := by
    have h1 : p ≫ k.hom = X.homOfLE hUE ≫ (g.comp k).hom := by
      simp only [p, compMorphInv, PartialMap.comp_hom, Category.assoc]
    rw [h1, hwU]
  have hp2 : p ≫ k.domain.ι = X.homOfLE hUle ≫ g.hom :=
    aux_compMorphInv_comp_domain_iota g k hUE hUle
  let q : V.toScheme ⟶ g.domain.toScheme := compMorphInv k g hVc
  have hq1 : q ≫ g.hom = V.ι := by
    have h1 : q ≫ g.hom = Y.homOfLE hVc ≫ (k.comp g).hom := by
      simp only [q, compMorphInv, PartialMap.comp_hom, Category.assoc]
    rw [h1, hwV]
  have hq2 : q ≫ g.domain.ι = Y.homOfLE hVle ≫ k.hom :=
    aux_compMorphInv_comp_domain_iota k g hVc hVle
  -- `x` lies in the domain of the composite, because `g x` lies in the domain of `k`.
  have hxU : x ∈ U := by
    show x ∈ g.domain.ι ''ᵁ (g.hom ⁻¹ᵁ k.domain)
    have h : g.domain.ι (⟨x, hx⟩ : g.domain.toScheme) ∈ g.domain.ι ''ᵁ (g.hom ⁻¹ᵁ k.domain) :=
      (Hom.apply_mem_image_iff g.domain.ι).mpr ((Hom.mem_preimage g.hom).mpr hy)
    simpa using h
  -- Range conditions for the two restrictions of `g` and `k`.
  have hαrange : Set.range ⇑(X.homOfLE hUle ≫ g.hom) ⊆ Set.range ⇑V.ι := by
    rw [Opens.range_ι]
    rintro y ⟨u, rfl⟩
    have hαu : (X.homOfLE hUle ≫ g.hom) u = k.domain.ι (p u) := by
      rw [← hp2, Hom.comp_apply]
    rw [hαu]
    refine (Hom.apply_mem_image_iff k.domain.ι).mpr ?_
    refine (Hom.mem_preimage k.hom).mpr ?_
    have hpu : k.hom (p u) = U.ι u := by rw [← Hom.comp_apply, hp1]
    rw [hpu]
    exact u.2
  have hβrange : Set.range ⇑(Y.homOfLE hVle ≫ k.hom) ⊆ Set.range ⇑U.ι := by
    rw [Opens.range_ι]
    rintro y ⟨v, rfl⟩
    have h1 : k.domain.ι (Y.homOfLE hVle v) ∈ V := by
      rw [← Hom.comp_apply, Scheme.homOfLE_ι Y hVle]
      exact v.2
    exact (Hom.mem_preimage k.hom).mp ((Hom.apply_mem_image_iff k.domain.ι).mp h1)
  -- The partial isomorphism `U ≅ V`.
  let α : U.toScheme ⟶ V.toScheme := IsOpenImmersion.lift V.ι (X.homOfLE hUle ≫ g.hom) hαrange
  have hαfac : α ≫ V.ι = X.homOfLE hUle ≫ g.hom :=
    IsOpenImmersion.lift_fac V.ι (X.homOfLE hUle ≫ g.hom) hαrange
  let β : V.toScheme ⟶ U.toScheme := IsOpenImmersion.lift U.ι (Y.homOfLE hVle ≫ k.hom) hβrange
  have hβfac : β ≫ U.ι = Y.homOfLE hVle ≫ k.hom :=
    IsOpenImmersion.lift_fac U.ι (Y.homOfLE hVle ≫ k.hom) hβrange
  have happ : α ≫ Y.homOfLE hVle = p := by
    rw [← cancel_mono k.domain.ι, Category.assoc, Scheme.homOfLE_ι Y hVle, hαfac, hp2]
  have hβq : β ≫ X.homOfLE hUle = q := by
    rw [← cancel_mono g.domain.ι, Category.assoc, Scheme.homOfLE_ι X hUle, hβfac, ← hq2]
  have hαβ : α ≫ β = 𝟙 U.toScheme := by
    rw [← cancel_mono U.ι, Category.id_comp]
    rw [Category.assoc, hβfac]
    rw [← Category.assoc, happ, hp1]
  have hβα : β ≫ α = 𝟙 V.toScheme := by
    rw [← cancel_mono V.ι, Category.id_comp]
    rw [Category.assoc, hαfac]
    rw [← Category.assoc, hβq, hq1]
  let iso : U.toScheme ≅ V.toScheme := ⟨α, β, hαβ, hβα⟩
  let i : X.PartialIso Y := ⟨U, hUd, V, hVd, iso⟩
  -- The partial isomorphism represents the rational map `g.toRationalMap = φ.hom`.
  have hptm : i.toPartialMap.equiv g := by
    refine ⟨U, hUd, le_rfl, hUle, ?_⟩
    show X.homOfLE (le_rfl : U ≤ U) ≫ i.toPartialMap.hom = X.homOfLE hUle ≫ g.hom
    rw [Scheme.homOfLE_rfl]
    show α ≫ V.ι = X.homOfLE hUle ≫ g.hom
    exact hαfac
  have hφ : i.toRationalMap = φ.hom := (PartialMap.toRationalMap_eq_iff.mpr hptm).trans hg
  exact ⟨i, hxU, hφ⟩

end Work.Motivic
