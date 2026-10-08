/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gorenstein–Walter formalisation team (area DSTR, `Work.DSTR`)

# The image of a normal quasisimple `E` in `Y / C_Y(E)` is `E / Z(E)`

Let `E ◁ X` be quasisimple (perfect with `E/Z(E)` simple) and let `E ≤ Y ≤ X`.  With
`C = C_X(E)` and `N = C.subgroupOf Y`, the image `L` of `E` in `↥Y ⧸ N` is normal, has trivial
centralizer there, and is isomorphic to `E / Z(E)`.

The identification of `L` with `E/Z(E)` is the first isomorphism theorem applied to the natural
map `↥E →* ↥Y ⧸ N` (whose kernel is `Z(E) = E ⊓ C_X(E)` and whose range is `L`).

The triviality of the centralizer is where perfectness of `E` is used: if `g ∈ Y` acts on `E`
trivially modulo `Z(E)` — i.e. `g⁻¹ * s⁻¹ * g * s ∈ Z(E)` for all `s ∈ E` — then the map
`s ↦ g⁻¹ * s⁻¹ * g * s` is a homomorphism of `E` into the abelian group `Z(E)`, hence trivial
because `E = ⁅E, E⁆`; so `g ∈ C_X(E)`, i.e. `g` maps to `1` in the quotient.  (Note that no
finiteness or oddness of `Z(E)` is needed here.)
-/
import Mathlib
import Submission.Work.DSTR.Defs
import Submission.Work.DSTR.conj_eq_self_of_commutator_mem_center

namespace Work.DSTR

open Subgroup

/-- `Z(E)`, viewed in the ambient group along `E.subtype`, is `E ⊓ C_X(E)`; the same statement
in the opposite orientation (and in the same universe) is
`Work.CORE2A.inf_centralizer_eq_center_map`. -/
private theorem map_subtype_center_eq_inf_centralizer {X : Type*} [Group X] (E : Subgroup X) :
    (Subgroup.center ↥E).map E.subtype = E ⊓ Subgroup.centralizer (E : Set X) := by
  ext x
  simp only [Subgroup.mem_inf, Subgroup.mem_centralizer_iff, Subgroup.mem_map,
    Subgroup.mem_center_iff, Subgroup.coe_subtype]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y.2, fun z hz => congrArg Subtype.val (hy ⟨z, hz⟩)⟩
  · rintro ⟨hxE, hx⟩
    exact ⟨⟨x, hxE⟩, fun y => Subtype.ext (hx y y.2), rfl⟩

/-- **Trivial centralizer.**  Let `E ◁ X` be perfect, let `E ≤ Y ≤ X`, put `C = C_X(E)`,
`N = C.subgroupOf Y`, and let `L` be the image of `E` in `↥Y ⧸ N`.  Then `C_{↥Y⧸N}(L) = 1`. -/
private theorem centralizer_map_quotient_eq_bot {X : Type*} [Group X] (E Y : Subgroup X)
    (hEY : E ≤ Y) (hEn : E.Normal) (hperf : ⁅E, E⁆ = E) :
    Subgroup.centralizer
      (((E.subgroupOf Y).map
        (QuotientGroup.mk' ((Subgroup.centralizer (E : Set X)).subgroupOf Y))) :
          Set (↥Y ⧸ ((Subgroup.centralizer (E : Set X)).subgroupOf Y))) = ⊥ := by
  let N : Subgroup ↥Y := (Subgroup.centralizer (E : Set X)).subgroupOf Y
  haveI hNn : N.Normal := inferInstance
  rw [Subgroup.eq_bot_iff_forall]
  intro y hy
  obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective N y
  rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  change g ∈ (Subgroup.centralizer (E : Set X)).subgroupOf Y
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_iff]
  intro s hs
  -- `g` acts on `E` trivially modulo `Z(E)`
  have hZ : ∀ t ∈ E, (g : X)⁻¹ * t⁻¹ * (g : X) * t ∈ (Subgroup.center ↥E).map E.subtype := by
    intro t ht
    rw [map_subtype_center_eq_inf_centralizer E]
    refine ⟨?_, ?_⟩
    · -- `(g)⁻¹ * t⁻¹ * g ∈ E` because `E` is normal
      have h1 : (g : X)⁻¹ * t⁻¹ * (g : X) ∈ E := by
        simpa using hEn.conj_mem t⁻¹ (Subgroup.inv_mem _ ht) (g : X)⁻¹
      exact Subgroup.mul_mem _ h1 ht
    · -- and it lies in `C_X(E)`, because `g` and `t` commute modulo `N`
      have hmem : QuotientGroup.mk' N (⟨t, hEY ht⟩ : ↥Y) ∈
          (E.subgroupOf Y).map (QuotientGroup.mk' N) :=
        Subgroup.mem_map.mpr ⟨⟨t, hEY ht⟩, ht, rfl⟩
      have hcomm := Subgroup.mem_centralizer_iff.mp hy _ hmem
      have hmemN : g⁻¹ * (⟨t, hEY ht⟩ : ↥Y)⁻¹ * g * (⟨t, hEY ht⟩ : ↥Y) ∈ N := by
        have hc := QuotientGroup.eq.mp (show QuotientGroup.mk' N ((⟨t, hEY ht⟩ : ↥Y) * g) =
            QuotientGroup.mk' N (g * (⟨t, hEY ht⟩ : ↥Y)) by
          simpa only [map_mul] using hcomm)
        convert hc using 1
        group
      have hcc := Subgroup.mem_subgroupOf.mp hmemN
      simpa using hcc
  -- perfectness forces `g` to centralize `E`
  have hconj := conj_eq_self_of_commutator_mem_center E hperf (g : X) hZ
  have h2 : (g : X) * s = s * (g : X) := by
    calc (g : X) * s = (g : X) * s * (g : X)⁻¹ * (g : X) := by group
      _ = s * (g : X) := by rw [hconj s hs]
  exact h2.symm

/-- **The image of `E` is `E/Z(E)`.**  With `N = C_X(E).subgroupOf Y`, the natural map
`↥E →* ↥Y ⧸ N` has kernel `Z(E)` and range the image of `E`, so the first isomorphism theorem
identifies that image with `E/Z(E)`. -/
private theorem map_subgroupOf_quotient_equiv_center {X : Type*} [Group X] (E Y : Subgroup X)
    (hEY : E ≤ Y) (hEn : E.Normal) :
    Nonempty (((E.subgroupOf Y).map
        (QuotientGroup.mk' ((Subgroup.centralizer (E : Set X)).subgroupOf Y))) ≃*
      (↥E ⧸ Subgroup.center ↥E)) := by
  let N : Subgroup ↥Y := (Subgroup.centralizer (E : Set X)).subgroupOf Y
  haveI hNn : N.Normal := inferInstance
  let g : ↥E →* ↥Y := MonoidHom.mk' (fun e => ⟨e.1, hEY e.2⟩) (by intro a b; rfl)
  let f : ↥E →* (↥Y ⧸ N) := (QuotientGroup.mk' N).comp g
  have hfker : f.ker = Subgroup.center ↥E := by
    ext e
    rw [MonoidHom.mem_ker]
    change (QuotientGroup.mk' N) ⟨e.1, hEY e.2⟩ = 1 ↔ e ∈ Subgroup.center ↥E
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf,
      Subgroup.mem_centralizer_iff, Subgroup.mem_center_iff]
    constructor
    · intro h x
      exact Subtype.ext (h x.1 x.2)
    · intro h y hy
      exact congrArg Subtype.val (h ⟨y, hy⟩)
  have hfrange : f.range = (E.subgroupOf Y).map (QuotientGroup.mk' N) := by
    refine Subgroup.ext fun q => ?_
    simp only [MonoidHom.mem_range, Subgroup.mem_map, Subgroup.mem_subgroupOf, f, g,
      MonoidHom.comp_apply, MonoidHom.mk'_apply]
    constructor
    · rintro ⟨e, rfl⟩
      exact ⟨⟨e.1, hEY e.2⟩, e.2, rfl⟩
    · rintro ⟨y, hy, rfl⟩
      exact ⟨⟨y.1, hy⟩, rfl⟩
  exact ⟨((QuotientGroup.quotientMulEquivOfEq hfker.symm).trans
    (QuotientGroup.quotientKerEquivRange f)).trans (MulEquiv.subgroupCongr hfrange) |>.symm⟩

/-- Let `E ◁ X` be quasisimple and `Y ≤ X` with `E ≤ Y`.  Put `N = C_X(E).subgroupOf Y` and
`π : ↥Y →* ↥Y ⧸ N`, and `L = E.map π` (the image of `E`).  Then `L ◁ ↥Y ⧸ N`, `L` has trivial
centralizer there, and `L ≃* ↥E ⧸ Z(E)`. -/
theorem map_centralizer_eq_bot_and_equiv {X : Type*} [Group X] (E Y : Subgroup X) (hEY : E ≤ Y)
    (hEn : E.Normal) (hEq : Work.GW2.IsQuasisimple E) :
    let N : Subgroup ↥Y := (Subgroup.centralizer (E : Set X)).subgroupOf Y
    let L : Subgroup (↥Y ⧸ N) := (E.subgroupOf Y).map (QuotientGroup.mk' N)
    L.Normal ∧ Subgroup.centralizer (L : Set (↥Y ⧸ N)) = ⊥ ∧
      Nonempty (L ≃* (↥E ⧸ Subgroup.center ↥E)) := by
  dsimp only
  refine ⟨?_, ?_, ?_⟩
  · infer_instance
  · exact centralizer_map_quotient_eq_bot E Y hEY hEn hEq.1
  · exact map_subgroupOf_quotient_equiv_center E Y hEY hEn

end Work.DSTR
