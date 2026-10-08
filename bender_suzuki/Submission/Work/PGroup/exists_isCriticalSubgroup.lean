import Mathlib
import Submission.Work.PGroup.Basic
import Submission.Work.PGroup.Omega1
import Submission.Work.PGroup.CriticalInternal

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# Existence of Thompson critical subgroups

This file transfers Thompson's critical subgroup theorem, proved intrinsically for a finite
`p`-group in `Work.PGroup.exists_characteristic_critical`, to a `p`-subgroup `P` of an arbitrary
ambient group `G`.  A critical subgroup of `↥P` is mapped into `G` along `P.subtype`; since it is
characteristic in `↥P`, its image is invariant under `N_G(P)`.
-/

set_option linter.style.haveILetI false
set_option linter.unusedVariables false

open Subgroup
open scoped Pointwise

namespace Work.PGroup

/-- `conjBy` is the image of the subgroup under the monoid homomorphism given by conjugation. -/
theorem conjBy_eq_map {G : Type*} [Group G] (g : G) (C : Subgroup G) :
    conjBy g C = C.map (MulAut.conj g).toMonoidHom := by
  rw [conjBy, Subgroup.pointwise_smul_def]; rfl

/-- The Frattini subgroup is carried to the Frattini subgroup by a group isomorphism. -/
theorem frattini_map_mulEquiv {A B : Type*} [Group A] [Group B] (e : A ≃* B) :
    (frattini A).map e.toMonoidHom = frattini B := by
  refine le_antisymm ?_ ?_
  · exact Subgroup.map_le_iff_le_comap.mpr (frattini_le_comap_frattini_of_surjective e.surjective)
  · have h : ((frattini B).map e.symm.toMonoidHom).map e.toMonoidHom ≤
        (frattini A).map e.toMonoidHom :=
      Subgroup.map_mono (f := e.toMonoidHom)
        (Subgroup.map_le_iff_le_comap.mpr
          (frattini_le_comap_frattini_of_surjective (φ := e.symm.toMonoidHom) e.symm.surjective))
    rw [Subgroup.map_map] at h
    have hcomp : e.toMonoidHom.comp e.symm.toMonoidHom = MonoidHom.id B := by
      ext x; simp
    rw [hcomp, Subgroup.map_id] at h
    exact h

theorem exists_isCriticalSubgroup {G : Type*} [Group G] {p : ℕ} (hp : p.Prime)
    (P : Subgroup G) [Finite P] (hP : IsPGroup p P) (hne : P ≠ ⊥) :
    ∃ C : Subgroup G, Work.PGroup.IsCriticalSubgroup p P C := by
  haveI hnt : Nontrivial ↥P := by
    obtain ⟨x, hxne⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hne
    exact ⟨x, 1, hxne⟩
  obtain ⟨C', hchar, hne', hfr, hcomm, hsc⟩ := exists_characteristic_critical_intrinsic (H := ↥P) hp hP
  haveI : C'.Characteristic := hchar
  set C : Subgroup G := C'.map P.subtype with hC
  set e := C'.equivMapOfInjective P.subtype P.subtype_injective with he
  have hcomp : (C'.map P.subtype).subtype.comp e.toMonoidHom = P.subtype.comp C'.subtype := by
    ext x
    simp only [MonoidHom.comp_apply]
    change (e x : G) = P.subtype (C'.subtype x)
    rw [he, Subgroup.coe_equivMapOfInjective_apply]
    rfl
  have heq_fr : frattiniIn C = (frattiniIn C').map P.subtype := by
    rw [hC, frattiniIn, frattiniIn, ← frattini_map_mulEquiv e, Subgroup.map_map]
    change Subgroup.map ((C'.map P.subtype).subtype.comp e.toMonoidHom) (frattini ↥C')
      = map P.subtype (map C'.subtype (frattini ↥C'))
    rw [hcomp, ← Subgroup.map_map]
  have heq_ce : centerIn C = (centerIn C').map P.subtype := by
    rw [hC, centerIn, centerIn, ← Subgroup.map_center_eq e, Subgroup.map_map]
    change Subgroup.map ((C'.map P.subtype).subtype.comp e.toMonoidHom) (Subgroup.center ↥C')
      = map P.subtype (map C'.subtype (Subgroup.center ↥C'))
    rw [hcomp, ← Subgroup.map_map]
  have heq_cm : ⁅P, C⁆ = (⁅(⊤ : Subgroup ↥P), C'⁆).map P.subtype := by
    rw [hC, Subgroup.map_commutator, Subgroup.map_top, Subgroup.range_subtype]
  refine ⟨C, Subgroup.map_subtype_le C', ?_, ?_, ?_, ?_, ?_⟩
  · rw [hC]
    intro hbot
    refine hne' (Subgroup.map_injective P.subtype_injective ?_)
    rw [hbot, Subgroup.map_bot]
  · intro g hg
    rw [conjBy_eq_map]
    let φ : ↥P ≃* ↥P :=
      { toFun := fun x => ⟨g * (x : G) * g⁻¹, (Subgroup.mem_normalizer_iff.mp hg (x : G)).mp x.2⟩
        invFun := fun x => ⟨g⁻¹ * (x : G) * g, (Subgroup.mem_normalizer_iff''.mp hg (x : G)).mp x.2⟩
        left_inv := fun x => by apply Subtype.ext; group
        right_inv := fun x => by apply Subtype.ext; group
        map_mul' := fun x y => by
          apply Subtype.ext
          simp only [Subgroup.coe_mul]
          group }
    have hφ : C'.map φ.toMonoidHom = C' := (Subgroup.characteristic_iff_map_eq.mp hchar) φ
    have hcomp2 : (MulAut.conj g).toMonoidHom.comp P.subtype = P.subtype.comp φ.toMonoidHom := by
      ext x
      simp only [MonoidHom.comp_apply]
      rfl
    rw [hC, Subgroup.map_map, hcomp2, ← Subgroup.map_map, hφ]
  · rw [heq_fr, heq_ce]
    exact Subgroup.map_mono (f := P.subtype) hfr
  · rw [heq_ce, heq_cm]
    exact Subgroup.map_mono (f := P.subtype) hcomm
  · intro x hx
    obtain ⟨hxP, hxC⟩ := Subgroup.mem_inf.mp hx
    have hxC' : (⟨x, hxP⟩ : ↥P) ∈ Subgroup.centralizer (C' : Set ↥P) := by
      rw [Subgroup.mem_centralizer_iff]
      intro c hc
      apply Subtype.ext
      simp only [Subgroup.coe_mul]
      exact (Subgroup.mem_centralizer_iff.mp hxC) ((c : ↥P) : G) (by
        rw [hC]; exact Subgroup.mem_map.mpr ⟨c, hc, rfl⟩)
    rw [hC]
    exact Subgroup.mem_map.mpr ⟨⟨x, hxP⟩, hsc hxC', rfl⟩

end Work.PGroup
