import Mathlib
import Submission.Work.Higman.clo_hard_defs
import Submission.Work.Higman.h8_trivial_action_quot

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `C/A` is an irreducible `𝔽₂⟨ξ⟩`-module (Higman's Lemma 8, the closeness of the layers)

Let `P` be a Suzuki 2-group with automorphism `ξ`, `A ≤ C ≤ P` with `A` a `ξ`-invariant abelian
normal subgroup, `C` normal and `ξ`-invariant, and suppose that `A` and `C` are adjacent in the
family of normal `ξ`-invariant subgroups (`hcover`) and that `C ^ (2) ≤ A`, `⁅C,C⁆ = A`
(the data `CloH8Data`).  Then the only `ξ`-invariant subgroups of `V = C/A` are `⊥` and `⊤`.

The point is Higman's `h8_trivial_action_quot`: `P` acts trivially on `C/A`.  Hence the full
preimage in `P` of a `ξ`-invariant subgroup `W ≤ C/A` is a normal `ξ`-invariant subgroup `D`
with `A ≤ D ≤ C`, so `hcover` forces `D = A` or `D = C`, i.e. `W = ⊥` or `W = ⊤`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

open scoped commutatorElement

namespace Work.Higman.H8

variable {P : Type} [Group P] [Finite P]

/-- **`cloXiQuot` on a representative.** -/
theorem cloXiQuot_mk_h8 (h : IsSuzuki2Grp P) {A C : Subgroup P} [A.Normal]
    (hAinv : A.map (h.xi : MulAut P).toMonoidHom = A)
    (hCinv : C.map (h.xi : MulAut P).toMonoidHom = C) (u : ↥C) :
    cloXiQuot h hAinv hCinv (QuotientGroup.mk u) = QuotientGroup.mk (cloXiC h hCinv u) := by
  rw [cloXiQuot]
  exact QuotientGroup.congr_mk _ _ _ _ u

/-- The inverse of `cloXiQuot` preserves a `cloXiQuot`-invariant subgroup.  This is the
finiteness statement that the pointwise invariance `W ≤ cloXiQuot '' W` is really an
invariance. -/
theorem cloXiQuot_symm_mem (h : IsSuzuki2Grp P) {A C : Subgroup P} [A.Normal]
    (S : CloH8Data h A C) (W : Subgroup (↥C ⧸ (A.subgroupOf C)))
    (hW : ∀ v ∈ W, cloXiQuot h S.hA.map_eq S.hCinv v ∈ W) :
    ∀ v ∈ W, (cloXiQuot h S.hA.map_eq S.hCinv).symm v ∈ W := by
  classical
  have hinj : Function.Injective
      (fun w : ↥W => (⟨cloXiQuot h S.hA.map_eq S.hCinv (w : ↥C ⧸ (A.subgroupOf C)),
        hW (w : ↥C ⧸ (A.subgroupOf C)) w.2⟩ : ↥W)) := by
    intro x y hxy
    apply Subtype.ext
    exact (cloXiQuot h S.hA.map_eq S.hCinv).injective (Subtype.ext_iff.mp hxy)
  intro v hv
  obtain ⟨w, hw⟩ := Finite.surjective_of_injective hinj (⟨v, hv⟩ : ↥W)
  have hwv : cloXiQuot h S.hA.map_eq S.hCinv (w : ↥C ⧸ (A.subgroupOf C)) = v :=
    Subtype.ext_iff.mp hw
  have h1 : (cloXiQuot h S.hA.map_eq S.hCinv).symm v = (w : ↥C ⧸ (A.subgroupOf C)) := by
    rw [← hwv, MulEquiv.symm_apply_apply]
  rw [h1]
  exact w.2

theorem cloXiQuot_irreducible {P : Type} [Group P] [Finite P] (h : IsSuzuki2Grp P)
    {A C : Subgroup P} [A.Normal] (S : CloH8Data h A C) :
    ∀ W : Subgroup (↥C ⧸ (A.subgroupOf C)),
      (∀ v ∈ W, cloXiQuot h S.hA.map_eq S.hCinv v ∈ W) → W = ⊥ ∨ W = ⊤ := by
  intro W hW
  -- `P` acts trivially on `C / A`
  have htriv : ⁅(⊤ : Subgroup P), C⁆ ≤ A :=
    h8_trivial_action_quot h S.hA S.hCn S.hCinv S.hAC S.hCA S.hcover S.hC2 S.hCd
  -- the preimage of `W` in `C` ...
  set W' : Subgroup ↥C := Subgroup.comap (QuotientGroup.mk' (A.subgroupOf C)) W with hW'def
  -- ... and its image `D` in `P`; it is a normal, `ξ`-invariant subgroup with `A ≤ D ≤ C`.
  set D : Subgroup P := Subgroup.map C.subtype W' with hDdef
  have hAleD : A ≤ D := by
    rw [hDdef]
    intro a ha
    refine Subgroup.mem_map.mpr ⟨(⟨a, S.hAC ha⟩ : ↥C), ?_, rfl⟩
    rw [hW'def, Subgroup.mem_comap]
    have h1 : QuotientGroup.mk' (A.subgroupOf C) (⟨a, S.hAC ha⟩ : ↥C) = 1 := by
      rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
      exact Subgroup.mem_subgroupOf.mpr ha
    rw [h1]
    exact W.one_mem
  have hDleC : D ≤ C := by
    rw [hDdef]
    exact Subgroup.map_subtype_le W'
  have hDnorm : D.Normal := by
    rw [hDdef]
    refine ⟨fun x hx g => ?_⟩
    obtain ⟨c, hc, hcx⟩ := Subgroup.mem_map.mp hx
    have hx' : x = (c : P) := hcx.symm
    rw [hx']
    have hcm : QuotientGroup.mk' (A.subgroupOf C) c ∈ W := by
      rw [hW'def] at hc
      exact Subgroup.mem_comap.mp hc
    rw [QuotientGroup.mk'_apply] at hcm
    have hgC : g * (c : P) * g⁻¹ ∈ C := S.hCn.conj_mem (c : P) c.2 g
    refine Subgroup.mem_map.mpr ⟨(⟨g * (c : P) * g⁻¹, hgC⟩ : ↥C), ?_, rfl⟩
    rw [hW'def, Subgroup.mem_comap]
    have heq : QuotientGroup.mk' (A.subgroupOf C) c
        = QuotientGroup.mk' (A.subgroupOf C) (⟨g * (c : P) * g⁻¹, hgC⟩ : ↥C) := by
      rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq,
        Subgroup.mem_subgroupOf]
      show (c : P)⁻¹ * (g * (c : P) * g⁻¹) ∈ A
      have hmemA : ⁅g, (c : P)⁆ ∈ A :=
        htriv (Subgroup.commutator_mem_commutator (Subgroup.mem_top g) c.2)
      have hconj : (c : P)⁻¹ * ⁅g, (c : P)⁆ * ((c : P)⁻¹)⁻¹ ∈ A :=
        (inferInstance : A.Normal).conj_mem ⁅g, (c : P)⁆ hmemA (c : P)⁻¹
      have hkey : (c : P)⁻¹ * (g * (c : P) * g⁻¹)
          = (c : P)⁻¹ * ⁅g, (c : P)⁆ * ((c : P)⁻¹)⁻¹ := by
        rw [commutatorElement_def]; group
      rw [hkey]
      exact hconj
    rw [← heq, QuotientGroup.mk'_apply]
    exact hcm
  have hDinv : D.map (h.xi : MulAut P).toMonoidHom = D := by
    rw [hDdef]
    apply le_antisymm
    · -- `ξ` maps `D` into itself
      intro y hy
      obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hy
      obtain ⟨c, hc, rfl⟩ := Subgroup.mem_map.mp hx
      have hcm : QuotientGroup.mk' (A.subgroupOf C) c ∈ W := by
        rw [hW'def] at hc
        exact Subgroup.mem_comap.mp hc
      rw [QuotientGroup.mk'_apply] at hcm
      have hxiC : h.xi (c : P) ∈ C :=
        le_of_eq S.hCinv (Subgroup.mem_map_of_mem ((h.xi : MulAut P).toMonoidHom) c.2)
      refine Subgroup.mem_map.mpr ⟨(⟨h.xi (c : P), hxiC⟩ : ↥C), ?_, rfl⟩
      rw [hW'def, Subgroup.mem_comap]
      have hspec : cloXiQuot h S.hA.map_eq S.hCinv (QuotientGroup.mk c)
          = QuotientGroup.mk' (A.subgroupOf C) (⟨h.xi (c : P), hxiC⟩ : ↥C) := by
        rw [cloXiQuot_mk_h8, QuotientGroup.mk'_apply]
        rfl
      rw [← hspec]
      exact hW (QuotientGroup.mk c) hcm
    · -- `D` is contained in its image under `ξ`
      intro y hy
      obtain ⟨c, hc, rfl⟩ := Subgroup.mem_map.mp hy
      have hcm : QuotientGroup.mk' (A.subgroupOf C) c ∈ W := by
        rw [hW'def] at hc
        exact Subgroup.mem_comap.mp hc
      rw [QuotientGroup.mk'_apply] at hcm
      have hxC : (h.xi : MulAut P).symm (c : P) ∈ C :=
        symm_mem_of_map_eq (h.xi : MulAut P) S.hCinv c.2
      refine Subgroup.mem_map.mpr
        ⟨(h.xi : MulAut P).symm (c : P), ?_,
          MulEquiv.apply_symm_apply h.xi (c : P)⟩
      refine Subgroup.mem_map.mpr ⟨(⟨(h.xi : MulAut P).symm (c : P), hxC⟩ : ↥C), ?_, rfl⟩
      rw [hW'def, Subgroup.mem_comap]
      have hspec : cloXiQuot h S.hA.map_eq S.hCinv
          (QuotientGroup.mk (⟨(h.xi : MulAut P).symm (c : P), hxC⟩ : ↥C))
          = QuotientGroup.mk c := by
        rw [cloXiQuot_mk_h8]
        congr 1
        exact Subtype.ext (MulEquiv.apply_symm_apply h.xi (c : P))
      have hsymm : QuotientGroup.mk (⟨(h.xi : MulAut P).symm (c : P), hxC⟩ : ↥C)
          = (cloXiQuot h S.hA.map_eq S.hCinv).symm (QuotientGroup.mk c) :=
        (MulEquiv.eq_symm_apply (cloXiQuot h S.hA.map_eq S.hCinv)).mpr hspec
      rw [QuotientGroup.mk'_apply, hsymm]
      exact cloXiQuot_symm_mem h S W hW (QuotientGroup.mk c) hcm
  rcases S.hcover D hDnorm hDinv hAleD hDleC with hDA | hDC
  · -- `D = A`: the preimage of `W` is `A`, i.e. `W` is trivial
    left
    rw [Subgroup.eq_bot_iff_forall]
    intro v hv
    obtain ⟨u, rfl⟩ := QuotientGroup.mk_surjective v
    have huW' : u ∈ W' := by
      rw [hW'def, Subgroup.mem_comap, QuotientGroup.mk'_apply]
      exact hv
    have huD : (u : P) ∈ D := Subgroup.mem_map.mpr ⟨u, huW', rfl⟩
    have huA : (u : P) ∈ A := by rw [← hDA]; exact huD
    rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
    exact huA
  · -- `D = C`: every element of `C/A` lies in `W`
    right
    apply le_antisymm le_top
    intro v _
    obtain ⟨u, rfl⟩ := QuotientGroup.mk_surjective v
    have huD : (u : P) ∈ D := by rw [hDC]; exact u.2
    obtain ⟨c, hc, hcu⟩ := Subgroup.mem_map.mp huD
    have hc_eq : c = u := Subtype.ext hcu
    have hcm : QuotientGroup.mk' (A.subgroupOf C) c ∈ W := by
      rw [hW'def] at hc
      exact Subgroup.mem_comap.mp hc
    rw [QuotientGroup.mk'_apply] at hcm
    rw [← hc_eq]
    exact hcm

end Work.Higman.H8
