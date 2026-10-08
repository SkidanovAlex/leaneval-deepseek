import Mathlib
import Submission.Work.Higman.Defs
import Submission.Work.Higman.Basic
import Submission.Work.Higman.SuzukiMaximal
import Submission.Work.Higman.PowSub
import Submission.Work.Higman.mem_comap_center_iff
import Submission.Work.Higman.map_comap_center_quot

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

open scoped commutatorElement

namespace Work.Higman

/-- **Higman's Lemma 8, "trivial action" step.**  Let `A` be a `ξ`-invariant abelian normal
subgroup of a Suzuki 2-group `P`, and let `C` be a normal `ξ`-invariant subgroup with
`A ≤ C`, `A ≠ C`, `C ^ (2) ≤ A`, `⁅C, C⁆ = A`, and such that `A` and `C` are adjacent in the
family of normal `ξ`-invariant subgroups (`hcover`).  Then `P` acts trivially on `C/A`, i.e.
`⁅P, C⁆ ≤ A`.

The proof is short.  Let `Γ ≤ P` be the preimage of the centre of `Q := P/A`.  Then `Γ` is
normal and `ξ`-invariant, `A ≤ Γ`, and `D := Γ ⊓ C` satisfies `A ≤ D ≤ C`.  If `D = A`, then
`(C/A)^P = C/A ⊓ Z(Q) = 1`; but `Q` is a `2`-group, hence nilpotent, and `C/A` is a non-trivial
normal subgroup of it, so it meets `Z(Q)` non-trivially -- contradiction.  Hence `D = C`,
i.e. `C ≤ Γ`, which says exactly that every element of `C` commutes with every element of `P`
modulo `A`, i.e. `⁅⊤, C⁆ ≤ A`. -/
theorem h8_trivial_action_quot {P : Type} [Group P] [Finite P] (h : Work.Higman.IsSuzuki2Grp P)
    {A C : Subgroup P} (hA : Work.Higman.IsXiAbelNormal h A)
    (hCn : C.Normal) (hCinv : C.map (h.xi : MulAut P).toMonoidHom = C)
    (hAC : A ≤ C) (hCA : A ≠ C)
    (hcover : ∀ D : Subgroup P, D.Normal → D.map (h.xi : MulAut P).toMonoidHom = D →
      A ≤ D → D ≤ C → D = A ∨ D = C)
    (hC2 : Work.Higman.powSub C 2 ≤ A) (hCd : ⁅C, C⁆ = A) :
    ⁅(⊤ : Subgroup P), C⁆ ≤ A := by
  haveI hAn : A.Normal := hA.normal
  haveI hCn' : C.Normal := hCn
  -- `Γ`: the preimage of the centre of `P ⧸ A`, i.e. the elements of `P` commuting with
  -- every element of `P` modulo `A`.
  set Γ : Subgroup P := (Subgroup.center (P ⧸ A)).comap (QuotientGroup.mk' A) with hΓdef
  have hΓchar : ∀ x : P, x ∈ Γ ↔ ∀ g : P, ⁅g, x⁆ ∈ A := by
    intro x
    rw [hΓdef]
    exact mem_comap_center_iff
  haveI hΓn : Γ.Normal := by
    rw [hΓdef]
    exact Subgroup.Normal.comap inferInstance (QuotientGroup.mk' A)
  have hΓinv : Γ.map (h.xi : MulAut P).toMonoidHom = Γ := by
    rw [hΓdef]
    exact map_comap_center_quot (h.xi : MulAut P) hA.map_eq
  have hAleΓ : A ≤ Γ := by
    intro a ha
    rw [hΓchar]
    intro g
    have h1 : g * a * g⁻¹ ∈ A := hAn.conj_mem a ha g
    rw [commutatorElement_def]
    exact A.mul_mem h1 (A.inv_mem ha)
  set D : Subgroup P := Γ ⊓ C with hDdef
  haveI hDn : D.Normal := by
    rw [hDdef]
    infer_instance
  have hDinv : D.map (h.xi : MulAut P).toMonoidHom = D := by
    rw [hDdef, Subgroup.map_inf Γ C (h.xi : MulAut P).toMonoidHom
      (h.xi : MulAut P).injective, hΓinv, hCinv]
  have hAleD : A ≤ D := by
    rw [hDdef]
    exact le_inf hAleΓ hAC
  have hDleC : D ≤ C := by
    rw [hDdef]
    exact inf_le_right
  -- a non-identity element of `C/A` central in `P/A`: `P/A` is a `2`-group, hence nilpotent,
  -- and any non-trivial normal subgroup of a nilpotent group meets the centre.
  haveI hNil : Group.IsNilpotent (P ⧸ A) := (h.isPGroup.to_quotient A).isNilpotent
  have hCbne : C.map (QuotientGroup.mk' A) ≠ ⊥ := by
    intro hb
    have hle : C ≤ A := by
      simpa [QuotientGroup.ker_mk' A] using (Subgroup.map_eq_bot_iff C).mp hb
    exact hCA (le_antisymm hle hAC).symm
  have hne : C.map (QuotientGroup.mk' A) ⊓ Subgroup.center (P ⧸ A) ≠ ⊥ :=
    Group.IsNilpotent.inf_center_ne_bot_of_normal hCbne
  obtain ⟨x, hxne⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hne
  have hxvCb : (x : P ⧸ A) ∈ C.map (QuotientGroup.mk' A) := x.2.1
  have hxvZ : (x : P ⧸ A) ∈ Subgroup.center (P ⧸ A) := x.2.2
  have hxvne : (x : P ⧸ A) ≠ 1 := fun hcon => hxne (Subtype.ext (by simpa using hcon))
  obtain ⟨c, hcC, hcx⟩ := Subgroup.mem_map.mp hxvCb
  have hcΓ : c ∈ Γ := by
    rw [hΓchar]
    intro g
    have hcomm : (QuotientGroup.mk' A) g * (x : P ⧸ A) = (x : P ⧸ A) * (QuotientGroup.mk' A) g :=
      Subgroup.mem_center_iff.mp hxvZ ((QuotientGroup.mk' A) g)
    have h1 : (QuotientGroup.mk' A) ⁅g, c⁆ = 1 := by
      rw [map_commutatorElement, hcx, commutatorElement_eq_one_iff_mul_comm]
      exact hcomm
    rwa [← MonoidHom.mem_ker, QuotientGroup.ker_mk'] at h1
  have hcA : c ∉ A := by
    intro hcA'
    have h1 : (QuotientGroup.mk' A) c = 1 := by
      rw [← MonoidHom.mem_ker, QuotientGroup.ker_mk']
      exact hcA'
    rw [hcx] at h1
    exact hxvne h1
  have hDne : D ≠ A := by
    intro hDA
    have hcD : c ∈ A := by
      rw [← hDA]
      exact ⟨hcΓ, hcC⟩
    exact hcA hcD
  rcases hcover D hDn hDinv hAleD hDleC with hDA | hDC
  · exact absurd hDA hDne
  · have hCleΓ : C ≤ Γ := by
      intro y hy
      have hy' : y ∈ D := by rw [hDC]; exact hy
      rw [hDdef] at hy'
      exact hy'.1
    rw [Subgroup.commutator_le]
    intro g _ c' hc'
    exact (hΓchar c').mp (hCleΓ hc') g

end Work.Higman
