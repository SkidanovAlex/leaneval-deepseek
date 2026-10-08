import Mathlib
import Submission.Work.CORE3.Defs
import Submission.Work.CORE3.A7V18.QuotientCenterIso

/-!
# Mapping a quasisimple subgroup to a quotient: central quotients agree

Let `X` be a finite group, `N ◁ X`, and `E ◁ X` quasisimple with `E ⊓ N ≤ Z(E)` and
`E ⊄ N`.  Then the image `E N / N = E.map (mk' N)` of `E` in `X ⧸ N` is again normal,
quasisimple and nontrivial, and the central quotients agree:

`E / Z(E) ≃* (E N / N) / Z(E N / N)`.

The proof writes `M = (E ⊓ N).subgroupOf E ≤ Z(E)`; the first isomorphism theorem gives
`↥E ⧸ M ≃* ↥(E.map (mk' N))`, the centre is transported along it, and `QuotientCenterIso`
computes the central quotient of `↥E ⧸ M` as `↥E ⧸ Z(↥E)`.
-/

set_option linter.style.haveILetI false

namespace Work.CORE3.A7V18

open Subgroup

theorem MapQuotientCenterIso {X : Type} [Group X] [Finite X] (E N : Subgroup X) [N.Normal]
    (hEn : E.Normal) (hEq : Work.GW2.IsQuasisimple E)
    (hcen : (E ⊓ N).subgroupOf E ≤ Subgroup.center ↥E) (hne : ¬ E ≤ N) :
    (E.map (QuotientGroup.mk' N)).Normal ∧
      Work.GW2.IsQuasisimple (E.map (QuotientGroup.mk' N)) ∧
      E.map (QuotientGroup.mk' N) ≠ ⊥ ∧
      Nonempty ((↥E ⧸ Subgroup.center ↥E) ≃*
        (↥(E.map (QuotientGroup.mk' N)) ⧸
          Subgroup.center ↥(E.map (QuotientGroup.mk' N)))) := by
  classical
  -- `M = (E ⊓ N).subgroupOf E` is normal in `↥E`.
  haveI hMn : ((E ⊓ N).subgroupOf E).Normal := by
    have h1 : (E ⊓ N).subgroupOf E = N.subgroupOf E := by
      rw [inf_comm]
      exact Subgroup.inf_subgroupOf_right N E
    rw [h1]
    exact (inferInstance : N.Normal).subgroupOf E
  have hperf : Group.IsPerfect ↥E := Subgroup.isPerfect_iff.mpr hEq.1
  haveI := hperf
  -- `M ≠ ⊤` because `E ⊄ N`.
  have hMtop : (E ⊓ N).subgroupOf E ≠ ⊤ := by
    intro htop
    apply hne
    intro x hx
    have hy : (⟨x, hx⟩ : ↥E) ∈ (E ⊓ N).subgroupOf E := by
      rw [htop]; exact Subgroup.mem_top _
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_inf] at hy
    exact hy.2
  -- Central quotient of `↥E ⧸ M`.
  obtain ⟨⟨e1⟩, hsimple1⟩ := QuotientCenterIso ((E ⊓ N).subgroupOf E) hcen hMtop hEq.2
  haveI := hsimple1
  -- The first isomorphism theorem: `↥E ⧸ M ≃* ↥(E.map (mk' N))`.
  let φ : ↥E →* X ⧸ N := (QuotientGroup.mk' N).comp E.subtype
  have hφker : φ.ker = (E ⊓ N).subgroupOf E := by
    ext y
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
    show (QuotientGroup.mk' N) (y : X) = 1 ↔ (y : X) ∈ E ∧ (y : X) ∈ N
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact ⟨fun h => ⟨y.2, h⟩, fun h => h.2⟩
  have hφrange : φ.range = E.map (QuotientGroup.mk' N) := by
    show ((QuotientGroup.mk' N).comp E.subtype).range = E.map (QuotientGroup.mk' N)
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  have e0 : ↥E ⧸ (E ⊓ N).subgroupOf E ≃* ↥(E.map (QuotientGroup.mk' N)) :=
    (QuotientGroup.quotientMulEquivOfEq hφker.symm).trans <|
      (QuotientGroup.quotientKerEquivRange φ).trans (MulEquiv.subgroupCongr hφrange)
  -- Transport of centres along `e0`.
  have e2 : (↥E ⧸ (E ⊓ N).subgroupOf E) ⧸
      Subgroup.center (↥E ⧸ (E ⊓ N).subgroupOf E) ≃*
      ↥(E.map (QuotientGroup.mk' N)) ⧸ Subgroup.center ↥(E.map (QuotientGroup.mk' N)) :=
    QuotientGroup.congr (Subgroup.center (↥E ⧸ (E ⊓ N).subgroupOf E))
      (Subgroup.center ↥(E.map (QuotientGroup.mk' N))) e0 (Subgroup.map_center_eq e0)
  refine ⟨hEn.map _ (QuotientGroup.mk'_surjective N), ⟨?_, ?_⟩, ?_, ?_⟩
  · -- Perfectness descends to the image.
    rw [← Subgroup.map_commutator E E (QuotientGroup.mk' N), hEq.1]
  · -- Simplicity of the central quotient descends along `e2`.
    exact MulEquiv.isSimpleGroup e2.symm
  · -- Nontriviality: `E ⊄ N`.
    intro hbot
    apply hne
    intro x hx
    have hmem : (QuotientGroup.mk' N) x ∈ E.map (QuotientGroup.mk' N) :=
      Subgroup.mem_map.mpr ⟨x, hx, rfl⟩
    rw [hbot, Subgroup.mem_bot, QuotientGroup.mk'_apply] at hmem
    exact (QuotientGroup.eq_one_iff x).mp hmem
  · -- `E / Z(E) ≃* (E N / N) / Z(E N / N)`.
    exact ⟨e1.symm.trans e2⟩

end Work.CORE3.A7V18
