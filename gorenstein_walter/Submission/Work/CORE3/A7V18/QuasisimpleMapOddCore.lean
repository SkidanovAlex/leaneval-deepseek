import Mathlib
import Submission.Work.CORE3.Defs
import Submission.Work.ASM.oddCore_odd
import Submission.Work.CORE3.A7V18.InfOddCoreLeCenter
import Submission.Work.CORE3.A7V18.QuotientCenterIso

/-!
# `E ↦ EO(X)/O(X)` preserves quasisimplicity with central quotient `A₇`

Let `X` be a finite group, `E ◁ X` quasisimple (perfect, with `E/Z(E)` simple) and
`E/Z(E) ≃* A₇`.  If `E ⊄ O(X)` (i.e. `E` is not an odd-order group) then the image
`E' = EO(X)/O(X) ≤ X/O(X)` is again quasisimple, nontrivial, and `E'/Z(E') ≃* A₇`.

The two ingredients are separated out:

* `InfOddCoreLeCenter` : `E ⊓ O(X) ≤ Z(E)` — the image of `E ⊓ O(X)` in the simple group
  `E/Z(E)` is normal, hence `⊥` or everything; the second alternative would make `E/Z(E)`
  a quotient of an odd-order group, hence odd, contradicting `|A₇| = 2520`.
* `QuotientCenterIso` : for perfect `Y` and `M ◁ Y`, the natural surjection
  `Y/Z(Y) ↠ (Y/M)/Z(Y/M)` (which exists because `Z(Y)` maps into `Z(Y/M)`) has target `⊥`
  or `⊤`; if `M ≠ ⊤` then `Y/M` is a nontrivial perfect group, so its centre is proper,
  and the map is an isomorphism.  Hence `(Y/M)/Z(Y/M) ≃* Y/Z(Y)`.

With `Y = ↥E`, `M = (E ⊓ O(X)).subgroupOf E`, the first isomorphism theorem identifies
`Y/M` with `↥E'`, and the centre is transported along that isomorphism
(`QuotientGroup.congr` + `Subgroup.map_center_eq`).
-/

set_option linter.style.haveILetI false

namespace Work.CORE3.A7V18

open Subgroup

/-- The general form of the computation, for an arbitrary normal `N` with `E ⊓ N ≤ Z(E)`:
the image of a quasisimple `E` in `X ⧸ N` is quasisimple, nontrivial, and its central
quotient is again `A₇`. -/
private theorem map_quotient_of_central_inf {X : Type} [Group X] [Finite X]
    (E N : Subgroup X) [Nn : N.Normal] (hEn : E.Normal) (hEq : Work.GW2.IsQuasisimple E)
    (hA7 : Nonempty ((↥E ⧸ Subgroup.center ↥E) ≃* alternatingGroup (Fin 7)))
    (hcen : (E ⊓ N).subgroupOf E ≤ Subgroup.center ↥E) (hne : ¬ E ≤ N) :
    (E.map (QuotientGroup.mk' N)).Normal ∧
    Work.GW2.IsQuasisimple (E.map (QuotientGroup.mk' N)) ∧
    E.map (QuotientGroup.mk' N) ≠ ⊥ ∧
    Nonempty ((↥(E.map (QuotientGroup.mk' N)) ⧸
      Subgroup.center ↥(E.map (QuotientGroup.mk' N))) ≃* alternatingGroup (Fin 7)) := by
  classical
  obtain ⟨hA7e⟩ := hA7
  haveI hMn : ((E ⊓ N).subgroupOf E).Normal := by
    have h1 : (E ⊓ N).subgroupOf E = N.subgroupOf E := by
      rw [inf_comm]
      exact Subgroup.inf_subgroupOf_right N E
    rw [h1]
    exact Nn.subgroupOf E
  have hperf : Group.IsPerfect ↥E := Subgroup.isPerfect_iff.mpr hEq.1
  haveI := hperf
  have hMtop : (E ⊓ N).subgroupOf E ≠ ⊤ := by
    intro htop
    apply hne
    intro x hx
    have hy : (⟨x, hx⟩ : ↥E) ∈ (E ⊓ N).subgroupOf E := by
      rw [htop]; exact Subgroup.mem_top _
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_inf] at hy
    exact hy.2
  obtain ⟨⟨e1⟩, hsimple1⟩ := QuotientCenterIso ((E ⊓ N).subgroupOf E) hcen hMtop hEq.2
  haveI := hsimple1
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
  have e2 : (↥E ⧸ (E ⊓ N).subgroupOf E) ⧸
      Subgroup.center (↥E ⧸ (E ⊓ N).subgroupOf E) ≃*
      ↥(E.map (QuotientGroup.mk' N)) ⧸ Subgroup.center ↥(E.map (QuotientGroup.mk' N)) :=
    QuotientGroup.congr (Subgroup.center (↥E ⧸ (E ⊓ N).subgroupOf E))
      (Subgroup.center ↥(E.map (QuotientGroup.mk' N))) e0 (Subgroup.map_center_eq e0)
  refine ⟨hEn.map _ (QuotientGroup.mk'_surjective N), ⟨?_, ?_⟩, ?_, ?_⟩
  · rw [← Subgroup.map_commutator E E (QuotientGroup.mk' N), hEq.1]
  · exact MulEquiv.isSimpleGroup e2.symm
  · intro hbot
    apply hne
    intro x hx
    have hmem : (QuotientGroup.mk' N) x ∈ E.map (QuotientGroup.mk' N) :=
      Subgroup.mem_map.mpr ⟨x, hx, rfl⟩
    rw [hbot, Subgroup.mem_bot, QuotientGroup.mk'_apply] at hmem
    exact (QuotientGroup.eq_one_iff x).mp hmem
  · exact ⟨e2.symm.trans (e1.trans hA7e)⟩

theorem QuasisimpleMapOddCore {X : Type} [Group X] [Finite X] (E : Subgroup X) (hEn : E.Normal) (hEq : Work.GW2.IsQuasisimple E) (hA7 : Nonempty ((↥E ⧸ Subgroup.center ↥E) ≃* alternatingGroup (Fin 7))) (hEnb : ¬ E ≤ Work.GW2.oddCore X) : (E.map (QuotientGroup.mk' (Work.GW2.oddCore X))).Normal ∧ Work.GW2.IsQuasisimple (E.map (QuotientGroup.mk' (Work.GW2.oddCore X))) ∧ E.map (QuotientGroup.mk' (Work.GW2.oddCore X)) ≠ ⊥ ∧ Nonempty ((↥(E.map (QuotientGroup.mk' (Work.GW2.oddCore X))) ⧸ Subgroup.center ↥(E.map (QuotientGroup.mk' (Work.GW2.oddCore X)))) ≃* alternatingGroup (Fin 7)) := by
  refine map_quotient_of_central_inf E (Work.GW2.oddCore X) hEn hEq hA7 ?_ hEnb
  intro y hy
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_inf] at hy
  obtain ⟨c, hc, hce⟩ := Subgroup.mem_map.mp
    (InfOddCoreLeCenter E hEq hA7 ⟨hy.1, hy.2⟩)
  have hcy : c = y := Subtype.ext hce
  rwa [← hcy]

end Work.CORE3.A7V18
