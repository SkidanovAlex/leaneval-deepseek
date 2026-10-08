import Mathlib
import Submission.Work.BG.hatInjBIdent
import Submission.Work.BG.HatInjDefs
import Submission.Work.BG.thmCSmallAux

namespace Work.BG

open OddOrder.RepresentationTheory Work.GW2 Work.GW2.C16 Subgroup

/-- The fixed-point subgroup of `sigmaU C` (the elements of `U = C.P.U` centralized by
`s = t₁`), viewed inside `G` through `U ≤ G`, coincides with `B = B₁ ⊓ B₂ = C_U(t₁) ⊓ C_U(t₂)`.

The inclusion `⊆` is `hatInjBIdent`.  For the reverse inclusion, an element of `D.B` lies in
`D.U = C.P.U` and is centralized by `t₁ = C.s`, hence is fixed by `sigmaU C`. -/
theorem hatFixedMapEq {G : Type} [Group G] [Finite G] (D : Work.GW2.BGData G) (C : Work.BG.Sec2Ctx G)
    (hc : Work.GW2.C16.Compat D C) (hn : D.n = 2) :
    (Work.BG.fixedSubgroup (Work.BG.sigmaU C)).map (Subgroup.subtype C.P.U) = D.B := by
  refine le_antisymm ?_ ?_
  · intro x hx
    rw [Subgroup.mem_map] at hx
    obtain ⟨u, hu, rfl⟩ := hx
    exact hatInjBIdent C hc hn u hu
  · intro x hx
    rw [Subgroup.mem_map]
    obtain ⟨hx1, _hx2⟩ := Subgroup.mem_inf.mp hx
    obtain ⟨hxU, hxc⟩ := Subgroup.mem_inf.mp hx1
    have hxU' : x ∈ C.P.U := hc.U_eq ▸ hxU
    refine ⟨⟨x, hxU'⟩, ?_, rfl⟩
    apply Subtype.ext
    have hcomm : x * D.t1 = D.t1 * x := Subgroup.mem_centralizer_singleton_iff.mp hxc
    show (C.s : G) * x * (C.s : G)⁻¹ = x
    rw [hc.s_eq, ← hcomm]
    group

end Work.BG
