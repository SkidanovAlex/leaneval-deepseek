import Mathlib
import Submission.Work.BG.HatInjDefs
import Submission.Work.BG.thmCSmallAux

namespace Work.BG

open OddOrder.RepresentationTheory Work.GW2 Work.GW2.C16 in
/-- Every element of `U` fixed by conjugation by `s = t₁` lies in `B = B₁ ⊓ B₂`.

Route: `u ∈ U = D.U` and `sigmaU C u = u` mean `t₁ u t₁⁻¹ = u`, i.e. `u ∈ C_G(t₁)`, so
`u ∈ D.B1 = D.U ⊓ C_G(t₁)`; for `D.n = 2` one has `D.B1 = D.B2` (`Work.BG.thmCSmallAux`), hence
`u ∈ D.B = D.B1 ⊓ D.B2`. -/
theorem hatInjBIdent {G : Type} [Group G] [Finite G] {D : Work.GW2.BGData G}
    (C : Work.BG.Sec2Ctx G) (hc : Work.GW2.C16.Compat D C) (hn : D.n = 2)
    (u : ↥C.P.U) (hu : Work.BG.sigmaU C u = u) : (u : G) ∈ D.B := by
  -- `sigmaU C u = u` says exactly that `s = t₁` conjugates `u` to itself.
  have hfix : (C.s : G) * (u : G) * (C.s : G)⁻¹ = (u : G) := by
    have h := congrArg (fun x : ↥C.P.U => (x : G)) hu
    simpa only [Work.BG.sigmaU_apply_coe] using h
  -- hence `u` commutes with `s = t₁`.
  have hcomm : (C.s : G) * (u : G) = (u : G) * (C.s : G) := by
    have h2 : ((C.s : G) * (u : G) * (C.s : G)⁻¹) * (C.s : G) = (u : G) * (C.s : G) := by
      rw [hfix]
    calc (C.s : G) * (u : G)
        = ((C.s : G) * (u : G) * (C.s : G)⁻¹) * (C.s : G) := by group
      _ = (u : G) * (C.s : G) := h2
  -- `u ∈ U = D.U`.
  have huU : (u : G) ∈ D.U := hc.U_eq ▸ u.2
  -- `u ∈ C_G(t₁)`.
  have hu1 : (u : G) ∈ Subgroup.centralizer ({D.t1} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff, ← hc.s_eq]
    exact hcomm.symm
  have hB1 : (u : G) ∈ D.B1 := Subgroup.mem_inf.mpr ⟨huU, hu1⟩
  -- for `D.n = 2`, `B₁ = B₂`.
  have hB_eq : D.B1 = D.B2 := (thmCSmallAux D hn).2.2.1
  have hB2 : (u : G) ∈ D.B2 := hB_eq ▸ hB1
  exact Subgroup.mem_inf.mpr ⟨hB1, hB2⟩

end Work.BG
