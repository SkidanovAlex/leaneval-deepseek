import Mathlib
import Submission.Work.BG.HatInjDefs

namespace Work.BG

open OddOrder.RepresentationTheory Work.GW2 Work.GW2.C16 in
/-- For `ν ∈ 𝒮₄(C)` (so `sconj C ν = ν`), the restriction `ν|_U` is invariant under `sigmaU C`
(conjugation by `s`): `ν|_U (sigmaU C u) = ν|_U u` for all `u : ↥C.P.U`.

Route: `sconj C ν = Work.BG.conjByH C.P C.s ν` and `Work.BG.conjMulEquiv_apply` identifies the
conjugation action of `s` on `H₀` with `sigmaU C` on `U`. -/
theorem hatInjRestrictSigma {G : Type} [Group G] [Finite G] {D : Work.GW2.BGData G}
    (C : Work.BG.Sec2Ctx G) (hc : Work.GW2.C16.Compat D C) (hn : D.n = 2)
    {ν : ClassFunction ↥C.P.H0 ℂ} (hν : ν ∈ Work.GW2.C16.S4Index C) :
    ∀ u : ↥C.P.U, Work.BG.restrictU C ν (Work.BG.sigmaU C u) = Work.BG.restrictU C ν u := by
  intro u
  -- `s`-invariance of `ν`, from `ν ∈ 𝒮₄(C)`.
  have hsconj : sconj C ν = ν := hν.2.1
  -- The two elements of `H₀` at which we evaluate `ν` agree in `G`.
  have hkey : conjMulEquiv C.P C.s (⟨(u : G), C.P.U_le_H0 u.2⟩ : ↥C.P.H0)
      = (⟨((sigmaU C u : ↥C.P.U) : G), C.P.U_le_H0 (sigmaU C u).2⟩ : ↥C.P.H0) :=
    Subtype.ext (by rw [conjMulEquiv_apply, sigmaU_apply_coe])
  calc restrictU C ν (sigmaU C u)
      = ν (⟨((sigmaU C u : ↥C.P.U) : G), C.P.U_le_H0 (sigmaU C u).2⟩ : ↥C.P.H0) := rfl
    _ = ν (conjMulEquiv C.P C.s (⟨(u : G), C.P.U_le_H0 u.2⟩ : ↥C.P.H0)) := by rw [hkey]
    _ = conjByH C.P C.s ν (⟨(u : G), C.P.U_le_H0 u.2⟩ : ↥C.P.H0) := rfl
    _ = sconj C ν (⟨(u : G), C.P.U_le_H0 u.2⟩ : ↥C.P.H0) := rfl
    _ = ν (⟨(u : G), C.P.U_le_H0 u.2⟩ : ↥C.P.H0) := by rw [hsconj]
    _ = restrictU C ν u := rfl

end Work.BG
