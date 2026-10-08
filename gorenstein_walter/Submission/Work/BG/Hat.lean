import Mathlib
import Submission.Work.BG.Thm43Defs
import Submission.Work.BG.ThmABCCharDefs
import Submission.Work.BG.S02
import Submission.Work.BG.glaubValue
import Submission.Work.BG.modTwoIndep
import Submission.Work.BG.HatInjDefs
import Submission.Work.BG.H0Conj
import Submission.Work.BG.hatInjRestrictIrr
import Submission.Work.BG.hatInjRestrictSigma
import Submission.Work.BG.hatInjCongruentEq
import Submission.Work.BG.hatInjBIdent
import Submission.Work.BG.thmCSmallAux
import Submission.Work.BG.glauberman_two
import Submission.Work.BG.glaubMultCongruence
import Submission.Work.BG.hatFixedMapEq
import Submission.Work.BG.HatUniq

namespace Work.BG

open OddOrder.RepresentationTheory Work.GW2 Work.BG Work.GW2.C16 Work.GW2.C23 Subgroup

variable {G : Type} [Group G] [Finite G]

/-! ## Bridge between `C_U(sigmaU C)` and `D.B`

For `D.n = 2` the Sylow `2`-subgroup is Klein four, so `B1 = B2` and the fixed-point
subgroup of `sigmaU C` (conjugation by `s = t₁` on `U`) is isomorphic to `D.B`. -/

/-- `D.B` is contained in `D.U`. -/
theorem mem_DU_of_mem_B (D : Work.GW2.BGData G) {x : G} (hx : x ∈ D.B) : x ∈ D.U :=
  hx.1.1

/-- `D.B` is contained in the centralizer of `D.t1`. -/
theorem le_C_t1_of_mem_B (D : Work.GW2.BGData G) {x : G} (hx : x ∈ D.B) :
    x ∈ Subgroup.centralizer ({D.t1} : Set G) :=
  hx.1.2

/-- An element of `D.B`, viewed in `C.P.U`, is fixed by `sigmaU C`. -/
theorem sigmaU_eq_self_of_mem_B (D : Work.GW2.BGData G) (C : Work.BG.Sec2Ctx G)
    (hc : Compat D C) {x : G} (hx : x ∈ D.B) (hu : x ∈ C.P.U) :
    sigmaU C ⟨x, hu⟩ = ⟨x, hu⟩ := by
  apply Subtype.ext
  rw [sigmaU_apply_coe]
  have hcx : (C.s : G) * x = x * (C.s : G) := by
    have h2 := le_C_t1_of_mem_B D hx
    rw [Subgroup.mem_centralizer_singleton_iff] at h2
    rw [hc.s_eq]
    exact h2.symm
  rw [hcx, mul_assoc, mul_inv_cancel, mul_one]

/-- `C_U(sigmaU C) ≃* D.B` for `D.n = 2`; the map preserves the underlying element of `G`. -/
noncomputable def hatEquiv (D : Work.GW2.BGData G) (C : Work.BG.Sec2Ctx G)
    (hc : Compat D C) (hn : D.n = 2) :
    ↥(fixedSubgroup (sigmaU C)) ≃* ↥D.B where
  toFun u := ⟨(u : ↥C.P.U), hatInjBIdent C hc hn u.1 u.2⟩
  invFun b :=
    let hu : (b : G) ∈ C.P.U := by rw [hc.U_eq]; exact mem_DU_of_mem_B D b.2
    ⟨⟨(b : G), hu⟩, sigmaU_eq_self_of_mem_B D C hc b.2 hu⟩
  left_inv u := Subtype.ext (Subtype.ext rfl)
  right_inv b := Subtype.ext rfl
  map_mul' u v := Subtype.ext rfl

@[simp] theorem hatEquiv_coe (D : Work.GW2.BGData G) (C : Work.BG.Sec2Ctx G)
    (hc : Compat D C) (hn : D.n = 2) (u : ↥(fixedSubgroup (sigmaU C))) :
    ((hatEquiv D C hc hn u : ↥D.B) : G) = ((u : ↥C.P.U) : G) := rfl

@[simp] theorem hatEquiv_symm_coe (D : Work.GW2.BGData G) (C : Work.BG.Sec2Ctx G)
    (hc : Compat D C) (hn : D.n = 2) (b : ↥D.B) :
    ((((hatEquiv D C hc hn).symm b : ↥(fixedSubgroup (sigmaU C))) : ↥C.P.U) : G) = (b : G) := rfl

/-! ## Existence half of `HatProp` -/

/-- **HAT, existence**: for `ν ∈ 𝒮₄(C)` there is `θ ∈ Irr(B)` congruent to `ν` mod `2` on `B`.

Route: `ν|_U ∈ Irr(U)` is `sigmaU`-invariant; Bender–Glauberman Lemma 1.9 (via
`Work.BG.glauberman_two` + `Work.BG.glaubMultCongruence`) gives `β ∈ Irr(C_U(sigmaU))`
congruent to `ν|_U`, and `hatEquiv` transports `β` to `D.B`. -/
theorem HatExists (D : Work.GW2.BGData G) (C : Work.BG.Sec2Ctx G)
    (hc : Compat D C) (hn : D.n = 2) (ν : ClassFunction ↥C.P.H0 ℂ)
    (hν : ν ∈ S4Index C) : ∃ θ, HatOf D C ν θ := by
  classical
  have : Fintype ↥C.P.U := Fintype.ofFinite _
  have : Fintype ↥(fixedSubgroup (sigmaU C)) := Fintype.ofFinite _
  have hαirr : IsIrreducibleCharacter (restrictU C ν) := hatInjRestrictIrr C hc hn hν
  have hαinv : ∀ u : ↥C.P.U, restrictU C ν (sigmaU C u) = restrictU C ν u :=
    hatInjRestrictSigma C hc hn hν
  have hUodd : Odd (Nat.card ↥C.P.U) := odd_card_U_of_compat hc
  obtain ⟨β, hβ, huniq⟩ := glauberman_two hUodd (sigmaU C) (sigmaU_mul_self C)
    (⟨restrictU C ν, hαirr⟩ : IrreducibleCharacter ↥C.P.U) hαinv
  have hcong : ∀ c : ↥(fixedSubgroup (sigmaU C)),
      AlgIntModTwo (restrictU C ν (c : ↥C.P.U))
        ((β : ClassFunction ↥(fixedSubgroup (sigmaU C)) ℂ) c) :=
    glaubMultCongruence (fixedSubgroup (sigmaU C)) (restrictU C ν) hαirr β
      (fun θ => ⟨fun h => huniq θ h, fun h => h ▸ hβ⟩)
  let e : ↥(fixedSubgroup (sigmaU C)) ≃* ↥D.B := hatEquiv D C hc hn
  let θ : ClassFunction ↥D.B ℂ :=
    ClassFunction.compHom e.symm.toMonoidHom (β : ClassFunction ↥(fixedSubgroup (sigmaU C)) ℂ)
  refine ⟨θ, ?_, ?_⟩
  · exact IsIrreducibleCharacter.compHom_of_surjective e.symm.surjective β.isIrreducible
  · intro h hb
    let u : ↥C.P.U := ⟨(h : G), by rw [hc.U_eq]; exact mem_DU_of_mem_B D hb⟩
    have hu_fixed : sigmaU C u = u := sigmaU_eq_self_of_mem_B D C hc hb u.2
    have hsymm : e.symm ⟨h, hb⟩ = ⟨u, hu_fixed⟩ := by
      apply Subtype.ext
      apply Subtype.ext
      rw [hatEquiv_symm_coe]
    have hth : θ ⟨h, hb⟩ = (β : ClassFunction ↥(fixedSubgroup (sigmaU C)) ℂ) ⟨u, hu_fixed⟩ := by
      show (β : ClassFunction ↥(fixedSubgroup (sigmaU C)) ℂ) (e.symm ⟨h, hb⟩) = _
      rw [hsymm]
    have hnu : restrictU C ν u = ν h := by
      rw [restrictU_apply]
    rw [hth, ← hnu]
    exact hcong ⟨u, hu_fixed⟩

open OddOrder.RepresentationTheory Work.GW2 Work.BG Work.GW2.C16 Work.GW2.C23 in
theorem Hat {G : Type} [Group G] [Finite G] (D : Work.GW2.BGData G)
    (C : Work.BG.Sec2Ctx G) : Work.GW2.C23.HatProp D C := by
  intro hc hn ν hν
  exact ⟨HatExists D C hc hn ν hν, HatUniq D C hc ν⟩

end Work.BG
