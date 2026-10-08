import Mathlib
import Submission.Work.BG.Thm43Defs
import Submission.Work.BG.ThmABCDefs
import Submission.Work.BG.ThmABCCharDefs
import Submission.Work.BG.S02
import Submission.Work.BG.Hat
import Submission.Work.BG.hatInj
import Submission.Work.BG.hatInjCore
import Submission.Work.BG.hatInjCountAlt
import Submission.Work.BG.hatInjParity
import Submission.Work.BG.hatInjCongruentEq
import Submission.Work.BG.hatInjRestrictIrr
import Submission.Work.BG.hatInjRestrictSigma
import Submission.Work.BG.hatInjBIdent
import Submission.Work.BG.glauberman_two
import Submission.Work.BG.glaubMultCongruence
import Submission.Work.BG.thmCSmallAux
import Submission.Work.BG.B_normalizes_K
import Submission.Work.BG.ubkLift

namespace Work.BG

open OddOrder.RepresentationTheory Work.GW2 Work.BG Work.GW2.C16 Work.GW2.C23

/-- The shape of the auxiliary fact used below: every irreducible character `β` of the fixed
point subgroup `fixedSubgroup (sigmaU C) = C_U(s)` lifts to an `s`-invariant irreducible
character of `U = C.P.U` agreeing with `β` on `C_U(s)` (the semidirect decomposition
`U = C_U(s) K`, proved separately as `Work.BG.ubkLift`). -/
def LiftProp : Prop :=
  ∀ {G : Type} [Group G] [Finite G] (D : Work.GW2.BGData G) (C : Work.BG.Sec2Ctx G)
    (K1 K2 : Subgroup G),
    Work.GW2.C16.Compat D C → D.n = 2 → Work.GW2.C16.ThmCHyps D K1 K2 →
    ∀ β : ClassFunction ↥(Work.BG.fixedSubgroup (Work.BG.sigmaU C)) ℂ,
      IsIrreducibleCharacter β →
      ∃ α₁ : ClassFunction ↥C.P.U ℂ,
        IsIrreducibleCharacter α₁ ∧
        (∀ u : ↥C.P.U, α₁ (Work.BG.sigmaU C u) = α₁ u) ∧
        (∀ c : ↥(Work.BG.fixedSubgroup (Work.BG.sigmaU C)), α₁ (c : ↥C.P.U) = β c)

/-- **Main argument.**  Given the lift `LiftProp`, every `ν ∈ 𝒮₄(C)` and every `θ` with
`HatOf D C ν θ` satisfy `θ 1 = ν 1`.

Write `α := ν|_U ∈ Irr(U)` (irreducible and `s`-invariant, since `ν ∈ 𝒮₄(C)`), and let
`β ∈ Irr(C_U(s))` be its Glauberman correspondent (`glauberman_two`): the unique irreducible
of `C_U(s)` occurring with odd multiplicity in `α|_{C_U(s)}`, so that `α ≡ β` mod 2 on
`C_U(s)` (`glaubMultCongruence`).

Because `D.n = 2`, `ThmCHyps` gives `U = C_U(s)·K` with `K = K₁ ⊓ K₂` inverted by `s` and
`K ⊴ U`; hence `β` lifts to an `s`-invariant `α₁ ∈ Irr(U)` with `α₁|_{C_U(s)} = β`.
Then `α ≡ α₁` mod 2 on `C_U(s)`, so `α = α₁` by injectivity of the Glauberman correspondence
(`glauberman_injective`, with the count and column-parity inputs `hatInjCountAlt`,
`hatInjParity`).  In particular `α(1) = β(1)`.

Finally `θ`, transported back to `C_U(s)` along `hatEquiv`, is an irreducible of that group
congruent to `α` modulo 2, hence equals `β` (`hatInjCongruentEq`); and `ν 1 = α 1 = β 1`. -/
theorem ubkIrrAux (hlift : LiftProp) :
    ∀ {G : Type} [Group G] [Finite G] [Fintype G] [Invertible (Nat.card G : ℂ)]
      (D : Work.GW2.BGData G) (C : Work.BG.Sec2Ctx G) (K1 K2 : Subgroup G)
      [Invertible (Nat.card ↥C.P.H0 : ℂ)],
      Work.GW2.C16.Compat D C → D.n = 2 → Work.GW2.C16.ThmCHyps D K1 K2 →
        ∀ ν ∈ Work.GW2.C16.S4Index C, ∀ θ : ClassFunction ↥D.B ℂ,
          Work.GW2.C23.HatOf D C ν θ → θ 1 = ν 1 := by
  classical
  intro G _ _ _ _ D C K1 K2 _ hc hn hT ν hν θ hθ
  -- ## Instances and the basic pieces
  haveI : Fintype ↥C.P.U := Fintype.ofFinite _
  haveI : Fintype ↥(fixedSubgroup (sigmaU C)) := Fintype.ofFinite _
  haveI : Fintype ↥D.B := Fintype.ofFinite _
  haveI hInvU : Invertible (Nat.card ↥C.P.U : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  haveI hInvF : Invertible (Nat.card ↥(fixedSubgroup (sigmaU C)) : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  haveI hInvB : Invertible (Nat.card ↥D.B : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  -- `α := ν|_U ∈ Irr(U)` and `α` is `s`-invariant
  have hαirr : IsIrreducibleCharacter (restrictU C ν) := hatInjRestrictIrr C hc hn hν
  have hαinv : ∀ u : ↥C.P.U, restrictU C ν (sigmaU C u) = restrictU C ν u :=
    hatInjRestrictSigma C hc hn hν
  have hUodd : Odd (Nat.card ↥C.P.U) := odd_card_U_of_compat hc
  -- ## The Glauberman correspondent `β` of `α` on `C_U(s)`
  obtain ⟨β, hβ, huniq⟩ := glauberman_two hUodd (sigmaU C) (sigmaU_mul_self C)
    (⟨restrictU C ν, hαirr⟩ : IrreducibleCharacter ↥C.P.U) hαinv
  -- `α ≡ β` modulo `2` on `C_U(s)`
  have hcongβ : ∀ c : ↥(fixedSubgroup (sigmaU C)),
      AlgIntModTwo (restrictU C ν (c : ↥C.P.U))
        ((β : ClassFunction ↥(fixedSubgroup (sigmaU C)) ℂ) c) :=
    glaubMultCongruence (fixedSubgroup (sigmaU C)) (restrictU C ν) hαirr β
      (fun θ => ⟨fun h => huniq θ h, fun h => h ▸ hβ⟩)
  -- ## The lift `α₁`
  obtain ⟨α₁, hα₁irr, hα₁inv, hα₁B⟩ :=
    hlift D C K1 K2 hc hn hT (β : ClassFunction ↥(fixedSubgroup (sigmaU C)) ℂ) β.isIrreducible
  -- `α ≡ α₁` modulo `2` on `C_U(s)`
  have hcongαα₁ : ∀ c : ↥(fixedSubgroup (sigmaU C)),
      AlgIntModTwo (restrictU C ν (c : ↥C.P.U)) (α₁ (c : ↥C.P.U)) := by
    intro c
    rw [hα₁B c]
    exact hcongβ c
  -- ## Injectivity of the Glauberman correspondence gives `α = α₁`
  have hcount : Nat.card (SigmaInvIrr ↥C.P.U (sigmaU C))
      = Nat.card (IrreducibleCharacter ↥(fixedSubgroup (sigmaU C))) :=
    hatInjCountAlt hUodd (sigmaU C) (sigmaU_mul_self C)
  have hparity : ∀ β' : IrreducibleCharacter ↥(fixedSubgroup (sigmaU C)),
      Odd (Nat.card {α : SigmaInvIrr ↥C.P.U (sigmaU C) //
        OddMult (sigmaU C) (α : IrreducibleCharacter ↥C.P.U) β'}) :=
    fun β' => hatInjParity hUodd (sigmaU C) (sigmaU_mul_self C) β'
  have hαeq : restrictU C ν = α₁ :=
    glauberman_injective hUodd (sigmaU C) (sigmaU_mul_self C) hcount hparity
      hαirr hαinv hα₁irr hα₁inv hcongαα₁
  -- hence `ν 1 = α 1 = β 1`
  have hν1 : ν (1 : ↥C.P.H0) = (β : ClassFunction ↥(fixedSubgroup (sigmaU C)) ℂ) 1 := by
    have hstep1 : restrictU C ν (1 : ↥C.P.U) = ν (1 : ↥C.P.H0) := by
      rw [restrictU_apply]
      exact congrArg ν (Subtype.ext rfl)
    have hstep2 : α₁ (1 : ↥C.P.U)
        = α₁ ((1 : ↥(fixedSubgroup (sigmaU C))) : ↥C.P.U) := congrArg α₁ (Subtype.ext rfl)
    calc ν (1 : ↥C.P.H0) = restrictU C ν (1 : ↥C.P.U) := hstep1.symm
      _ = α₁ (1 : ↥C.P.U) := by rw [hαeq]
      _ = α₁ ((1 : ↥(fixedSubgroup (sigmaU C))) : ↥C.P.U) := hstep2
      _ = (β : ClassFunction ↥(fixedSubgroup (sigmaU C)) ℂ) 1 := hα₁B 1
  -- ## `θ` transported back to `C_U(s)` equals `β`
  let e : ↥(fixedSubgroup (sigmaU C)) ≃* ↥D.B := hatEquiv D C hc hn
  let β' : ClassFunction ↥D.B ℂ :=
    ClassFunction.compHom e.symm.toMonoidHom
      (β : ClassFunction ↥(fixedSubgroup (sigmaU C)) ℂ)
  have hβ'irr : IsIrreducibleCharacter β' :=
    IsIrreducibleCharacter.compHom_of_surjective e.symm.surjective β.isIrreducible
  have hBodd : Odd (Nat.card ↥D.B) := by
    have h1 : Nat.card ↥D.B = Nat.card ↥(fixedSubgroup (sigmaU C)) :=
      (Nat.card_congr (hatEquiv D C hc hn).toEquiv).symm
    rw [h1]
    exact Odd.of_dvd_nat hUodd (Subgroup.card_subgroup_dvd_card _)
  have hθβ' : θ = β' := by
    refine hatInjCongruentEq (K := ↥D.B) hBodd hθ.1 hβ'irr ?_
    intro b
    have hbU : (b : G) ∈ C.P.U := by rw [hc.U_eq]; exact b.2.1.1
    let h : ↥C.P.H0 := ⟨(b : G), C.P.U_le_H0 hbU⟩
    have hmem : (h : G) ∈ D.B := b.2
    have h1 : AlgIntModTwo (ν h) (θ ⟨h, hmem⟩) := hθ.2 h hmem
    have hb_eq : (⟨h, hmem⟩ : ↥D.B) = b := Subtype.ext rfl
    rw [hb_eq] at h1
    have h1' : AlgIntModTwo (restrictU C ν ⟨(b : G), hbU⟩) (θ b) := by
      have hνh : ν h = restrictU C ν ⟨(b : G), hbU⟩ := rfl
      rw [← hνh]
      exact h1
    have h2 : AlgIntModTwo (restrictU C ν ⟨(b : G), hbU⟩) ((β : ClassFunction ↥(fixedSubgroup (sigmaU C)) ℂ) (e.symm b)) := by
      have h3 := hcongβ (e.symm b)
      have hc_eq : (⟨(b : G), hbU⟩ : ↥C.P.U)
          = ((e.symm b : ↥(fixedSubgroup (sigmaU C))) : ↥C.P.U) := Subtype.ext rfl
      rw [hc_eq]
      exact h3
    have h3 : AlgIntModTwo (θ b) ((β : ClassFunction ↥(fixedSubgroup (sigmaU C)) ℂ) (e.symm b)) := h1'.symm.trans h2
    simpa [β'] using h3
  -- ## Degrees
  calc θ 1 = β' 1 := by rw [hθβ']
    _ = (β : ClassFunction ↥(fixedSubgroup (sigmaU C)) ℂ) (e.symm 1) := rfl
    _ = (β : ClassFunction ↥(fixedSubgroup (sigmaU C)) ℂ) 1 := by rw [map_one]
    _ = ν (1 : ↥C.P.H0) := hν1.symm

/-- Sanity check: `ubkIrrAux` applied to a proof of `LiftProp` has exactly the target
statement (`Work.BG.ubkLift` supplies the proof of `LiftProp`). -/
example (h : LiftProp) {G : Type} [Group G] [Finite G] [Fintype G]
    [Invertible (Nat.card G : ℂ)]
    (D : Work.GW2.BGData G) (C : Work.BG.Sec2Ctx G) (K1 K2 : Subgroup G)
    [Invertible (Nat.card ↥C.P.H0 : ℂ)] :
    Work.GW2.C16.Compat D C → D.n = 2 → Work.GW2.C16.ThmCHyps D K1 K2 →
      ∀ ν ∈ Work.GW2.C16.S4Index C, ∀ θ : ClassFunction ↥D.B ℂ,
        Work.GW2.C23.HatOf D C ν θ → θ 1 = ν 1 := ubkIrrAux (G := G) h D C K1 K2

open OddOrder.RepresentationTheory Work.GW2 Work.BG Work.GW2.C16 Work.GW2.C23 in
theorem ubkIrr {G : Type} [Group G] [Finite G] [Fintype G] [Invertible (Nat.card G : ℂ)]
    (D : Work.GW2.BGData G) (C : Work.BG.Sec2Ctx G) (K1 K2 : Subgroup G)
    [Invertible (Nat.card ↥C.P.H0 : ℂ)] :
    Work.GW2.C16.Compat D C → D.n = 2 → Work.GW2.C16.ThmCHyps D K1 K2 →
      ∀ ν ∈ Work.GW2.C16.S4Index C, ∀ θ : ClassFunction ↥D.B ℂ,
        Work.GW2.C23.HatOf D C ν θ → θ 1 = ν 1 := by
  intro hc hn hT ν hν θ hθ
  exact ubkIrrAux (G := G) Work.BG.ubkLift D C K1 K2 hc hn hT ν hν θ hθ

end Work.BG
