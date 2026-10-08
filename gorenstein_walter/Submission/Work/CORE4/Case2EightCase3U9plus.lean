/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gorenstein–Walter formalisation team (area CORE4, `Work.CORE4`)

# AREA CORE4 — Bender §4 (8), case 3, with the extra hypothesis `C_U(Q) ⊆ I_U(s)`

The statement proved here is the repaired case-3 leaf of Bender 1981, p. 226 (see
`Submission/Work/CORE4/Case2EightCase3U9.lean` for the prover's verdict on the
under-hypothesised version and `EightExCase3.lean` for the sibling analysis):

    `¬ IsCyclic (Qsub p B)` →  `s` inverts `Qsub p B`  →  `s` inverts `C_U(Qsub p B)`
      ⟹  `U = (U ⊓ M) · F(U)`.

## The argument

Write `Q := Qsub p B = Ω₁(Z₂(O_p(U))) ≤ U` and `I := C_U(Q) = U ⊓ C_G(Q)`.

* `Q ⊴ U` (`O_p(U) ⊴ U`, `Z₂` and `Ω₁` are given by commutator/power conditions, hence
  invariant under conjugation by `U`), so `Z₂` and `Ω₁` closures are normal in `U`.  This is
  `u9_Qsub_le_U`/`u9_Qsub_normal_in_U` below, and it is the only group-theoretic input needed
  from the definitions of §4 (8).
* Bender 1.5 (the `invSet`/`centralizer` decomposition, `A4aAux.exists_centralizer_mul_of_odd`):
  `U = C_U(s) · I_U(s)` for the involution `s`.
* `I_U(s) ⊆ C_U(Q)` — `Work.CORE4.invSet_commute_of_inverts`, using `Q ⊴ U` and odd `|U|`.
* The extra hypothesis `∀ x ∈ C_U(Q), s x s⁻¹ = x⁻¹` gives `C_U(Q) ⊆ I_U(s)`, so
  `I_U(s) = C_U(Q)` is the carrier of a subgroup of `G`.
* Coprime 15 (`I.toolkit.c15`), applied to the subgroup `I := C_U(Q)` whose carrier is
  `I_U(s)`, then yields `I ≤ F(U)`.
* `C_U(s) = B₀ ≤ U ⊓ M` by §4 (1)–(5) (`Case2Pre.B0_eq`) together with §4 (1)–(2)
  (`Case2PrePlus`), whence `U = C_U(s) · I_U(s) ≤ (U ⊓ M) · F(U)` and the reverse inclusion
  `(U ⊓ M) ⊔ F(U) ≤ U` is trivial.

The hypotheses `p.Prime`, `P ≤ F`, `|P| = p`, `Case2EightObj`, `¬ IsCyclic (Qsub p B)` and
`Case2SevenFacts` are not needed for this conclusion (the non-cyclicity is used elsewhere, to
produce the hypothesis that `s` inverts `C_U(Q)`); they are kept so that the leaf has exactly
the requested shape.
-/
import Mathlib
import Submission.Work.CORE4.EightExCase3
import Submission.Work.CORE4.A4aAux.U_eq_F_sup_invSet

open scoped commutatorElement

namespace Work.CORE4

open Work.GW2 Subgroup

/-! ## Auxiliary group theory -/

/-- If `A ⊴ ↥H`, then `H` normalizes the image of `A` under `H.subtype`. -/
theorem u9_le_normalizer_map_subtype_of_normal {G : Type} [Group G] {H : Subgroup G}
    {A : Subgroup ↥H} (hA : A.Normal) :
    H ≤ Subgroup.normalizer ((A.map H.subtype : Subgroup G) : Set G) := by
  rw [Subgroup.le_normalizer_iff]
  intro h hh x hx
  obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
  exact Subgroup.mem_map.mpr ⟨⟨h, hh⟩ * y * ⟨h, hh⟩⁻¹, hA.conj_mem y hy ⟨h, hh⟩, rfl⟩

/-- If `U` normalizes `P`, then conjugation by an element of `U` preserves the second-centre
set `z2Set P = {x ∈ P | [[x,y],z] = 1 for all y, z ∈ P}`. -/
theorem u9_conj_mem_z2Set {G : Type} [Group G] {P U : Subgroup G}
    (hUP : U ≤ Subgroup.normalizer (P : Set G)) {u : G} (hu : u ∈ U) {y : G}
    (hy : y ∈ z2Set P) : u * y * u⁻¹ ∈ z2Set P := by
  refine ⟨(Subgroup.le_normalizer_iff.mp hUP u hu) y hy.1, ?_⟩
  intro a ha b hb
  have ha' : u⁻¹ * a * u ∈ P := by
    have h := (Subgroup.le_normalizer_iff.mp hUP u⁻¹ (U.inv_mem hu)) a ha
    simpa using h
  have hb' : u⁻¹ * b * u ∈ P := by
    have h := (Subgroup.le_normalizer_iff.mp hUP u⁻¹ (U.inv_mem hu)) b hb
    simpa using h
  -- conjugation is a homomorphism for the commutator
  have hcomm : ∀ g h : G, ⁅u * g * u⁻¹, u * h * u⁻¹⁆ = u * ⁅g, h⁆ * u⁻¹ := by
    intro g h
    have hmain : (MulAut.conj u) ⁅g, h⁆ = ⁅(MulAut.conj u) g, (MulAut.conj u) h⁆ :=
      map_commutatorElement (MulAut.conj u).toMonoidHom g h
    rw [MulAut.conj_apply u g, MulAut.conj_apply u h, MulAut.conj_apply u ⁅g, h⁆] at hmain
    exact hmain.symm
  have hA : a = u * (u⁻¹ * a * u) * u⁻¹ := by group
  have hB : b = u * (u⁻¹ * b * u) * u⁻¹ := by group
  rw [hA, hB, hcomm y (u⁻¹ * a * u), hcomm ⁅y, u⁻¹ * a * u⁆ (u⁻¹ * b * u),
    hy.2 (u⁻¹ * a * u) ha' (u⁻¹ * b * u) hb']
  group

/-- `Z₂` is invariant under conjugation by any subgroup normalizing `P`. -/
theorem u9_le_normalizer_z2 {G : Type} [Group G] {P U : Subgroup G}
    (hUP : U ≤ Subgroup.normalizer (P : Set G)) :
    U ≤ Subgroup.normalizer ((z2 P : Subgroup G) : Set G) := by
  rw [Subgroup.le_normalizer_iff]
  intro u hu x hx
  rw [z2] at hx ⊢
  exact Subgroup.closure_induction (p := fun z _ => u * z * u⁻¹ ∈ Subgroup.closure (z2Set P))
    (fun y hy => Subgroup.subset_closure (u9_conj_mem_z2Set hUP hu hy))
    (by rw [mul_one, mul_inv_cancel]; exact Subgroup.one_mem _)
    (fun x y _ _ ihx ihy => by
      rw [show u * (x * y) * u⁻¹ = (u * x * u⁻¹) * (u * y * u⁻¹) by group]
      exact Subgroup.mul_mem _ ihx ihy)
    (fun x _ ihx => by
      rw [show u * x⁻¹ * u⁻¹ = (u * x * u⁻¹)⁻¹ by group]
      exact Subgroup.inv_mem _ ihx)
    hx

/-- `Ω₁` is invariant under conjugation by any subgroup normalizing `P`. -/
theorem u9_le_normalizer_omega1 {G : Type} [Group G] {K U : Subgroup G} (p : ℕ)
    (hUK : U ≤ Subgroup.normalizer (K : Set G)) :
    U ≤ Subgroup.normalizer ((omega1 p K : Subgroup G) : Set G) := by
  rw [Subgroup.le_normalizer_iff]
  intro u hu x hx
  rw [omega1] at hx ⊢
  exact Subgroup.closure_induction (p := fun z _ => u * z * u⁻¹ ∈ Subgroup.closure (omega1Set p K))
    (fun y hy => Subgroup.subset_closure ⟨(Subgroup.le_normalizer_iff.mp hUK u hu) y hy.1, by
      have hpow : (u * y * u⁻¹) ^ p = u * y ^ p * u⁻¹ := by
        rw [show u * y * u⁻¹ = (MulAut.conj u) y from (MulAut.conj_apply u y).symm,
          ← map_pow, MulAut.conj_apply]
      rw [hpow, hy.2, mul_one, mul_inv_cancel]⟩)
    (by rw [mul_one, mul_inv_cancel]; exact Subgroup.one_mem _)
    (fun x y _ _ ihx ihy => by
      rw [show u * (x * y) * u⁻¹ = (u * x * u⁻¹) * (u * y * u⁻¹) by group]
      exact Subgroup.mul_mem _ ihx ihy)
    (fun x _ ihx => by
      rw [show u * x⁻¹ * u⁻¹ = (u * x * u⁻¹)⁻¹ by group]
      exact Subgroup.inv_mem _ ihx)
    hx

/-- `Q := Qsub p B = Ω₁(Z₂(O_p(U)))` lies in `U`. -/
theorem u9_Qsub_le_U {G : Type} [Group G] [Finite G] (p : ℕ) (B : BenderSetup G) :
    Qsub p B ≤ B.U := by
  have hPleU : pCoreIn p B.U ≤ B.U := by
    rw [pCoreIn]
    exact Subgroup.map_subtype_le (pCore p ↥B.U)
  have hz2 : ∀ x ∈ z2 (pCoreIn p B.U), x ∈ pCoreIn p B.U := by
    intro x hx
    rw [z2] at hx
    exact Subgroup.closure_induction (fun y hy => hy.1) (Subgroup.one_mem _)
      (fun a b _ _ ha hb => Subgroup.mul_mem _ ha hb)
      (fun a _ ha => Subgroup.inv_mem _ ha) hx
  intro x hx
  rw [Qsub, omega1] at hx
  exact Subgroup.closure_induction (fun y hy => hPleU (hz2 y hy.1)) (Subgroup.one_mem _)
    (fun a b _ _ ha hb => Subgroup.mul_mem _ ha hb)
    (fun a _ ha => Subgroup.inv_mem _ ha) hx

/-- `Q := Qsub p B` is normal in `U`. -/
theorem u9_Qsub_normal_in_U {G : Type} [Group G] [Finite G] (p : ℕ) (B : BenderSetup G) :
    ((Qsub p B).subgroupOf B.U).Normal := by
  refine (Subgroup.normal_subgroupOf_iff_le_normalizer (u9_Qsub_le_U p B)).mpr ?_
  have hP : B.U ≤ Subgroup.normalizer ((pCoreIn p B.U : Subgroup G) : Set G) := by
    rw [pCoreIn]
    exact u9_le_normalizer_map_subtype_of_normal (pCore_normal p ↥B.U)
  have h1 : B.U ≤ Subgroup.normalizer ((z2 (pCoreIn p B.U) : Subgroup G) : Set G) :=
    u9_le_normalizer_z2 hP
  have h2 : B.U ≤
      Subgroup.normalizer ((omega1 p (z2 (pCoreIn p B.U)) : Subgroup G) : Set G) :=
    u9_le_normalizer_omega1 p h1
  rw [Qsub]
  exact h2

/-! ## The leaf -/

theorem Case2EightCase3U9plus (I : Work.GW2.C4Inputs) :
    ∀ (G : Type) [Group G] [Finite G], Work.GW2.BenderCtx G → ∀ B : Work.GW2.BenderSetup G,
      Work.GW2.Case2 B → ∀ C : Work.GW2.Case2Ctx6 B, Work.GW2.Case2PrePlus B C.D →
        Work.GW2.Case2SevenFacts B C.D →
        ∀ (p : ℕ) (P A : Subgroup G), p.Prime → P ≤ C.D.F → Nat.card P = p →
          Work.GW2.Case2EightObj C.D p P A →
          ¬ IsCyclic ↥(Work.CORE4.Qsub p B) →
          (∀ x ∈ Work.CORE4.Qsub p B, C.D.s * x * C.D.s⁻¹ = x⁻¹) →
          (∀ x ∈ B.U ⊓ Subgroup.centralizer ((Work.CORE4.Qsub p B : Subgroup G) : Set G),
              C.D.s * x * C.D.s⁻¹ = x⁻¹) →
          B.U = (B.U ⊓ C.D.M) ⊔ Work.GW2.fittingIn B.U := by
  intro G _ _ _hbc B _h2 C hplus _h7 p P A _hp _hPF _hPcard _hObj _hncyc hinvQ hA
  have hodd : Odd (Nat.card ↥B.U) := B.U_odd
  have hQleU : Work.CORE4.Qsub p B ≤ B.U := u9_Qsub_le_U p B
  have hQn : ((Work.CORE4.Qsub p B).subgroupOf B.U).Normal := u9_Qsub_normal_in_U p B
  -- `s` is an involution normalizing `U`
  have hss : C.D.s * C.D.s = 1 := by
    have h : C.D.s ^ 2 = 1 := by rw [← C.D.s_order]; exact pow_orderOf_eq_one C.D.s
    simpa [pow_two] using h
  have hsNU : C.D.s ∈ Subgroup.normalizer ((B.U : Subgroup G) : Set G) := by
    have hsH : C.D.s ∈ B.H := B.S_le_H C.D.s_mem_S
    have hUnorm : ∀ y ∈ B.U, ∀ k ∈ B.H, k * y * k⁻¹ ∈ B.U := fun y hy k hk =>
      (Subgroup.normal_subgroupOf_iff B.U_le_H).mp B.U_normal y k hy hk
    rw [Subgroup.mem_normalizer_iff]
    intro y
    refine ⟨fun hy => hUnorm y hy C.D.s hsH, fun hy => ?_⟩
    have h2 := hUnorm (C.D.s * y * C.D.s⁻¹) hy C.D.s⁻¹ (B.H.inv_mem hsH)
    have h3 : C.D.s⁻¹ * (C.D.s * y * C.D.s⁻¹) * (C.D.s⁻¹)⁻¹ = y := by group
    rwa [h3] at h2
  -- the extra hypothesis identifies `C_U(Q)` with `I_U(s)`
  have hIs : ((B.U ⊓ Subgroup.centralizer ((Work.CORE4.Qsub p B : Subgroup G) : Set G) :
      Subgroup G) : Set G) = Work.GW2.invSet B.U C.D.s := by
    ext x
    constructor
    · intro hx
      exact ⟨hx.1, hA x hx⟩
    · intro hx
      have hxU : x ∈ B.U := hx.1
      refine ⟨hxU, ?_⟩
      exact Subgroup.mem_centralizer_iff.mpr (fun y hy =>
        (Work.CORE4.invSet_commute_of_inverts hodd hQleU hQn hinvQ hxU hx y hy).symm)
  -- Coprime 15: an inversion set which is a subgroup lies in the Fitting subgroup
  have hc15 := I.toolkit.c15 G I.toolkit.ft B.U C.D.s C.D.s_order hodd hsNU
  have hIsfit : (B.U ⊓ Subgroup.centralizer ((Work.CORE4.Qsub p B : Subgroup G) : Set G))
      ≤ Work.GW2.fittingIn B.U := (hc15.2.2 _ hIs).2.2
  refine le_antisymm ?_ ?_
  · -- `U = C_U(s) · I_U(s) ≤ (U ⊓ M) · F(U)`
    intro u hu
    obtain ⟨c, hc, i, hi, hci⟩ :=
      Work.CORE4.A4aAux.exists_centralizer_mul_of_odd B.U hsNU hss hodd hu
    have hcM : c ∈ B.U ⊓ C.D.M := by
      have hcB0 : c ∈ C.D.B0 := by
        rw [Work.GW2.Case2Pre.B0_eq B C.D C.pre]
        exact hc
      rw [hplus.2.2] at hcB0
      exact hcB0.1
    have hiIs : i ∈ ((B.U ⊓ Subgroup.centralizer ((Work.CORE4.Qsub p B : Subgroup G) : Set G) :
        Subgroup G) : Set G) := by
      rw [hIs]
      exact hi
    rw [hci]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hcM) (Subgroup.mem_sup_right (hIsfit hiIs))
  · -- the reverse inclusion is trivial
    show (B.U ⊓ C.D.M) ⊔ ((Work.GW2.fitting ↥B.U).map B.U.subtype) ≤ B.U
    exact sup_le inf_le_left (Subgroup.map_subtype_le (Work.GW2.fitting ↥B.U))

end Work.CORE4
