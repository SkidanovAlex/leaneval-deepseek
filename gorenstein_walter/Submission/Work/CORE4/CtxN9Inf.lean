/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gorenstein–Walter formalisation team (area CORE4, `Work.CORE4`)

# Bender 1981, §4 (8) case 2, at the `Case2Ctx` level: `N_U(A) ≤ (U ⊓ M) ⊔ F(U)`

Bender 1981, p. 226 (case 2 of the trichotomy on `Q := Ω₁(Z₂(O_p(U)))`): for an odd prime `p`,
`P ≤ F` of order `p` and the `(p,p)`-subgroup `A` of `F × K₁` containing `P`, if `A ≤ Q`,
`Z(Q) < A < Q` and `|Q : A| = p`, then

    N_U(A) = N_U(P) Q = B K F(U) ,

in particular `N_U(A) ≤ (U ⊓ M) ⊔ F(U)` — the inclusion proved here (`Case2EightN9Inf` of
`Submission.Work.CORE4.Case2EightN9Inf`, at the `Case2Ctx` level rather than the `Case2Ctx6` one).

The two inputs are

* `Work.CORE4.QsubCase2Facts`: the elementary facts about `Q` in case 2 (`|Q| = p ^ 3`,
  `|Z(Q)| = p`, `Q ≤ F(U)`, `U ≤ N_G(Q)`, `⁅Q, A⁆ ≤ Z(Q)`), and
* `Work.CORE4.ConjPowOrbit`, the group-theoretic core of `N_U(A) = N_U(P)Q`: conjugation by the
  powers of an element `q ∈ Q` that does not centralise `A` moves every subgroup of `A` of order
  `p` other than `Z(Q)` onto every other one.

The proof of the inclusion: let `x ∈ U` normalise `A` and put `P^x = P^x`.  Since `P _ x ≤ A` has
order `p`, and `P = A ∩ F` is the only subgroup of `A` of order `p` lying in `F` (`N_G(P) = M`),
either `P^x = P`, in which case `x ∈ N_G(P) = M` and `x ∈ U ⊓ M` is immediate, or `P^x ≠ P`, in
which case `P^x ≠ Z(Q)` (else `A = P ⊔ Z(Q)` would give `A = A^x = Z(Q)`) and some power `q ^ i`
of a suitable `q ∈ Q` conjugates `P^x` back to `P`; then `q ^ i * x ∈ N_G(P) = M`, so
`x = (q ^ i)⁻¹ (q ^ i x) ∈ Q (U ⊓ M) ≤ (U ⊓ M) ⊔ Q ≤ (U ⊓ M) ⊔ F(U)`.
-/
import Mathlib
import Submission.Work.CORE4.Defs
import Submission.Work.CORE4.API
import Submission.Work.CORE4.EightIdxDefs
import Submission.Work.CORE4.Case2EightObjExists
import Submission.Work.CORE4.SixThree
import Submission.Work.CORE4.Case2EightA_le_FsupK0
import Submission.Work.CORE4.Case2SixThreeRaw
import Submission.Work.CORE4.Case2Eight
import Submission.Work.CORE4.Case2Numeric
import Submission.Work.CORE4.Case2CountSetup
import Submission.Work.CORE4.Case2Count11
import Submission.Work.CORE4.Case2EightQfacts
import Submission.Work.CORE4.EightAnormalPcore_of_Qpos
import Submission.Work.CORE4.CtxN9InfAux.QsubCase2Facts
import Submission.Work.CORE4.CtxN9InfAux.ConjPowOrbit

namespace Work.CORE4

open Work.GW2 Subgroup

open Work.CORE4.CtxN9InfAux

variable {G : Type} [Group G] [Finite G]

/-- `Ω₁(P) ≤ P`. -/
private theorem omega1_le_self_inf (p : ℕ) (H : Subgroup G) : omega1 p H ≤ H := by
  rw [omega1]
  exact (Subgroup.closure_le H).mpr (fun x hx => hx.1)

/-- `Z₂(P) ≤ P`. -/
private theorem z2_le_self_inf (H : Subgroup G) : z2 H ≤ H := by
  rw [z2]
  exact (Subgroup.closure_le H).mpr (fun x hx => hx.1)

/-- `Q = Ω₁(Z₂(O_p(U))) ≤ F(U)`. -/
private theorem Qsub_le_fittingIn {p : ℕ} (hp : p.Prime) (B : Work.GW2.BenderSetup G) :
    Qsub p B ≤ Work.GW2.fittingIn B.U := by
  rw [Qsub]
  exact le_trans (omega1_le_self_inf p _)
    (le_trans (z2_le_self_inf _) (pCoreIn_le_fittingIn B.U hp))

/-- `Z(Q)` is fixed by anything normalising `Q`. -/
private theorem conjSub_centerIn_self {Q : Subgroup G} {x : G}
    (hx : x ∈ Subgroup.normalizer (Q : Set G)) :
    conjSub x (centerIn Q) = centerIn Q := by
  have hmem : ∀ y : G, y ∈ Q ↔ x * y * x⁻¹ ∈ Q := fun y =>
    Subgroup.mem_normalizer_iff.mp hx y
  have hmem' : ∀ y : G, y ∈ Q ↔ x⁻¹ * y * x ∈ Q := by
    intro y
    simpa using Subgroup.mem_normalizer_iff.mp
      ((Subgroup.normalizer (Q : Set G)).inv_mem hx) y
  have key : ∀ z w : G, z ∈ centerIn Q → w ∈ Q → x * z * x⁻¹ * w = w * (x * z * x⁻¹) := by
    intro z w hz hw
    obtain ⟨_, hzc⟩ := mem_centerIn_iff.mp hz
    have hwx : x⁻¹ * w * x ∈ Q := (hmem (x⁻¹ * w * x)).mpr (by
      show x * (x⁻¹ * w * x) * x⁻¹ ∈ Q
      rw [show x * (x⁻¹ * w * x) * x⁻¹ = w by group]
      exact hw)
    have h1 : z * (x⁻¹ * w * x) = (x⁻¹ * w * x) * z := hzc _ hwx
    calc x * z * x⁻¹ * w = x * (z * (x⁻¹ * w * x)) * x⁻¹ := by group
      _ = x * ((x⁻¹ * w * x) * z) * x⁻¹ := by rw [h1]
      _ = w * (x * z * x⁻¹) := by group
  apply le_antisymm
  · rintro y ⟨z, hz, rfl⟩
    rw [mem_centerIn_iff]
    exact ⟨(hmem z).mp (mem_centerIn_iff.mp hz).1, fun w hw => key z w hz hw⟩
  · intro y hy
    have hyQ : y ∈ Q := (mem_centerIn_iff.mp hy).1
    have hyc : ∀ w ∈ Q, y * w = w * y := (mem_centerIn_iff.mp hy).2
    refine Subgroup.mem_map.mpr ⟨x⁻¹ * y * x, ?_, ?_⟩
    · rw [mem_centerIn_iff]
      refine ⟨(hmem' y).mp hyQ, fun w hw => ?_⟩
      have hwx : x * w * x⁻¹ ∈ Q := (hmem w).mp hw
      have h1 : y * (x * w * x⁻¹) = (x * w * x⁻¹) * y := hyc _ hwx
      calc x⁻¹ * y * x * w = x⁻¹ * (y * (x * w * x⁻¹)) * x := by group
        _ = x⁻¹ * ((x * w * x⁻¹) * y) * x := by rw [h1]
        _ = w * (x⁻¹ * y * x) := by group
    · show x * (x⁻¹ * y * x) * x⁻¹ = y
      group

/-- **Bender 1981, §4 (8) case 2 (p. 226): `N_U(A) ≤ (U ⊓ M) ⊔ Q`**, the core of the case-2
half of `N_U(A) = N_U(P) Q = B K F(U)`.  The proof is reproduced in the module header. -/
private theorem nu_le_inf_sup_Q (I : Work.GW2.C4Inputs) (hbc : Work.GW2.BenderCtx G)
    (B : Work.GW2.BenderSetup G) (h : Work.GW2.Case2Ctx B)
    (p : ℕ) (P A : Subgroup G) (hp : p.Prime) (hPF : P ≤ h.D.F) (hPcard : Nat.card P = p)
    (hObj : Work.GW2.Case2EightObj h.D p P A)
    (hAQ : A ≤ Qsub p B) (hZA : centerIn (Qsub p B) < A)
    (hAQlt : A < Qsub p B) (hIdx : A.relIndex (Qsub p B) = p) :
    B.U ⊓ Subgroup.normalizer (A : Set G) ≤ (B.U ⊓ h.D.M) ⊔ Qsub p B := by
  have hAcard : Nat.card ↥A = p ^ 2 := hObj.2.2.2.2.1
  have hAexp : ∀ x ∈ A, x ^ p = 1 := hObj.2.2.2.2.2.1
  have hPA : P ≤ A := hObj.2.2.2.2.2.2.1
  have hAle : A ≤ h.D.F ⊔ h.D.K := hObj.2.2.2.1
  have hAcomm : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x :=
    Case2Eight_A_comm I B (Case2Ctx.toCtx6 h) A hAle
  obtain ⟨-, hZcard, hZle, hQleF, hUleNQ, -, hcomm⟩ :=
    QsubCase2Facts I G hbc B h p P A hp hPF hPcard hObj hAQ hZA hAQlt hIdx
  have hFUleU : Work.GW2.fittingIn B.U ≤ B.U := Subgroup.map_subtype_le _
  have hPne : P ≠ ⊥ := by
    intro hbot
    rw [hbot, Subgroup.card_bot] at hPcard
    have hp2 : 2 ≤ p := hp.two_le
    omega
  have hNP : Subgroup.normalizer (P : Set G) = h.D.M :=
    normalizerP_of_ctx6 B (Case2Ctx.toCtx6 h) P hPF hPne
  intro x hx
  obtain ⟨hxU, hxN⟩ := Subgroup.mem_inf.mp hx
  have hAx : conjSub x A = A := Subgroup.mem_normalizer_iff_map_conj_eq.mp hxN
  have hxNQ : x ∈ Subgroup.normalizer (Qsub p B : Set G) := hUleNQ hxU
  have hZfix : conjSub x (centerIn (Qsub p B)) = centerIn (Qsub p B) :=
    conjSub_centerIn_self hxNQ
  have hPxA : conjSub x P ≤ A := by rw [← hAx]; exact Subgroup.map_mono hPA
  have hPxcard : Nat.card ↥(conjSub x P) = p := by
    rw [conjSub, Subgroup.card_map_of_injective (MulAut.conj x).injective, hPcard]
  by_cases hPZ : P = centerIn (Qsub p B)
  · have hPfix : conjSub x P = P := by rw [hPZ, hZfix]
    have hxNP : x ∈ Subgroup.normalizer (P : Set G) :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mpr hPfix
    rw [hNP] at hxNP
    exact Subgroup.mem_sup_left (Subgroup.mem_inf.mpr ⟨hxU, hxNP⟩)
  · by_cases hPfix : conjSub x P = P
    · have hxNP : x ∈ Subgroup.normalizer (P : Set G) :=
        Subgroup.mem_normalizer_iff_map_conj_eq.mpr hPfix
      rw [hNP] at hxNP
      exact Subgroup.mem_sup_left (Subgroup.mem_inf.mpr ⟨hxU, hxNP⟩)
    · -- ## the hard case: `P ≠ Z(Q)` and `P^x ≠ P`
      have hdisj : P ⊓ centerIn (Qsub p B) = ⊥ := by
        rw [eq_bot_iff]
        intro y hy
        obtain ⟨hyP, -⟩ := Subgroup.mem_inf.mp hy
        by_contra hyne
        have hcardP : Nat.card ↥(P ⊓ centerIn (Qsub p B)) = p := by
          have hdvd : Nat.card ↥(P ⊓ centerIn (Qsub p B)) ∣ p := by
            rw [← hPcard]; exact Subgroup.card_dvd_of_le inf_le_left
          rcases (Nat.dvd_prime hp).mp hdvd with h1 | h2
          · exact absurd h1 (fun h1' =>
              hyne (Subgroup.mem_bot.mp (Subgroup.card_eq_one.mp h1' ▸ hy)))
          · exact h2
        have hPleZ : P ≤ centerIn (Qsub p B) := by
          have heq : P ⊓ centerIn (Qsub p B) = P :=
            Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [hcardP, hPcard])
          exact heq ▸ inf_le_right
        exact hPZ (Subgroup.eq_of_le_of_card_ge hPleZ (by rw [hZcard, hPcard]))
      have hPleNZ : P ≤ Subgroup.normalizer (centerIn (Qsub p B) : Set G) := by
        intro q hq
        have hqQ : q ∈ Qsub p B := hAQ (hPA hq)
        have hqU : q ∈ B.U := hFUleU (hQleF hqQ)
        exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr (conjSub_centerIn_self (hUleNQ hqU))
      have hAeq : A = P ⊔ centerIn (Qsub p B) := by
        have hcard : Nat.card ↥(P ⊔ centerIn (Qsub p B)) = p ^ 2 := by
          rw [card_sup_of_disjoint_normalizer hdisj hPleNZ, hPcard, hZcard]
          ring
        exact (Subgroup.eq_of_le_of_card_ge (sup_le hPA hZle)
          (by rw [hAcard, hcard])).symm
      have hPxneZ : conjSub x P ≠ centerIn (Qsub p B) := by
        intro hcon
        have hmap : conjSub x A
            = conjSub x P ⊔ conjSub x (centerIn (Qsub p B)) := by
          rw [hAeq, conjSub, conjSub, conjSub, Subgroup.map_sup]
        have hconjA : conjSub x A = conjSub x P ⊔ centerIn (Qsub p B) := by
          rw [hmap, hZfix]
        have hAZ : A = centerIn (Qsub p B) :=
          hAx.symm.trans (hconjA.trans (by rw [hcon, sup_idem]))
        have hcard : Nat.card ↥A = p := by rw [hAZ, hZcard]
        rw [hAcard] at hcard
        have hp2 : 2 ≤ p := hp.two_le
        nlinarith
      -- ## pick `q ∈ Q` with `[q, A] ≠ 1`
      obtain ⟨a, haA, haZ⟩ : ∃ a ∈ A, a ∉ centerIn (Qsub p B) := by
        by_contra hc
        push_neg at hc
        exact (ne_of_lt hZA) (le_antisymm hZle (fun a ha => hc a ha))
      have haQ : a ∈ Qsub p B := hAQ haA
      have hnotcen : (⟨a, haQ⟩ : ↥(Qsub p B)) ∉ Subgroup.center ↥(Qsub p B) := by
        intro hcen
        exact haZ (Subgroup.mem_map.mpr ⟨⟨a, haQ⟩, hcen, rfl⟩)
      have hex : ∃ y : ↥(Qsub p B),
          (⟨a, haQ⟩ : ↥(Qsub p B)) * y ≠ y * ⟨a, haQ⟩ := by
        by_contra hc
        push_neg at hc
        exact hnotcen ((Subgroup.mem_center_iff (G := ↥(Qsub p B))).mpr
          (fun g => (hc g).symm))
      obtain ⟨y, hy⟩ := hex
      have hqQ : (y : G) ∈ Qsub p B := y.2
      have hqane : (y : G) * a * (y : G)⁻¹ * a⁻¹ ≠ 1 := by
        intro h1
        apply hy
        have hconj : (y : G) * a * (y : G)⁻¹ = a := by
          have h2 := congrArg (fun t => t * a) h1
          simpa [mul_assoc] using h2
        refine Subtype.ext ?_
        show a * (y : G) = (y : G) * a
        calc a * (y : G) = ((y : G) * a * (y : G)⁻¹) * (y : G) := by rw [hconj]
          _ = (y : G) * a := by group
      have hcommq : ∀ b ∈ A, (y : G) * b * (y : G)⁻¹ * b⁻¹ ∈ centerIn (Qsub p B) :=
        fun b hb => hcomm b hb (y : G) hqQ
      obtain ⟨i, hi⟩ := ConjPowOrbit p hp (Qsub p B) A (y : G) hqQ (le_of_lt hAQlt)
        hAcard hAexp hAcomm hZcard hZle hcommq ⟨a, haA, hqane⟩ (conjSub x P) P hPxA hPA
        hPxcard hPcard hPxneZ hPZ
      have hmem : (y : G) ^ i * x ∈ Subgroup.normalizer (P : Set G) := by
        rw [Subgroup.mem_normalizer_iff_map_conj_eq]
        exact (conjSub_mul' ((y : G) ^ i) x P).symm.trans hi
      rw [hNP] at hmem
      have hqiQ : (y : G) ^ i ∈ Qsub p B := (Qsub p B).pow_mem hqQ i
      have hqiU : (y : G) ^ i ∈ B.U := hFUleU (hQleF hqiQ)
      have hmid : (y : G) ^ i * x ∈ B.U ⊓ h.D.M :=
        Subgroup.mem_inf.mpr ⟨B.U.mul_mem hqiU hxU, hmem⟩
      have hxsplit : x = ((y : G) ^ i)⁻¹ * ((y : G) ^ i * x) := by group
      rw [hxsplit]
      have h1 : ((y : G) ^ i)⁻¹ ∈ (B.U ⊓ h.D.M) ⊔ Qsub p B :=
        Subgroup.mem_sup_right ((Qsub p B).inv_mem hqiQ)
      have h2 : (y : G) ^ i * x ∈ (B.U ⊓ h.D.M) ⊔ Qsub p B :=
        Subgroup.mem_sup_left hmid
      exact mul_mem h1 h2

theorem CtxN9Inf (I : Work.GW2.C4Inputs) :
    ∀ (G : Type) [Group G] [Finite G], Work.GW2.BenderCtx G →
      ∀ (B : Work.GW2.BenderSetup G) (h : Work.GW2.Case2Ctx B),
        ∀ (p : ℕ) (P A : Subgroup G), p.Prime → P ≤ h.D.F → Nat.card P = p →
          Work.GW2.Case2EightObj h.D p P A →
          A ≤ Work.CORE4.Qsub p B → Work.CORE4.centerIn (Work.CORE4.Qsub p B) < A →
            A < Work.CORE4.Qsub p B → A.relIndex (Work.CORE4.Qsub p B) = p →
            B.U ⊓ Subgroup.normalizer (A : Set G) ≤
              (B.U ⊓ h.D.M) ⊔ Work.GW2.fittingIn B.U := by
  intro G _ _ hbc B h p P A hp hPF hPcard hObj hAQ hZA hAQlt hIdx
  refine (nu_le_inf_sup_Q I hbc B h p P A hp hPF hPcard hObj hAQ hZA hAQlt hIdx).trans ?_
  exact sup_le_sup_left (Qsub_le_fittingIn hp B) _

end Work.CORE4
