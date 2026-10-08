import Mathlib
import Submission.Work.CORE3.Case1aFrattiniApi
import Submission.Work.CORE3.Case1aPpart
import Submission.Work.CORE3.Case1aSetup

/-!
# CORE3 / A7V18: the `p`-part of `C_U(t₂)`

Deliverable: `Work.CORE3.A7V18.PpartT2`, the identity

`|C_U(t₂)|_p = |C_U(S)|_p`,

where `(B, D)` is the `Case1aData` of Bender 1981 §3 with `p = D.p`, `S = B.S` the dihedral
Sylow `2`-subgroup, `U = O(H)` and `t₂ ∈ S − S₀` inverts `O_p(U)` (`D.inv`).

Mathematically this is the `t₂`-analogue of `Work.CORE3.Case1aPpart` (which computes
`|C_U(t₁)|_p = |O_p(U)| · |C_U(S)|_p` for the reflection `t₁` centralizing `O_p(U)`).  The same
decomposition applies: since `S` acts trivially on `U/F(U)` (`hSAct`), one has
`U = F(U) · C_U(S)`, hence `C_U(t₂) = C_{F(U)}(t₂) · C_U(S)`; the counting identity
`|C_U(t₂)| · |C_{F(U)}(t₂) ⊓ C_U(S)| = |C_{F(U)}(t₂)| · |C_U(S)|` follows because `C_U(S)`
normalizes `C_{F(U)}(t₂)`.  The difference from `t₁` is the first factor: whereas
`|C_{F(U)}(t₁)|_p = |O_p(U)|` (because `t₁` centralizes the Sylow `p`-subgroup `O_p(U)` of the
nilpotent group `F(U)`), here `t₂` *inverts* `O_p(U)`, so `C_{F(U)}(t₂)` has order prime to `p`
(an element of `p`-power order in `F(U)` lies in `O_p(U)`, where inversion has no nontrivial
fixed point since `U`, hence `O_p(U)`, has odd order).  Thus the `p`-part of the first factor is
`1` and the `p`-parts of `|C_U(t₂)|` and `|C_U(S)|` agree.

This module is self-contained: the auxiliary lemmas it needs (`card_sup_mul_card_inf_of_le_normalizer`,
`pCoreIn_of_pow_eq_one_of_mem_fittingIn`, `inverts_inf_centralizer_eq_bot_of_odd`, the CORE3
"characteristic subgroup" API) are all imported.
-/

set_option linter.style.haveILetI false
set_option linter.dupNamespace false

namespace Work.CORE3.A7V18

open Work.GW2
open Subgroup
open scoped commutatorElement

theorem PpartT2 (G : Type) [Group G] [Finite G] (hFT : Work.GW2.FeitThompsonProp)
    (T : Work.GW2.LocalToolkit) (hBc : Work.GW2.BenderCtx G) (B : Work.GW2.BenderSetup G)
    (D : Work.GW2.Case1aData B) (hSAct : Work.CORE3.SActsTriviallyModFitting B) :
    (Nat.card ↥(B.U ⊓ Subgroup.centralizer ({D.t2} : Set G))).factorization D.p
      = (Nat.card ↥(B.U ⊓ Subgroup.centralizer ((B.S : Subgroup G) : Set G))).factorization D.p := by
  classical
  haveI hpFact : Fact D.p.Prime := ⟨D.hp⟩
  haveI htwo : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  -- ## Notation
  set S : Subgroup G := (B.S : Subgroup G) with hS
  set U : Subgroup G := B.U with hU
  set F : Subgroup G := fittingIn U with hF
  set P : Subgroup G := pCoreIn D.p U with hP
  set B0 : Subgroup G := U ⊓ centralizer (S : Set G) with hB0
  set C : Subgroup G := F ⊓ centralizer ({D.t2} : Set G) with hC
  set A : Subgroup G := U ⊓ centralizer ({D.t2} : Set G) with hA
  -- ## Basic facts
  have hF_le_U : F ≤ U := c1aFittingIn_le U
  -- `C_G(S) ≤ C_G(t₂)` since `t₂ ∈ S`
  have hCS_le_Ct2 : centralizer (S : Set G) ≤ centralizer ({D.t2} : Set G) :=
    Subgroup.centralizer_le (by
      intro y hy
      rw [Set.mem_singleton_iff] at hy
      subst hy
      exact D.t2_mem)
  -- `F ◁ U`
  have hU_le_NF : U ≤ Subgroup.normalizer (F : Set G) := by
    haveI hchar : (Work.GW2.fitting ↥U).Characteristic := c1aFitting_characteristic U
    have hN : (Work.GW2.fitting ↥U).Normal := by
      rw [Work.CORE2A.fitting_eq_isaacsFitting (G := ↥U)]
      exact OddOrder.Isaacs.Ch01.fitting.normal ↥U
    have h := c1aLe_normalizer_map_subtype (K := U) (N := Work.GW2.fitting ↥U) hN
    rw [hF]
    simpa [Work.GW2.fittingIn] using h
  have hF_norm : (F.subgroupOf U).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hF_le_U).mpr hU_le_NF
  -- ## Step 1: `[S,U] ≤ F(U)`
  have hcommS : (⁅S, U⁆ : Subgroup G) ≤ F := by
    rw [Subgroup.commutator_le]
    intro s hs u hu
    have hz : u⁻¹ * (s * u * s⁻¹) ∈ F := hSAct s hs u hu
    have heq : ⁅s, u⁆ = u * (u⁻¹ * (s * u * s⁻¹)) * u⁻¹ := by
      rw [commutatorElement_def]
      group
    rw [heq]
    exact (Subgroup.mem_normalizer_iff.mp (hU_le_NF hu)
      (u⁻¹ * (s * u * s⁻¹))).mp hz
  -- ## Step 2: the coprime-action decomposition `U = [S,U] · C_U(S)`
  have hU_decomp : U = (⁅S, U⁆ : Subgroup G) ⊔ B0 := by
    have hSp : IsPGroup 2 S := B.S.isPGroup'
    have hcp : Nat.Coprime 2 (Nat.card U) := Odd.coprime_two_left (Work.CORE2A.bSetup_U_odd B)
    have hnorm : S ≤ Subgroup.normalizer (U : Set G) :=
      fun x hx => Work.CORE2A.bender_s_mem_normalizer_U B hx
    exact ((T.c11i G 2 S U hSp hcp hnorm).2).symm
  have hF_sup_B0 : F ⊔ B0 = U := by
    refine le_antisymm ?_ ?_
    · exact sup_le (c1aFittingIn_le U) inf_le_left
    · rw [hU_decomp]
      exact sup_le_sup_right hcommS B0
  -- elementwise decomposition of `U` with respect to `(F, B0)`
  have hdecomp : ∀ x ∈ U, ∃ f ∈ F, ∃ b ∈ B0, f * b = x :=
    Work.CORE2A.exists_mul_of_mem_sup_of_normal hF_le_U inf_le_left hF_norm hF_sup_B0
  -- ## Step 3: `C_U(t₂) = C_{F(U)}(t₂) · C_U(S)`
  have hA_eq : A = C ⊔ B0 := by
    refine le_antisymm ?_ ?_
    · intro x hx
      obtain ⟨f, hf, b, hb, hfb⟩ := hdecomp x hx.1
      have hb1 : D.t2 * b = b * D.t2 := (Subgroup.mem_centralizer_iff.mp hb.2) D.t2 D.t2_mem
      have hx1 : D.t2 * x = x * D.t2 :=
        (Subgroup.mem_centralizer_iff.mp hx.2) D.t2 (by simp)
      have hf1 : D.t2 * f = f * D.t2 := by
        have h0 : D.t2 * (f * b) = (f * b) * D.t2 := by rw [hfb]; exact hx1
        have h2 : D.t2 * f * b = f * D.t2 * b := by
          calc D.t2 * f * b = D.t2 * (f * b) := by group
            _ = (f * b) * D.t2 := h0
            _ = f * (b * D.t2) := by group
            _ = f * (D.t2 * b) := by rw [← hb1]
            _ = f * D.t2 * b := by group
        exact mul_right_cancel h2
      have hfC : f ∈ C := ⟨hf, by
        change f ∈ Subgroup.centralizer ({D.t2} : Set G)
        rw [Subgroup.mem_centralizer_iff]
        intro y hy
        rw [Set.mem_singleton_iff] at hy
        subst hy
        exact hf1⟩
      rw [← hfb]
      exact Subgroup.mul_mem_sup hfC hb
    · refine sup_le ?_ ?_
      · intro x hx
        exact ⟨hF_le_U hx.1, hx.2⟩
      · refine le_inf inf_le_left ?_
        intro x hx
        exact hCS_le_Ct2 hx.2
  -- ## Step 4: `B₀` normalizes `C`, hence the cardinality identity
  have hB0_le_NC : B0 ≤ Subgroup.normalizer (C : Set G) := by
    have key : ∀ {T : Set G} {g x : G}, g ∈ Subgroup.centralizer T →
        x ∈ Subgroup.centralizer T → g * x * g⁻¹ ∈ Subgroup.centralizer T := by
      intro T g x hg hx
      rw [Subgroup.mem_centralizer_iff] at hg hx ⊢
      intro y hy
      have hyg : y * g = g * y := hg y hy
      have hyx : y * x = x * y := hx y hy
      have hygi : y * g⁻¹ = g⁻¹ * y := by
        have h := congrArg (fun z => g⁻¹ * z * g⁻¹) hyg
        simpa [mul_assoc] using h.symm
      calc y * (g * x * g⁻¹) = (y * g) * x * g⁻¹ := by group
        _ = (g * y) * x * g⁻¹ := by rw [hyg]
        _ = g * (y * x) * g⁻¹ := by group
        _ = g * (x * y) * g⁻¹ := by rw [hyx]
        _ = g * x * (y * g⁻¹) := by group
        _ = g * x * (g⁻¹ * y) := by rw [hygi]
        _ = (g * x * g⁻¹) * y := by group
    rw [hC, Subgroup.le_normalizer_iff]
    intro b hb f hf
    refine ⟨?_, ?_⟩
    · exact Subgroup.le_normalizer_iff.mp hU_le_NF b hb.1 f hf.1
    · exact key (hCS_le_Ct2 hb.2) hf.2
  have hcard : Nat.card ↥A * Nat.card ↥(C ⊓ B0) = Nat.card ↥C * Nat.card ↥B0 := by
    have h := card_sup_mul_card_inf_of_le_normalizer (A := C) (B := B0) hB0_le_NC
    rwa [← hA_eq] at h
  -- ## Step 5: `C` has order prime to `p`
  -- `O_p(U)` has odd order (`U` does), so inversion by `t₂` has no nontrivial fixed point.
  have hoddP : Odd (Nat.card ↥P) :=
    Odd.of_dvd_nat (Work.CORE2A.bSetup_U_odd B)
      (Subgroup.card_dvd_of_le (c1aPcoreIn_le_self D.p U))
  have hbot : P ⊓ centralizer ({D.t2} : Set G) = ⊥ :=
    Work.CORE2A.inverts_inf_centralizer_eq_bot_of_odd D.inv hoddP
  -- every `p`-element of `F(U)` centralized by `t₂` is trivial
  have keyG : ∀ y : G, y ∈ F → y ^ D.p = 1 →
      y ∈ centralizer ({D.t2} : Set G) → y = 1 := by
    intro y hyF hyp hycen
    have hyP : y ∈ P := pCoreIn_of_pow_eq_one_of_mem_fittingIn B.U D.p hyF hyp
    exact Subgroup.mem_bot.mp (by rw [← hbot]; exact ⟨hyP, hycen⟩)
  have hC_fac : (Nat.card ↥C).factorization D.p = 0 := by
    apply Nat.factorization_eq_zero_of_not_dvd
    intro hdvd
    obtain ⟨x, hxord⟩ := exists_prime_orderOf_dvd_card' (G := ↥C) D.p hdvd
    have hyp : (x : G) ^ D.p = 1 := by
      have h1 : x ^ D.p = 1 := by rw [← hxord]; exact pow_orderOf_eq_one x
      simpa using congrArg (fun z : ↥C => (z : G)) h1
    have hx1g : (x : G) = 1 := keyG (x : G) x.2.1 hyp x.2.2
    have hx1 : x = 1 := Subtype.ext (by simpa using hx1g)
    rw [hx1, orderOf_one] at hxord
    exact absurd hxord (Fact.out : D.p.Prime).one_lt.ne
  have hCB0_fac : (Nat.card ↥(C ⊓ B0)).factorization D.p = 0 := by
    apply Nat.factorization_eq_zero_of_not_dvd
    intro hdvd
    obtain ⟨x, hxord⟩ := exists_prime_orderOf_dvd_card' (G := ↥(C ⊓ B0)) D.p hdvd
    have hxC : (x : G) ∈ C := (Subgroup.mem_inf.mp x.2).1
    have hyp : (x : G) ^ D.p = 1 := by
      have h1 : x ^ D.p = 1 := by rw [← hxord]; exact pow_orderOf_eq_one x
      simpa using congrArg (fun z : ↥(C ⊓ B0) => (z : G)) h1
    have hx1g : (x : G) = 1 := keyG (x : G) hxC.1 hyp hxC.2
    have hx1 : x = 1 := Subtype.ext (by simpa using hx1g)
    rw [hx1, orderOf_one] at hxord
    exact absurd hxord (Fact.out : D.p.Prime).one_lt.ne
  -- ## Step 6: assemble
  have hpos : ∀ H : Subgroup G, Nat.card ↥H ≠ 0 := fun H => by
    haveI : Nonempty ↥H := ⟨⟨1, H.one_mem⟩⟩
    exact Nat.card_pos.ne'
  have hmain : (Nat.card ↥A).factorization D.p = (Nat.card ↥B0).factorization D.p := by
    have h1 := congrArg (fun n : ℕ => n.factorization D.p) hcard
    rw [Nat.factorization_mul (hpos A) (hpos (C ⊓ B0)),
      Nat.factorization_mul (hpos C) (hpos B0)] at h1
    simp only [Finsupp.add_apply] at h1
    rw [hC_fac, hCB0_fac] at h1
    simpa using h1
  exact hmain

end Work.CORE3.A7V18
