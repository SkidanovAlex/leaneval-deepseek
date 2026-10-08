import Mathlib
import Submission.Work.CORE3.Case1aFrattiniApi
import Submission.Work.BSW.Api.card_sup_of_le_normalizer_of_inf_eq_bot
import Submission.Work.CORE3.relIndex_of_factorization_eq

/-!
# CORE3 / `Case1aP1Sylow`

Bender 1981, §3, p. 222.  With `P = O_p(U)`, `P₂ ∈ Syl_p(C_U(S))` and `V₁ = ⟨t, t₁⟩`, the
subgroup `P₁ = P·P₂` is a Sylow `p`-subgroup of `C_G(V₁)`.

The proof is a cardinality computation:

* `C_G(V₁) = (U ⊓ C_G(t₁)) ⊔ V₁` (`Work.CORE3.Work.CORE3.centralizer_V1`), and this is a
  direct product since `V₁ ⊓ (U ⊓ C_G(t₁)) = 1` and `V₁` normalizes the odd factor;
* hence `|C_G(V₁)| = |U ⊓ C_G(t₁)| · |V₁|`, and `|V₁| = 4` is coprime to the odd prime `p`;
* `P ⊓ P₂ = 1` (`P ∩ C_U(S) = 1` since `t₂ ∈ S` inverts `P`), so `|P ⊔ P₂| = |P| · |P₂|`;
* finally `hppart` computes the `p`-part of `|U ⊓ C_G(t₁)|` as `|P| · |C_U(S)|` and `hP2syl`
  identifies `|P₂|` with the `p`-part of `|C_U(S)|`.

Comparing `p`-adic valuations and applying `Work.CORE3.relIndex_of_factorization_eq` finishes.
-/

open scoped MatrixGroups

namespace Work.CORE3

open Work.GW2
open Subgroup

variable {G : Type} [Group G] [Finite G]

/-- `O_p(U) ⊓ C_U(S) = 1`: `t₂ ∈ S` centralizes `C_U(S)` but inverts the `p`-group `O_p(U)`,
so an element of the intersection has `x = x⁻¹` and odd order. -/
theorem pCoreIn_inf_centralizerS_eq_bot (B : BenderSetup G) (D : Case1aData B) :
    pCoreIn D.p B.U ⊓ (B.U ⊓ centralizer ((B.S : Subgroup G) : Set G)) = ⊥ := by
  have hpodd : Odd (Nat.card ↥(pCoreIn D.p B.U)) := by
    have hdvd : Nat.card ↥(pCoreIn D.p B.U) ∣ Nat.card ↥B.U := by
      have h := Subgroup.relIndex_mul_card (pCoreIn D.p B.U) B.U
      rw [inf_eq_left.mpr (c1aPcoreIn_le_self D.p B.U)] at h
      exact ⟨(pCoreIn D.p B.U).relIndex B.U, h.symm.trans (mul_comm _ _)⟩
    exact Odd.of_dvd_nat (Work.CORE2A.bSetup_U_odd B) hdvd
  have hbot : pCoreIn D.p B.U ⊓ centralizer ({D.t2} : Set G) = ⊥ :=
    Work.CORE2A.inverts_inf_centralizer_eq_bot_of_odd D.inv hpodd
  refine le_bot_iff.mp ?_
  calc pCoreIn D.p B.U ⊓ (B.U ⊓ centralizer ((B.S : Subgroup G) : Set G))
      ≤ pCoreIn D.p B.U ⊓ centralizer ({D.t2} : Set G) :=
        le_inf inf_le_left
          ((inf_le_right.trans inf_le_right).trans (Subgroup.centralizer_le (by
            intro z hz
            rw [Set.mem_singleton_iff] at hz
            subst hz
            exact D.t2_mem)))
    _ = ⊥ := hbot

/-- `⟨t, t₁⟩ ≤ N_G(U ⊓ C_G(t₁))`. -/
theorem V1_le_normalizer_inf_centralizer_t1 (B : BenderSetup G) (D : Case1aData B) :
    V1 B D ≤ Subgroup.normalizer ((B.U ⊓ centralizer ({D.t1} : Set G)) : Set G) := by
  have hD0_le : (B.U ⊓ centralizer ({D.t1} : Set G))
      ≤ centralizer ((V1 B D : Subgroup G) : Set G) := by
    rw [V1, Subgroup.centralizer_sup]
    refine le_inf ?_ ?_
    · rw [Work.CORE3.Work.CORE3.centralizer_zpowers_eq B.t]
      exact inf_le_left.trans (Work.CORE2A.bSetup_U_le_H B)
    · rw [Work.CORE3.Work.CORE3.centralizer_zpowers_eq D.t1]
      exact inf_le_right
  exact (Subgroup.le_centralizer_iff.mpr hD0_le).trans
    (Subgroup.centralizer_le_normalizer ((B.U ⊓ centralizer ({D.t1} : Set G)) : Set G))

theorem Case1aP1Sylow (G : Type) [Group G] [Finite G] (hFT : Work.GW2.FeitThompsonProp) (T : Work.GW2.LocalToolkit) (hBc : Work.GW2.BenderCtx G) (B : Work.GW2.BenderSetup G) (D : Work.GW2.Case1aData B) (P2 : Subgroup G) (hP2le : P2 ≤ B.U ⊓ Subgroup.centralizer ((B.S : Subgroup G) : Set G)) (hP2grp : IsPGroup D.p P2) (hP2syl : ¬ D.p ∣ P2.relIndex (B.U ⊓ Subgroup.centralizer ((B.S : Subgroup G) : Set G))) (hppart : Work.CORE3.PpartProp B D) : Work.CORE3.P1SylowIn B D P2 := by
  haveI hpprime : Fact D.p.Prime := ⟨D.hp⟩
  -- `D.p` is odd (`p ∈ π(F(U))` and `|F(U)| ∣ |U|` is odd)
  have hpodd : Odd D.p := by
    have hpF : D.p ∣ Nat.card ↥(fittingIn B.U) := (Nat.mem_primeFactors.mp D.p_mem).2.1
    have hFdvd : Nat.card ↥(fittingIn B.U) ∣ Nat.card ↥B.U := by
      have h := Subgroup.relIndex_mul_card (fittingIn B.U) B.U
      rw [inf_eq_left.mpr (c1aFittingIn_le B.U)] at h
      exact ⟨(fittingIn B.U).relIndex B.U, h.symm.trans (mul_comm _ _)⟩
    exact Odd.of_dvd_nat (Work.CORE2A.bSetup_U_odd B) (hpF.trans hFdvd)
  have hnotdvd4 : ¬ D.p ∣ 4 := by
    intro h
    have hsq : D.p ∣ 2 ^ 2 := by
      rw [show (4 : ℕ) = 2 ^ 2 by norm_num] at h
      exact h
    have hpm : D.p ∣ 2 := Nat.Prime.dvd_of_dvd_pow D.hp hsq
    have h2 : D.p = 2 := ((Nat.Prime.dvd_iff_eq Nat.prime_two D.hp.ne_one).mp hpm).symm
    have hodd2 : Odd D.p := hpodd
    rw [h2] at hodd2
    exact (Odd.not_two_dvd_nat hodd2) (dvd_refl 2)
  -- all relevant subgroup orders are non-zero
  have hne : ∀ (H : Subgroup G), Nat.card ↥H ≠ 0 := fun H =>
    Nat.card_ne_zero.mpr ⟨⟨1, H.one_mem⟩, inferInstance⟩
  -- `P₂` normalizes `P = O_p(U)`
  have hP2norm : P2 ≤ Subgroup.normalizer (↑(pCoreIn D.p B.U) : Set G) :=
    (hP2le.trans inf_le_left).trans
      ((Subgroup.le_normalizer).trans (c1aLe_normalizer_pCoreIn D.p B.U))
  -- `P ⊓ P₂ = 1`
  have hPP2 : pCoreIn D.p B.U ⊓ P2 = ⊥ := by
    refine le_bot_iff.mp ?_
    calc pCoreIn D.p B.U ⊓ P2
        ≤ pCoreIn D.p B.U ⊓ (B.U ⊓ centralizer ((B.S : Subgroup G) : Set G)) :=
          le_inf inf_le_left (inf_le_right.trans hP2le)
      _ = ⊥ := pCoreIn_inf_centralizerS_eq_bot B D
  -- #### first conjunct: `P ⊔ P₂ ≤ C_G(V₁)`
  have hQleC : (pCoreIn D.p B.U ⊔ P2 : Subgroup G)
      ≤ Subgroup.centralizer ((V1 B D : Subgroup G) : Set G) := by
    refine sup_le ?_ ?_
    · rw [V1, Subgroup.centralizer_sup]
      refine le_inf ?_ ?_
      · rw [Work.CORE3.Work.CORE3.centralizer_zpowers_eq B.t]
        exact (c1aPcoreIn_le_self D.p B.U).trans (Work.CORE2A.bSetup_U_le_H B)
      · rw [Work.CORE3.Work.CORE3.centralizer_zpowers_eq D.t1]
        exact D.cent
    · rw [V1, Subgroup.centralizer_sup]
      refine le_inf ?_ ?_
      · rw [Work.CORE3.Work.CORE3.centralizer_zpowers_eq B.t]
        exact (hP2le.trans inf_le_left).trans (Work.CORE2A.bSetup_U_le_H B)
      · rw [Work.CORE3.Work.CORE3.centralizer_zpowers_eq D.t1]
        exact (hP2le.trans inf_le_right).trans (Subgroup.centralizer_le (by
          intro z hz
          rw [Set.mem_singleton_iff] at hz
          subst hz
          exact D.t1_mem))
  -- #### second conjunct: `P ⊔ P₂` is a `p`-group
  have hQp : IsPGroup D.p (↥(pCoreIn D.p B.U ⊔ P2 : Subgroup G)) :=
    IsPGroup.to_sup_of_normal_left' (c1aIsPGroup_pCoreIn D.p B.U) hP2grp hP2norm
  -- #### cardinalities
  have hcardQ : Nat.card ↥(pCoreIn D.p B.U ⊔ P2)
      = Nat.card ↥(pCoreIn D.p B.U) * Nat.card ↥P2 :=
    Work.BSW.Api.card_sup_of_le_normalizer_of_inf_eq_bot hP2norm hPP2
  have hD0V : (B.U ⊓ centralizer ({D.t1} : Set G)) ⊓ V1 B D = ⊥ := by
    have hV1S : V1 B D ≤ (B.S : Subgroup G) :=
      sup_le (Subgroup.zpowers_le.mpr (B.S0_le B.t_mem)) (Subgroup.zpowers_le.mpr D.t1_mem)
    rw [inf_comm]
    refine le_bot_iff.mp ?_
    calc V1 B D ⊓ (B.U ⊓ centralizer ({D.t1} : Set G))
        ≤ V1 B D ⊓ B.U := le_inf inf_le_left (inf_le_right.trans inf_le_left)
      _ ≤ (B.S : Subgroup G) ⊓ B.U := le_inf (inf_le_left.trans hV1S) inf_le_right
      _ = ⊥ := by rw [inf_comm]; exact Work.CORE2A.inf_U_S_eq_bot B
  have hCV : Subgroup.centralizer ((V1 B D : Subgroup G) : Set G)
      = (B.U ⊓ centralizer ({D.t1} : Set G)) ⊔ V1 B D :=
    Work.CORE3.Work.CORE3.centralizer_V1 hBc T B D
  have hcardC : Nat.card ↥(Subgroup.centralizer ((V1 B D : Subgroup G) : Set G))
      = Nat.card ↥(B.U ⊓ centralizer ({D.t1} : Set G)) * Nat.card ↥(V1 B D) := by
    rw [hCV]
    exact Work.BSW.Api.card_sup_of_le_normalizer_of_inf_eq_bot
      (V1_le_normalizer_inf_centralizer_t1 B D) hD0V
  -- `|P| · |P₂| = |C_G(V₁)|` at the prime `p`, via `hppart` and `hP2syl`
  have hL : (Nat.card ↥(pCoreIn D.p B.U ⊔ P2)).factorization D.p
      = (Nat.card ↥(pCoreIn D.p B.U)).factorization D.p
        + (Nat.card ↥P2).factorization D.p := by
    rw [hcardQ, Nat.factorization_mul (hne (pCoreIn D.p B.U)) (hne P2)]
    simp only [Finsupp.add_apply]
  have hR : (Nat.card ↥(Subgroup.centralizer ((V1 B D : Subgroup G) : Set G))).factorization D.p
      = (Nat.card ↥(B.U ⊓ centralizer ({D.t1} : Set G))).factorization D.p
        + (Nat.card ↥(V1 B D)).factorization D.p := by
    rw [hcardC, Nat.factorization_mul
      (hne (B.U ⊓ centralizer ({D.t1} : Set G))) (hne (V1 B D))]
    simp only [Finsupp.add_apply]
  have hP2fac : (Nat.card ↥P2).factorization D.p
      = (Nat.card ↥(B.U ⊓ centralizer ((B.S : Subgroup G) : Set G))).factorization D.p := by
    have h := Subgroup.relIndex_mul_card P2 (B.U ⊓ centralizer ((B.S : Subgroup G) : Set G))
    rw [inf_eq_left.mpr hP2le] at h
    have hne0 : P2.relIndex (B.U ⊓ centralizer ((B.S : Subgroup G) : Set G)) ≠ 0 := by
      intro h0
      rw [h0, zero_mul] at h
      exact hne (B.U ⊓ centralizer ((B.S : Subgroup G) : Set G)) h.symm
    rw [← h, Nat.factorization_mul hne0 (hne P2)]
    simp only [Finsupp.add_apply, Nat.factorization_eq_zero_of_not_dvd hP2syl, zero_add]
  have hV1card : Nat.card ↥(V1 B D) = 4 := (Work.CORE3.Work.CORE3.fourGroup_V1 hBc B D).1
  have hV1fac : (Nat.card ↥(V1 B D)).factorization D.p = 0 := by
    rw [hV1card]
    exact Nat.factorization_eq_zero_of_not_dvd hnotdvd4
  have hpp : (Nat.card ↥(B.U ⊓ centralizer ({D.t1} : Set G))).factorization D.p
      = (Nat.card ↥(pCoreIn D.p B.U)).factorization D.p
        + (Nat.card ↥(B.U ⊓ centralizer ((B.S : Subgroup G) : Set G))).factorization D.p :=
    hppart
  have hkey : (Nat.card ↥(pCoreIn D.p B.U ⊔ P2)).factorization D.p
      = (Nat.card ↥(Subgroup.centralizer ((V1 B D : Subgroup G) : Set G))).factorization D.p := by
    calc (Nat.card ↥(pCoreIn D.p B.U ⊔ P2)).factorization D.p
        = (Nat.card ↥(pCoreIn D.p B.U)).factorization D.p
            + (Nat.card ↥P2).factorization D.p := hL
      _ = (Nat.card ↥(pCoreIn D.p B.U)).factorization D.p
            + (Nat.card ↥(B.U ⊓ centralizer ((B.S : Subgroup G) : Set G))).factorization D.p := by
          rw [hP2fac]
      _ = (Nat.card ↥(B.U ⊓ centralizer ({D.t1} : Set G))).factorization D.p := hpp.symm
      _ = (Nat.card ↥(B.U ⊓ centralizer ({D.t1} : Set G))).factorization D.p
            + (Nat.card ↥(V1 B D)).factorization D.p := by rw [hV1fac, add_zero]
      _ = (Nat.card ↥(Subgroup.centralizer ((V1 B D : Subgroup G) : Set G))).factorization D.p :=
          hR.symm
  have hQrel : ¬ D.p ∣ (pCoreIn D.p B.U ⊔ P2 : Subgroup G).relIndex
      (Subgroup.centralizer ((V1 B D : Subgroup G) : Set G)) :=
    relIndex_of_factorization_eq _ _ hQleC D.p D.hp hkey
  exact ⟨hQleC, hQp, hQrel⟩

end Work.CORE3
