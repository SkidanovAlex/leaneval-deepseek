import Mathlib
import Submission.Work.CORE3.Case1aThmCInputs
import Submission.Work.CORE3.Case1aSetup
import Submission.Work.CORE3.Case1aBothInvert
import Submission.Work.CORE3.H_eq_U_sup_S
import Submission.Work.CORE3.SylowDihedral
import Submission.Work.CORE3.Case1aBFpf
import Submission.Work.CORE3.Case1aFrattiniSAct
import Submission.Work.CORE3.Case1aP_ne_bot
import Submission.Work.CORE3.fittingPiIn_eq_iSup_pCoreIn
import Submission.Work.CORE3.isPGroup_le_or_inf_eq_bot_of_isHallIn
import Submission.Work.CORE3.oddInvertedLeFittingIn
import Submission.Work.CORE3.p_eq_three
import Submission.Work.CORE2A.odd_subgroup_le_oddCoreIn
import Submission.Work.CORE2A.Extra
import Submission.Work.DSTR.M110.PiCoreFacts

set_option linter.style.haveILetI false
set_option linter.unusedVariables false

namespace Work.CORE3

open scoped Pointwise
open Subgroup
open Work.GW2

/-! ## Helpers -/

/-- `F_π(K) = O_π(F(K))` is a `π`-subgroup. -/
theorem isPiSubgroupFittingPiIn {G : Type} [Group G] [Finite G] (π : Set ℕ) (K : Subgroup G) :
    Subgroup.IsPiSubgroup π (Work.GW2.fittingPiIn π K) := by
  have h1 : Subgroup.IsPiSubgroup π (Work.GW2.piCore π ↥(Work.GW2.fitting ↥K)) :=
    Work.DSTR.FittingPiImg.isPiSubgroup_piCore π
  have h2 : Subgroup.IsPiSubgroup π
      ((Work.GW2.piCore π ↥(Work.GW2.fitting ↥K)).map (Work.GW2.fitting ↥K).subtype) :=
    Work.DSTR.FittingPiImg.isPiSubgroup_map (f := (Work.GW2.fitting ↥K).subtype) h1
  exact Work.DSTR.FittingPiImg.isPiSubgroup_map (f := K.subtype) h2

/-- The `3'`-part of `F(K)` has order coprime to `3`. -/
theorem not_three_dvd_card_fittingPiIn {G : Type} [Group G] [Finite G] (K : Subgroup G) :
    ¬ 3 ∣ Nat.card (Work.GW2.fittingPiIn ({3}ᶜ : Set ℕ) K) := by
  intro hdvd
  have hmem : 3 ∈ (Nat.card (Work.GW2.fittingPiIn ({3}ᶜ : Set ℕ) K)).primeFactors :=
    Nat.mem_primeFactors.mpr ⟨Nat.prime_three, hdvd, Nat.card_pos.ne'⟩
  exact absurd (isPiSubgroupFittingPiIn ({3}ᶜ : Set ℕ) K 3 hmem) (by simp)

/-- `F_{3'}(K) ⊓ O_3(K) = ⊥`. -/
theorem threeParts_disjoint {G : Type} [Group G] [Finite G] (K : Subgroup G) :
    Work.GW2.fittingPiIn ({3}ᶜ : Set ℕ) K ⊓ Work.GW2.pCoreIn 3 K = ⊥ := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hcop : Nat.Coprime (Nat.card ↥(Work.GW2.fittingPiIn ({3}ᶜ : Set ℕ) K))
      (Nat.card ↥(Work.GW2.pCoreIn 3 K)) := by
    obtain ⟨k, hk⟩ := (c1aIsPGroup_pCoreIn 3 K).exists_card_eq
    rw [hk]
    exact Nat.prime_three.coprime_pow_of_not_dvd (not_three_dvd_card_fittingPiIn K)
  have hone : Nat.card ↥(Work.GW2.fittingPiIn ({3}ᶜ : Set ℕ) K ⊓ Work.GW2.pCoreIn 3 K) = 1 :=
    Nat.eq_one_of_dvd_coprimes hcop (Subgroup.card_dvd_of_le inf_le_left)
      (Subgroup.card_dvd_of_le inf_le_right)
  exact Subgroup.card_eq_one.mp hone

/-- The two factors of `F(K)` commute elementwise. -/
theorem threeParts_commute {G : Type} [Group G] [Finite G] (K : Subgroup G) :
    ∀ a ∈ Work.GW2.fittingPiIn ({3}ᶜ : Set ℕ) K,
      ∀ b ∈ Work.GW2.pCoreIn 3 K, a * b = b * a := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  intro a ha b hb
  set A : Subgroup G := Work.GW2.fittingPiIn ({3}ᶜ : Set ℕ) K with hAdef
  set B : Subgroup G := Work.GW2.pCoreIn 3 K with hBdef
  have hAK : A ≤ K := (bfpf_fittingPiIn_le_fittingIn ({3}ᶜ : Set ℕ) K).trans (c1aFittingIn_le K)
  have hBK : B ≤ K := c1aPcoreIn_le_self 3 K
  have hKA : K ≤ Subgroup.normalizer (A : Set G) :=
    Work.DSTR.M110.le_normalizer_fittingPiIn G ({3}ᶜ) K
  have hKB : K ≤ Subgroup.normalizer (B : Set G) :=
    Subgroup.le_normalizer.trans (c1aLe_normalizer_pCoreIn 3 K)
  have hdisj : A ⊓ B = ⊥ := threeParts_disjoint K
  have hconjA : ∀ g ∈ K, ∀ x ∈ A, g * x * g⁻¹ ∈ A :=
    fun g hg x hx => (Subgroup.mem_normalizer_iff.mp (hKA hg) x).mp hx
  have hconjB : ∀ g ∈ K, ∀ x ∈ B, g * x * g⁻¹ ∈ B :=
    fun g hg x hx => (Subgroup.mem_normalizer_iff.mp (hKB hg) x).mp hx
  have hbK : b ∈ K := hBK hb
  have haK : a ∈ K := hAK ha
  have hcA : a⁻¹ * b⁻¹ * a * b ∈ A := by
    have h1 : b⁻¹ * a * b ∈ A := by
      have h := hconjA b⁻¹ (K.inv_mem hbK) a ha
      simpa using h
    have h2 := A.mul_mem (A.inv_mem ha) h1
    simpa [mul_assoc] using h2
  have hcB : a⁻¹ * b⁻¹ * a * b ∈ B := by
    have h1 : a⁻¹ * b⁻¹ * a ∈ B := by
      have h := hconjB a⁻¹ (K.inv_mem haK) b⁻¹ (B.inv_mem hb)
      simpa using h
    have h2 := B.mul_mem h1 hb
    simpa [mul_assoc] using h2
  have hc : a⁻¹ * b⁻¹ * a * b = 1 := by
    have hmem : a⁻¹ * b⁻¹ * a * b ∈ (⊥ : Subgroup G) := by
      rw [← hdisj]
      exact Subgroup.mem_inf.mpr ⟨hcA, hcB⟩
    simpa using hmem
  have h5 : b⁻¹ * a * b = a := by
    calc b⁻¹ * a * b = a * (a⁻¹ * b⁻¹ * a * b) := by group
      _ = a * 1 := by rw [hc]
      _ = a := mul_one a
  calc a * b = b * (b⁻¹ * a * b) := by group
    _ = b * a := by rw [h5]

/-- `F(K) = F_{3'}(K) × O_3(K)` elementwise: every element of the Fitting subgroup of `K` is a
commuting product of an element of the `3'`-part and an element of the `3`-core. -/
private theorem c1aFittingDecomp {G : Type} [Group G] [Finite G] (K : Subgroup G) :
    ∀ y ∈ Work.GW2.fittingIn K,
      ∃ a ∈ Work.GW2.fittingPiIn ({3}ᶜ : Set ℕ) K, ∃ b ∈ Work.GW2.pCoreIn 3 K,
        y = a * b ∧ a * b = b * a := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  intro y hy
  have hKB : Work.GW2.pCoreIn 3 K ≤
      Subgroup.normalizer (Work.GW2.fittingPiIn ({3}ᶜ : Set ℕ) K : Set G) :=
    (c1aPcoreIn_le_self 3 K).trans (Work.DSTR.M110.le_normalizer_fittingPiIn G ({3}ᶜ) K)
  have hsup : Work.GW2.fittingPiIn ({3}ᶜ : Set ℕ) K ⊔ Work.GW2.pCoreIn 3 K =
      Work.GW2.fittingIn K := (c1aFittingIn_eq_sup_three K).symm
  have hmem : y ∈ (Work.GW2.fittingPiIn ({3}ᶜ : Set ℕ) K : Set G) *
      ((Work.GW2.pCoreIn 3 K : Subgroup G) : Set G) := by
    rw [← Subgroup.coe_mul_of_right_le_normalizer_left
      (Work.GW2.fittingPiIn ({3}ᶜ : Set ℕ) K) (Work.GW2.pCoreIn 3 K) hKB, hsup]
    exact hy
  obtain ⟨a, ha, b, hb, hab⟩ := Set.mem_mul.mp hmem
  exact ⟨a, ha, b, hb, hab.symm, threeParts_commute K a ha b hb⟩

theorem c1aDirMaxInv (I : Work.CORE3.Case1Inputs) (hFr : Work.GW2.Case1aFrattiniProp)
    (hAb : Work.GW2.Case1aAbelianProp) (hA7 : Work.GW2.Case1aA7Prop)
    (hBpf : Work.CORE3.Case1aBFpfProp) (hMD : Work.CORE3.Case1aMDataProp)
    (hDir : Work.CORE3.Case1aDirectProp) :
    ∀ (G : Type) [Group G] [Finite G], Work.GW2.FeitThompsonProp → Work.GW2.BenderCtx G →
      ∀ B : Work.GW2.BenderSetup G, Work.GW2.Case1 B → B.Hhat = B.H →
      ∀ D : Work.GW2.Case1aData B,
        Work.GW2.IsMaxInverted B.H D.t1 (Work.GW2.fittingPiIn ({3}ᶜ) B.U) ∧
        Work.GW2.IsMaxInverted B.H D.t2 (Work.GW2.fittingIn B.U) := by
  intro G _instG _finG hFT hCtx B hCase1 hH D
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  -- (0) Bender's two inversion facts for `F_{3'}(U)`
  have hInv : Inverts D.t1 (fittingPiIn ({3}ᶜ : Set ℕ) B.U) ∧
      Inverts D.t2 (fittingPiIn ({3}ᶜ : Set ℕ) B.U) :=
    (Case1aBothInvert I (Case1aSetup I) hFr hAb hA7 hBpf) G hFT hCtx B hCase1 hH D
  have hInv1 : Inverts D.t1 (fittingPiIn ({3}ᶜ : Set ℕ) B.U) := hInv.1
  have hInv2 : Inverts D.t2 (fittingPiIn ({3}ᶜ : Set ℕ) B.U) := hInv.2
  -- (1) `S` acts trivially on `U/F(U)` and `H = U·S`
  have hSAct : SActsTriviallyModFitting B := Case1aFrattiniSAct G hFT I.T hCtx B hCase1
  have hHU : B.U ⊔ (B.S : Subgroup G) = B.H := H_eq_U_sup_S G I.T hCtx B
  have hodd_le_U : ∀ X : Subgroup G, X ≤ B.H → Odd (Nat.card X) → X ≤ B.U :=
    fun X hXH hodd =>
      Work.CORE2A.odd_subgroup_le_oddCoreIn B.H B.U (B.S : Subgroup G) rfl hHU B.S.isPGroup' X hXH hodd
  -- (2) `p = 3`, so `O_3(U)` is centralized by `t₁` and inverted by `t₂`
  have hp3 : D.p = 3 := p_eq_three B D hInv1
  have hcent3 : pCoreIn 3 B.U ≤ Subgroup.centralizer ({D.t1} : Set G) := hp3 ▸ D.cent
  have hinvO3 : Inverts D.t2 (pCoreIn 3 B.U) := hp3 ▸ D.inv
  -- (3) odd `t₂`-inverted subgroups of `H` lie in `F(U)`
  have hmax2 : ∀ X : Subgroup G, X ≤ B.H → Odd (Nat.card X) → Inverts D.t2 X →
      X ≤ fittingIn B.U :=
    fun X hXH hodd hinv =>
      oddInvertedLeFittingIn B hSAct D.t2_mem (hodd_le_U X hXH hodd) hodd hinv
  -- (4) odd `t₁`-inverted subgroups of `H` lie in `F_{3'}(U)`
  have hmax1 : ∀ X : Subgroup G, X ≤ B.H → Odd (Nat.card X) → Inverts D.t1 X →
      X ≤ fittingPiIn ({3}ᶜ : Set ℕ) B.U := by
    intro X hXH hodd hinv x hx
    have hXF : X ≤ fittingIn B.U :=
      oddInvertedLeFittingIn B hSAct D.t1_mem (hodd_le_U X hXH hodd) hodd hinv
    obtain ⟨a, ha, b, hb, hab, hcomm⟩ := c1aFittingDecomp B.U x (hXF hx)
    have hbcent : D.t1 * b * D.t1⁻¹ = b := by
      have h := (Subgroup.mem_centralizer_iff.mp (hcent3 hb)) D.t1 (by simp)
      rw [show D.t1 * b = b * D.t1 from h]
      group
    have hconj : D.t1 * x * D.t1⁻¹ = a⁻¹ * b := by
      rw [hab, show D.t1 * (a * b) * D.t1⁻¹ =
        (D.t1 * a * D.t1⁻¹) * (D.t1 * b * D.t1⁻¹) from by group, hInv1 a ha, hbcent]
    have hxinv : x⁻¹ = a⁻¹ * b⁻¹ := by
      have hcab : Commute a b := hcomm
      rw [hab, mul_inv_rev]
      exact ((hcab.inv_inv).eq).symm
    have hbeq : a⁻¹ * b = a⁻¹ * b⁻¹ := by rw [← hconj, hinv x hx, hxinv]
    have hbb : b = b⁻¹ := mul_left_cancel hbeq
    have hbsq : b * b = 1 := by nth_rewrite 2 [hbb]; exact mul_inv_cancel b
    have hb1 : b = 1 :=
      c1aEqOneOfMulSelfOdd (Work.CORE2A.bSetup_U_odd B) (c1aPcoreIn_le_self 3 B.U hb) hbsq
    rw [show x = a from by rw [hab, hb1, mul_one]]
    exact ha
  -- (5) `t₂` inverts `F(U) = F_{3'}(U) × O_3(U)`
  have hInvF : Inverts D.t2 (fittingIn B.U) := by
    intro x hx
    obtain ⟨a, ha, b, hb, hab, hcomm⟩ := c1aFittingDecomp B.U x hx
    have hright : D.t2 * x * D.t2⁻¹ = a⁻¹ * b⁻¹ := by
      rw [hab, show D.t2 * (a * b) * D.t2⁻¹ =
        (D.t2 * a * D.t2⁻¹) * (D.t2 * b * D.t2⁻¹) from by group, hInv2 a ha, hinvO3 b hb]
    have hleft : x⁻¹ = a⁻¹ * b⁻¹ := by
      have hcab : Commute a b := hcomm
      rw [hab, mul_inv_rev]
      exact ((hcab.inv_inv).eq).symm
    rw [hright, hleft]
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_⟩⟩
  · exact (bfpf_fittingPiIn_le_fittingIn ({3}ᶜ : Set ℕ) B.U).trans
      ((c1aFittingIn_le B.U).trans (Work.CORE2A.bSetup_U_le_H B))
  · have hle : fittingPiIn ({3}ᶜ : Set ℕ) B.U ≤ B.U :=
      (bfpf_fittingPiIn_le_fittingIn ({3}ᶜ : Set ℕ) B.U).trans (c1aFittingIn_le B.U)
    exact Odd.of_dvd_nat (Work.CORE2A.bSetup_U_odd B) (Subgroup.card_dvd_of_le hle)
  · exact hInv1
  · exact fun X hXH hodd hinv => hmax1 X hXH hodd hinv
  · exact (c1aFittingIn_le B.U).trans (Work.CORE2A.bSetup_U_le_H B)
  · exact Odd.of_dvd_nat (Work.CORE2A.bSetup_U_odd B)
      (Subgroup.card_dvd_of_le (c1aFittingIn_le B.U))
  · exact hInvF
  · exact fun X hXH hodd hinv => hmax2 X hXH hodd hinv

end Work.CORE3
