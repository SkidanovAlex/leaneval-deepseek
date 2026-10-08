import Mathlib
import Submission.Work.NormalComplement.S5K.Defs
import Submission.Work.NormalComplement.S5K.ca_coprime
import Submission.Work.NormalComplement.sec4_prop1_star
import Submission.Work.NormalComplement.Design.Extra

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option autoImplicit false

open Classical
open scoped Pointwise commutatorElement
open LeanEval.GroupTheory.Defs
open Submission.Blueprint

namespace Work.NormalComplement.S5K

variable {G : Type*} [Group G] [Finite G]

/-! ## A generic `π`-core helper -/

/-- A normal `π'`-subgroup `R` of a subgroup `X` (normalised by `X`) is contained in
`O_{π'}(X) = piPrimeCoreSub π X`. -/
lemma le_piPrimeCoreSub_of_normal_isPiNat {π : Set ℕ} {X R : Subgroup G} (hRX : R ≤ X)
    (hnorm : X ≤ Subgroup.normalizer (R : Set G))
    (hpi : Work.Fitting.IsPiNat (fun r => r ∉ π) (Nat.card ↥R)) :
    R ≤ piPrimeCoreSub π X := by
  have hN : (R.subgroupOf X).Normal := Subgroup.normal_subgroupOf_of_le_normalizer hnorm
  have hcard : Nat.card ↥(R.subgroupOf X) = Nat.card ↥R :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hRX).toEquiv
  have hpi' : Work.Fitting.IsPiNat (fun r => r ∉ π) (Nat.card ↥(R.subgroupOf X)) := by
    rw [hcard]; exact hpi
  have hle : R.subgroupOf X ≤ Work.Fitting.piCore (fun r => r ∉ π) ↥X :=
    Work.Fitting.le_piCore hN hpi'
  calc R = R ⊓ X := (inf_of_le_left hRX).symm
    _ = (R.subgroupOf X).map X.subtype := (Subgroup.subgroupOf_map_subtype R X).symm
    _ ≤ (Work.Fitting.piCore (fun r => r ∉ π) ↥X).map X.subtype := Subgroup.map_mono hle
    _ = piPrimeCoreSub π X := rfl

/-- `O_{π'}(X) ≤ X`. -/
lemma piPrimeCoreSub_le_self (π : Set ℕ) (X : Subgroup G) : piPrimeCoreSub π X ≤ X :=
  Subgroup.map_subtype_le _

/-! ## Formula (∗) with the P3 clauses retained

`Work.NormalComplement.sec4_prop1_star` produces its `2`-subgroup `S₂` from Ch. II §4 Prop. 3
applied to `X = U ⊔ P`, `Y = U`, but its statement discards the clauses of that proposition about
the subgroup.  For §4 Prop. 1 step 1 we need that `H ⊓ N_G(U ⊔ P)` — in particular `C_W(U)` for
`W = H ⊓ N_G(P)` — normalises `S₂`: only then is `S₂ ⊔ P` a *normal* `π'`-subgroup of `C_W(U)`,
hence inside `O_{π'}(C_W(U))`.  The proof below is the proof of
`Work.NormalComplement.sec4_prop1_star` with those two clauses carried along. -/

/-- **Peterfalvi I Ch. III §4 Prop. 1, formula (∗), strengthened** (p.180): as
`Work.NormalComplement.sec4_prop1_star`, but the `2`-subgroup `S₂` is the one coming from Ch. II §4
Prop. 3 (applied to `X = U ⊔ P`, `Y = U`): it lies in `O^{2'}(C_G(U ⊔ P))` and the whole
normaliser `H ⊓ N_G(U ⊔ P)` normalises it. -/
theorem sec4_prop1_star_strong (hFT : Submission.Blueprint.FeitThompsonProp)
    (hP3 : Submission.Blueprint.ChIIFourP3SubnormalProp) {G : Type} [Group G] [Finite G]
    {H : Subgroup G} {t : G} {W : Subgroup G} {p : ℕ} {P A : Subgroup G}
    (h : Work.NormalComplement.Design.Setup45A G H t W p P A) (U : Subgroup G) (hU : U ≠ ⊥)
    (hUA : U ≤ A ⊓ Subgroup.centralizer (P : Set G)) :
    ∃ S₂ : Subgroup G, IsPGroup 2 S₂ ∧ S₂ ≤ H ∧
      S₂ ≤ Subgroup.centralizer (U : Set G) ⊓ Subgroup.centralizer (P : Set G) ∧
      S₂ ≤ (Submission.Blueprint.oddResidual
              ↥(Subgroup.centralizer ((U ⊔ P : Subgroup G) : Set G))).map
        (Subgroup.centralizer ((U ⊔ P : Subgroup G) : Set G)).subtype ∧
      H ⊓ Subgroup.normalizer ((U ⊔ P : Subgroup G) : Set G) ≤ Subgroup.normalizer (S₂ : Set G) ∧
      H ⊓ Subgroup.normalizer (U : Set G) ⊓ Subgroup.normalizer (P : Set G) =
        (S₂ ⊔ P) ⊔ (A ⊓ Subgroup.centralizer (P : Set G) ⊓
          Subgroup.normalizer (U : Set G)) := by
  classical
  -- ## Elementary inclusions among `U, P, A, V = C_D(t)`
  have hU_le_A : U ≤ A := hUA.trans inf_le_left
  have hU_le_V : U ≤ centD H t := hU_le_A.trans h.A_le
  have hP_le_V : P ≤ centD H t := h.P_le.trans inf_le_right
  have hX_le_V : U ⊔ P ≤ centD H t := sup_le hU_le_V hP_le_V
  have hPU : P ≤ Subgroup.normalizer (U : Set G) :=
    sec4_star_le_normalizer_of_le_centralizer (hUA.trans inf_le_right)
  have hX_norm : U ⊔ P ≤ Subgroup.normalizer (U : Set G) :=
    sup_le Subgroup.le_normalizer hPU
  -- ## a non-identity element of `K` normalising `U` (from `C_K(A) ≠ 1`)
  have hp2 : 2 ≤ p := h.prime.two_le
  have hpow : 4 ≤ 2 ^ p := by
    calc (4 : ℕ) = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ p := Nat.pow_le_pow_right (by norm_num) hp2
  have h1CK : (1 : G) ∈ Design.CK H t A :=
    ⟨⟨Subgroup.one_mem _, by simp⟩, Subgroup.one_mem _⟩
  have hk : ∃ k ∈ Design.CK H t A, k ≠ 1 := by
    by_contra hcon
    push_neg at hcon
    have hsub : Design.CK H t A ⊆ ({1} : Set G) := fun x hx => by
      simpa using hcon x hx
    have hle : (Design.CK H t A).ncard ≤ 1 := by
      have := Set.ncard_le_ncard hsub (Set.finite_singleton (1 : G))
      simpa using this
    rw [h.A_CK] at hle
    omega
  obtain ⟨k, hkCK, hk1⟩ := hk
  have hkN : k ∈ Subgroup.normalizer (U : Set G) :=
    sec4_star_centralizer_le_normalizer hU_le_A hkCK.2
  have hk' : ∃ k ∈ invertedBy (twoPoint H t) t, k ≠ 1 ∧
      k ∈ Subgroup.normalizer (U : Set G) :=
    ⟨k, hkCK.1, hk1, hkN⟩
  -- ## Ch. II §4 Prop. 3 with `X = U ⊔ P`, `Y = U`
  obtain ⟨-, S, hS2, hSF, hSH, hSN, _hSD, hSsup⟩ :=
    (p3Normal_of_chIIFourP3Subnormal hP3) G h.sit H h.se t h.invol h.notMem
      (U ⊔ P) U hX_le_V hU le_sup_left hX_norm hk'
  have hS'_le : S ≤ Subgroup.centralizer ((U ⊔ P : Subgroup G) : Set G) :=
    hSF.trans (Subgroup.map_subtype_le
      (K := Submission.Blueprint.oddResidual ↥(Subgroup.centralizer
        ((U ⊔ P : Subgroup G) : Set G))))
  have hS_le_cent : S ≤ Subgroup.centralizer (U : Set G) ⊓ Subgroup.centralizer (P : Set G) :=
    le_inf (hS'_le.trans ((sec4_star_centralizer_sup_le U P).trans inf_le_left))
           (hS'_le.trans ((sec4_star_centralizer_sup_le U P).trans inf_le_right))
  -- ## §4 Lemma 1 (c): the normaliser of `P` inside `D`
  have hNDP : twoPoint H t ⊓ Subgroup.normalizer (P : Set G) =
      (A ⊓ Subgroup.centralizer (P : Set G)) ⊔ P := (sec4_one_c hFT h).1
  have hcentD_tp : centD H t ≤ twoPoint H t := inf_le_left
  have hcentD_H : centD H t ≤ H := inf_le_left.trans inf_le_left
  have hAH : A ≤ H := h.A_le.trans (inf_le_left.trans inf_le_left)
  have hS_le_C : S ≤ H ⊓ Subgroup.normalizer (U : Set G) ⊓
      Subgroup.normalizer (P : Set G) :=
    le_inf (le_inf hSH (hS_le_cent.trans (inf_le_left.trans
            (Subgroup.centralizer_le_normalizer (U : Set G)))))
           (hS_le_cent.trans (inf_le_right.trans
            (Subgroup.centralizer_le_normalizer (P : Set G))))
  refine ⟨S, hS2, hSH, hS_le_cent, hSF, hSN, ?_⟩
  -- ## the group identity
  apply le_antisymm
  · -- `N_H(U) ⊓ N_H(P) ≤ (S ⊔ P) ⊔ (C_A(P) ⊓ N_H(U))`
    -- `N_D(U ⊔ P) = D ⊓ N(U ⊔ P)` is normalised by `S` (Ch. II §4 Prop. 3)
    have hM_le_NS : twoPoint H t ⊓ Subgroup.normalizer ((U ⊔ P : Subgroup G) : Set G) ≤
        Subgroup.normalizer (S : Set G) :=
      (le_inf (inf_le_left.trans inf_le_left) inf_le_right).trans hSN
    -- hence `N_H(U ⊔ P) = S · N_D(U ⊔ P)` as a set product
    have hSM : (↑(S ⊔ (twoPoint H t ⊓ Subgroup.normalizer ((U ⊔ P : Subgroup G) : Set G))) :
          Set G) =
        (S : Set G) *
          (twoPoint H t ⊓ Subgroup.normalizer ((U ⊔ P : Subgroup G) : Set G) : Set G) :=
      Subgroup.coe_mul_of_right_le_normalizer_left S _ hM_le_NS
    -- and `N_D(U ⊔ P) ⊓ N_H(U) ⊓ N_H(P) ≤ (C_A(P) ⊓ N_H(U)) ⊔ P`
    have hMC_le : (twoPoint H t ⊓ Subgroup.normalizer ((U ⊔ P : Subgroup G) : Set G)) ⊓
          (H ⊓ Subgroup.normalizer (U : Set G) ⊓ Subgroup.normalizer (P : Set G)) ≤
        (A ⊓ Subgroup.centralizer (P : Set G) ⊓ Subgroup.normalizer (U : Set G)) ⊔ P := by
      have hP_le_NA : P ≤ Subgroup.normalizer ((A ⊓ Subgroup.centralizer (P : Set G)) : Set G) :=
        sec4_star_le_normalizer_of_le_centralizer inf_le_right
      have hprod : (↑((A ⊓ Subgroup.centralizer (P : Set G)) ⊔ P) : Set G) =
          ((A ⊓ Subgroup.centralizer (P : Set G) : Subgroup G) : Set G) * (P : Set G) :=
        Subgroup.coe_mul_of_right_le_normalizer_left
          (A ⊓ Subgroup.centralizer (P : Set G)) P hP_le_NA
      intro x hx
      obtain ⟨hxM, hxC⟩ := Subgroup.mem_inf.mp hx
      have hxTP : x ∈ twoPoint H t := (Subgroup.mem_inf.mp hxM).1
      have hxNP : x ∈ Subgroup.normalizer (P : Set G) := (Subgroup.mem_inf.mp hxC).2
      have hxNU : x ∈ Subgroup.normalizer (U : Set G) :=
        (Subgroup.mem_inf.mp (Subgroup.mem_inf.mp hxC).1).2
      have hxJP : x ∈ (A ⊓ Subgroup.centralizer (P : Set G)) ⊔ P := by
        have h1 : x ∈ twoPoint H t ⊓ Subgroup.normalizer (P : Set G) :=
          ⟨hxTP, hxNP⟩
        rwa [hNDP] at h1
      have hx' : x ∈ ((A ⊓ Subgroup.centralizer (P : Set G) : Subgroup G) : Set G) *
          (P : Set G) := by
        rw [← hprod]
        exact hxJP
      obtain ⟨a, ha, q, hq, haq⟩ := Set.mem_mul.mp hx'
      have hqNU : q ∈ Subgroup.normalizer (U : Set G) := hPU hq
      have haNU : a ∈ Subgroup.normalizer (U : Set G) := by
        have h3 : x * q⁻¹ ∈ Subgroup.normalizer (U : Set G) :=
          (Subgroup.normalizer (U : Set G)).mul_mem hxNU
            ((Subgroup.normalizer (U : Set G)).inv_mem hqNU)
        rw [← haq] at h3
        rwa [mul_assoc, mul_inv_cancel, mul_one] at h3
      rw [← haq]
      exact ((A ⊓ Subgroup.centralizer (P : Set G) ⊓ Subgroup.normalizer (U : Set G)) ⊔
        P).mul_mem (Subgroup.mem_sup_left ⟨ha, haNU⟩) (Subgroup.mem_sup_right hq)
    intro g hg
    -- `g` lies in `H ⊓ N(U ⊔ P) = S ⊔ N_D(U ⊔ P)`
    have hgH : g ∈ H := (Subgroup.mem_inf.mp (Subgroup.mem_inf.mp hg).1).1
    have hgNU : g ∈ Subgroup.normalizer (U : Set G) :=
      (Subgroup.mem_inf.mp (Subgroup.mem_inf.mp hg).1).2
    have hgNP : g ∈ Subgroup.normalizer (P : Set G) := (Subgroup.mem_inf.mp hg).2
    have hnin : Subgroup.normalizer (U : Set G) ⊓ Subgroup.normalizer (P : Set G) ≤
        Subgroup.normalizer ((U ⊔ P : Subgroup G) : Set G) :=
      sec4_star_normalizer_inf_le_normalizer_sup U P
    have hgNX : g ∈ Subgroup.normalizer ((U ⊔ P : Subgroup G) : Set G) :=
      hnin (Subgroup.mem_inf.mpr ⟨hgNU, hgNP⟩)
    have hgHNX : g ∈ H ⊓ Subgroup.normalizer ((U ⊔ P : Subgroup G) : Set G) :=
      Subgroup.mem_inf.mpr ⟨hgH, hgNX⟩
    have hgSM : g ∈ (S : Set G) *
        (twoPoint H t ⊓ Subgroup.normalizer ((U ⊔ P : Subgroup G) : Set G) : Set G) := by
      rw [← hSM, hSsup]
      exact hgHNX
    obtain ⟨s, hs, m, hm, hsm⟩ := Set.mem_mul.mp hgSM
    have hsC : s ∈ H ⊓ Subgroup.normalizer (U : Set G) ⊓
        Subgroup.normalizer (P : Set G) := hS_le_C hs
    have hmC : m ∈ H ⊓ Subgroup.normalizer (U : Set G) ⊓
        Subgroup.normalizer (P : Set G) := by
      have h2 : s⁻¹ * g ∈ H ⊓ Subgroup.normalizer (U : Set G) ⊓
          Subgroup.normalizer (P : Set G) :=
        (H ⊓ Subgroup.normalizer (U : Set G) ⊓
            Subgroup.normalizer (P : Set G)).mul_mem
          ((H ⊓ Subgroup.normalizer (U : Set G) ⊓
            Subgroup.normalizer (P : Set G)).inv_mem hsC) hg
      rw [← hsm] at h2
      rwa [← mul_assoc, inv_mul_cancel, one_mul] at h2
    have hmT : m ∈ (A ⊓ Subgroup.centralizer (P : Set G) ⊓
        Subgroup.normalizer (U : Set G)) ⊔ P := hMC_le ⟨hm, hmC⟩
    have hmBig : m ∈ (S ⊔ P) ⊔ (A ⊓ Subgroup.centralizer (P : Set G) ⊓
        Subgroup.normalizer (U : Set G)) :=
      (sup_le_sup (le_sup_right : P ≤ S ⊔ P) le_rfl)
        ((sup_comm (A ⊓ Subgroup.centralizer (P : Set G) ⊓
          Subgroup.normalizer (U : Set G)) P) ▸ hmT)
    rw [← hsm]
    exact ((S ⊔ P) ⊔ (A ⊓ Subgroup.centralizer (P : Set G) ⊓
      Subgroup.normalizer (U : Set G))).mul_mem
        (Subgroup.mem_sup_left (Subgroup.mem_sup_left hs)) hmBig
  · -- `(S ⊔ P) ⊔ (C_A(P) ⊓ N_H(U)) ≤ N_H(U) ⊓ N_H(P)`
    have hPE : P ≤ Design.Egrp H t W := h.P_le.trans inf_le_left
    have hPW : P ≤ W := hPE.trans inf_le_left
    have hPH : P ≤ H := hPW.trans h.le
    have hPC : P ≤ H ⊓ Subgroup.normalizer (U : Set G) ⊓
        Subgroup.normalizer (P : Set G) :=
      le_inf (le_inf hPH hPU) Subgroup.le_normalizer
    have hAC1 : A ⊓ Subgroup.centralizer (P : Set G) ⊓ Subgroup.normalizer (U : Set G) ≤ H :=
      inf_le_left.trans (inf_le_left.trans hAH)
    have hAC2 : A ⊓ Subgroup.centralizer (P : Set G) ⊓ Subgroup.normalizer (U : Set G) ≤
        Subgroup.normalizer (P : Set G) :=
      inf_le_left.trans (inf_le_right.trans (Subgroup.centralizer_le_normalizer (P : Set G)))
    have hAC : A ⊓ Subgroup.centralizer (P : Set G) ⊓ Subgroup.normalizer (U : Set G) ≤
        H ⊓ Subgroup.normalizer (U : Set G) ⊓ Subgroup.normalizer (P : Set G) :=
      le_inf (le_inf hAC1 inf_le_right) hAC2
    exact sup_le (sup_le hS_le_C hPC) hAC

/-- **Peterfalvi I Ch. III §4 Prop. 1, step 1** (p.180): the conclusion `Step1Conc H t p P A`
(`Submission/Work/NormalComplement/S5K/Defs.lean`), i.e. `C = C_A(P) = A ⊓ C_G(P)` is a Hall
subgroup of `N_H(P) = H ⊓ N_G(P)` and has a normal complement in `N_H(P)`.

Route (the source's step 1, p.180):
* For `1 ≠ U ≤ C_A(P)` one has `C_K(U) ≠ 1`, since `U ≤ A = C_V(K₁)` with `K₁ = N_K(X) ≠ 1`
  (`Setup45A.A_CK`, `Setup45A.A_B`).
* Formula (∗), `Work.NormalComplement.sec4_prop1_star` (proved), applied to this `U`, gives a
  2-subgroup `S₂ ≤ H` centralising `U` and `P` with
  `N_H(U) ⊓ N_H(P) = (S₂ ⊔ P) ⊔ (C_A(P) ⊓ N_H(U))`.
* Apply the Corollary of §1 Lemma 2 (`hCC : ControlCorollaryProp`) with `E = C_A(P)`,
  `W = H ⊓ N_G(P)`.  Its hypothesis is the displayed formula rewritten: with `π` the primes of
  `|E|` one has `S₂ ⊔ P ≤ O_{π'}(C_W(U))` because `E` has odd order (`E ≤ V = C_D(t)`, `D` odd)
  so `2 ∉ π`, and `p ∉ π` by `hPsyl`
  (`Work.NormalComplement.S5K.not_dvd_p_card_CA`, proved in `S5K/ca_coprime.lean`); normality of
  `S₂` in `C_W(U)` comes from `S₂ ≤ C_G(U) ⊓ C_G(P)` together with clause (b) of
  `ChIIFourP3SubnormalProp` re-applied to `X = U ⊔ P`, `Y = U`. -/
theorem prop1_step1 (hFT : Submission.Blueprint.FeitThompsonProp)
    (hP3 : Submission.Blueprint.ChIIFourP3SubnormalProp)
    (hCC : Work.NormalComplement.ControlCorollaryProp)
    {G : Type} [Group G] [Finite G] {H : Subgroup G} {t : G} {W : Subgroup G}
    {p : ℕ} {P A : Subgroup G}
    (h : Work.NormalComplement.Design.Setup45A G H t W p P A)
    (hPsyl : Work.NormalComplement.IsSylowIn p P (Submission.Blueprint.twoPoint H t)) :
    Work.NormalComplement.S5K.Step1Conc H t p P A := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  -- ## `E = C_A(P)` is odd, hence solvable by Feit–Thompson, and `2 ∉ π`
  have hDodd : Odd (Nat.card ↥(Submission.Blueprint.twoPoint H t)) := h.se.2.2 t h.notMem
  have hEodd : Odd (Nat.card ↥(A ⊓ Subgroup.centralizer (P : Set G))) :=
    Odd.of_dvd_nat hDodd
      (Subgroup.card_dvd_of_le ((inf_le_left.trans h.A_le).trans inf_le_left))
  have hEsolv : Group.IsSolvable ↥(A ⊓ Subgroup.centralizer (P : Set G)) :=
    hFT ↥(A ⊓ Subgroup.centralizer (P : Set G)) hEodd
  have hE2 : ¬ 2 ∣ Nat.card ↥(A ⊓ Subgroup.centralizer (P : Set G)) := hEodd.not_two_dvd_nat
  have hpE : ¬ p ∣ Nat.card ↥(A ⊓ Subgroup.centralizer (P : Set G)) := not_dvd_p_card_CA h hPsyl
  have hEW : A ⊓ Subgroup.centralizer (P : Set G) ≤ H ⊓ Subgroup.normalizer (P : Set G) :=
    le_inf ((inf_le_left.trans h.A_le).trans (inf_le_left.trans inf_le_left))
      (inf_le_right.trans (Subgroup.centralizer_le_normalizer (P : Set G)))
  -- ## the hypothesis of the Corollary of §1 Lemma 2, for `E = C_A(P)` and `W = N_H(P)`
  -- (written out rather than via `Work.NormalComplement.ControlHyp`, whose module `CCDefs` cannot
  -- be imported together with `sec4_prop1_star`: both pull in a duplicate
  -- `card_sup_mul_card_inf`)
  have hch :
      (∀ (q : ℕ) (U : Subgroup G), q.Prime →
          q ∣ Nat.card ↥(A ⊓ Subgroup.centralizer (P : Set G)) →
          U ≤ A ⊓ Subgroup.centralizer (P : Set G) → U ≠ ⊥ → IsPGroup q U →
        (H ⊓ Subgroup.normalizer (P : Set G)) ⊓ Subgroup.normalizer (U : Set G) =
          piPrimeCoreSub {r : ℕ | r ∣ Nat.card ↥(A ⊓ Subgroup.centralizer (P : Set G))}
            ((H ⊓ Subgroup.normalizer (P : Set G)) ⊓ Subgroup.centralizer (U : Set G)) ⊔
            ((A ⊓ Subgroup.centralizer (P : Set G)) ⊓ Subgroup.normalizer (U : Set G))) := by
    intro q U hq hqE hUE hUne hUq
    -- formula (∗), with the P3 clauses kept
    obtain ⟨S₂, hS₂p, hS₂H, hS₂cent, hS₂F, hS₂norm, hS₂eq⟩ :=
      sec4_prop1_star_strong hFT hP3 h U hUne hUE
    -- `P` commutes with `U`, and `P ≤ H`
    have hP_cent_U : P ≤ Subgroup.centralizer (U : Set G) :=
      Subgroup.le_centralizer_iff.mp (hUE.trans inf_le_right)
    have hPH : P ≤ H := h.P_le.trans (inf_le_right.trans (inf_le_left.trans inf_le_left))
    have hS₂_le_NP : S₂ ≤ Subgroup.normalizer (P : Set G) :=
      (hS₂cent.trans inf_le_right).trans (Subgroup.centralizer_le_normalizer (P : Set G))
    have hS₂_le_NH : S₂ ≤ H ⊓ Subgroup.normalizer (P : Set G) := le_inf hS₂H hS₂_le_NP
    have hP_le_N : P ≤ H ⊓ Subgroup.normalizer (P : Set G) := le_inf hPH Subgroup.le_normalizer
    have hR_le : S₂ ⊔ P ≤ (H ⊓ Subgroup.normalizer (P : Set G)) ⊓
        Subgroup.centralizer (U : Set G) :=
      sup_le (le_inf hS₂_le_NH (hS₂cent.trans inf_le_left)) (le_inf hP_le_N hP_cent_U)
    -- ## `S₂ ⊔ P` is normal in `C_{N_H(P)}(U)`
    have hX_le_NU : (H ⊓ Subgroup.normalizer (P : Set G)) ⊓ Subgroup.centralizer (U : Set G) ≤
        Subgroup.normalizer (U : Set G) :=
      inf_le_right.trans (Subgroup.centralizer_le_normalizer (U : Set G))
    have hX_le_NP : (H ⊓ Subgroup.normalizer (P : Set G)) ⊓ Subgroup.centralizer (U : Set G) ≤
        Subgroup.normalizer (P : Set G) :=
      inf_le_left.trans inf_le_right
    have hX_le_NX : (H ⊓ Subgroup.normalizer (P : Set G)) ⊓ Subgroup.centralizer (U : Set G) ≤
        Subgroup.normalizer ((U ⊔ P : Subgroup G) : Set G) :=
      (le_inf hX_le_NU hX_le_NP).trans
        (Work.NormalComplement.sec4_star_normalizer_inf_le_normalizer_sup U P)
    have hX_le_NS₂ : (H ⊓ Subgroup.normalizer (P : Set G)) ⊓ Subgroup.centralizer (U : Set G) ≤
        Subgroup.normalizer (S₂ : Set G) :=
      (le_inf (inf_le_left.trans inf_le_left) hX_le_NX).trans hS₂norm
    have hR_norm : (H ⊓ Subgroup.normalizer (P : Set G)) ⊓ Subgroup.centralizer (U : Set G) ≤
        Subgroup.normalizer ((S₂ ⊔ P : Subgroup G) : Set G) :=
      (le_inf hX_le_NS₂ hX_le_NP).trans
        (Work.NormalComplement.sec4_star_normalizer_inf_le_normalizer_sup S₂ P)
    -- ## `S₂ ⊔ P` is a `π'`-group, since `2 ∉ π` and `p ∉ π`
    have hRpi : Work.Fitting.IsPiNat
        (fun r => r ∉ {r : ℕ | r ∣ Nat.card ↥(A ⊓ Subgroup.centralizer (P : Set G))})
        (Nat.card ↥(S₂ ⊔ P)) := by
      intro r hr hrdvd
      obtain ⟨a, ha⟩ := IsPGroup.iff_card.mp hS₂p
      have hcardR : Nat.card ↥(S₂ ⊔ P) ∣ Nat.card ↥S₂ * Nat.card ↥P := by
        have h := Work.NormalComplement.card_sup_mul_card_inf (H := P) (K := S₂) hS₂_le_NP
        rw [sup_comm] at h
        exact ⟨Nat.card ↥(P ⊓ S₂), by
          rw [mul_comm (Nat.card ↥S₂) (Nat.card ↥P)]
          exact h.symm⟩
      have hdiv : r ∣ Nat.card ↥S₂ * Nat.card ↥P := hrdvd.trans hcardR
      rw [ha, h.P_card] at hdiv
      rcases hr.dvd_mul.mp hdiv with h2 | hp'
      · have hr2 : r = 2 := by
          rcases Nat.prime_two.eq_one_or_self_of_dvd r (hr.dvd_of_dvd_pow h2) with h1 | h1
          · exact absurd h1 hr.ne_one
          · exact h1
        rw [hr2]
        exact hE2
      · have hrp : r = p := (Nat.prime_dvd_prime_iff_eq hr h.prime).mp hp'
        rw [hrp]
        exact hpE
    have hR_core : S₂ ⊔ P ≤ piPrimeCoreSub
        {r : ℕ | r ∣ Nat.card ↥(A ⊓ Subgroup.centralizer (P : Set G))}
        ((H ⊓ Subgroup.normalizer (P : Set G)) ⊓ Subgroup.centralizer (U : Set G)) :=
      le_piPrimeCoreSub_of_normal_isPiNat hR_le hR_norm hRpi
    -- ## the displayed formula, rewritten
    have hLHS : (H ⊓ Subgroup.normalizer (P : Set G)) ⊓ Subgroup.normalizer (U : Set G) =
        (S₂ ⊔ P) ⊔ ((A ⊓ Subgroup.centralizer (P : Set G)) ⊓
          Subgroup.normalizer (U : Set G)) := by
      rw [← hS₂eq]
      ac_rfl
    rw [hLHS]
    refine le_antisymm ?_ ?_
    · exact sup_le (hR_core.trans le_sup_left) le_sup_right
    · refine sup_le ?_ le_sup_right
      exact (piPrimeCoreSub_le_self _ _).trans (hLHS ▸ le_inf inf_le_left
        (inf_le_right.trans (Subgroup.centralizer_le_normalizer (U : Set G))))
  -- ## the Corollary of §1 Lemma 2
  obtain ⟨hcop, N₀, hN₀le, hN₀norm, hN₀inf, hN₀sup⟩ :=
    hCC G (A ⊓ Subgroup.centralizer (P : Set G)) (H ⊓ Subgroup.normalizer (P : Set G))
      hEW hEsolv hch
  exact ⟨hcop, N₀, hN₀le, hN₀norm, hN₀inf, hN₀sup⟩

end Work.NormalComplement.S5K
