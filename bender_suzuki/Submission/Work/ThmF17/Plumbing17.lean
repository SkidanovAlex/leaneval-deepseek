import Mathlib
import Submission.Work.ThmF.ChV3.Step16ChainTail
import Submission.Work.ThmF.ChV3.NearFieldExp
import Submission.Work.ThmF.Prove.step8
import Submission.Work.ThmF.Prove.step9v13
import Submission.Work.ThmF.Prove.step10Wrapper
import Submission.Work.ThmF.Prove.n1NotDvdQ
import Submission.Work.ThmF.Prove.WfpfOddPart
import Submission.Work.ThmF.ChV12.lemma2b
import Submission.Work.ThmF.ChV12.lemma2a
import Submission.Work.ThmF.ChV3.Prove.chain15_aux_nohp
import Submission.Work.ThmF.ChV3.Prove.hpf_of_dvd_sig
import Submission.Work.ThmF.ChV3.Prove.hpf_of_not_dvd_sig
import Submission.Work.ThmF.ChV3.Prove.case102_of_steps
import Submission.Work.ThmF.ChV3.Prove.commV_mem_W
import Submission.Work.ThmF.ChV3.Prove.R_abelian
import Submission.Work.ThmF.ChV3.Prove.step11Out_of_data
import Submission.Work.ThmF17.ExpOfChain

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.ThmF17.Plumbing17` — the assembly of §3 with `NearFieldExpProp` removed

This is `ThmF/ChV3/Step16Plumbing.lean` (`ChV3Prop16` / `chV3Prop16`) with the input
`NearFieldFullAppXIProp` replaced by the bare shadow `NearFieldAppXIProp` — three edits:

* the input type of `ChV3Prop17` is `NearFieldAppXIProp`, not `NearFieldFullAppXIProp`;
* `hNF := hNF0` instead of `hNF := hNFfull.1`;
* l.160's `hexp := hNFfull.2 c h15 hpf` becomes
  `hexp := Work.ThmF17.exp_of_chain c h15 h7 hpf hcomm` (steps (7), (11) are in hand).

The mathematical content of the replacement is `Work.ThmF17.exp_of_chain`
(`ThmF17/ExpOfChain.lean`): the additive-group clause `NearFieldExpProp` of
`ChV3/NearFieldExp.lean` is *not* an App. XI input, it is a consequence of the chain.

Every other line is verbatim `Step16Plumbing.lean`; no file of the `ThmF` area is edited.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

open LeanEval.GroupTheory.Defs Submission.Blueprint

namespace Work.ThmF17

open Work.ThmF.ChV3 Work.ThmF

/-- `ChV3Prop17`: the §3 contradiction, with the named inputs the proved chain consumes — the
`NearFieldExpProp` clause of `ChV3Prop16` is gone. -/
def ChV3Prop17 : Prop :=
  ∀ {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t s r : G} {P : Subgroup G},
    FeitThompsonProp → ChIIFourProp → ThompsonFrobeniusProp →
    Work.ThmF.WielandtFixedPoint → Work.ThmF.HallWielandtProp →
    Work.ThmF.ArithmeticNineTwoSeven → NearFieldAppXIProp →
    AppXIProp2 → NearFieldFieldProp → HigmanProp →
    CtxF H Q t s r P → False

/-- **The assembly of §3**, i.e. steps (1)–(17) from the standing context and the named inputs. -/
theorem chV3Prop17 : ChV3Prop17 := by
  intro G _ _ H Q t s r P hFT hC4 hTh hW hHW hA hNF0 hXI2 hNFF hHig c
  classical
  -- ## App. XI Prop. 1: the shadow of step (2) and the additive-group clause of (11)
  have hNF : NearFieldAppXIProp := hNF0
  -- ## `Q` is nilpotent (Ch. V §1 Prop. 1 (b))
  have hnil : Group.IsNilpotent ↥Q :=
    Work.ThmF.ChV12.prop1b c.sit hC4 hTh H Q t c.split (CtxF.Kset_nontrivial c)
  -- ## steps (1)–(5)
  obtain ⟨h15⟩ := chain15 hFT hW hTh hNF hXI2 hC4 c
  -- ## step (7)
  have h7 : Ker H Q P t = P := ker_eq_P_of_chain15 hFT hTh hNF hNFF hC4 hnil c h15
  -- ## step (6) (both conjuncts)
  have h6full := fun (hQ1 : oddPart Q = ⊥) => step6_of_chain15 hA hFT hTh hNF hC4 c h15 hQ1 h7
  have h6 : oddPart Q = ⊥ → IsMulCommutative ↥(CQ Q P) → Sig H t P = ⊥ :=
    fun hQ1 hcomm => ((h6full hQ1).2 hcomm).2
  have h6a : oddPart Q = ⊥ → IsMulCommutative ↥(CQ Q P) → Sig H t P = ⊥ := h6
  have h6n : oddPart Q = ⊥ → ¬ IsMulCommutative ↥(CQ Q P) →
      Nat.card ↥(Sig H t P) = 1 ∨ Nat.card ↥(Sig H t P) = 3 :=
    fun hQ1 hnc => (h6full hQ1).1 hnc
  -- ## step (8)
  have h8 : oddPart Q ≠ ⊥ → Work.ThmF.Prove.Step8Out H Q t P :=
    fun hQ1 hSig => Work.ThmF.Prove.step8 hA hNFF hC4 hnil c h15 hQ1 hSig
  -- ## the cardinalities
  have hH : Nat.card ↥H = Nat.card Q * Nat.card ↥(twoPoint H t) := Work.ThmF.split_card_H c.split
  have hG : Nat.card G = (Nat.card Q + 1) * Nat.card ↥H := by
    have h := Work.ThmF.ChV12.card_G_eq c.split
    rw [← hH] at h
    rw [h]; ring
  have hV : Nat.card ↥(centD H t) = Nat.card ↥(W H t) * Nat.card P := by
    have h := Work.ThmF.ChV3.Prove.card_sup_of_le_normalizer (A := W H t) (B := P)
      (Work.ThmF.ChV3.Prove.P_le_normalizer_W (H := H) (t := t) c) h15.hWP
    rwa [h15.hV] at h
  have hPW : P ⊓ W H t = ⊥ := by rw [inf_comm]; exact h15.hWP
  have hVW := Work.ThmF.ChV3.Prove.commV_mem_W c h15
  -- ## §2 Lemma 2 b)
  have hL2b : ∀ X : Subgroup G, X ≤ centD H t → X ≠ ⊥ →
      Subgroup.normalizer (X : Set G) =
        Subgroup.centralizer (X : Set G) ⊔ (centD H t ⊓ Subgroup.normalizer (X : Set G)) :=
    fun X hX hXne => Work.ThmF.ChV12.lemma2b c.sit hC4 H Q t c.split X hX hXne
      (Work.ThmF.ChV12.lemma2a c.sit hC4 H Q t c.split X hX hXne)
  -- ## `p ∤ |Q|` and `W` fixed-point-free on `Q₁`
  have hQ : ¬ Nat.card P ∣ Nat.card Q := Work.ThmF.Prove.n1NotDvdQ hC4 hTh c h15.h3
  have hfpfW : ∀ w ∈ W H t, w ≠ 1 →
      oddPart Q ⊓ Subgroup.centralizer ({w} : Set G) = ⊥ :=
    fun w hw hw1 => Work.ThmF.Prove.WfpfOddPart hC4 hnil c h15.hQ0 w hw hw1
  -- ## `|D| = (2^p−1)|W|p` and `p ∤ |W| → p ∤ |Σ|` (the dead-weight `hpf` of the leaves)
  obtain ⟨hD, hSigW⟩ := Work.ThmF.ChV3.Prove.chain15_aux_nohp hC4 c h15
  -- ## step (9)
  have h9 : oddPart Q ≠ ⊥ → ¬ Nat.card P ∣ Nat.card ↥(Sig H t P) := by
    intro hQ1
    exact (Work.ThmF.Prove.step9v13 hC4 hTh hHW c h15.h3 (h8 hQ1) h15.hm h15.hcq h15.hf hQ1
      hG hH hD hV hPW hfpfW hVW hL2b).2
  -- ## `p = f` (step (9)/(10)), by cases on `p ∣ |Σ|`
  have hpf : Nat.card P = orderOf (s * t) := by
    by_cases hsig : Nat.card P ∣ Nat.card ↥(Sig H t P)
    · exact Work.ThmF.ChV3.Prove.hpf_of_dvd_sig c h15 h9 h6n h6a hsig
    · exact Work.ThmF.ChV3.Prove.hpf_of_not_dvd_sig hFT hC4 c h15 hG hH hD hQ hSigW hsig
  -- ## step (10)
  have hcq' : Nat.card ↥(CQ Q P) + 1 = Nat.card P ^ h15.m := by
    rw [hpf]; exact h15.hcq
  have hcase : Nat.card P ∣ Nat.card ↥(Sig H t P) →
      Nat.card P = 3 ∧ Nat.card ↥(CQ Q P) = 8 ∧ Nat.card ↥(Sig H t P) = 3 ∧
        (Nat.card ↥(W H t) = 3 ∨ Nat.card ↥(W H t) = 9) := by
    intro hsig
    obtain ⟨hp3, hs3, hc8, hW39, -, -⟩ :=
      Work.ThmF.ChV3.Prove.case102_of_steps hFT hC4 hHig c h15 h7 hpf h9 h6a h6n hsig
    exact ⟨hp3, hc8, hs3, hW39⟩
  have hWcyc : Nat.card P ∣ Nat.card ↥(Sig H t P) → IsCyclic ↥(W H t) :=
    fun hsig =>
      (Work.ThmF.ChV3.Prove.case102_of_steps hFT hC4 hHig c h15 h7 hpf h9 h6a h6n hsig).2.2.2.2.2
  have h10 : Case101 H t P h15.m ∨
      (Nat.card P = 3 ∧ Nat.card ↥(Sig H t P) = 3 ∧ Nat.card ↥(CQ Q P) = 8 ∧
        (Nat.card ↥(W H t) = 3 ∨ Nat.card ↥(W H t) = 9) ∧
        pPart 3 (Nat.card G) = 3 ^ 4 * Nat.card ↥(W H t)) :=
    Work.ThmF.Prove.step10Wrapper c hD hG hH h15.hm hcq' h15.h4 hSigW hcase
  -- ## step (11): `R` abelian, then `T` and the sharp-transitivity clause
  have hcomm : IsMulCommutative ↥h15.R :=
    Work.ThmF.ChV3.Prove.R_abelian hFT hC4 c h15 h7 hpf h10
  have hsZQ : ∀ q ∈ Q, q * s = s * q := by
    have hcentQ : s ∈ Work.ThmF.centerOf Q :=
      Work.ThmF.ChV12.prop1c c.sit H Q t c.split
        (Work.ThmF.Bender.DTransitiveInv (t := t) c.split.stronglyEmbedded c.split.invol
          c.split.not_mem)
        (Work.ThmF.L5.Q_nilpotent c.sit hC4 c.split) s ⟨c.split.le c.s_mem, c.s_inv⟩
    intro q hq
    exact (((Work.ThmF.mem_centerOf (Q := Q)).mp hcentQ).2 q hq).symm
  have hsC : ∀ y ∈ CQ Q P, y * s * y⁻¹ = s := by
    intro y hy
    rw [hsZQ y hy.1]
    simp
  have hsS : ∀ y ∈ Sig H t P, y * s * y⁻¹ = s := by
    have hVle : centD H t ≤ Subgroup.centralizer ({s} : Set G) :=
      Work.ThmF.Prove.centDLowerCentralizerS c.split c.s_mem c.s_inv c.r_mem c.sid
    intro y hy
    have hyV : y ∈ centD H t := (Subgroup.mem_inf.mp (Subgroup.mem_inf.mp hy).1).1
    have hcomm' : y * s = s * y :=
      Subgroup.mem_centralizer_singleton_iff.mp (hVle hyV)
    rw [hcomm']
    simp
  have hexp : ∀ x ∈ h15.R, x ^ Nat.card P = 1 := Work.ThmF17.exp_of_chain c h15 h7 hpf hcomm
  obtain ⟨T, h11⟩ :=
    Work.ThmF.ChV3.Prove.step11Out_of_data hFT hC4 c h15 h7 hpf hcomm hsC hsS hexp
  -- ## steps (12)–(17)
  exact chain_tail hFT hC4 hHW c h15 h7 hpf h11 h6 h8 hH hD hQ hSigW hWcyc h10

end Work.ThmF17

#print axioms Work.ThmF17.chV3Prop17
