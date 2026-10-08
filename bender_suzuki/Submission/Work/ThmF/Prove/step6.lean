import Mathlib
import Submission.Work.ThmF.ChV3.Ctx
import Submission.Work.ThmF.ChV3.NearField
import Submission.Work.ThmF.Tools.External
import Submission.Work.ThmF.ChV3.step1
import Submission.Work.ThmF.ChV12.conj_action_data
import Submission.Work.ThmF.Prove.Step6.isPGroup_two_of_oddPart_eq_bot
import Submission.Work.ThmF.Prove.Step6.card_eq_one_or_three_of_odd_order_subgroup_mulAut
import Submission.Work.ThmF.Prove.Step6.eq_bot_of_odd_order_subgroup_mulAut_abelian_two_group
import Submission.Work.ThmF.Prove.Step6.arith_succ_eq_or_nine

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option linter.unusedVariables false

namespace Work.ThmF.Prove

open Classical

theorem step6 (hA : Work.ThmF.ArithmeticNineTwoSeven) {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t s r : G} {P : Subgroup G} (hFT : Submission.Blueprint.FeitThompsonProp) (hTh : Submission.Blueprint.ThompsonFrobeniusProp) (hNF : Work.ThmF.ChV3.NearFieldAppXIProp) (hC4 : Submission.Blueprint.ChIIFourProp) (c : Work.ThmF.ChV3.CtxF H Q t s r P) (h4 : Nat.card Q = Nat.card ↥(Work.ThmF.ChV3.CQ Q P) ^ Nat.card P) (h5 : ¬ IsMulCommutative ↥(Work.ThmF.ChV3.CQ Q P) → Nat.card ↥(Work.ThmF.ChV3.CQ Q P) = 8 ∧ Work.ThmF.oddPart Q = ⊥) (hQ1 : Work.ThmF.oddPart Q = ⊥) (hf : (orderOf (s * t)).Prime) (hlink : ∃ m : ℕ, 1 ≤ m ∧ Nat.card ↥(Work.ThmF.ChV3.CQ Q P) + 1 = orderOf (s * t) ^ m) (h7 : Work.ThmF.ChV3.Ker H Q P t = P) : (¬ IsMulCommutative ↥(Work.ThmF.ChV3.CQ Q P) → Nat.card ↥(Work.ThmF.ChV3.Sig H t P) = 1 ∨ Nat.card ↥(Work.ThmF.ChV3.Sig H t P) = 3) ∧ (IsMulCommutative ↥(Work.ThmF.ChV3.CQ Q P) → (Nat.card ↥(Work.ThmF.ChV3.CQ Q P) + 1 = orderOf (s * t) ∨ Nat.card ↥(Work.ThmF.ChV3.CQ Q P) + 1 = 9) ∧ Work.ThmF.ChV3.Sig H t P = ⊥) := by
  classical
  haveI : IsSimpleGroup G := c.simple
  -- ## 0. Standing facts
  have hsplit := c.split
  have hDodd : Odd (Nat.card ↥(Submission.Blueprint.twoPoint H t)) :=
    hsplit.stronglyEmbedded.2.2 t hsplit.not_mem
  have hWbot : Work.ThmF.W H t ⊓ P = ⊥ :=
    Work.ThmF.ChV3.W_inf_eq_bot_of_prime c.sit hC4 hsplit c.P_prime c.F1
  have hSigW : Work.ThmF.ChV3.Sig H t P ≤ Work.ThmF.W H t := inf_le_left
  have hSigC : Work.ThmF.ChV3.Sig H t P ≤ Subgroup.centralizer (P : Set G) := inf_le_right
  have hSigD : Work.ThmF.ChV3.Sig H t P ≤ Submission.Blueprint.twoPoint H t :=
    hSigW.trans ((Work.ThmF.W_le_centD H t).trans inf_le_left)
  have hSigOdd : Odd (Nat.card ↥(Work.ThmF.ChV3.Sig H t P)) :=
    hDodd.of_dvd_nat (Subgroup.card_dvd_of_le hSigD)
  -- ## 1. `Σ` normalises `C_Q(P)`
  have hfwd : ∀ x ∈ Work.ThmF.ChV3.Sig H t P,
      ∀ y ∈ Work.ThmF.ChV3.CQ Q P, x * y * x⁻¹ ∈ Work.ThmF.ChV3.CQ Q P := by
    intro x hx y hy
    have hxV : x ∈ Submission.Blueprint.centD H t := Work.ThmF.W_le_centD H t (hSigW hx)
    have hxH : x ∈ H := (Subgroup.mem_inf.mp (Subgroup.mem_inf.mp hxV).1).1
    have hxP : x ∈ Subgroup.centralizer (P : Set G) := hSigC hx
    have hyQ : y ∈ Q := (Subgroup.mem_inf.mp hy).1
    have hyP : y ∈ Subgroup.centralizer (P : Set G) := (Subgroup.mem_inf.mp hy).2
    refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
    · exact (Subgroup.mem_normalizer_iff.mp (hsplit.normal hxH) y).mp hyQ
    · rw [Subgroup.mem_centralizer_iff]
      intro p hp
      have h1 : p * x = x * p := Subgroup.mem_centralizer_iff.mp hxP p hp
      have h2 : p * y = y * p := Subgroup.mem_centralizer_iff.mp hyP p hp
      have h4 : x * p * x⁻¹ = p := by rw [← h1]; group
      calc p * (x * y * x⁻¹) = (x * p * x⁻¹) * (x * y * x⁻¹) := by rw [h4]
        _ = x * (p * y) * x⁻¹ := by group
        _ = x * (y * p) * x⁻¹ := by rw [h2]
        _ = (x * y * x⁻¹) * (x * p * x⁻¹) := by group
        _ = (x * y * x⁻¹) * p := by rw [h4]
  have hSigN : Work.ThmF.ChV3.Sig H t P ≤
      Subgroup.normalizer ((Work.ThmF.ChV3.CQ Q P : Subgroup G) : Set G) := by
    intro x hx
    rw [Subgroup.mem_normalizer_iff]
    intro y
    exact ⟨hfwd x hx y, fun hy => by
      have h := hfwd x⁻¹ ((Work.ThmF.ChV3.Sig H t P).inv_mem hx) (x * y * x⁻¹) hy
      rwa [show x⁻¹ * (x * y * x⁻¹) * (x⁻¹)⁻¹ = y from by group] at h⟩
  -- ## 2. the conjugation homomorphism `Σ → Aut(C_Q(P))` is injective
  let φ : ↥(Work.ThmF.ChV3.Sig H t P) →* MulAut ↥(Work.ThmF.ChV3.CQ Q P) :=
    Work.ThmF.ChV12.conjAutOfLe (Work.ThmF.ChV3.CQ Q P) (Work.ThmF.ChV3.Sig H t P) hSigN
  have hφker : φ.ker = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    rw [Subgroup.mem_bot]
    rw [MonoidHom.mem_ker] at hx
    have hxCQ : (x : G) ∈ Subgroup.centralizer
        ((Work.ThmF.ChV3.CQ Q P : Subgroup G) : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      have h1 : φ x ⟨y, hy⟩ = ⟨y, hy⟩ := by rw [hx, MulAut.one_apply]
      have h2 : ((φ x ⟨y, hy⟩ : ↥(Work.ThmF.ChV3.CQ Q P)) : G) = y :=
        congrArg Subtype.val h1
      have hval : ((φ x ⟨y, hy⟩ : ↥(Work.ThmF.ChV3.CQ Q P)) : G)
          = (x : G) * (⟨y, hy⟩ : ↥(Work.ThmF.ChV3.CQ Q P)) * (x : G)⁻¹ :=
        Work.ThmF.ChV12.conjAutOfLe_apply (Work.ThmF.ChV3.CQ Q P)
          (Work.ThmF.ChV3.Sig H t P) hSigN x ⟨y, hy⟩
      rw [hval] at h2
      have h3 : (x : G) * y = y * (x : G) := by
        have h3' : (x : G) * y * (x : G)⁻¹ = y := by simpa using h2
        calc (x : G) * y = ((x : G) * y * (x : G)⁻¹) * (x : G) := by group
          _ = y * (x : G) := by rw [h3']
      exact h3.symm
    have hxKer : (x : G) ∈ Work.ThmF.ChV3.Ker H Q P t :=
      Subgroup.mem_inf.mpr ⟨⟨hSigD x.2, hxCQ⟩, hSigC x.2⟩
    rw [h7] at hxKer
    have hxbot : (x : G) ∈ Work.ThmF.W H t ⊓ P := ⟨hSigW x.2, hxKer⟩
    rw [hWbot] at hxbot
    exact Subtype.ext (Subgroup.mem_bot.mp hxbot)
  have hφinj : Function.Injective φ := (MonoidHom.ker_eq_bot_iff φ).mp hφker
  have hcardrange : Nat.card ↥(φ.range) = Nat.card ↥(Work.ThmF.ChV3.Sig H t P) := by
    rw [show φ.range = Subgroup.map φ ⊤ from MonoidHom.range_eq_map φ,
      Subgroup.card_map_of_injective hφinj (K := ⊤), Subgroup.card_top]
  have hodd_range : Odd (Nat.card ↥(φ.range)) := by rw [hcardrange]; exact hSigOdd
  -- ## 3. assemble
  constructor
  · intro hnc
    obtain ⟨hCQ8, -⟩ := h5 hnc
    have hres := Work.ThmF.Prove.Step6.card_eq_one_or_three_of_odd_order_subgroup_mulAut
      (P := ↥(Work.ThmF.ChV3.CQ Q P)) hCQ8 hnc φ.range hodd_range
    rw [hcardrange] at hres
    exact hres
  · intro hcomm
    refine ⟨?_, ?_⟩
    · -- arithmetic
      haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      have hQ2 : IsPGroup 2 ↥Q :=
        Work.ThmF.Prove.Step6.isPGroup_two_of_oddPart_eq_bot Q hQ1
      have hCQ2 : IsPGroup 2 ↥(Work.ThmF.ChV3.CQ Q P) :=
        hQ2.to_le (inf_le_left : Work.ThmF.ChV3.CQ Q P ≤ Q)
      have hpow : ∃ b, Nat.card ↥(Work.ThmF.ChV3.CQ Q P) = 2 ^ b :=
        IsPGroup.iff_card.mp hCQ2
      exact Work.ThmF.Prove.Step6.arith_succ_eq_or_nine hf hpow hlink hA
    · -- `Σ = ⊥`
      haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      have hQ2 : IsPGroup 2 ↥Q :=
        Work.ThmF.Prove.Step6.isPGroup_two_of_oddPart_eq_bot Q hQ1
      have hCQ2 : IsPGroup 2 ↥(Work.ThmF.ChV3.CQ Q P) :=
        hQ2.to_le (inf_le_left : Work.ThmF.ChV3.CQ Q P ≤ Q)
      have hnf : ¬ Submission.Blueprint.HasFourGroup ↥(Work.ThmF.ChV3.CQ Q P) := by
        intro h
        apply c.F1
        obtain ⟨a, b, ha, hb, hne, hcom⟩ := h
        refine ⟨⟨(a : G), (Subgroup.mem_inf.mp a.2).2⟩,
          ⟨(b : G), (Subgroup.mem_inf.mp b.2).2⟩, ?_, ?_, ?_, ?_⟩
        · exact (Subgroup.orderOf_coe (⟨(a : G), (Subgroup.mem_inf.mp a.2).2⟩ :
            ↥(Subgroup.centralizer (P : Set G)))).symm.trans
              ((Subgroup.orderOf_coe a).trans ha)
        · exact (Subgroup.orderOf_coe (⟨(b : G), (Subgroup.mem_inf.mp b.2).2⟩ :
            ↥(Subgroup.centralizer (P : Set G)))).symm.trans
              ((Subgroup.orderOf_coe b).trans hb)
        · intro hh
          exact hne (Subtype.ext (congrArg
            (fun z : ↥(Subgroup.centralizer (P : Set G)) => (z : G)) hh))
        · apply Subtype.ext
          have := congrArg (fun z : ↥(Work.ThmF.ChV3.CQ Q P) => (z : G)) hcom
          simpa using this
      have hrangebot : φ.range = ⊥ :=
        Work.ThmF.Prove.Step6.eq_bot_of_odd_order_subgroup_mulAut_abelian_two_group
          hcomm hCQ2 hnf φ.range hodd_range
      have hcard1 : Nat.card ↥(Work.ThmF.ChV3.Sig H t P) = 1 := by
        rw [← hcardrange, hrangebot, Subgroup.card_bot]
      exact Subgroup.card_eq_one.mp hcard1

end Work.ThmF.Prove
