import Mathlib
import Submission.Work.ThmF.ChV3.Step16Defs
import Submission.Work.ThmF.ChV3.Chain17
import Submission.Work.ThmF.ChV3.Prove.card_sup_of_le_normalizer
import Submission.Work.ThmF.ChV3.Prove.S1_CH_aux

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.ThmF.ChV3.Prove.S1_CH_card` — step (1) of Peterfalvi II Ch. V §3

The cardinality of the centraliser of `P` inside the Bender subgroup `H`:

  `|C_H(P)| = |C_Q(P)| · |Σ| · |P|`,   where `Σ = C_W(P)` and `C_Q(P) = Q ⊓ C_G(P)`.

As the syntax already announces (all three factors are displayed as subgroups, and the source
computes `C_H(P)` as the direct product `C_Q(P) Σ P`), the content is split into two halves:

* **Group-theoretic half.**  `C_H(P)` *is* the join `C_Q(P) ⊔ (Σ ⊔ P)`.  For `≤`, write
  `x ∈ C_H(P)` in the split factorisation `x = d * q` (`H = D · Q` with `D = H ⊓ Hᵗ`,
  `Setup.split_exists_unique_factor`) and let `p ∈ P`; from `p * x = x * p` one gets
  `q p q⁻¹ = d⁻¹ p d`, and both `(q p q⁻¹) p⁻¹ ∈ Q` (as `p` normalises `Q`) and
  `(d⁻¹ p d) p⁻¹ ∈ D` (as `d, p ∈ D`), so this "commutator" dies in `Q ⊓ D = ⊥`: `d`
  centralises `P`.  Then `q = d⁻¹ x` centralises `P` as well, so `d ∈ D ⊓ C_G(P) = Σ ⊔ P`
  (step (1) of the chain, `Chain15.h1e`) and `q ∈ C_Q(P)`.  For `≥` each of
  `C_Q(P), Σ, P` is contained in `H ⊓ C_G(P)` (for `P` because `P` has prime order, hence is
  cyclic and commutative).
* **Counting half.**  `C_Q(P) ⊓ (Σ ⊔ P) = ⊥` and `Σ ⊔ P ≤ N_G(C_Q(P))`
  (`Prove.S1_CH_aux`), so `|C_Q(P) ⊔ (Σ ⊔ P)| = |C_Q(P)| · |Σ ⊔ P|`
  (`Prove.card_sup_of_le_normalizer`); and `Σ ⊓ P = ⊥` with `Σ ≤ C_G(P)` gives
  `|Σ ⊔ P| = |Σ| · |P|`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

open LeanEval.GroupTheory.Defs Submission.Blueprint

namespace Work.ThmF.ChV3.Prove

open Work.ThmF.ChV3 Submission.Blueprint

theorem S1_CH_card {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t s r : G} {P : Subgroup G}
    (c : Work.ThmF.ChV3.CtxF H Q t s r P) (h15 : Work.ThmF.ChV3.Chain15 H Q t s r P) :
    Nat.card ↥(H ⊓ Work.ThmF.ChV3.CG P) =
      Nat.card ↥(Work.ThmF.ChV3.CQ Q P) * Nat.card ↥(Work.ThmF.ChV3.Sig H t P) * Nat.card P := by
  classical
  -- ## basic containments
  have hD_le_H : twoPoint H t ≤ H := inf_le_left
  have hP_le_D : P ≤ twoPoint H t := c.P_le.trans (Work.ThmF.centD_le_twoPoint t)
  have hP_le_H : P ≤ H := hP_le_D.trans hD_le_H
  have hS_le_W : Sig H t P ≤ Work.ThmF.W H t := inf_le_left
  have hS_le_D : Sig H t P ≤ twoPoint H t :=
    hS_le_W.trans ((Work.ThmF.W_le_centD H t).trans (Work.ThmF.centD_le_twoPoint t))
  have hS_le_H : Sig H t P ≤ H := hS_le_D.trans hD_le_H
  have hS_le_C : Sig H t P ≤ CG P := inf_le_right
  have hC_le_Q : CQ Q P ≤ Q := inf_le_left
  have hC_le_H : CQ Q P ≤ H := hC_le_Q.trans c.split.le
  have hC_le_C : CQ Q P ≤ CG P := inf_le_right
  -- `P` has prime order, hence is cyclic and commutative, hence centralises itself
  have hP_le_C : P ≤ CG P := by
    haveI : Fact (Nat.card P).Prime := ⟨c.P_prime⟩
    haveI : IsCyclic ↥P := isCyclic_of_prime_card rfl
    exact Subgroup.le_centralizer P
  -- ## the group-theoretic half: `C_H(P) = C_Q(P) ⊔ (Σ ⊔ P)`
  have hEq : H ⊓ CG P = CQ Q P ⊔ (Sig H t P ⊔ P) := by
    apply le_antisymm
    · -- every element of `C_H(P)` factors through `C_Q(P)` and `C_D(P) = Σ P`
      rintro x ⟨hxH, hxC⟩
      obtain ⟨⟨d, q⟩, ⟨hdD, hqQ, hdq⟩, huniq⟩ := Work.ThmF.split_exists_unique_factor c.split hxH
      -- `d` centralizes `P`
      have hdC : d ∈ CG P := by
        rw [Subgroup.mem_centralizer_iff]
        intro p hp
        have hpD : p ∈ twoPoint H t := hP_le_D hp
        have hpH : p ∈ H := hP_le_H hp
        have hcomm : p * x = x * p := (Subgroup.mem_centralizer_iff.mp hxC) p hp
        -- the two conjugates of `p` coincide: `q p q⁻¹ = d⁻¹ p d`
        have hpq : q * p * q⁻¹ = d⁻¹ * p * d := by
          have h1 : d * q * p = p * (d * q) := by rw [hdq]; exact hcomm.symm
          have h2 : d * (q * p * q⁻¹) = d * (d⁻¹ * p * d) := by
            calc d * (q * p * q⁻¹) = (d * q * p) * q⁻¹ := by group
              _ = (p * (d * q)) * q⁻¹ := by rw [h1]
              _ = p * d := by group
              _ = d * (d⁻¹ * p * d) := by group
          exact mul_left_cancel h2
        -- the "commutator" `(d⁻¹ p d) p⁻¹` lies in `D` and in `Q`, hence is trivial
        have huD : (d⁻¹ * p * d) * p⁻¹ ∈ twoPoint H t :=
          (twoPoint H t).mul_mem
            (show d⁻¹ * p * d ∈ twoPoint H t from
              (twoPoint H t).mul_mem
                (show d⁻¹ * p ∈ twoPoint H t from
                  (twoPoint H t).mul_mem ((twoPoint H t).inv_mem hdD) hpD)
                hdD)
            ((twoPoint H t).inv_mem hpD)
        have huQ : (d⁻¹ * p * d) * p⁻¹ ∈ Q := by
          have hpN : p ∈ Subgroup.normalizer (Q : Set G) := c.split.normal hpH
          have h1 : p * q⁻¹ * p⁻¹ ∈ Q :=
            (Subgroup.mem_normalizer_iff.mp hpN q⁻¹).mp (Q.inv_mem hqQ)
          have h2 : q * (p * q⁻¹ * p⁻¹) ∈ Q := Q.mul_mem hqQ h1
          have h3 : q * (p * q⁻¹ * p⁻¹) = (d⁻¹ * p * d) * p⁻¹ := by
            rw [show q * (p * q⁻¹ * p⁻¹) = (q * p * q⁻¹) * p⁻¹ by group, hpq]
          rwa [h3] at h2
        have hu1 : (d⁻¹ * p * d) * p⁻¹ = 1 := by
          have hmem : (d⁻¹ * p * d) * p⁻¹ ∈ Q ⊓ twoPoint H t := ⟨huQ, huD⟩
          rw [Work.ThmF.split_inf_eq c.split] at hmem
          exact Subgroup.mem_bot.mp hmem
        have hdd : d⁻¹ * p * d = p := mul_inv_eq_one.mp hu1
        have h4 : d * (d⁻¹ * p * d) = d * p := by rw [hdd]
        rwa [show d * (d⁻¹ * p * d) = p * d by group] at h4
      -- `q = d⁻¹ x` centralizes `P` too
      have hqC : q ∈ CG P := by
        have hqx : q = d⁻¹ * x := by rw [← hdq]; group
        rw [hqx]
        exact (CG P).mul_mem ((CG P).inv_mem hdC) hxC
      have hd_mem : d ∈ Sig H t P ⊔ P := by
        rw [← h15.h1e]
        exact ⟨hdD, hdC⟩
      have hq_mem : q ∈ CQ Q P := ⟨hqQ, hqC⟩
      rw [← hdq]
      exact (CQ Q P ⊔ (Sig H t P ⊔ P)).mul_mem
        ((le_sup_right : (Sig H t P ⊔ P) ≤ CQ Q P ⊔ (Sig H t P ⊔ P)) hd_mem)
        ((le_sup_left : CQ Q P ≤ CQ Q P ⊔ (Sig H t P ⊔ P)) hq_mem)
    · -- the reverse inclusion
      intro x hx
      exact Subgroup.mem_inf.mpr
        ⟨(sup_le hC_le_H (sup_le hS_le_H hP_le_H)) hx,
         (sup_le hC_le_C (sup_le hS_le_C hP_le_C)) hx⟩
  -- ## the counting half
  obtain ⟨hN1, hbot1, hbot2⟩ := S1_CH_aux c h15
  have hPinfSig : P ⊓ Sig H t P = ⊥ := by rw [inf_comm]; exact hbot2
  have hSig_le_NP : Sig H t P ≤ Subgroup.normalizer (P : Set G) := by
    rw [Subgroup.le_normalizer_iff]
    intro y hy p hp
    have h : p * y = y * p := (Subgroup.mem_centralizer_iff.mp (hS_le_C hy)) p hp
    have hy' : y * p * y⁻¹ = p := by
      calc y * p * y⁻¹ = p * y * y⁻¹ := by rw [← h]
        _ = p := by group
    rw [hy']; exact hp
  have hSigP_card : Nat.card ↥(Sig H t P ⊔ P) = Nat.card ↥(Sig H t P) * Nat.card ↥P := by
    rw [sup_comm]
    rw [card_sup_of_le_normalizer (A := P) (B := Sig H t P) hSig_le_NP hPinfSig, mul_comm]
  rw [hEq, card_sup_of_le_normalizer (A := CQ Q P) (B := Sig H t P ⊔ P) hN1 hbot1,
    hSigP_card, mul_assoc]

end Work.ThmF.ChV3.Prove
