import Submission.ZagierHoffmanProof.StepL46
import Submission.ZagierHoffmanProof.StepL48
import Submission.ZagierHoffmanProof.StepL29
import Submission.ZagierHoffmanProof.StepC
set_option autoImplicit false
set_option maxHeartbeats 100000000
open Polynomial RatFunc
open scoped BigOperators
/-!
# Step L103: G5T_case1 order lemmas — g5T1_aSide_order / g5T1_bSide_order (SESSION 253)

The two ORDER lemmas of the level-2 j=0 chain ((q, s₂>q, …): 2 ≤ r, s₀ = q,
s₁ > q; D := BCqIter F 1 (toData R0)):
  • g5T1_aSide_order (r s hcase hs0v hbigv R0 u hpref) : ∀ i ≠ u ℓ ≥ 2,
      psum (D.cA i) ℓ ≤ psum s ℓ   [psum(D.cA i)ℓ = q + psum(R0.cA i)(ℓ−1);
      hpref + lemma29_qExp_telescope at k=2: X(ℓ−1) = s⟨1⟩ + (psum s ℓ − psum s 2);
      q + s⟨1⟩ = psum s 2]
  • g5T1_bSide_order (r s hcase hs0v hbigv R0 hbhd hbndB) : ∀ p ℓ ≥ 2,
      psum (D.cB p) ℓ ≤ psum s ℓ   [one iterate layer: D.cB p = consVec oneExp
      (X.c p.2), X := p2WpT(q−1, R0.cB p.1); ℓ=2 via the front-bound ≤ q+1 ≤ q+s₁;
      ℓ≥3 via 1 + (q−1) + [1 + (s₁−1) + (psum s(ℓ−1) − psum s 2)] =
      psum s 2 + (…) ≤ psum s (ℓ−1) ≤ psum s ℓ]
(ports of StepL85's g53c1_aSide_order/bSide_order at k=2 with s₁ > q, one front q.)
These + ℓ > r weight saturation form G5T_case1's horder.
theorem_B/D remain ABP-gated (no route).
-/

namespace ZagierHoffmanPositiveChar
attribute [instance] P2Data.fin
attribute [instance] RelData.finA
attribute [instance] RelData.finB
attribute [instance] FixedRel.fin
attribute [local instance] Classical.propDecidable
variable (F : Type*) [Field F] [Finite F] [DecidableEq (RatFunc F)]

theorem g5T1_aSide_order (r : ℕ) (s : Fin r → ℕ+) (hcase : 2 ≤ r)
    (hs0v : (s ⟨0, by omega⟩ : ℕ) = Nat.card F)
    (hbigv : (Nat.card F : ℕ) < (s ⟨1, by omega⟩ : ℕ))
    (R0 : BinaryRel F) (u : R0.ιA)
    (hpref : ∀ i : R0.ιA, i ≠ u → ∀ m : ℕ,
      psum (R0.cA i) m ≤ psumSeq (tupPadSum (single (qExp F))
        (consVec (w1Of F r s 2 (by omega : 1 ≤ 2) hcase hbigv) (sTail r s 2 hcase))) m) :
    let D := RelData.BCqIter F 1 (toData F R0)
    ∀ i : R0.ιA, i ≠ u → ∀ ℓ : ℕ, 2 ≤ ℓ → psum (D.cA i) ℓ ≤ psum s ℓ := by
  classical
  intro D i hi ℓ hℓ2
  have hcA : D.cA i = consVec (qExp F) (R0.cA i) := by
    dsimp [D, RelData.BCqIter, RelData.BCq]
    rfl
  have hsplit : psum (D.cA i) ℓ = (qExp F : ℕ) + psum (R0.cA i) (ℓ - 1) := by
    change psum (consVec (qExp F) (R0.cA i)) ℓ = (qExp F : ℕ) + psum (R0.cA i) (ℓ - 1)
    have hℓ1 : ℓ = (ℓ - 1) + 1 := by omega
    rw [hℓ1]
    rw [psum_consVec (qExp F) (R0.cA i) (ℓ - 1)]
    rfl
  have hpre := hpref i hi (ℓ - 1)
  have htel := lemma29_qExp_telescope F r s 2 (by omega : 1 ≤ 2) hcase hbigv (ℓ - 1) (by omega : 1 ≤ ℓ - 1)
  have htel' : psumSeq (tupPadSum (single (qExp F))
        (consVec (w1Of F r s 2 (by omega : 1 ≤ 2) hcase hbigv) (sTail r s 2 hcase))) (ℓ - 1) =
      (s ⟨1, by omega⟩ : ℕ) + (psum s ℓ - psum s 2) := by
    rw [htel]
    congr 1
    have hidx : 2 + (ℓ - 1) - 1 = ℓ := by omega
    rw [hidx]
  have hb : psum (R0.cA i) (ℓ - 1) ≤ (s ⟨1, by omega⟩ : ℕ) + (psum s ℓ - psum s 2) := by
    rw [← htel']
    exact hpre
  have hp2 : psum s 2 = (qExp F : ℕ) + (s ⟨1, by omega⟩ : ℕ) := by
    change (∑ j ∈ Finset.range 2, pad0 s j) = (qExp F : ℕ) + (s ⟨1, by omega⟩ : ℕ)
    rw [Finset.sum_range_succ, Finset.sum_range_succ]
    simp
    rw [pad0_of_lt s (by omega : 0 < r)]
    rw [pad0_of_lt s (by omega : 1 < r)]
    rw [hs0v]
    rw [← show (qExp F : ℕ) = Nat.card F by rfl]
  rw [hsplit]
  have hmono2 : psum s 2 ≤ psum s ℓ := psum_mono s hℓ2
  omega

theorem g5T1_bSide_order (r : ℕ) (s : Fin r → ℕ+) (hcase : 2 ≤ r)
    (hs0v : (s ⟨0, by omega⟩ : ℕ) = Nat.card F)
    (hbigv : (Nat.card F : ℕ) < (s ⟨1, by omega⟩ : ℕ))
    (R0 : BinaryRel F)
    (hbhd : ∀ j' : R0.ιB, ((R0.cB j') ⟨0, R0.hdepB j'⟩ : ℕ) = 1)
    (hbndB : ∀ j' : R0.ιB, ∀ m : ℕ,
      psum (expTail (R0.cB j')) m ≤ psumSeq (tupPadSum (single (qMinusExp F))
        (consVec (w1Of F r s 2 (by omega : 1 ≤ 2) hcase hbigv) (sTail r s 2 hcase))) m) :
    let D := RelData.BCqIter F 1 (toData F R0)
    ∀ p : D.ιB, ∀ ℓ : ℕ, 2 ≤ ℓ → psum (D.cB p) ℓ ≤ psum s ℓ := by
  classical
  intro D p ℓ hℓ2
  let X := p2WpT F (qMinusExp F) (R0.hdepB p.1) (R0.cB p.1)
  have hcB : D.cB p = consVec oneExp (X.c p.2) := by
    dsimp [D, RelData.BCqIter, RelData.BCq, X]
    rfl
  have hp2 : psum s 2 = (qExp F : ℕ) + (s ⟨1, by omega⟩ : ℕ) := by
    change (∑ j ∈ Finset.range 2, pad0 s j) = (qExp F : ℕ) + (s ⟨1, by omega⟩ : ℕ)
    rw [Finset.sum_range_succ, Finset.sum_range_succ]
    simp
    rw [pad0_of_lt s (by omega : 0 < r)]
    rw [pad0_of_lt s (by omega : 1 < r)]
    rw [hs0v]
    rw [← show (qExp F : ℕ) = Nat.card F by rfl]
  by_cases hℓ2e : ℓ = 2
  · subst ℓ
    -- psum(D.cB p) 2 = 1 + X-first ≤ 1 + (q−1) + R0-head = q+1 ≤ q + s₁ = psum s 2
    have hL1 : psum (D.cB p) 2 = (1 : ℕ) + psum (X.c p.2) 1 := by
      rw [hcB]
      change psum (consVec oneExp (X.c p.2)) 2 = (1 : ℕ) + psum (X.c p.2) 1
      rw [psum_consVec oneExp (X.c p.2) 1]
      rfl
    have hL1le : psum (X.c p.2) 1 ≤ psumSeq (tupPadSum (single (qMinusExp F)) (R0.cB p.1)) 1 := by
      exact (X.hle p.2).2 1
    have hsplit1 : psumSeq (tupPadSum (single (qMinusExp F)) (R0.cB p.1)) 1 =
        (qMinusExp F : ℕ) + (1 : ℕ) := by
      rw [psumSeq_tupPadSum_split (single (qMinusExp F)) (R0.cB p.1) 1]
      have hsa : psum (single (qMinusExp F)) 1 = (qMinusExp F : ℕ) := by
        exact psum_single_of_pos (qMinusExp F) (by omega : 0 < 1)
      rw [hsa]
      have hpb : psum (R0.cB p.1) 1 = (1 : ℕ) := by
        change (∑ j ∈ Finset.range 1, pad0 (R0.cB p.1) j) = (1 : ℕ)
        simp
        rw [pad0_of_lt (R0.cB p.1) (R0.hdepB p.1)]
        exact hbhd p.1
      rw [hpb]
    have hq : (qMinusExp F : ℕ) = Nat.card F - 1 := rfl
    have hq0 : (qExp F : ℕ) = Nat.card F := rfl
    have hgoal : psum (D.cB p) 2 ≤ psum s 2 := by
      rw [hL1]
      have hNat : (qMinusExp F : ℕ) + 1 = Nat.card F := by
        change (Nat.card F - 1) + 1 = Nat.card F
        have hq : 1 ≤ Nat.card F := by
          have h2 := card_ge_two F
          omega
        omega
      have hb1 : psum (X.c p.2) 1 ≤ Nat.card F := by
        have hb0 : psum (X.c p.2) 1 ≤ (qMinusExp F : ℕ) + 1 := le_trans hL1le (by rw [hsplit1])
        rw [hNat] at hb0
        exact hb0
      have hq0 : (qExp F : ℕ) = Nat.card F := rfl
      have h1s : 1 ≤ (s ⟨1, by omega⟩ : ℕ) := (s ⟨1, by omega⟩).pos
      rw [hp2]
      rw [hq0]
      omega
    exact hgoal
  · -- ℓ ≥ 3
    have hℓ3 : 3 ≤ ℓ := by omega
    have hL : psum (D.cB p) ℓ = (1 : ℕ) + psum (X.c p.2) (ℓ - 1) := by
      rw [hcB]
      change psum (consVec oneExp (X.c p.2)) ℓ = (1 : ℕ) + psum (X.c p.2) (ℓ - 1)
      have hℓ1 : ℓ = (ℓ - 1) + 1 := by omega
      rw [hℓ1]
      rw [psum_consVec oneExp (X.c p.2) (ℓ - 1)]
      rfl
    have hLle : psum (X.c p.2) (ℓ - 1) ≤
        psumSeq (tupPadSum (single (qMinusExp F)) (R0.cB p.1)) (ℓ - 1) := by
      exact (X.hle p.2).2 (ℓ - 1)
    have hsplit : psumSeq (tupPadSum (single (qMinusExp F)) (R0.cB p.1)) (ℓ - 1) =
        (qMinusExp F : ℕ) + psum (R0.cB p.1) (ℓ - 1) := by
      rw [psumSeq_tupPadSum_split (single (qMinusExp F)) (R0.cB p.1) (ℓ - 1)]
      have hsa : psum (single (qMinusExp F)) (ℓ - 1) = (qMinusExp F : ℕ) := by
        exact psum_single_of_pos (qMinusExp F) (by omega : 0 < ℓ - 1)
      rw [hsa]
    have hR0 : psum (R0.cB p.1) (ℓ - 1) = (1 : ℕ) + psum (expTail (R0.cB p.1)) (ℓ - 2) := by
      have hh := psum_head_expTail (R0.hdepB p.1) (R0.cB p.1) (ℓ - 2)
      have hℓ2' : (ℓ - 2) + 1 = ℓ - 1 := by omega
      rw [hℓ2'] at hh
      have hhead : (((R0.cB p.1) ⟨0, R0.hdepB p.1⟩ : ℕ)) = 1 := hbhd p.1
      rw [hh, hhead]
    have hbnd := hbndB p.1 (ℓ - 2)
    have htel := lemma29_X_telescope F r s 2 (by omega : 1 ≤ 2) hcase hbigv (ℓ - 2) (by omega : 1 ≤ ℓ - 2)
    have htel' : psumSeq (tupPadSum (single (qMinusExp F))
          (consVec (w1Of F r s 2 (by omega : 1 ≤ 2) hcase hbigv) (sTail r s 2 hcase))) (ℓ - 2) =
        ((s ⟨1, by omega⟩ : ℕ) - 1) + (psum s (ℓ - 1) - psum s 2) := by
      rw [htel]
      congr 1
      have hidx : 2 + (ℓ - 2) - 1 = ℓ - 1 := by omega
      rw [hidx]
    have hEt : psum (expTail (R0.cB p.1)) (ℓ - 2) ≤
        ((s ⟨1, by omega⟩ : ℕ) - 1) + (psum s (ℓ - 1) - psum s 2) := by
      rw [← htel']
      exact hbnd
    have hB : psum (R0.cB p.1) (ℓ - 1) ≤
        (1 : ℕ) + (((s ⟨1, by omega⟩ : ℕ) - 1) + (psum s (ℓ - 1) - psum s 2)) := by
      calc
        psum (R0.cB p.1) (ℓ - 1) = (1 : ℕ) + psum (expTail (R0.cB p.1)) (ℓ - 2) := hR0
        _ ≤ (1 : ℕ) + (((s ⟨1, by omega⟩ : ℕ) - 1) + (psum s (ℓ - 1) - psum s 2)) := by
              exact Nat.add_le_add_left hEt (1 : ℕ)
    have hmain : psum (D.cB p) ℓ ≤ psum s (ℓ - 1) := by
      calc
        psum (D.cB p) ℓ = (1 : ℕ) + psum (X.c p.2) (ℓ - 1) := hL
        _ ≤ (1 : ℕ) + psumSeq (tupPadSum (single (qMinusExp F)) (R0.cB p.1)) (ℓ - 1) := by
              exact Nat.add_le_add_left hLle (1 : ℕ)
        _ = (1 : ℕ) + ((qMinusExp F : ℕ) + psum (R0.cB p.1) (ℓ - 1)) := by rw [hsplit]
        _ ≤ (1 : ℕ) + ((qMinusExp F : ℕ) +
              ((1 : ℕ) + (((s ⟨1, by omega⟩ : ℕ) - 1) + (psum s (ℓ - 1) - psum s 2)))) := by
              have hle := Nat.add_le_add_left hB ((1 : ℕ) + (qMinusExp F : ℕ))
              omega
        _ ≤ psum s (ℓ - 1) := by
              have hq : (qMinusExp F : ℕ) = Nat.card F - 1 := rfl
              have hq0 : (qExp F : ℕ) = Nat.card F := rfl
              have hq2 : 2 ≤ Nat.card F := card_ge_two F
              have hmono2 : psum s 2 ≤ psum s (ℓ - 1) := psum_mono s (by omega : 2 ≤ ℓ - 1)
              have hAbs : (1 : ℕ) + (Nat.card F - 1) + (1 : ℕ) ≤ psum s 2 := by
                rw [hp2]
                rw [hq0]
                omega
              omega
    have hmono' : psum s (ℓ - 1) ≤ psum s ℓ := psum_mono s (by omega : ℓ - 1 ≤ ℓ)
    omega

end ZagierHoffmanPositiveChar
