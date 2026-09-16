import Submission.ZagierHoffmanProof.StepL78
set_option autoImplicit false
set_option maxHeartbeats 100000000
open Polynomial RatFunc
open scoped BigOperators
namespace ZagierHoffmanPositiveChar
/-!
# Step L79: CASE-1 j=0 b-side member facts (SESSION 227)

The b-members of the CASE-1 empty-front chain (D := BCqIter F 1 (toData R0),
p : D.ιB) are consVec oneExp over the p2WpT(q−1, R0.cB p.1)-stuffle outputs:
  ★ g5c1_bSide_weight (… hbhd hXw) : weight (D.depB p)(D.cB p) = weight r s —
      via weight_consVec + the stuffle LePad weight + R0 b-tuple weight = psum r −
      psum 1 (g5c1_R0_b_weight: weight_head_tail (StepL32) head-1 split + hXw);
  ★ g5c1_b_fiber_front_le : the stuffle outputs' first entry ≤ (q−1) + head = q
      (p2WpT_front_le + hbhd);
  ★ g5c1_b_fiber_dep_ge_two : stuffle outputs have depth ≥ 2 — a depth-1 output of
      weight (q−1)+(psum r−psum 1) = w−1 would violate the prefix bound (q−1)+1,
      since w ≥ q+2 (case1_weight_ge_q_add_two);
  ★ g5c1_bSide_twoAdm : ∀ p, kAdmissible q (D.cB p) 2 — via kAdm2_cons_one
      (StepL75's generic (1::t) lemma) with depth ≥ 3 and the front bound.
CONSEQUENCE: every b-member of the CASE-1 j=0 chain is 2-admissible (self-dispatch).
LEAN: the R0 b-facts are over j : (toData R0).ιB with R0-forms inside (change-based);
the closing arithmetic needs explicit psum-value equalities (psum 1 = q, psum r =
weight r s) — omega cannot see psum/weight values on its own.
NEXT: (c) the g5 recursion: g5_total = l2_induction over in-domain head-q weight-w
tuples; step: inDomain2_cases — CASE-1 (2 ≤ r ∧ q < pad0 s 1): g5c1_zeta's members
(a ≠ u: by_cases 2-adm → admExp_self / ¬2-adm → 1-adm + prefix-2-drop (StepL78) →
IH; b: self via g5c1_bSide_twoAdm + weight); CASE-2 (r = 2 ∧ pad0 s 1 = q): the
(q,q) form via g5_case2_qq — then MAIN2_weak_of_g5/A2_weak_of_g5 instantiated
unconditionally.  Named gates unchanged.
-/

attribute [instance] P2Data.fin
attribute [instance] RelData.finA
attribute [instance] RelData.finB
attribute [instance] FixedRel.fin
attribute [local instance] Classical.propDecidable
variable (F : Type*) [Field F] [Finite F] [DecidableEq (RatFunc F)]

/-- b-member weight of the CASE-1 j=0 chain is w. -/
lemma g5c1_bSide_weight (r : ℕ) (s : Fin r → ℕ+) (hcase : 2 ≤ r)
    (hs0 : (s ⟨0, by omega⟩ : ℕ) = Nat.card F)
    (hbig : (Nat.card F : ℕ) < (s ⟨1, by omega⟩ : ℕ))
    (R0 : BinaryRel F)
    (hbhd : ∀ j' : R0.ιB, ((R0.cB j') ⟨0, R0.hdepB j'⟩ : ℕ) = 1)
    (hXw : ∀ j' : R0.ιB, weight (R0.depB j' - 1) (expTail (R0.cB j')) =
      psum s r - psum s (2 - 1) - 1) :
    let D := RelData.BCqIter F 1 (toData F R0)
    ∀ p : D.ιB, weight (D.depB p) (D.cB p) = weight r s := by
  classical
  intro D p
  have hcB : D.cB p = consVec oneExp ((p2WpT F (qMinusExp F) ((toData F R0).hdepB p.1) ((toData F R0).cB p.1)).c p.2) := by
    rfl
  rw [hcB]
  change weight ((p2WpT F (qMinusExp F) ((toData F R0).hdepB p.1) ((toData F R0).cB p.1)).dep p.2 + 1)
      (consVec oneExp ((p2WpT F (qMinusExp F) ((toData F R0).hdepB p.1) ((toData F R0).cB p.1)).c p.2)) =
    weight r s
  have hwcons : weight ((p2WpT F (qMinusExp F) ((toData F R0).hdepB p.1) ((toData F R0).cB p.1)).dep p.2 + 1)
      (consVec oneExp ((p2WpT F (qMinusExp F) ((toData F R0).hdepB p.1) ((toData F R0).cB p.1)).c p.2)) =
      (oneExp : ℕ) + weight ((p2WpT F (qMinusExp F) ((toData F R0).hdepB p.1) ((toData F R0).cB p.1)).dep p.2)
        ((p2WpT F (qMinusExp F) ((toData F R0).hdepB p.1) ((toData F R0).cB p.1)).c p.2) := by
    exact weight_consVec oneExp ((p2WpT F (qMinusExp F) ((toData F R0).hdepB p.1) ((toData F R0).cB p.1)).c p.2)
  rw [hwcons]
  have hwle := (p2WpT F (qMinusExp F) ((toData F R0).hdepB p.1) ((toData F R0).cB p.1)).hle p.2
  have hwm : weight ((p2WpT F (qMinusExp F) ((toData F R0).hdepB p.1) ((toData F R0).cB p.1)).dep p.2)
        ((p2WpT F (qMinusExp F) ((toData F R0).hdepB p.1) ((toData F R0).cB p.1)).c p.2) =
      (qMinusExp F : ℕ) + weight ((toData F R0).depB p.1) ((toData F R0).cB p.1) := by
    change weight ((p2WpT F (qMinusExp F) ((toData F R0).hdepB p.1) ((toData F R0).cB p.1)).dep p.2)
        ((p2WpT F (qMinusExp F) ((toData F R0).hdepB p.1) ((toData F R0).cB p.1)).c p.2) =
      weight 1 (single (qMinusExp F)) + weight ((toData F R0).depB p.1) ((toData F R0).cB p.1)
    rw [weight_single]
    exact hwle.1
  rw [hwm]
  have hcbw : weight ((toData F R0).depB p.1) ((toData F R0).cB p.1) = psum s r - psum s 1 := by
    have hwt := weight_head_tail (R0.hdepB p.1) (R0.cB p.1)
    have hh : (((R0.cB p.1) ⟨0, (R0.hdepB p.1)⟩ : ℕ)) = 1 := by
      exact hbhd p.1
    rw [hh] at hwt
    have hX0 := hXw p.1
    change weight (R0.depB p.1 - 1) (expTail (R0.cB p.1)) = psum s r - psum s 1 - 1 at hX0
    rw [hX0] at hwt
    -- hwt : weight (R0.depB)(R0.cB) = 1 + (psum r − psum 1 − 1) ; goal (toData-form) = psum r − psum 1
    have hps1v : psum s 1 = (qExp F : ℕ) := by
      have hp : psum s 1 = pad0 s 0 := by
        change (∑ j ∈ Finset.range 1, pad0 s j) = pad0 s 0
        simp
      rw [hp]
      have hp0 : pad0 s 0 = (s ⟨0, by omega⟩ : ℕ) := pad0_of_lt s (by omega : 0 < r)
      rw [hp0]
      change (s ⟨0, by omega⟩ : ℕ) = (qExp F : ℕ)
      rw [hs0]
      rfl
    have hq : (qExp F : ℕ) = Nat.card F := by rfl
    have hW1 : psum s 1 + 1 ≤ psum s r := by
      have hp2 : psum s 2 ≤ psum s r := psum_mono s (by omega : 2 ≤ r)
      have hp2v : psum s 2 = psum s 1 + (s ⟨1, by omega⟩ : ℕ) := by
        have hpsum2 : psum s 2 = pad0 s 0 + pad0 s 1 := by
          change (∑ j ∈ Finset.range 2, pad0 s j) = pad0 s 0 + pad0 s 1
          rw [Finset.sum_range_succ]
          rw [Finset.sum_range_succ]
          simp
        rw [hpsum2]
        have h0 : pad0 s 0 = (s ⟨0, by omega⟩ : ℕ) := pad0_of_lt s (by omega : 0 < r)
        have h1 : pad0 s 1 = (s ⟨1, by omega⟩ : ℕ) := pad0_of_lt s (by omega : 1 < r)
        rw [h0, h1]
        rw [hps1v, hq]
        rw [hs0]
      have hs2 : (s ⟨1, by omega⟩ : ℕ) ≥ 1 := (s ⟨1, by omega⟩).pos
      omega
    change weight (R0.depB p.1) (R0.cB p.1) = psum s r - psum s 1
    omega
  rw [hcbw]
  have hps1 : psum s 1 = (qExp F : ℕ) := by
    have hp : psum s 1 = pad0 s 0 := by
      change (∑ j ∈ Finset.range 1, pad0 s j) = pad0 s 0
      simp
    rw [hp]
    have hp0 : pad0 s 0 = (s ⟨0, by omega⟩ : ℕ) := pad0_of_lt s (by omega : 0 < r)
    rw [hp0]
    change (s ⟨0, by omega⟩ : ℕ) = (qExp F : ℕ)
    rw [hs0]
    rfl
  have hpsr : psum s r = weight r s := psum_self s
  have hq : (qExp F : ℕ) = Nat.card F := by rfl
  have hOne : (oneExp : ℕ) = 1 := by rfl
  have hqm : (qMinusExp F : ℕ) = Nat.card F - 1 := by rfl
  rw [hOne, hqm, hps1, hq]
  rw [← hpsr]
  change 1 + (Nat.card F - 1 + (psum s r - Nat.card F)) = psum s r
  have hW : Nat.card F + 1 ≤ psum s r := by
    have hp2 : psum s 2 ≤ psum s r := psum_mono s (by omega : 2 ≤ r)
    have hp2v : psum s 2 = Nat.card F + (s ⟨1, by omega⟩ : ℕ) := by
      have hpsum2 : psum s 2 = pad0 s 0 + pad0 s 1 := by
        change (∑ j ∈ Finset.range 2, pad0 s j) = pad0 s 0 + pad0 s 1
        rw [Finset.sum_range_succ]
        rw [Finset.sum_range_succ]
        simp
      rw [hpsum2]
      have h0 : pad0 s 0 = (qExp F : ℕ) := by
        rw [pad0_of_lt s (by omega : 0 < r)]
        change (s ⟨0, by omega⟩ : ℕ) = (qExp F : ℕ)
        rw [hs0]
        rfl
      have h1 : pad0 s 1 = (s ⟨1, by omega⟩ : ℕ) := by
        rw [pad0_of_lt s (by omega : 1 < r)]
      rw [h0, h1, hq]
    omega
  have hq2 : 2 ≤ Nat.card F := card_ge_two F
  omega

/-- first-entry bound of the b-fiber stuffle outputs: ≤ (q−1) + (R0.cB-head) = q. -/
lemma g5c1_b_fiber_front_le (R0 : BinaryRel F) (j : (toData F R0).ιB)
    (hbhd : ∀ j' : R0.ιB, ((R0.cB j') ⟨0, R0.hdepB j'⟩ : ℕ) = 1)
    (e : (p2WpT F (qMinusExp F) ((toData F R0).hdepB j) ((toData F R0).cB j)).ι) :
    pad0 ((p2WpT F (qMinusExp F) ((toData F R0).hdepB j) ((toData F R0).cB j)).c e) 0 ≤ Nat.card F := by
  classical
  have h1 := p2WpT_front_le F ((toData F R0).hdepB j) ((toData F R0).cB j) e
  have hb : (((toData F R0).cB j) ⟨0, (toData F R0).hdepB j⟩ : ℕ) = 1 := by
    change (((R0.cB j) ⟨0, (R0.hdepB j)⟩ : ℕ)) = 1
    exact hbhd j
  have hNat : (qMinusExp F : ℕ) + 1 = Nat.card F := by
    change Nat.card F - 1 + 1 = Nat.card F
    have hq : 1 ≤ Nat.card F := by
      have h2 := card_ge_two F
      omega
    omega
  rw [hb] at h1
  rw [hNat] at h1
  exact h1

/-- R0 b-tuple weight: weight (depB j)(cB j) = psum r − psum 1 (= w − q). -/
lemma g5c1_R0_b_weight (r : ℕ) (s : Fin r → ℕ+) (hcase : 2 ≤ r)
    (hs0 : (s ⟨0, by omega⟩ : ℕ) = Nat.card F)
    (hbig : (Nat.card F : ℕ) < (s ⟨1, by omega⟩ : ℕ))
    (R0 : BinaryRel F) (j : (toData F R0).ιB)
    (hbhd : ∀ j' : R0.ιB, ((R0.cB j') ⟨0, R0.hdepB j'⟩ : ℕ) = 1)
    (hXw : ∀ j' : R0.ιB, weight (R0.depB j' - 1) (expTail (R0.cB j')) =
      psum s r - psum s (2 - 1) - 1) :
    weight ((toData F R0).depB j) ((toData F R0).cB j) = psum s r - psum s 1 := by
  classical
  have hwt := weight_head_tail (R0.hdepB j) (R0.cB j)
  have hh : (((R0.cB j) ⟨0, (R0.hdepB j)⟩ : ℕ)) = 1 := hbhd j
  rw [hh] at hwt
  have hX0 := hXw j
  change weight (R0.depB j - 1) (expTail (R0.cB j)) = psum s r - psum s 1 - 1 at hX0
  -- hwt : weight(R0.depB)(R0.cB) = 1 + tail
  change weight (R0.depB j) (R0.cB j) = psum s r - psum s 1
  have hW1 : psum s 1 + 1 ≤ psum s r := by
    have hp2 : psum s 2 ≤ psum s r := psum_mono s (by omega : 2 ≤ r)
    have hp2v : psum s 2 ≥ psum s 1 + 1 := by
      have hpsum2 : psum s 2 = pad0 s 0 + pad0 s 1 := by
        change (∑ j ∈ Finset.range 2, pad0 s j) = pad0 s 0 + pad0 s 1
        rw [Finset.sum_range_succ]
        rw [Finset.sum_range_succ]
        simp
      rw [hpsum2]
      have h0 : pad0 s 0 = (s ⟨0, by omega⟩ : ℕ) := pad0_of_lt s (by omega : 0 < r)
      have h1 : pad0 s 1 = (s ⟨1, by omega⟩ : ℕ) := pad0_of_lt s (by omega : 1 < r)
      rw [h0, h1]
      change (s ⟨0, by omega⟩ : ℕ) + (s ⟨1, by omega⟩ : ℕ) ≥ psum s 1 + 1
      have hp1 : psum s 1 = (s ⟨0, by omega⟩ : ℕ) := by
        have hp : psum s 1 = pad0 s 0 := by
          change (∑ j ∈ Finset.range 1, pad0 s j) = pad0 s 0
          simp
        rw [hp]
        exact pad0_of_lt s (by omega : 0 < r)
      have hs1 : 1 ≤ (s ⟨1, by omega⟩ : ℕ) := (s ⟨1, by omega⟩).pos
      omega
    omega
  omega

/-- the b-fiber stuffle outputs have depth ≥ 2 (a depth-1 output of weight w−1
violates the prefix bound (q−1)+1 since w ≥ q+2). -/
lemma g5c1_b_fiber_dep_ge_two (r : ℕ) (s : Fin r → ℕ+) (hcase : 2 ≤ r)
    (hs0 : (s ⟨0, by omega⟩ : ℕ) = Nat.card F)
    (hbig : (Nat.card F : ℕ) < (s ⟨1, by omega⟩ : ℕ))
    (R0 : BinaryRel F) (j : (toData F R0).ιB)
    (hbhd : ∀ j' : R0.ιB, ((R0.cB j') ⟨0, R0.hdepB j'⟩ : ℕ) = 1)
    (hXw : ∀ j' : R0.ιB, weight (R0.depB j' - 1) (expTail (R0.cB j')) =
      psum s r - psum s (2 - 1) - 1)
    (e : (p2WpT F (qMinusExp F) ((toData F R0).hdepB j) ((toData F R0).cB j)).ι) :
    2 ≤ (p2WpT F (qMinusExp F) ((toData F R0).hdepB j) ((toData F R0).cB j)).dep e := by
  classical
  by_contra h
  have hpos : 0 < (p2WpT F (qMinusExp F) ((toData F R0).hdepB j) ((toData F R0).cB j)).dep e :=
    (p2WpT F (qMinusExp F) ((toData F R0).hdepB j) ((toData F R0).cB j)).hdep e
  have hd1 : (p2WpT F (qMinusExp F) ((toData F R0).hdepB j) ((toData F R0).cB j)).dep e = 1 := by omega
  let P2 := p2WpT F (qMinusExp F) ((toData F R0).hdepB j) ((toData F R0).cB j)
  have hbw := g5c1_R0_b_weight F r s hcase hs0 hbig R0 j hbhd hXw
  have hw : weight (P2.dep e) (P2.c e) = (qMinusExp F : ℕ) + (psum s r - psum s 1) := by
    have hwle := (P2.hle e).1
    change weight (P2.dep e) (P2.c e) =
      weight 1 (single (qMinusExp F)) + weight ((toData F R0).depB j) ((toData F R0).cB j) at hwle
    rw [weight_single] at hwle
    rw [hbw] at hwle
    exact hwle
  have hpsum1 : psum (P2.c e) 1 = weight (P2.dep e) (P2.c e) := by
    have hw1 : weight (P2.dep e) (P2.c e) = pad0 (P2.c e) 0 := weight_dep_one_eq_pad0 (P2.c e) hd1
    have hp : psum (P2.c e) 1 = pad0 (P2.c e) 0 := by
      change (∑ x ∈ Finset.range 1, pad0 (P2.c e) x) = pad0 (P2.c e) 0
      simp
    omega
  have hle1 := (P2.hle e).2 1
  have hrhs : psumSeq (tupPadSum (single (qMinusExp F)) ((toData F R0).cB j)) 1 =
      (qMinusExp F : ℕ) + 1 := by
    change (∑ x ∈ Finset.range 1, (pad0 (single (qMinusExp F)) x +
        pad0 ((toData F R0).cB j) x)) = (qMinusExp F : ℕ) + 1
    simp
    rw [pad0_single_zero]
    have hc0 : pad0 ((toData F R0).cB j) 0 = 1 := by
      change pad0 ((R0.cB j)) 0 = 1
      rw [pad0_of_lt (R0.cB j) (R0.hdepB j)]
      change (((R0.cB j) ⟨0, (R0.hdepB j)⟩ : ℕ)) = 1
      exact hbhd j
    exact congrArg (fun t : ℕ => (qMinusExp F : ℕ) + t) hc0
  rw [hpsum1, hw] at hle1
  rw [hrhs] at hle1
  -- arithmetic: (q−1) + (psum r − psum 1) ≤ (q−1)+1 → psum r − psum 1 ≤ 1; but ≥ q+2−q = 2
  have hwg : Nat.card F + 2 ≤ psum s r := by
    have hbigp : (Nat.card F : ℕ) < pad0 s 1 := by
      rw [pad0_of_lt s (by omega : 1 < r)]
      exact hbig
    have hw' : Nat.card F + 2 ≤ weight r s := case1_weight_ge_q_add_two F s hcase hbigp
    rw [← psum_self s] at hw'
    exact hw'
  have hps1 : psum s 1 = (qExp F : ℕ) := by
    have hp : psum s 1 = pad0 s 0 := by
      change (∑ j ∈ Finset.range 1, pad0 s j) = pad0 s 0
      simp
    rw [hp]
    have hp0 : pad0 s 0 = (s ⟨0, by omega⟩ : ℕ) := pad0_of_lt s (by omega : 0 < r)
    rw [hp0]
    change (s ⟨0, by omega⟩ : ℕ) = (qExp F : ℕ)
    rw [hs0]
    rfl
  have hq : (qExp F : ℕ) = Nat.card F := by rfl
  have hqm : (qMinusExp F : ℕ) = Nat.card F - 1 := by rfl
  change (qMinusExp F : ℕ) + (psum s r - psum s 1) ≤ (qMinusExp F : ℕ) + 1 at hle1
  rw [hqm, hps1, hq] at hle1
  change Nat.card F - 1 + (psum s r - Nat.card F) ≤ Nat.card F - 1 + 1 at hle1
  omega

/-- b-members of the CASE-1 j=0 chain are 2-admissible. -/
lemma g5c1_bSide_twoAdm (r : ℕ) (s : Fin r → ℕ+) (hcase : 2 ≤ r)
    (hs0 : (s ⟨0, by omega⟩ : ℕ) = Nat.card F)
    (hbig : (Nat.card F : ℕ) < (s ⟨1, by omega⟩ : ℕ))
    (R0 : BinaryRel F)
    (hbhd : ∀ j' : R0.ιB, ((R0.cB j') ⟨0, R0.hdepB j'⟩ : ℕ) = 1)
    (hXw : ∀ j' : R0.ιB, weight (R0.depB j' - 1) (expTail (R0.cB j')) =
      psum s r - psum s (2 - 1) - 1) :
    let D := RelData.BCqIter F 1 (toData F R0)
    ∀ p : D.ιB, kAdmissible (Nat.card F) (D.cB p) 2 := by
  classical
  intro D p
  have hcB : D.cB p = consVec oneExp ((p2WpT F (qMinusExp F) ((toData F R0).hdepB p.1) ((toData F R0).cB p.1)).c p.2) := by
    rfl
  rw [hcB]
  have hge : 2 ≤ (p2WpT F (qMinusExp F) ((toData F R0).hdepB p.1) ((toData F R0).cB p.1)).dep p.2 := by
    exact g5c1_b_fiber_dep_ge_two F r s hcase hs0 hbig R0 p.1 hbhd hXw p.2
  have hfront : pad0 ((p2WpT F (qMinusExp F) ((toData F R0).hdepB p.1) ((toData F R0).cB p.1)).c p.2) 0 ≤
      Nat.card F := by
    exact g5c1_b_fiber_front_le F R0 p.1 hbhd p.2
  exact kAdm2_cons_one (Nat.card F) (card_ge_two F) hge
    ((p2WpT F (qMinusExp F) ((toData F R0).hdepB p.1) ((toData F R0).cB p.1)).c p.2) hfront
end ZagierHoffmanPositiveChar

