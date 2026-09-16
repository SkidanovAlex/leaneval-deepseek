import Submission.ZagierHoffmanProof.StepL75
set_option autoImplicit false
set_option maxHeartbeats 100000000
open Polynomial RatFunc
open scoped BigOperators
/-!
# Step L93: the (q,q,q) CASE-2 j=0 chain — iterate-2 member facts (SESSION 249)

The level-3 j=0 empty-front chain D := BCqIter F 2 (toData F (r1Rel F))
(a-side = (q,q,q), coeff 1; members = D.cB).  This module proves the member facts
needed by the (q,q,q) leaf (main3's last CASE-2 subcase):
  • g53E_member_head: iterate-1 member heads are 1 (BCqIter_cB_head at n = 0);
  • g53Y_dep_ge_two: outer p2WpT(q−1, iterate-1-member) outputs have depth ≥ 2
      (a depth-1 output of weight (q−1)+2q violates the prefix bound (q−1)+1);
  • ★ g53D_member_twoAdm: iterate-2 members are 2-admissible (entry-0 = 1,
      entry-1 ≤ (q−1)+1 = q via p2WpT_front_le, depth ≥ 3 kills cond2);
  • g53D_member_weight = 3q;  g53D_member_dep_ge_three ≥ 3;
  • ★ g53D_member_psum3_lt: psum(member) 3 < 3q = psum(q,q,q) 3 — the STRICT
      prefix-3 drop (LePad prefix-2 bound of the Y-fiber + iterate-1 second entry
      ≤ q gives psum-3 ≤ 2q+1 < 3q), so EVERY ¬3-adm iterate-2 member
      dispatches through main3's rec via Main3Step (Or.inl), NO InitLt needed
      (paper-consistent: Prop 2.13's type-3 Init(u) ≻ Init(s) outputs are
      impossible for s = (q,q,q), so all members are type-2-like).
DISPATCH SHAPE (verified against StepL92's pattern): per-member e by_cases
3-adm → admExpT_self (weight = 3q) / ¬3-adm → Main3Step (strict drop) +
2-adm → rec; horder trivial (depth-3 s saturates).  Remaining for the (q,q,q)
leaf: the ζ-identity g53qqq_zeta := BCqIter_zeta_zero F 2 (r1Rel F) + the
a-side collapse to ζ(q,q,q) (mirror g5qq_aSide at n = 2) and the single-family
fold assembly → AdmExpT F 3q 3 s.  theorem_B/D remain ABP-gated (no route).
-/

namespace ZagierHoffmanPositiveChar
attribute [instance] P2Data.fin
attribute [instance] RelData.finA
attribute [instance] RelData.finB
attribute [instance] FixedRel.fin
attribute [local instance] Classical.propDecidable
variable (F : Type*) [Field F] [Finite F] [DecidableEq (RatFunc F)]

/-- The (q,q,q) CASE-2 j=0 chain data: TWO BC_q-iterations of R1 (empty front). -/
noncomputable def g53D (F : Type*) [Field F] [Finite F] [DecidableEq (RatFunc F)] : RelData F :=
  RelData.BCqIter F 2 (toData F (r1Rel F))

/-- iterate-1 data = StepL75's g5D. -/
noncomputable def g53E (F : Type*) [Field F] [Finite F] [DecidableEq (RatFunc F)] : RelData F :=
  g5D F

/-- the Y-fiber of an iterate-2 member index (j : iterate-1 b-index, e : p2WpT-fiber). -/
noncomputable def g53Y (F : Type*) [Field F] [Finite F] [DecidableEq (RatFunc F)]
    (j : (g53E F).ιB) :
    P2Data F 1 ((g53E F).depB j) (by omega : 0 < 1) ((g53E F).hdepB j)
      (single (qMinusExp F)) ((g53E F).cB j) :=
  p2WpT F (qMinusExp F) ((g53E F).hdepB j) ((g53E F).cB j)

/-- iterate-1 member heads are 1 (BCqIter_cB_head at n = 0). -/
lemma g53E_member_head (j : (g53E F).ιB) :
    ((g53E F).cB j) ⟨0, (g53E F).hdepB j⟩ = oneExp := by
  dsimp [g53E, g5D]
  exact RelData.BCqIter_cB_head F 0 (toData F (r1Rel F)) j

/-- outer p2WpT(q−1, iterate-1-member) outputs have depth ≥ 2 (a depth-1 output of
weight (q−1)+2q would violate the prefix bound (q−1)+1). -/
lemma g53Y_dep_ge_two (j : (g53E F).ιB)
    (e : (g53Y F j).ι) : 2 ≤ (g53Y F j).dep e := by
  classical
  by_contra h
  have hpos : 0 < (g53Y F j).dep e := (g53Y F j).hdep e
  have hd1 : (g53Y F j).dep e = 1 := by omega
  have hw : weight ((g53Y F j).dep e) ((g53Y F j).c e) =
      (qMinusExp F : ℕ) + ((qExp F : ℕ) + (qExp F : ℕ)) := by
    have hwle := ((g53Y F j).hle e).1
    rw [weight_single] at hwle
    have hbw := g5D_member_weight F j
    change weight ((g53E F).depB j) ((g53E F).cB j) = (qExp F : ℕ) + (qExp F : ℕ) at hbw
    rw [hbw] at hwle
    exact hwle
  have hpsum1 : psum ((g53Y F j).c e) 1 = weight ((g53Y F j).dep e) ((g53Y F j).c e) := by
    have hw1 : weight ((g53Y F j).dep e) ((g53Y F j).c e) = pad0 ((g53Y F j).c e) 0 :=
      weight_dep_one_eq_pad0 ((g53Y F j).c e) hd1
    have hp : psum ((g53Y F j).c e) 1 = pad0 ((g53Y F j).c e) 0 := by
      change (∑ t ∈ Finset.range 1, pad0 ((g53Y F j).c e) t) = pad0 ((g53Y F j).c e) 0
      simp
    omega
  have hle1 := ((g53Y F j).hle e).2 1
  have hrhs : psumSeq (tupPadSum (single (qMinusExp F)) ((g53E F).cB j)) 1 =
      (qMinusExp F : ℕ) + 1 := by
    change (∑ x ∈ Finset.range 1, (pad0 (single (qMinusExp F)) x +
        pad0 ((g53E F).cB j) x)) = (qMinusExp F : ℕ) + 1
    simp
    rw [pad0_single_zero]
    have hc0 : pad0 ((g53E F).cB j) 0 = 1 := by
      have hh := g53E_member_head F j
      have hd : 0 < (g53E F).depB j := (g53E F).hdepB j
      rw [pad0_of_lt ((g53E F).cB j) hd]
      exact congrArg (fun t : ℕ+ => (t : ℕ)) hh
    exact congrArg (fun t : ℕ => (qMinusExp F : ℕ) + t) hc0
  rw [hpsum1, hw] at hle1
  rw [hrhs] at hle1
  change (qMinusExp F : ℕ) + ((qExp F : ℕ) + (qExp F : ℕ)) ≤ (qMinusExp F : ℕ) + 1 at hle1
  change (Nat.card F - 1) + (Nat.card F + Nat.card F) ≤ (Nat.card F - 1) + 1 at hle1
  have hq : 2 ≤ Nat.card F := card_ge_two F
  omega

/-- ★ iterate-2 members are 2-admissible (entry-0 = 1, entry-1 ≤ (q−1)+1 = q,
depth ≥ 3 kills the depth-2 form). -/
lemma g53D_member_twoAdm (p : (g53D F).ιB) :
    kAdmissible (Nat.card F) ((g53D F).cB p) 2 := by
  classical
  rcases p with ⟨j, e⟩
  change kAdmissible (Nat.card F) (consVec oneExp ((g53Y F j).c e)) 2
  have hge : 2 ≤ (g53Y F j).dep e := g53Y_dep_ge_two F j e
  have h1 := p2WpT_front_le F ((g53E F).hdepB j) ((g53E F).cB j) e
  have hb : ((g53E F).cB j) ⟨0, (g53E F).hdepB j⟩ = oneExp := g53E_member_head F j
  have hb2 : (((g53E F).cB j) ⟨0, (g53E F).hdepB j⟩ : ℕ) = 1 := by
    exact congrArg (fun u : ℕ+ => (u : ℕ)) hb
  have hfront : pad0 ((g53Y F j).c e) 0 ≤ Nat.card F := by
    have hNat : (qMinusExp F : ℕ) + 1 = Nat.card F := by
      change Nat.card F - 1 + 1 = Nat.card F
      have hq : 1 ≤ Nat.card F := by
        have h2 := card_ge_two F
        omega
      omega
    rw [hb2] at h1
    rw [hNat] at h1
    exact h1
  exact kAdm2_cons_one (Nat.card F) (card_ge_two F) hge ((g53Y F j).c e) hfront

/-- member weight of the iterate-2 chain is 3q. -/
lemma g53D_member_weight (p : (g53D F).ιB) :
    weight ((g53D F).depB p) ((g53D F).cB p) =
      (qExp F : ℕ) + (qExp F : ℕ) + (qExp F : ℕ) := by
  classical
  rcases p with ⟨j, e⟩
  change weight ((g53Y F j).dep e + 1) (consVec oneExp ((g53Y F j).c e)) =
    (qExp F : ℕ) + (qExp F : ℕ) + (qExp F : ℕ)
  have hwcons : weight ((g53Y F j).dep e + 1) (consVec oneExp ((g53Y F j).c e)) =
      (oneExp : ℕ) + weight ((g53Y F j).dep e) ((g53Y F j).c e) := by
    exact weight_consVec oneExp ((g53Y F j).c e)
  rw [hwcons]
  have hwle := ((g53Y F j).hle e).1
  have hwm : weight ((g53Y F j).dep e) ((g53Y F j).c e) =
      (qMinusExp F : ℕ) + ((qExp F : ℕ) + (qExp F : ℕ)) := by
    change weight ((g53Y F j).dep e) ((g53Y F j).c e) =
      weight 1 (single (qMinusExp F)) + weight ((g53E F).depB j) ((g53E F).cB j) at hwle
    rw [weight_single] at hwle
    have hbw := g5D_member_weight F j
    change weight ((g53E F).depB j) ((g53E F).cB j) = (qExp F : ℕ) + (qExp F : ℕ) at hbw
    rw [hbw] at hwle
    exact hwle
  rw [hwm]
  change (oneExp : ℕ) + ((qMinusExp F : ℕ) + ((qExp F : ℕ) + (qExp F : ℕ))) =
    (qExp F : ℕ) + (qExp F : ℕ) + (qExp F : ℕ)
  change 1 + ((Nat.card F - 1) + (Nat.card F + Nat.card F)) =
    Nat.card F + Nat.card F + Nat.card F
  have hq : 1 ≤ Nat.card F := by
    have h2 := card_ge_two F
    omega
  omega

/-- member depths of the iterate-2 chain are ≥ 3 (needed for the level-0 shift). -/
lemma g53D_member_dep_ge_three (p : (g53D F).ιB) : 3 ≤ (g53D F).depB p := by
  classical
  rcases p with ⟨j, e⟩
  change 3 ≤ (g53Y F j).dep e + 1
  have hge2 : 2 ≤ (g53Y F j).dep e := g53Y_dep_ge_two F j e
  omega




/-- iterate-1 members are 2-adm, so their second entry is ≤ q (needed for the
member prefix-3 bound). -/
lemma g53E_member_entry1_le_q (j : (g53E F).ιB) :
    pad0 ((g53E F).cB j) 1 ≤ Nat.card F := by
  have h2 := g5D_member_twoAdm F j
  exact kAdmissible.pad0_le h2 1 (by omega : 1 < 2)

/-- prefix-2 value of the Y-bound template at the iterate-1 member. -/
lemma g53Y_psumSeq2_le (j : (g53E F).ιB) :
    psumSeq (tupPadSum (single (qMinusExp F)) ((g53E F).cB j)) 2 ≤
      (qMinusExp F : ℕ) + (1 + Nat.card F) := by
  classical
  change (∑ x ∈ Finset.range 2, (pad0 (single (qMinusExp F)) x +
      pad0 ((g53E F).cB j) x)) ≤ (qMinusExp F : ℕ) + (1 + Nat.card F)
  rw [Finset.sum_range_succ]
  rw [Finset.sum_range_succ]
  simp
  have h0 : pad0 (single (qMinusExp F)) 0 = (qMinusExp F : ℕ) := pad0_single_zero (qMinusExp F)
  have hc0 : pad0 ((g53E F).cB j) 0 = 1 := by
    have hh := g53E_member_head F j
    have hd : 0 < (g53E F).depB j := (g53E F).hdepB j
    rw [pad0_of_lt ((g53E F).cB j) hd]
    exact congrArg (fun t : ℕ+ => (t : ℕ)) hh
  have h1 : pad0 (single (qMinusExp F)) 1 = 0 := pad0_of_ge (single (qMinusExp F)) (by omega : 1 ≥ 1)
  have hE2 : pad0 ((g53E F).cB j) 1 ≤ Nat.card F := g53E_member_entry1_le_q F j
  rw [h0, hc0, h1]
  omega

/-- ★ iterate-2 members satisfy the STRICT prefix-3 drop from s = (q,q,q):
psum(member) 3 ≤ 1 + (q−1) + (1 + E₂) ≤ 2q+1 < 3q (LePad prefix-2 of
the Y-fiber + iterate-1 second entry ≤ q) — every iterate-2 member feeds
main3's rec via Main3Step (Or.inl of the strict drop), NO InitLt needed. -/
lemma g53D_member_psum3_lt (p : (g53D F).ιB) :
    psum ((g53D F).cB p) 3 < (qExp F : ℕ) + (qExp F : ℕ) + (qExp F : ℕ) := by
  classical
  rcases p with ⟨j, e⟩
  change psum (consVec oneExp ((g53Y F j).c e)) 3 <
    (qExp F : ℕ) + (qExp F : ℕ) + (qExp F : ℕ)
  have hp3 : psum (consVec oneExp ((g53Y F j).c e)) 3 =
      1 + psum ((g53Y F j).c e) 2 := by
    have hc := psum_consVec oneExp ((g53Y F j).c e) 2
    rw [hc]
    have hone : (oneExp : ℕ) = 1 := by rfl
    rw [hone]
  rw [hp3]
  have hle2 := ((g53Y F j).hle e).2 2
  have hseq2 := g53Y_psumSeq2_le F j
  have hbnd : psum ((g53Y F j).c e) 2 ≤ (qMinusExp F : ℕ) + (1 + Nat.card F) :=
    le_trans hle2 hseq2
  have hbnd' : 1 + psum ((g53Y F j).c e) 2 ≤ 1 + ((qMinusExp F : ℕ) + (1 + Nat.card F)) :=
    Nat.add_le_add_left hbnd 1
  have hmax : 1 + ((qMinusExp F : ℕ) + (1 + Nat.card F)) <
      (qExp F : ℕ) + (qExp F : ℕ) + (qExp F : ℕ) := by
    change 1 + ((Nat.card F - 1) + (1 + Nat.card F)) <
      Nat.card F + Nat.card F + Nat.card F
    have hq : 2 ≤ Nat.card F := card_ge_two F
    omega
  exact lt_of_le_of_lt hbnd' hmax
end ZagierHoffmanPositiveChar
