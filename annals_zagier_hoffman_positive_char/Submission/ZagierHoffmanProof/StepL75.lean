import Submission.ZagierHoffmanProof.StepL74
set_option autoImplicit false
set_option maxHeartbeats 100000000
open Polynomial RatFunc
open scoped BigOperators
/-!
# Step L75: G5 CASE-2 (q,q) — the j = 0 empty-front BC-iterate chain (SESSION 225/226)

★ g5_case2_qq : AdmExp F ((qExp:ℕ)+(qExp:ℕ)) 2 (pair qExp qExp) — the depth-2
(q,q) in-domain tuple (weight 2q) expands at level 2 into its BC-iterate b-members.
MATHEMATICS (paper Prop 2.13 at k=2, j=0; PLAN SESSION 225 G5 analysis): for
s=(q,q) the maximal j with s_j<q is 0 (s_0=0), so the CASE-2 chain is the EMPTY-front
BC-iterate D := BCqIter F 1 (toData r1Rel): its a-side is (q,q) itself (coeff 1) and
its b-side members (consVec 1 of the p2WpT(q−1,(1,q−1))-stuffle outputs) carry the
decomposition.  The ζ-identity is the LEVEL-SUM of the iterate's validity:
  g5qq_zeta : ζ_A(q,q) + Σ_p (aB p)·ζ_A(cB p) = 0   [BCqIter_zeta_zero n=1 +
    the PUnit a-side collapse g5qq_aSide — the shift S(e+1) washes out because every
    term has depth ≥ 2].
Member facts (sorry-free, the (q,q) analogue of StepL52/53's):
  g5D_cB/g5D_depB (rfl member structure); g5D_member_weight = 2q (weight_consVec +
    the P2Data LePad weight equality + r1RelData_b_weight = q);
  kAdm2_cons_one (generic: (1::t), depth(t) ≥ 2, first entry of t ≤ q ⟹ 2-adm);
  p2WpT_front_le (first stuffle-output entry ≤ v + B₁ from LePad prefix-1);
  g5stuff_dep_ge_two (stuffle outputs of (q−1)×(1,q−1) have depth ≥ 2: a depth-1
    output's whole weight (q−1)+q would violate the prefix bound (q−1)+1);
  g5D_member_twoAdm (members 2-adm: head 1, second entry ≤ q, depth ≥ 3 ⟹ the
    cond2 witness is impossible).
LEAN NOTES: toData/r1Rel field projections are semireducible — `change`+kernel steps
(rfl-level) are used instead of simp; rewrite through dependent weight-args fails
("motive not type correct") — first rewrite the tuple (g5D_cB) then `change` the
depth; F-parameterization: lemmas mentioning Nat.card F/g5D take F as first arg
(e.g. g5D_cB F p), the pure p2WpT_front_le is F-free.
NEXT: the G5 CASE-1 j = 0 instance ((q, s₂>q, …), empty-front tail-relation chain),
then instantiate MAIN2-weak/A2-weak (StepL74's g5 hypothesis).  Named gates
unchanged: m≥3 hierarchy (β), theorem_B/D.
-/

namespace ZagierHoffmanPositiveChar
attribute [instance] P2Data.fin
attribute [instance] RelData.finA
attribute [instance] RelData.finB
attribute [instance] FixedRel.fin
attribute [local instance] Classical.propDecidable
variable (F : Type*) [Field F] [Finite F] [DecidableEq (RatFunc F)]

/-- generic: (1 :: t) with depth(t) ≥ 2 and first entry of t ≤ q is 2-admissible. -/
lemma kAdm2_cons_one (q : ℕ) (hq : 2 ≤ q) {k : ℕ} (hk2 : 2 ≤ k) (t : Fin k → ℕ+)
    (hfront : pad0 t 0 ≤ q) : kAdmissible q (consVec oneExp t) 2 := by
  classical
  constructor
  · intro x hx
    have hx01 : x = 0 ∨ x = 1 := by omega
    rcases hx01 with hx0 | hx1
    · subst x
      have hd : 0 < k + 1 := by omega
      rw [pad0_of_lt (consVec oneExp t) hd]
      have h0 := congrArg (fun u : ℕ+ => (u : ℕ)) (consVec_zero oneExp t)
      rw [h0]
      change 1 ≤ q
      omega
    · subst x
      have hd1 : 1 < k + 1 := by omega
      rw [pad0_of_lt (consVec oneExp t) hd1]
      have h1v : (((consVec oneExp t) ⟨1, hd1⟩ : ℕ) = (t ⟨0, by omega⟩ : ℕ)) := by
        have hc := congrArg (fun u : ℕ+ => (u : ℕ)) (consVec_succ oneExp t ⟨0, by omega⟩)
        change (((consVec oneExp t) ⟨1, hd1⟩ : ℕ)) = (t ⟨0, by omega⟩ : ℕ)
        simpa using hc
      rw [h1v]
      have hp : pad0 t 0 = (t ⟨0, by omega⟩ : ℕ) := pad0_of_lt t (by omega : 0 < k)
      rw [← hp]
      exact hfront
  · intro hw2
    rcases hw2 with ⟨hr1, hr2, hall, hlast⟩
    omega

/-- The (q,q) CASE-2 j=0 chain data: one BC_q-iteration of R1 (empty front). -/
noncomputable def g5D (F : Type*) [Field F] [Finite F] [DecidableEq (RatFunc F)] : RelData F :=
  RelData.BCqIter F 1 (toData F (r1Rel F))

@[simp] lemma r1Rel_cB_apply (j : (r1Rel F).ιB) : (r1Rel F).cB j = pair oneExp (qMinusExp F) := by rfl
@[simp] lemma r1Rel_depB_apply (j : (r1Rel F).ιB) : (r1Rel F).depB j = 2 := by rfl
@[simp] lemma toData_cB (R : BinaryRel F) (j : (toData F R).ιB) : (toData F R).cB j = R.cB j := by rfl
@[simp] lemma toData_depB (R : BinaryRel F) (j : (toData F R).ιB) : (toData F R).depB j = R.depB j := by rfl
@[simp] lemma toData_hdepB (R : BinaryRel F) (j : (toData F R).ιB) : (toData F R).hdepB j = R.hdepB j := by rfl

lemma r1RelData_b_weight (j : (toData F (r1Rel F)).ιB) :
    weight ((toData F (r1Rel F)).depB j) ((toData F (r1Rel F)).cB j) = (qExp F : ℕ) := by
  change weight 2 (pair oneExp (qMinusExp F)) = (qExp F : ℕ)
  rw [weight_pair]
  change (oneExp : ℕ) + (qMinusExp F : ℕ) = (qExp F : ℕ)
  change 1 + (Nat.card F - 1) = Nat.card F
  have hq : 1 ≤ Nat.card F := by
    have h2 := card_ge_two F
    omega
  omega


lemma r1RelData_b_pair_head (j : (toData F (r1Rel F)).ιB) :
    ((toData F (r1Rel F)).cB j) ⟨0, (toData F (r1Rel F)).hdepB j⟩ = oneExp := by
  change ((r1Rel F).cB j) ⟨0, (r1Rel F).hdepB j⟩ = oneExp
  change (pair oneExp (qMinusExp F)) ⟨0, (r1Rel F).hdepB j⟩ = oneExp
  rw [pair_zero]

/-- first-entry bound of p2WpT outputs from LePad (prefix at 1). -/
lemma p2WpT_front_le {v : ℕ+} {k : ℕ} (hk : 0 < k) (B : Fin k → ℕ+) (e : (p2WpT F v hk B).ι) :
    pad0 ((p2WpT F v hk B).c e) 0 ≤ (v : ℕ) + ((B ⟨0, hk⟩ : ℕ)) := by
  classical
  have hle := ((p2WpT F v hk B).hle e).2 1
  have hpsum : psum ((p2WpT F v hk B).c e) 1 = pad0 ((p2WpT F v hk B).c e) 0 := by
    change (∑ j ∈ Finset.range 1, pad0 ((p2WpT F v hk B).c e) j) = pad0 ((p2WpT F v hk B).c e) 0
    simp
  have hrhs : psumSeq (tupPadSum (single v) B) 1 = (v : ℕ) + ((B ⟨0, hk⟩ : ℕ)) := by
    change (∑ j ∈ Finset.range 1, (pad0 (single v) j + pad0 B j)) = (v : ℕ) + ((B ⟨0, hk⟩ : ℕ))
    simp
    rw [pad0_single_zero]
    rw [pad0_of_lt B hk]
  calc
    pad0 ((p2WpT F v hk B).c e) 0 = psum ((p2WpT F v hk B).c e) 1 := by rw [hpsum]
    _ ≤ psumSeq (tupPadSum (single v) B) 1 := hle
    _ = (v : ℕ) + ((B ⟨0, hk⟩ : ℕ)) := hrhs

/-- the q−1-fiber outputs over r1Rel-data have depth ≥ 2 (a depth-1 output of weight
(q−1)+q would violate the prefix bound (q−1)+1). -/
lemma g5stuff_dep_ge_two (j : (toData F (r1Rel F)).ιB)
    (e : (p2WpT F (qMinusExp F) ((toData F (r1Rel F)).hdepB j) ((toData F (r1Rel F)).cB j)).ι) :
    2 ≤ (p2WpT F (qMinusExp F) ((toData F (r1Rel F)).hdepB j) ((toData F (r1Rel F)).cB j)).dep e := by
  classical
  by_contra h
  have hpos : 0 < (p2WpT F (qMinusExp F) ((toData F (r1Rel F)).hdepB j) ((toData F (r1Rel F)).cB j)).dep e :=
    (p2WpT F (qMinusExp F) ((toData F (r1Rel F)).hdepB j) ((toData F (r1Rel F)).cB j)).hdep e
  have hd1 : (p2WpT F (qMinusExp F) ((toData F (r1Rel F)).hdepB j) ((toData F (r1Rel F)).cB j)).dep e = 1 := by omega
  let P2 := p2WpT F (qMinusExp F) ((toData F (r1Rel F)).hdepB j) ((toData F (r1Rel F)).cB j)
  have hw : weight (P2.dep e) (P2.c e) = (qMinusExp F : ℕ) + (qExp F : ℕ) := by
    have hwle := (P2.hle e).1
    change weight (P2.dep e) (P2.c e) =
      weight 1 (single (qMinusExp F)) + weight ((toData F (r1Rel F)).depB j)
        ((toData F (r1Rel F)).cB j) at hwle
    rw [weight_single] at hwle
    rw [r1RelData_b_weight F j] at hwle
    exact hwle
  have hpsum1 : psum (P2.c e) 1 = weight (P2.dep e) (P2.c e) := by
    have hw1 : weight (P2.dep e) (P2.c e) = pad0 (P2.c e) 0 := weight_dep_one_eq_pad0 (P2.c e) hd1
    have hp : psum (P2.c e) 1 = pad0 (P2.c e) 0 := by
      change (∑ j ∈ Finset.range 1, pad0 (P2.c e) j) = pad0 (P2.c e) 0
      simp
    omega
  have hle1 := (P2.hle e).2 1
  have hrhs : psumSeq (tupPadSum (single (qMinusExp F)) ((toData F (r1Rel F)).cB j)) 1 =
      (qMinusExp F : ℕ) + 1 := by
    change (∑ x ∈ Finset.range 1, (pad0 (single (qMinusExp F)) x +
        pad0 ((toData F (r1Rel F)).cB j) x)) = (qMinusExp F : ℕ) + 1
    simp
    rw [pad0_single_zero]
    have hc0 : pad0 ((r1Rel F).cB j) 0 = 1 := by
      change pad0 (pair oneExp (qMinusExp F)) 0 = 1
      rw [pad0_pair_zero]
      change (oneExp : ℕ) = 1
      rfl
    exact congrArg (fun t : ℕ => (qMinusExp F : ℕ) + t) hc0
  rw [hpsum1, hw] at hle1
  rw [hrhs] at hle1
  change (qMinusExp F : ℕ) + (qExp F : ℕ) ≤ (qMinusExp F : ℕ) + 1 at hle1
  change Nat.card F - 1 + Nat.card F ≤ Nat.card F - 1 + 1 at hle1
  have hq : 2 ≤ Nat.card F := card_ge_two F
  omega


/-- collapse of the PUnit a-side sum of the (q,q) chain (toBinaryRel form, matching
`BCqIter_zeta_zero`'s unfolded statement). -/
lemma g5qq_aSide :
    (∑ i : (RelData.toBinaryRel F (RelData.BCqIter F 1 (toData F (r1Rel F)))
        (BCqIter_valid F 1 (r1Rel F))).ιA,
      ((((RelData.toBinaryRel F (RelData.BCqIter F 1 (toData F (r1Rel F)))
        (BCqIter_valid F 1 (r1Rel F))).aA i : RatFunc F) : RatFunc.CompletionAtInfty F) *
          ζ_A F ((RelData.toBinaryRel F (RelData.BCqIter F 1 (toData F (r1Rel F)))
        (BCqIter_valid F 1 (r1Rel F))).cA i))) =
    ζ_A F (pair (qExp F) (qExp F)) := by
  classical
  change (∑ i : PUnit,
      ((((RelData.BCqIter F 1 (toData F (r1Rel F))).aA i : RatFunc F) : RatFunc.CompletionAtInfty F) *
        ζ_A F ((RelData.BCqIter F 1 (toData F (r1Rel F))).cA i))) =
    ζ_A F (pair (qExp F) (qExp F))
  have h1 : (∑ i : PUnit,
      ((((RelData.BCqIter F 1 (toData F (r1Rel F))).aA i : RatFunc F) : RatFunc.CompletionAtInfty F) *
        ζ_A F ((RelData.BCqIter F 1 (toData F (r1Rel F))).cA i))) =
      ((((RelData.BCqIter F 1 (toData F (r1Rel F))).aA PUnit.unit : RatFunc F) : RatFunc.CompletionAtInfty F) *
        ζ_A F ((RelData.BCqIter F 1 (toData F (r1Rel F))).cA PUnit.unit)) := by
    rw [show (Finset.univ : Finset PUnit) = {PUnit.unit} by ext i; simp]
    rw [Finset.sum_singleton]
  rw [h1]
  have hc : (((RelData.BCqIter F 1 (toData F (r1Rel F))).aA PUnit.unit : RatFunc F) : RatFunc.CompletionAtInfty F) = 1 := by
    change ((1 : RatFunc F) : RatFunc.CompletionAtInfty F) = 1
    simp [completion_coe_one]
  have ht : ζ_A F ((RelData.BCqIter F 1 (toData F (r1Rel F))).cA PUnit.unit) =
      ζ_A F (pair (qExp F) (qExp F)) := by
    congr 1
    change consVec (qExp F) (single (qExp F)) = pair (qExp F) (qExp F)
    exact consVec_single_q_eq_pair F (qExp F)
  rw [hc, ht]
  simp

/-- ζ-identity of the (q,q) chain: ζ_A(q,q) + Σ_b (aB p)·ζ_A(cB p) = 0. -/
theorem g5qq_zeta :
    ζ_A F (pair (qExp F) (qExp F)) +
      (∑ p : (RelData.BCqIter F 1 (toData F (r1Rel F))).ιB,
        ((((RelData.BCqIter F 1 (toData F (r1Rel F))).aB p : RatFunc F) : RatFunc.CompletionAtInfty F) *
          ζ_A F ((RelData.BCqIter F 1 (toData F (r1Rel F))).cB p))) = 0 := by
  classical
  have hz0 := BCqIter_zeta_zero F 1 (r1Rel F)
  unfold BinaryRel.zeta at hz0
  rw [g5qq_aSide F] at hz0
  exact hz0

/-- the q−1-fiber over the chain's b-data (aux). -/
noncomputable def g5P2 (F : Type*) [Field F] [Finite F] [DecidableEq (RatFunc F)]
    (j : (toData F (r1Rel F)).ιB) :=
  p2WpT F (qMinusExp F) ((toData F (r1Rel F)).hdepB j) ((toData F (r1Rel F)).cB j)

/-- member tuple of the (q,q) chain (rfl-level from BCq's cB def). -/
lemma g5D_cB (p : (g5D F).ιB) : (g5D F).cB p = consVec oneExp ((g5P2 F p.1).c p.2) := by
  rfl

/-- member depth of the (q,q) chain. -/
lemma g5D_depB (p : (g5D F).ιB) : (g5D F).depB p = (g5P2 F p.1).dep p.2 + 1 := by
  rfl

/-- member weight of the (q,q) chain is 2q. -/
lemma g5D_member_weight (p : (g5D F).ιB) :
    weight ((g5D F).depB p) ((g5D F).cB p) = (qExp F : ℕ) + (qExp F : ℕ) := by
  classical
  rw [g5D_cB F p]
  change weight ((g5P2 F p.1).dep p.2 + 1) (consVec oneExp ((g5P2 F p.1).c p.2)) =
    (qExp F : ℕ) + (qExp F : ℕ)
  have hwcons : weight ((g5P2 F p.1).dep p.2 + 1) (consVec oneExp ((g5P2 F p.1).c p.2)) =
      (oneExp : ℕ) + weight ((g5P2 F p.1).dep p.2) ((g5P2 F p.1).c p.2) := by
    exact weight_consVec oneExp ((g5P2 F p.1).c p.2)
  rw [hwcons]
  have hwle := ((g5P2 F p.1).hle p.2).1
  change weight ((g5P2 F p.1).dep p.2) ((g5P2 F p.1).c p.2) =
      weight 1 (single (qMinusExp F)) + weight ((toData F (r1Rel F)).depB p.1)
        ((toData F (r1Rel F)).cB p.1) at hwle
  have hwm : weight ((g5P2 F p.1).dep p.2) ((g5P2 F p.1).c p.2) =
      (qMinusExp F : ℕ) + weight ((toData F (r1Rel F)).depB p.1)
          ((toData F (r1Rel F)).cB p.1) := by
    rw [weight_single] at hwle
    exact hwle
  rw [hwm]
  have hbw := r1RelData_b_weight F p.1
  rw [hbw]
  change (oneExp : ℕ) + ((qMinusExp F : ℕ) + (qExp F : ℕ)) = (qExp F : ℕ) + (qExp F : ℕ)
  change 1 + ((Nat.card F - 1) + Nat.card F) = Nat.card F + Nat.card F
  have hq : 1 ≤ Nat.card F := by
    have h2 := card_ge_two F
    omega
  omega

/-- members of the (q,q) chain are 2-admissible. -/
lemma g5D_member_twoAdm (p : (g5D F).ιB) :
    kAdmissible (Nat.card F) ((g5D F).cB p) 2 := by
  classical
  rw [g5D_cB F p]
  have hge : 2 ≤ (g5P2 F p.1).dep p.2 := by
    exact g5stuff_dep_ge_two F p.1 p.2
  have h1 := p2WpT_front_le F ((toData F (r1Rel F)).hdepB p.1)
        ((toData F (r1Rel F)).cB p.1) p.2
  have hb : ((toData F (r1Rel F)).cB p.1) ⟨0, (toData F (r1Rel F)).hdepB p.1⟩ = oneExp := by
    rw [r1RelData_b_pair_head F p.1]
  have hb2 : (((toData F (r1Rel F)).cB p.1) ⟨0, (toData F (r1Rel F)).hdepB p.1⟩ : ℕ) = 1 := by
    exact congrArg (fun u : ℕ+ => (u : ℕ)) hb
  have hfront : pad0 ((g5P2 F p.1).c p.2) 0 ≤ Nat.card F := by
    have hq : 1 ≤ Nat.card F := by
      have h2 := card_ge_two F
      omega
    have hNat : (qMinusExp F : ℕ) + 1 = Nat.card F := by
      change Nat.card F - 1 + 1 = Nat.card F
      have hq : 1 ≤ Nat.card F := by
        have h2 := card_ge_two F
        omega
      omega
    rw [hb2] at h1
    rw [hNat] at h1
    exact h1
  have hk2 : kAdmissible (Nat.card F) (consVec oneExp ((g5P2 F p.1).c p.2)) 2 := by
    exact kAdm2_cons_one (Nat.card F) (card_ge_two F) hge ((g5P2 F p.1).c p.2) hfront
  exact hk2


/-- ★ G5 CASE-2 (q,q) instance: the depth-2 (q,q) tuple (weight 2q) expands at level
2 into its BC-iterate b-members (weight-2q, 2-admissible). -/
theorem g5_case2_qq :
    AdmExp F ((qExp F : ℕ) + (qExp F : ℕ)) 2 (pair (qExp F) (qExp F)) := by
  classical
  let D := g5D F
  refine ⟨D.ιB, inferInstance, D.depB, D.hdepB, D.cB, (fun p => -(D.aB p)), ?_, ?_, ?_⟩
  · intro p
    change weight (D.depB p) (D.cB p) = (qExp F : ℕ) + (qExp F : ℕ)
    dsimp [D]
    exact g5D_member_weight F p
  · intro p
    change kAdmissible (Nat.card F) (D.cB p) 2
    dsimp [D]
    exact g5D_member_twoAdm F p
  · -- hid: ζ(pair q q) = Σ_p ((-(aB p) : RatFunc F) : K∞)·ζ(cB p)
    have hz : ζ_A F (pair (qExp F) (qExp F)) +
        (∑ p : D.ιB, (((D.aB p : RatFunc F) : RatFunc.CompletionAtInfty F) *
          ζ_A F (D.cB p))) = 0 := by
      dsimp [D]
      exact g5qq_zeta F
    calc
      ζ_A F (pair (qExp F) (qExp F)) =
          -(∑ p : D.ιB, (((D.aB p : RatFunc F) : RatFunc.CompletionAtInfty F) *
            ζ_A F (D.cB p))) := eq_neg_of_add_eq_zero_left hz
      _ = ∑ p : D.ιB, -(((D.aB p : RatFunc F) : RatFunc.CompletionAtInfty F) *
            ζ_A F (D.cB p)) := by
            rw [← Finset.sum_neg_distrib]
      _ = ∑ p : D.ιB, (((-(D.aB p : RatFunc F) : RatFunc F) : RatFunc.CompletionAtInfty F) *
            ζ_A F (D.cB p)) := by
            apply Finset.sum_congr rfl
            intro p hp
            exact (neg_coe_mul_zeta F (D.aB p) (D.cB p)).symm

end ZagierHoffmanPositiveChar
