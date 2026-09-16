import Submission.ZagierHoffmanProof.StepL35
import Submission.ZagierHoffmanProof.StepL32
set_option autoImplicit false
set_option maxHeartbeats 100000000
open Polynomial RatFunc
open scoped BigOperators
/-!
# Step L84: level-3 CASE-1 type-3 members are 2-admissible (SESSIONS 231-232)

probe_l3shape content, committed: for the level-3 (k=3) CASE-1 Prop-2.12 chains
the TYPE-3 members are 2-admissible at both j = 1 (s₀ < q = s₁, s₂ > q) and
j = 2 (s₁ < q, s₂ > q).  Together with StepL83's type-1/type-2 facts this closes
"every level-3 CASE-1 Step-1 member is 2-admissible" (no ¬2-adm member reaches
the A(2)-dispatch inside MAIN(3)'s CASE-1).  Mechanism: type-3 members are the
headAdd slot (position j−1 value s_{j−1}+1 ≤ q by s_{j−1} < q); their depth ≥ 3
(hB2/weight) kills the depth-2 (·,q) cond2₂ witness; the j=1 side's depth-2 form
is additionally killed by a weight argument (member weight = weight r s vs ≤ 2q).
-/

namespace ZagierHoffmanPositiveChar
attribute [instance] P2Data.fin
attribute [instance] RelData.finA
attribute [instance] RelData.finB
attribute [instance] FixedRel.fin
attribute [local instance] Classical.propDecidable
variable (F : Type*) [Field F] [Finite F] [DecidableEq (RatFunc F)]


/-! ## SESSION 231 — the level-3 kept-member SHAPE question (design item (i)).

CLAIM under test: for the level-3 (k=3, j=1) Step-1 chain (s₀ < q = s₁, s₂ > q),
every TYPE-3 member u = Q.c (Sum.inr (Sum.inr i)) has SECOND entry ≤ q.
If TRUE: u₁ = q+1 is IMPOSSIBLE for level-3 type-3 members, so the a2T_q1_all
class (s₀<q, s₁=q+1) does NOT arise among them — the Session-229 premise (reachable
kept member u=(2,4,2)@q=3, u₁=q+1) is contradicted, and the only level-3 kept
(¬2-adm) form is the depth-2 (s₀+1, q) tuple.
TRACE: type3_pad0_headAdd (j=1, t=1) ⟹ pad0 u 1 = pad0 (headAdd s₀ (D.cB i)) 1
= pad0 (D.cB i) 1 (headAdd keeps positions ≠ 0); D = BCq (toData R0) has
D.cB i = consVec oneExp (X.c i.2), X := p2WpT(q−1, R0.cB i.1); hence pad0 u 1 =
first entry of X.c i.2 ≤ (q−1) + head(R0.cB i.1) = q (X.hle LePad at m=1 + hbhd). -/

/-- headAdd keeps every position ≥ 1. -/
lemma pad0_headAdd_succ (v : ℕ+) {k : ℕ} (hk : 0 < k) (t : Fin k → ℕ+) (n : ℕ) :
    pad0 (headAdd v hk t) (n + 1) = pad0 t (n + 1) := by
  by_cases hn : n + 1 < k
  · rw [pad0_of_lt (headAdd v hk t) hn]
    rw [pad0_of_lt t hn]
    simp [headAdd]
  · have hge : k ≤ n + 1 := le_of_not_gt hn
    rw [pad0_of_ge (headAdd v hk t) hge]
    rw [pad0_of_ge t hge]

theorem level3_type3_entry_le_q (r : ℕ) (s : Fin r → ℕ+) (hr3 : 3 ≤ r)
    (hbig : (Nat.card F : ℕ) < (s ⟨2, by omega⟩ : ℕ))
    (hs0q : (s ⟨0, by omega⟩ : ℕ) < Nat.card F)
    (R0 : BinaryRel F)
    (hbhd : ∀ j' : R0.ιB, ((R0.cB j') ⟨0, R0.hdepB j'⟩ : ℕ) = 1) :
    let D := RelData.BCqIter F 1 (toData F R0)
    let Bs := ofBstarOver F D (s ⟨0, by omega⟩) (fun e => BCqIter_valid F 1 R0 e)
        (RelData.iterate_merge_hv F 1 R0 (s ⟨0, by omega⟩) (by omega) hbhd)
    let Q := FixedOver.prependList F Bs (sPrefix r s 1 (by omega) (by omega))
    ∀ i : D.ιB, pad0 (Q.c (Sum.inr (Sum.inr i))) 1 ≤ Nat.card F := by
  classical
  intro D Bs Q i
  have hp := type3_pad0_headAdd F r s 3 1 (by omega : 1 ≤ 3) hr3 (by omega : 1 ≤ 1)
    (by omega : 1 ≤ 3 - 1) hbig hs0q R0 hbhd i 1
  have hp1 : pad0 (Q.c (Sum.inr (Sum.inr i))) 1 =
      pad0 (headAdd (s ⟨0, by omega⟩) (D.hdepB i) (D.cB i)) 1 := by
    simpa using hp
  have hfib : D.cB i = consVec oneExp ((p2WpT F (qMinusExp F) (R0.hdepB i.1) (R0.cB i.1)).c i.2) := by
    change (RelData.BCq F (toData F R0)).cB i =
      consVec oneExp ((p2WpT F (qMinusExp F) (R0.hdepB i.1) (R0.cB i.1)).c i.2)
    rfl
  let X : P2Data F 1 (R0.depB i.1) (by omega : 0 < 1) (R0.hdepB i.1)
      (single (qMinusExp F)) (R0.cB i.1) :=
    p2WpT F (qMinusExp F) (R0.hdepB i.1) (R0.cB i.1)
  have hle1 := (X.hle i.2).2 1
  have hsumL : psum (X.c i.2) 1 = ((X.c i.2) ⟨0, X.hdep i.2⟩ : ℕ) := by
    rw [psum_succ, psum_zero]
    simp
    rw [pad0_of_lt (X.c i.2) (X.hdep i.2)]
  have hsumR : psumSeq (tupPadSum (single (qMinusExp F)) (R0.cB i.1)) 1 =
      (qMinusExp F : ℕ) + ((R0.cB i.1) ⟨0, R0.hdepB i.1⟩ : ℕ) := by
    dsimp [psumSeq, tupPadSum]
    change pad0 (single (qMinusExp F)) 0 + pad0 (R0.cB i.1) 0 =
      (qMinusExp F : ℕ) + ((R0.cB i.1) ⟨0, R0.hdepB i.1⟩ : ℕ)
    rw [pad0_single_zero]
    rw [pad0_of_lt (R0.cB i.1) (R0.hdepB i.1)]
  have hle2 : pad0 (X.c i.2) 0 ≤ Nat.card F := by
    have hb := hbhd i.1
    have hq : (qMinusExp F : ℕ) = Nat.card F - 1 := by rfl
    calc
      pad0 (X.c i.2) 0 = ((X.c i.2) ⟨0, X.hdep i.2⟩ : ℕ) := by
            rw [pad0_of_lt (X.c i.2) (X.hdep i.2)]
      _ = psum (X.c i.2) 1 := hsumL.symm
      _ ≤ psumSeq (tupPadSum (single (qMinusExp F)) (R0.cB i.1)) 1 := hle1
      _ = (qMinusExp F : ℕ) + ((R0.cB i.1) ⟨0, R0.hdepB i.1⟩ : ℕ) := hsumR
      _ = Nat.card F - 1 + 1 := by rw [hq, hb]
      _ = Nat.card F := by
        have h2 : 2 ≤ Nat.card F := card_ge_two F
        omega
  calc
    pad0 (Q.c (Sum.inr (Sum.inr i))) 1
        = pad0 (headAdd (s ⟨0, by omega⟩) (D.hdepB i) (D.cB i)) 1 := hp1
    _ = pad0 (D.cB i) 1 := by
          rw [pad0_headAdd_succ (s ⟨0, by omega⟩) (D.hdepB i) (D.cB i) 0]
    _ = pad0 ((p2WpT F (qMinusExp F) (R0.hdepB i.1) (R0.cB i.1)).c i.2) 0 := by
          rw [hfib]
          change pad0 (consVec oneExp ((p2WpT F (qMinusExp F) (R0.hdepB i.1) (R0.cB i.1)).c i.2)) 1 =
            pad0 ((p2WpT F (qMinusExp F) (R0.hdepB i.1) (R0.cB i.1)).c i.2) 0
          rw [pad0_consVec]
    _ = pad0 (X.c i.2) 0 := rfl
    _ ≤ Nat.card F := hle2

/-- Position-0 of the level-3 j=1 type-3 member is the merged head s₀+1. -/
lemma pad0_headAdd_zero (v : ℕ+) {k : ℕ} (hk : 0 < k) (t : Fin k → ℕ+) :
    pad0 (headAdd v hk t) 0 = (v : ℕ) + (t ⟨0, hk⟩ : ℕ) := by
  rw [pad0_of_lt (headAdd v hk t) (by omega : 0 < k)]
  simp [headAdd]

theorem level3_type3_entry0_eq_s0_add_one (r : ℕ) (s : Fin r → ℕ+) (hr3 : 3 ≤ r)
    (hbig : (Nat.card F : ℕ) < (s ⟨2, by omega⟩ : ℕ))
    (hs0q : (s ⟨0, by omega⟩ : ℕ) < Nat.card F)
    (R0 : BinaryRel F)
    (hbhd : ∀ j' : R0.ιB, ((R0.cB j') ⟨0, R0.hdepB j'⟩ : ℕ) = 1) :
    let D := RelData.BCqIter F 1 (toData F R0)
    let Bs := ofBstarOver F D (s ⟨0, by omega⟩) (fun e => BCqIter_valid F 1 R0 e)
        (RelData.iterate_merge_hv F 1 R0 (s ⟨0, by omega⟩) (by omega) hbhd)
    let Q := FixedOver.prependList F Bs (sPrefix r s 1 (by omega) (by omega))
    ∀ i : D.ιB, pad0 (Q.c (Sum.inr (Sum.inr i))) 0 = (s ⟨0, by omega⟩ : ℕ) + 1 := by
  classical
  intro D Bs Q i
  have hp := type3_pad0_headAdd F r s 3 1 (by omega : 1 ≤ 3) hr3 (by omega : 1 ≤ 1)
    (by omega : 1 ≤ 3 - 1) hbig hs0q R0 hbhd i 0
  have hp0 : pad0 (Q.c (Sum.inr (Sum.inr i))) 0 =
      pad0 (headAdd (s ⟨0, by omega⟩) (D.hdepB i) (D.cB i)) 0 := by
    simpa using hp
  have hfib : D.cB i = consVec oneExp ((p2WpT F (qMinusExp F) (R0.hdepB i.1) (R0.cB i.1)).c i.2) := by
    change (RelData.BCq F (toData F R0)).cB i =
      consVec oneExp ((p2WpT F (qMinusExp F) (R0.hdepB i.1) (R0.cB i.1)).c i.2)
    rfl
  have hhead : ((D.cB i) ⟨0, D.hdepB i⟩ : ℕ) = 1 := by
    rw [hfib]
    change (((consVec oneExp ((p2WpT F (qMinusExp F) (R0.hdepB i.1) (R0.cB i.1)).c i.2))
      ⟨0, (RelData.BCq F (toData F R0)).hdepB i⟩) : ℕ) = 1
    rw [consVec_zero]
    rfl
  calc
    pad0 (Q.c (Sum.inr (Sum.inr i))) 0
        = pad0 (headAdd (s ⟨0, by omega⟩) (D.hdepB i) (D.cB i)) 0 := hp0
    _ = (s ⟨0, by omega⟩ : ℕ) + ((D.cB i) ⟨0, D.hdepB i⟩ : ℕ) := by
          rw [pad0_headAdd_zero (s ⟨0, by omega⟩) (D.hdepB i) (D.cB i)]
    _ = (s ⟨0, by omega⟩ : ℕ) + 1 := by rw [hhead]

theorem level3_type3_entry0_le_q (r : ℕ) (s : Fin r → ℕ+) (hr3 : 3 ≤ r)
    (hbig : (Nat.card F : ℕ) < (s ⟨2, by omega⟩ : ℕ))
    (hs0q : (s ⟨0, by omega⟩ : ℕ) < Nat.card F)
    (R0 : BinaryRel F)
    (hbhd : ∀ j' : R0.ιB, ((R0.cB j') ⟨0, R0.hdepB j'⟩ : ℕ) = 1) :
    let D := RelData.BCqIter F 1 (toData F R0)
    let Bs := ofBstarOver F D (s ⟨0, by omega⟩) (fun e => BCqIter_valid F 1 R0 e)
        (RelData.iterate_merge_hv F 1 R0 (s ⟨0, by omega⟩) (by omega) hbhd)
    let Q := FixedOver.prependList F Bs (sPrefix r s 1 (by omega) (by omega))
    ∀ i : D.ιB, pad0 (Q.c (Sum.inr (Sum.inr i))) 0 ≤ Nat.card F := by
  classical
  intro D Bs Q i
  have heq := level3_type3_entry0_eq_s0_add_one F r s hr3 hbig hs0q R0 hbhd i
  have h0 : ((s ⟨0, by omega⟩ : ℕ) + 1) ≤ Nat.card F := by
    omega
  rw [heq]
  exact h0

/-- VERDICT theorem: every type-3 member of the level-3 (k=3, j=1) Step-1 chain of
an in-domain input s (s₀ < q = s₁, s₂ > q, depth ≥ 3) is 2-admissible.  Hence no
¬2-adm member ever reaches the A(2)-dispatch inside MAIN(3): the Session-229
β-premise (kept member u with u₁ = q+1, e.g. (2,4,2)@q=3) cannot occur at level 3. -/
theorem level3_j1_type3_twoAdm (r : ℕ) (s : Fin r → ℕ+) (hr3 : 3 ≤ r)
    (hbig : (Nat.card F : ℕ) < (s ⟨2, by omega⟩ : ℕ))
    (hs0q : (s ⟨0, by omega⟩ : ℕ) < Nat.card F)
    (hs1q : (s ⟨1, by omega⟩ : ℕ) = Nat.card F) :
    ∃ (R0 : BinaryRel F) (u : R0.ιA)
      (hbhd : ∀ j' : R0.ιB, ((R0.cB j') ⟨0, R0.hdepB j'⟩ : ℕ) = 1),
      let D := RelData.BCqIter F 1 (toData F R0)
      let Bs := ofBstarOver F D (s ⟨0, by omega⟩) (fun e => BCqIter_valid F 1 R0 e)
          (RelData.iterate_merge_hv F 1 R0 (s ⟨0, by omega⟩) (by omega) hbhd)
      let Q := FixedOver.prependList F Bs (sPrefix r s 1 (by omega) (by omega))
      ∀ i : D.ιB, kAdmissible (Nat.card F) (Q.c (Sum.inr (Sum.inr i))) 2 := by
  classical
  have hmid : ∀ i : Fin r, (1 : ℕ) ≤ (i : ℕ) → (i : ℕ) < 2 → (s i : ℕ) = Nat.card F := by
    intro i hi1 hi2
    have hiv : (i : ℕ) = 1 := by omega
    have hidx : i = ⟨1, (by omega : 1 < r)⟩ := by
      apply Fin.ext
      exact hiv
    rw [hidx]
    exact hs1q
  have hsleq : ∀ x : ℕ, x < 2 → pad0 s x ≤ Nat.card F := by
    intro x hx
    have hx01 : x = 0 ∨ x = 1 := by omega
    rcases hx01 with hx0 | hx1
    · subst x
      have hp : pad0 s 0 = (s ⟨0, by omega⟩ : ℕ) := pad0_of_lt s (by omega : 0 < r)
      rw [hp]
      omega
    · subst x
      have hp : pad0 s 1 = (s ⟨1, by omega⟩ : ℕ) := pad0_of_lt s (by omega : 1 < r)
      rw [hp]
      rw [hs1q]
  rcases prop212_step1 F r s 3 1 (by omega : 1 ≤ 3) hr3 (by omega : 1 ≤ 1)
    (by omega : 1 ≤ 3 - 1) hbig hs0q hmid hsleq with
    ⟨R0, u, hbhd, ha, hdep0, hc0, hrel, ht1, ht2, ht3⟩
  refine ⟨R0, u, hbhd, ?_⟩
  intro D Bs Q i
  constructor
  · intro x hx
    have hx01 : x = 0 ∨ x = 1 := by omega
    rcases hx01 with hx0 | hx1
    · subst x
      exact level3_type3_entry0_le_q F r s hr3 hbig hs0q R0 hbhd i
    · subst x
      exact level3_type3_entry_le_q F r s hr3 hbig hs0q R0 hbhd i
  · intro hform
    rcases hform with ⟨hr1, hdep2, hall, hlast⟩
    have hdepge : 2 ≤ Q.dep (Sum.inr (Sum.inr i)) := by
      have hq : Q.dep (Sum.inr (Sum.inr i)) = D.depB i := by
        dsimp [Q, Bs, D, ofBstarOver]
        rfl
      rw [hq]
      have hb := D.hB2 i
      omega
    have hwmem : weight (Q.dep (Sum.inr (Sum.inr i))) (Q.c (Sum.inr (Sum.inr i))) =
        weight r s := by
      simpa [D, Bs, Q] using (ht3 i).1
    have hwsum : weight (Q.dep (Sum.inr (Sum.inr i))) (Q.c (Sum.inr (Sum.inr i))) =
        pad0 (Q.c (Sum.inr (Sum.inr i))) 0 + pad0 (Q.c (Sum.inr (Sum.inr i))) 1 := by
      have hdep2' : Q.dep (Sum.inr (Sum.inr i)) = 2 := by omega
      have hps := psum_self (Q.c (Sum.inr (Sum.inr i)))
      -- weight u = psum u (depth) = psum u 2 = pad0 0 + pad0 1
      calc
        weight (Q.dep (Sum.inr (Sum.inr i))) (Q.c (Sum.inr (Sum.inr i)))
            = psum (Q.c (Sum.inr (Sum.inr i))) (Q.dep (Sum.inr (Sum.inr i))) := hps.symm
        _ = psum (Q.c (Sum.inr (Sum.inr i))) 2 := by
              exact congrArg (psum (Q.c (Sum.inr (Sum.inr i)))) hdep2' 
        _ = pad0 (Q.c (Sum.inr (Sum.inr i))) 0 + pad0 (Q.c (Sum.inr (Sum.inr i))) 1 := by
              rw [psum_succ, psum_succ]
              rw [psum_zero]
              simp
    have hu0 : pad0 (Q.c (Sum.inr (Sum.inr i))) 0 = (s ⟨0, by omega⟩ : ℕ) + 1 :=
      level3_type3_entry0_eq_s0_add_one F r s hr3 hbig hs0q R0 hbhd i
    have hle1 : pad0 (Q.c (Sum.inr (Sum.inr i))) 1 ≤ Nat.card F :=
      level3_type3_entry_le_q F r s hr3 hbig hs0q R0 hbhd i
    have hwle : weight (Q.dep (Sum.inr (Sum.inr i))) (Q.c (Sum.inr (Sum.inr i))) ≤
        (s ⟨0, by omega⟩ : ℕ) + Nat.card F + 1 := by
      rw [hwsum, hu0]
      omega
    have hwlow : (s ⟨0, by omega⟩ : ℕ) + Nat.card F + 1 < weight r s := by
      have hp0 : pad0 s 0 = (s ⟨0, by omega⟩ : ℕ) := pad0_of_lt s (by omega : 0 < r)
      have hp1 : pad0 s 1 = (s ⟨1, by omega⟩ : ℕ) := pad0_of_lt s (by omega : 1 < r)
      have hp2 : pad0 s 2 = (s ⟨2, by omega⟩ : ℕ) := pad0_of_lt s (by omega : 2 < r)
      have hpsle : psum s 3 ≤ weight r s := psum_le_weight s 3
      have hpsum3 : psum s 3 = (s ⟨0, by omega⟩ : ℕ) + (s ⟨1, by omega⟩ : ℕ) + (s ⟨2, by omega⟩ : ℕ) := by
        change (∑ j ∈ Finset.range 3, pad0 s j) =
          (s ⟨0, by omega⟩ : ℕ) + (s ⟨1, by omega⟩ : ℕ) + (s ⟨2, by omega⟩ : ℕ)
        rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ]
        simp
        rw [hp0, hp1, hp2]
      rw [hpsum3] at hpsle
      have hq2 : 2 ≤ Nat.card F := card_ge_two F
      omega
    omega

/-! ## SESSION 232 — level-3 j=2 chains (s₁ < q, s₂ > q): type-3 members are 2-adm.

Mirror of the j=1 proof.  At j=2 the iterate count is k−j−1 = 0 (D = toData R0),
the front is [s₀] (length j−1 = 1), and the type-3 member is
consVec s₀ (headAdd s₁ (D.cB i)) with D.cB = R0.cB (heads 1): entry-0 = s₀
(member_prefix_pos at m = 0 < j−1), entry-1 = s₁ + 1 (type3_pad0_headAdd at
t = 0 + pad0_headAdd_zero + hbhd), depth = 1 + D.depB ≥ 3 (D.hB2) — so cond1
(s₀ ≤ q, s₁+1 ≤ q via s₁ < q) and no depth-2 form: 2-adm without any weight
argument. -/

theorem level3_j2_type3_entry1_eq (r : ℕ) (s : Fin r → ℕ+) (hr3 : 3 ≤ r)
    (hbig : (Nat.card F : ℕ) < (s ⟨2, by omega⟩ : ℕ))
    (hs1q : (s ⟨1, by omega⟩ : ℕ) < Nat.card F)
    (R0 : BinaryRel F)
    (hbhd : ∀ j' : R0.ιB, ((R0.cB j') ⟨0, R0.hdepB j'⟩ : ℕ) = 1) :
    let D := RelData.BCqIter F 0 (toData F R0)
    let Bs := ofBstarOver F D (s ⟨1, by omega⟩) (fun e => BCqIter_valid F 0 R0 e)
        (RelData.iterate_merge_hv F 0 R0 (s ⟨1, by omega⟩) (by omega) hbhd)
    let Q := FixedOver.prependList F Bs (sPrefix r s 2 (by omega) (by omega))
    ∀ i : D.ιB, pad0 (Q.c (Sum.inr (Sum.inr i))) 1 = (s ⟨1, by omega⟩ : ℕ) + 1 := by
  classical
  intro D Bs Q i
  have hp := type3_pad0_headAdd F r s 3 2 (by omega : 1 ≤ 3) hr3 (by omega : 1 ≤ 2)
    (by omega : 2 ≤ 3 - 1) hbig hs1q R0 hbhd i 0
  have hp1 : pad0 (Q.c (Sum.inr (Sum.inr i))) 1 =
      pad0 (headAdd (s ⟨1, by omega⟩) (D.hdepB i) (D.cB i)) 0 := by
    simpa using hp
  have hdhead : ((D.cB i) ⟨0, D.hdepB i⟩ : ℕ) = 1 := by
    have hfib : D.cB i = R0.cB i := by
      change (toData F R0).cB i = R0.cB i
      rfl
    rw [hfib]
    exact hbhd i
  calc
    pad0 (Q.c (Sum.inr (Sum.inr i))) 1
        = pad0 (headAdd (s ⟨1, by omega⟩) (D.hdepB i) (D.cB i)) 0 := hp1
    _ = (s ⟨1, by omega⟩ : ℕ) + ((D.cB i) ⟨0, D.hdepB i⟩ : ℕ) := by
          rw [pad0_headAdd_zero (s ⟨1, by omega⟩) (D.hdepB i) (D.cB i)]
    _ = (s ⟨1, by omega⟩ : ℕ) + 1 := by rw [hdhead]

theorem level3_j2_type3_entry0_eq (r : ℕ) (s : Fin r → ℕ+) (hr3 : 3 ≤ r)
    (hbig : (Nat.card F : ℕ) < (s ⟨2, by omega⟩ : ℕ))
    (hs1q : (s ⟨1, by omega⟩ : ℕ) < Nat.card F)
    (R0 : BinaryRel F)
    (hbhd : ∀ j' : R0.ιB, ((R0.cB j') ⟨0, R0.hdepB j'⟩ : ℕ) = 1) :
    let D := RelData.BCqIter F 0 (toData F R0)
    let Bs := ofBstarOver F D (s ⟨1, by omega⟩) (fun e => BCqIter_valid F 0 R0 e)
        (RelData.iterate_merge_hv F 0 R0 (s ⟨1, by omega⟩) (by omega) hbhd)
    let Q := FixedOver.prependList F Bs (sPrefix r s 2 (by omega) (by omega))
    ∀ i : D.ιB, pad0 (Q.c (Sum.inr (Sum.inr i))) 0 = (s ⟨0, by omega⟩ : ℕ) := by
  classical
  intro D Bs Q i
  have hQ0 : 0 < Q.dep (Sum.inr (Sum.inr i)) := by
    have hQd : Q.dep (Sum.inr (Sum.inr i)) = D.depB i + 1 := by
      have h1 := FixedOver.prependList_dep F Bs (sPrefix r s 2 (by omega) (by omega))
        (Sum.inr (Sum.inr i))
      have h2 : Bs.dep (Sum.inr (Sum.inr i)) = D.depB i := by
        dsimp [Bs, ofBstarOver]
      have hlen : (sPrefix r s 2 (by omega) (by omega)).length = 1 :=
        sPrefix_length r s 2 (by omega) (by omega)
      rw [h1, h2, hlen]
    rw [hQd]
    omega
  have hv := member_prefix_pos F r s 3 2 (by omega : 1 ≤ 3) hr3 (by omega : 1 ≤ 2)
    (by omega : 2 ≤ 3 - 1) hbig hs1q R0 hbhd (Sum.inr (Sum.inr i)) 0
    (by omega : 0 < 2 - 1) hQ0
  rw [pad0_of_lt (Q.c (Sum.inr (Sum.inr i))) hQ0]
  exact congrArg (fun t : ℕ+ => (t : ℕ)) hv

theorem level3_j2_type3_entry1_le_q (r : ℕ) (s : Fin r → ℕ+) (hr3 : 3 ≤ r)
    (hbig : (Nat.card F : ℕ) < (s ⟨2, by omega⟩ : ℕ))
    (hs1q : (s ⟨1, by omega⟩ : ℕ) < Nat.card F)
    (R0 : BinaryRel F)
    (hbhd : ∀ j' : R0.ιB, ((R0.cB j') ⟨0, R0.hdepB j'⟩ : ℕ) = 1) :
    let D := RelData.BCqIter F 0 (toData F R0)
    let Bs := ofBstarOver F D (s ⟨1, by omega⟩) (fun e => BCqIter_valid F 0 R0 e)
        (RelData.iterate_merge_hv F 0 R0 (s ⟨1, by omega⟩) (by omega) hbhd)
    let Q := FixedOver.prependList F Bs (sPrefix r s 2 (by omega) (by omega))
    ∀ i : D.ιB, pad0 (Q.c (Sum.inr (Sum.inr i))) 1 ≤ Nat.card F := by
  classical
  intro D Bs Q i
  have heq := level3_j2_type3_entry1_eq F r s hr3 hbig hs1q R0 hbhd i
  rw [heq]
  omega

theorem level3_j2_type3_twoAdm (r : ℕ) (s : Fin r → ℕ+) (hr3 : 3 ≤ r)
    (hbig : (Nat.card F : ℕ) < (s ⟨2, by omega⟩ : ℕ))
    (hs0 : (s ⟨0, by omega⟩ : ℕ) ≤ Nat.card F)
    (hs1q : (s ⟨1, by omega⟩ : ℕ) < Nat.card F)
    (R0 : BinaryRel F)
    (hbhd : ∀ j' : R0.ιB, ((R0.cB j') ⟨0, R0.hdepB j'⟩ : ℕ) = 1) :
    let D := RelData.BCqIter F 0 (toData F R0)
    let Bs := ofBstarOver F D (s ⟨1, by omega⟩) (fun e => BCqIter_valid F 0 R0 e)
        (RelData.iterate_merge_hv F 0 R0 (s ⟨1, by omega⟩) (by omega) hbhd)
    let Q := FixedOver.prependList F Bs (sPrefix r s 2 (by omega) (by omega))
    ∀ i : D.ιB, kAdmissible (Nat.card F) (Q.c (Sum.inr (Sum.inr i))) 2 := by
  classical
  intro D Bs Q i
  constructor
  · intro x hx
    have hx01 : x = 0 ∨ x = 1 := by omega
    rcases hx01 with hx0 | hx1
    · subst x
      have heq := level3_j2_type3_entry0_eq F r s hr3 hbig hs1q R0 hbhd i
      rw [heq]
      exact hs0
    · subst x
      have heq := level3_j2_type3_entry1_eq F r s hr3 hbig hs1q R0 hbhd i
      rw [heq]
      omega
  · intro hform
    rcases hform with ⟨hr1, hdep2f, hall, hlast⟩
    have hdge : 3 ≤ Q.dep (Sum.inr (Sum.inr i)) := by
      have hQd : Q.dep (Sum.inr (Sum.inr i)) = D.depB i + 1 := by
        have h1 := FixedOver.prependList_dep F Bs (sPrefix r s 2 (by omega) (by omega))
          (Sum.inr (Sum.inr i))
        have h2 : Bs.dep (Sum.inr (Sum.inr i)) = D.depB i := by
          dsimp [Bs, ofBstarOver]
        have hlen : (sPrefix r s 2 (by omega) (by omega)).length = 1 :=
          sPrefix_length r s 2 (by omega) (by omega)
        rw [h1, h2, hlen]
      rw [hQd]
      have hb := D.hB2 i
      omega
    omega
end ZagierHoffmanPositiveChar
