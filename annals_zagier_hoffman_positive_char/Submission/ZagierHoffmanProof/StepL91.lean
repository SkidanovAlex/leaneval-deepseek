import Submission.ZagierHoffmanProof.StepL44
import Submission.ZagierHoffmanProof.StepL49
set_option autoImplicit false
set_option maxHeartbeats 100000000
open Polynomial RatFunc
open scoped BigOperators
/-!
# Step L91: the (a,q,q) CASE-2 j=1 member 2-adm facts (SESSION 234, committed 248)

The level-3 CASE-2 subcase (a, q, q) with a < q (b = q is not < q, so the
Prop-2.13 chain has iterate k−j−1 = 1 over r1Rel at head a, empty front):
  ★ case2j1_type3_entry_le_q (a) (ha : a < q) : ∀ i : D.ιB,
      pad0 (Bs.c (Sum.inr (Sum.inr i))) 1 ≤ q  (type-3 = headAdd a (D.cB i));
  ★ case2j1_type2_twoAdm (a) (ha) : every type-2 member (consVec a (D.cB i),
      D := BCqIter F 1 (toData r1Rel), D.cB i = consVec oneExp (X.c i.2),
      X := p2WpT(q−1, r1Rel.cB)) is 2-adm;
  ★ case2j1_type3_twoAdm (a) (ha) : every type-3 member is 2-adm (the
      depth-2 (·,q)-form is killed by weight w = 2q+a > q+1+a... via prop213's
      weight conjunct).
NOT a 3-adm leaf: type-3 members can be ¬3-adm (later X-output entries > q) —
they are in-domain and go to the MAIN(3) recursion.  main3's CASE-2 b=q∧a<q
branch will use these facts (per-member dispatch) in its ζ-identity/e/horder/rec
assembly (mirroring main3_case1_j1's script at r = 3 with the (3,1)-chain D :=
BCqIter F 1 over r1Rel).  theorem_B/D remain ABP-gated (no route).
-/

namespace ZagierHoffmanPositiveChar
attribute [instance] P2Data.fin
attribute [instance] RelData.finA
attribute [instance] RelData.finB
attribute [instance] FixedRel.fin
attribute [local instance] Classical.propDecidable
variable (F : Type*) [Field F] [Finite F] [DecidableEq (RatFunc F)]

/-! ## SESSION 234 — the (a,q,q) CASE-2 j=1 side at level 3.

Input s := (a, q, q) (depth 3, a < q): 2-adm ∧ ¬3-adm via the depth-3 form, but
j = 1 (b = q is not < q) — the iterate-1 R1 chain over r1Rel at head a, empty
front:  D := BCqIter F 1 (toData r1Rel),  Bs := ofBstarOver F D a,  Q = Bs.
Type-2 members = consVec a (D.cB i);  type-3 members = headAdd a (D.cB i), with
D.cB i = consVec oneExp (X.c i.2), X := p2WpT(q−1, r1Rel.cB) (one BCq step).
CLAIMS (the (β)-closure on this side): all type-2 AND type-3 members are 2-adm.
NOT a 3-adm leaf: type-3 members can be ¬3-adm (entry-2 = later X-output entries
> q, e.g. X-output (1, 2q−2)-type) — they are 2-adm∧¬3-adm in-domain and go to the
MAIN(3) recursion.  -/

/-- headAdd keeps positions ≥ 1 (position-0 is the merged head). -/
lemma pad0_headAdd_zero (v : ℕ+) {k : ℕ} (hk : 0 < k) (t : Fin k → ℕ+) :
    pad0 (headAdd v hk t) 0 = (v : ℕ) + (t ⟨0, hk⟩ : ℕ) := by
  rw [pad0_of_lt (headAdd v hk t) (by omega : 0 < k)]
  simp [headAdd]

theorem case2j1_type3_entry_le_q (a : ℕ+) (ha : (a : ℕ) < Nat.card F) :
    let D := RelData.BCqIter F 1 (toData F (r1Rel F))
    let Bs := ofBstarOver F D a (fun e => BCqIter_valid F 1 (r1Rel F) e)
        (RelData.iterate_merge_hv F 1 (r1Rel F) a (by omega) (r1Rel_hbhd F))
    ∀ i : D.ιB, pad0 (Bs.c (Sum.inr (Sum.inr i))) 1 ≤ Nat.card F := by
  classical
  intro D Bs i
  -- type-3 member = headAdd a (D.cB i) (empty-front B*-inr-inr slot)
  have hu : Bs.c (Sum.inr (Sum.inr i)) = headAdd a (D.hdepB i) (D.cB i) := by
    dsimp [Bs, D, ofBstarOver]
  have hfib : D.cB i = consVec oneExp ((p2WpT F (qMinusExp F) ((r1Rel F).hdepB i.1)
      ((r1Rel F).cB i.1)).c i.2) := by
    change (RelData.BCq F (toData F (r1Rel F))).cB i =
      consVec oneExp ((p2WpT F (qMinusExp F) ((toData F (r1Rel F)).hdepB i.1)
        ((toData F (r1Rel F)).cB i.1)).c i.2)
    rfl
  -- position-1 of headAdd keeps D.cB (type-3 slot is defeq to headAdd)
  have hu1 : pad0 (Bs.c (Sum.inr (Sum.inr i))) 1 = pad0 (D.cB i) 1 := by
    change pad0 (headAdd a (D.hdepB i) (D.cB i)) 1 = pad0 (D.cB i) 1
    by_cases hn : 1 < D.depB i
    · rw [pad0_of_lt (headAdd a (D.hdepB i) (D.cB i)) hn]
      rw [pad0_of_lt (D.cB i) hn]
      dsimp [headAdd]
    · have hge : D.depB i ≤ 1 := le_of_not_gt hn
      rw [pad0_of_ge (headAdd a (D.hdepB i) (D.cB i)) hge]
      rw [pad0_of_ge (D.cB i) hge]
  let X : P2Data F 1 ((r1Rel F).depB i.1) (by omega : 0 < 1) ((r1Rel F).hdepB i.1)
      (single (qMinusExp F)) ((r1Rel F).cB i.1) :=
    p2WpT F (qMinusExp F) ((r1Rel F).hdepB i.1) ((r1Rel F).cB i.1)
  have hle1 := (X.hle i.2).2 1
  have hsumL : psum (X.c i.2) 1 = ((X.c i.2) ⟨0, X.hdep i.2⟩ : ℕ) := by
    rw [psum_succ, psum_zero]
    simp
    rw [pad0_of_lt (X.c i.2) (X.hdep i.2)]
  have hsumR : psumSeq (tupPadSum (single (qMinusExp F)) ((r1Rel F).cB i.1)) 1 =
      (qMinusExp F : ℕ) + ((r1Rel F).cB i.1) ⟨0, (r1Rel F).hdepB i.1⟩ := by
    dsimp [psumSeq, tupPadSum]
    change pad0 (single (qMinusExp F)) 0 + pad0 ((r1Rel F).cB i.1) 0 =
      (qMinusExp F : ℕ) + (((r1Rel F).cB i.1) ⟨0, (r1Rel F).hdepB i.1⟩ : ℕ)
    rw [pad0_single_zero]
    rw [pad0_of_lt ((r1Rel F).cB i.1) ((r1Rel F).hdepB i.1)]
  have hle2 : pad0 (X.c i.2) 0 ≤ Nat.card F := by
    have hb := r1Rel_hbhd F i.1
    have hq : (qMinusExp F : ℕ) = Nat.card F - 1 := rfl
    calc
      pad0 (X.c i.2) 0 = ((X.c i.2) ⟨0, X.hdep i.2⟩ : ℕ) := by
            rw [pad0_of_lt (X.c i.2) (X.hdep i.2)]
      _ = psum (X.c i.2) 1 := hsumL.symm
      _ ≤ psumSeq (tupPadSum (single (qMinusExp F)) ((r1Rel F).cB i.1)) 1 := hle1
      _ = (qMinusExp F : ℕ) + (((r1Rel F).cB i.1) ⟨0, (r1Rel F).hdepB i.1⟩ : ℕ) := hsumR
      _ = Nat.card F - 1 + 1 := by rw [hq, hb]
      _ = Nat.card F := by
        have h2 : 2 ≤ Nat.card F := card_ge_two F
        omega
  calc
    pad0 (Bs.c (Sum.inr (Sum.inr i))) 1
        = pad0 (D.cB i) 1 := hu1
    _ = pad0 ((p2WpT F (qMinusExp F) ((r1Rel F).hdepB i.1) ((r1Rel F).cB i.1)).c i.2) 0 := by
          rw [hfib]
          change pad0 (consVec oneExp ((p2WpT F (qMinusExp F) ((r1Rel F).hdepB i.1) ((r1Rel F).cB i.1)).c i.2)) 1 =
            pad0 ((p2WpT F (qMinusExp F) ((r1Rel F).hdepB i.1) ((r1Rel F).cB i.1)).c i.2) 0
          rw [pad0_consVec]
    _ = pad0 (X.c i.2) 0 := rfl
    _ ≤ Nat.card F := hle2

/-- Type-2 members of the (a,q,q) j=1 R1 chain are 2-adm: member = consVec a
(D.cB i), entries (a, 1, …), depth ≥ 3 — pure structure. -/
theorem case2j1_type2_twoAdm (a : ℕ+) (ha : (a : ℕ) < Nat.card F) :
    let D := RelData.BCqIter F 1 (toData F (r1Rel F))
    let Bs := ofBstarOver F D a (fun e => BCqIter_valid F 1 (r1Rel F) e)
        (RelData.iterate_merge_hv F 1 (r1Rel F) a (by omega) (r1Rel_hbhd F))
    ∀ i : D.ιB, kAdmissible (Nat.card F) (Bs.c (Sum.inr (Sum.inl i))) 2 := by
  classical
  intro D Bs i
  have hc1 : pad0 (Bs.c (Sum.inr (Sum.inl i))) 0 = (a : ℕ) := by
    dsimp [Bs, D, ofBstarOver]
    rw [pad0_of_lt (consVec a (D.cB i)) (by omega : 0 < D.depB i + 1)]
    rfl
  have hfib : D.cB i = consVec oneExp ((p2WpT F (qMinusExp F) ((r1Rel F).hdepB i.1)
      ((r1Rel F).cB i.1)).c i.2) := by
    change (RelData.BCq F (toData F (r1Rel F))).cB i =
      consVec oneExp ((p2WpT F (qMinusExp F) ((toData F (r1Rel F)).hdepB i.1)
        ((toData F (r1Rel F)).cB i.1)).c i.2)
    rfl
  have hdhead : ((D.cB i) ⟨0, D.hdepB i⟩ : ℕ) = 1 := by
    rw [hfib]
    change (((consVec oneExp ((p2WpT F (qMinusExp F) ((r1Rel F).hdepB i.1) ((r1Rel F).cB i.1)).c i.2))
      ⟨0, (RelData.BCq F (toData F (r1Rel F))).hdepB i⟩) : ℕ) = 1
    rw [consVec_zero]
    rfl
  have hc2 : pad0 (Bs.c (Sum.inr (Sum.inl i))) 1 = 1 := by
    dsimp [Bs, D, ofBstarOver]
    rw [pad0_consVec]
    rw [pad0_of_lt (D.cB i) (D.hdepB i)]
    exact hdhead
  have hdge : 3 ≤ Bs.dep (Sum.inr (Sum.inl i)) := by
    have hd : Bs.dep (Sum.inr (Sum.inl i)) = D.depB i + 1 := by
      dsimp [Bs, D, ofBstarOver]
    rw [hd]
    have hb := D.hB2 i
    omega
  constructor
  · intro x hx
    have hx01 : x = 0 ∨ x = 1 := by omega
    rcases hx01 with hx0 | hx1
    · subst x
      rw [hc1]
      omega
    · subst x
      rw [hc2]
      have hq2 : 2 ≤ Nat.card F := card_ge_two F
      omega
  · intro hf
    rcases hf with ⟨hr1, hdep2f, hall, hlast⟩
    omega

/-- Type-3 members of the (a,q,q) j=1 R1 chain are 2-adm.  cond1 from the entry
lemmas; the depth-2-form alternative is killed by weight: prop213 at (3,1) gives
member weight = weight 3 (a,q,q) = a+2q ≥ 2q+1, while a depth-2-form member would
weigh ≤ 2q. -/
theorem case2j1_type3_twoAdm (a : ℕ+) (ha : (a : ℕ) < Nat.card F) :
    let D := RelData.BCqIter F 1 (toData F (r1Rel F))
    let Bs := ofBstarOver F D a (fun e => BCqIter_valid F 1 (r1Rel F) e)
        (RelData.iterate_merge_hv F 1 (r1Rel F) a (by omega) (r1Rel_hbhd F))
    let Q := FixedOver.prependList F Bs (sPrefix 3 (consVec a (pair (qExp F) (qExp F))) 1 (by omega) (by omega))
    ∀ i : D.ιB, kAdmissible (Nat.card F) (Q.c (Sum.inr (Sum.inr i))) 2 := by
  classical
  intro D Bs Q i
  let s : Fin 3 → ℕ+ := consVec a (pair (qExp F) (qExp F))
  have hs0v : (s ⟨0, by omega⟩ : ℕ) = (a : ℕ) := by
    dsimp [s]
    rfl
  have hsj : (s ⟨0, by omega⟩ : ℕ) < Nat.card F := by
    rw [hs0v]
    exact ha
  have hqend : ∀ i' : Fin 3, (1 : ℕ) ≤ (i' : ℕ) → (i' : ℕ) < 3 → (s i' : ℕ) = Nat.card F := by
    intro i' hi1 hi2
    have hiv : (i' : ℕ) = 1 ∨ (i' : ℕ) = 2 := by omega
    rcases hiv with hi'1 | hi'2
    · have hidx : i' = ⟨1, (by omega : 1 < 3)⟩ := by
        apply Fin.ext
        omega
      rw [hidx]
      dsimp [s]
      rfl
    · have hidx : i' = ⟨2, (by omega : 2 < 3)⟩ := by
        apply Fin.ext
        omega
      rw [hidx]
      dsimp [s]
      rfl
  have hsleq : ∀ x : ℕ, x < 2 → pad0 s x ≤ Nat.card F := by
    intro x hx
    have hx01 : x = 0 ∨ x = 1 := by omega
    rcases hx01 with hx0 | hx1
    · subst x
      have hp : pad0 s 0 = (s ⟨0, by omega⟩ : ℕ) := pad0_of_lt s (by omega : 0 < 3)
      rw [hp, hs0v]
      omega
    · subst x
      have hp : pad0 s 1 = (s ⟨1, by omega⟩ : ℕ) := pad0_of_lt s (by omega : 1 < 3)
      rw [hp]
      dsimp [s]
      rfl
  rcases prop213_step1 F 3 s 1 (by omega : 1 ≤ 3) (by omega : 1 ≤ 1)
    (by omega : 1 ≤ 3 - 1) hsj hqend hsleq with ⟨hrel, hT2, hT3⟩
  have hdhead : ((D.cB i) ⟨0, D.hdepB i⟩ : ℕ) = 1 := by
    have hfib : D.cB i = consVec oneExp ((p2WpT F (qMinusExp F) ((r1Rel F).hdepB i.1)
        ((r1Rel F).cB i.1)).c i.2) := by
      change (RelData.BCq F (toData F (r1Rel F))).cB i =
        consVec oneExp ((p2WpT F (qMinusExp F) ((toData F (r1Rel F)).hdepB i.1)
          ((toData F (r1Rel F)).cB i.1)).c i.2)
      rfl
    rw [hfib]
    change (((consVec oneExp ((p2WpT F (qMinusExp F) ((r1Rel F).hdepB i.1) ((r1Rel F).cB i.1)).c i.2))
      ⟨0, (RelData.BCq F (toData F (r1Rel F))).hdepB i⟩) : ℕ) = 1
    rw [consVec_zero]
    rfl
  have he0 : pad0 (Q.c (Sum.inr (Sum.inr i))) 0 = (a : ℕ) + 1 := by
    change pad0 (headAdd a (D.hdepB i) (D.cB i)) 0 = (a : ℕ) + 1
    rw [pad0_headAdd_zero a (D.hdepB i) (D.cB i)]
    rw [hdhead]
  have hdeps : Q.dep (Sum.inr (Sum.inr i)) = D.depB i := by
    have h1 := FixedOver.prependList_dep F Bs (sPrefix 3 s 1 (by omega) (by omega))
      (Sum.inr (Sum.inr i))
    have h2 : Bs.dep (Sum.inr (Sum.inr i)) = D.depB i := by
      dsimp [Bs, D, ofBstarOver]
    have hlen : (sPrefix 3 s 1 (by omega) (by omega)).length = 0 := by
      rw [sPrefix_length]
    rw [h1, h2, hlen]
    omega
  have hwmem : weight (Q.dep (Sum.inr (Sum.inr i))) (Q.c (Sum.inr (Sum.inr i))) =
      weight 3 s := by
    exact (hT3 i).1
  constructor
  · intro x hx
    have hx01 : x = 0 ∨ x = 1 := by omega
    rcases hx01 with hx0 | hx1
    · subst x
      rw [he0]
      omega
    · subst x
      exact case2j1_type3_entry_le_q F a ha i
  · intro hf
    rcases hf with ⟨hr1, hdep2f, hall, hlast⟩
    have hdepge : 2 ≤ Q.dep (Sum.inr (Sum.inr i)) := by
      rw [hdeps]
      have hb := D.hB2 i
      omega
    have hdep2 : Q.dep (Sum.inr (Sum.inr i)) = 2 := by omega
    have hw3s : weight 3 s = (a : ℕ) + 2 * Nat.card F := by
      dsimp [s]
      rw [weight_consVec, weight_pair]
      have hq : (qExp F : ℕ) = Nat.card F := rfl
      rw [hq]
      omega
    have hw2form : weight (Q.dep (Sum.inr (Sum.inr i))) (Q.c (Sum.inr (Sum.inr i))) ≤
        2 * Nat.card F := by
      have hwsum : weight (Q.dep (Sum.inr (Sum.inr i))) (Q.c (Sum.inr (Sum.inr i))) =
          pad0 (Q.c (Sum.inr (Sum.inr i))) 0 + pad0 (Q.c (Sum.inr (Sum.inr i))) 1 := by
        have hps := psum_self (Q.c (Sum.inr (Sum.inr i)))
        calc
          weight (Q.dep (Sum.inr (Sum.inr i))) (Q.c (Sum.inr (Sum.inr i)))
              = psum (Q.c (Sum.inr (Sum.inr i))) (Q.dep (Sum.inr (Sum.inr i))) := hps.symm
          _ = psum (Q.c (Sum.inr (Sum.inr i))) 2 := by
                exact congrArg (psum (Q.c (Sum.inr (Sum.inr i)))) hdep2
          _ = pad0 (Q.c (Sum.inr (Sum.inr i))) 0 + pad0 (Q.c (Sum.inr (Sum.inr i))) 1 := by
                rw [psum_succ, psum_succ]
                rw [psum_zero]
                simp
      rw [hwsum]
      have h0le : pad0 (Q.c (Sum.inr (Sum.inr i))) 0 ≤ Nat.card F := by
        rw [he0]
        omega
      have h1eq : pad0 (Q.c (Sum.inr (Sum.inr i))) 1 = Nat.card F := by
        have h1 : 1 < Q.dep (Sum.inr (Sum.inr i)) := by omega
        rw [pad0_of_lt (Q.c (Sum.inr (Sum.inr i))) h1]
        have hlast' : ((Q.c (Sum.inr (Sum.inr i))) ⟨1, h1⟩ : ℕ) = Nat.card F := by
          have hidx : (⟨Q.dep (Sum.inr (Sum.inr i)) - 1, by omega⟩ :
              Fin (Q.dep (Sum.inr (Sum.inr i)))) = ⟨1, h1⟩ := by
            apply Fin.ext
            change Q.dep (Sum.inr (Sum.inr i)) - 1 = 1
            omega
          have hcong := congrArg (fun j : Fin (Q.dep (Sum.inr (Sum.inr i))) =>
            ((Q.c (Sum.inr (Sum.inr i))) j : ℕ)) hidx
          rw [← hcong]
          exact hlast
        exact hlast'
      omega
    have hwgt : (a : ℕ) + 2 * Nat.card F ≤
        weight (Q.dep (Sum.inr (Sum.inr i))) (Q.c (Sum.inr (Sum.inr i))) := by
      rw [← hw3s]
      rw [← hwmem]
    have hapos : 0 < (a : ℕ) := a.pos
    omega

end ZagierHoffmanPositiveChar
