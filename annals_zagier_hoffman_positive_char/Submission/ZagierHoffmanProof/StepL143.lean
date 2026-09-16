import Submission.ZagierHoffmanProof.StepL142
set_option autoImplicit false
set_option maxHeartbeats 8000000
open Polynomial RatFunc
open scoped BigOperators
/-!
# Step L143: the OUTSIDE-IN iterate `BCqIterO`, its descent-free b-side weight,
and the one-step `p2WpT` fiber facts (SESSION 259v)

The b-side of the G5 (j = 0) CASE-1 chain needs iterate-level facts about the
`b`-families of `BCqIter F (k−1) (toData R0)`.  `BCqIter` peels INSIDE-OUT
(`BCqIter (n+1) R = BCqIter n (BCq R)`, `rfl`), so for symbolic `n` its `ιB` is
`Nat.iterate`-headed and the `BCqIdx`-Σ is NOT syntactically available — the
`p.1` projection that the per-level recursion needs does not elaborate
(SESSION 259p).  FIX (SESSION 259v): introduce the OUTSIDE-IN iterate
  `BCqIterO (n+1) R := BCq (BCqIterO n R)`  (`rfl`),
whose `ιB` IS syntactically the `BCqIdx`-Σ at every successor level, prove
`BCqIterO n R = BCqIter n R` from `BCq_BCqIter_commute` (StepL142), and do all
b-side recursion on `BCqIterO`, transporting to the `BCqIter` statements through
the generic `cases h; rfl` transport lemmas below.

Deliverables:
  • `BCqIterO` + `BCqIterO_zero/succ` (rfl) + `BCqIterO_eq_BCqIter`;
  • transport lemmas `depB_eq_of_eq`, `cB_weight_eq_of_eq`, `cB_head_eq_of_eq`,
    `pad0_cB_eq_of_eq`, `kAdmissible_cB_iff_of_eq` (all `cases h; rfl`);
  • ★ `BCqIterO_cB_head` — every iterate `cB`-tuple has head 1 (given the base's);
  • ★ `BCqIterO_cB_weight` — the iterate weight with a UNIFORM base weight `W`:
      `weight = n * q + W`;  the per-step gain is exactly `q`
      (`weight_consVec` + the P2-data's `hle.1` + `weight_single`);
  • the one-step `p2WpT` fiber facts at general `B` with head 1:
      `p2WpT_front_le_one` (`pad0 (c e) 0 ≤ q`) and `p2WpT_dep_ge_two_of`
      (depth ≥ 2 from `q + 1 ≤ (q−1) + weight B`);
  • ★ `BCqIterO_b_fiber_succ` — both one-step facts for the top level of
      `BCqIterO (n+1) R`;
  • ★★ `BCqIterO_bSide_twoAdm_succ` — every top-level `cB`-tuple of
      `BCqIterO (n+1) R` is 2-admissible (`kAdm2_cons_one`).
theorem_B/D remain ABP-gated (no route).
-/

namespace ZagierHoffmanPositiveChar
attribute [local instance] Classical.propDecidable
variable (F : Type*) [Field F] [Finite F] [DecidableEq (RatFunc F)]

/-! ## The outside-in iterate -/

/-- The OUTSIDE-IN iterate of `BCq`: `BCqIterO (n+1) R = BCq (BCqIterO n R)` (`rfl`).
Its `ιB` is the syntactic `BCqIdx`-Σ at every successor level. -/
noncomputable def RelData.BCqIterO (n : ℕ) (R : RelData F) : RelData F :=
  Nat.rec R (fun _ R' => RelData.BCq F R') n

lemma RelData.BCqIterO_zero (R : RelData F) : RelData.BCqIterO F 0 R = R := rfl

lemma RelData.BCqIterO_succ (n : ℕ) (R : RelData F) :
    RelData.BCqIterO F (n + 1) R = RelData.BCq F (RelData.BCqIterO F n R) := rfl

/-- One step of the outside-in iterate exposes the `BCqIdx`-Σ pairing. -/
lemma RelData.BCqIterO_depB_succ (n : ℕ) (R : RelData F)
    (p : (RelData.BCqIterO F (n + 1) R).ιB) :
    (RelData.BCqIterO F (n + 1) R).depB p =
      (p2WpT F (qMinusExp F) ((RelData.BCqIterO F n R).hdepB p.1)
        ((RelData.BCqIterO F n R).cB p.1)).dep p.2 + 1 := rfl

/-- One step of the outside-in iterate, on the `cB`-tuples. -/
lemma RelData.BCqIterO_cB_succ (n : ℕ) (R : RelData F)
    (p : (RelData.BCqIterO F (n + 1) R).ιB) :
    (RelData.BCqIterO F (n + 1) R).cB p =
      consVec oneExp ((p2WpT F (qMinusExp F) ((RelData.BCqIterO F n R).hdepB p.1)
        ((RelData.BCqIterO F n R).cB p.1)).c p.2) := rfl

/-- The outside-in and inside-out iterates agree. -/
lemma RelData.BCqIterO_eq_BCqIter (n : ℕ) (R : RelData F) :
    RelData.BCqIterO F n R = RelData.BCqIter F n R := by
  induction n generalizing R with
  | zero => rfl
  | succ n ih =>
      rw [RelData.BCqIterO_succ, ih R, BCq_BCqIter_commute F n R, ← RelData.BCqIter_succ]

/-! ## Transport along an equality of `RelData`s -/

lemma RelData.depB_eq_of_eq {A B : RelData F} (h : A = B) (p : B.ιB) :
    A.depB (h.symm ▸ p) = B.depB p := by
  cases h; rfl

lemma RelData.cB_weight_eq_of_eq {A B : RelData F} (h : A = B) (p : B.ιB) :
    weight (A.depB (h.symm ▸ p)) (A.cB (h.symm ▸ p)) = weight (B.depB p) (B.cB p) := by
  cases h; rfl

lemma RelData.cB_head_eq_of_eq {A B : RelData F} (h : A = B) (p : B.ιB) :
    ((A.cB (h.symm ▸ p)) ⟨0, A.hdepB (h.symm ▸ p)⟩ : ℕ) =
      ((B.cB p) ⟨0, B.hdepB p⟩ : ℕ) := by
  cases h; rfl

lemma RelData.pad0_cB_eq_of_eq {A B : RelData F} (h : A = B) (p : B.ιB) (m : ℕ) :
    pad0 (A.cB (h.symm ▸ p)) m = pad0 (B.cB p) m := by
  cases h; rfl

lemma RelData.kAdmissible_cB_iff_of_eq {A B : RelData F} (h : A = B) (p : B.ιB)
    (q k : ℕ) :
    kAdmissible q (A.cB (h.symm ▸ p)) k ↔ kAdmissible q (B.cB p) k := by
  cases h; exact Iff.rfl

/-! ## Head and weight of the iterated `cB`-tuples -/

/-- Head-1 of `consVec oneExp X`. -/
lemma consVec_oneExp_head {m : ℕ} (X : Fin m → ℕ+) (hd : 0 < m + 1) :
    (((consVec oneExp X) ⟨0, hd⟩ : ℕ+) : ℕ) = 1 := by
  have h0 : (((consVec oneExp X) ⟨0, hd⟩ : ℕ+) : ℕ) = ((oneExp : ℕ+) : ℕ) :=
    congrArg (fun u : ℕ+ => (u : ℕ)) (consVec_zero oneExp X)
  rw [h0]
  rfl

/-- Every iterate `cB`-tuple has head 1, given the base's. -/
lemma RelData.BCqIterO_cB_head (n : ℕ) (R : RelData F)
    (hbhd : ∀ j : R.ιB, ((R.cB j) ⟨0, R.hdepB j⟩ : ℕ) = 1) :
    ∀ p : (RelData.BCqIterO F n R).ιB,
      (((RelData.BCqIterO F n R).cB p) ⟨0, (RelData.BCqIterO F n R).hdepB p⟩ : ℕ) = 1 := by
  induction n with
  | zero => intro p; exact hbhd p
  | succ n ih =>
      intro p
      exact consVec_oneExp_head
        ((p2WpT F (qMinusExp F) ((RelData.BCqIterO F n R).hdepB p.1)
          ((RelData.BCqIterO F n R).cB p.1)).c p.2)
        ((RelData.BCqIterO F (n + 1) R).hdepB p)

/-- ★ The iterate weight with a UNIFORM base weight `W`: each level adds exactly `q`. -/
lemma RelData.BCqIterO_cB_weight (n : ℕ) (R : RelData F) (W : ℕ)
    (hW : ∀ j : R.ιB, weight (R.depB j) (R.cB j) = W) :
    ∀ p : (RelData.BCqIterO F n R).ιB,
      weight ((RelData.BCqIterO F n R).depB p) ((RelData.BCqIterO F n R).cB p) =
        n * Nat.card F + W := by
  induction n with
  | zero => intro p
            have h0 : (0 : ℕ) * Nat.card F + W = W := by simp
            rw [h0]
            exact hW p
  | succ n ih =>
      intro p
      let fib := p2WpT F (qMinusExp F) ((RelData.BCqIterO F n R).hdepB p.1)
        ((RelData.BCqIterO F n R).cB p.1)
      have hstep : weight ((RelData.BCqIterO F (n + 1) R).depB p)
          ((RelData.BCqIterO F (n + 1) R).cB p) =
          weight (fib.dep p.2 + 1) (consVec oneExp (fib.c p.2)) := rfl
      rw [hstep, weight_consVec]
      have hle := (fib.hle p.2).1
      rw [hle, weight_single, ih p.1]
      have hq1 : 1 ≤ Nat.card F := by have h2 := card_ge_two F; omega
      have hqm : (qMinusExp F : ℕ) = Nat.card F - 1 := rfl
      have hone : (oneExp : ℕ) = 1 := rfl
      rw [hqm, hone, Nat.succ_mul]
      omega

/-! ## The one-step `p2WpT` fiber facts -/

/-- front bound of the `p2WpT`-outputs when the second tuple has head 1. -/
lemma p2WpT_front_le_one {k : ℕ} (hk : 0 < k) (B : Fin k → ℕ+)
    (hhead : ((B ⟨0, hk⟩ : ℕ+) : ℕ) = 1)
    (e : (p2WpT F (qMinusExp F) hk B).ι) :
    pad0 ((p2WpT F (qMinusExp F) hk B).c e) 0 ≤ Nat.card F := by
  have h := p2WpT_front_le F hk B e
  rw [hhead] at h
  have hqm : (qMinusExp F : ℕ) = Nat.card F - 1 := rfl
  rw [hqm] at h
  have hq1 : 1 ≤ Nat.card F := by have h2 := card_ge_two F; omega
  omega

/-- depth ≥ 2 of the `p2WpT`-outputs, from head 1 of the second tuple and the
weight bound `q + 1 ≤ (q−1) + weight B`. -/
lemma p2WpT_dep_ge_two_of {k : ℕ} (hk : 0 < k) (B : Fin k → ℕ+)
    (hhead : ((B ⟨0, hk⟩ : ℕ+) : ℕ) = 1)
    (hWbig : Nat.card F + 1 ≤ (qMinusExp F : ℕ) + weight k B)
    (e : (p2WpT F (qMinusExp F) hk B).ι) :
    2 ≤ (p2WpT F (qMinusExp F) hk B).dep e := by
  by_contra hcon
  have hpos : 0 < (p2WpT F (qMinusExp F) hk B).dep e :=
    (p2WpT F (qMinusExp F) hk B).hdep e
  have hd1 : (p2WpT F (qMinusExp F) hk B).dep e = 1 := by omega
  have hwle := ((p2WpT F (qMinusExp F) hk B).hle e).1
  have hwv : weight ((p2WpT F (qMinusExp F) hk B).dep e) ((p2WpT F (qMinusExp F) hk B).c e)
      = (qMinusExp F : ℕ) + weight k B := by
    rw [hwle, weight_single]
  have hfront := p2WpT_front_le F hk B e
  rw [hhead] at hfront
  have hone : weight ((p2WpT F (qMinusExp F) hk B).dep e) ((p2WpT F (qMinusExp F) hk B).c e)
      = pad0 ((p2WpT F (qMinusExp F) hk B).c e) 0 :=
    weight_dep_one_eq_pad0 _ hd1
  have hqm : (qMinusExp F : ℕ) = Nat.card F - 1 := rfl
  rw [hqm] at hwv hWbig hfront
  have hq1 : 1 ≤ Nat.card F := by have h2 := card_ge_two F; omega
  have hqsub : Nat.card F - 1 + 1 = Nat.card F := by omega
  rw [hqsub] at hfront
  omega

/-- ★ The two one-step facts for the top level of `BCqIterO (n+1) R`. -/
lemma RelData.BCqIterO_b_fiber_succ (n : ℕ) (R : RelData F) (W : ℕ)
    (hW : ∀ j : R.ιB, weight (R.depB j) (R.cB j) = W)
    (hbhd : ∀ j : R.ιB, ((R.cB j) ⟨0, R.hdepB j⟩ : ℕ) = 1) (hW2 : 2 ≤ W)
    (p : (RelData.BCqIterO F (n + 1) R).ιB) :
    (2 ≤ (p2WpT F (qMinusExp F) ((RelData.BCqIterO F n R).hdepB p.1)
        ((RelData.BCqIterO F n R).cB p.1)).dep p.2) ∧
    (pad0 ((p2WpT F (qMinusExp F) ((RelData.BCqIterO F n R).hdepB p.1)
        ((RelData.BCqIterO F n R).cB p.1)).c p.2) 0 ≤ Nat.card F) := by
  have hhead := RelData.BCqIterO_cB_head F n R hbhd p.1
  have hwprev := RelData.BCqIterO_cB_weight F n R W hW p.1
  have hq1 : 1 ≤ Nat.card F := by have h2 := card_ge_two F; omega
  have hqm : (qMinusExp F : ℕ) = Nat.card F - 1 := rfl
  have hWbig : Nat.card F + 1 ≤ (qMinusExp F : ℕ)
      + weight ((RelData.BCqIterO F n R).depB p.1) ((RelData.BCqIterO F n R).cB p.1) := by
    rw [hwprev, hqm]
    have hqsub : Nat.card F - 1 + (n * Nat.card F + W) + 1 = Nat.card F + (n * Nat.card F + W) := by
      omega
    omega
  exact ⟨p2WpT_dep_ge_two_of F _ _ hhead hWbig p.2,
    p2WpT_front_le_one F _ _ hhead p.2⟩

/-- ★★ Every top-level `cB`-tuple of `BCqIterO (n+1) R` is 2-admissible. -/
lemma RelData.BCqIterO_bSide_twoAdm_succ (n : ℕ) (R : RelData F) (W : ℕ)
    (hW : ∀ j : R.ιB, weight (R.depB j) (R.cB j) = W)
    (hbhd : ∀ j : R.ιB, ((R.cB j) ⟨0, R.hdepB j⟩ : ℕ) = 1) (hW2 : 2 ≤ W) :
    ∀ p : (RelData.BCqIterO F (n + 1) R).ιB,
      kAdmissible (Nat.card F) ((RelData.BCqIterO F (n + 1) R).cB p) 2 := by
  intro p
  have hfac := RelData.BCqIterO_b_fiber_succ F n R W hW hbhd hW2 p
  have hvec : (RelData.BCqIterO F (n + 1) R).cB p =
      consVec oneExp ((p2WpT F (qMinusExp F) ((RelData.BCqIterO F n R).hdepB p.1)
        ((RelData.BCqIterO F n R).cB p.1)).c p.2) :=
    RelData.BCqIterO_cB_succ F n R p
  rw [hvec]
  exact kAdm2_cons_one (Nat.card F) (card_ge_two F) hfac.1
    ((p2WpT F (qMinusExp F) ((RelData.BCqIterO F n R).hdepB p.1)
      ((RelData.BCqIterO F n R).cB p.1)).c p.2) hfac.2

end ZagierHoffmanPositiveChar
