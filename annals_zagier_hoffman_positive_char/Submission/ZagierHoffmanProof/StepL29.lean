import Submission.ZagierHoffmanProof.StepL28

set_option autoImplicit false
set_option maxHeartbeats 100000000
open Polynomial RatFunc
open scoped BigOperators

/-!
# Step L29: BC_q b-fiber prefix bounds (tail-bound piece of the type-2 full-prefix)

The type-2 members of the (2.14) chain continue past the `s_1…s_j, 1`-prefix with the
fiber data of the `BC_q`-iterate `D = BCqIter (k−j−1) (toData R0)`.  Each `BC_q` step
replaces a b-tuple `cB j` (head `1`) by `(1, τ)` where `τ` is a p2WpT-fiber with the
P2Data `hle` bound `LePad τ (single(q−1)) (cB j)` — `p2_fiber_prefix` records its
prefix-sum content (`psum τ m ≤ psum (single(q−1)) m + psum (cB j) m`).  Iterating this
recursion `n` times bounds the type-2 tail entries against the paper's
`(q{n}, s_k−1, s_{k+1}, …)`-reference; the iterate-level recursion (one step: new
fiber prefix at `n+1` ≤ `q` + old fiber prefix at `n`, using head-1 via
`RelData.BCqIter_head_one` and the `psum (cB) (m+1) = head + psum (expTail) m` split)
is designed but the nested-Σ index bookkeeping of `Nat.iterate`-prepending
(`BCqIter (n+1) D = BCqIter n (BCq D)` — `BCqIter_succ`) makes the "parent of `i` at
level `n`" live over `BCq^{·}`-accumulated relations; see PLAN SESSION 169 for the
precise recursion design.  `p2_fiber_prefix` is the committed local piece.
-/

namespace ZagierHoffmanPositiveChar
attribute [instance] P2Data.fin
attribute [instance] RelData.finA
attribute [instance] RelData.finB
attribute [instance] FixedRel.fin
variable (F : Type*) [Field F] [Finite F] [DecidableEq (RatFunc F)]

/-- The p2WpT-fiber of one `BC_q` b-step has prefix sums bounded by those of
`(q−1)` plus the old b-tuple (from the P2Data `hle` bound). -/
lemma p2_fiber_prefix (R : BinaryRel F) (j : R.ιB)
    (e : (p2WpT F (qMinusExp F) (R.hdepB j) (R.cB j)).ι) (m : ℕ) :
    psum ((p2WpT F (qMinusExp F) (R.hdepB j) (R.cB j)).c e) m ≤
      psum (single (qMinusExp F)) m + psum (R.cB j) m := by
  classical
  have hle := (p2WpT F (qMinusExp F) (R.hdepB j) (R.cB j)).hle e
  have hp := hle.2 m
  calc
    psum ((p2WpT F (qMinusExp F) (R.hdepB j) (R.cB j)).c e) m
        ≤ psumSeq (tupPadSum (single (qMinusExp F)) (R.cB j)) m := hp
    _ = psum (single (qMinusExp F)) m + psum (R.cB j) m := by
          unfold psumSeq tupPadSum psum
          rw [Finset.sum_add_distrib]

lemma psum_head_expTail {d : ℕ} (hr0 : 0 < d) (t : Fin d → ℕ+) (n : ℕ) :
    psum t (n + 1) = (t ⟨0, hr0⟩ : ℕ) + psum (expTail t) n := by
  classical
  have hz : pad0 t 0 = (t ⟨0, hr0⟩ : ℕ) := by
    rw [pad0_of_lt t hr0]
  induction n with
  | zero =>
      calc
        psum t (0 + 1) = pad0 t 0 := by
          rw [psum_succ]
          simp [psum_zero]
        _ = (t ⟨0, hr0⟩ : ℕ) := hz
        _ = (t ⟨0, hr0⟩ : ℕ) + 0 := by omega
        _ = (t ⟨0, hr0⟩ : ℕ) + psum (expTail t) 0 := by simp [psum_zero]
  | succ n ih =>
      calc
        psum t ((n + 1) + 1) = psum t (n + 1) + pad0 t (n + 1) := by
          rw [psum_succ]
        _ = ((t ⟨0, hr0⟩ : ℕ) + psum (expTail t) n) + pad0 t (n + 1) := by rw [ih]
        _ = (t ⟨0, hr0⟩ : ℕ) + (psum (expTail t) n + pad0 (expTail t) n) := by
              have hp : pad0 t (n + 1) = pad0 (expTail t) n := by
                classical
                by_cases hnl : n < d - 1
                · have hn1 : n + 1 < d := by omega
                  rw [pad0_of_lt t hn1, pad0_of_lt (expTail t) hnl]
                  rfl
                · have hn1 : ¬ n + 1 < d := by omega
                  have hg1 : d ≤ n + 1 := le_of_not_gt hn1
                  have hg2 : d - 1 ≤ n := by omega
                  rw [pad0_of_ge t hg1, pad0_of_ge (expTail t) hg2]
              rw [hp]
              omega
        _ = (t ⟨0, hr0⟩ : ℕ) + psum (expTail t) (n + 1) := by
              rw [psum_succ]
lemma BCq_one_step_prefix (R : BinaryRel F) (j : R.ιB)
    (e : (p2WpT F (qMinusExp F) (R.hdepB j) (R.cB j)).ι) (ℓ : ℕ)
    (hhead : ((R.cB j) ⟨0, R.hdepB j⟩ : ℕ) = 1) :
    psum (expTail ((RelData.BCq F (toData F R)).cB ⟨j, e⟩)) (ℓ + 1) ≤
      (Nat.card F : ℕ) + psum (expTail (R.cB j)) ℓ := by
  classical
  have hcB : (RelData.BCq F (toData F R)).cB ⟨j, e⟩ =
      consVec oneExp ((p2WpT F (qMinusExp F) (R.hdepB j) (R.cB j)).c e) := by
    dsimp [RelData.BCq, toData]
  have htail : expTail ((RelData.BCq F (toData F R)).cB ⟨j, e⟩) =
      (p2WpT F (qMinusExp F) (R.hdepB j) (R.cB j)).c e := by
    rw [hcB]
    rfl
  have hfib := p2_fiber_prefix F R j e (ℓ + 1)
  have hsplit : psum (R.cB j) (ℓ + 1) = 1 + psum (expTail (R.cB j)) ℓ := by
    have hp := psum_head_expTail (R.hdepB j) (R.cB j) ℓ
    -- hp : psum (R.cB j) (ℓ+1) = ((R.cB j)⟨0, by omega⟩ : ℕ) + psum (expTail (R.cB j)) ℓ
    -- the head value is 1:
    have hh1 : ((R.cB j) ⟨0, R.hdepB j⟩ : ℕ) = 1 := by
      simpa using hhead
    rw [hp, hh1]
  have hsingle : psum (single (qMinusExp F)) (ℓ + 1) = (Nat.card F - 1 : ℕ) := by
    have hpos : 0 < ℓ + 1 := by omega
    have hp := psum_single_of_pos (qMinusExp F) hpos
    simpa [qMinusExp] using hp
  have hq : 1 ≤ Nat.card F := by
    have h2 : 2 ≤ Nat.card F := card_ge_two F
    omega
  calc
    psum (expTail ((RelData.BCq F (toData F R)).cB ⟨j, e⟩)) (ℓ + 1)
        = psum ((p2WpT F (qMinusExp F) (R.hdepB j) (R.cB j)).c e) (ℓ + 1) := by
          exact congrArg (fun u => psum u (ℓ + 1)) htail
    _ ≤ psum (single (qMinusExp F)) (ℓ + 1) + psum (R.cB j) (ℓ + 1) := hfib
    _ = (Nat.card F - 1 : ℕ) + (1 + psum (expTail (R.cB j)) ℓ) := by rw [hsingle, hsplit]
    _ ≤ (Nat.card F : ℕ) + psum (expTail (R.cB j)) ℓ := by
          omega

lemma BCqIter_append (n : ℕ) (D : RelData F) :
    RelData.BCqIter F (n + 1) D = RelData.BCq F (RelData.BCqIter F n D) := by
  dsimp [RelData.BCqIter]
  have h := congrFun (Function.iterate_succ' (RelData.BCq F) n) D
  simpa using h

/-- RelData version of the p2WpT-fiber prefix bound. -/
lemma p2_fiber_prefix' (D : RelData F) (j : D.ιB)
    (e : (p2WpT F (qMinusExp F) (D.hdepB j) (D.cB j)).ι) (m : ℕ) :
    psum ((p2WpT F (qMinusExp F) (D.hdepB j) (D.cB j)).c e) m ≤
      psum (single (qMinusExp F)) m + psum (D.cB j) m := by
  classical
  have hle := (p2WpT F (qMinusExp F) (D.hdepB j) (D.cB j)).hle e
  have hp := hle.2 m
  calc
    psum ((p2WpT F (qMinusExp F) (D.hdepB j) (D.cB j)).c e) m
        ≤ psumSeq (tupPadSum (single (qMinusExp F)) (D.cB j)) m := hp
    _ = psum (single (qMinusExp F)) m + psum (D.cB j) m := by
          unfold psumSeq tupPadSum psum
          rw [Finset.sum_add_distrib]

/-- RelData version of the one `BC_q` step prefix increment. -/
lemma BCq_one_step_prefix' (D : RelData F) (j : D.ιB)
    (e : (p2WpT F (qMinusExp F) (D.hdepB j) (D.cB j)).ι) (ℓ : ℕ)
    (hhead : ((D.cB j) ⟨0, D.hdepB j⟩ : ℕ) = 1) :
    psum (expTail ((RelData.BCq F D).cB ⟨j, e⟩)) (ℓ + 1) ≤
      (Nat.card F : ℕ) + psum (expTail (D.cB j)) ℓ := by
  classical
  have hcB : (RelData.BCq F D).cB ⟨j, e⟩ =
      consVec oneExp ((p2WpT F (qMinusExp F) (D.hdepB j) (D.cB j)).c e) := by
    dsimp [RelData.BCq]
  have htail : expTail ((RelData.BCq F D).cB ⟨j, e⟩) =
      (p2WpT F (qMinusExp F) (D.hdepB j) (D.cB j)).c e := by
    rw [hcB]
    rfl
  have hfib := p2_fiber_prefix' F D j e (ℓ + 1)
  have hsplit : psum (D.cB j) (ℓ + 1) = 1 + psum (expTail (D.cB j)) ℓ := by
    have hp := psum_head_expTail (D.hdepB j) (D.cB j) ℓ
    have hh1 : ((D.cB j) ⟨0, D.hdepB j⟩ : ℕ) = 1 := hhead
    rw [hp, hh1]
  have hsingle : psum (single (qMinusExp F)) (ℓ + 1) = (Nat.card F - 1 : ℕ) := by
    have hpos : 0 < ℓ + 1 := by omega
    have hp := psum_single_of_pos (qMinusExp F) hpos
    simpa [qMinusExp] using hp
  have hq : 1 ≤ Nat.card F := by
    have h2 : 2 ≤ Nat.card F := card_ge_two F
    omega
  calc
    psum (expTail ((RelData.BCq F D).cB ⟨j, e⟩)) (ℓ + 1)
        = psum ((p2WpT F (qMinusExp F) (D.hdepB j) (D.cB j)).c e) (ℓ + 1) := by
          exact congrArg (fun u => psum u (ℓ + 1)) htail
    _ ≤ psum (single (qMinusExp F)) (ℓ + 1) + psum (D.cB j) (ℓ + 1) := hfib
    _ = (Nat.card F - 1 : ℕ) + (1 + psum (expTail (D.cB j)) ℓ) := by rw [hsingle, hsplit]
    _ ≤ (Nat.card F : ℕ) + psum (expTail (D.cB j)) ℓ := by omega

/-- One iterate level: the level-`n+1` b-fiber prefix at `n+1` is bounded by `q`
plus the level-`n` fiber prefix at `n` (given the level-`n` heads are `1`). -/
lemma BCq_iterate_level_succ (n : ℕ) (D : RelData F)
    (hbhd : ∀ j : (RelData.BCqIter F n D).ιB,
      (((RelData.BCqIter F n D).cB j) ⟨0, (RelData.BCqIter F n D).hdepB j⟩ : ℕ) = 1) :
    ∀ j : (RelData.BCqIter F n D).ιB,
      ∀ e : (p2WpT F (qMinusExp F) ((RelData.BCqIter F n D).hdepB j)
              ((RelData.BCqIter F n D).cB j)).ι,
        psum (expTail ((RelData.BCq F (RelData.BCqIter F n D)).cB ⟨j, e⟩)) (n + 1) ≤
          (Nat.card F : ℕ) + psum (expTail ((RelData.BCqIter F n D).cB j)) n := by
  classical
  intro j e
  exact BCq_one_step_prefix' F (RelData.BCqIter F n D) j e n (hbhd j)

/-- Head-1 of the `BC_q`-iterate b-tuples of a base with `1`-headed b-tuples. -/
lemma BCqIter_head_one_data (n : ℕ) (R0 : BinaryRel F)
    (hbhd : ∀ j : R0.ιB, ((R0.cB j) ⟨0, R0.hdepB j⟩ : ℕ) = 1) :
    ∀ j' : (RelData.BCqIter F n (toData F R0)).ιB,
      (((RelData.BCqIter F n (toData F R0)).cB j')
        ⟨0, (RelData.BCqIter F n (toData F R0)).hdepB j'⟩ : ℕ) = 1 := by
  classical
  intro j'
  have hh := RelData.BCqIter_head_one F n R0 hbhd j'
  have hh' := congrArg (fun t : ℕ+ => (t : ℕ)) hh
  simpa [oneExp] using hh'


/-- ★ The `BC_q`-iterate fiber prefix bound: a level-`n` b-fiber tail has prefix
sum at `n` at most `n·q`.  (Level `n` = `BCqIter n (toData R0)`; tails are bounded
entry-by-entry by the `q`-blocks of the `BC_q` iteration.) -/
lemma BCq_fiber_prefix_qN (n : ℕ) (R0 : BinaryRel F)
    (hbhd : ∀ j : R0.ιB, ((R0.cB j) ⟨0, R0.hdepB j⟩ : ℕ) = 1) :
    ∀ i : (RelData.BCqIter F n (toData F R0)).ιB,
      psum (expTail ((RelData.BCqIter F n (toData F R0)).cB i)) n ≤ n * Nat.card F := by
  classical
  induction n with
  | zero =>
      intro i
      simp [psum_zero]
  | succ n ih =>
      rw [BCqIter_append]
      intro i
      change RelData.BCqIdx F (RelData.BCqIter F n (toData F R0)) at i
      rcases i with ⟨j, e⟩
      have hstep := BCq_iterate_level_succ F n (toData F R0) (BCqIter_head_one_data F n R0 hbhd) j e
      have hih := ih j
      calc
        psum (expTail ((RelData.BCq F (RelData.BCqIter F n (toData F R0))).cB ⟨j, e⟩)) (n + 1)
            ≤ (Nat.card F) + psum (expTail ((RelData.BCqIter F n (toData F R0)).cB j)) n := hstep
        _ ≤ (Nat.card F) + n * Nat.card F := by
              exact add_le_add_right hih (Nat.card F)
        _ = (n + 1) * Nat.card F := by ring


/-- ★ The full fiber-prefix bound through the `BC_q` iterate: a level-`n` fiber tail
has prefix sum at `m` at most `n·q` plus the level-0 tail bound `X` at `m − n`.  (The
`ℓ > k` type-2 prefix estimates use this with `X` the level-0 `LePad` reference.) -/
lemma BCq_fiber_prefix_X (n : ℕ) (R0 : BinaryRel F)
    (hbhd : ∀ j : R0.ιB, ((R0.cB j) ⟨0, R0.hdepB j⟩ : ℕ) = 1)
    (X : ℕ → ℕ)
    (hX0 : ∀ j : R0.ιB, ∀ m : ℕ, psum (expTail (R0.cB j)) m ≤ X m) :
    ∀ i : (RelData.BCqIter F n (toData F R0)).ιB,
      ∀ m : ℕ, psum (expTail ((RelData.BCqIter F n (toData F R0)).cB i)) m ≤ n * Nat.card F + X (m - n) := by
  classical
  induction n with
  | zero =>
      intro i m
      change psum (expTail (R0.cB i)) m ≤ 0 * Nat.card F + X (m - 0)
      simpa using hX0 i m
  | succ n ih =>
      rw [BCqIter_append]
      intro i m
      change RelData.BCqIdx F (RelData.BCqIter F n (toData F R0)) at i
      rcases i with ⟨j, e⟩
      by_cases hm : 0 < m
      · have hhead := BCqIter_head_one_data F n R0 hbhd j
        have hstep := BCq_one_step_prefix' F (RelData.BCqIter F n (toData F R0)) j e (m - 1) hhead
        have hstep' : psum (expTail ((RelData.BCq F (RelData.BCqIter F n (toData F R0))).cB ⟨j, e⟩)) m ≤
            (Nat.card F : ℕ) + psum (expTail ((RelData.BCqIter F n (toData F R0)).cB j)) (m - 1) := by
          have hm1 : (m - 1) + 1 = m := by omega
          simpa [hm1] using hstep
        have hih := ih j (m - 1)
        calc
          psum (expTail ((RelData.BCq F (RelData.BCqIter F n (toData F R0))).cB ⟨j, e⟩)) m
              ≤ (Nat.card F : ℕ) + psum (expTail ((RelData.BCqIter F n (toData F R0)).cB j)) (m - 1) := hstep'
          _ ≤ (Nat.card F : ℕ) + (n * Nat.card F + X ((m - 1) - n)) := by
                exact add_le_add_right hih (Nat.card F)
          _ = (n + 1) * Nat.card F + X (m - (n + 1)) := by
                have hsub : (m - 1) - n = m - (n + 1) := by omega
                rw [hsub]
                ring
      · have hm0 : m = 0 := by omega
        subst m
        simp [psum_zero]

end ZagierHoffmanPositiveChar
