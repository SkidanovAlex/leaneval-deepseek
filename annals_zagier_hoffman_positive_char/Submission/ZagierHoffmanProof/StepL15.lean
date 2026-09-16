import Submission.ZagierHoffmanProof.StepL14

set_option autoImplicit false
set_option maxHeartbeats 100000000
open Polynomial RatFunc
open scoped BigOperators

/-!
# Step L15: the prefixed-`ofBstar` level-sum with the type-1 term explicit

`ofBstar_decompose` splits the level value of the B*_v fixed relation (`FixedRel
.ofBstar`, paper (2.13)) into the `a`-side sum (over `D.ιA`) plus the `b`-side (over
`D.ιB ⊕ D.ιB`).  `ofBstar_a_sum` rewrites the `a`-side members by `ofBstar_a_term`
to `D`'s own fields (type-1 terms `(D.aA i)·S_d(v :: D.cA i)`).
★ `ofBstar_split_zero` is the (2.13) level identity with the type-1 sum explicit:
`Σ_i (D.aA i)·S_d(v :: D.cA i)` + `b`-side = `0` at every level.
-/

namespace ZagierHoffmanPositiveChar
attribute [instance] P2Data.fin
attribute [instance] RelData.finA
attribute [instance] RelData.finB
attribute [instance] FixedRel.fin
variable (F : Type*) [Field F] [Finite F] [DecidableEq (RatFunc F)]

/-- The `a`-side (type-1) sum of the B*_v output, expressed with `D`'s own fields
(the family-1 members are exactly `D.aA i` with tuples `v :: (D.cA i)`). -/
lemma ofBstar_a_sum (D : RelData F) (v : ℕ+)
    (hvalid : ∀ e : ℕ, RelData.level F D e = 0)
    (hv : ∀ p : D.ιB, (v : ℕ) + ((D.cB p) ⟨0, D.hdepB p⟩ : ℕ) ≤ Nat.card F) (d : ℕ) :
    (∑ i : D.ιA, (((FixedRel.ofBstar F D v hvalid hv).a (Sum.inl i) : RatFunc F) :
        RatFunc.CompletionAtInfty F) *
        S F ((FixedRel.ofBstar F D v hvalid hv).dep (Sum.inl i))
          ((FixedRel.ofBstar F D v hvalid hv).hdep (Sum.inl i))
          ((FixedRel.ofBstar F D v hvalid hv).c (Sum.inl i)) d) =
    (∑ i : D.ιA, (((D.aA i : RatFunc F) : RatFunc.CompletionAtInfty F) *
        S F (D.depA i + 1) (by omega : 0 < D.depA i + 1) (consVec v (D.cA i)) d)) := by
  classical
  apply Finset.sum_congr rfl
  intro i hi
  exact FixedRel.ofBstar_a_term F D v hvalid hv i d

/-- The level value of the B*_v output decomposes into the `a`-side (type-1, over
`D.ιA`) plus the `b`-side (over `D.ιB ⊕ D.ιB`). -/
lemma ofBstar_decompose (D : RelData F) (v : ℕ+)
    (hvalid : ∀ e : ℕ, RelData.level F D e = 0)
    (hv : ∀ p : D.ιB, (v : ℕ) + ((D.cB p) ⟨0, D.hdepB p⟩ : ℕ) ≤ Nat.card F) (d : ℕ) :
    FixedRel.level F (FixedRel.ofBstar F D v hvalid hv) d =
      (∑ i : D.ιA, (((FixedRel.ofBstar F D v hvalid hv).a (Sum.inl i) : RatFunc F) :
          RatFunc.CompletionAtInfty F) *
          S F ((FixedRel.ofBstar F D v hvalid hv).dep (Sum.inl i))
            ((FixedRel.ofBstar F D v hvalid hv).hdep (Sum.inl i))
            ((FixedRel.ofBstar F D v hvalid hv).c (Sum.inl i)) d) +
      (∑ q : (D.ιB ⊕ D.ιB), (((FixedRel.ofBstar F D v hvalid hv).a (Sum.inr q) : RatFunc F) :
          RatFunc.CompletionAtInfty F) *
          S F ((FixedRel.ofBstar F D v hvalid hv).dep (Sum.inr q))
            ((FixedRel.ofBstar F D v hvalid hv).hdep (Sum.inr q))
            ((FixedRel.ofBstar F D v hvalid hv).c (Sum.inr q)) d) := by
  classical
  dsimp [FixedRel.level]
  change (∑ p : D.ιA ⊕ (D.ιB ⊕ D.ιB),
      (((FixedRel.ofBstar F D v hvalid hv).a p : RatFunc F) : RatFunc.CompletionAtInfty F) *
        S F ((FixedRel.ofBstar F D v hvalid hv).dep p) ((FixedRel.ofBstar F D v hvalid hv).hdep p)
          ((FixedRel.ofBstar F D v hvalid hv).c p) d) =
      (∑ i : D.ιA, (((FixedRel.ofBstar F D v hvalid hv).a (Sum.inl i) : RatFunc F) :
          RatFunc.CompletionAtInfty F) *
          S F ((FixedRel.ofBstar F D v hvalid hv).dep (Sum.inl i))
            ((FixedRel.ofBstar F D v hvalid hv).hdep (Sum.inl i))
            ((FixedRel.ofBstar F D v hvalid hv).c (Sum.inl i)) d) +
      (∑ q : (D.ιB ⊕ D.ιB), (((FixedRel.ofBstar F D v hvalid hv).a (Sum.inr q) : RatFunc F) :
          RatFunc.CompletionAtInfty F) *
          S F ((FixedRel.ofBstar F D v hvalid hv).dep (Sum.inr q))
            ((FixedRel.ofBstar F D v hvalid hv).hdep (Sum.inr q))
            ((FixedRel.ofBstar F D v hvalid hv).c (Sum.inr q)) d)
  rw [Fintype.sum_sum_type]

/-- ★ The (2.13) level identity with the type-1 sum explicit: the `a`-side
`Σ_i (D.aA i)·S_d(v :: D.cA i)` plus the `b`-side sums to `0`. -/
theorem ofBstar_split_zero (D : RelData F) (v : ℕ+)
    (hvalid : ∀ e : ℕ, RelData.level F D e = 0)
    (hv : ∀ p : D.ιB, (v : ℕ) + ((D.cB p) ⟨0, D.hdepB p⟩ : ℕ) ≤ Nat.card F) (d : ℕ) :
    (∑ i : D.ιA, (((D.aA i : RatFunc F) : RatFunc.CompletionAtInfty F) *
        S F (D.depA i + 1) (by omega : 0 < D.depA i + 1) (consVec v (D.cA i)) d)) +
    (∑ q : (D.ιB ⊕ D.ιB), (((FixedRel.ofBstar F D v hvalid hv).a (Sum.inr q) : RatFunc F) :
        RatFunc.CompletionAtInfty F) *
        S F ((FixedRel.ofBstar F D v hvalid hv).dep (Sum.inr q))
          ((FixedRel.ofBstar F D v hvalid hv).hdep (Sum.inr q))
          ((FixedRel.ofBstar F D v hvalid hv).c (Sum.inr q)) d) = 0 := by
  classical
  have h0 : FixedRel.level F (FixedRel.ofBstar F D v hvalid hv) d = 0 :=
    FixedRel.ofBstar_valid F D v hvalid hv d
  have hdec := ofBstar_decompose F D v hvalid hv d
  have hsum := ofBstar_a_sum F D v hvalid hv d
  calc
    (∑ i : D.ιA, (((D.aA i : RatFunc F) : RatFunc.CompletionAtInfty F) *
          S F (D.depA i + 1) (by omega : 0 < D.depA i + 1) (consVec v (D.cA i)) d)) +
        (∑ q : (D.ιB ⊕ D.ιB), (((FixedRel.ofBstar F D v hvalid hv).a (Sum.inr q) : RatFunc F) :
            RatFunc.CompletionAtInfty F) *
            S F ((FixedRel.ofBstar F D v hvalid hv).dep (Sum.inr q))
              ((FixedRel.ofBstar F D v hvalid hv).hdep (Sum.inr q))
              ((FixedRel.ofBstar F D v hvalid hv).c (Sum.inr q)) d)
        = (∑ i : D.ιA, (((FixedRel.ofBstar F D v hvalid hv).a (Sum.inl i) : RatFunc F) :
              RatFunc.CompletionAtInfty F) *
              S F ((FixedRel.ofBstar F D v hvalid hv).dep (Sum.inl i))
                ((FixedRel.ofBstar F D v hvalid hv).hdep (Sum.inl i))
                ((FixedRel.ofBstar F D v hvalid hv).c (Sum.inl i)) d) +
            (∑ q : (D.ιB ⊕ D.ιB), (((FixedRel.ofBstar F D v hvalid hv).a (Sum.inr q) : RatFunc F) :
                RatFunc.CompletionAtInfty F) *
                S F ((FixedRel.ofBstar F D v hvalid hv).dep (Sum.inr q))
                  ((FixedRel.ofBstar F D v hvalid hv).hdep (Sum.inr q))
                  ((FixedRel.ofBstar F D v hvalid hv).c (Sum.inr q)) d) := by
          rw [← hsum]
    _ = FixedRel.level F (FixedRel.ofBstar F D v hvalid hv) d := by
          rw [← hdec]
    _ = 0 := h0

end ZagierHoffmanPositiveChar
