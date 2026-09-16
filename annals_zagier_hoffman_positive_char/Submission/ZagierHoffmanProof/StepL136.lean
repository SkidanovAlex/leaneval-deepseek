import Submission.ZagierHoffmanProof.StepL135
set_option autoImplicit false
set_option maxHeartbeats 4000000
open Polynomial RatFunc
open scoped BigOperators
/-!
# Step L136: the count-(k−1) u-values lemma for the G5 chain (SESSION 259e)

`maink_g5_u_cA_values_front`: the iterated leading member's q-branch entries
(m < k−1) equal s's — the `m < k−1` half of the count-(k−1) analogue of
`g5c1_u_cA_values` (StepL77), from `BCqIter_cA_value`'s if-branch plus the
all-q-front hypothesis `hallq`.
theorem_B/D remain ABP-gated (no route).
-/

namespace ZagierHoffmanPositiveChar
attribute [local instance] Classical.propDecidable
variable (F : Type*) [Field F] [Finite F] [DecidableEq (RatFunc F)]

/-- ★ The q-branch of the G5 u-values: for `m < k−1` the iterated leading
member's entry is `s⟨m⟩`. -/
lemma maink_g5_u_cA_values_front (r : ℕ) (s : Fin r → ℕ+) (k : ℕ) (hkr : k ≤ r)
    (hallq : ∀ x : ℕ, x < k - 1 → pad0 s x = Nat.card F)
    (R0 : BinaryRel F) (u : R0.ιA) :
    ∀ (m : ℕ) (hmQ : m < (RelData.BCqIter F (k - 1) (toData F R0)).depA
        (RelData.iterIdx F (k - 1) (toData F R0) u)) (hmr : m < r),
      m < k - 1 →
      (RelData.BCqIter F (k - 1) (toData F R0)).cA
        (RelData.iterIdx F (k - 1) (toData F R0) u) ⟨m, hmQ⟩ = s ⟨m, hmr⟩ := by
  intro m hmQ hmr hm
  have hdep_eq : (RelData.BCqIter F (k - 1) (toData F R0)).depA
      (RelData.iterIdx F (k - 1) (toData F R0) u) = (toData F R0).depA u + (k - 1) :=
    RelData.BCqIter_depA_at F (k - 1) (toData F R0) u
  have hbase : m < (toData F R0).depA u + (k - 1) := by rw [← hdep_eq]; exact hmQ
  have hcv := RelData.BCqIter_cA_value F (k - 1) (toData F R0) u ⟨m, hbase⟩
  have hcast : (Fin.cast (RelData.BCqIter_depA_at F (k - 1) (toData F R0) u).symm
        ⟨m, hbase⟩) = (⟨m, hmQ⟩ : Fin ((RelData.BCqIter F (k - 1) (toData F R0)).depA
          (RelData.iterIdx F (k - 1) (toData F R0) u))) := by
    apply Fin.ext
    simp
  rw [← hcast, hcv]
  simp only [hm, dif_pos]
  apply Subtype.ext
  change (qExp F : ℕ) = (s ⟨m, hmr⟩ : ℕ)
  rw [show (qExp F : ℕ) = Nat.card F from rfl, ← pad0_of_lt s hmr]
  exact (hallq m hm).symm

-- TAIL BRANCH (m ≥ k−1) — recipe, two fixes identified before the budget ran out:
--   • reduce the `if` with `rw [dif_neg (show ¬ (m < k - 1) by omega)]` (not
--     `simp only [hm, dif_neg]` — `hm : k−1 ≤ m` is not syntactically `¬ m < k−1`);
--   • the index bridge is `rw [hcast2, hb]` (NOT `← hcast2`): the goal carries the
--     plain index `⟨m−(k−1), _⟩` and `hcast2 : ⟨j, hjbase⟩ = Fin.cast hdepu.symm
--     ⟨j, hjlt⟩` must rewrite it INTO the cast form that `hb := congrFun (hc0 hdepu)
--     ⟨j, hjlt⟩` matches; `(toData F R0).cA u` vs `R0.cA u` are only
--     definitionally equal, so insert a `change`/`show` if the rw misses;
--   • then `bstarBase_head` (j = 0 ⇒ m = k−1) / `bstarBase_tail` (j = t+1) and the
--     `Fin.ext`-`omega` close on `k + t = m` and on the s-index.


end ZagierHoffmanPositiveChar
