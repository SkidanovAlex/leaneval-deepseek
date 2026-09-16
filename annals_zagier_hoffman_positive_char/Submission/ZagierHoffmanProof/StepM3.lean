import Submission.ZagierHoffmanProof.StepM1

set_option autoImplicit false
set_option maxHeartbeats 100000000
open Polynomial RatFunc
open scoped BigOperators

/-!
# Step M3: the Step-1 input and Init-bound lemmas for Prop 3.2 (k-admissibility)

Two pure-tuple facts the H_k algorithm needs, on top of StepM1's `kAdmissible`/
`initLen` notions:
  ★ `depth_ge_of_not_adm` — the paper's "depth(fs) ≥ k": a `(k−1)`-admissible tuple
    that is NOT `k`-admissible has depth ≥ k (else `(k−1)`-admissibility would force
    `k`-admissibility).  This is what guarantees the Step-1 CASE-1/CASE-2 split
    (`s_k` exists) can run on the algorithm's inputs.
  ★ `initLen_le_of_not_adm` — the "Init bounded by q{k}" termination ingredient: a
    NOT-`k`-admissible tuple has initial tuple of length ≤ k (whether because some of
    the first `k` entries exceeds `q` — `initLen_le_of_gt` — or because it is of the
    forbidden form: all entries ≤ q of depth ≤ k, so `Init` is the whole tuple).
NOTE (G3 analysis): the type-3 member depth ≥ k claim is NOT provable (BC_q-iterate
`b`-depths are only bounded below by 2 — `p2WpT` is a `Classical.choice` with only
`hdep`/`hbd` upper depth data), and is NOT needed: type-1/type-2 members leave the
chain via `prefix-k < S`, and the termination argument needs only Init boundedness
(`initLen_le_of_not_adm`) plus Init strict growth (`type3_Init_gt`, StepL33).  See
PLAN.md SESSION 183c for the full analysis.
-/

namespace ZagierHoffmanPositiveChar

/-- ★ (L1) The paper's "depth(fs) ≥ k" for the Step-1 input: a tuple that is
`(k−1)`-admissible but NOT `k`-admissible must have depth at least `k` (if
`depth < k` then `(k−1)`-admissibility already forces `k`-admissibility). -/
lemma depth_ge_of_not_adm (q : ℕ) {r k : ℕ} (s : Fin r → ℕ+) (hk : 1 ≤ k)
    (hadm : kAdmissible q s (k - 1)) (hnot : ¬ kAdmissible q s k) : k ≤ r := by
  by_contra h
  have hrk : r < k := lt_of_not_ge h
  apply hnot
  constructor
  · intro x hx
    by_cases hxr : x < r
    · have hxkm : x < k - 1 := by omega
      exact hadm.1 x hxkm
    · have hge : r ≤ x := le_of_not_gt hxr
      rw [pad0_of_ge s hge]
      exact Nat.zero_le q
  · intro hc2
    rcases hc2 with ⟨hr1, hrk', hall, hlast⟩
    apply hadm.2
    refine ⟨hr1, ?_, hall, hlast⟩
    omega

/-- ★ (L2) The `Init` boundedness the termination argument needs: a tuple that is NOT
`k`-admissible has initial tuple of length ≤ `k` (whether via a `> q` entry among the
first `k` positions, or via the forbidden form of depth ≤ k with last = q). -/
lemma initLen_le_of_not_adm (q : ℕ) {r k : ℕ} (s : Fin r → ℕ+) (hnot : ¬ kAdmissible q s k) :
    initLen q s ≤ k := by
  classical
  unfold kAdmissible at hnot
  by_cases hc1 : ∀ x : ℕ, x < k → pad0 s x ≤ q
  · have hc2 : ∃ hr1 : 1 ≤ r,
        r ≤ k ∧ (∀ x : ℕ, x < r - 1 → pad0 s x ≤ q) ∧ (s ⟨r - 1, by omega⟩ : ℕ) = q := by
      by_contra hc2'
      apply hnot
      exact ⟨hc1, hc2'⟩
    rcases hc2 with ⟨hr1, hrk, hall, hlast⟩
    have hall' : ∀ x : ℕ, (hx : x < r) → (s ⟨x, hx⟩ : ℕ) ≤ q := by
      intro x hx
      by_cases hxr : x = r - 1
      · subst x
        rw [hlast]
      · have hx1 : x < r - 1 := by omega
        have hle := hall x hx1
        rwa [pad0_of_lt s hx] at hle
    have hinit : initList q s = valueList s := initList_eq_valueList q s hall'
    have hlen : (valueList s).length = r := valueList_length s
    rw [initLen, hinit, hlen]
    omega
  · push Not at hc1
    rcases hc1 with ⟨x, hxk, hgt⟩
    have hxr : x < r := by
      by_contra hxr'
      have hge : r ≤ x := le_of_not_gt hxr'
      have hz : pad0 s x = 0 := pad0_of_ge s hge
      omega
    have hp : pad0 s x = (s ⟨x, hxr⟩ : ℕ) := pad0_of_lt s hxr
    have hgt' : q < (s ⟨x, hxr⟩ : ℕ) := by rwa [hp] at hgt
    have hle := initLen_le_of_gt q s x hxr hgt'
    omega

end ZagierHoffmanPositiveChar
