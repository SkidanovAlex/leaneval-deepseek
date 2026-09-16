import Submission.ZagierHoffmanProof.StepL19

set_option autoImplicit false
set_option maxHeartbeats 100000000
open Polynomial RatFunc
open scoped BigOperators

/-!
# Step L20: the (2.14) instantiated validity at the s/k/j configuration

`sPrefix` builds Prop 2.12's prefix entries `(s_{j-1}, …, s_1)` (application order);
`sTail` the tail `(s_{k+1}, …, s_r)`.  `succ_merge_hv` gives the B*_v merge condition
on a `(m+1)`-iterate without hypotheses on `R` (b-heads are `1` by
`BCqIter_cB_head`).  ★ `chain_valid_of` is the instantiated validity on a BinaryRel
`R0` with `1`-headed `b`-tuples and a distinguished coefficient-`1` output `u`.
★ `chain_valid_sjk_data` is the concrete Prop-2.12 configuration: given the
Lemma-2.9 data at `W := (s_k − q, s_{k+1}, …, s_r)` (`R0`, `u`, `ha`, `hbhd` — the
outputs of `lemma_2_9_rel`, which now also exposes the `1`-headedness), iterate
`BC_q` `k−j−1` times, apply B*_{s_j}, prepend `(s_{j−1}, …, s_1)`; validity at every
level.  (Assembly: `rcases lemma_2_9_rel` for the data, then this theorem.)
-/

namespace ZagierHoffmanPositiveChar
attribute [instance] P2Data.fin
attribute [instance] RelData.finA
attribute [instance] RelData.finB
attribute [instance] FixedRel.fin
variable (F : Type*) [Field F] [Finite F] [DecidableEq (RatFunc F)]

/-- The prefix entries `(s_{j-1}, …, s_1)` (1-indexed) of Prop 2.12's (2.14), in
application order: `s`-entries at Fin-indices `j-2, j-3, …, 0`. -/
noncomputable def sPrefix (r : ℕ) (s : Fin r → ℕ+) (j : ℕ) (hr1 : 1 ≤ r) (hj : j ≤ r) : List ℕ+ :=
  (List.range (j - 1)).map (fun i : ℕ => s ⟨(j - 2) - i, by omega⟩)

/-- The tail `(s_{k+1}, …, s_r)` (1-indexed) of `s` after its `k`-th entry. -/
noncomputable def sTail (r : ℕ) (s : Fin r → ℕ+) (k : ℕ) (hkr : k ≤ r) : Fin (r - k) → ℕ+ :=
  fun i => s ⟨k + (i : ℕ), by omega⟩

/-- Merge condition on the `(m+1)`-iterate: b-heads are `1` (`BCqIter_cB_head`), no
hypothesis on `R`'s own heads needed. -/
lemma succ_merge_hv (m : ℕ) (R : BinaryRel F) (v : ℕ+) (hvq : (v : ℕ) + 1 ≤ Nat.card F) :
    ∀ p : (RelData.BCqIter F (m + 1) (toData F R)).ιB,
      (v : ℕ) + (((RelData.BCqIter F (m + 1) (toData F R)).cB p)
        ⟨0, (RelData.BCqIter F (m + 1) (toData F R)).hdepB p⟩ : ℕ) ≤ Nat.card F := by
  classical
  intro p
  have hh := RelData.BCqIter_cB_head F m (toData F R) p
  have hv1 : (((RelData.BCqIter F (m + 1) (toData F R)).cB p)
      ⟨0, (RelData.BCqIter F (m + 1) (toData F R)).hdepB p⟩ : ℕ) = 1 := by
    calc
      (((RelData.BCqIter F (m + 1) (toData F R)).cB p)
          ⟨0, (RelData.BCqIter F (m + 1) (toData F R)).hdepB p⟩ : ℕ) = (oneExp : ℕ) := by
        simpa using congrArg (fun t : ℕ+ => (t : ℕ)) hh
      _ = 1 := by simp [oneExp]
  omega

/-- ★ The instantiated chain validity: given a BinaryRel `R0` whose `b`-tuples are
`1`-headed (`hbhd` — supplied by `lemma_2_9_rel`), a distinguished `a`-output `u` with
coefficient `1`, iterate `BC_q` `n` times, apply B*_v, prepend `xs`; the level is `0`
at every level. -/
theorem chain_valid_of (R0 : BinaryRel F)
    (hbhd : ∀ j : R0.ιB, ((R0.cB j) ⟨0, R0.hdepB j⟩ : ℕ) = 1)
    (u : R0.ιA) (ha : R0.aA u = 1) (n : ℕ) (v : ℕ+) (hvq : (v : ℕ) + 1 ≤ Nat.card F)
    (xs : List ℕ+) (d : ℕ) :
    FixedOver.level F
      (FixedOver.prependList F
        (ofBstarOver F (RelData.BCqIter F n (toData F R0)) v
          (fun e => BCqIter_valid F n R0 e)
          (RelData.iterate_merge_hv F n R0 v hvq hbhd)) xs) d = 0 := by
  exact FixedOver.prependList_valid F
    (ofBstarOver F (RelData.BCqIter F n (toData F R0)) v
      (fun e => BCqIter_valid F n R0 e)
      (RelData.iterate_merge_hv F n R0 v hvq hbhd)) xs d

/-- ★ The concrete instantiation at the Prop-2.12 configuration, data-shaped: given
the Lemma-2.9 relation data `(R0, u)` at `W := (s_k − q, s_{k+1}, …, s_r)` — i.e. the
conjuncts of `lemma_2_9_rel` (`ha`, `hbhd`, …) — iterate `BC_q` `k−j−1` times, apply
B*_{s_j} (`hsj` supplies `s_j < q` for the merge), prepend `(s_{j−1}, …, s_1)`; the
fixed relation is valid at every level.  (Assembly: `rcases lemma_2_9_rel …` to get
these hypotheses, then this theorem; the leading member is `u`.) -/
theorem chain_valid_sjk_data (r : ℕ) (s : Fin r → ℕ+) (k j : ℕ)
    (hk1 : 1 ≤ k) (hkr : k ≤ r) (hj1 : 1 ≤ j) (hjk : j ≤ k - 1)
    (hbig : (Nat.card F : ℕ) < (s ⟨k - 1, by omega⟩ : ℕ))
    (hsj : (s ⟨j - 1, by omega⟩ : ℕ) < Nat.card F)
    (R0 : BinaryRel F) (u : R0.ιA)
    (ha : R0.aA u = 1)
    (hbhd : ∀ j' : R0.ιB, ((R0.cB j') ⟨0, R0.hdepB j'⟩ : ℕ) = 1) :
    ∀ d : ℕ,
      FixedOver.level F
        (FixedOver.prependList F
          (ofBstarOver F (RelData.BCqIter F (k - j - 1) (toData F R0))
            (s ⟨j - 1, by omega⟩)
            (fun e => BCqIter_valid F (k - j - 1) R0 e)
            (RelData.iterate_merge_hv F (k - j - 1) R0 (s ⟨j - 1, by omega⟩)
              (by omega) hbhd))
          (sPrefix r s j (by omega) (by omega))) d = 0 := by
  intro d
  exact chain_valid_of F R0 hbhd u ha (k - j - 1) (s ⟨j - 1, by omega⟩)
    (by omega) (sPrefix r s j (by omega) (by omega)) d

end ZagierHoffmanPositiveChar
