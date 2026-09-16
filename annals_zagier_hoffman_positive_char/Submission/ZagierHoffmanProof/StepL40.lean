import Submission.ZagierHoffmanProof.StepL39
import Submission.ZagierHoffmanProof.StepL24

set_option autoImplicit false
set_option maxHeartbeats 100000000
open Polynomial RatFunc
open scoped BigOperators

/-!
# Step L40: R1-chain leading-tuple VALUE, DEPTH and ζ-lemmas (CASE-2, Prop 2.13)

The CASE-2 (Prop 2.13) chain runs the same `s/k/j` construction as CASE-1 but with
`R0 := r1Rel F`, `u := PUnit.unit`, on an input `s : Fin k` of depth `k` with
`s₁..s_{k−1} ≤ q` and `s_k = q`; `j` is the last index with `s_j < q`, so positions
`j..k−1` (0-based) of `s` are all `q` (`hqend`).  The leading member of the chain —
`Q.c (inl u')` with `Q := prependList Bs (sPrefix k s j)`, `Bs := B*_{s_j}` applied
to the `BC_q^{k−j−1}`-iterate of `r1Rel` — then IS `s`:
  front region (positions `0..j−2`): the prefix entries `s₁..s_{j−1}` (R0-independent);
  base region (positions `j−1..k−1`): the B*-leading values `(s_j, q, …, q)` which
  match `s_{j−1}..s_{k−1}` (head `s_j` at position 0, then all-`q` — the R1 a-iterate
  is all-`q` by `r1_iter_cA_all_q` and the `q`-end block of `s` by `hqend`).
These three lemmas are the CASE-2 analogues of StepL24's `leading_tuple_value`,
`leading_dep`, `leading_zeta` (there, `bstarBase`/`hbig`/`hmid`; here the all-`q`
end block).  `leading_zeta_R1` gives `ζ_A s = ζ_A (Q.c (inl u'))`, the value content
of the CASE-2 `zeta_213`.
-/

namespace ZagierHoffmanPositiveChar
attribute [instance] P2Data.fin
attribute [instance] RelData.finA
attribute [instance] RelData.finB
attribute [instance] FixedRel.fin
attribute [local instance] Classical.propDecidable
variable (F : Type*) [Field F] [Finite F] [DecidableEq (RatFunc F)]

/-- Value of the R1-chain leading tuple at every position `m` — the tuple IS `s`:
front region (`m < j−1`) has `s₁..s_{j−1}` via the prefix-prepend front values, base
region has the B*-leading values `(s_j, q, …, q) = s_{j−1}..s_{k−1}`. -/
lemma leading_tuple_value_R1 (k : ℕ) (s : Fin k → ℕ+) (j : ℕ)
    (hk1 : 1 ≤ k) (hj1 : 1 ≤ j) (hjk : j ≤ k - 1)
    (hsj : (s ⟨j - 1, by omega⟩ : ℕ) < Nat.card F)
    (hqend : ∀ i : Fin k, (j : ℕ) ≤ (i : ℕ) → (i : ℕ) < k → (s i : ℕ) = Nat.card F) :
    let D := RelData.BCqIter F (k - j - 1) (toData F (r1Rel F))
    let Bs := ofBstarOver F D (s ⟨j - 1, by omega⟩) (fun e => BCqIter_valid F (k - j - 1) (r1Rel F) e)
        (RelData.iterate_merge_hv F (k - j - 1) (r1Rel F) (s ⟨j - 1, by omega⟩) (by omega) (r1Rel_hbhd F))
    let Q := FixedOver.prependList F Bs (sPrefix k s j (by omega) (by omega))
    ∀ (m : ℕ) (hmQ : m < Q.dep (Sum.inl (RelData.iterIdx F (k - j - 1) (toData F (r1Rel F)) PUnit.unit)))
      (hmk : m < k),
      Q.c (Sum.inl (RelData.iterIdx F (k - j - 1) (toData F (r1Rel F)) PUnit.unit)) ⟨m, hmQ⟩ = s ⟨m, hmk⟩ := by
  classical
  intro D Bs Q m hmQ hmk
  let u' := RelData.iterIdx F (k - j - 1) (toData F (r1Rel F)) PUnit.unit
  have hlen : (sPrefix k s j (by omega) (by omega)).length = j - 1 :=
    sPrefix_length k s j (by omega) (by omega)
  by_cases hpre : m < (sPrefix k s j (by omega) (by omega)).length
  · -- front region: value = (sPrefix.reverse).get m = s⟨m⟩
    have hval := prependList_c_front_value F Bs (sPrefix k s j (by omega) (by omega))
      (Sum.inl u') m hmQ hpre
    rw [hval]
    exact sPrefix_reverse_value k s j (by omega) (by omega) m hpre
  · -- base region: value = Bs.c u' at m − len = s⟨(j−1) + (m−len)⟩ = s⟨m⟩
    have hge : (sPrefix k s j (by omega) (by omega)).length ≤ m := le_of_not_gt hpre
    have hval := prependList_c_base_value F Bs (sPrefix k s j (by omega) (by omega))
      (Sum.inl u') m hmQ hge
    rw [hval]
    have hQdep : Q.dep (Sum.inl u') =
        Bs.dep (Sum.inl u') + (sPrefix k s j (by omega) (by omega)).length := by
      exact FixedOver.prependList_dep F Bs (sPrefix k s j (by omega) (by omega)) (Sum.inl u')
    have hm1 : m < Bs.dep (Sum.inl u') + (sPrefix k s j (by omega) (by omega)).length := by
      rw [← hQdep]
      exact hmQ
    have hℓ : m - (sPrefix k s j (by omega) (by omega)).length < Bs.dep (Sum.inl u') := by
      omega
    have hbd' : (j - 1) + (m - (sPrefix k s j (by omega) (by omega)).length) < k := by
      omega
    have hbv := Bs_leading_pos_R1 F k j s hk1 hj1 hjk hsj hqend
      (m - (sPrefix k s j (by omega) (by omega)).length) hℓ hbd'
    rw [hbv]
    congr 1
    apply Fin.ext
    simp
    omega

/-- Depth of the R1-chain leading member is `k`. -/
lemma leading_dep_R1 (k : ℕ) (s : Fin k → ℕ+) (j : ℕ)
    (hk1 : 1 ≤ k) (hj1 : 1 ≤ j) (hjk : j ≤ k - 1)
    (hsj : (s ⟨j - 1, by omega⟩ : ℕ) < Nat.card F) :
    let D := RelData.BCqIter F (k - j - 1) (toData F (r1Rel F))
    let Bs := ofBstarOver F D (s ⟨j - 1, by omega⟩) (fun e => BCqIter_valid F (k - j - 1) (r1Rel F) e)
        (RelData.iterate_merge_hv F (k - j - 1) (r1Rel F) (s ⟨j - 1, by omega⟩) (by omega) (r1Rel_hbhd F))
    let Q := FixedOver.prependList F Bs (sPrefix k s j (by omega) (by omega))
    Q.dep (Sum.inl (RelData.iterIdx F (k - j - 1) (toData F (r1Rel F)) PUnit.unit)) = k := by
  classical
  intro D Bs Q
  let u' := RelData.iterIdx F (k - j - 1) (toData F (r1Rel F)) PUnit.unit
  have h1 := FixedOver.prependList_dep F Bs (sPrefix k s j (by omega) (by omega)) (Sum.inl u')
  have hlen : (sPrefix k s j (by omega) (by omega)).length = j - 1 :=
    sPrefix_length k s j (by omega) (by omega)
  have h2 : Bs.dep (Sum.inl u') = (RelData.BCqIter F (k - j - 1) (toData F (r1Rel F))).depA u' + 1 := by
    dsimp [Bs, ofBstarOver, D]
  have h3 : (RelData.BCqIter F (k - j - 1) (toData F (r1Rel F))).depA u' =
      (r1Rel F).depA PUnit.unit + (k - j - 1) := by
    dsimp [u']
    exact RelData.BCqIter_depA_at F (k - j - 1) (toData F (r1Rel F)) PUnit.unit
  calc
    Q.dep (Sum.inl u') = Bs.dep (Sum.inl u') + (sPrefix k s j (by omega) (by omega)).length := h1
    _ = Bs.dep (Sum.inl u') + (j - 1) := by rw [hlen]
    _ = ((RelData.BCqIter F (k - j - 1) (toData F (r1Rel F))).depA u' + 1) + (j - 1) := by rw [h2]
    _ = ((r1Rel F).depA PUnit.unit + (k - j - 1) + 1) + (j - 1) := by rw [h3]
    _ = k := by
      simp [r1Rel]
      omega

/-- The leading member of the CASE-2 chain evaluates to `ζ_A s`. -/
theorem leading_zeta_R1 (k : ℕ) (s : Fin k → ℕ+) (j : ℕ)
    (hk1 : 1 ≤ k) (hj1 : 1 ≤ j) (hjk : j ≤ k - 1)
    (hsj : (s ⟨j - 1, by omega⟩ : ℕ) < Nat.card F)
    (hqend : ∀ i : Fin k, (j : ℕ) ≤ (i : ℕ) → (i : ℕ) < k → (s i : ℕ) = Nat.card F) :
    let D := RelData.BCqIter F (k - j - 1) (toData F (r1Rel F))
    let Bs := ofBstarOver F D (s ⟨j - 1, by omega⟩) (fun e => BCqIter_valid F (k - j - 1) (r1Rel F) e)
        (RelData.iterate_merge_hv F (k - j - 1) (r1Rel F) (s ⟨j - 1, by omega⟩) (by omega) (r1Rel_hbhd F))
    let Q := FixedOver.prependList F Bs (sPrefix k s j (by omega) (by omega))
    ζ_A F s = ζ_A F (Q.c (Sum.inl (RelData.iterIdx F (k - j - 1) (toData F (r1Rel F)) PUnit.unit))) := by
  classical
  intro D Bs Q
  let u' := RelData.iterIdx F (k - j - 1) (toData F (r1Rel F)) PUnit.unit
  have hdepQ : Q.dep (Sum.inl u') = k := by
    dsimp [Q, Bs, D, u']
    exact leading_dep_R1 F k s j hk1 hj1 hjk hsj
  exact (ζ_A_eq_of_reindex F hdepQ (Q.c (Sum.inl u')) s
    (fun i : Fin (Q.dep (Sum.inl u')) => by
      have hmk : (i : ℕ) < k := by
        have hq := i.isLt
        simpa [hdepQ] using hq
      have hv := leading_tuple_value_R1 F k s j hk1 hj1 hjk hsj hqend (i : ℕ) i.isLt hmk
      rw [hv])).symm

end ZagierHoffmanPositiveChar
