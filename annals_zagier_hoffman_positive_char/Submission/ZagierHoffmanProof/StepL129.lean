import Submission.ZagierHoffmanProof.StepL128
import Submission.ZagierHoffmanProof.StepL119
set_option autoImplicit false
set_option maxHeartbeats 1000000
open Polynomial RatFunc
open scoped BigOperators
/-!
# Step L129: the (k, k−3) CASE-1 dispatch, first pieces (SESSION 258v)

`maink_case1_kk3` (StepL115 obligation (2)) needs, for every member of the
(k, k−3)-chain: (i) MainkStep-from-s at level k, and (ii) (k−1)-admissibility
(so the (k−1)-adm `rec` carries it — the (k,k−3) members are automatically
(k−1)-adm, per PLAN SESSION 258n).

This module delivers:
  • `maink_kk3_hmid`: the `hmid` of the (k, k−3)-shape (s⟨k−3⟩ = s⟨k−2⟩ = q);
  • ★ `maink_type1_k1adm`: EVERY type-1 (i₀ ≠ u) member is (k−1)-adm, for ALL j
    (cond1: entries 0..k−2 = s's by StepL126 + the (k−1)-admissibility `hadm`;
     cond2: the member's depth is ≥ k by `maink_type1_dep_ge`, so the
     depth-form witness r ≤ k−1 is impossible);
  • ★ `maink_kk3_chain_step`: the MainkStep conjuncts at (k, k−3), a direct
    instantiation of `maink_chain_step_all` (StepL119).
Type-2/3 members' (k−1)-admissibility (the remaining half at j = k−3, needing the
level-2 fiber head/entry-1 bounds) is the next StepL130 piece.
theorem_B/D remain ABP-gated (no route).
-/

namespace ZagierHoffmanPositiveChar
attribute [local instance] Classical.propDecidable
variable (F : Type*) [Field F] [Finite F] [DecidableEq (RatFunc F)]

omit [Field F] [Finite F] [DecidableEq (RatFunc F)] in
/-- The `hmid` of the (k, k−3)-shape: the entries k−3 and k−2 equal q. -/
lemma maink_kk3_hmid (r : ℕ) (s : Fin r → ℕ+) (k : ℕ) (hk1 : 1 ≤ k) (hkr : k ≤ r)
    (hqmid : (s ⟨k - 3, by omega⟩ : ℕ) = Nat.card F)
    (hqmid1 : (s ⟨k - 2, by omega⟩ : ℕ) = Nat.card F) :
    ∀ i : Fin r, (k - 3 : ℕ) ≤ (i : ℕ) → (i : ℕ) < k - 1 → (s i : ℕ) = Nat.card F := by
  intro i hi1 hi2
  have hi : (i : ℕ) = k - 3 ∨ (i : ℕ) = k - 2 := by omega
  rcases hi with h | h
  · rw [show i = ⟨k - 3, by omega⟩ from Fin.ext h]
    exact hqmid
  · rw [show i = ⟨k - 2, by omega⟩ from Fin.ext h]
    exact hqmid1

/-- ★ Every type-1 (i₀ ≠ u) member of the (k, j)-chain is `(k−1)`-admissible
(for EVERY j) — cond1 from the entrywise agreement with s, cond2 from the
depth bound. -/
theorem maink_type1_k1adm (r : ℕ) (s : Fin r → ℕ+) (k j : ℕ)
    (hk1 : 1 ≤ k) (hkr : k ≤ r) (hj1 : 1 ≤ j) (hjk : j ≤ k - 1)
    (hbig : (Nat.card F : ℕ) < (s ⟨k - 1, by omega⟩ : ℕ))
    (hsj : (s ⟨j - 1, by omega⟩ : ℕ) < Nat.card F)
    (hadm : ∀ x : ℕ, x < k - 1 → pad0 s x ≤ Nat.card F)
    (hmid : ∀ i : Fin r, (j : ℕ) ≤ (i : ℕ) → (i : ℕ) < k - 1 → (s i : ℕ) = Nat.card F)
    (R0 : BinaryRel F)
    (hbhd : ∀ j' : R0.ιB, ((R0.cB j') ⟨0, R0.hdepB j'⟩ : ℕ) = 1) :
    let D := RelData.BCqIter F (k - j - 1) (toData F R0)
    let Bs := ofBstarOver F D (s ⟨j - 1, by omega⟩) (fun e => BCqIter_valid F (k - j - 1) R0 e)
        (RelData.iterate_merge_hv F (k - j - 1) R0 (s ⟨j - 1, by omega⟩) (by omega) hbhd)
    let Q := FixedOver.prependList F Bs (sPrefix r s j (by omega) (by omega))
    ∀ i₀ : R0.ιA,
      kAdmissible (Nat.card F)
        (Q.c (Sum.inl (RelData.iterIdx F (k - j - 1) (toData F R0) i₀))) (k - 1) := by
  classical
  intro D Bs Q i₀
  have hdep : k ≤ Q.dep (Sum.inl (RelData.iterIdx F (k - j - 1) (toData F R0) i₀)) :=
    maink_type1_dep_ge F r s k j hk1 hkr hj1 hjk hbig hsj R0 hbhd i₀
  refine ⟨?_, ?_⟩
  · intro x hx
    exact (maink_type1_entry_eq F r s k j hk1 hkr hj1 hjk hbig hsj hmid R0 hbhd i₀ x hx).trans_le
      (hadm x hx)
  · intro hwit
    rcases hwit with ⟨hr1, hrle, -, -⟩
    omega

/-- ★ The MainkStep conjuncts of the (k, k−3)-chain (instantiation of
`maink_chain_step_all` at j = k−3). -/
theorem maink_kk3_chain_step (r : ℕ) (s : Fin r → ℕ+) (k : ℕ)
    (hk1 : 1 ≤ k) (hk4 : 4 ≤ k) (hkr : k ≤ r)
    (hbig : (Nat.card F : ℕ) < (s ⟨k - 1, by omega⟩ : ℕ))
    (hsj : (s ⟨k - 3 - 1, by omega⟩ : ℕ) < Nat.card F)
    (hqmid : (s ⟨k - 3, by omega⟩ : ℕ) = Nat.card F)
    (hqmid1 : (s ⟨k - 2, by omega⟩ : ℕ) = Nat.card F)
    (hsleq : ∀ x : ℕ, x < k - 1 → pad0 s x ≤ Nat.card F)
    (R0 : BinaryRel F) (u : R0.ιA)
    (hbhd : ∀ j' : R0.ιB, ((R0.cB j') ⟨0, R0.hdepB j'⟩ : ℕ) = 1)
    (hhead : ∀ i₀ : R0.ιA, i₀ ≠ u →
      ((R0.cA i₀) ⟨0, R0.hdepA i₀⟩ : ℕ) < (s ⟨k - 1, by omega⟩ : ℕ))
    (hbndB : ∀ j' : R0.ιB, ∀ m : ℕ,
      psum (expTail (R0.cB j')) m ≤ psumSeq (tupPadSum (single (qMinusExp F))
        (consVec (w1Of F r s k hk1 hkr hbig) (sTail r s k hkr))) m) :
    let D := RelData.BCqIter F (k - (k - 3) - 1) (toData F R0)
    let Bs := ofBstarOver F D (s ⟨k - 3 - 1, by omega⟩)
        (fun e => BCqIter_valid F (k - (k - 3) - 1) R0 e)
        (RelData.iterate_merge_hv F (k - (k - 3) - 1) R0 (s ⟨k - 3 - 1, by omega⟩) (by omega) hbhd)
    let Q := FixedOver.prependList F Bs (sPrefix r s (k - 3) (by omega) (by omega))
    (∀ i₀ : R0.ιA, i₀ ≠ u → MainkStep k (Nat.card F) s
        (Q.c (Sum.inl (RelData.iterIdx F (k - (k - 3) - 1) (toData F R0) i₀)))) ∧
    (∀ i : D.ιB, MainkStep k (Nat.card F) s (Q.c (Sum.inr (Sum.inl i)))) ∧
    (∀ i : D.ιB, MainkStep k (Nat.card F) s (Q.c (Sum.inr (Sum.inr i)))) := by
  classical
  have hmid := maink_kk3_hmid F r s k hk1 hkr hqmid hqmid1
  exact maink_chain_step_all F r s k (k - 3) hk1 hkr (by omega) (by omega) hbig hsj hmid
    hsleq R0 u hbhd hhead hbndB

end ZagierHoffmanPositiveChar
