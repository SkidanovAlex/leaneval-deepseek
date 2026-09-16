import Submission.ZagierHoffmanProof.StepL131
set_option autoImplicit false
set_option maxHeartbeats 4000000
open Polynomial RatFunc
open scoped BigOperators
/-!
# Step L132: the GENERIC (k, j) member dispatch against MainkStep3/P_full
(SESSION 258z)

StepL131's dispatch specialised to j = k−3; this module states it for an
ARBITRARY j (1 ≤ j ≤ k−1), with `hmid`/`hsj` and the (k−1)-front admissibility
`hsleq` as hypotheses and the MainkStep evidence taken from StepL119's generic
`maink_chain_step_all`.  This is the piece every CASE-1 splice (kk3 and the
deeper-j ones) plugs into its `rec`:
    rec := fun r' m hm hstep3 hnotkadm => dispatch …
The kk3 instance recovers StepL131 exactly (via `maink_kk3_hmid`).
theorem_B/D remain ABP-gated (no route).
-/

namespace ZagierHoffmanPositiveChar
attribute [local instance] Classical.propDecidable
variable (F : Type*) [Field F] [Finite F] [DecidableEq (RatFunc F)]

/-- ★ The per-member dispatch of a CASE-1 (k, j) splice against MainkStep3/P_full
(the j = k−3 case is StepL131's `maink_kk3_member_dispatch`). -/
theorem maink_case1_member_dispatch (w : ℕ) (r : ℕ) (s : Fin r → ℕ+) (hw : weight r s = w)
    (k j : ℕ) (hk1 : 1 ≤ k) (hkr : k ≤ r) (hj1 : 1 ≤ j) (hjk : j ≤ k - 1)
    (hbig : (Nat.card F : ℕ) < (s ⟨k - 1, by omega⟩ : ℕ))
    (hsj : (s ⟨j - 1, by omega⟩ : ℕ) < Nat.card F)
    (hmid : ∀ i : Fin r, (j : ℕ) ≤ (i : ℕ) → (i : ℕ) < k - 1 → (s i : ℕ) = Nat.card F)
    (hsleq : ∀ x : ℕ, x < k - 1 → pad0 s x ≤ Nat.card F)
    (R0 : BinaryRel F) (u : R0.ιA)
    (hbhd : ∀ j' : R0.ιB, ((R0.cB j') ⟨0, R0.hdepB j'⟩ : ℕ) = 1)
    (hhead : ∀ i₀ : R0.ιA, i₀ ≠ u →
      ((R0.cA i₀) ⟨0, R0.hdepA i₀⟩ : ℕ) < (s ⟨k - 1, by omega⟩ : ℕ))
    (hbndB : ∀ j' : R0.ιB, ∀ m : ℕ,
      psum (expTail (R0.cB j')) m ≤ psumSeq (tupPadSum (single (qMinusExp F))
        (consVec (w1Of F r s k hk1 hkr hbig) (sTail r s k hkr))) m)
    (hwtA : ∀ i : R0.ιA, i ≠ u →
      weight (R0.depA i) (R0.cA i) = psum s r - psum s (k - 1))
    (hXw : ∀ j' : R0.ιB,
      weight (R0.depB j' - 1) (expTail (R0.cB j')) = psum s r - psum s (k - 1) - 1)
    (rec : ∀ (r' : ℕ) (m : Fin r' → ℕ+) (_hm : weight r' m = w),
      MainkStep3 k (Nat.card F) w s m → ¬ kAdmissible (Nat.card F) m k → AdmExpT F w k m) :
    let D := RelData.BCqIter F (k - j - 1) (toData F R0)
    let Bs := ofBstarOver F D (s ⟨j - 1, by omega⟩)
        (fun e => BCqIter_valid F (k - j - 1) R0 e)
        (RelData.iterate_merge_hv F (k - j - 1) R0 (s ⟨j - 1, by omega⟩) (by omega) hbhd)
    let Q := FixedOver.prependList F Bs (sPrefix r s j (by omega) (by omega))
    (∀ i₀ : R0.ιA, i₀ ≠ u → AdmExpT F w k
        (Q.c (Sum.inl (RelData.iterIdx F (k - j - 1) (toData F R0) i₀)))) ∧
    (∀ i : D.ιB, AdmExpT F w k (Q.c (Sum.inr (Sum.inl i)))) ∧
    (∀ i : D.ιB, AdmExpT F w k (Q.c (Sum.inr (Sum.inr i)))) := by
  classical
  intro D Bs Q
  have hstep := maink_chain_step_all F r s k j hk1 hkr hj1 hjk hbig hsj hmid hsleq
    R0 u hbhd hhead hbndB
  refine ⟨?_, ?_, ?_⟩
  · intro i₀ hi₀
    by_cases hkadm : kAdmissible (Nat.card F)
        (Q.c (Sum.inl (RelData.iterIdx F (k - j - 1) (toData F R0) i₀))) k
    · exact admExpT_self F w k
        (Q.hdep (Sum.inl (RelData.iterIdx F (k - j - 1) (toData F R0) i₀)))
        _ ((type1_weight_eq F r s k j hk1 hkr hj1 hjk hbig hsj hmid
          R0 hbhd i₀ (hwtA i₀ hi₀)).trans hw) hkadm
    · refine rec _ _ ?_ ?_ hkadm
      · exact (type1_weight_eq F r s k j hk1 hkr hj1 hjk hbig hsj hmid
          R0 hbhd i₀ (hwtA i₀ hi₀)).trans hw
      · exact maink_step_to_step3 k (Nat.card F) w s _ hw
          ((type1_weight_eq F r s k j hk1 hkr hj1 hjk hbig hsj hmid
            R0 hbhd i₀ (hwtA i₀ hi₀)).trans hw) (hstep.1 i₀ hi₀)
  · intro i
    by_cases hkadm : kAdmissible (Nat.card F) (Q.c (Sum.inr (Sum.inl i))) k
    · exact admExpT_self F w k (Q.hdep (Sum.inr (Sum.inl i))) _
        ((type2_weight_eq F r s k j hk1 hkr hj1 hjk hbig hsj hmid
          R0 hbhd i hXw).trans hw) hkadm
    · refine rec _ _ ?_ ?_ hkadm
      · exact (type2_weight_eq F r s k j hk1 hkr hj1 hjk hbig hsj hmid
          R0 hbhd i hXw).trans hw
      · exact maink_step_to_step3 k (Nat.card F) w s _ hw
          ((type2_weight_eq F r s k j hk1 hkr hj1 hjk hbig hsj hmid
            R0 hbhd i hXw).trans hw) (hstep.2.1 i)
  · intro i
    by_cases hkadm : kAdmissible (Nat.card F) (Q.c (Sum.inr (Sum.inr i))) k
    · exact admExpT_self F w k (Q.hdep (Sum.inr (Sum.inr i))) _
        ((type3_weight_eq F r s k j hk1 hkr hj1 hjk hbig hsj hmid
          R0 hbhd i hXw).trans hw) hkadm
    · refine rec _ _ ?_ ?_ hkadm
      · exact (type3_weight_eq F r s k j hk1 hkr hj1 hjk hbig hsj hmid
          R0 hbhd i hXw).trans hw
      · exact maink_step_to_step3 k (Nat.card F) w s _ hw
          ((type3_weight_eq F r s k j hk1 hkr hj1 hjk hbig hsj hmid
            R0 hbhd i hXw).trans hw) (hstep.2.2 i)

/-- The kk3 instance recovers StepL131's specialised dispatch. -/
theorem maink_kk3_member_dispatch'  (w : ℕ) (r : ℕ) (s : Fin r → ℕ+) (hw : weight r s = w)
    (k : ℕ) (hk1 : 1 ≤ k) (hk4 : 4 ≤ k) (hkr : k ≤ r)
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
        (consVec (w1Of F r s k hk1 hkr hbig) (sTail r s k hkr))) m)
    (hwtA : ∀ i : R0.ιA, i ≠ u →
      weight (R0.depA i) (R0.cA i) = psum s r - psum s (k - 1))
    (hXw : ∀ j' : R0.ιB,
      weight (R0.depB j' - 1) (expTail (R0.cB j')) = psum s r - psum s (k - 1) - 1)
    (rec : ∀ (r' : ℕ) (m : Fin r' → ℕ+) (_hm : weight r' m = w),
      MainkStep3 k (Nat.card F) w s m → ¬ kAdmissible (Nat.card F) m k → AdmExpT F w k m) :
    let D := RelData.BCqIter F (k - (k - 3) - 1) (toData F R0)
    let Bs := ofBstarOver F D (s ⟨k - 3 - 1, by omega⟩)
        (fun e => BCqIter_valid F (k - (k - 3) - 1) R0 e)
        (RelData.iterate_merge_hv F (k - (k - 3) - 1) R0 (s ⟨k - 3 - 1, by omega⟩) (by omega) hbhd)
    let Q := FixedOver.prependList F Bs (sPrefix r s (k - 3) (by omega) (by omega))
    (∀ i₀ : R0.ιA, i₀ ≠ u → AdmExpT F w k
        (Q.c (Sum.inl (RelData.iterIdx F (k - (k - 3) - 1) (toData F R0) i₀)))) ∧
    (∀ i : D.ιB, AdmExpT F w k (Q.c (Sum.inr (Sum.inl i)))) ∧
    (∀ i : D.ιB, AdmExpT F w k (Q.c (Sum.inr (Sum.inr i)))) :=
  maink_case1_member_dispatch F w r s hw k (k - 3) hk1 hkr (by omega) (by omega) hbig hsj
    (maink_kk3_hmid F r s k hk1 hkr hqmid hqmid1) hsleq R0 u hbhd hhead hbndB hwtA hXw rec

end ZagierHoffmanPositiveChar
