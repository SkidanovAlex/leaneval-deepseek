import Submission.ZagierHoffmanProof.StepL130
set_option autoImplicit false
set_option maxHeartbeats 4000000
open Polynomial RatFunc
open scoped BigOperators
/-!
# Step L131: the (k, k−3) member dispatch against MainkStep3 / P_full (SESSION 258y)

The dispatch core of the `maink_case1_kk3` splice, wired to the (β) machinery
(SESSION 258x decision: the ¬(k−1)-adm members are handled by the MainkStep3
induction hypothesis, so no (k−1)-admissibility / depth bound is needed):
  • k-adm members → `admExpT_self`;
  • ¬k-adm members → `rec` (the P_full IH) with
      – the member's weight = w (the type1/2/3_weight_eq lemmas, fed by hwtA/hXw),
      – the MainkStep3-from-s evidence (StepL129's `maink_kk3_chain_step`, which
        gives the STRONGER `MainkStep`, transferred by `maink_step_to_step3`).
This packages the per-member `e`-function of StepL111's script for j = k−3; the
remaining ζ-fold (`zeta_214_reindexed` at (k,k−3) + the 3-family splice) plugs
`rec := dispatch` directly.
theorem_B/D remain ABP-gated (no route).
-/

namespace ZagierHoffmanPositiveChar
attribute [local instance] Classical.propDecidable
variable (F : Type*) [Field F] [Finite F] [DecidableEq (RatFunc F)]

/-- ★ The per-member dispatch of the (k, k−3) splice against MainkStep3/P_full. -/
theorem maink_kk3_member_dispatch (w : ℕ) (r : ℕ) (s : Fin r → ℕ+) (hw : weight r s = w)
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
    (∀ i : D.ιB, AdmExpT F w k (Q.c (Sum.inr (Sum.inr i)))) := by
  classical
  intro D Bs Q
  have hmid := maink_kk3_hmid F r s k hk1 hkr hqmid hqmid1
  have hstep := maink_kk3_chain_step F r s k hk1 hk4 hkr hbig hsj hqmid hqmid1 hsleq
    R0 u hbhd hhead hbndB
  refine ⟨?_, ?_, ?_⟩
  · intro i₀ hi₀
    by_cases hkadm : kAdmissible (Nat.card F)
        (Q.c (Sum.inl (RelData.iterIdx F (k - (k - 3) - 1) (toData F R0) i₀))) k
    · exact admExpT_self F w k
        (Q.hdep (Sum.inl (RelData.iterIdx F (k - (k - 3) - 1) (toData F R0) i₀)))
        _ ((type1_weight_eq F r s k (k - 3) hk1 hkr (by omega) (by omega) hbig hsj hmid
          R0 hbhd i₀ (hwtA i₀ hi₀)).trans hw) hkadm
    · refine rec _ _ ?_ ?_ hkadm
      · exact (type1_weight_eq F r s k (k - 3) hk1 hkr (by omega) (by omega) hbig hsj hmid
          R0 hbhd i₀ (hwtA i₀ hi₀)).trans hw
      · exact maink_step_to_step3 k (Nat.card F) w s _ hw
          ((type1_weight_eq F r s k (k - 3) hk1 hkr (by omega) (by omega) hbig hsj hmid
            R0 hbhd i₀ (hwtA i₀ hi₀)).trans hw) (hstep.1 i₀ hi₀)
  · intro i
    by_cases hkadm : kAdmissible (Nat.card F) (Q.c (Sum.inr (Sum.inl i))) k
    · exact admExpT_self F w k (Q.hdep (Sum.inr (Sum.inl i))) _
        ((type2_weight_eq F r s k (k - 3) hk1 hkr (by omega) (by omega) hbig hsj hmid
          R0 hbhd i hXw).trans hw) hkadm
    · refine rec _ _ ?_ ?_ hkadm
      · exact (type2_weight_eq F r s k (k - 3) hk1 hkr (by omega) (by omega) hbig hsj hmid
          R0 hbhd i hXw).trans hw
      · exact maink_step_to_step3 k (Nat.card F) w s _ hw
          ((type2_weight_eq F r s k (k - 3) hk1 hkr (by omega) (by omega) hbig hsj hmid
            R0 hbhd i hXw).trans hw) (hstep.2.1 i)
  · intro i
    by_cases hkadm : kAdmissible (Nat.card F) (Q.c (Sum.inr (Sum.inr i))) k
    · exact admExpT_self F w k (Q.hdep (Sum.inr (Sum.inr i))) _
        ((type3_weight_eq F r s k (k - 3) hk1 hkr (by omega) (by omega) hbig hsj hmid
          R0 hbhd i hXw).trans hw) hkadm
    · refine rec _ _ ?_ ?_ hkadm
      · exact (type3_weight_eq F r s k (k - 3) hk1 hkr (by omega) (by omega) hbig hsj hmid
          R0 hbhd i hXw).trans hw
      · exact maink_step_to_step3 k (Nat.card F) w s _ hw
          ((type3_weight_eq F r s k (k - 3) hk1 hkr (by omega) (by omega) hbig hsj hmid
            R0 hbhd i hXw).trans hw) (hstep.2.2 i)

end ZagierHoffmanPositiveChar
