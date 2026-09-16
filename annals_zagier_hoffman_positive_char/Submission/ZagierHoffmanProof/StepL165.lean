import Submission.ZagierHoffmanProof.StepL164
import Submission.ZagierHoffmanProof.StepL33
set_option autoImplicit false
set_option maxHeartbeats 100000000
open Polynomial RatFunc
open scoped BigOperators
/-!
# Step L165: the AMBIENT step of every member family of the `(k,j)` CASE-1 chain
(SESSION 269) — each member `m` satisfies `ambNu Λ m < ambNu Λ s` at every ambient level

This is the measure-descent interface that the ambient chain splices of route (C) need:
  • TYPE-1: `depth(m) ≥ r` (`type1_dep_ge`) — if strict, the depth component decides; at
    equal depth a strict prefix drop or the `type1_Init` datum (`C2'`/`C3`) decides;
  • TYPE-2: `depth(m) > r` (`type2_dep_gt`) — the depth component decides at once;
  • TYPE-3: `depth(m) ≥ r` (`type3_dep_ge`) plus `type3_Init_gt` (`C2'`), with the prefix
    bound from `type3_psum_le_amb`.
theorem_B/D remain ABP-gated (no route).
-/

namespace ZagierHoffmanPositiveChar
attribute [instance] P2Data.fin
attribute [instance] RelData.finA
attribute [instance] RelData.finB
attribute [instance] FixedRel.fin
attribute [local instance] Classical.propDecidable
variable (F : Type*) [Field F] [Finite F] [DecidableEq (RatFunc F)]

/-- ★ Ambient step for the type-1 members. -/
lemma type1_amb_step (r : ℕ) (s : Fin r → ℕ+) (k j : ℕ)
    (hk1 : 1 ≤ k) (hkr : k ≤ r) (hj1 : 1 ≤ j) (hjk : j ≤ k - 1)
    (hbig : (Nat.card F : ℕ) < (s ⟨k - 1, by omega⟩ : ℕ))
    (hsj : (s ⟨j - 1, by omega⟩ : ℕ) < Nat.card F)
    (hmid : ∀ i : Fin r, (j : ℕ) ≤ (i : ℕ) → (i : ℕ) < k - 1 → (s i : ℕ) = Nat.card F)
    (hsleq : ∀ x : ℕ, x < k - 1 → pad0 s x ≤ Nat.card F)
    (R0 : BinaryRel F)
    (hbhd : ∀ j' : R0.ιB, ((R0.cB j') ⟨0, R0.hdepB j'⟩ : ℕ) = 1) :
    let D := RelData.BCqIter F (k - j - 1) (toData F R0)
    let Bs := ofBstarOver F D (s ⟨j - 1, by omega⟩) (fun e => BCqIter_valid F (k - j - 1) R0 e)
        (RelData.iterate_merge_hv F (k - j - 1) R0 (s ⟨j - 1, by omega⟩) (by omega) hbhd)
    let Q := FixedOver.prependList F Bs (sPrefix r s j (by omega) (by omega))
    ∀ i₀ : R0.ιA,
      (weight (R0.depA i₀) (R0.cA i₀) = psum s r - psum s (k - 1)) →
      (∀ m : ℕ, psum (R0.cA i₀) m ≤ psumSeq (tupPadSum (single (qExp F))
          (consVec (w1Of F r s k hk1 hkr hbig) (sTail r s k hkr))) m) →
      ((R0.cA i₀) ⟨0, R0.hdepA i₀⟩ : ℕ) < (s ⟨k - 1, by omega⟩ : ℕ) →
      ∀ (w : ℕ), weight r s = w → ∀ (Λ : ℕ), k ≤ Λ →
        ambNu Λ (Nat.card F) w
            (Q.c (Sum.inl (RelData.iterIdx F (k - j - 1) (toData F R0) i₀)))
          < ambNu Λ (Nat.card F) w s := by
  classical
  intro D Bs Q i₀ hwtA hpref hhead w hw Λ hΛ
  have hle := type1_psum_le_amb F r s k j hk1 hkr hj1 hjk hbig hsj hmid R0 hbhd
    i₀ hwtA hpref Λ hΛ
  have hdep := type1_dep_ge F r s k j hk1 hkr hj1 hjk hbig hsj R0 hbhd i₀ hwtA hpref
  have hmw : weight (Q.dep (Sum.inl (RelData.iterIdx F (k - j - 1) (toData F R0) i₀)))
      (Q.c (Sum.inl (RelData.iterIdx F (k - j - 1) (toData F R0) i₀))) = w :=
    (type1_weight_eq F r s k j hk1 hkr hj1 hjk hbig hsj hmid R0 hbhd i₀ hwtA).trans hw
  have hmd_le : Q.dep (Sum.inl (RelData.iterIdx F (k - j - 1) (toData F R0) i₀)) ≤ w := by
    rw [← hmw]
    exact weight_ge_depth _ _
  have hs_le : r ≤ w := by
    rw [← hw]
    exact weight_ge_depth r s
  rcases lt_or_eq_of_le hdep with hlt | heq
  · exact ambNu_lt_of_depth_gt Λ (Nat.card F) w s _ hs_le hmd_le hlt hle
  · have hInit := type1_Init F r s k j hk1 hkr hj1 hjk hbig hsj hmid hsleq R0 hbhd i₀ hhead
    rcases lt_or_eq_of_le hle with hplt | hpeq
    · exact ambNu_lt_of_psum_lt Λ (Nat.card F) w s _ hplt
    · rcases hInit with hlex | ⟨heqi, hdrop⟩
      · have hiv := initVal_lex_lt (Nat.card F) w s hw _ hmw hlex
        exact ambNu_lt_of_initVal Λ (Nat.card F) w s _ hw hmw hpeq heq hiv
      · have hval_eq : initVal (Nat.card F) w
            (Q.c (Sum.inl (RelData.iterIdx F (k - j - 1) (toData F R0) i₀))) =
            initVal (Nat.card F) w s := by
          rw [initVal, initVal, heqi]
        exact ambNu_lt_of_entry Λ (Nat.card F) w s _ hpeq heq hval_eq hdrop

/-- ★ Ambient step for the type-2 members (depth strictly grows). -/
lemma type2_amb_step (r : ℕ) (s : Fin r → ℕ+) (k j : ℕ)
    (hk1 : 1 ≤ k) (hkr : k ≤ r) (hj1 : 1 ≤ j) (hjk : j ≤ k - 1)
    (hbig : (Nat.card F : ℕ) < (s ⟨k - 1, by omega⟩ : ℕ))
    (hsj : (s ⟨j - 1, by omega⟩ : ℕ) < Nat.card F)
    (hmid : ∀ i : Fin r, (j : ℕ) ≤ (i : ℕ) → (i : ℕ) < k - 1 → (s i : ℕ) = Nat.card F)
    (R0 : BinaryRel F)
    (hbhd : ∀ j' : R0.ιB, ((R0.cB j') ⟨0, R0.hdepB j'⟩ : ℕ) = 1) :
    let D := RelData.BCqIter F (k - j - 1) (toData F R0)
    let Bs := ofBstarOver F D (s ⟨j - 1, by omega⟩) (fun e => BCqIter_valid F (k - j - 1) R0 e)
        (RelData.iterate_merge_hv F (k - j - 1) R0 (s ⟨j - 1, by omega⟩) (by omega) hbhd)
    let Q := FixedOver.prependList F Bs (sPrefix r s j (by omega) (by omega))
    ∀ i : D.ιB,
      (∀ j' : R0.ιB, weight (R0.depB j' - 1) (expTail (R0.cB j')) =
          psum s r - psum s (k - 1) - 1) →
      (∀ j' : R0.ιB, ∀ mm : ℕ, psum (expTail (R0.cB j')) mm ≤ psumSeq (tupPadSum
          (single (qMinusExp F)) (consVec (w1Of F r s k hk1 hkr hbig) (sTail r s k hkr))) mm) →
      ∀ (w : ℕ), weight r s = w → ∀ (Λ : ℕ), k ≤ Λ →
        ambNu Λ (Nat.card F) w (Q.c (Sum.inr (Sum.inl i))) < ambNu Λ (Nat.card F) w s := by
  classical
  intro D Bs Q i hXw hbndB w hw Λ hΛ
  have hle := type2_psum_le_amb F r s k j hk1 hkr hj1 hjk hbig hsj hmid R0 hbhd
    i hXw hbndB Λ hΛ
  have hdep := type2_dep_gt F r s k j hk1 hkr hj1 hjk hbig hsj hmid R0 hbhd i hXw hbndB
  have hmw : weight (Q.dep (Sum.inr (Sum.inl i))) (Q.c (Sum.inr (Sum.inl i))) = w :=
    (type2_weight_eq F r s k j hk1 hkr hj1 hjk hbig hsj hmid R0 hbhd i hXw).trans hw
  have hmd_le : Q.dep (Sum.inr (Sum.inl i)) ≤ w := by
    rw [← hmw]
    exact weight_ge_depth _ _
  have hs_le : r ≤ w := by
    rw [← hw]
    exact weight_ge_depth r s
  exact ambNu_lt_of_depth_gt Λ (Nat.card F) w s _ hs_le hmd_le hdep hle

/-- ★ Ambient step for the type-3 members (`Init` strictly grows). -/
lemma type3_amb_step (r : ℕ) (s : Fin r → ℕ+) (k j : ℕ)
    (hk1 : 1 ≤ k) (hkr : k ≤ r) (hj1 : 1 ≤ j) (hjk : j ≤ k - 1)
    (hbig : (Nat.card F : ℕ) < (s ⟨k - 1, by omega⟩ : ℕ))
    (hsj : (s ⟨j - 1, by omega⟩ : ℕ) < Nat.card F)
    (hmid : ∀ i : Fin r, (j : ℕ) ≤ (i : ℕ) → (i : ℕ) < k - 1 → (s i : ℕ) = Nat.card F)
    (hsleq : ∀ x : ℕ, x < k - 1 → pad0 s x ≤ Nat.card F)
    (R0 : BinaryRel F)
    (hbhd : ∀ j' : R0.ιB, ((R0.cB j') ⟨0, R0.hdepB j'⟩ : ℕ) = 1) :
    let D := RelData.BCqIter F (k - j - 1) (toData F R0)
    let Bs := ofBstarOver F D (s ⟨j - 1, by omega⟩) (fun e => BCqIter_valid F (k - j - 1) R0 e)
        (RelData.iterate_merge_hv F (k - j - 1) R0 (s ⟨j - 1, by omega⟩) (by omega) hbhd)
    let Q := FixedOver.prependList F Bs (sPrefix r s j (by omega) (by omega))
    ∀ i : D.ιB,
      (∀ j' : R0.ιB, weight (R0.depB j' - 1) (expTail (R0.cB j')) =
          psum s r - psum s (k - 1) - 1) →
      (∀ j' : R0.ιB, ∀ mm : ℕ, psum (expTail (R0.cB j')) mm ≤ psumSeq (tupPadSum
          (single (qMinusExp F)) (consVec (w1Of F r s k hk1 hkr hbig) (sTail r s k hkr))) mm) →
      ∀ (w : ℕ), weight r s = w → ∀ (Λ : ℕ), k ≤ Λ →
        ambNu Λ (Nat.card F) w (Q.c (Sum.inr (Sum.inr i))) < ambNu Λ (Nat.card F) w s := by
  classical
  intro D Bs Q i hXw hbndB w hw Λ hΛ
  have hle := type3_psum_le_amb F r s k j hk1 hkr hj1 hjk hbig hsj hmid R0 hbhd
    i hXw hbndB Λ hΛ
  have hdep := type3_dep_ge F r s k j hk1 hkr hj1 hjk hbig hsj hmid R0 hbhd i hXw hbndB
  have hmw : weight (Q.dep (Sum.inr (Sum.inr i))) (Q.c (Sum.inr (Sum.inr i))) = w :=
    (type3_weight_eq F r s k j hk1 hkr hj1 hjk hbig hsj hmid R0 hbhd i hXw).trans hw
  have hmd_le : Q.dep (Sum.inr (Sum.inr i)) ≤ w := by
    rw [← hmw]
    exact weight_ge_depth _ _
  have hs_le : r ≤ w := by
    rw [← hw]
    exact weight_ge_depth r s
  rcases lt_or_eq_of_le hdep with hlt | heq
  · exact ambNu_lt_of_depth_gt Λ (Nat.card F) w s _ hs_le hmd_le hlt hle
  · rcases lt_or_eq_of_le hle with hplt | hpeq
    · exact ambNu_lt_of_psum_lt Λ (Nat.card F) w s _ hplt
    · have hlex := type3_Init_gt F r s k j hk1 hkr hj1 hjk hbig hsj hsleq R0 hbhd i
      have hiv := initVal_lex_lt (Nat.card F) w s hw _ hmw hlex
      exact ambNu_lt_of_initVal Λ (Nat.card F) w s _ hw hmw hpeq heq hiv

end ZagierHoffmanPositiveChar
