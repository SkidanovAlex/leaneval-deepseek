import Submission.ZagierHoffmanProof.StepL162
import Submission.ZagierHoffmanProof.StepL48
set_option autoImplicit false
set_option maxHeartbeats 100000000
open Polynomial RatFunc
open scoped BigOperators
/-!
# Step L163: the AMBIENT prefix bound `psum member ℓ ≤ psum s ℓ` for all `ℓ ≥ k`
(SESSION 269) — the horder of the chains, extracted at an ARBITRARY ambient level

The committed splices prove the prefix order `psum m ℓ ≤ psum s ℓ` (`ℓ ≥ k`) only INSIDE
their bodies.  Route (C) needs it as a standalone interface, for the ambient level `Λ ≥ k`
of the recursion.  The proofs are the same as in the splices: the `ℓ ≤ r` regime via the
`ℓ`-parametrized order lemmas, the `ℓ > r` regime by saturation (`psum · ℓ = weight`).
theorem_B/D remain ABP-gated (no route).
-/

namespace ZagierHoffmanPositiveChar
attribute [instance] P2Data.fin
attribute [instance] RelData.finA
attribute [instance] RelData.finB
attribute [instance] FixedRel.fin
attribute [local instance] Classical.propDecidable
variable (F : Type*) [Field F] [Finite F] [DecidableEq (RatFunc F)]

/-- ★ Ambient order for the type-1 members. -/
lemma type1_psum_le_amb (r : ℕ) (s : Fin r → ℕ+) (k j : ℕ)
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
    ∀ i₀ : R0.ιA,
      (weight (R0.depA i₀) (R0.cA i₀) = psum s r - psum s (k - 1)) →
      (∀ m : ℕ, psum (R0.cA i₀) m ≤ psumSeq (tupPadSum (single (qExp F))
          (consVec (w1Of F r s k hk1 hkr hbig) (sTail r s k hkr))) m) →
      ∀ ℓ : ℕ, k ≤ ℓ → psum (Q.c (Sum.inl (RelData.iterIdx F (k - j - 1) (toData F R0) i₀))) ℓ
        ≤ psum s ℓ := by
  classical
  intro D Bs Q i₀ hwtA hpref ℓ hkℓ
  let i : D.ιA := RelData.iterIdx F (k - j - 1) (toData F R0) i₀
  by_cases hℓr : ℓ ≤ r
  · have hdec := type1_psum_decompose_ge F r s k j hk1 hkr hj1 hjk hbig hsj hmid R0 hbhd i₀ ℓ hkℓ
    have hm1 : 1 ≤ ℓ - k + 1 := by omega
    have hpre := hpref (ℓ - k + 1)
    have htel := lemma29_qExp_telescope F r s k hk1 hkr hbig (ℓ - k + 1) hm1
    have hidx : k + (ℓ - k + 1) - 1 = ℓ := by omega
    rw [hidx] at htel
    have hpk := psum_last_eq r s k hk1 hkr
    have hle : psum (R0.cA i₀) (ℓ - k + 1) ≤ (s ⟨k - 1, by omega⟩ : ℕ) +
        (psum s ℓ - psum s k) := le_trans hpre htel.le
    rw [hdec]
    have hle2 : psum s (k - 1) + psum (R0.cA i₀) (ℓ - k + 1) ≤
        psum s (k - 1) + ((s ⟨k - 1, by omega⟩ : ℕ) + (psum s ℓ - psum s k)) :=
      Nat.add_le_add_left hle _
    refine le_trans hle2 ?_
    have hks : psum s k ≤ psum s ℓ := psum_mono s hkℓ
    omega
  · have hge : r ≤ ℓ := by omega
    have hw := type1_weight_eq F r s k j hk1 hkr hj1 hjk hbig hsj hmid R0 hbhd i₀ hwtA
    calc psum (Q.c (Sum.inl i)) ℓ ≤ weight (Q.dep (Sum.inl i)) (Q.c (Sum.inl i)) :=
          psum_le_weight (Q.c (Sum.inl i)) ℓ
      _ = weight r s := hw
      _ = psum s ℓ := (psum_ge_depth s hge).symm

/-- ★ Ambient order for the type-2 members. -/
lemma type2_psum_le_amb (r : ℕ) (s : Fin r → ℕ+) (k j : ℕ)
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
      (∀ j' : R0.ιB, ∀ m : ℕ, psum (expTail (R0.cB j')) m ≤ psumSeq (tupPadSum
          (single (qMinusExp F)) (consVec (w1Of F r s k hk1 hkr hbig) (sTail r s k hkr))) m) →
      ∀ ℓ : ℕ, k ≤ ℓ → psum (Q.c (Sum.inr (Sum.inl i))) ℓ ≤ psum s ℓ := by
  classical
  intro D Bs Q i hXw hbndB ℓ hkℓ
  by_cases hℓr : ℓ ≤ r
  · by_cases hℓk : ℓ = k
    · rw [hℓk]
      exact le_of_lt (type2_psum_lt_k F r s k j hk1 hkr hj1 hjk hbig hsj hmid R0 hbhd i)
    · have hgt : k < ℓ := by omega
      exact le_of_lt (type2_psum_ge_k_lt F r s k j hk1 hkr hj1 hjk hbig hsj hmid R0 hbhd
        hbndB i ℓ hgt hℓr)
  · have hge : r ≤ ℓ := by omega
    have hw := type2_weight_eq F r s k j hk1 hkr hj1 hjk hbig hsj hmid R0 hbhd i hXw
    calc psum (Q.c (Sum.inr (Sum.inl i))) ℓ ≤
          weight (Q.dep (Sum.inr (Sum.inl i))) (Q.c (Sum.inr (Sum.inl i))) :=
          psum_le_weight (Q.c (Sum.inr (Sum.inl i))) ℓ
      _ = weight r s := hw
      _ = psum s ℓ := (psum_ge_depth s hge).symm

/-- ★ Ambient order for the type-3 members. -/
lemma type3_psum_le_amb (r : ℕ) (s : Fin r → ℕ+) (k j : ℕ)
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
      (∀ j' : R0.ιB, ∀ m : ℕ, psum (expTail (R0.cB j')) m ≤ psumSeq (tupPadSum
          (single (qMinusExp F)) (consVec (w1Of F r s k hk1 hkr hbig) (sTail r s k hkr))) m) →
      ∀ ℓ : ℕ, k ≤ ℓ → psum (Q.c (Sum.inr (Sum.inr i))) ℓ ≤ psum s ℓ := by
  classical
  intro D Bs Q i hXw hbndB ℓ hkℓ
  by_cases hℓr : ℓ ≤ r
  · exact type3_psum_ge_k_le F r s k j hk1 hkr hj1 hjk hbig hsj hmid R0 hbhd hbndB i ℓ hkℓ hℓr
  · have hge : r ≤ ℓ := by omega
    have hw := type3_weight_eq F r s k j hk1 hkr hj1 hjk hbig hsj hmid R0 hbhd i hXw
    calc psum (Q.c (Sum.inr (Sum.inr i))) ℓ ≤
          weight (Q.dep (Sum.inr (Sum.inr i))) (Q.c (Sum.inr (Sum.inr i))) :=
          psum_le_weight (Q.c (Sum.inr (Sum.inr i))) ℓ
      _ = weight r s := hw
      _ = psum s ℓ := (psum_ge_depth s hge).symm

end ZagierHoffmanPositiveChar
