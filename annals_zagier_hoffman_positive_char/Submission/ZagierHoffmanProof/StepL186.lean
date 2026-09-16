import Submission.ZagierHoffmanProof.StepL185
import Submission.ZagierHoffmanProof.StepL147

set_option autoImplicit false
set_option maxHeartbeats 40000000
open Polynomial RatFunc
open scoped BigOperators
set_option linter.unnecessarySimpa false
set_option linter.unusedSimpArgs false

/-!
# Step L186: ★★ `maink_case2_j_amb` — the CASE-2 (`prop213_step1`) splice at an AMBIENT level

The second ambient chain port: the `maink_case2_j` splice (StepL147) runs at its own level `k`
with `Λ`-admissible outputs and the AMBIENT `ambNu Λ` descent, supplied by StepL175's
`maink_case2_j_type2_amb_step` (strict prefix drop at `k` ⟹ `depth > k` ⟹ the depth component)
and `maink_case2_j_type3_amb_step` (depth `> k`, else equal depth with the chain's `InitLt`).
theorem_B/D remain ABP-gated (no route).
-/

namespace ZagierHoffmanPositiveChar
attribute [instance] P2Data.fin
attribute [instance] RelData.finA
attribute [instance] RelData.finB
attribute [instance] FixedRel.fin
attribute [local instance] Classical.propDecidable
variable (F : Type*) [Field F] [Finite F] [DecidableEq (RatFunc F)]

theorem maink_case2_j_amb (w : ℕ) (k : ℕ) (s : Fin k → ℕ+) (hw : weight k s = w)
    (hk1 : 1 ≤ k) (hk2 : 2 ≤ k) (j : ℕ) (hj1 : 1 ≤ j) (hjk : j ≤ k - 1)
    (hsj : (s ⟨j - 1, by omega⟩ : ℕ) < Nat.card F)
    (hqend : ∀ i : Fin k, (j : ℕ) ≤ (i : ℕ) → (i : ℕ) < k → (s i : ℕ) = Nat.card F)
    (hsleq : ∀ x : ℕ, x < k - 1 → pad0 s x ≤ Nat.card F)
    (Λ : ℕ) (hΛ : k ≤ Λ)
    (rec : ∀ (r' : ℕ) (m : Fin r' → ℕ+) (_hm : weight r' m = w),
      ambNu Λ (Nat.card F) w m < ambNu Λ (Nat.card F) w s →
        ¬ kAdmissible (Nat.card F) m Λ → AdmExpT F w Λ m) :
    AdmExpT F w Λ s := by
  classical
  rcases prop213_step1 F k s j hk1 hj1 hjk hsj hqend hsleq with ⟨hrel, hT2, hT3⟩
  let D : RelData F := RelData.BCqIter F (k - j - 1) (toData F (r1Rel F))
  let Bs : FixedOver F (D.ιA ⊕ (D.ιB ⊕ D.ιB)) :=
    ofBstarOver F D (s ⟨j - 1, by omega⟩) (fun e => BCqIter_valid F (k - j - 1) (r1Rel F) e)
      (RelData.iterate_merge_hv F (k - j - 1) (r1Rel F) (s ⟨j - 1, by omega⟩) (by omega)
        (r1Rel_hbhd F))
  let Q : FixedOver F (D.ιA ⊕ (D.ιB ⊕ D.ιB)) :=
    FixedOver.prependList F Bs (sPrefix k s j (by omega) (by omega))
  have hrel0 : ζ_A F s +
      (∑ i : D.ιB, (((Q.a (Sum.inr (Sum.inl i)) : RatFunc F) : RatFunc.CompletionAtInfty F) *
        ζ_A F (Q.c (Sum.inr (Sum.inl i))))) +
      (∑ i : D.ιB, (((Q.a (Sum.inr (Sum.inr i)) : RatFunc F) : RatFunc.CompletionAtInfty F) *
        ζ_A F (Q.c (Sum.inr (Sum.inr i))))) = 0 := by
    exact hrel
  -- the two-family fold
  let ι : Type := D.ιB ⊕ D.ιB
  let mdep (p : ι) : ℕ := match p with
    | Sum.inl i => Q.dep (Sum.inr (Sum.inl i))
    | Sum.inr i => Q.dep (Sum.inr (Sum.inr i))
  let mhdep (p : ι) : 0 < mdep p := by
    dsimp [mdep]
    cases p with
    | inl i => exact Q.hdep (Sum.inr (Sum.inl i))
    | inr i => exact Q.hdep (Sum.inr (Sum.inr i))
  let mc (p : ι) : Fin (mdep p) → ℕ+ := match p with
    | Sum.inl i => Q.c (Sum.inr (Sum.inl i))
    | Sum.inr i => Q.c (Sum.inr (Sum.inr i))
  let ma (p : ι) : RatFunc F := match p with
    | Sum.inl i => -(Q.a (Sum.inr (Sum.inl i)))
    | Sum.inr i => -(Q.a (Sum.inr (Sum.inr i)))
  let x₂ (i : D.ιB) : RatFunc.CompletionAtInfty F :=
    (((Q.a (Sum.inr (Sum.inl i)) : RatFunc F) : RatFunc.CompletionAtInfty F) *
      ζ_A F (Q.c (Sum.inr (Sum.inl i))))
  let x₃ (i : D.ιB) : RatFunc.CompletionAtInfty F :=
    (((Q.a (Sum.inr (Sum.inr i)) : RatFunc F) : RatFunc.CompletionAtInfty F) *
      ζ_A F (Q.c (Sum.inr (Sum.inr i))))
  have hrel' : ζ_A F s + (∑ i : D.ιB, x₂ i) + (∑ i : D.ιB, x₃ i) = 0 := by
    simpa [x₂, x₃] using hrel0
  have hid3 : ζ_A F s = -(∑ i : D.ιB, x₂ i) + -(∑ i : D.ιB, x₃ i) := by
    have h' : ζ_A F s + ((∑ i : D.ιB, x₂ i) + (∑ i : D.ιB, x₃ i)) = 0 := by
      simpa [add_assoc] using hrel'
    have hz : ζ_A F s = -((∑ i : D.ιB, x₂ i) + (∑ i : D.ιB, x₃ i)) :=
      eq_neg_of_add_eq_zero_left h'
    rw [hz]
    abel
  have hid : ζ_A F s = ∑ p : ι,
      (((ma p : RatFunc F) : RatFunc.CompletionAtInfty F) * ζ_A F (mc p)) := by
    calc
      ζ_A F s = ∑ p : ι, (match p with
            | Sum.inl i => -(x₂ i) | Sum.inr i => -(x₃ i)) := by
        rw [hid3, Fintype.sum_sum_type]
        simp [Finset.sum_neg_distrib]
      _ = ∑ p : ι, (((ma p : RatFunc F) : RatFunc.CompletionAtInfty F) * ζ_A F (mc p)) := by
        apply Finset.sum_congr rfl
        intro p hp
        cases p with
        | inl i =>
            dsimp [x₂, ma, mc]
            exact (neg_coe_mul_zeta F (Q.a (Sum.inr (Sum.inl i))) (Q.c (Sum.inr (Sum.inl i)))).symm
        | inr i =>
            dsimp [x₃, ma, mc]
            exact (neg_coe_mul_zeta F (Q.a (Sum.inr (Sum.inr i))) (Q.c (Sum.inr (Sum.inr i)))).symm
  -- order: trivial (s saturates at depth k)
  have horder : ∀ p : ι, ∀ ℓ : ℕ, Λ ≤ ℓ → psum (mc p) ℓ ≤ psum s ℓ := by
    intro p ℓ hℓ
    have hkℓ : k ≤ ℓ := le_trans hΛ hℓ
    rw [psum_ge_depth s hkℓ]
    calc
      psum (mc p) ℓ ≤ weight (mdep p) (mc p) := psum_le_weight (mc p) ℓ
      _ = w := by
            cases p with
            | inl i => rw [(hT2 i).1]; exact hw
            | inr i => rw [(hT3 i).1]; exact hw
      _ = weight k s := hw.symm
  -- per-member expansion
  have e : ∀ p : ι, AdmExpT F w Λ (mc p) := by
    intro p
    cases p with
    | inl i =>
        have hwv : weight (mdep (Sum.inl i)) (mc (Sum.inl i)) = w := by
          dsimp [mdep, mc]
          rw [(hT2 i).1]
          exact hw
        by_cases hkadm : kAdmissible (Nat.card F) (mc (Sum.inl i)) Λ
        · exact admExpT_self F w Λ (mhdep (Sum.inl i)) (mc (Sum.inl i)) hwv hkadm
        · refine rec (mdep (Sum.inl i)) (mc (Sum.inl i)) hwv ?_ hkadm
          dsimp only [mdep, mc]
          exact maink_case2_j_type2_amb_step F w k s hw j hk1 hj1 hjk hsj hqend hsleq i Λ hΛ
    | inr i =>
        have hwv : weight (mdep (Sum.inr i)) (mc (Sum.inr i)) = w := by
          dsimp [mdep, mc]
          rw [(hT3 i).1]
          exact hw
        by_cases hkadm : kAdmissible (Nat.card F) (mc (Sum.inr i)) Λ
        · exact admExpT_self F w Λ (mhdep (Sum.inr i)) (mc (Sum.inr i)) hwv hkadm
        · refine rec (mdep (Sum.inr i)) (mc (Sum.inr i)) hwv ?_ hkadm
          dsimp only [mdep, mc]
          exact maink_case2_j_type3_amb_step F w k s hw j hk1 hj1 hjk hsj hqend hsleq i Λ hΛ
  exact admExpT_combine F w Λ s mdep mhdep mc ma hid horder e

end ZagierHoffmanPositiveChar
