import Submission.ZagierHoffmanProof.StepL132
import Submission.ZagierHoffmanProof.StepL165
set_option autoImplicit false
set_option maxHeartbeats 8000000
open Polynomial RatFunc
open scoped BigOperators
/-!
# Step L166: ★★ `maink_case1_splice_amb` — the GENERIC CASE-1 (k, j) splice at an
AMBIENT level (SESSION 269)

The port of StepL133's splice to route (C): the chain runs at its own in-domain level `k`
on the input `s` (same ζ-identity `zeta_214_reindexed`, same three-family fold, same member
list/coefficients), but the OUTPUTS are required to be `Λ`-admissible (the AMBIENT level
`Λ ≥ k`) and the recursion hypothesis `rec` receives the AMBIENT measure descent
`ambNu Λ q w m < ambNu Λ q w s` (produced by `StepL165`'s three ambient step lemmas) instead
of the chain-level `MainkStep3`.
theorem_B/D remain ABP-gated (no route).
-/

namespace ZagierHoffmanPositiveChar
attribute [local instance] Classical.propDecidable
variable (F : Type*) [Field F] [Finite F] [DecidableEq (RatFunc F)]

theorem maink_case1_splice_amb (w : ℕ) (r : ℕ) (s : Fin r → ℕ+) (hw : weight r s = w)
    (k j : ℕ) (hk1 : 1 ≤ k) (hkr : k ≤ r) (hj1 : 1 ≤ j) (hjk : j ≤ k - 1)
    (hbig : (Nat.card F : ℕ) < (s ⟨k - 1, by omega⟩ : ℕ))
    (hsj : (s ⟨j - 1, by omega⟩ : ℕ) < Nat.card F)
    (hmid : ∀ i : Fin r, (j : ℕ) ≤ (i : ℕ) → (i : ℕ) < k - 1 → (s i : ℕ) = Nat.card F)
    (hsleq : ∀ x : ℕ, x < k - 1 → pad0 s x ≤ Nat.card F)
    (R0 : BinaryRel F) (u : R0.ιA)
    (hdepu : R0.depA u = (r - k) + 1)
    (hau : R0.aA u = 1)
    (hc0 : ∀ hd : R0.depA u = (r - k) + 1,
        (fun x : Fin ((r - k) + 1) => R0.cA u (Fin.cast hd.symm x)) =
          bstarBase F r s k hk1 hkr hbig)
    (hbhd : ∀ j' : R0.ιB, ((R0.cB j') ⟨0, R0.hdepB j'⟩ : ℕ) = 1)
    (hwtA : ∀ i : R0.ιA, i ≠ u →
      weight (R0.depA i) (R0.cA i) = psum s r - psum s (k - 1))
    (hhead : ∀ i₀ : R0.ιA, i₀ ≠ u →
      ((R0.cA i₀) ⟨0, R0.hdepA i₀⟩ : ℕ) < (s ⟨k - 1, by omega⟩ : ℕ))
    (hXw : ∀ j' : R0.ιB,
      weight (R0.depB j' - 1) (expTail (R0.cB j')) = psum s r - psum s (k - 1) - 1)
    (hbndB : ∀ j' : R0.ιB, ∀ m : ℕ,
      psum (expTail (R0.cB j')) m ≤ psumSeq (tupPadSum (single (qMinusExp F))
        (consVec (w1Of F r s k hk1 hkr hbig) (sTail r s k hkr))) m)
    (hpref : ∀ i : R0.ιA, i ≠ u → ∀ m : ℕ,
      psum (R0.cA i) m ≤ psumSeq (tupPadSum (single (qExp F))
        (consVec (w1Of F r s k hk1 hkr hbig) (sTail r s k hkr))) m)
    (Λ : ℕ) (hΛ : k ≤ Λ)
    (rec : ∀ (r' : ℕ) (m : Fin r' → ℕ+) (_hm : weight r' m = w),
      ambNu Λ (Nat.card F) w m < ambNu Λ (Nat.card F) w s → ¬ kAdmissible (Nat.card F) m Λ →
      AdmExpT F w Λ m) :
    AdmExpT F w Λ s := by
  classical
  have hid0 := zeta_214_reindexed F r s k j hk1 hkr hj1 hjk hbig hsj hmid R0 u hau hdepu hc0 hbhd
  let D := RelData.BCqIter F (k - j - 1) (toData F R0)
  let Bs := ofBstarOver F D (s ⟨j - 1, by omega⟩) (fun e => BCqIter_valid F (k - j - 1) R0 e)
      (RelData.iterate_merge_hv F (k - j - 1) R0 (s ⟨j - 1, by omega⟩) (by omega) hbhd)
  let Q := FixedOver.prependList F Bs (sPrefix r s j (by omega) (by omega))
  let ι₁ : Type := {i₀ : R0.ιA // i₀ ≠ u}
  let ι₂ : Type := D.ιB
  let ι₃ : Type := D.ιB
  let ι : Type := ι₁ ⊕ (ι₂ ⊕ ι₃)
  let inst₁ : Fintype ι₁ :=
    Fintype.subtype ((Finset.univ : Finset R0.ιA).filter (fun i₀ => i₀ ≠ u))
      (by intro x; simp [Finset.mem_filter])
  letI : Fintype ι₁ := inst₁
  let mdep (p : ι) : ℕ := match p with
    | Sum.inl q => Q.dep (Sum.inl (RelData.iterIdx F (k - j - 1) (toData F R0) q.1))
    | Sum.inr (Sum.inl i) => Q.dep (Sum.inr (Sum.inl i))
    | Sum.inr (Sum.inr i) => Q.dep (Sum.inr (Sum.inr i))
  let mhdep (p : ι) : 0 < mdep p := by
    dsimp [mdep]
    cases p with
    | inl q => exact Q.hdep (Sum.inl (RelData.iterIdx F (k - j - 1) (toData F R0) q.1))
    | inr s => cases s with
      | inl i => exact Q.hdep (Sum.inr (Sum.inl i))
      | inr i => exact Q.hdep (Sum.inr (Sum.inr i))
  let mc (p : ι) : Fin (mdep p) → ℕ+ := match p with
    | Sum.inl q => Q.c (Sum.inl (RelData.iterIdx F (k - j - 1) (toData F R0) q.1))
    | Sum.inr (Sum.inl i) => Q.c (Sum.inr (Sum.inl i))
    | Sum.inr (Sum.inr i) => Q.c (Sum.inr (Sum.inr i))
  let ma (p : ι) : RatFunc F := match p with
    | Sum.inl q => -(Q.a (Sum.inl (RelData.iterIdx F (k - j - 1) (toData F R0) q.1)))
    | Sum.inr (Sum.inl i) => -(Q.a (Sum.inr (Sum.inl i)))
    | Sum.inr (Sum.inr i) => -(Q.a (Sum.inr (Sum.inr i)))
  let A : RatFunc.CompletionAtInfty F :=
    ∑ i₀ : R0.ιA, (if i₀ = u then 0 else
      (((Q.a (Sum.inl (RelData.iterIdx F (k - j - 1) (toData F R0) i₀)) : RatFunc F) : RatFunc.CompletionAtInfty F) *
        ζ_A F (Q.c (Sum.inl (RelData.iterIdx F (k - j - 1) (toData F R0) i₀)))))
  let B : RatFunc.CompletionAtInfty F :=
    ∑ i : D.ιB, (((Q.a (Sum.inr (Sum.inl i)) : RatFunc F) : RatFunc.CompletionAtInfty F) *
      ζ_A F (Q.c (Sum.inr (Sum.inl i))))
  let C : RatFunc.CompletionAtInfty F :=
    ∑ i : D.ιB, (((Q.a (Sum.inr (Sum.inr i)) : RatFunc F) : RatFunc.CompletionAtInfty F) *
      ζ_A F (Q.c (Sum.inr (Sum.inr i))))
  have hrel' : ζ_A F s + A + B + C = 0 := by
    dsimp [A, B, C, Q, Bs, D]
    exact hid0
  have hid3 : ζ_A F s = -A + -B + -C := eq_neg_add_add_add' (ζ_A F s) A B C hrel'
  let x₁ (p : ι₁) : RatFunc.CompletionAtInfty F :=
    (((Q.a (Sum.inl (RelData.iterIdx F (k - j - 1) (toData F R0) p.1)) : RatFunc F) : RatFunc.CompletionAtInfty F) *
      ζ_A F (Q.c (Sum.inl (RelData.iterIdx F (k - j - 1) (toData F R0) p.1))))
  let x₂ (i : ι₂) : RatFunc.CompletionAtInfty F :=
    (((Q.a (Sum.inr (Sum.inl i)) : RatFunc F) : RatFunc.CompletionAtInfty F) * ζ_A F (Q.c (Sum.inr (Sum.inl i))))
  let x₃ (i : ι₃) : RatFunc.CompletionAtInfty F :=
    (((Q.a (Sum.inr (Sum.inr i)) : RatFunc F) : RatFunc.CompletionAtInfty F) * ζ_A F (Q.c (Sum.inr (Sum.inr i))))
  have hA : A = ∑ p : ι₁, x₁ p := by
    dsimp [A, x₁]
    exact sum_guarded_subtype' (u := u)
      (f := fun i₀ : R0.ιA => (((Q.a (Sum.inl (RelData.iterIdx F (k - j - 1) (toData F R0) i₀)) : RatFunc F) : RatFunc.CompletionAtInfty F) *
        ζ_A F (Q.c (Sum.inl (RelData.iterIdx F (k - j - 1) (toData F R0) i₀)))))
  rw [hA] at hid3
  have hid3' : ζ_A F s = ∑ p : ι,
      (match p with
       | Sum.inl q => -(x₁ q)
       | Sum.inr (Sum.inl i) => -(x₂ i)
       | Sum.inr (Sum.inr i) => -(x₃ i)) := by
    calc
      ζ_A F s = -(∑ p : ι₁, x₁ p) + -(∑ i : ι₂, x₂ i) + -(∑ i : ι₃, x₃ i) := by
        simpa [x₂, x₃] using hid3
      _ = ∑ p : ι, (match p with
           | Sum.inl q => -(x₁ q)
           | Sum.inr (Sum.inl i) => -(x₂ i)
           | Sum.inr (Sum.inr i) => -(x₃ i)) := by
        exact neg_sum_sum_type' x₁ x₂ x₃
  have hid : ζ_A F s = ∑ p : ι, (((ma p : RatFunc F) : RatFunc.CompletionAtInfty F) * ζ_A F (mc p)) := by
    rw [hid3']
    apply Finset.sum_congr rfl
    intro p hp
    cases p with
    | inl q =>
        dsimp [x₁, ma, mc]
        exact (neg_coe_mul_zeta F (Q.a (Sum.inl (RelData.iterIdx F (k - j - 1) (toData F R0) q.1)))
          (Q.c (Sum.inl (RelData.iterIdx F (k - j - 1) (toData F R0) q.1)))).symm
    | inr s =>
        cases s with
        | inl i =>
            dsimp [x₂, ma, mc]
            exact (neg_coe_mul_zeta F (Q.a (Sum.inr (Sum.inl i))) (Q.c (Sum.inr (Sum.inl i)))).symm
        | inr i =>
            dsimp [x₃, ma, mc]
            exact (neg_coe_mul_zeta F (Q.a (Sum.inr (Sum.inr i))) (Q.c (Sum.inr (Sum.inr i)))).symm
  -- the per-member extension at the AMBIENT level Λ
  have e : ∀ p : ι, AdmExpT F w Λ (mc p) := by
    intro p
    have hmdp : 0 < mdep p := mhdep p
    have hmw : weight (mdep p) (mc p) = w := by
      cases p with
      | inl q =>
          exact (type1_weight_eq F r s k j hk1 hkr hj1 hjk hbig hsj hmid R0 hbhd q.1
            (hwtA q.1 q.2)).trans hw
      | inr s' => cases s' with
        | inl i =>
            exact (type2_weight_eq F r s k j hk1 hkr hj1 hjk hbig hsj hmid R0 hbhd i hXw).trans hw
        | inr i =>
            exact (type3_weight_eq F r s k j hk1 hkr hj1 hjk hbig hsj hmid R0 hbhd i hXw).trans hw
    by_cases hkadm : kAdmissible (Nat.card F) (mc p) Λ
    · exact admExpT_self F w Λ (mhdep p) (mc p) hmw hkadm
    · refine rec (mdep p) (mc p) hmw ?_ hkadm
      cases p with
      | inl q =>
          exact type1_amb_step F r s k j hk1 hkr hj1 hjk hbig hsj hmid hsleq R0 hbhd q.1
            (hwtA q.1 q.2) (hpref q.1 q.2) (hhead q.1 q.2) w hw Λ hΛ
      | inr s' => cases s' with
        | inl i =>
            exact type2_amb_step F r s k j hk1 hkr hj1 hjk hbig hsj hmid R0 hbhd i hXw hbndB
              w hw Λ hΛ
        | inr i =>
            exact type3_amb_step F r s k j hk1 hkr hj1 hjk hbig hsj hmid hsleq R0 hbhd i hXw hbndB
              w hw Λ hΛ
  -- the per-member orders at the ambient level `Λ` (`StepL163`'s ambient horder)
  have horder : ∀ p : ι, ∀ ℓ : ℕ, Λ ≤ ℓ → psum (mc p) ℓ ≤ psum s ℓ := by
    intro p ℓ hℓ
    have hkℓ : k ≤ ℓ := le_trans hΛ hℓ
    cases p with
    | inl q =>
        exact type1_psum_le_amb F r s k j hk1 hkr hj1 hjk hbig hsj hmid R0 hbhd q.1
          (hwtA q.1 q.2) (hpref q.1 q.2) ℓ hkℓ
    | inr s' => cases s' with
      | inl i =>
          exact type2_psum_le_amb F r s k j hk1 hkr hj1 hjk hbig hsj hmid R0 hbhd i hXw hbndB ℓ hkℓ
      | inr i =>
          exact type3_psum_le_amb F r s k j hk1 hkr hj1 hjk hbig hsj hmid R0 hbhd i hXw hbndB ℓ hkℓ
  exact admExpT_combine F w Λ s mdep mhdep mc ma hid horder e

end ZagierHoffmanPositiveChar
