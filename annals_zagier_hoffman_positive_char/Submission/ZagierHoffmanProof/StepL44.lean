import Submission.ZagierHoffmanProof.StepL43

set_option autoImplicit false
set_option maxHeartbeats 100000000
open Polynomial RatFunc
open scoped BigOperators

/-!
# Step L44: prop213_step1 — the CASE-2 (Prop 2.13) Step-1 ∃-package

For a CASE-2 input `s : Fin k` (depth `k`, `s₁..s_{k−1} ≤ q` (`hsleq`), `s_k = q`,
`j` the last index with `s_j < q`, positions `j..k−1` all `q` (`hqend`)) the R1
chain (`D Bs Q`, R0 := r1Rel F, u := PUnit.unit) gives the ζ_A-level decomposition
`zeta_213`.  Since the R1 `a`-side is a singleton (`R0.ιA = PUnit`), the guarded
type-1 family of `zeta_213` is `0` (`type1_guard_zero_R1` via `sum_reindex_iterIdx`),
so the relation is
  ζ_A s + (type-2 sum) + (type-3 sum) = 0,
with per-member facts (mirroring `prop212_step1`'s T2/T3, no type-1 family):
  T2: type-2 members have weight `w(s)` and prefix-k STRICT < `psum s k`;
  T3: type-3 members have weight `w(s)`, prefix-k ≤ `psum s k`, and
      `InitLt q s u` (Init-growth — the Route-B termination engine).
This is the CASE-2 Step-1 input of the Prop-3.2 recursion.
-/

namespace ZagierHoffmanPositiveChar
attribute [instance] P2Data.fin
attribute [instance] RelData.finA
attribute [instance] RelData.finB
attribute [instance] FixedRel.fin
attribute [local instance] Classical.propDecidable
variable (F : Type*) [Field F] [Finite F] [DecidableEq (RatFunc F)]

/-- The guarded type-1 sum of `zeta_213` is `0`: the R1 `a`-side is a singleton
(`R0.ιA = PUnit`), so every guarded term is `0`. -/
lemma type1_guard_zero_R1 (k : ℕ) (s : Fin k → ℕ+) (j : ℕ)
    (hk1 : 1 ≤ k) (hj1 : 1 ≤ j) (hjk : j ≤ k - 1)
    (hsj : (s ⟨j - 1, by omega⟩ : ℕ) < Nat.card F) :
    let D := RelData.BCqIter F (k - j - 1) (toData F (r1Rel F))
    let Bs := ofBstarOver F D (s ⟨j - 1, by omega⟩) (fun e => BCqIter_valid F (k - j - 1) (r1Rel F) e)
        (RelData.iterate_merge_hv F (k - j - 1) (r1Rel F) (s ⟨j - 1, by omega⟩) (by omega) (r1Rel_hbhd F))
    let Q := FixedOver.prependList F Bs (sPrefix k s j (by omega) (by omega))
    let u' := RelData.iterIdx F (k - j - 1) (toData F (r1Rel F)) PUnit.unit
    (∑ i : D.ιA, (if i = u' then 0 else (Q.a (Sum.inl i) : RatFunc.CompletionAtInfty F) *
        ζ_A F (Q.c (Sum.inl i)))) = 0 := by
  classical
  intro D Bs Q u'
  have hsum := sum_reindex_iterIdx F (k - j - 1) (r1Rel F)
    (fam := fun i : D.ιA => if i = u' then 0 else (Q.a (Sum.inl i) : RatFunc.CompletionAtInfty F) *
      ζ_A F (Q.c (Sum.inl i)))
  rw [hsum]
  apply Finset.sum_eq_zero
  intro i₀ hi
  have hiu : RelData.iterIdx F (k - j - 1) (toData F (r1Rel F)) i₀ = u' := by
    cases i₀
    rfl
  simp [hiu]

/-- The ζ_A-level CASE-2 relation without the (zero) type-1 family:
`ζ_A s + (type-2 sum) + (type-3 sum) = 0`. -/
theorem zeta_213_no_type1 (k : ℕ) (s : Fin k → ℕ+) (j : ℕ)
    (hk1 : 1 ≤ k) (hj1 : 1 ≤ j) (hjk : j ≤ k - 1)
    (hsj : (s ⟨j - 1, by omega⟩ : ℕ) < Nat.card F)
    (hqend : ∀ i : Fin k, (j : ℕ) ≤ (i : ℕ) → (i : ℕ) < k → (s i : ℕ) = Nat.card F) :
    let D := RelData.BCqIter F (k - j - 1) (toData F (r1Rel F))
    let Bs := ofBstarOver F D (s ⟨j - 1, by omega⟩) (fun e => BCqIter_valid F (k - j - 1) (r1Rel F) e)
        (RelData.iterate_merge_hv F (k - j - 1) (r1Rel F) (s ⟨j - 1, by omega⟩) (by omega) (r1Rel_hbhd F))
    let Q := FixedOver.prependList F Bs (sPrefix k s j (by omega) (by omega))
    ζ_A F s +
      (∑ i : D.ιB, (Q.a (Sum.inr (Sum.inl i)) : RatFunc.CompletionAtInfty F) *
        ζ_A F (Q.c (Sum.inr (Sum.inl i)))) +
      (∑ i : D.ιB, (Q.a (Sum.inr (Sum.inr i)) : RatFunc.CompletionAtInfty F) *
        ζ_A F (Q.c (Sum.inr (Sum.inr i)))) = 0 := by
  classical
  intro D Bs Q
  have hz := zeta_213 F k s j hk1 hj1 hjk hsj hqend
  -- hz has its own lets D Bs Q u'; bring them to the same values
  let u' := RelData.iterIdx F (k - j - 1) (toData F (r1Rel F)) PUnit.unit
  have hT1 : (∑ i : D.ιA, (if i = u' then 0 else (Q.a (Sum.inl i) : RatFunc.CompletionAtInfty F) *
        ζ_A F (Q.c (Sum.inl i)))) = 0 := by
    dsimp [D, Bs, Q]
    exact type1_guard_zero_R1 F k s j hk1 hj1 hjk hsj
  have hz' : ζ_A F s +
      (∑ i : D.ιA, (if i = u' then 0 else (Q.a (Sum.inl i) : RatFunc.CompletionAtInfty F) *
        ζ_A F (Q.c (Sum.inl i)))) +
      (∑ i : D.ιB, (Q.a (Sum.inr (Sum.inl i)) : RatFunc.CompletionAtInfty F) *
        ζ_A F (Q.c (Sum.inr (Sum.inl i)))) +
      (∑ i : D.ιB, (Q.a (Sum.inr (Sum.inr i)) : RatFunc.CompletionAtInfty F) *
        ζ_A F (Q.c (Sum.inr (Sum.inr i)))) = 0 := by
    simpa [D, Bs, Q, u'] using hz
  rw [hT1] at hz'
  simpa using hz'

/-- ★ The CASE-2 Step-1 decomposition (Prop 2.13): the R1 chain at the R1 config
gives `ζ_A s + type-2 + type-3 = 0` with per-member weight/prefix-k/Init facts. -/
theorem prop213_step1 (k : ℕ) (s : Fin k → ℕ+) (j : ℕ)
    (hk1 : 1 ≤ k) (hj1 : 1 ≤ j) (hjk : j ≤ k - 1)
    (hsj : (s ⟨j - 1, by omega⟩ : ℕ) < Nat.card F)
    (hqend : ∀ i : Fin k, (j : ℕ) ≤ (i : ℕ) → (i : ℕ) < k → (s i : ℕ) = Nat.card F)
    (hsleq : ∀ x : ℕ, x < k - 1 → pad0 s x ≤ Nat.card F) :
    let D := RelData.BCqIter F (k - j - 1) (toData F (r1Rel F))
    let Bs := ofBstarOver F D (s ⟨j - 1, by omega⟩) (fun e => BCqIter_valid F (k - j - 1) (r1Rel F) e)
        (RelData.iterate_merge_hv F (k - j - 1) (r1Rel F) (s ⟨j - 1, by omega⟩) (by omega) (r1Rel_hbhd F))
    let Q := FixedOver.prependList F Bs (sPrefix k s j (by omega) (by omega))
    (ζ_A F s +
      (∑ i : D.ιB, (Q.a (Sum.inr (Sum.inl i)) : RatFunc.CompletionAtInfty F) *
        ζ_A F (Q.c (Sum.inr (Sum.inl i)))) +
      (∑ i : D.ιB, (Q.a (Sum.inr (Sum.inr i)) : RatFunc.CompletionAtInfty F) *
        ζ_A F (Q.c (Sum.inr (Sum.inr i)))) = 0) ∧
    (∀ i : D.ιB,
      weight (Q.dep (Sum.inr (Sum.inl i))) (Q.c (Sum.inr (Sum.inl i))) = weight k s ∧
      psum (Q.c (Sum.inr (Sum.inl i))) k < psum s k) ∧
    (∀ i : D.ιB,
      weight (Q.dep (Sum.inr (Sum.inr i))) (Q.c (Sum.inr (Sum.inr i))) = weight k s ∧
      psum (Q.c (Sum.inr (Sum.inr i))) k ≤ psum s k ∧
      InitLt (Nat.card F) s (Q.c (Sum.inr (Sum.inr i)))) := by
  classical
  intro D Bs Q
  constructor
  · exact zeta_213_no_type1 F k s j hk1 hj1 hjk hsj hqend
  · constructor
    · intro i
      constructor
      · exact type2_weight_eq_R1 F k s j hk1 hj1 hjk hsj hqend i
      · exact type2_psum_lt_k_R1 F k s j hk1 hj1 hjk hsj hqend i
    · intro i
      constructor
      · exact type3_weight_eq_R1 F k s j hk1 hj1 hjk hsj hqend i
      · constructor
        · exact type3_psum_k_le_R1 F k s j hk1 hj1 hjk hsj hqend i
        · exact type3_Init_gt_R1 F k s j hk1 hj1 hjk hsj hsleq i

end ZagierHoffmanPositiveChar
