import Submission.ZagierHoffmanProof.ATFormula
import Submission.ZagierHoffmanProof.DescentGen

set_option autoImplicit false
set_option maxHeartbeats 2000000

open Polynomial
open scoped BigOperators

/-!
# The Anderson–Thakur interpolation identity and Chen's key claim

This file proves the algebraic heart of Chen's Theorem 3.1 (the explicit Anderson–Thakur formula,
arXiv:1506.06463, *mainproposition*):

* `atInterp` — the **interpolation identity** `∑_{i ≤ k} θ^(j q^i)/(D_i L_{k-i}^(q^i)) = δ_{j,k}`
  for `j ≤ k`, transported from the one-variable form (`atPsi_eq_atPsiClosed`, `atPsi_X_pow`,
  `atPsi_eq_zero_of_lt_degree`) to the two-variable field `atQ F = F(θ,t)` along the field
  homomorphism `atEval : F(θ) → F(θ,t)`, `θ ↦ θ`;
* `atClaim'`/`atClaim` — **Chen's key claim**: with `P_k = ∏_{j ≤ k}(θ - t^(q^j))`,
  `L_k = ∏_{j ≤ k}(θ - θ^(q^j))`, `γ_i` the Anderson–Thakur numerators and `D_i` the Carlitz
  factorials,
  `1 - ∑_{i=1}^{M-1} (γ_i/D_i) (1/L_{M-1-i}^(q^i)) P_{M-1-i}^(q^i) = P_{M-1}/L_{M-1}`.
-/

namespace ZagierHoffmanPositiveChar



variable (F : Type*) [Field F] [Finite F]

/-- `L_k` evaluated at `θ`, as an element of the two-variable field. -/
noncomputable def atL (k : ℕ) : atQ F :=
  algebraMap ((F[X])[X]) (atQ F) (Polynomial.C (carlitzL F k))

/-- `P_k = ∏_{j=1}^{k} (θ - t ^ (q^j))`. -/
noncomputable def atPk (k : ℕ) : atQ F :=
  ∏ j ∈ Finset.Icc 1 k, ((atTheta F) - (atT F) ^ (Nat.card F ^ j))

/-- The ring hom `F[X] → F(θ,t)` sending `X` to `θ`. -/
noncomputable def atCX : F[X] →+* atQ F :=
  (algebraMap ((F[X])[X]) (atQ F)).comp (Polynomial.C)

lemma atCX_injective : Function.Injective (atCX F) := by
  intro p q h
  have h1 : (Polynomial.C p : (F[X])[X]) = Polynomial.C q := by
    apply (IsFractionRing.injective ((F[X])[X]) (atQ F)) h
  exact Polynomial.C_injective h1

lemma atCX_apply (p : F[X]) : atCX F p = algebraMap ((F[X])[X]) (atQ F) (Polynomial.C p) := rfl

lemma atCX_X : atCX F Polynomial.X = atTheta F := rfl

lemma atCX_fact (i : ℕ) : atCX F (carlitzFact F i) = atD F i := rfl

lemma atCX_L (i : ℕ) : atCX F (carlitzL F i) = atL F i := rfl

/-- The field hom `F(θ) → F(θ,t)` sending `θ` to `θ`. -/
noncomputable def atEval : RatFunc F →+* atQ F :=
  IsFractionRing.lift (g := atCX F) (atCX_injective F)

lemma atEval_algebraMap (p : F[X]) :
    atEval F (algebraMap F[X] (RatFunc F) p) = atCX F p :=
  IsFractionRing.lift_algebraMap (g := atCX F) (atCX_injective F) p

lemma atEval_carlitzTheta : atEval F (carlitzTheta F) = atTheta F := by
  rw [show carlitzTheta F = algebraMap F[X] (RatFunc F) Polynomial.X from rfl, atEval_algebraMap, atCX_X]

lemma atEval_atDen (k i : ℕ) :
    atEval F (atDen F k i) = atD F i * (atL F (k - i)) ^ (Nat.card F ^ i) := by
  rw [atDen]
  simp only [map_mul, map_pow]
  rw [show ((carlitzFact F i : F[X]) : RatFunc F) = algebraMap F[X] (RatFunc F) (carlitzFact F i) from rfl,
    show ((carlitzL F (k - i) : F[X]) : RatFunc F) = algebraMap F[X] (RatFunc F) (carlitzL F (k - i)) from rfl,
    atEval_algebraMap, atEval_algebraMap, atCX_fact, atCX_L]

lemma atEval_RatFunc_X : atEval F (RatFunc.X : RatFunc F) = atTheta F := by
  rw [← RatFunc.algebraMap_X (K := F), atEval_algebraMap, atCX_X]

lemma atPsi_X_pow_eq (k j : ℕ) (hj : j ≤ k) :
    atPsi F k (Polynomial.X ^ j) = if j = k then 1 else 0 := by
  rcases lt_or_eq_of_le hj with h | h
  · rw [if_neg (h.ne), atPsi_eq_zero_of_lt_degree F k _ (by rw [Polynomial.natDegree_X_pow]; exact h)]
  · rw [h, if_pos rfl]; exact atPsi_X_pow F k

lemma atInterp_rat (k j : ℕ) (hj : j ≤ k) :
    (∑ i ∈ Finset.range (k+1), (RatFunc.X : RatFunc F) ^ (j * Nat.card F ^ i) * (atDen F k i)⁻¹)
      = if j = k then 1 else 0 := by
  rw [← atPsi_X_pow_eq F k j hj, atPsi_eq_atPsiClosed, atPsiClosed]
  refine Finset.sum_congr rfl (fun i hi => ?_)
  have h0 : (Polynomial.aeval ((carlitzTheta F) ^ (Nat.card F ^ i)) (Polynomial.X ^ j : F[X]))
      = (carlitzTheta F) ^ (j * Nat.card F ^ i) := by
    rw [Polynomial.aeval_X_pow]
    rw [← pow_mul]
    exact congrArg (fun t => (carlitzTheta F) ^ t) (Nat.mul_comm (Nat.card F ^ i) j)
  rw [h0]
  have hc : carlitzTheta F = (RatFunc.X : RatFunc F) := by
    rw [show carlitzTheta F = algebraMap F[X] (RatFunc F) Polynomial.X from rfl,
      RatFunc.algebraMap_X (K := F)]
  rw [hc]

/-- ★ **The Anderson–Thakur interpolation identity**, in the two-variable field:
`∑_{i ≤ k} θ^(j q^i) / (D_i * L_{k-i}^(q^i)) = δ_{j,k}` for `j ≤ k`. -/
theorem atInterp (k j : ℕ) (hj : j ≤ k) :
    (∑ i ∈ Finset.range (k+1), (atTheta F) ^ (j * Nat.card F ^ i)
        * (atD F i * (atL F (k - i)) ^ (Nat.card F ^ i))⁻¹) = if j = k then 1 else 0 := by
  have h := congrArg (atEval F) (atInterp_rat F k j hj)
  simp only [map_sum, map_mul, map_pow, map_inv₀, atEval_RatFunc_X, atEval_atDen] at h
  by_cases hjk : j = k
  · rw [if_pos hjk, map_one] at h; rw [if_pos hjk]; exact h
  · rw [if_neg hjk, map_zero] at h; rw [if_neg hjk]; exact h


variable (F : Type*) [Field F] [Finite F]


lemma atPk_pow (k i : ℕ) :
    (atPk F k) ^ (Nat.card F ^ i)
      = ∏ j ∈ Finset.Icc 1 k,
          ((atTheta F)^(Nat.card F ^ i) - (atT F)^(Nat.card F ^ (i+j))) := by
  rw [atPk, ← Finset.prod_pow]
  refine Finset.prod_congr rfl (fun j hj => ?_)
  rw [sub_pow_card_pow F]
  congr 1
  rw [← pow_mul, ← pow_add]
  have hcomm : Nat.card F ^ (j + i) = Nat.card F ^ (i + j) := by rw [Nat.add_comm]
  rw [hcomm]

lemma prod_Icc_mul_shift (M i : ℕ) (hi : i ≤ M - 1) (f : ℕ → atQ F) :
    (∏ ℓ ∈ Finset.Icc 1 i, f ℓ) * (∏ j ∈ Finset.Icc 1 (M - 1 - i), f (i + j))
      = ∏ s ∈ Finset.Icc 1 (M - 1), f s := by
  have h1 : (∏ ℓ ∈ Finset.Icc 1 i, f ℓ) = ∏ j ∈ Finset.range i, f (1 + j) := by
    rw [← Finset.Ico_succ_right_eq_Icc, Finset.prod_Ico_eq_prod_range]
    simp
  have h2 : (∏ j ∈ Finset.Icc 1 (M - 1 - i), f (i + j))
      = ∏ j ∈ Finset.range (M - 1 - i), f (i + (1 + j)) := by
    rw [← Finset.Ico_succ_right_eq_Icc, Finset.prod_Ico_eq_prod_range]
    simp
  have h3 : (∏ s ∈ Finset.Icc 1 (M - 1), f s) = ∏ j ∈ Finset.range (M - 1), f (1 + j) := by
    rw [← Finset.Ico_succ_right_eq_Icc, Finset.prod_Ico_eq_prod_range]
    simp
  rw [h1, h2, h3]
  conv_rhs => rw [show M - 1 = i + (M - 1 - i) from by omega, Finset.prod_range_add]
  congr 1
  refine Finset.prod_congr rfl (fun j hj => ?_)
  congr 1
  omega

lemma atGamma_mul_atPk (M i : ℕ) (hi : i ≤ M - 1) :
    atGamma F i * (atPk F (M - 1 - i)) ^ (Nat.card F ^ i)
      = ∏ s ∈ Finset.Icc 1 (M - 1),
          ((atTheta F) ^ (Nat.card F ^ i) - (atT F) ^ (Nat.card F ^ s)) := by
  rw [atGamma, atPk_pow F (M - 1 - i) i]
  exact prod_Icc_mul_shift F M i hi
    (fun s => (atTheta F) ^ (Nat.card F ^ i) - (atT F) ^ (Nat.card F ^ s))

lemma atD_zero : atD F 0 = 1 := by
  rw [atD, carlitzFact_zero]
  simp

lemma atL_zero : atL F 0 = 1 := by
  rw [atL, carlitzL_zero]
  simp

lemma sum_mul_prod_sub {ι : Type*} [DecidableEq ι] (S : Finset ι) (A B C : ι → atQ F) :
    ∑ i ∈ S, A i * ∏ s ∈ S, (B i - C s)
      = ∑ t ∈ S.powerset, (-1) ^ t.card * (∏ s ∈ t, C s) *
          (∑ i ∈ S, A i * (B i) ^ (S.card - t.card)) := by
  have hterm : ∀ i ∈ S, A i * ∏ s ∈ S, (B i - C s)
      = ∑ t ∈ S.powerset, (-1) ^ t.card * (B i) ^ (S.card - t.card) * (∏ s ∈ t, C s) * A i := by
    intro i _
    rw [Finset.prod_sub (f := fun _ : ι => B i) (g := C) (s := S), Finset.mul_sum]
    refine Finset.sum_congr rfl (fun t ht => ?_)
    rw [Finset.prod_const, Finset.card_sdiff_of_subset (Finset.mem_powerset.mp ht)]
    ring
  rw [Finset.sum_congr rfl hterm, Finset.sum_comm]
  refine Finset.sum_congr rfl (fun t ht => ?_)
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun i hi => ?_)
  ring

/-- The reverse expansion: `∏ (a - C s) = ∑_{t} (-1)^#t (∏_{s∈t} C s) a^(#S - #t)`. -/
lemma prod_sub_rev {ι : Type*} [DecidableEq ι] (S : Finset ι) (C : ι → atQ F) (a : atQ F) :
    ∏ s ∈ S, (a - C s)
      = ∑ t ∈ S.powerset, (-1) ^ t.card * (∏ s ∈ t, C s) * a ^ (S.card - t.card) := by
  rw [Finset.prod_sub (f := fun _ : ι => a) (g := C) (s := S)]
  refine Finset.sum_congr rfl (fun t ht => ?_)
  rw [Finset.prod_const, Finset.card_sdiff_of_subset (Finset.mem_powerset.mp ht)]
  ring




lemma atS_eq_erase (M : ℕ) :
    Finset.Icc 1 (M - 1) = (Finset.range M).erase 0 := by
  ext x
  simp only [Finset.mem_Icc, Finset.mem_erase, Finset.mem_range]
  omega

lemma atS_card (M : ℕ) : (Finset.Icc 1 (M - 1)).card = M - 1 := by
  rw [atS_eq_erase]
  rcases Nat.eq_zero_or_pos M with h | h
  · simp [h]
  · rw [Finset.card_erase_of_mem (Finset.mem_range.mpr h), Finset.card_range]

/-- The inner sums of the interpolation, over the index set `S = Icc 1 (M-1)`. -/
lemma atInnerSum (M : ℕ) (hM : 0 < M) (j : ℕ) (hj : j ≤ M - 1) :
    (∑ i ∈ Finset.Icc 1 (M - 1), (atD F i * (atL F (M - 1 - i)) ^ (Nat.card F ^ i))⁻¹ *
        (atTheta F) ^ (j * Nat.card F ^ i))
      = (if j = M - 1 then (1 : atQ F) else 0)
          - (atTheta F) ^ j * (atL F (M - 1))⁻¹ := by
  have h0S : (0 : ℕ) ∉ Finset.Icc 1 (M - 1) := by
    rw [Finset.mem_Icc]; omega
  have hrange : Finset.range M = insert 0 (Finset.Icc 1 (M - 1)) := by
    ext x; simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Icc]; omega
  have hAI := atInterp F (M - 1) j hj
  rw [Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr (Nat.pos_iff_ne_zero.mp hM))] at hAI
  rw [hrange, Finset.sum_insert h0S] at hAI
  have h0term : (atTheta F) ^ (j * Nat.card F ^ 0) *
      (atD F 0 * (atL F (M - 1 - 0)) ^ (Nat.card F ^ 0))⁻¹
        = (atTheta F) ^ j * (atL F (M - 1))⁻¹ := by
    simp [atD_zero]
  rw [h0term] at hAI
  rw [← hAI, add_sub_cancel_left]
  exact Finset.sum_congr rfl (fun i hi => by ring)


/-- ★ **The key claim of Chen's Theorem 3.1 (Step 1)**, in the two-variable field: the sum of the
"ratio" terms equals `1 - P_{M-1}/L_{M-1}`. -/
theorem atClaim' (M : ℕ) :
    1 - ∑ i ∈ Finset.Icc 1 (M - 1),
          (atD F i * (atL F (M - 1 - i)) ^ (Nat.card F ^ i))⁻¹ *
            ∏ s ∈ Finset.Icc 1 (M - 1),
              ((atTheta F) ^ (Nat.card F ^ i) - (atT F) ^ (Nat.card F ^ s))
      = atPk F (M - 1) * (atL F (M - 1))⁻¹ := by
  rcases Nat.eq_zero_or_pos M with hM0 | hM
  · subst hM0; simp [atPk, atL_zero]
  set S := Finset.Icc 1 (M - 1) with hS
  have hScard : S.card = M - 1 := by rw [hS]; exact atS_card M
  have hkey : (∑ i ∈ S, (atD F i * (atL F (M - 1 - i)) ^ (Nat.card F ^ i))⁻¹ *
        ∏ s ∈ S, ((atTheta F) ^ (Nat.card F ^ i) - (atT F) ^ (Nat.card F ^ s)))
      = 1 - atPk F (M - 1) * (atL F (M - 1))⁻¹ := by
    rw [sum_mul_prod_sub F S _ _ _]
    have hinner : ∀ t ∈ S.powerset,
        (∑ i ∈ S, (atD F i * (atL F (M - 1 - i)) ^ (Nat.card F ^ i))⁻¹ *
            ((atTheta F) ^ (Nat.card F ^ i)) ^ (S.card - t.card))
          = (if t.card = 0 then (1 : atQ F) else 0)
              - (atTheta F) ^ (S.card - t.card) * (atL F (M - 1))⁻¹ := by
      intro t ht
      have htS : t ⊆ S := Finset.mem_powerset.mp ht
      have htc : t.card ≤ S.card := Finset.card_le_card htS
      have hjt : S.card - t.card ≤ M - 1 := by rw [hScard]; exact Nat.sub_le _ _
      have hcond : (S.card - t.card = M - 1) ↔ (t.card = 0) := by
        constructor
        · intro h; omega
        · intro h; rw [h]; simp [hScard]
      rw [show (∑ i ∈ S, (atD F i * (atL F (M - 1 - i)) ^ (Nat.card F ^ i))⁻¹ *
            ((atTheta F) ^ (Nat.card F ^ i)) ^ (S.card - t.card))
          = (∑ i ∈ S, (atD F i * (atL F (M - 1 - i)) ^ (Nat.card F ^ i))⁻¹ *
            (atTheta F) ^ ((S.card - t.card) * Nat.card F ^ i)) from by
        refine Finset.sum_congr rfl (fun i hi => ?_)
        rw [← pow_mul]
        congr 1
        ring]
      rw [atInnerSum F M hM (S.card - t.card) hjt]
      by_cases h0 : t.card = 0
      · rw [if_pos (hcond.mpr h0), if_pos h0]
      · rw [if_neg (fun h => h0 (hcond.mp h)), if_neg h0]
    have hinner' : ∀ t ∈ S.powerset,
        ((-1 : atQ F) ^ t.card * (∏ s ∈ t, (atT F) ^ (Nat.card F ^ s))) *
            (∑ i ∈ S, (atD F i * (atL F (M - 1 - i)) ^ (Nat.card F ^ i))⁻¹ *
              ((atTheta F) ^ (Nat.card F ^ i)) ^ (S.card - t.card))
          = ((-1 : atQ F) ^ t.card * (∏ s ∈ t, (atT F) ^ (Nat.card F ^ s))) *
            ((if t.card = 0 then (1 : atQ F) else 0)
              - (atTheta F) ^ (S.card - t.card) * (atL F (M - 1))⁻¹) := by
      intro t ht; rw [hinner t ht]
    rw [Finset.sum_congr rfl hinner']
    have h1 : (∑ t ∈ S.powerset, (-1 : atQ F) ^ t.card *
          (∏ s ∈ t, (atT F) ^ (Nat.card F ^ s)) * (if t.card = 0 then (1 : atQ F) else 0)) = 1 := by
      rw [Finset.sum_eq_single (∅ : Finset ℕ)]
      · simp
      · intro t ht hne
        rw [if_neg (fun hc => hne (Finset.card_eq_zero.mp hc))]
        ring
      · intro h; exact absurd (Finset.mem_powerset.mpr (Finset.empty_subset S)) h
    have h2 : (∑ t ∈ S.powerset, (-1 : atQ F) ^ t.card *
          (∏ s ∈ t, (atT F) ^ (Nat.card F ^ s)) * (atTheta F) ^ (S.card - t.card))
        = atPk F (M - 1) := by
      rw [atPk, ← hS]
      exact (prod_sub_rev F S (fun s => (atT F) ^ (Nat.card F ^ s)) (atTheta F)).symm
    have hdist : ∀ t ∈ S.powerset,
        (-1 : atQ F) ^ t.card * (∏ s ∈ t, (atT F) ^ (Nat.card F ^ s)) *
            ((if t.card = 0 then (1 : atQ F) else 0)
              - (atTheta F) ^ (S.card - t.card) * (atL F (M - 1))⁻¹)
          = (-1 : atQ F) ^ t.card * (∏ s ∈ t, (atT F) ^ (Nat.card F ^ s)) *
              (if t.card = 0 then (1 : atQ F) else 0)
            - (-1 : atQ F) ^ t.card * (∏ s ∈ t, (atT F) ^ (Nat.card F ^ s)) *
              ((atTheta F) ^ (S.card - t.card) * (atL F (M - 1))⁻¹) := by
      intro t ht; ring
    rw [Finset.sum_congr rfl hdist, Finset.sum_sub_distrib, h1]
    have h4 : (∑ t ∈ S.powerset, (-1 : atQ F) ^ t.card *
          (∏ s ∈ t, (atT F) ^ (Nat.card F ^ s)) *
          ((atTheta F) ^ (S.card - t.card) * (atL F (M - 1))⁻¹))
        = atPk F (M - 1) * (atL F (M - 1))⁻¹ := by
      have hre : ∀ t ∈ S.powerset,
          (-1 : atQ F) ^ t.card * (∏ s ∈ t, (atT F) ^ (Nat.card F ^ s)) *
              ((atTheta F) ^ (S.card - t.card) * (atL F (M - 1))⁻¹)
            = ((-1 : atQ F) ^ t.card * (∏ s ∈ t, (atT F) ^ (Nat.card F ^ s)) *
                (atTheta F) ^ (S.card - t.card)) * (atL F (M - 1))⁻¹ := by
        intro t ht; ring
      rw [Finset.sum_congr rfl hre, ← Finset.sum_mul, h2]
    rw [h4]
  rw [hS] at hkey
  rw [hkey]
  ring


/-- ★★ **Chen's key claim** in the form used for the induction (with the `γ_i` and `P` factors of
the recursion separated). -/
theorem atClaim (M : ℕ) :
    1 - ∑ i ∈ Finset.Icc 1 (M - 1),
          (atGamma F i * (atD F i)⁻¹) *
            (((atL F (M - 1 - i)) ^ (Nat.card F ^ i))⁻¹ * (atPk F (M - 1 - i)) ^ (Nat.card F ^ i))
      = atPk F (M - 1) * (atL F (M - 1))⁻¹ := by
  rw [← atClaim' F M]
  congr 1
  refine Finset.sum_congr rfl (fun i hi => ?_)
  have hi' : i ≤ M - 1 := (Finset.mem_Icc.mp hi).2
  rw [← atGamma_mul_atPk F M i hi', mul_inv]
  ring

end ZagierHoffmanPositiveChar
