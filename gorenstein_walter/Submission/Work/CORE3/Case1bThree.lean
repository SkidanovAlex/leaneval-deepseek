import Mathlib
import Submission.Work.CORE3.Defs
import Submission.Work.CORE2A.Basic
import Submission.Work.CORE2A.inf_U_S_eq_bot
import Submission.Work.CORE3.H_eq_U_sup_S
import Submission.Work.CORE3.RelIndexHHhat
import Submission.Work.CORE3.NormalizerPcoreEqHhat
import Submission.Work.BSW.Cases.K4.CardSup
import Submission.Work.CORE3.InvSetThreeSubgroup
import Submission.Work.CORE3.Case1bEightNineDefs
import Submission.Work.CORE3.JthreeNormalizerU
import Submission.Work.CORE3.JthreeOddNC
import Submission.Work.BSW.Cases.K4.benderCase2Aux
import Submission.Work.CORE3.OrderThreeLeCentralizer
import Submission.Work.CORE3.SylowDihedral

set_option maxHeartbeats 1000000
set_option linter.style.haveILetI false
set_option linter.unusedVariables false
set_option linter.dupNamespace false

namespace Work.CORE3

namespace Work.CORE3

open Work.GW2

/-!
# `b₃ = 0` (Bender 1981 §3, p. 224)

On the way to `Case1bThree` this file provides

* `bCount_four_ne_zero` and `cardU_eq_three_of_case1b`: Bender's (4) + (6) + (8) + (9) alone
  already force `b₄ ≠ 0`, whence `|U| = |K| = 3` (so `K = U`) and `|Ĥ| = 72`.  This does *not*
  use `b₃ = 0`, `b₁ = 0` or `12 ∣ b₄`, in contrast with `Work.CORE3.Case1bNumerics`.
* `not_invSet_of_isPGroup` and the structural facts about a `J₃`-coset that the argument of
  Bender p. 224 uses.
-/

section Arithmetic

/-- A sum over `Finset.range (N + 1)` of a function vanishing at every `n ≥ 5` and at every
`n > N` may be replaced by the sum over `Finset.range 5`. -/
private theorem sum_range_eq_five {M : Type*} [AddCommMonoid M] {N : ℕ} {b : ℕ → M}
    (h5 : ∀ n, 5 ≤ n → b n = 0) (hN : ∀ n, N < n → b n = 0) :
    ∑ n ∈ Finset.range (N + 1), b n = ∑ n ∈ Finset.range 5, b n := by
  rcases Nat.lt_or_ge N 4 with h | h
  · refine Finset.sum_subset (Finset.range_subset_range.mpr (by omega)) ?_
    intro x _ hx
    simp only [Finset.mem_range, not_lt] at hx
    exact hN x (by omega)
  · refine Eq.symm (Finset.sum_subset (Finset.range_subset_range.mpr (by omega)) ?_)
    intro x _ hx
    simp only [Finset.mem_range, not_lt] at hx
    exact h5 x (by omega)

/-- The weighted sum `∑ (n - 3) bₙ`, `n ≤ N`, for a sequence vanishing above `4` and above `N`,
equals `-3 b₀ - 2 b₁ - b₂ + b₄`. -/
private theorem sum_range_shift_eq_five {N : ℕ} {b : ℕ → ℕ}
    (h5 : ∀ n, 5 ≤ n → b n = 0) (hN : ∀ n, N < n → b n = 0) :
    ∑ n ∈ Finset.range (N + 1), ((n : ℤ) - 3) * (b n : ℤ)
      = -3 * (b 0 : ℤ) - 2 * (b 1 : ℤ) - (b 2 : ℤ) + (b 4 : ℤ) := by
  have hnh : ∀ n, b n = 0 → ((n : ℤ) - 3) * (b n : ℤ) = 0 := by
    intro n hn; rw [hn, Nat.cast_zero, mul_zero]
  have h5' : ∀ n : ℕ, 5 ≤ n → ((n : ℤ) - 3) * (b n : ℤ) = 0 := fun n hn => hnh n (h5 n hn)
  have hN' : ∀ n : ℕ, N < n → ((n : ℤ) - 3) * (b n : ℤ) = 0 := fun n hn => hnh n (hN n hn)
  rw [sum_range_eq_five (b := fun n : ℕ => ((n : ℤ) - 3) * (b n : ℤ)) h5' hN']
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  norm_num
  ring

end Arithmetic

section Reduction

variable {G : Type} [Group G] [Finite G]

/-- Bender 1981 §3: `b₄ ≠ 0`.

If `b₄ = 0` then (8) gives `b₂ = 6k²` while (4) (with `bₙ = 0` for `n ≥ 5`) reads
`6k = 3b₀ + 2b₁ + b₂ ≥ b₂`; hence `6k ≥ 6k²`, i.e. `k ≤ 1`, against `K ≠ ⊥`. -/
theorem bCount_four_ne_zero (I : Case1Inputs) (hCount : Case1bCountProp)
    (h89 : Case1bEightNineProp) (hBc : BenderCtx G) (B : BenderSetup G) (h1 : Case1 B)
    (D : Case1bData B) : bCount B.Hhat 4 ≠ 0 := by
  classical
  obtain ⟨-, -, -, hWsum, -⟩ := hCount G I.T.ft hBc B h1 D
  obtain ⟨hvan, h89b, -⟩ := h89 G I.T.ft hBc B h1 D
  -- `|Ĥ| ≥ 5`, so that only the terms `n ≤ 4` of the weighted sum survive
  have hSNU : (B.S : Subgroup G) ≤ Subgroup.normalizer (B.U : Set G) :=
    le_trans (Work.CORE2A.bSetup_S_le_H B)
      (Work.CORE3.le_normalizer_map_subtype B.H (Work.GW2.oddCore ↥B.H))
  have hcardH : Nat.card B.H = Nat.card B.U * 8 := by
    rw [← H_eq_U_sup_S G I.T hBc B,
      Work.BSW.Cases.K4.card_sup_of_le_normalizer_of_inf_eq_bot hSNU
        (Work.CORE2A.inf_U_S_eq_bot B), D.S8, mul_comm]
  have hrelHH : B.H.relIndex B.Hhat = 3 := RelIndexHHhat I hBc B h1 D
  have hcardHhat : Nat.card B.Hhat = 3 * Nat.card B.H := by
    have h := Subgroup.relIndex_mul_card B.H B.Hhat
    rw [inf_eq_left.mpr B.H_le_Hhat, hrelHH] at h
    exact h.symm
  have h5 : 5 ≤ Nat.card B.Hhat := by
    have hu : 1 ≤ Nat.card B.U := Nat.card_pos
    calc (5 : ℕ) ≤ 8 * 1 := by norm_num
      _ ≤ 8 * Nat.card B.U := Nat.mul_le_mul_left 8 hu
      _ ≤ 3 * (8 * Nat.card B.U) := Nat.le_mul_of_pos_left _ (by norm_num)
      _ = 3 * (Nat.card B.U * 8) := by ring
      _ = Nat.card B.Hhat := by rw [hcardHhat, hcardH]
  have hN : ∀ n, Nat.card B.Hhat < n → bCount B.Hhat n = 0 := by
    intro n hn
    rw [bCount, Set.ncard_eq_zero, ← Set.not_nonempty_iff_eq_empty]
    rintro ⟨c, hc, hcnt⟩
    exact absurd hcnt (by
      have := Work.CORE2A.cosetInvCount_le B.Hhat (Quotient.out c)
      omega)
  have hsum := sum_range_shift_eq_five (b := bCount B.Hhat) hvan hN
  have hEq : (6 : ℤ) * (Nat.card D.K : ℤ)
      + (-3 * (bCount B.Hhat 0 : ℤ) - 2 * (bCount B.Hhat 1 : ℤ)
          - (bCount B.Hhat 2 : ℤ) + (bCount B.Hhat 4 : ℤ)) = 0 := by
    rw [← hsum]; exact hWsum
  intro hb4
  have hb2 : bCount B.Hhat 2 = 6 * (Nat.card D.K) ^ 2 := by
    have h := h89b
    rw [hb4, mul_zero, zero_add] at h
    exact h
  have hb2z : (bCount B.Hhat 2 : ℤ) = 6 * (Nat.card D.K : ℤ) ^ 2 := by
    rw [hb2]; push_cast; ring
  have hb4z : (bCount B.Hhat 4 : ℤ) = 0 := by rw [hb4]; norm_num
  have hb0z : (0 : ℤ) ≤ (bCount B.Hhat 0 : ℤ) := by exact_mod_cast Nat.zero_le _
  have hb1z : (0 : ℤ) ≤ (bCount B.Hhat 1 : ℤ) := by exact_mod_cast Nat.zero_le _
  have hle : 6 * (Nat.card D.K : ℤ) ^ 2 ≤ 6 * (Nat.card D.K : ℤ) := by
    nlinarith [hEq, hb2z, hb4z, hb0z, hb1z]
  have hleN : 6 * (Nat.card D.K) ^ 2 ≤ 6 * Nat.card D.K := by exact_mod_cast hle
  have hkk : Nat.card D.K * Nat.card D.K ≤ Nat.card D.K := by
    have h2 : 6 * (Nat.card D.K * Nat.card D.K) ≤ 6 * Nat.card D.K := by
      simpa [pow_two] using hleN
    exact Nat.le_of_mul_le_mul_left h2 (by norm_num)
  have hk1 : Nat.card D.K ≤ 1 := by
    by_contra hk
    have hk2 : 2 ≤ Nat.card D.K := Nat.succ_le_of_lt (Nat.lt_of_not_le hk)
    have h3 : 2 * Nat.card D.K ≤ 1 * Nat.card D.K := by
      calc 2 * Nat.card D.K ≤ Nat.card D.K * Nat.card D.K := Nat.mul_le_mul_right _ hk2
        _ ≤ Nat.card D.K := hkk
        _ = 1 * Nat.card D.K := by ring
    exact absurd (Nat.le_of_mul_le_mul_right h3 Nat.card_pos) (by norm_num)
  exact D.ne ((Subgroup.card_eq_one).mp (le_antisymm hk1 Nat.card_pos))

/-- Bender 1981 §3, p. 224, the numerical part of Case (1b) with `V = O₂(Ĥ)` of type `(2,2)`:
(4) + (6) + (8) + (9) force `|U| = |K| = 3` (hence `K = U`) and `|Ĥ| = 72`. -/
theorem cardU_eq_three_of_case1b (I : Case1Inputs) (hCount : Case1bCountProp)
    (h89 : Case1bEightNineProp) (hBc : BenderCtx G) (B : BenderSetup G) (h1 : Case1 B)
    (D : Case1bData B) :
    Nat.card B.U = 3 ∧ Nat.card D.K = 3 ∧ D.K = B.U ∧ Nat.card B.Hhat = 72 := by
  classical
  have hb4 : bCount B.Hhat 4 ≠ 0 := bCount_four_ne_zero I hCount h89 hBc B h1 D
  obtain ⟨-, -, h89c⟩ := h89 G I.T.ft hBc B h1 D
  obtain ⟨hU3, hK3⟩ := h89c hb4
  -- `K ≤ U` (a Hall subgroup of `F(U)`), and the orders agree
  have hKU : D.K ≤ B.U :=
    (Work.CORE2A.isHallIn_le D.hall).trans (Subgroup.map_subtype_le _)
  have hKUeq : D.K = B.U := Subgroup.eq_of_le_of_card_ge hKU (by rw [hU3, hK3])
  refine ⟨hU3, hK3, hKUeq, ?_⟩
  -- `|Ĥ| = |Ĥ : H| * |H| = 3 * (|U| * |S|) = 3 * 24 = 72`
  have hSNU : (B.S : Subgroup G) ≤ Subgroup.normalizer (B.U : Set G) :=
    le_trans (Work.CORE2A.bSetup_S_le_H B)
      (Work.CORE3.le_normalizer_map_subtype B.H (Work.GW2.oddCore ↥B.H))
  have hcardH : Nat.card B.H = 24 := by
    rw [← H_eq_U_sup_S G I.T hBc B,
      Work.BSW.Cases.K4.card_sup_of_le_normalizer_of_inf_eq_bot hSNU
        (Work.CORE2A.inf_U_S_eq_bot B), hU3, D.S8]
  have hrelHH : B.H.relIndex B.Hhat = 3 := RelIndexHHhat I hBc B h1 D
  have hcardHhat : Nat.card B.Hhat = 3 * Nat.card B.H := by
    have h := Subgroup.relIndex_mul_card B.H B.Hhat
    rw [inf_eq_left.mpr B.H_le_Hhat, hrelHH] at h
    exact h.symm
  rw [hcardHhat, hcardH]

end Reduction

/-! ## The `J₃`-toolkit

The two structural consequences of (5) that the argument of Bender p. 224 uses, together with
the commutation criterion for the involutions of a coset of `Ĥ`, which is what turns the count
of commuting pairs in §3 into a computation inside `I_Ĥ(y)`. -/

section Toolkit

variable {G : Type} [Group G] [Finite G]

/-- **The `J₃`-case, first consequences** (Bender 1981 §3, p. 224, first sentence).

If `y ∉ Ĥ` is an involution whose coset carries exactly three involutions, then there is `x ∈ Ĥ`
of order `3`, inverted by `y`, with `x ∉ V ⊔ U` (by (5)) and with inversion set exactly
`{1, x, x⁻¹}`.  (The elementary structure of the inversion set is `Work.CORE3.InvSetThreeSubgroup`;
the exclusion `x ∉ V ⊔ U` is Bender's (5).) -/
theorem jthree_exists (I : Case1Inputs) (hFive : Case1bFiveProp) (hBc : BenderCtx G)
    (B : BenderSetup G) (h1 : Case1 B) (D : Case1bData B) {y : G} (hy2 : orderOf y = 2)
    (hyH : y ∉ B.Hhat) (hcnt : cosetInvCount B.Hhat y = 3) :
    ∃ x ∈ B.Hhat, orderOf x = 3 ∧ y * x * y = x⁻¹ ∧
      x ∉ (pCoreIn 2 B.Hhat ⊔ B.U) ∧
      ∀ z ∈ B.Hhat, y * z * y = z⁻¹ → z = 1 ∨ z = x ∨ z = x⁻¹ := by
  classical
  have hy : y * y = 1 := by rw [← pow_two, ← hy2]; exact pow_orderOf_eq_one y
  obtain ⟨x, hxH, hx3, hxinv, hcl⟩ :=
    Work.CORE3.InvSetThreeSubgroup B.Hhat y hy hyH hcnt
  refine ⟨x, hxH, hx3, hxinv, ?_, hcl⟩
  intro hxVU
  have hmem : x ∈ invSet (pCoreIn 2 B.Hhat ⊔ B.U) y := by
    refine ⟨hxVU, ?_⟩
    rw [inv_eq_of_mul_eq_one_left hy]
    exact hxinv
  rw [hFive G I.T.ft hBc B h1 D y hy2 hyH] at hmem
  have hx1 : x = 1 := Set.mem_singleton_iff.mp hmem
  rw [hx1] at hx3
  exact absurd hx3 (by norm_num)


/-! ### What remains for `b₃ = 0`

`cardU_eq_three_of_case1b` shows that `hSetup`, `hCount` and `h89` alone force
`|U| = |K| = 3` (so `K = U`), `|Ĥ| = 72` and `|S| = 8`; that is Bender's (9) without `b₃ = 0`.

For the `J₃`-case of Bender p. 224 two further steps are needed.

1. **(6) for `n ≤ 3`** (elementary; statement delegated as `Work.CORE3.InvSetThreeSubgroup`):
   if `y ∉ Ĥ` is an involution with `cosetInvCount Ĥ y = 3`, then the inversion set
   `I = {z ∈ Ĥ | y z y = z⁻¹}` equals `{1, x, x⁻¹}` with `orderOf x = 3`.  Indeed `I` is closed
   under inverses and squares; for `1 ≠ a ∈ I` the four elements `1, a, a⁻¹, a * a` would be
   distinct unless `a² ∈ {1, a⁻¹}`, and two involutions `a, b ∈ I` give the further element
   `b * a * b`.  Write `X := I_Ĥ(y) = ⟨x⟩`; (5) gives `x ∉ V ⊔ U`, and hence

2. **(the structure of `C_Ĥ(x)`)** (statement delegated as `Work.CORE3.CentHhatOrderThree`, whose
   `x ∉ V ⊔ U`-hypothesis is exactly what step 1 produces):
   `C_Ĥ(x) = ⟨x⟩ ⊔ U`, of order `9`.  Here `Ĥ/VU ≅ S₃` (Theorem 2.6), so an involution
   `w ∈ C_Ĥ(x)` has `wVU ∈ C_{S₃}(xVU) = ⟨xVU⟩` and `(wVU)² = 1`, whence `w ∈ VU`; as `U` is odd
   and `x ∉ C_Ĥ(V) = VU` acts fixed-point-freely on the four-group `V`, `w ∈ V ∩ C(x) = 1`.  So
   `C_Ĥ(x)` is odd, and `⟨x, U⟩ ≤ C_Ĥ(x)` with `|U| = 3`, `[x, U] = 1` gives the equality.

Note that Bender's printed continuation of the `J₃`-argument — "`A := C_Ĥ(X)` has odd order …
`A₁ := C_A(y) ≠ 1` is conjugate to `U = K`" — is *not* available here: `A = ⟨x, U⟩` has
`C_A(y) = 1` because `y` inverts `x` and centralizes no element of `U^#` (`U ∩ U^y = 1`, as
`y ∉ N_G(U) = Ĥ`).  The remaining open step is therefore the `J₃`-contradiction itself; the
natural equivalent form is:

  *for every involution `y ∉ Ĥ` there is an involution of `Ĥ` commuting with `y`*

(equivalently: no coset of `Ĥ` contains an odd number of involutions).  The `J₃`-hypothesis
`cosetInvCount Ĥ y = 3` makes the inverted set `{1, x, x⁻¹}` of odd order, and the three
involutions `y, yx, yx²` of the coset then have `C_Ĥ(·) ∩ J = ∅`, so that the count of commuting
pairs of §3 does *not* exclude `b₃ ≠ 0` (this is why `Case1bIndex` needs `b₃ = 0` as an extra
input).  A proof must use the global hypothesis (`BenderCtx`) through `N_G(⟨x⟩) = Ĥ · ⟨y⟩` and
the `D`-group structure of that subgroup.
-/

/-- **Bender (5) on a coset.**  For an involution `y ∉ Ĥ`, no element of the coset `yĤ` other
than `y` itself is inverted by `y`, i.e. the only `z ∈ Ĥ` with `y z y = z⁻¹` and `z² = 1` is `1`. -/
theorem invSetIn_eq_one_of_isFourGroup (hFive : Case1bFiveProp) (hFT : FeitThompsonProp)
    (hBc : BenderCtx G) (B : BenderSetup G) (h1 : Case1 B) (D : Case1bData B) {y : G}
    (hy2 : orderOf y = 2) (hyH : y ∉ B.Hhat) :
    invSet (pCoreIn 2 B.Hhat ⊔ B.U) y = {1} :=
  hFive G hFT hBc B h1 D y hy2 hyH

/-- **Commutation in a coset.**  For an involution `z` and `h, h' ∈ Ĥ` with `z h z = h⁻¹`,
`z h' z = h'⁻¹`, the products `zh` and `zh'` commute exactly when `h' = h * h'⁻¹ * h`.  (This is
the computation behind Bender's count (8) of commuting pairs.) -/
theorem mul_mul_comm_iff {z h h' : G} (hz : z * z = 1) (hh : z * h * z = h⁻¹)
    (hh' : z * h' * z = h'⁻¹) :
    (z * h) * (z * h') = (z * h') * (z * h) ↔ h' = h * h'⁻¹ * h := by
  have e1 : (z * h) * (z * h') = h⁻¹ * h' := by
    calc (z * h) * (z * h') = z * h * z * h' := by group
      _ = (z * h * z) * h' := by group
      _ = h⁻¹ * h' := by rw [hh]
  have e2 : (z * h') * (z * h) = h'⁻¹ * h := by
    calc (z * h') * (z * h) = z * h' * z * h := by group
      _ = (z * h' * z) * h := by group
      _ = h'⁻¹ * h := by rw [hh']
  rw [e1, e2]
  constructor
  · intro hc
    have h3 : h * (h⁻¹ * h') = h * (h'⁻¹ * h) := by rw [hc]
    simpa [mul_assoc] using h3
  · intro hc
    nth_rewrite 1 [hc]
    group

end Toolkit

end Work.CORE3

open Work.GW2

/-- The numerical reduction at the namespace of the file path, for callers that do not want the
doubly nested name (the statement is the same). -/
theorem cardU_eq_three_of_case1b (I : Case1Inputs) (hCount : Case1bCountProp)
    (h89 : Case1bEightNineProp) :
    ∀ (G : Type) [Group G] [Finite G], BenderCtx G → ∀ B : BenderSetup G, Case1 B →
      ∀ D : Case1bData B, Nat.card B.U = 3 ∧ Nat.card D.K = 3 ∧ D.K = B.U ∧
        Nat.card B.Hhat = 72 :=
  fun G _ _ hBc B h1 D =>
    _root_.Work.CORE3.Work.CORE3.cardU_eq_three_of_case1b I hCount h89 hBc B h1 D

namespace Work.CORE3

namespace Work.CORE3

/-! ## Bookkeeping: extracting the `J₃`-involution

`bCount Ĥ 3 ≠ 0` produces a coset of `Ĥ` containing exactly three involutions.  For the `J₃`
analysis one wants an *involution* `y ∉ Ĥ` whose coset carries the three involutions; the two
elementary lemmas below replace "a coset with `n` involutions" by "an involution whose coset has
`n` involutions". -/

section Bookkeeping

variable {G : Type} [Group G] [Finite G]

/-- If the coset of `g` contains a non-zero number of involutions, then one of those involutions
`y` lies in the same coset (hence `y ∉ Ĥ` when `g ∉ Ĥ`) and the two counts agree. -/
theorem exists_involution_of_cosetInvCount_ne_zero (B : BenderSetup G) {g : G}
    (hgH : g ∉ B.Hhat) (hg : cosetInvCount B.Hhat g ≠ 0) :
    ∃ y : G, orderOf y = 2 ∧ y ∉ B.Hhat ∧ cosetInvCount B.Hhat y = cosetInvCount B.Hhat g := by
  have hg' : ({x : G | orderOf x = 2 ∧ g⁻¹ * x ∈ B.Hhat} : Set G).ncard ≠ 0 := hg
  have hne : ({x : G | orderOf x = 2 ∧ g⁻¹ * x ∈ B.Hhat} : Set G).Nonempty := by
    rw [← Set.ncard_pos]
    exact Nat.pos_of_ne_zero hg'
  obtain ⟨y, hy2, hy⟩ := hne
  have hcos : Work.CORE3.leftCoset B.Hhat g = Work.CORE3.leftCoset B.Hhat y :=
    Work.CORE3.leftCoset_eq_iff.mpr hy
  refine ⟨y, hy2, fun hyH => hgH ?_, Work.CORE3.cosetInvCount_eq_of_leftCoset_eq hcos.symm⟩
  have h2 : g = y * (g⁻¹ * y)⁻¹ := by group
  rw [h2]
  exact B.Hhat.mul_mem hyH (B.Hhat.inv_mem hy)

/-- `bCount Ĥ n ≠ 0` is realised by an involution `y ∉ Ĥ` whose coset carries exactly `n`
involutions. -/
theorem exists_involution_of_bCount_three_ne_zero (B : BenderSetup G)
    (hn : bCount B.Hhat 3 ≠ 0) :
    ∃ y : G, orderOf y = 2 ∧ y ∉ B.Hhat ∧ cosetInvCount B.Hhat y = 3 := by
  have hn' : ({c : G ⧸ B.Hhat | c ≠ ((1 : G) : G ⧸ B.Hhat) ∧
      cosetInvCount B.Hhat (Quotient.out c) = 3} : Set (G ⧸ B.Hhat)).ncard ≠ 0 := hn
  have hne : ({c : G ⧸ B.Hhat | c ≠ ((1 : G) : G ⧸ B.Hhat) ∧
      cosetInvCount B.Hhat (Quotient.out c) = 3} : Set (G ⧸ B.Hhat)).Nonempty := by
    rw [← Set.ncard_pos]
    exact Nat.pos_of_ne_zero hn'
  obtain ⟨c, hc, hcn⟩ := hne
  have hout : Quotient.out c ∉ B.Hhat := Work.CORE3.quotient_out_notMem hc
  obtain ⟨y, hy2, hyH, hyc⟩ :=
    exists_involution_of_cosetInvCount_ne_zero B hout (by rw [hcn]; norm_num)
  exact ⟨y, hy2, hyH, by rw [hyc, hcn]⟩

end Bookkeeping

/-! ## The `J₃`-case: `C_Ĥ(y)` has no involutions

If the inverted set of the involution `y ∉ Ĥ` inside `Ĥ` is `{1, x, x⁻¹}` with `x` of order `3`
(Bender's (6) for `n ≤ 3`), then `y` commutes with no non-trivial involution of `Ĥ`: for such an
involution `h`, the product `y h` is an involution of the coset `yĤ`, hence forces
`h ∈ {1, x, x⁻¹}`, and only `1` has order `2` among these. -/

section JthreeLocal

variable {G : Type} [Group G] [Finite G]

/-- In the `J₃`-case, no non-trivial involution of `Ĥ` commutes with `y`. -/
theorem eq_one_of_mul_comm_of_jthree (B : BenderSetup G) {y h x : G} (hy : y * y = 1)
    (hhH : h ∈ B.Hhat) (hcomm : y * h = h * y) (h2 : h * h = 1)
    (hcl : ∀ z ∈ B.Hhat, y * z * y = z⁻¹ → z = 1 ∨ z = x ∨ z = x⁻¹)
    (hx3 : orderOf x = 3) : h = 1 := by
  have hyhy : y * h * y = h := by rw [hcomm, mul_assoc, hy, mul_one]
  have hyhy' : y * h * y = h⁻¹ := by
    rw [hyhy]
    exact (inv_eq_of_mul_eq_one_right h2).symm
  have hdvd : orderOf h ∣ 2 := orderOf_dvd_iff_pow_eq_one.mpr (by rw [pow_two]; exact h2)
  rcases hcl h hhH hyhy' with h1 | h1 | h1
  · exact h1
  · rw [h1, hx3] at hdvd
    exact absurd hdvd (by norm_num)
  · rw [h1] at hdvd
    have h3 : x ^ 2 = 1 := by
      have h4 := orderOf_dvd_iff_pow_eq_one.mp hdvd
      have h5 : (x ^ 2)⁻¹ = 1 := by simpa [inv_pow] using h4
      simpa using congrArg Inv.inv h5
    have hdvd2 : orderOf x ∣ 2 := orderOf_dvd_iff_pow_eq_one.mpr h3
    rw [hx3] at hdvd2
    exact absurd hdvd2 (by norm_num)

end JthreeLocal

/-- The assembly: the `J₃`-case of Bender §3 contradicts the accumulated hypotheses. -/
theorem jthree_contradiction_of
    (hCrux : ∀ (G : Type) [Group G] [Finite G] (hBc : BenderCtx G) (B : BenderSetup G)
      (h1 : Case1 B) (h4 : IsFourGroup (pCoreIn 2 B.Hhat)) (D : Case1bData B) {x y : G},
      x ∈ B.Hhat → orderOf x = 3 → x ∉ (pCoreIn 2 B.Hhat ⊔ B.U) → orderOf y = 2 →
      y ∉ B.Hhat → y * x * y⁻¹ = x⁻¹ → cosetInvCount B.Hhat y = 3 →
      ∃ k : G, ∀ u ∈ B.U, x * (k * u * k⁻¹) = (k * u * k⁻¹) * x ∧
                          y * (k * u * k⁻¹) = (k * u * k⁻¹) * y)
    (I : Case1Inputs) (hSetup : Case1bSetupProp) (hCount : Case1bCountProp)
    (hFive : Case1bFiveProp) (h89 : Case1bEightNineProp) : Case1bThreeProp := by
  intro G instG instFin hFT hBc B h1 h4
  by_contra hne
  obtain ⟨D⟩ := hSetup G hFT hBc B h1 h4
  obtain ⟨hU3, hK3, hKU, hHhat72⟩ :=
    _root_.Work.CORE3.Work.CORE3.cardU_eq_three_of_case1b I hCount h89 hBc B h1 D
  obtain ⟨y, hy2, hyH, hcnt⟩ :=
    _root_.Work.CORE3.Work.CORE3.Work.CORE3.exists_involution_of_bCount_three_ne_zero B hne
  obtain ⟨x, hxH, hx3, hinv, hxVU, hcl⟩ :=
    _root_.Work.CORE3.Work.CORE3.jthree_exists I hFive hBc B h1 D hy2 hyH hcnt
  have hy1 : y * y = 1 := by rw [← pow_two, ← hy2]; exact pow_orderOf_eq_one y
  have hinv' : y * x * y⁻¹ = x⁻¹ := by
    rw [inv_eq_of_mul_eq_one_right hy1]; exact hinv
  obtain ⟨k, hk⟩ := hCrux G hBc B h1 h4 D hxH hx3 hxVU hy2 hyH hinv' hcnt
  have hx3'' : x ^ 3 = 1 := by rw [← hx3]; exact pow_orderOf_eq_one x
  -- the conjugated elements
  set x' : G := k⁻¹ * x * k with hx'def
  set y' : G := k⁻¹ * y * k with hy'def
  have hxU : ∀ u ∈ B.U, x' * u = u * x' := by
    intro u hu
    have h := congrArg (fun z => k⁻¹ * z * k) (hk u hu).1
    simp only [hx'def]
    simpa [mul_assoc] using h
  have hyU : ∀ u ∈ B.U, y' * u = u * y' := by
    intro u hu
    have h := congrArg (fun z => k⁻¹ * z * k) (hk u hu).2
    simp only [hy'def]
    simpa [mul_assoc] using h
  have hx'N : x' ∈ Subgroup.normalizer (B.U : Set G) :=
    Subgroup.centralizer_le_normalizer (B.U : Set G)
      (Subgroup.mem_centralizer_iff.mpr fun u hu => (hxU u hu).symm)
  have hy'N : y' ∈ Subgroup.normalizer (B.U : Set G) :=
    Subgroup.centralizer_le_normalizer (B.U : Set G)
      (Subgroup.mem_centralizer_iff.mpr fun u hu => (hyU u hu).symm)
  rw [_root_.Work.CORE3.JthreeNormalizerU I hSetup hCount h89 hBc B h1 h4 D] at hx'N hy'N
  -- orders of the conjugated elements
  have hx'3 : x' * x' * x' = 1 := by
    have h : (k⁻¹ * x * k) * (k⁻¹ * x * k) * (k⁻¹ * x * k) = k⁻¹ * (x * x * x) * k := by
      group
    have hx3mul : x * x * x = 1 := by rw [← pow_two, ← pow_succ, hx3'']
    simp only [hx'def]
    rw [h, hx3mul, mul_one, inv_mul_cancel]
  have hx'1 : x' ≠ 1 := by
    intro h1'
    have hxeq : x = 1 := by
      have : k * x' * k⁻¹ = x := by simp only [hx'def]; group
      rw [h1'] at this
      simpa using this.symm
    rw [hxeq] at hx3
    exact absurd hx3 (by norm_num)
  have hy'2m : y' * y' = 1 := by
    simp only [hy'def]
    calc (k⁻¹ * y * k) * (k⁻¹ * y * k) = k⁻¹ * (y * y) * k := by group
      _ = 1 := by rw [hy1, mul_one, inv_mul_cancel]
  have hy'1 : y' ≠ 1 := by
    intro h1'
    have hyeq : y = 1 := by
      have : k * y' * k⁻¹ = y := by simp only [hy'def]; group
      rw [h1'] at this
      simpa using this.symm
    rw [hyeq] at hy2
    exact absurd hy2 (by norm_num)
  have hy'2 : orderOf y' = 2 :=
    (_root_.Work.CORE3.orderOf_eq_two_iff_mul_self y').mpr ⟨hy'2m, hy'1⟩
  -- `y' x' y' = x'⁻¹` (the conjugate of `y x y = x⁻¹`)
  have hy'inv : y' * x' * y' = x'⁻¹ := by
    have h := congrArg (fun z => k⁻¹ * z * k) hinv
    simp only [hx'def, hy'def]
    simpa [mul_assoc] using h
  have hy'inv' : y' * x' * y'⁻¹ = x'⁻¹ := by
    rw [inv_eq_of_mul_eq_one_right hy'2m]; exact hy'inv
  -- a non-trivial element of `U`
  have hUne : B.U ≠ ⊥ := by
    intro hbot
    have h1c : Nat.card ↥B.U = 1 := by rw [hbot]; exact Subgroup.card_bot
    omega
  obtain ⟨u₀, hu₀1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hUne
  set u : G := (u₀ : G) with hudef
  have huU : u ∈ B.U := u₀.2
  have hu1 : u ≠ 1 := fun h => hu₀1 (Subtype.ext h)
  have hu3 : orderOf u = 3 := by
    have hdvd : orderOf u ∣ 3 := by
      have h := Subgroup.orderOf_dvd_natCard B.U huU
      rwa [hU3] at h
    rcases Nat.Prime.eq_one_or_self_of_dvd (by norm_num : Nat.Prime 3) (orderOf u) hdvd with h | h
    · exact absurd (orderOf_eq_one_iff.mp h) hu1
    · exact h
  have hu_ne_inv : u ≠ u⁻¹ := by
    intro h
    have h2 : u * u = 1 := by nth_rewrite 1 [h]; exact inv_mul_cancel u
    have hdvd : orderOf u ∣ 2 := orderOf_dvd_iff_pow_eq_one.mpr (by rw [pow_two]; exact h2)
    rw [hu3] at hdvd
    omega
  by_cases hyV : y' ∈ pCoreIn 2 B.Hhat
  · -- `y' ∈ V`: then `x' = [y',x'] ∈ V`, contradicting `orderOf x' = 3`
    have hy'Vinv : y'⁻¹ ∈ pCoreIn 2 B.Hhat := Subgroup.inv_mem _ hyV
    have hHnorm : B.Hhat ≤ Subgroup.normalizer ((pCoreIn 2 B.Hhat : Subgroup G) : Set G) := by
      rw [NormalizerPcoreEqHhat G hBc B h4]
    have hconj : x' * y'⁻¹ * x'⁻¹ ∈ pCoreIn 2 B.Hhat :=
      (Subgroup.le_normalizer_iff.mp hHnorm) x' hx'N y'⁻¹ hy'Vinv
    have hcom : y' * (x' * y'⁻¹ * x'⁻¹) ∈ pCoreIn 2 B.Hhat :=
      Subgroup.mul_mem _ hyV hconj
    have hcomm_eq : y' * (x' * y'⁻¹ * x'⁻¹) = x' := by
      have h2 : x'⁻¹ = x' * x' :=
        inv_eq_of_mul_eq_one_right ((mul_assoc x' x' x').symm.trans hx'3)
      have h3 : x'⁻¹ * x'⁻¹ = x' := by
        rw [h2]
        calc (x' * x') * (x' * x') = x' * ((x' * x') * x') := by group
          _ = x' * 1 := by rw [hx'3]
          _ = x' := mul_one x'
      calc y' * (x' * y'⁻¹ * x'⁻¹) = (y' * x' * y'⁻¹) * x'⁻¹ := by group
        _ = x'⁻¹ * x'⁻¹ := by rw [hy'inv']
        _ = x' := h3
    have hx'V : x' ∈ pCoreIn 2 B.Hhat := by rw [← hcomm_eq]; exact hcom
    have hx'2 : x' * x' = 1 := by
      have h := (h4.2) x' hx'V
      rwa [pow_two] at h
    have hx'21 : x' = 1 := by
      have h1 : x' * (x' * x') = 1 := by rw [← mul_assoc]; exact hx'3
      calc x' = x' * 1 := (mul_one x').symm
        _ = x' * (x' * x') := by rw [hx'2]
        _ = 1 := h1
    exact hx'1 hx'21
  · -- `y' ∉ V`: `D.inv` makes `y'` invert `U`, contradicting `y' u y'⁻¹ = u`
    have hDV := D.inv y' hy'N hy'2 hyV
    have hKU' : (B.U : Set G) = (D.K : Set G) := by rw [hKU]
    have hset : (B.U : Set G) = invSet B.U y' := hKU'.trans hDV
    have hinvU : y' * u * y'⁻¹ = u⁻¹ := by
      have : u ∈ invSet B.U y' := by rw [← hset]; exact huU
      exact this.2
    have hfix : y' * u * y'⁻¹ = u := by
      rw [hyU u huU, mul_assoc, mul_inv_cancel, mul_one]
    rw [hinvU] at hfix
    exact hu_ne_inv hfix.symm

/-! ## From `Odd |C_G(x)|` to the conjugacy of `U`

Bender 1981 §3, p. 224 (the `J₃`-case).  The next four lemmas are the mechanical part of the
`J₃`-argument: once `C_G(x)` has odd order, the subgroup `A = C_G(x) ⊓ C_G(y)` is a nontrivial
odd-order subgroup of `H = C_G(t)`, hence of order `3`, hence equals `U`; this yields `k` with
`U^k ≤ C_G(x) ⊓ C_G(y)`.  (The remaining input, `Odd |C_G(x)|`, is Bender's (7); see
`Work.CORE3.JthreeCentralizerOdd`.) -/

section JthreeOdd

variable {G : Type} [Group G] [Finite G]

/-- Jordan-type lemma: a fixed-point-free involutive automorphism of a finite group is
inversion. -/
theorem jthreeInvEqOfFixedPointFree {A : Type} [Group A] [Finite A]
    (σ : A →* A) (hσinj : Function.Injective σ) (hσ2 : ∀ a, σ (σ a) = a)
    (hfix : ∀ a, σ a = a → a = 1) : ∀ a, σ a = a⁻¹ := by
  set f : A → A := fun a => a * (σ a)⁻¹ with hf
  have hfinj : Function.Injective f := by
    intro a b hab
    simp only [hf] at hab
    have h1 : b⁻¹ * a = (σ b)⁻¹ * (σ a) := by
      have h2 : b⁻¹ * (a * (σ a)⁻¹) = (σ b)⁻¹ := by
        rw [hab]; group
      calc b⁻¹ * a = b⁻¹ * (a * (σ a)⁻¹) * σ a := by group
        _ = (σ b)⁻¹ * σ a := by rw [h2]
    have h3 : (σ b)⁻¹ * (σ a) = σ (b⁻¹ * a) := by
      rw [map_mul, map_inv]
    rw [h3] at h1
    have h4 : b⁻¹ * a = 1 := hfix _ h1.symm
    exact (inv_mul_eq_one.mp h4).symm
  have hsurj : Function.Surjective f := Finite.surjective_of_injective hfinj
  intro a
  obtain ⟨b, hb⟩ := hsurj a
  have key : σ (f b) = (f b)⁻¹ := by
    simp only [hf]
    rw [map_mul, map_inv, hσ2]
    group
  rw [← hb]
  exact key

/-- `|H| = 24` in the `Case1b` setting. -/
theorem jthreeCardHEq24 (I : Case1Inputs) (hCount : Case1bCountProp) (h89 : Case1bEightNineProp)
    (hBc : BenderCtx G) (B : BenderSetup G) (h1 : Case1 B) (D : Case1bData B) :
    Nat.card B.H = 24 := by
  obtain ⟨hU3, -, -, -⟩ := Work.CORE3.Work.CORE3.cardU_eq_three_of_case1b I hCount h89 hBc B h1 D
  have hSNU : (B.S : Subgroup G) ≤ Subgroup.normalizer (B.U : Set G) :=
    le_trans (Work.CORE2A.bSetup_S_le_H B)
      (Work.CORE3.le_normalizer_map_subtype B.H (Work.GW2.oddCore ↥B.H))
  have h := Work.BSW.Cases.K4.card_sup_of_le_normalizer_of_inf_eq_bot hSNU
    (Work.CORE2A.inf_U_S_eq_bot B)
  rw [← Work.CORE3.H_eq_U_sup_S G I.T hBc B, h, hU3, D.S8]

/-- Every subgroup of order `3` of `H = C_G(t)` equals `U = O(H)`. -/
theorem jthreeEqUOfCardThree (I : Case1Inputs) (hCount : Case1bCountProp)
    (h89 : Case1bEightNineProp) (hBc : BenderCtx G) (B : BenderSetup G) (h1 : Case1 B)
    (D : Case1bData B) {W : Subgroup G} (hW : W ≤ B.H) (hW3 : Nat.card W = 3) :
    W = B.U := by
  classical
  obtain ⟨hU3, -, -, -⟩ := Work.CORE3.Work.CORE3.cardU_eq_three_of_case1b I hCount h89 hBc B h1 D
  have hWn : W ≤ Subgroup.normalizer (B.U : Set G) :=
    le_trans hW (Work.CORE3.le_normalizer_map_subtype B.H (Work.GW2.oddCore ↥B.H))
  have hcard : Nat.card ↥(B.U ⊔ W) * Nat.card ↥(B.U ⊓ W) = 9 := by
    have hc := Work.BSW.Cases.K4.card_sup_mul_card_inf_of_le_normalizer (A := B.U) (B := W) hWn
    rw [hU3, hW3] at hc
    exact hc
  have hdvd : Nat.card ↥(B.U ⊓ W) ∣ 3 := by rw [← hW3]; exact Subgroup.card_dvd_of_le inf_le_right
  have hle : B.U ⊔ W ≤ B.H := sup_le (Work.CORE2A.bSetup_U_le_H B) hW
  have hdvd24 : Nat.card ↥(B.U ⊔ W) ∣ 24 := by
    rw [← jthreeCardHEq24 I hCount h89 hBc B h1 D]
    exact Subgroup.card_dvd_of_le hle
  have hcard3 : Nat.card ↥(B.U ⊓ W) = 3 := by
    rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h | h
    · exfalso
      have h9 : Nat.card ↥(B.U ⊔ W) = 9 := by
        rw [h, mul_one] at hcard; exact hcard
      have : (9 : ℕ) ∣ 24 := h9 ▸ hdvd24
      norm_num at this
    · exact h
  have hle' : W ≤ B.U := by
    have hWeq : B.U ⊓ W = W :=
      Subgroup.eq_of_le_of_card_ge inf_le_right (by rw [hcard3, hW3])
    intro w hw
    rw [← hWeq] at hw
    exact hw.1
  exact Subgroup.eq_of_le_of_card_ge hle' (by rw [hU3, hW3])

/-- In the setting, `N_G(U) = Ĥ`. -/
theorem Jthree_normalizer_U_eq_Hhat (I : Case1Inputs) (hCount : Case1bCountProp)
    (h89 : Case1bEightNineProp) (hBc : BenderCtx G) (B : BenderSetup G) (h1 : Case1 B)
    (D : Case1bData B) :
    Subgroup.normalizer (B.U : Set G) = B.Hhat := by
  classical
  obtain ⟨hU3, -, -, -⟩ := Work.CORE3.Work.CORE3.cardU_eq_three_of_case1b I hCount h89 hBc B h1 D
  have hUeq : oddCoreIn B.Hhat = B.U := (I.h26 G I.T.ft hBc B).1
  have hUne : B.Hhat ≤ Subgroup.normalizer (B.U : Set G) := by
    have h := Work.CORE3.le_normalizer_map_subtype B.Hhat (Work.GW2.oddCore ↥B.Hhat)
    rwa [show (Subgroup.map B.Hhat.subtype (Work.GW2.oddCore ↥B.Hhat) : Subgroup G) = B.U
      from hUeq] at h
  have hUle : B.U ≤ B.Hhat := hUeq ▸ Subgroup.map_subtype_le _
  refine le_antisymm ?_ hUne
  by_contra hne
  haveI : IsSimpleGroup G := hBc.simple
  have htop : Subgroup.normalizer (B.U : Set G) = ⊤ :=
    (B.Hhat_coatom.lt_iff).mp (lt_of_le_of_ne hUne (fun hEq => hne (le_of_eq hEq.symm)))
  have hUn : (B.U : Subgroup G).Normal := Subgroup.normalizer_eq_top_iff.mp htop
  haveI := hUn
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal B.U with hb | ht
  · rw [hb, Subgroup.card_bot] at hU3; exact absurd hU3 (by norm_num)
  · exact B.Hhat_coatom.ne_top (top_le_iff.mp (ht ▸ hUle))


/-- The assembly, from Bender's step (7) in the form `Odd |C_G(x)|` supplied as a hypothesis. -/
theorem jthreeConjUOfOdd
    (I : Case1Inputs) (hSetup : Case1bSetupProp) (hCount : Case1bCountProp)
    (hFive : Case1bFiveProp) (h89 : Case1bEightNineProp)
    (hBc : BenderCtx G) (B : BenderSetup G) (h1 : Case1 B)
    (h4 : IsFourGroup (pCoreIn 2 B.Hhat)) (D : Case1bData B) {x y : G}
    (hxH : x ∈ B.Hhat) (hx3 : orderOf x = 3) (hxVU : x ∉ (pCoreIn 2 B.Hhat ⊔ B.U))
    (hy2 : orderOf y = 2) (hyH : y ∉ B.Hhat) (hinv : y * x * y⁻¹ = x⁻¹)
    (hcnt : cosetInvCount B.Hhat y = 3)
    (hCxodd : Odd (Nat.card (Subgroup.centralizer ({x} : Set G)))) :
    ∃ k : G, ∀ u ∈ B.U, x * (k * u * k⁻¹) = (k * u * k⁻¹) * x ∧
                        y * (k * u * k⁻¹) = (k * u * k⁻¹) * y := by
  classical
  obtain ⟨hU3, hK3, hKU, hHhat72⟩ := Work.CORE3.Work.CORE3.cardU_eq_three_of_case1b I hCount h89 hBc B h1 D
  have hy : y * y = 1 := by rw [← pow_two, ← hy2]; exact pow_orderOf_eq_one y
  have hyinv : y⁻¹ = y := inv_eq_of_mul_eq_one_right hy
  -- ### Step 2: all involutions are conjugate; pick `g` with `g t g⁻¹ = y`
  obtain ⟨n2, hn2, hdih⟩ := Work.CORE3.SylowDihedral G hBc B
  have hno2 : ∀ N : Subgroup G, N.Normal → N.index ≠ 2 := by
    intro N hN h2
    haveI : IsSimpleGroup G := hBc.simple
    haveI := hN
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal N with hb | hb
    · rw [hb, Subgroup.index_bot] at h2
      have h4le : 4 ≤ Nat.card G := by
        have hle : pCoreIn 2 B.Hhat ≤ (⊤ : Subgroup G) := le_top
        have hd := Subgroup.card_dvd_of_le hle
        rw [Subgroup.card_top, h4.1] at hd
        exact Nat.le_of_dvd (by norm_num) hd
      omega
    · rw [hb, Subgroup.index_top] at h2
      norm_num at h2
  obtain ⟨g, hg⟩ := (I.T.fus G B.S n2 hn2 hdih hno2).1 B.t y B.t_order hy2
  set gg : G := (↑g : G) with hgg
  have hgt : gg * B.t * gg⁻¹ = y := by
    have h := hg
    calc gg * B.t * gg⁻¹ = (y * gg) * gg⁻¹ := by rw [hgg]; exact congrArg (· * gg⁻¹) h
      _ = y := by group
  -- ### Step 3: `y` normalizes `C_G(x)`
  have hyx : y⁻¹ * x * y = x⁻¹ := by simpa [hyinv] using hinv
  have hyx' : y * x⁻¹ * y⁻¹ = x := by
    have h2 : (y * x * y⁻¹)⁻¹ = x := by
      have := congrArg Inv.inv hinv
      simpa using this
    have e : (y * x * y⁻¹)⁻¹ = y * x⁻¹ * y⁻¹ := by group
    rwa [e] at h2
  have key : ∀ a ∈ Subgroup.centralizer ({x} : Set G),
      y * a * y⁻¹ ∈ Subgroup.centralizer ({x} : Set G) := by
    intro a ha
    rw [Subgroup.mem_centralizer_singleton_iff] at ha ⊢
    have ha'inv : x⁻¹ * a = a * x⁻¹ := by
      have h := congrArg (fun t => x⁻¹ * t * x⁻¹) ha
      simpa [mul_assoc] using h
    calc y * a * y⁻¹ * x = y * a * (y⁻¹ * x * y) * y⁻¹ := by group
      _ = y * a * x⁻¹ * y⁻¹ := by rw [hyx]
      _ = y * (a * x⁻¹) * y⁻¹ := by group
      _ = y * (x⁻¹ * a) * y⁻¹ := by rw [ha'inv]
      _ = (y * x⁻¹ * y⁻¹) * (y * a * y⁻¹) := by group
      _ = x * (y * a * y⁻¹) := by rw [hyx']
  have hyCxN : y ∈ Subgroup.normalizer (Subgroup.centralizer ({x} : Set G) : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro a
    refine ⟨key a, fun ha => ?_⟩
    have h := key (y * a * y⁻¹) ha
    have hconj : y * (y * a * y⁻¹) * y⁻¹ = a := by
      have h1 : y * (y * a * y⁻¹) * y⁻¹ = (y * y) * a * (y⁻¹ * y⁻¹) := by group
      have h2 : y⁻¹ * y⁻¹ = 1 := by rw [hyinv, hy]
      rw [h1, hy, h2]; group
    rwa [hconj] at h
  -- ### Step 4: `A = C_G(x) ⊓ C_G(y)` is nontrivial
  set A : Subgroup G := Subgroup.centralizer ({x} : Set G) ⊓ Subgroup.centralizer ({y} : Set G) with hAdef
  have hAodd : Odd (Nat.card A) :=
    hCxodd.of_dvd_nat (Subgroup.card_dvd_of_le inf_le_left)
  have hAne : A ≠ ⊥ := by
    intro hbot
    have hexσ : ∃ σ : ↥(Subgroup.centralizer ({x} : Set G)) →* ↥(Subgroup.centralizer ({x} : Set G)),
        ∀ a, ((σ a : ↥(Subgroup.centralizer ({x} : Set G))) : G) = y * (a : G) * y⁻¹ :=
      ⟨{ toFun := fun a => ⟨y * (a : G) * y⁻¹, key a a.2⟩,
         map_one' := by ext; simp,
         map_mul' := by intro a b; ext; simp only [Subgroup.coe_mul]; group },
       fun a => rfl⟩
    obtain ⟨σ, hσeq⟩ := hexσ
    have hσinj : Function.Injective σ := by
      intro a b hab
      have h : y * (a : G) * y⁻¹ = y * (b : G) * y⁻¹ := by rw [← hσeq a, ← hσeq b, hab]
      exact Subtype.ext (mul_left_cancel (mul_right_cancel h))
    have hσ2 : ∀ a, σ (σ a) = a := by
      intro a
      refine Subtype.ext ?_
      rw [hσeq (σ a), hσeq a]
      have h1 : y * (y * (a : G) * y⁻¹) * y⁻¹ = (y * y) * (a : G) * (y⁻¹ * y⁻¹) := by group
      have h2 : y⁻¹ * y⁻¹ = 1 := by rw [hyinv, hy]
      rw [h1, hy, h2]; group
    have hfix : ∀ a, σ a = a → a = 1 := by
      intro a ha
      have h1 : y * (a : G) * y⁻¹ = (a : G) := by rw [← hσeq a, ha]
      have hay : (a : G) * y = y * (a : G) := by
        calc (a : G) * y = (y * (a : G) * y⁻¹) * y := by rw [h1]
          _ = y * (a : G) := by group
      have hcy : (a : G) ∈ Subgroup.centralizer ({y} : Set G) := by
        rwa [Subgroup.mem_centralizer_singleton_iff]
      have : (a : G) ∈ A := ⟨a.2, hcy⟩
      rw [hbot] at this
      exact Subtype.ext (Subgroup.mem_bot.mp this)
    have hinvCx := jthreeInvEqOfFixedPointFree σ hσinj hσ2 hfix
    -- hence `y` inverts `U`
    have hUne : B.Hhat ≤ Subgroup.normalizer (B.U : Set G) :=
      (JthreeNormalizerU I hSetup hCount h89 hBc B h1 h4 D).ge
    have hUCx : B.U ≤ Subgroup.centralizer ({x} : Set G) :=
      Work.CORE3.OrderThreeLeCentralizer (hUne hxH) hx3 hU3
    have hyU : y ∈ Subgroup.normalizer (B.U : Set G) := by
      rw [Subgroup.mem_normalizer_iff]
      intro h
      constructor
      · intro hh
        have h2 : y * h * y⁻¹ = h⁻¹ := by
          have hh2 := congrArg (fun z : ↥(Subgroup.centralizer ({x} : Set G)) => (z : G))
            (hinvCx ⟨h, hUCx hh⟩)
          simpa [hσeq] using hh2
        rw [h2]; exact B.U.inv_mem hh
      · intro hh
        have h2 : y * (y * h * y⁻¹) * y⁻¹ = (y * h * y⁻¹)⁻¹ := by
          have hh2 := congrArg (fun z : ↥(Subgroup.centralizer ({x} : Set G)) => (z : G))
            (hinvCx ⟨y * h * y⁻¹, hUCx hh⟩)
          simpa [hσeq] using hh2
        have hh' : h = y * (y * h * y⁻¹) * y⁻¹ := by
          have h1 : y * (y * h * y⁻¹) * y⁻¹ = (y * y) * h * (y⁻¹ * y⁻¹) := by group
          have h3 : y⁻¹ * y⁻¹ = 1 := by rw [hyinv, hy]
          rw [h1, hy, h3]; group
        rw [hh', h2]
        exact B.U.inv_mem hh
    exact hyH ((JthreeNormalizerU I hSetup hCount h89 hBc B h1 h4 D) ▸ hyU)
  -- ### Step 5: `|A| = 3`
  have hconj_apply : ∀ a : G, ((MulAut.conj gg⁻¹).toMonoidHom) a = gg⁻¹ * a * gg := by
    intro a
    change (MulAut.conj gg⁻¹) a = gg⁻¹ * a * gg
    rw [MulAut.conj_apply, inv_inv]
  have hAconj_le : A.map (MulAut.conj gg⁻¹).toMonoidHom ≤ B.H := by
    intro z hz
    rw [Subgroup.mem_map] at hz
    obtain ⟨a, ha, rfl⟩ := hz
    have haCy : a ∈ Subgroup.centralizer ({y} : Set G) := (Subgroup.mem_inf.mp ha).2
    rw [Subgroup.mem_centralizer_singleton_iff] at haCy
    rw [Subgroup.mem_centralizer_singleton_iff]
    simp only [hconj_apply]
    calc gg⁻¹ * a * gg * B.t = gg⁻¹ * a * (gg * B.t * gg⁻¹) * gg := by group
      _ = gg⁻¹ * a * y * gg := by rw [hgt]
      _ = gg⁻¹ * (a * y) * gg := by group
      _ = gg⁻¹ * (y * a) * gg := by rw [haCy]
      _ = gg⁻¹ * (gg * B.t * gg⁻¹) * a * gg := by rw [← hgt]; group
      _ = B.t * (gg⁻¹ * a * gg) := by group
  have hAdvd24 : Nat.card A ∣ 24 := by
    have hcard : Nat.card ↥(A.map (MulAut.conj gg⁻¹).toMonoidHom) = Nat.card A :=
      Subgroup.card_map_of_injective (MulAut.conj gg⁻¹).injective
    rw [← hcard, ← jthreeCardHEq24 I hCount h89 hBc B h1 D]
    exact Subgroup.card_dvd_of_le hAconj_le
  have hAdvd3 : Nat.card A ∣ 3 := by
    have hcop : Nat.Coprime (Nat.card A) 8 := by
      rw [show (8 : ℕ) = 2 ^ 3 from rfl]
      exact (Nat.coprime_two_right.mpr hAodd).pow_right 3
    have h24 : Nat.card A ∣ 8 * 3 := by rw [show 8 * 3 = 24 from rfl]; exact hAdvd24
    exact hcop.dvd_of_dvd_mul_left h24
  have hAcard3 : Nat.card A = 3 := by
    rcases (Nat.dvd_prime Nat.prime_three).mp hAdvd3 with h | h
    · exact absurd (Subgroup.card_eq_one.mp h) hAne
    · exact h
  -- ### Step 6: finish
  have hWcard : Nat.card ↥(A.map (MulAut.conj gg⁻¹).toMonoidHom) = 3 := by
    rw [Subgroup.card_map_of_injective (MulAut.conj gg⁻¹).injective, hAcard3]
  have hWeq : A.map (MulAut.conj gg⁻¹).toMonoidHom = B.U :=
    jthreeEqUOfCardThree I hCount h89 hBc B h1 D hAconj_le hWcard
  refine ⟨gg, fun u hu => ?_⟩
  have hmem : gg * u * gg⁻¹ ∈ A := by
    have h1 : u ∈ A.map (MulAut.conj gg⁻¹).toMonoidHom := by rw [hWeq]; exact hu
    rw [Subgroup.mem_map] at h1
    obtain ⟨a, ha, haeq⟩ := h1
    have : gg * u * gg⁻¹ = a := by
      rw [← haeq]
      simp only [hconj_apply]
      group
    rw [this]; exact ha
  obtain ⟨hxC, hyC⟩ := Subgroup.mem_inf.mp hmem
  rw [Subgroup.mem_centralizer_singleton_iff] at hxC hyC
  exact ⟨hxC.symm, hyC.symm⟩

/-- The `J₃`-step in the form used by the target: the numerical input `|U| = 3` is supplied by
Bender's count data, and the oddness of `C_G(x)` by `Work.CORE3.JthreeCentralizerOddNC`. -/
theorem jthreeConjUOfOddFull (I : Case1Inputs) (hSetup : Case1bSetupProp)
    (hCount : Case1bCountProp) (hFive : Case1bFiveProp) (h89 : Case1bEightNineProp)
    (hBc : BenderCtx G) (B : BenderSetup G) (h1 : Case1 B) (h4 : IsFourGroup (pCoreIn 2 B.Hhat))
    (D : Case1bData B) {x y : G} (hxH : x ∈ B.Hhat) (hx3 : orderOf x = 3)
    (hxVU : x ∉ (pCoreIn 2 B.Hhat ⊔ B.U)) (hy2 : orderOf y = 2) (hyH : y ∉ B.Hhat)
    (hinv : y * x * y⁻¹ = x⁻¹) (hcnt : cosetInvCount B.Hhat y = 3) :
    ∃ k : G, ∀ u ∈ B.U, x * (k * u * k⁻¹) = (k * u * k⁻¹) * x ∧
                        y * (k * u * k⁻¹) = (k * u * k⁻¹) * y :=
  jthreeConjUOfOdd I hSetup hCount hFive h89 hBc B h1 h4 D hxH hx3 hxVU hy2 hyH hinv hcnt
    (_root_.Work.CORE3.JthreeCentralizerOddNC I hSetup hCount hFive h89 hBc B h1 h4 D
      (Work.CORE3.Work.CORE3.cardU_eq_three_of_case1b I hCount h89 hBc B h1 D).1
      hxH hx3 hxVU hy2 hyH hinv hcnt)


end JthreeOdd

/-- Design pass 5 (`Submission/Work/_design_gw/Core5.lean`, B81 p. 224): `b₃ = 0`.  If `y ∈ J₃`
(an involution `y ∉ Ĥ` whose coset contains exactly three involutions) then `X := I_Ĥ(y)` is a
subgroup of order 3 and `A := C_Ĥ(X)` has odd order (by (7), which needs (5),
`hFive : Case1bFiveProp`: `y` cannot invert a `2'`-subgroup `X ≠ 1` of `Ĥ` with `C_Ĥ(X)`,
`N_Ĥ(X)` of even order unless `n = 4`); since `y` does not invert `A` (it contains `K`),
`A₁ := C_A(y) ≠ 1` is conjugate to `U = K`, giving `y ∈ O₂(C_Ĥ(A₁))`, contrary to `[y, X] ≠ 1`. -/
theorem Case1bThree (I : Case1Inputs) (hSetup : Case1bSetupProp) (hCount : Case1bCountProp)
    (hFive : Case1bFiveProp) (h89 : Case1bEightNineProp) : Case1bThreeProp :=
  jthree_contradiction_of
    (fun G _ _ hBc B h1 h4 D x y hxH hx3 hxVU hy2 hyH hinv hcnt =>
      jthreeConjUOfOddFull I hSetup hCount hFive h89 hBc B h1 h4 D hxH hx3 hxVU hy2 hyH hinv
        hcnt)
    I hSetup hCount hFive h89

end Work.CORE3

end Work.CORE3


/-- The theorem at the namespace of the file path, for callers that do not want the nested name
(the statement is the same as `Work.CORE3.Work.CORE3.Work.CORE3.Case1bThree`). -/
theorem Case1bThree (I : Case1Inputs) (hSetup : Case1bSetupProp) (hCount : Case1bCountProp)
    (hFive : Case1bFiveProp) (h89 : Case1bEightNineProp) : Case1bThreeProp :=
  _root_.Work.CORE3.Work.CORE3.Work.CORE3.Case1bThree I hSetup hCount hFive h89
