import Submission.ZagierHoffmanProof.StepL203
import Submission.ZagierHoffmanProof.Counting

set_option autoImplicit false
set_option maxHeartbeats 2000000
open Polynomial RatFunc
open scoped BigOperators WithZero
open WithZero

/-!
# Step L204: positivity of `d(w)` and non-emptiness of the weight-`w` spanning sets

`d F w > 0` for every `w` (needed to make the rank equalities of Theorem D non-vacuous), and
`𝒯 F w`, `𝒯0 F w` are nonempty for every `w ≥ 1` (they contain the all-ones MZV, which is
`w`-admissible).  Neither needs the ABP machinery.
-/

namespace ZagierHoffmanPositiveChar

variable (F : Type*) [Field F] [Finite F] [DecidableEq (RatFunc F)]

/-- ★ `d F w > 0` for every weight `w` (in particular the dimension predicted by Zagier's
conjecture is at least `1`). -/
theorem d_pos : ∀ w : ℕ, 0 < d F w := by
  intro w
  induction w using Nat.strong_induction_on with
  | h w ih =>
    rcases Nat.eq_zero_or_pos w with h0 | hw
    · subst h0
      unfold d
      simp
    · rcases lt_or_ge w (Nat.card F) with hlt | hge
      · rw [d_eq_pow_two F hw hlt]
        positivity
      · rcases eq_or_lt_of_le hge with heq | hgt
        · rw [← heq, d_eq_pow_two_sub_one F]
          have hle : 1 ≤ Nat.card F - 1 := by have := card_ge_two F; omega
          have h2 : (2 : ℕ) ≤ 2 ^ (Nat.card F - 1) := by
            calc (2 : ℕ) = 2 ^ 1 := by norm_num
              _ ≤ 2 ^ (Nat.card F - 1) := Nat.pow_le_pow_right (by norm_num) hle
          omega
        · unfold d
          rw [if_neg (by omega : ¬ w = 0)]
          rw [if_neg (by omega : ¬ w ≤ Nat.card F - 1)]
          rw [if_neg (by omega : ¬ w = Nat.card F)]
          have hmem : 0 ∈ Finset.range (Nat.card F) :=
            Finset.mem_range.mpr (by have := card_ge_two F; omega)
          have hsingle := Finset.single_le_sum
            (f := fun i => d F (w - (i + 1))) (fun i _ => Nat.zero_le _) hmem
          have hprev : 0 < d F (w - 1) := ih (w - 1) (by omega)
          exact lt_of_lt_of_le hprev hsingle

/-- `d F w ≥ 1`. -/
lemma one_le_d (w : ℕ) : 1 ≤ d F w := d_pos F w

/-- The all-ones tuple of weight `w` is `w`-admissible. -/
lemma kAdmissible_onesTuple (w : ℕ) (hw : 1 ≤ w) :
    kAdmissible (Nat.card F) (onesTuple w) w := by
  constructor
  · intro x hx
    rw [pad0_of_lt (onesTuple w) hx]
    have h : (onesTuple w ⟨x, hx⟩ : ℕ) = 1 := rfl
    rw [h]
    have := card_ge_two F
    omega
  · rintro ⟨_, _, _, hlast⟩
    have h1 : (onesTuple w ⟨w - 1, by omega⟩ : ℕ) = 1 := rfl
    rw [h1] at hlast
    have := card_ge_two F
    omega

/-- ★ `ζ_A(1,…,1) ∈ 𝒯 F w` for `w ≥ 1`. -/
lemma onesTuple_mem_T (w : ℕ) (hw : 1 ≤ w) : ζ_A F (onesTuple w) ∈ 𝒯 F w :=
  admissible_mem_𝒯 F w (by omega) (onesTuple w) (weight_onesTuple w)
    (kAdmissible_onesTuple F w hw)

/-- `ζ_A(1,…,1) ∈ 𝒯0_aux F w ⟨w,_⟩` (all entries are `1 < q`). -/
lemma onesTuple_mem_T0_aux_general (w : ℕ) (hw : 1 ≤ w) :
    ζ_A F (onesTuple w) ∈ 𝒯0_aux F w ⟨w, by omega⟩ := by
  rw [mem_𝒯0_aux_iff F w ⟨w, by omega⟩]
  refine ⟨onesTuple w, onesTuple_mem_𝔖 w, fun i => ?_, rfl⟩
  have h : (onesTuple w i : ℕ) = 1 := rfl
  rw [h]
  have := card_ge_two F
  omega

/-- ★ `ζ_A(1,…,1) ∈ 𝒯0 F w` for `w ≥ 1`. -/
lemma onesTuple_mem_T0 (w : ℕ) (hw : 1 ≤ w) : ζ_A F (onesTuple w) ∈ 𝒯0 F w := by
  rw [mem_𝒯0_iff F w]
  exact ⟨⟨w, by omega⟩, onesTuple_mem_T0_aux_general F w hw⟩

/-- ★★ `𝒯 F w` is nonempty for `w ≥ 1`. -/
theorem T_nonempty (w : ℕ) (hw : 1 ≤ w) : (𝒯 F w).Nonempty :=
  ⟨ζ_A F (onesTuple w), onesTuple_mem_T F w hw⟩

/-- ★★ `𝒯0 F w` is nonempty for `w ≥ 1`. -/
theorem T0_nonempty (w : ℕ) (hw : 1 ≤ w) : (𝒯0 F w).Nonempty :=
  ⟨ζ_A F (onesTuple w), onesTuple_mem_T0 F w hw⟩

/-- ★ `𝒯 F w` is finite (`w ≥ 1`): it injects into the finite set of Hoffmann shapes. -/
theorem T_finite (w : ℕ) (hw : 1 ≤ w) : Set.Finite (𝒯 F w) := by
  have hFin : Finite {x : RatFunc.CompletionAtInfty F // x ∈ 𝒯 F w} :=
    Finite.of_injective (valueToShape F w hw) (valueToShape_inj F w hw)
  letI := hFin
  exact Set.toFinite (𝒯 F w)

/-- ★ `𝒯0 F w` is finite (`w ≥ 1`) — it is contained in `𝒯 F w`. -/
theorem T0_finite (w : ℕ) (hw : 1 ≤ w) : Set.Finite (𝒯0 F w) :=
  (T_finite F w hw).subset (𝒯0_subset_𝒯 F w)

/-- ★★ `ncard (𝒯 F w) ≥ 1` for `w ≥ 1`. -/
theorem ncard_T_pos (w : ℕ) (hw : 1 ≤ w) : 0 < Set.ncard (𝒯 F w) :=
  (Set.ncard_pos (T_finite F w hw)).mpr (T_nonempty F w hw)

/-- ★★ `ncard (𝒯0 F w) ≥ 1` for `w ≥ 1`. -/
theorem ncard_T0_pos (w : ℕ) (hw : 1 ≤ w) : 0 < Set.ncard (𝒯0 F w) :=
  (Set.ncard_pos (T0_finite F w hw)).mpr (T0_nonempty F w hw)

/-- `1 ≤ ncard (𝒯 F w)` for `w ≥ 1`. -/
theorem one_le_ncard_T (w : ℕ) (hw : 1 ≤ w) : 1 ≤ Set.ncard (𝒯 F w) := ncard_T_pos F w hw

/-- `1 ≤ ncard (𝒯0 F w)` for `w ≥ 1`. -/
theorem one_le_ncard_T0 (w : ℕ) (hw : 1 ≤ w) : 1 ≤ Set.ncard (𝒯0 F w) := ncard_T0_pos F w hw

end ZagierHoffmanPositiveChar
