import Mathlib
import Submission.Work.HP.Q44Setup
import Submission.Work.HP.Defs
import Submission.Work.HP.Lat.card_Mon
import Submission.Work.HP.MDBasic.finite_sets

/-!
# The number of nonzero coefficient vectors of small Euclidean norm

For `(d,n) = (4,4)` there are `N_{4,4} = 70` quartic monomials, so a coefficient vector
`c : Mon 4 4 → ℤ` has `70` coordinates.  Bounding each coordinate by `M` (a coordinate is at
most the Euclidean norm in absolute value) puts the set
`{c : Mon 4 4 → ℤ | c ≠ 0 ∧ eNorm c ≤ M}` inside the box `[-(⌈M⌉₊), ⌈M⌉₊]^{70}`, which has
`(2⌈M⌉₊ + 1)^{70} ≤ (5M)^{70} = 5^{70} M^{70}` elements for `M ≥ 1`.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section

namespace Work.HP.Q44Main

open Work.HP

/-- The number of nonzero coefficient vectors `c : Mon 4 4 → ℤ` of Euclidean norm at most `M`
is `≪ M ^ 70` (there are `N_{4,4} = 70` monomials). -/
theorem witSet_ncard_le :
    ∃ K : ℝ, 0 < K ∧ ∀ M : ℝ, 1 ≤ M →
      (({c : Mon 4 4 → ℤ | c ≠ 0 ∧ eNorm c ≤ M} : Set (Mon 4 4 → ℤ)).ncard : ℝ)
        ≤ K * M ^ 70 := by
  refine ⟨5 ^ 70, by positivity, ?_⟩
  intro M hM
  set B : Finset (Mon 4 4 → ℤ) :=
    Fintype.piFinset (fun _ : Mon 4 4 => Finset.Icc (-(⌈M⌉₊ : ℤ)) (⌈M⌉₊ : ℤ)) with hB
  have hsub : ({c : Mon 4 4 → ℤ | c ≠ 0 ∧ eNorm c ≤ M} : Set (Mon 4 4 → ℤ)) ⊆ ↑B := by
    intro c hc
    rw [hB, Finset.mem_coe, Fintype.mem_piFinset]
    intro j
    rw [Finset.mem_Icc]
    have h1 : |(c j : ℝ)| ≤ M := le_trans (MDBasic.abs_apply_le_eNorm c j) hc.2
    obtain ⟨h2, h3⟩ := abs_le.1 h1
    constructor
    · have h4 : -(⌈M⌉₊ : ℝ) ≤ (c j : ℝ) := by
        have := Nat.le_ceil M
        linarith
      exact_mod_cast h4
    · have h5 : (c j : ℝ) ≤ (⌈M⌉₊ : ℝ) := le_trans h3 (Nat.le_ceil M)
      exact_mod_cast h5
  have h1 : (({c : Mon 4 4 → ℤ | c ≠ 0 ∧ eNorm c ≤ M} : Set (Mon 4 4 → ℤ)).ncard : ℝ)
      ≤ (B.card : ℝ) := by
    have hle := Set.ncard_le_ncard hsub (Finset.finite_toSet B)
    rw [Set.ncard_coe_finset] at hle
    exact_mod_cast hle
  have hcard : B.card = (2 * ⌈M⌉₊ + 1) ^ 70 := by
    rw [hB, Fintype.card_piFinset]
    have hc1 : ∀ i : Mon 4 4,
        (Finset.Icc (-(⌈M⌉₊ : ℤ)) (⌈M⌉₊ : ℤ)).card = 2 * ⌈M⌉₊ + 1 := by
      intro _
      rw [Int.card_Icc]
      have h2 : ((⌈M⌉₊ : ℤ) + 1 - -(⌈M⌉₊ : ℤ)) = ((2 * ⌈M⌉₊ + 1 : ℕ) : ℤ) := by
        push_cast; ring
      rw [h2, Int.toNat_natCast]
    calc ∏ i : Mon 4 4, (Finset.Icc (-(⌈M⌉₊ : ℤ)) (⌈M⌉₊ : ℤ)).card
        = ∏ _i : Mon 4 4, (2 * ⌈M⌉₊ + 1) := Finset.prod_congr rfl (fun i _ => hc1 i)
      _ = (2 * ⌈M⌉₊ + 1) ^ 70 := by
          rw [Finset.prod_const, Finset.card_univ, Lat.card_Mon 4 4]
          norm_num [Nat.choose]
  have hcardR : ((B.card : ℝ)) ≤ 5 ^ 70 * M ^ 70 := by
    rw [hcard, Nat.cast_pow]
    have hM0 : (0 : ℝ) ≤ M := le_trans zero_le_one hM
    have hceil2 : (⌈M⌉₊ : ℝ) < M + 1 := Nat.ceil_lt_add_one hM0
    have hcast : (((2 * ⌈M⌉₊ + 1 : ℕ) : ℝ)) = 2 * (⌈M⌉₊ : ℝ) + 1 := by push_cast; ring
    have hb : (((2 * ⌈M⌉₊ + 1 : ℕ) : ℝ)) ≤ 5 * M := by
      rw [hcast]; linarith [hceil2, hM]
    calc (((2 * ⌈M⌉₊ + 1 : ℕ) : ℝ)) ^ 70
        ≤ (5 * M) ^ 70 := pow_le_pow_left₀ (by positivity) hb 70
      _ = 5 ^ 70 * M ^ 70 := by rw [mul_pow]
  exact le_trans h1 hcardR

end Work.HP.Q44Main
