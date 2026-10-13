/-
  annals_wilkies_conjecture, AREA E3K (`Submission.Work.WilE3K`): the *branch constant* of the K1
  lift (design `sources/wilkiesE3E9/wilkies_E3E9_gaps.md` §GAP 1, FIX-1).

  On a *convex* set `D ⊆ ℝ` on which `cos` does not vanish, `D` lies inside a single branch
  `(kπ - π/2, kπ + π/2)` of `tan`; this is what makes the lifted graph equation
  `arctan t - (y - kπ) = 0` available (without the `kπ` the equation is false off the principal
  branch).  For the lift one applies this to `D = ℓ_j '' D₀`, which is convex as the image of a
  convex set under an affine map, and where `cos ≠ 0` follows from `dom j` and the derivative
  relation `(tan)' = 1 + tan²`.
-/
import Mathlib

set_option autoImplicit false
noncomputable section
open Classical
namespace Work.WilE3K

/-- **The branch of a point off the poles.**  For `y` with `cos y ≠ 0` there is an integer `k`
with `y - kπ ∈ (-(π/2), π/2)`. -/
theorem exists_int_sub_mul_pi_mem_Ioo (y : ℝ) (hy : Real.cos y ≠ 0) :
    ∃ k : ℤ, -(Real.pi / 2) < y - k * Real.pi ∧ y - k * Real.pi < Real.pi / 2 := by
  have hpi : 0 < Real.pi := Real.pi_pos
  set k : ℤ := ⌊(y + Real.pi / 2) / Real.pi⌋ with hk
  have h1 : (k : ℝ) ≤ (y + Real.pi / 2) / Real.pi := Int.floor_le _
  have h2 : (y + Real.pi / 2) / Real.pi < (k : ℝ) + 1 := Int.lt_floor_add_one _
  have hmul1 : (k : ℝ) * Real.pi ≤ y + Real.pi / 2 := by
    have := mul_le_mul_of_nonneg_right h1 (le_of_lt hpi)
    rwa [div_mul_cancel₀ _ (ne_of_gt hpi)] at this
  have hmul2 : y + Real.pi / 2 < ((k : ℝ) + 1) * Real.pi := by
    have := mul_lt_mul_of_pos_right h2 hpi
    rwa [div_mul_cancel₀ _ (ne_of_gt hpi)] at this
  have hlo : -(Real.pi / 2) ≤ y - (k : ℝ) * Real.pi := by linarith
  have hhi : y - (k : ℝ) * Real.pi < Real.pi / 2 := by linarith
  refine ⟨k, lt_of_le_of_ne hlo ?_, hhi⟩
  intro heq
  apply hy
  have hy' : y = -(Real.pi / 2) + (k : ℝ) * Real.pi := by linarith
  rw [hy', Real.cos_add_int_mul_pi, Real.cos_neg, Real.cos_pi_div_two, mul_zero]

/-- **The branch is constant on a convex set off the poles** (FIX-1 of the review). -/
theorem exists_branch_sub {D : Set ℝ} (hD : Convex ℝ D) (hcos : ∀ y ∈ D, Real.cos y ≠ 0) :
    ∃ k : ℤ, ∀ y ∈ D, -(Real.pi / 2) < y - k * Real.pi ∧ y - k * Real.pi < Real.pi / 2 := by
  rcases D.eq_empty_or_nonempty with h | ⟨y₀, hy₀⟩
  · exact ⟨0, by simp [h]⟩
  obtain ⟨k, hk1, hk2⟩ := exists_int_sub_mul_pi_mem_Ioo y₀ (hcos y₀ hy₀)
  refine ⟨k, fun y hy => ⟨?_, ?_⟩⟩
  · by_contra hlt
    push Not at hlt
    have hz : -(Real.pi / 2) + (k : ℝ) * Real.pi ∈ D := by
      refine hD.ordConnected.out hy hy₀ ?_
      refine ⟨by linarith, by linarith⟩
    have hcos' := hcos _ hz
    apply hcos'
    have : -(Real.pi / 2) + (k : ℝ) * Real.pi = -(Real.pi / 2) + (k : ℝ) * Real.pi := rfl
    rw [this, Real.cos_add_int_mul_pi, Real.cos_neg, Real.cos_pi_div_two, mul_zero]
  · by_contra hlt
    push Not at hlt
    have hz : Real.pi / 2 + (k : ℝ) * Real.pi ∈ D := by
      refine hD.ordConnected.out hy₀ hy ?_
      refine ⟨by linarith, by linarith⟩
    have hcos' := hcos _ hz
    apply hcos'
    rw [Real.cos_add_int_mul_pi, Real.cos_pi_div_two, mul_zero]

end Work.WilE3K
