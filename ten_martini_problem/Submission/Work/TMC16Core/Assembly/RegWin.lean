import Mathlib
import Submission.Work.TMC16Core.Defs
import Submission.Work.TMC16Core.Core.uni_nonres3_havoid
import Submission.Work.TMC16Core.Assembly.S0

/-!
# `RegWin`: regularity with an explicit window and margin (lead design C16_CLOSE_LEAD §2)

`RegWin` is `IsRegularBig` with the witnessing interval pinned to exactly `K` sites and an
explicit margin `g` from the site `y` to both endpoints.  It is the interface between the three
branch lemmas (`s0_reg`, `res_reg`, `nr_case1_full`) and the glue:

* the branch lemmas produce `RegWin` (their constructions give a *named* window);
* `RegWin.toBig` turns it into `IsRegularBig`, which is what `RegFamily` demands.

Also here: `bG`, the level function of the glue, and the mirrored `s = 0` windows
(`W1s0L`/`W2s0L`) for the case `y < M = m qₙ`.
-/

namespace Work.TMC16Core.Assembly

open Work.TMC16Core
open Work.TMC16Core.Core
open Filter

noncomputable section

/-! ## `RegWin` and its passage to `IsRegularBig` -/

/-- Regularity with an explicit window of exactly `K` sites and explicit margin `g`. -/
def RegWin (α lam θ : ℝ) (E : ℂ) (γ g : ℝ) (K : ℕ) (y : ℤ) : Prop :=
  ∃ x₁ : ℤ,
    x₁ ≤ y ∧ y ≤ x₁ + (K : ℤ) - 1 ∧
    g ≤ ((y - x₁ : ℤ) : ℝ) ∧ g ≤ ((x₁ + (K : ℤ) - 1 - y : ℤ) : ℝ) ∧
    (dirMat α lam (θ + (x₁ : ℝ) * α) E K).det ≠ 0 ∧
    ‖G α lam θ E x₁ (x₁ + (K : ℤ) - 1) y x₁‖ <
      Real.exp (-(γ * ((y - x₁ : ℤ) : ℝ))) ∧
    ‖G α lam θ E x₁ (x₁ + (K : ℤ) - 1) y (x₁ + (K : ℤ) - 1)‖ <
      Real.exp (-(γ * ((x₁ + (K : ℤ) - 1 - y : ℤ) : ℝ)))

theorem RegWin.toBig {α lam θ γ g γ' q : ℝ} {E : ℂ} {K : ℕ} {y : ℤ}
    (h : RegWin α lam θ E γ g K y) (hK : (K : ℝ) ≤ 40 * g) (hq : q ≤ (K : ℝ))
    (hγ : γ' ≤ γ) (hγ' : 0 ≤ γ') : IsRegularBig α lam θ E γ' q y := by
  obtain ⟨x₁, h1, h2, h3, h4, h5, h6, h7⟩ := h
  have hlen : ((x₁ + (K : ℤ) - 1) - x₁ + 1 : ℤ) = (K : ℤ) := by ring
  have h3' : g ≤ (y : ℝ) - (x₁ : ℝ) := by
    have := h3; push_cast at this; linarith
  have h4' : g ≤ (x₁ : ℝ) + (K : ℝ) - 1 - (y : ℝ) := by
    have := h4; push_cast at this; linarith
  have h40a : (40 : ℝ) * ((y - x₁ : ℤ) : ℝ) ≥ ((x₁ + (K : ℤ) - 1 - x₁ + 1 : ℤ) : ℝ) := by
    rw [hlen]; push_cast; linarith
  have h40b : (40 : ℝ) * ((x₁ + (K : ℤ) - 1 - y : ℤ) : ℝ)
      ≥ ((x₁ + (K : ℤ) - 1 - x₁ + 1 : ℤ) : ℝ) := by
    rw [hlen]; push_cast; linarith
  refine ⟨x₁, x₁ + (K : ℤ) - 1, h1, h2, ?_, h40a, h40b, ?_, ?_, ?_⟩
  · rw [hlen]; exact_mod_cast hq
  · rw [hlen]; exact h5
  · refine lt_of_lt_of_le h6 (Real.exp_le_exp.mpr ?_)
    have hd : (0 : ℝ) ≤ ((y - x₁ : ℤ) : ℝ) := by
      have hg0 : 0 ≤ g := by
        have hK0 : (0 : ℝ) ≤ (K : ℝ) := by positivity
        linarith
      linarith
    have hkey : -γ * ((y - x₁ : ℤ) : ℝ) ≤ -γ' * ((y - x₁ : ℤ) : ℝ) := by
      nlinarith [hd, hγ, hγ']
    linarith
  · refine lt_of_lt_of_le h7 (Real.exp_le_exp.mpr ?_)
    have hd : (0 : ℝ) ≤ ((x₁ + (K : ℤ) - 1 - y : ℤ) : ℝ) := by
      have hg0 : 0 ≤ g := by
        have hK0 : (0 : ℝ) ≤ (K : ℝ) := by positivity
        linarith
      linarith
    have hkey : -γ * ((x₁ + (K : ℤ) - 1 - y : ℤ) : ℝ)
        ≤ -γ' * ((x₁ + (K : ℤ) - 1 - y : ℤ) : ℝ) := by
      nlinarith [hd, hγ, hγ']
    linarith

/-! ## The level function `bG` and the mirrored `s = 0` windows -/

/-- The level function of the glue: `bG n = max(qₙ^{8/9}, q(n-1)/20 + 3)`. -/
def bG (q : ℕ → ℕ) (n : ℕ) : ℝ :=
  max ((q n : ℝ) ^ (8 / 9 : ℝ)) ((q (n - 1) : ℝ) / 20 + 3)

/-- The mirror image (`x ↦ -x - (H-2)`) of `W1s0 a U`, of `2U` sites. -/
def W1s0L (a : ℤ) (U H : ℕ) : Finset ℤ :=
  Finset.Icc (-a - 2 * (U : ℤ) - (H : ℤ) + 3) (-a - (H : ℤ) + 2)

/-- The mirror image of `W2s0 a U H (-M)`, the translate by `M` of the complementary interval. -/
def W2s0L (a : ℤ) (U H : ℕ) (M : ℤ) : Finset ℤ :=
  Finset.Icc (M - a - 2 * (H : ℤ) + 3) (M - a - 2 * (U : ℤ) - (H : ℤ) + 2)

theorem mem_W1s0L_iff {a x : ℤ} {U H : ℕ} :
    x ∈ W1s0L a U H ↔ (-x - ((H : ℤ) - 2)) ∈ W1s0 a U := by
  simp only [W1s0L, W1s0, Finset.mem_Icc]
  constructor <;> intro h <;> constructor <;> omega

theorem mem_W2s0L_iff {a x M : ℤ} {U H : ℕ} :
    x ∈ W2s0L a U H M ↔ (-x - ((H : ℤ) - 2)) ∈ W2s0 a U H (-M) := by
  simp only [W2s0L, W2s0, Finset.mem_Icc]
  constructor <;> intro h <;> constructor <;> omega

/-! ## Symmetry of the exceptional set -/

theorem theta_neg {α θ : ℝ} (h : θ ∉ Theta α) : -θ ∉ Theta α := by
  rw [Theta, Set.mem_setOf_eq, not_or, not_or] at h
  obtain ⟨h1, h2, h3⟩ := h
  have keyT : ∃ a : ℤ, ∀ b : ℤ, a ≤ b →
      (((b.natAbs : ℕ)) : ℝ)⁻¹ ^ 2 ≤ fracDist (2 * θ + (b : ℝ) * α) := by
    rw [frequently_atTop] at h1
    push_neg at h1
    exact h1
  have keyB : ∃ a : ℤ, ∀ b : ℤ, b ≤ a →
      (((b.natAbs : ℕ)) : ℝ)⁻¹ ^ 2 ≤ fracDist (2 * θ + (b : ℝ) * α) := by
    rw [frequently_atBot] at h2
    push_neg at h2
    exact h2
  rw [Theta, Set.mem_setOf_eq, not_or, not_or]
  refine ⟨?_, ?_, ?_⟩
  · intro hc
    rw [frequently_atTop] at hc
    obtain ⟨a, ha⟩ := keyB
    obtain ⟨b, hb1, hb2⟩ := hc (-a)
    have hb1' : -b ≤ a := by omega
    have hh := ha (-b) hb1'
    have hbn : ((((-b).natAbs : ℕ)) : ℝ) = (((b.natAbs : ℕ)) : ℝ) := by simp
    rw [hbn] at hh
    have he : 2 * (-θ) + (b : ℝ) * α = -(2 * θ + ((-b : ℤ) : ℝ) * α) := by push_cast; ring
    rw [he, Core.fracDist_neg] at hb2
    linarith
  · intro hc
    rw [frequently_atBot] at hc
    obtain ⟨a, ha⟩ := keyT
    obtain ⟨b, hb1, hb2⟩ := hc (-a)
    have hb1' : a ≤ -b := by omega
    have hh := ha (-b) hb1'
    have hbn : ((((-b).natAbs : ℕ)) : ℝ) = (((b.natAbs : ℕ)) : ℝ) := by simp
    rw [hbn] at hh
    have he : 2 * (-θ) + (b : ℝ) * α = -(2 * θ + ((-b : ℤ) : ℝ) * α) := by push_cast; ring
    rw [he, Core.fracDist_neg] at hb2
    linarith
  · rintro ⟨m, z, hz⟩
    exact h3 ⟨-m, -z, by push_cast at hz ⊢; linarith⟩

end

end Work.TMC16Core.Assembly
