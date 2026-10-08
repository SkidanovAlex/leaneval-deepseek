import Mathlib
import Submission.Work.CharCore.Basic
import Submission.Work.CharCore.irr_orthonormal
import Submission.Work.CharCore.classFun_eq_sum_irr

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.CharCore

/-- The inner product of the regular character with an irreducible character `χ` is the
degree of `χ`.

This is the classical computation `⟨reg, χ⟩ = (1/|G|) · |G| · conj (χ 1) = χ(1)`, since the
regular character is supported at `1` and `χ 1 = irrDeg χ` is a natural number, hence fixed
by complex conjugation. -/
theorem cfInner_regularChar {G : Type*} [Group G] [Fintype G] {χ : G → ℂ} (hχ : χ ∈ Irr G) :
    cfInner (regularChar G) χ = (irrDeg χ : ℂ) := by
  have hcard : (Nat.card G : ℂ) ≠ 0 := by
    rw [← Fintype.card_eq_nat_card]
    exact Nat.cast_ne_zero.mpr
      (Nat.pos_iff_ne_zero.mp (Fintype.card_pos_iff.mpr ⟨1⟩))
  have hsum : (∑ x : G, regularChar G x * starRingEnd ℂ (χ x))
      = (Nat.card G : ℂ) * starRingEnd ℂ (χ 1) := by
    rw [Finset.sum_eq_single 1]
    · simp [regularChar]
    · intro b _ hb
      simp [regularChar, hb]
    · intro h
      exact absurd (Finset.mem_univ 1) h
  rw [cfInner_apply, hsum, Fintype.card_eq_nat_card]
  have hstar1 : starRingEnd ℂ (χ 1) = (irrDeg χ : ℂ) := by
    rw [irrDeg_spec hχ, starRingEnd_apply, star_natCast]
  rw [hstar1, ← mul_assoc, inv_mul_cancel₀ hcard, one_mul]

end Work.CharCore
