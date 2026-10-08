import Mathlib
import Submission.Work.CharCore.Main

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.Hering.AppVII

/-- The sum over the group of the squared norm of an irreducible character is the order of
the group.  This is the first orthogonality relation `cfInner χ χ = 1` written out, using
`z * conj z = (normSq z : ℂ)`. -/
theorem part2_count_irrNorm {G : Type*} [Group G] [Fintype G] {χ : G → ℂ}
    (hχ : χ ∈ Work.CharCore.Irr G) :
    ∑ g : G, Complex.normSq (χ g) = (Nat.card G : ℝ) := by
  -- rewrite `χ x * conj (χ x)` as the real number `normSq (χ x)`
  have hsum : (∑ x : G, χ x * (starRingEnd ℂ) (χ x))
      = ((∑ x : G, Complex.normSq (χ x) : ℝ) : ℂ) := by
    rw [Complex.ofReal_sum]
    exact Finset.sum_congr rfl (fun x _ => Complex.mul_conj (χ x))
  have h2 := Work.CharCore.cfInner_self_mem_Irr hχ
  rw [Work.CharCore.cfInner, hsum] at h2
  -- `h2 : (|G| : ℂ)⁻¹ * (∑ ‖χ‖² : ℂ) = 1`; multiply by `|G|`
  have hc : ((Fintype.card G : ℕ) : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have h3 : ((∑ x : G, Complex.normSq (χ x) : ℝ) : ℂ) = (Fintype.card G : ℂ) := by
    have h4 := congrArg (fun t : ℂ => (Fintype.card G : ℂ) * t) h2
    simp only [mul_one] at h4
    rw [← mul_assoc, mul_inv_cancel₀ hc, one_mul] at h4
    exact h4
  have h5 : (∑ x : G, Complex.normSq (χ x)) = (Fintype.card G : ℝ) :=
    Complex.ofReal_injective h3
  rw [h5, Nat.card_eq_fintype_card]

end Work.Hering.AppVII
