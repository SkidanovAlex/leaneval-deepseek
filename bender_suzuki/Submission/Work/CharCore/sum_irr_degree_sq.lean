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

/-- **Sum of squares of the degrees of the irreducible complex characters.**
The regular character `g ↦ |G|` if `g = 1` and `0` otherwise is a class function, hence by
`Work.CharCore.classFun_eq_sum_irr` it is `∑ χ ∈ Irr G, ⟨reg, χ⟩ • χ`.  Its inner product
with `χ ∈ Irr G` is `χ 1`, and evaluating the resulting identity at `1` gives
`|G| = ∑ χ ∈ Irr G, χ 1 ^ 2`. -/
theorem sum_irr_degree_sq {G : Type*} [Group G] [Fintype G] :
    ∑ χ ∈ Irr G, χ 1 ^ 2 = (Nat.card G : ℂ) := by
  classical
  rw [← Fintype.card_eq_nat_card]
  set regFun : G → ℂ := fun g => if g = 1 then (Fintype.card G : ℂ) else 0 with hreg
  have hregclass : IsClassFun regFun := by
    intro g h
    have hiff : h * g * h⁻¹ = 1 ↔ g = 1 := by
      constructor
      · intro hc
        have := congrArg (fun t => h⁻¹ * t * h) hc
        simpa [mul_assoc] using this
      · intro hc; subst hc; simp
    simp only [hreg]
    rw [hiff]
  have hcard : (Fintype.card G : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hcf : ∀ χ ∈ Irr G, cfInner regFun χ = χ 1 := by
    intro χ hχ
    have hsum : (∑ x : G, regFun x * starRingEnd ℂ (χ x))
        = (Fintype.card G : ℂ) * starRingEnd ℂ (χ 1) := by
      rw [Finset.sum_eq_single 1]
      · simp [hreg]
      · intro b _ hb
        simp [hreg, hb]
      · intro h; exact absurd (Finset.mem_univ 1) h
    rw [cfInner, hsum, ← mul_assoc, inv_mul_cancel₀ hcard, one_mul]
    obtain ⟨d, hd⟩ := exists_natCast_apply_one hχ
    rw [hd]; simp
  have hkey := classFun_eq_sum_irr (f := regFun) hregclass
  have hreg1 : regFun 1 = (Fintype.card G : ℂ) := by simp [hreg]
  have h1 := congrFun hkey 1
  rw [hreg1] at h1
  rw [h1, Finset.sum_apply]
  refine Finset.sum_congr rfl fun χ hχ => ?_
  rw [Pi.smul_apply, smul_eq_mul, hcf χ hχ]
  ring

end Work.CharCore
