import Mathlib
import Submission.Work.LinnikBurgess.gaussTwoLocal_defs
import Submission.Work.LinnikAreas.LocalCorr.sum_zmod_val_pow_eq
import Submission.Work.LinnikBurgess.zmod_char_val

open scoped BigOperators
open Work.LinnikAreas.LocalCorr

-- `hK : 1 ≤ K` is redundant for the statement (only `p ≠ 0` is needed); keep the linter quiet.
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

namespace Work.LinnikBurgess

/-- On the kernel of `2 * γ`, the quadratic term `γ * h ^ 2` vanishes: for odd `p`, `2` is a unit
of `ZMod (p ^ K)`, so `(2 * γ) * h = 0` gives `2 * (γ * h ^ 2) = ((2 * γ) * h) * h = 0` and hence
`γ * h ^ 2 = 0`. -/
lemma kernel_mul_sq_eq_zero {p K : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {γ h : ZMod (p ^ K)}
    (hh : (2 * γ) * h = 0) : γ * h ^ 2 = 0 := by
  have hodd : Odd (p ^ K) := ((Fact.out : p.Prime).odd_of_ne_two hp2).pow
  have hcop : Nat.Coprime 2 (p ^ K) := Nat.coprime_two_left.mpr hodd
  have hunit : IsUnit (2 : ZMod (p ^ K)) :=
    ⟨ZMod.unitOfCoprime 2 hcop, by simp [ZMod.coe_unitOfCoprime]⟩
  have h2 : (2 : ZMod (p ^ K)) * (γ * h ^ 2) = 0 := by
    have hmul : ((2 * γ) * h) * h = 0 := by rw [hh, zero_mul]
    rw [← hmul]; ring
  exact (hunit.mul_right_eq_zero).mp h2

/-- **Norm-square identity for the quadratic Gauss sum.**  For an odd prime `p`, `K ≥ 1`, a
primitive `p^K`-th root of unity `θ` and `α γ : ZMod (p^K)`, the product of the complete
quadratic Gauss sum `G = ∑_w θ^((α w + γ w²).val)` with its conjugate is
`p^K · ∑_{h : 2γh = 0} θ^((α h).val)`.

Proof: expand `G · conj G` as a double sum `∑_w ∑_{w'} θ^((f(w) - f(w')).val)` (using that
`w ↦ θ^w.val` is an additive character and `conj(θ^n) = θ^{-n}`); substitute `w = w' + h`, which
gives `f(w) - f(w') = (α h + γ h²) + 2γ h w'`; the inner sum `∑_{w'} θ^((2γh)·w').val` is `p^K`
when `2γh = 0` and `0` otherwise (`sum_zmod_val_pow_eq`), and on the kernel `γ h² = 0` so that
`α h + γ h² = α h`. -/
theorem gaussQuad_mul_star {p K : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (hK : 1 ≤ K)
    {θ : ℂ} (hθ : IsPrimitiveRoot θ (p ^ K)) (α γ : ZMod (p ^ K)) :
    gaussQuad p K θ α γ * star (gaussQuad p K θ α γ)
      = ((p ^ K : ℕ) : ℂ)
        * (∑ h : ZMod (p ^ K), if (2 * γ) * h = 0 then θ ^ ((α * h).val) else 0) := by
  classical
  have hp0 : p ^ K ≠ 0 := pow_ne_zero K (Fact.out : p.Prime).ne_zero
  haveI : NeZero (p ^ K) := ⟨hp0⟩
  -- ### Step 1: expand the product as a double sum with a single `.val`
  have hsplit : gaussQuad p K θ α γ * star (gaussQuad p K θ α γ)
      = ∑ w : ZMod (p ^ K), ∑ w' : ZMod (p ^ K),
          θ ^ (((α * w + γ * w ^ 2) + -(α * w' + γ * w' ^ 2)).val) := by
    rw [gaussQuad, star_sum, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun w _ => Finset.sum_congr rfl fun w' _ => ?_
    rw [zmod_pow_val_star hp0 hθ]
    exact (zmod_pow_val_add hθ _ _).symm
  -- ### Step 2: reindex `w = w' + h`
  have hreindex : (∑ w : ZMod (p ^ K), ∑ w' : ZMod (p ^ K),
          θ ^ (((α * w + γ * w ^ 2) + -(α * w' + γ * w' ^ 2)).val))
      = ∑ h : ZMod (p ^ K), ∑ w' : ZMod (p ^ K),
          θ ^ (((α * h + γ * h ^ 2) + ((2 * γ) * h) * w').val) := by
    have h1 : (∑ w : ZMod (p ^ K), ∑ w' : ZMod (p ^ K),
            θ ^ (((α * w + γ * w ^ 2) + -(α * w' + γ * w' ^ 2)).val))
        = ∑ w' : ZMod (p ^ K), ∑ w : ZMod (p ^ K),
            θ ^ (((α * w + γ * w ^ 2) + -(α * w' + γ * w' ^ 2)).val) := Finset.sum_comm
    have h2 : (∑ w' : ZMod (p ^ K), ∑ w : ZMod (p ^ K),
            θ ^ (((α * w + γ * w ^ 2) + -(α * w' + γ * w' ^ 2)).val))
        = ∑ w' : ZMod (p ^ K), ∑ h : ZMod (p ^ K),
            θ ^ (((α * h + γ * h ^ 2) + ((2 * γ) * h) * w').val) := by
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [← Equiv.sum_comp (Equiv.addRight a)
        (fun w => θ ^ (((α * w + γ * w ^ 2) + -(α * a + γ * a ^ 2)).val))]
      simp only [Equiv.coe_addRight]
      refine Finset.sum_congr rfl fun b _ => ?_
      apply congrArg (fun z : ZMod (p ^ K) => θ ^ z.val)
      ring
    have h3 : (∑ w' : ZMod (p ^ K), ∑ h : ZMod (p ^ K),
            θ ^ (((α * h + γ * h ^ 2) + ((2 * γ) * h) * w').val))
        = ∑ h : ZMod (p ^ K), ∑ w' : ZMod (p ^ K),
            θ ^ (((α * h + γ * h ^ 2) + ((2 * γ) * h) * w').val) := Finset.sum_comm
    exact h1.trans (h2.trans h3)
  -- ### Step 3: the inner complete character sum
  have hfin : (∑ h : ZMod (p ^ K), ∑ w' : ZMod (p ^ K),
          θ ^ (((α * h + γ * h ^ 2) + ((2 * γ) * h) * w').val))
      = ((p ^ K : ℕ) : ℂ)
        * (∑ h : ZMod (p ^ K), if (2 * γ) * h = 0 then θ ^ ((α * h).val) else 0) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun h _ => ?_
    have hprod : (∑ w' : ZMod (p ^ K),
            θ ^ (((α * h + γ * h ^ 2) + ((2 * γ) * h) * w').val))
        = θ ^ ((α * h + γ * h ^ 2).val)
          * (∑ w' : ZMod (p ^ K), θ ^ ((((2 * γ) * h) * w').val)) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun w' _ => ?_
      exact zmod_pow_val_add hθ _ _
    rw [hprod, sum_zmod_val_pow_eq (p ^ K) hθ ((2 * γ) * h)]
    by_cases hc : (2 * γ) * h = 0
    · rw [if_pos hc, if_pos hc, kernel_mul_sq_eq_zero hp2 hc, add_zero]
      ring
    · rw [if_neg hc, if_neg hc]
      ring
  rw [hsplit, hreindex]
  exact hfin

end Work.LinnikBurgess
