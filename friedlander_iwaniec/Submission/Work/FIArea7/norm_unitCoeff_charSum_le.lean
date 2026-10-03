import Mathlib
import Submission.Work.FIArea7.Section16Expansion

set_option autoImplicit false

namespace Work.FIArea7

open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-- The character `conj ∘ χ` of `Additive G`: conjugation is a multiplicative self-map of `ℂ`
fixing `1`, so precomposition with it turns an additive character into an additive character. -/
def conjAddChar {G : Type*} [Monoid G] (χ : AddChar (Additive G) ℂ) :
    AddChar (Additive G) ℂ where
  toFun x := star (χ x)
  map_zero_eq_one' := by simp
  map_add_eq_mul' a b := by
    show star (χ (a + b)) = star (χ a) * star (χ b)
    rw [AddChar.map_add_eq_mul, star_mul, mul_comm]

@[simp] lemma conjAddChar_apply {G : Type*} [Monoid G] (χ : AddChar (Additive G) ℂ)
    (x : Additive G) : conjAddChar χ x = star (χ x) := rfl

/-- The coefficient `unitCoeff n c z = c̄(z)·[z unit mod n]` is the conjugate of
`c z · [z unit mod n]` (the indicator is real). -/
lemma star_coeff_ind (n : ℕ) (c : GaussianInt → ℂ) (z : GaussianInt) :
    star (c z * unitInd n z) = unitCoeff n c z := by
  rw [unitCoeff, star_mul, star_unitInd, mul_comm]

/-- **The character-sum bound transfers from the coefficients `c` to their conjugates.**  If every
character sum of `c z · [z unit] · χ(class of z)` is bounded by `B`, the same bound holds for the
character sums of the conjugated family `unitCoeff n c`.  Conjugating the target sum replaces the
character `χ` by `conj ∘ χ` (again an additive character) and rewrites `unitCoeff n c` back to
`c · [· unit]`, so the hypothesis at `conj ∘ χ` applies verbatim. -/
theorem norm_unitCoeff_charSum_le (n : ℕ) [NeZero n] (Rz : ℤ) (c : GaussianInt → ℂ) (B : ℝ)
    (hB : ∀ χ : AddChar (Additive (Work.FIArea7.GaussUnit n)) ℂ,
      ‖∑ z ∈ Work.FIPlan.gBox Rz, c z * Work.FIArea7.unitInd n z * χ (Additive.ofMul (Work.FIArea7.unitClassD n z))‖ ≤ B)
    (χ : AddChar (Additive (Work.FIArea7.GaussUnit n)) ℂ) :
    ‖∑ z ∈ Work.FIPlan.gBox Rz, Work.FIArea7.unitCoeff n c z * χ (Additive.ofMul (Work.FIArea7.unitClassD n z))‖ ≤ B := by
  have h := hB (conjAddChar χ)
  have hTS : (∑ z ∈ Work.FIPlan.gBox Rz,
        Work.FIArea7.unitCoeff n c z * χ (Additive.ofMul (Work.FIArea7.unitClassD n z)))
      = star (∑ z ∈ Work.FIPlan.gBox Rz,
          c z * Work.FIArea7.unitInd n z *
            conjAddChar χ (Additive.ofMul (Work.FIArea7.unitClassD n z))) := by
    rw [star_sum]
    refine Finset.sum_congr rfl fun z _ => ?_
    rw [star_mul, star_coeff_ind]
    simp only [conjAddChar_apply, star_star]
    ring
  rw [hTS, norm_star]
  exact h

end

end Work.FIArea7
