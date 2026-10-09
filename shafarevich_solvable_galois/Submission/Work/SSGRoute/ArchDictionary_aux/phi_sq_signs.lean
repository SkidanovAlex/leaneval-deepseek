import Mathlib
import Submission.Work.SSGRoute.PTDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute.ArchDictionary_aux

theorem phi_sq_signs {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] (φ : Ω →+* ℂ) (c : Ω ≃ₐ[k] Ω)
    (hlink : ∀ x : Ω, φ (c x) = starRingEnd ℂ (φ x)) :
    (∀ z : Ω, c z = z → z ≠ 0 → ∃ u : ℝˣ, ((u : ℝ) : ℂ) ^ 2 = φ z ^ 2) ∧
    (∀ z : Ω, c z = -z → z ≠ 0 → ¬ ∃ u : ℝˣ, ((u : ℝ) : ℂ) ^ 2 = φ z ^ 2) := by
  constructor
  · -- `c z = z`: `φ z` is fixed by complex conjugation, hence is real.
    intro z hz hz0
    have hconj : starRingEnd ℂ (φ z) = φ z := by rw [← hlink z, hz]
    have hre : ((φ z).re : ℂ) = φ z := Complex.conj_eq_iff_re.mp hconj
    have hφinjt : Function.Injective φ := RingHom.injective φ
    have hφz : φ z ≠ 0 := by
      intro h
      exact hz0 (hφinjt (by rw [h, map_zero]))
    have hrene : (φ z).re ≠ 0 := by
      intro h
      exact hφz (by rw [← hre, h, Complex.ofReal_zero])
    refine ⟨Units.mk0 (φ z).re hrene, ?_⟩
    rw [Units.val_mk0]
    conv_rhs => rw [← hre]
  · -- `c z = -z`: `φ z` is fixed by `conj ∘ neg`, hence purely imaginary.
    rintro z hz hz0 ⟨u, hu⟩
    have hconj : starRingEnd ℂ (φ z) = -φ z := by rw [← hlink z, hz, map_neg]
    have hre0 : (φ z).re = 0 := by
      have h : (φ z).re = -(φ z).re := by
        have := congrArg Complex.re hconj
        simpa [Complex.conj_re, Complex.neg_re] using this
      linarith
    have hsq : (φ z ^ 2).re = -((φ z).im) ^ 2 := by
      rw [pow_two, Complex.mul_re, hre0]; ring
    have hu_re : (((u : ℝ) : ℂ) ^ 2).re = (u : ℝ) ^ 2 := by
      rw [pow_two, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]; ring
    have key : (u : ℝ) ^ 2 = -((φ z).im) ^ 2 := by
      rw [← hu_re, hu, hsq]
    have hpos : (0 : ℝ) < (u : ℝ) ^ 2 := sq_pos_of_ne_zero (Units.ne_zero u)
    have hnonpos : -((φ z).im) ^ 2 ≤ 0 := by
      have := sq_nonneg (φ z).im; linarith
    linarith [key, hpos, hnonpos]

end Work.SSGRoute.ArchDictionary_aux
