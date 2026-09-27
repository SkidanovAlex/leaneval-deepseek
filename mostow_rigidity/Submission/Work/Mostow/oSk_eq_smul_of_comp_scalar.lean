import Mathlib
import Submission.Work.Mostow.abelianBlockDefs

namespace Work.Mostow

/-- If `oSk T₀ = 2 s₀ • J` on `W` with `s₀ ≠ 0`, where `J` is an almost complex structure on `W`
(`J (J x) = -x` for `x ∈ W` and `J` maps `W` into itself), and the composite
`oSk T * oSk T₀` equals `m • 1` on `W`, then `oSk T = -(m / (2 * s₀)) • J` on `W`.
Here `oSk b = b - b⁻¹` is the antisymmetric part of `b`
(`Submission.Work.Mostow.abelianBlockDefs`). -/
theorem oSk_eq_smul_of_comp_scalar {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (T T₀ : V ≃ₗᵢ[ℝ] V) (W : Submodule ℝ V) (J : V →ₗ[ℝ] V) (s₀ m : ℝ) (hs₀ : s₀ ≠ 0)
    (hJ : ∀ x ∈ W, J (J x) = -x) (hJmem : ∀ x ∈ W, J x ∈ W)
    (hT₀ : ∀ x ∈ W, oSk T₀ x = (2 * s₀) • J x)
    (hm : ∀ x ∈ W, (oSk T * oSk T₀) x = m • x) :
    ∀ x ∈ W, oSk T x = (-(m / (2 * s₀))) • J x := by
  have h2s : (2 * s₀ : ℝ) ≠ 0 := mul_ne_zero two_ne_zero hs₀
  -- On `W`, `oSk T ∘ J` is the scalar map `(m / (2 * s₀)) • id`.
  have hkey : ∀ y ∈ W, oSk T (J y) = (m / (2 * s₀)) • y := by
    intro y hy
    -- `(oSk T * oSk T₀) y` is defeq to `oSk T (oSk T₀ y)`.
    have h : oSk T (oSk T₀ y) = m • y := hm y hy
    rw [hT₀ y hy, map_smul] at h
    -- `h : (2 * s₀) • oSk T (J y) = m • y`
    calc oSk T (J y) = ((2 * s₀)⁻¹ * (2 * s₀)) • oSk T (J y) := by
            rw [inv_mul_cancel₀ h2s, one_smul]
        _ = (2 * s₀)⁻¹ • ((2 * s₀) • oSk T (J y)) := by rw [mul_smul]
        _ = (2 * s₀)⁻¹ • (m • y) := by rw [h]
        _ = (m / (2 * s₀)) • y := by
              rw [← mul_smul, div_eq_mul_inv]
              congr 1
              ring
  intro x hx
  -- Apply the key relation to `J x ∈ W`.
  have hh : oSk T x = -((m / (2 * s₀)) • J x) := by
    have h1 := hkey (J x) (hJmem x hx)
    rw [hJ x hx, map_neg] at h1
    exact neg_eq_iff_eq_neg.mp h1
  rw [hh, neg_smul]

end Work.Mostow
