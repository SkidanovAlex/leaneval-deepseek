import Mathlib

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.BSLit.Wielandt

/-- If `K ⊓ P = ⊥` then the decomposition `a * b` with `a : K`, `b : P` is unique:
from `a * b = a' * b'` we get `a = a'` and `b = b'`.
(The element `(a')⁻¹ * a = b' * b⁻¹` lies in both `K` and `P`, hence is `1`.) -/
theorem EqOfMulEqMul {F : Type*} [Group F] (K P : Subgroup F) (hdisj : K ⊓ P = ⊥)
    {a a' : K} {b b' : P} (h : (a : F) * (b : F) = (a' : F) * (b' : F)) :
    a = a' ∧ b = b' := by
  have hx : ((a'⁻¹ * a : K) : F) = ((b' * b⁻¹ : P) : F) := by
    have hh := congrArg (fun x : F => (a' : F)⁻¹ * x * (b : F)⁻¹) h
    push_cast
    simpa [mul_assoc] using hh
  have hmemP : ((a'⁻¹ * a : K) : F) ∈ P := by rw [hx]; exact (b' * b⁻¹).2
  have hmemK : ((a'⁻¹ * a : K) : F) ∈ K := (a'⁻¹ * a).2
  have hx1 : ((a'⁻¹ * a : K) : F) = 1 := by
    have hmem : ((a'⁻¹ * a : K) : F) ∈ K ⊓ P := ⟨hmemK, hmemP⟩
    rw [hdisj] at hmem
    simpa using hmem
  have ha : a = a' := by
    have : a'⁻¹ * a = 1 := Subtype.ext (by simpa using hx1)
    exact (inv_mul_eq_one.mp this).symm
  have hb : b = b' := by
    have h' : (a' : F) * (b : F) = (a' : F) * (b' : F) := by
      rw [← ha] at h ⊢
      exact h
    exact Subtype.ext (mul_left_cancel h')
  exact ⟨ha, hb⟩

end Work.BSLit.Wielandt
