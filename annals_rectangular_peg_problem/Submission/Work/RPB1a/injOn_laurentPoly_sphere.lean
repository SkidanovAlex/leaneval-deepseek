import Mathlib
import Submission.Work.RPB1a.Defs
import Submission.Work.RPB1a.laurentPoly_exp
import Submission.Work.RPB.B1a.laurentAux

/-!
# Injectivity of a Laurent polynomial on the unit circle (node `RPB1a`)

If the trigonometric polynomial `trigPoly N a` is a smooth loop (`IsSmoothLoop` — in particular
injective up to `2π`-periodicity), then its Laurent form `laurentPoly N a` is injective on the unit
sphere `{|w| = 1} ⊂ ℂ`.

The proof is the change of variables `w = e^{it}`: by `laurentPoly_exp`,
`laurentPoly N a (e^{it}) = trigPoly N a t`, and injectivity-mod-`2π` of `v = trigPoly N a` says
that two points of the circle with the same image have arguments differing by an integer multiple of
`2π`, hence give the same point of the circle (periodicity of `exp`).
-/

open Complex Set Metric
open scoped ContDiff Real

set_option autoImplicit false

noncomputable section

namespace Work.RPB1a

/-- `exp` is `2π`-periodic, in the form needed here: `e^{i(t + 2πm)} = e^{it}` for `m : ℤ`. -/
private theorem exp_add_two_pi_int_mul_I (t : ℝ) (m : ℤ) :
    Complex.exp ((↑(t + 2 * Real.pi * m) : ℂ) * Complex.I) = Complex.exp (t * Complex.I) := by
  rw [show ((t + 2 * Real.pi * m : ℝ) : ℂ) * Complex.I
        = (t : ℂ) * Complex.I + (m : ℂ) * (2 * Real.pi * Complex.I) by push_cast; ring]
  rw [Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

theorem injOn_laurentPoly_sphere (N : ℕ) (a : ℤ → ℂ) (hv : Work.RPB1a.IsSmoothLoop (Work.RPB1a.trigPoly N a)) :
    Set.InjOn (Work.RPB1a.laurentPoly N a) (Metric.sphere (0 : ℂ) 1) := by
  obtain ⟨-, -, hinj, -⟩ := hv
  intro z hz w hw hzw
  -- write both points of the circle as `e^{it}`, `e^{it'}`
  obtain ⟨t, rfl⟩ := Work.RPB.B1a.exists_exp_of_mem_sphere hz
  obtain ⟨t', rfl⟩ := Work.RPB.B1a.exists_exp_of_mem_sphere hw
  -- the Laurent polynomial on the circle is the trigonometric polynomial
  rw [Work.RPB1a.laurentPoly_exp, Work.RPB1a.laurentPoly_exp] at hzw
  -- injectivity up to `2π`-periodicity of `v`
  obtain ⟨m, hm⟩ := hinj t t' hzw
  rw [hm]
  -- `e^{i(t + 2πm)} = e^{it}`
  exact (exp_add_two_pi_int_mul_I t m).symm

end Work.RPB1a

end
