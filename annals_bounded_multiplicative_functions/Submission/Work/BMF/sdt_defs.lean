import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

open scoped Topology
open Filter

/-!
# Definitions for the second-derivative-test → partial-sum development

Shared interface for `Work.BMF.sdt_partialSum_large_le`.

* `SDTProp C` is the van der Corput second-derivative-test hypothesis with
  constant `C` (the same shape as the hypothesis `hsdt` of the main theorem).
* `phaseR t x = exp(-i·t·log x)` is the oscillating phase whose partial sums are
  controlled by the second-derivative test.
-/

namespace Work.BMF

/-- **Second-derivative-test hypothesis** with constant `C`: for every `C²`
function `f` on `[a, a+n]` (`n ≥ 1`) with `r ≤ f'' ≤ 4r` in the interior
(`0 < r`),
`‖Σ_{a<k≤a+n} exp(2πi f(k))‖ ≤ C·(n√r + 1/√r)`. -/
def SDTProp (C : ℝ) : Prop :=
  ∀ {a : ℤ} {n : ℕ}, 1 ≤ n → ∀ f : ℝ → ℝ, ∀ r : ℝ, 0 < r →
    ContDiffOn ℝ 2 f (Set.Icc (a : ℝ) ((a : ℝ) + n)) →
    (∀ x ∈ Set.Ioo (a : ℝ) ((a : ℝ) + n), r ≤ deriv (deriv f) x ∧ deriv (deriv f) x ≤ 4 * r) →
    ‖∑ k ∈ Finset.Icc (a + 1) (a + (n : ℤ)),
        Complex.exp (((2 * Real.pi * f (k : ℝ) : ℝ) : ℂ) * Complex.I)‖
      ≤ C * ((n : ℝ) * Real.sqrt r + 1 / Real.sqrt r)

/-- The oscillating phase `x ↦ exp(-i·t·log x)`. -/
noncomputable def phaseR (t x : ℝ) : ℂ := Complex.exp (((-t * Real.log x : ℝ) : ℂ) * Complex.I)

end Work.BMF

namespace Work.BMF

/-- The real phase `x ↦ -(t/(2π))·log x`; `phaseR t x` is its `2π`-exponential. -/
noncomputable def phaseFn (t x : ℝ) : ℝ := -(t / (2 * Real.pi)) * Real.log x

/-- `phaseR` is the exponential of `phaseFn`, in the exact shape used by the
second-derivative test (`exp(2πi·f)`). -/
lemma phaseR_eq_exp_phaseFn (t x : ℝ) :
    phaseR t x = Complex.exp (((2 * Real.pi * phaseFn t x : ℝ) : ℂ) * Complex.I) := by
  have h : 2 * Real.pi * phaseFn t x = -t * Real.log x := by
    unfold phaseFn
    field_simp
  unfold phaseR
  rw [h]

end Work.BMF

namespace Work.BMF

/-- `phaseR t x` is a unit complex number. -/
lemma phaseR_norm (t x : ℝ) : ‖phaseR t x‖ = 1 := by
  unfold phaseR
  exact Complex.norm_exp_ofReal_mul_I _

end Work.BMF
