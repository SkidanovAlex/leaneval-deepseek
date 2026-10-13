import Mathlib.Analysis.Real.Sqrt
import Submission.Work.Cyl.Coords
import Submission.Work.Cyl.Frame
import Submission.Work.Cyl.Basic
import Submission.Work.Cyl.FieldDeriv
import Submission.Work.Cyl.isOdd_axiField

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

set_option autoImplicit false
set_option linter.unusedSimpArgs false

open Work.Cyl

namespace Work.Cyl

/-!
# Parity of the no-swirl field `cylField ur uz`

`cylField ur uz x = (u_r(r,x₃)/r) • (x₀,x₁,0) + u_z(r,x₃) • e₃` with `r = √(x₀²+x₁²)`.

Since `cylField ur uz = axiField (fun s z => u_r(√s,z)/√s) (fun s z => u_z(√s,z))` the parity
criterion is exactly the one proved for `axiField`, transported across `s = r²` (`√(r²) = r`
for `r ≥ 0`).  The result is

* `u_r` is even in `x₃`, only forced for `r > 0` (on the axis the factor `x₀ = x₁ = 0` makes the
  first two components vanish identically);
* `u_z` is odd in `x₃`, forced for `r ≥ 0`, including the axis.
-/

theorem isOdd_cylField (ur uz : ℝ → ℝ → ℝ) :
    FiniteTimeSingularity.IsOdd (Work.Cyl.cylField ur uz) ↔
      (∀ r, 0 < r → ∀ z, ur r (-z) = ur r z) ∧ (∀ r, 0 ≤ r → ∀ z, uz r (-z) = -uz r z) := by
  rw [cylField_eq_axiField, isOdd_axiField]
  constructor
  · -- **Forward**: read the parity of the profiles off the reflected profiles `a`, `b`.
    rintro ⟨ha, hb⟩
    refine ⟨?_, ?_⟩
    · -- `u_r` even in `x₃` for `r > 0`: substitute `s = r²` and cancel the factor `√(r²) = r`.
      intro r hr z
      have h := ha (r ^ 2) (by positivity) z
      rw [Real.sqrt_sq hr.le] at h
      exact (div_left_inj' hr.ne').mp h
    · -- `u_z` odd in `x₃` for `r ≥ 0`: substitute `s = r²`.
      intro r hr z
      have h := hb (r ^ 2) (by positivity) z
      rwa [Real.sqrt_sq hr] at h
  · -- **Backward**: transport the parity of the profiles back to the reflected profiles.
    rintro ⟨hur, huz⟩
    refine ⟨?_, ?_⟩
    · intro s hs z
      have h := hur (Real.sqrt s) (Real.sqrt_pos.mpr hs) z
      rw [h]
    · intro s hs z
      exact huz (Real.sqrt s) (Real.sqrt_nonneg s) z

end Work.Cyl
