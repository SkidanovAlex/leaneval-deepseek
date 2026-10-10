import Mathlib
import Submission.Work.PointlessTwist.Defs
import Submission.Work.Reflect.PolyId
set_option maxRecDepth 100000

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.PointlessTwist.Kummer

/-- `intDegree` of a power of a nonzero rational function. -/
lemma intDegree_pow_of_ne_zero {𝔽 : Type} [Field 𝔽] {b : RatFunc 𝔽} (hb : b ≠ 0) (n : ℕ) :
    (b ^ n).intDegree = (n : ℤ) * b.intDegree := by
  induction n with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, RatFunc.intDegree_mul (pow_ne_zero k hb) hb, ih]
    push_cast
    first | refl_ring1 | ring

/-- **`t` is not a fifth power in the rational function field.**  This is the field-theoretic input of
the Kummer / Artin–Schreier construction at `a = t`: with `𝕜 = 𝔽(t)`, the extension `s ^ 5 = t` is
cyclic of degree `5` over a field containing a primitive `5`-th root of unity, and `L = 𝔽(s)`; the
proof that `t ∉ 𝕜 ^ 5` is exactly what `Work.TorsorExistence.existsCyclicExtension_of_zeta5`
consumes.  (Holds in every characteristic.)

Route: `RatFunc.intDegree` (`𝔽 → ℤ`) with `RatFunc.intDegree_X : X.intDegree = 1` and
`RatFunc.intDegree_mul`; `b ^ 5 = X ≠ 0` gives `b ≠ 0`, hence `5 * b.intDegree = 1`, impossible.
Equivalently `RatFunc.num_div_denom` + coprimality: `p ^ 5 = X * q ^ 5` forces `q` constant and then
`5 * p.natDegree = 1`. -/
theorem not_exists_pow_five_eq_X {𝔽 : Type} [Field 𝔽] :
    ¬ ∃ b : RatFunc 𝔽, b ^ 5 = RatFunc.X := by
  rintro ⟨b, hb⟩
  have hbne : b ≠ 0 := by
    intro h
    rw [h, zero_pow (by norm_num : (5 : ℕ) ≠ 0)] at hb
    exact RatFunc.X_ne_zero hb.symm
  have h := congrArg RatFunc.intDegree hb
  rw [intDegree_pow_of_ne_zero hbne 5, RatFunc.intDegree_X] at h
  norm_num at h
  omega

end Work.PointlessTwist.Kummer
