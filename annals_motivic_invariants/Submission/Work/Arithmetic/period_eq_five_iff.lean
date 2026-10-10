import Mathlib
import Submission.Work.Arithmetic.Defs

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.Arithmetic

/-
Paper: Lin-Shinder, `lem:torsors` and the surrounding discussion ("torsors of index 5",
"a divisor of degree 5" with no rational points).  For a genus-one curve of period `p`,
"carries a `𝕜`-rational divisor of degree `n`" is `n · [C] = 0` in `H¹(𝕜,E)`, i.e.
`T.cls ^ n = 1` (`T.DivisorOfDegree n`), and "no rational point" is `T.cls ≠ 1`
(`T.Pointless`).  Since `5` is prime, period `5` is exactly the conjunction.

Route: `orderOf_dvd_iff_pow_eq_one`, `orderOf_eq_one_iff`, primality of `5`.

Companions the caller will use (prove them here as extra lemmas if convenient, they are
immediate from this one): `period_eq_five_iff.1 h5` gives both conjuncts.
-/
theorem period_eq_five_iff {𝕜 : Type} [Field 𝕜] (T : Work.Arithmetic.Torsor 𝕜) :
    T.period = 5 ↔ T.DivisorOfDegree 5 ∧ T.Pointless := by
  rw [Torsor.period, Torsor.DivisorOfDegree, Torsor.Pointless]
  constructor
  · intro h
    exact ⟨h ▸ pow_orderOf_eq_one T.cls, fun h1 => by
      rw [h1, orderOf_one] at h
      exact absurd h (by decide)⟩
  · rintro ⟨hd, hp⟩
    rcases (Nat.prime_five.eq_one_or_self_of_dvd _ (orderOf_dvd_iff_pow_eq_one.mpr hd)) with
      h1 | h5
    · exact absurd (orderOf_eq_one_iff.mp h1) hp
    · exact h5

/-- Period `5` implies that `C` has no `𝕜`-rational point. -/
theorem pointless_of_period_eq_five {𝕜 : Type} [Field 𝕜] (T : Work.Arithmetic.Torsor 𝕜)
    (h5 : T.period = 5) : T.Pointless :=
  (period_eq_five_iff T).mp h5 |>.2

/-- Period `5` implies that `C` carries a `𝕜`-rational divisor of degree `5`. -/
theorem divisorOfDegree_five_of_period_eq_five {𝕜 : Type} [Field 𝕜]
    (T : Work.Arithmetic.Torsor 𝕜) (h5 : T.period = 5) : T.DivisorOfDegree 5 :=
  (period_eq_five_iff T).mp h5 |>.1

end Work.Arithmetic
