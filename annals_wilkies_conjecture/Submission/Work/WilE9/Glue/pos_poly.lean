import Mathlib
import Submission.Work.WilE9.Defs
import Submission.Work.WilE9.Gen.gen_pos_set

namespace Work.WilE9.Glue

/-
  The strict-positive locus of a polynomial is a `Gen`-set of format `m+2` and degree
  `P.totalDegree + 2`.  (Note: `Submission/Work/WilE9/Gen/gen_pos_set.lean` already contains
  `gen_pos_mpoly_fmt` with substantially this statement — if it is available and sorry-free,
  a one-line aliasing proof is fine, otherwise copy its proof:
  `0 < P x ↔ ∃ t, t^2 * P x = 1`, i.e. the set is `projLast {t^2 * rename P - 1 = 0}`, giving
  `Gen.hyp (m+1)` then `Gen.proj`, then `Gen.mono_D` for the degree.)
-/
theorem pos_poly {m : ℕ} (P : MvPolynomial (Fin m) ℝ) :
    WilkiesDesign.E.Gen (m + 2) (P.totalDegree + 2) m {z : Fin m → ℝ | 0 < MvPolynomial.eval z P} :=
  Work.WilE9.Gen.gen_pos_mpoly_fmt P

end Work.WilE9.Glue
