import Mathlib
import Submission.Diff.Alg
import Submission.Work.Diff.Alg.Pinch.Defs
import Submission.Work.Diff.Alg.Pinch.BQDefs
import Submission.Work.Diff.Alg.Pinch.BQ_iso
import Submission.Work.Diff.PP.Q_smul

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The linearization of Hamilton's reaction term about the round sphere

For an algebraic curvature tensor `R`,

`(1/4) • (Q (R + Iso n) − Q (R − Iso n)) = Ric(R) ∧ id`,

i.e. the symmetric difference quotient of Hamilton's quadratic reaction term `Q` in the direction
of the round-sphere curvature `Iso n` is the Kulkarni–Nomizu product of the Ricci tensor of `R` with
the metric `id2 n`.  Equivalently: `Q` is `C¹` with derivative `2 • BQ R ·` at `R`, and the first
order term of `Q` at the round sphere is the Ricci tensor.

The proof only needs the polarisation `BQ` of `Q` (`Q (R + S) = Q R + Q S + 2 • BQ R S`,
`Work.Diff.Alg.Pinch.Q_add_polarize`), the evenness of `Q` (`Q (c • R) = c² • Q R`,
`Work.Diff.PP.Q_smul`), bilinearity of `BQ` in its second slot
(`Work.Diff.Alg.Pinch.BQ_smul_right`), and the component identity
`BQ R (Iso n) = knProd (ric R) (id2 n)` (`Work.Diff.Alg.Pinch.BQ_iso`); the whole content is that
the quadratic term `Q (R − Iso n)` differs from `Q (R + Iso n)` exactly in the sign of the mixed
term `BQ R (Iso n)`, so that the difference of the two is `4 • BQ R (Iso n)`.
-/

namespace Work.Diff.Alg.Pinch

open Finset Submission.Diff.Alg

theorem Q_shift_iso (n : ℕ) {R : Submission.Diff.Alg.Curv4 n}
    (hR : Submission.Diff.Alg.IsAlgCurv R) :
    (4⁻¹ : ℝ) • (Submission.Diff.Alg.Q (R + Submission.Diff.Alg.Iso n) -
        Submission.Diff.Alg.Q (R - Submission.Diff.Alg.Iso n)) =
      Work.Diff.Alg.Pinch.knProd (Work.Diff.Alg.Pinch.ric R) (Work.Diff.Alg.Pinch.id2 n) := by
  -- `R - Iso n = R + (-1) • Iso n`, so that both arguments of `Q` are of the form `R + S`
  have hsub : R - Iso n = R + (-1 : ℝ) • Iso n := by
    ext i j k l
    simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  -- `Q` is homogeneous of degree `2`, so the negative of `Iso n` is irrelevant
  have hQneg : Q ((-1 : ℝ) • Iso n) = Q (Iso n) := by
    rw [Work.Diff.PP.Q_smul n (-1) (Iso n)]
    norm_num
  -- polarization in both arguments: the mixed terms have opposite signs
  have hdiff : Q (R + Iso n) - Q (R - Iso n) = (4 : ℝ) • BQ R (Iso n) := by
    rw [hsub, Q_add_polarize R (Iso n), Q_add_polarize R ((-1 : ℝ) • Iso n), hQneg,
      BQ_smul_right]
    ext i j k l
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring
  rw [hdiff, smul_smul, show (4 : ℝ)⁻¹ * 4 = 1 by norm_num, one_smul]
  exact BQ_iso n hR

end Work.Diff.Alg.Pinch
