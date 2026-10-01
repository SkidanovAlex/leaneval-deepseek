import Mathlib
import Submission.Work.ZeroFreeTables.t23Defs
import Submission.Work.ZeroFreeTables.testFn7_2
import Submission.Work.ZeroFreeTables.tf72Fc_re_eq_realIntegral
import Submission.Work.ZeroFreeTables.tf72_realIntegral_eq_hb72G

/-!
# `tf72Fc_re_eq_hb72G` — the Laplace transform of HB Lemma 7.2's test function in closed form

With `g(u) = (2-u)³(4+6u+u²) = 32 - 40u² + 20u³ - u⁵` and
`G(x) = ∫₀² g(u) e^{xu} du` (the normalised density `hb72g`/`hb72G` of
`HBTable2and3_engine`), the Laplace transform of HB Lemma 7.2's test function at scale `λ`
is `F_λ(z) = G(-z/λ)/30`.

This is the identification used to turn the `F`-expressions of HB Tables 2 and 3 into
functions of the rational data `(λ, b, v)` alone.  It splits into

* `tf72Fc_re_eq_realIntegral`: the real part of the complex transform `tf72Fc` is the real
  Laplace integral `∫₀^{2/λ} e^{−zt} f(t) dt`;
* `tf72_realIntegral_eq_hb72G`: the substitution `u = λt` turns that integral into
  `G(−z/λ)/30`.
-/

noncomputable section
namespace Work.ZeroFreeTables

theorem tf72Fc_re_eq_hb72G (lam z : ℝ) (hlam : 0 < lam) :
    (Work.ZeroFreeTables.tf72Fc lam (z : ℂ)).re = Work.ZeroFreeTables.hb72G (-z / lam) / 30 := by
  rw [tf72Fc_re_eq_realIntegral lam z, tf72_realIntegral_eq_hb72G lam z hlam]

end Work.ZeroFreeTables
