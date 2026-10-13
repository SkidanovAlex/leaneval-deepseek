import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Submission.Work.Spaces.Defs
import Submission.Work.Elliptic.Defs
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.ClassC.PzSinCos2Box
import Submission.Work.FTS.EllipticEst.TT.HkMem_descend_open
import Submission.Work.FTS.EllipticEst.Cores.OrthCond_lambda_zero
import Submission.Work.EllipticEst.H2W.Fstar_sub_eq_integral_pz

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.ClassC

open scoped Real Topology
open MeasureTheory Set Filter

/-! ## The moment chain for `∂_z`

The angular moment `F_*(g)(z) = ∫_θ g(z,θ) sinθcos²θ dθ` of the plain radial derivative
`∂_z f` is an antiderivative of `F_* f`:

  `F_* f (z) - F_* f (s) = ∫_{s}^{z} F_*(∂_z f)(r) dr`  (`0 < s ≤ z`).

This is the `j = 0` case of the paper's chain rule for `F_*` along the radial operators
(the `D_z`-chain of `Work.FTS.EllipticEst.FstarDzIter_chain_open`), stated at the *minimal*
honesty level `HkMem α 1 f`:  only the first `D_z`-slot of the `ℋ¹`-integrand is needed,
because on the radial box `(s,z]` one has `∂_z f = D_z f / r` with `r ≥ s > 0`, so the plain
`z`-derivative is controlled by the first weighted `D_z`-slot
(`PzSinCos2Box`, via `pzSqSeta_le_Dz1_mul`).

The analytic content is Fubini on the box `[s,z] × Iθ` together with the fundamental theorem
of calculus along the radial slices
(`Work.EllipticEst.H2W.Fstar_sub_eq_integral_pz`); the three integrability hypotheses of that
theorem are supplied from `HkMem α 1 f`:
`Cores.integrableOn_slice_mul_sinCos2` (via the descent `HkMem α 1 f → HkMem α 0 f`) for the two
endpoint slices, and `PzSinCos2Box` for the box integrand. -/
theorem Fstar_chain_pz {α : ℝ} {f : ℝ → ℝ → ℝ}
    (hsm : Work.FTS.EllipticEst.SmoothOpen f) (hmem : Work.Spaces.HkMem α 1 f)
    {s z : ℝ} (hs : 0 < s) (hsz : s ≤ z) :
    Work.Elliptic.Fstar f z - Work.Elliptic.Fstar f s
      = ∫ r in s..z, Work.Elliptic.Fstar (Work.Spaces.pz f) r := by
  -- descent to `ℋ⁰`, for the integrability of the two endpoint slices
  have hmem0 : Work.Spaces.HkMem α 0 f :=
    Work.FTS.EllipticEst.TT.HkMem_descend_open (α := α) (f := f) (k := 0) (l := 1)
      (by norm_num) ((Work.FTS.EllipticEst.smoothOpen_iff_forall f).mp hsm) hmem
  have hsl : ∀ ρ : ℝ, 0 < ρ → MeasureTheory.IntegrableOn
      (fun θ : ℝ => f ρ θ * Work.Elliptic.sinCos2 θ) Work.Spaces.Iθ :=
    fun ρ hρ => Work.FTS.EllipticEst.Cores.integrableOn_slice_mul_sinCos2
      hsm.continuousOn hmem0 hρ
  rcases eq_or_lt_of_le hsz with h | h
  · rw [← h, sub_self, intervalIntegral.integral_same]
  refine Work.EllipticEst.H2W.Fstar_sub_eq_integral_pz (f := f) hsm hs hsz
    (hsl s hs) (hsl z (lt_of_lt_of_le hs h.le)) ?_
  exact PzSinCos2Box hsm hmem hs h

end Work.FTS.ClassC
