import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Submission.Work.FTS.EllipticEst.HkNorm_add_le
import Submission.Work.FTS.EllipticEst.Cores.DiagEstEllT.HkIntegrand_add_le_of_contDiffOn
import Submission.Work.FTS.OpenPkg.HkMem_add_of_contDiffOn_four
import Submission.Work.FTS.EllipticEst.Cores.AlphaRateEstEllT.PthIter2VftsAux

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongPersist

open MeasureTheory Set

/-- **Closure of `ℋ^k` under addition, at finite smoothness, together with the `√2`-triangle
inequality for the norm.**

Both halves are already available in the library in exactly the required form:

* the *membership* half is `Work.FTS.EllipticEst.Cores.AlphaRateEstEllT.HkMem_add_of_contDiffOn_le`
  — the `C^k`-on-the-open-quadrant version of `HkMem`-closure (its proof uses the pointwise
  subadditivity `HkIntegrand_add_le_domain` of the integrand, which extends the interior
  inequality `Work.FTS.EllipticEst.Cores.DiagEstEllT.HkIntegrand_add_le_of_contDiffOn` to the
  boundary lines `z = 0` and `sin 2θ = 0` where every integrand vanishes);
* the *norm* half is `Work.FTS.EllipticEst.HkSq_add_le_of_pointwise` (which needs only the
  pointwise subadditivity of the integrand together with `HkMem` of the two summands, no further
  smoothness), followed by the scalar inequality `√(2x + 2y) ≤ √2 (√x + √y)`.

Note that `HkMem α k (f + g)` is *not* needed for the norm half beyond what
`HkSq_add_le_of_pointwise` consumes: the honesty of the three squared norms is precisely the two
hypotheses `hmf`, `hmg` (the pointwise inequality `hpt` bounds the integrand of the sum by an
integrable majorant, and `HkIntegrand_nonneg` supplies the a.e.-positivity). -/
theorem HkAddFin {α : ℝ} {k : ℕ} {f g : ℝ → ℝ → ℝ}
    (hf : ContDiffOn ℝ k (Function.uncurry f) Work.FTS.EllipticEst.Q0)
    (hg : ContDiffOn ℝ k (Function.uncurry g) Work.FTS.EllipticEst.Q0)
    (hmf : Work.Spaces.HkMem α k f) (hmg : Work.Spaces.HkMem α k g) :
    Work.Spaces.HkMem α k (fun z θ => f z θ + g z θ) ∧
      Work.Spaces.HkNorm α k (fun z θ => f z θ + g z θ)
        ≤ Real.sqrt 2 * (Work.Spaces.HkNorm α k f + Work.Spaces.HkNorm α k g) := by
  -- the pointwise subadditivity of the integrand on the closed quadrant
  have hpt : ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      Work.Spaces.HkIntegrand α k (fun z θ => f z θ + g z θ) z θ
        ≤ 2 * Work.Spaces.HkIntegrand α k f z θ
          + 2 * Work.Spaces.HkIntegrand α k g z θ :=
    Work.FTS.EllipticEst.Cores.AlphaRateEstEllT.HkIntegrand_add_le_domain α k hf hg
  refine ⟨Work.FTS.EllipticEst.Cores.AlphaRateEstEllT.HkMem_add_of_contDiffOn_le α k hf hg hmf hmg,
    ?_⟩
  -- the squared estimate
  have hsq : Work.Spaces.HkSq α k (fun z θ => f z θ + g z θ)
      ≤ 2 * Work.Spaces.HkSq α k f + 2 * Work.Spaces.HkSq α k g :=
    Work.FTS.EllipticEst.HkSq_add_le_of_pointwise α k hmf hmg hpt
  have hx : 0 ≤ Work.Spaces.HkSq α k f := Work.Spaces.HkSq_nonneg α k f
  have hy : 0 ≤ Work.Spaces.HkSq α k g := Work.Spaces.HkSq_nonneg α k g
  -- take square roots: `HkNorm` is `√(HkSq)`
  have hroot : Work.Spaces.HkNorm α k (fun z θ => f z θ + g z θ)
      ≤ Real.sqrt (2 * Work.Spaces.HkSq α k f + 2 * Work.Spaces.HkSq α k g) :=
    Real.sqrt_le_sqrt hsq
  refine le_trans hroot ?_
  have hsqrt : Real.sqrt (2 * Work.Spaces.HkSq α k f + 2 * Work.Spaces.HkSq α k g)
      = Real.sqrt 2 * Real.sqrt (Work.Spaces.HkSq α k f + Work.Spaces.HkSq α k g) := by
    rw [show 2 * Work.Spaces.HkSq α k f + 2 * Work.Spaces.HkSq α k g
        = 2 * (Work.Spaces.HkSq α k f + Work.Spaces.HkSq α k g) by ring,
      Real.sqrt_mul (by norm_num)]
  rw [hsqrt, Work.Spaces.HkNorm, Work.Spaces.HkNorm]
  exact mul_le_mul_of_nonneg_left
    (Work.FTS.EllipticEst.Cores.AlphaRateEstEllT.sqrt_add_le_honest hx hy)
    (Real.sqrt_nonneg 2)

end Work.FTS.StrongPersist
