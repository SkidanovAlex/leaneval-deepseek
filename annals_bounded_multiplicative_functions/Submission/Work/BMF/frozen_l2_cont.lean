import Mathlib
import Submission.Work.BMF.parseval.Defs
import Submission.Work.BMF.mwt_transform_bound

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Continuity of the frozen-frequency quadratic kernel

The frozen-frequency form of the `L²` bound for `mwt` is the iterated integral

`∫_{t,t'} a t · conj (a t') · ∫_{X e^{-1}}^{X e^3} mwt(X,x) · x^{4 + i(t-t')} dx`.

This file records the (elementary) continuity of the integrand of the outer two
integrals, viewed as a function of the triple `(x, t, t')`.  On the rectangle
`[X e^{-1}, X e^3] × [-L,L] × [-L,L]` the base `x` is bounded away from `0`, so the
complex power `x^{4 + i(t-t')}` is continuous there; `mwt X` is continuous on the same
range because `x ↦ log(x/X)` is, and `κ` is continuous.
-/

namespace Work.BMF

open Set

/-- **Continuity of the frozen-frequency kernel.**
For `X > 0` and continuous `a`, the integrand
`z ↦ mwt(X, z.1) · a(z.2.1) · conj(a(z.2.2)) · z.1^{4 + i(z.2.1 - z.2.2)}`
is continuous on the box `[X e^{-1}, X e^3] × [-L,L] × [-L,L]`. -/
theorem frozen_l2_cont (X L : ℝ) (hX : 0 < X) (a : ℝ → ℂ) (ha : Continuous a) :
    ContinuousOn (fun z : ℝ × ℝ × ℝ =>
        (mwt X z.1 : ℂ) * ((a z.2.1 * (starRingEnd ℂ) (a z.2.2)) * (z.1:ℂ)^(4 + Complex.I*((z.2.1 - z.2.2 : ℝ):ℂ))))
      (Set.Icc (X * Real.exp (-1)) (X * Real.exp 3) ×ˢ (Set.Icc (-L) L ×ˢ Set.Icc (-L) L)) := by
  set S := Set.Icc (X * Real.exp (-1)) (X * Real.exp 3) ×ˢ (Set.Icc (-L) L ×ˢ Set.Icc (-L) L) with hS
  have hXe : 0 < X * Real.exp (-1) := by positivity
  -- On the box, the first coordinate is positive, hence bounded away from `0`.
  have hpos : ∀ z ∈ S, 0 < z.1 := by
    intro z hz
    rw [hS, Set.mem_prod] at hz
    exact lt_of_lt_of_le hXe hz.1.1
  -- The weight `mwt X z.1` is continuous.
  have hmwt : ContinuousOn (fun z : ℝ × ℝ × ℝ => (mwt X z.1 : ℂ)) S := by
    have hlog : ContinuousOn (fun z : ℝ × ℝ × ℝ => Real.log (z.1 / X)) S := by
      apply ContinuousOn.log
      · apply ContinuousOn.div continuous_fst.continuousOn continuousOn_const
        intro z hz; exact hX.ne'
      · intro z hz
        exact div_ne_zero (ne_of_gt (hpos z hz)) hX.ne'
    have h1 : ContinuousOn (fun z : ℝ × ℝ × ℝ => kappa (Real.log (z.1 / X) + 1)) S :=
      continuous_kappa_glue.comp_continuousOn (hlog.add continuousOn_const)
    exact Complex.continuous_ofReal.comp_continuousOn (by simpa [mwt] using h1)
  -- The factor `a z.2.1 * conj (a z.2.2)` is continuous.
  have ha' : ContinuousOn (fun z : ℝ × ℝ × ℝ => a z.2.1 * (starRingEnd ℂ) (a z.2.2)) S :=
    (ha.comp_continuousOn ((continuous_fst.comp continuous_snd).continuousOn)).mul
      (Complex.continuous_conj.comp_continuousOn
        (ha.comp_continuousOn ((continuous_snd.comp continuous_snd).continuousOn)))
  -- The complex power `z.1^{4 + i(z.2.1 - z.2.2)}` is continuous.
  have hbase : ContinuousOn (fun z : ℝ × ℝ × ℝ => (z.1 : ℂ)) S :=
    Complex.continuous_ofReal.comp_continuousOn continuous_fst.continuousOn
  have hexp : ContinuousOn (fun z : ℝ × ℝ × ℝ => (4:ℂ) + Complex.I * ((z.2.1 - z.2.2 : ℝ) : ℂ)) S :=
    continuousOn_const.add (continuousOn_const.mul
      (Complex.continuous_ofReal.comp_continuousOn
        (((continuous_fst.comp continuous_snd).sub (continuous_snd.comp continuous_snd)).continuousOn)))
  have hcpow : ContinuousOn (fun z : ℝ × ℝ × ℝ => (z.1:ℂ)^(4 + Complex.I*((z.2.1 - z.2.2 : ℝ):ℂ))) S :=
    hbase.cpow hexp (fun z hz => by
      rw [Complex.mem_slitPlane_iff]
      left
      simpa using hpos z hz)
  exact hmwt.mul (ha'.mul hcpow)

end Work.BMF
