import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.H2.T1Q.PwBdQ
import Submission.Work.FTS.H2.HQ.HardyZQ

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The radial Hardy inequality for the angular slices of the open class

For `f` of class `C^∞` on the *open* quadrant (`Work.FTS.EllipticEst.SmoothOpen f`) with
`Work.Spaces.DecayAll 4 f`, and for every interior angle `σ ∈ (0, π/2)`,

  `(D_z^b D_θ^a f(z,σ))² ≤ ∫_0^∞ (D_z^{b+1} D_θ^a f(s,σ))² w(s)² ds`   for every `z > 0`.

This is the interior (open-quadrant) radial Hardy inequality: apply
`Work.FTS.H2.HQ.HardyZQ` to the `z`-slice `v s := D_z^b D_θ^a f(s,σ)`, whose `z`-derivative is
`∂_z v s = ∂_z (D_z^b D_θ^a f)(s,σ)` and whose `D_z`-derivative is
`s ∂_z v s = D_z^{b+1} D_θ^a f(s,σ)`, exactly the integrand of the target.  The three
hypotheses of `HardyZQ` are the slice smoothness (`SmoothOpen f`), the decay of the slice at
`+∞` (the `DecayMixed`-half of `DecayAll 4 f`, using `a + b ≤ 4`) and the integrability
hypothesis `hint` (transported along the definitional identity above).
-/

open MeasureTheory Set Filter
open scoped Real Topology

namespace Work.FTS.StrongPersist.N6Trans.OpenTwins

theorem hardyZQ_mixed_slice_open (f : ℝ → ℝ → ℝ)
    (hf : Work.FTS.EllipticEst.SmoothOpen f) (hdec : Work.Spaces.DecayAll 4 f)
    (b a : ℕ) (hab : a + b ≤ 4) {σ : ℝ} (hσ : σ ∈ Set.Ioo (0 : ℝ) (π / 2))
    (hint : MeasureTheory.IntegrableOn
      (fun s => (Work.Spaces.mixed (b + 1) a f s σ) ^ 2 * (Work.Spaces.w s) ^ 2)
      Work.Spaces.Iz) :
    ∀ z ∈ Set.Ioi (0 : ℝ),
      (Work.Spaces.mixed b a f z σ) ^ 2
        ≤ ∫ s in Work.Spaces.Iz,
            (Work.Spaces.mixed (b + 1) a f s σ) ^ 2 * (Work.Spaces.w s) ^ 2 := by
  intro z hz
  -- the slice `s ↦ D_z^b D_θ^a f s σ` is `C¹` on `(0,∞)`
  have hslicecont : ContDiffOn ℝ 1 (fun s : ℝ => Work.Spaces.mixed b a f s σ)
      (Set.Ioi (0 : ℝ)) :=
    ((hf.mixed b a).curry_z hσ).of_le (by simp [Work.Stability.smoothOrder])
  -- the slice decays at `+∞`
  have hdecs : Tendsto (fun s : ℝ => Work.Spaces.mixed b a f s σ) atTop (nhds 0) :=
    hdec.2 a b hab σ ⟨le_of_lt hσ.1, le_of_lt hσ.2⟩
  -- integrability of `(s ∂_s v)² w²`, which is `hint` up to unfolding `D_z`
  have hints : MeasureTheory.IntegrableOn
      (fun s => (s * deriv (fun s' : ℝ => Work.Spaces.mixed b a f s' σ) s) ^ 2
        * (Work.Spaces.w s) ^ 2) Work.Spaces.Iz := by
    simpa only [Work.Spaces.mixed, Work.Spaces.DzIter_succ, Work.Spaces.DzIter_zero,
      Work.Spaces.Dz, Work.Spaces.pz, mul_comm, mul_left_comm, mul_assoc] using hint
  have h := Work.FTS.H2.HQ.HardyZQ (fun s : ℝ => Work.Spaces.mixed b a f s σ)
    hslicecont hdecs hints z hz
  simpa only [Work.Spaces.mixed, Work.Spaces.DzIter_succ, Work.Spaces.DzIter_zero,
    Work.Spaces.Dz, Work.Spaces.pz, mul_comm, mul_left_comm, mul_assoc] using h

end Work.FTS.StrongPersist.N6Trans.OpenTwins
