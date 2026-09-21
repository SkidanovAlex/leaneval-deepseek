import Mathlib
import Submission.Work.OddCurve.LowSlope.GlueDefs
import Submission.Work.OddRadon.radialSystem_exists_C2
import Submission.Work.OddRadon.radonInverse_radonPhi_local

namespace Work.OddCurve.LowSlope

open Set

/-- **The glued datum is the datum of the reconstructed body.**

The first Radon datum of the body reconstructed from the glued data (through the two-power
system `RadialSystem n (GluePhi n ρa) (GluePsi n ρa) R r`) is, on `(0,1)`, the glued datum
itself: inverting `radonPhi n (rhoNew R r)` at `u` gives the same value as inverting the glued
datum `GlueF n ρa`.

This is the consistency between the two halves of the low-slope step: `rhoNew` was defined from
the solution `(R,r)` of the two-power system, and that system is precisely the statement that
`R(arccos u)^{2n+2} + r(arccos u)^{2n+2}` equals `2 𝓡^{-1}(GlueF n ρa)(u)/u²`. -/
theorem radonInverseRhoNewEq (n : ℕ) (hn : 1 ≤ n) {ρa R r : ℝ → ℝ}
    (hsm : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (Work.OddCurve.LowSlope.rhoNew R r) (Set.Ioo (-1 : ℝ) 1))
    (hRsys : Work.OddRadon.RadialSystem n (Work.OddCurve.LowSlope.GluePhi n ρa)
      (Work.OddCurve.LowSlope.GluePsi n ρa) R r)
    {u : ℝ} (hu0 : 0 < u) (hu1 : u < 1) :
    Work.OddRadon.radonInverse n
        (Work.OddCurve.LowSlope.radonPhi n (Work.OddCurve.LowSlope.rhoNew R r)) u
      = Work.OddRadon.radonInverse n (Work.OddCurve.LowSlope.GlueF n ρa) u := by
  -- Invert the first datum of the reconstructed profile, locally at `u`.
  obtain ⟨c₁, huc₁, hc₁lt⟩ : ∃ c₁, u < c₁ ∧ c₁ < 1 := ⟨(u + 1) / 2, by linarith, by linarith⟩
  have hloc := Work.OddRadon.radonInverse_radonPhi_local n hn hc₁lt hsm hu0 huc₁
  rw [hloc]
  -- Evaluate the reconstructed profile at `u` and at `-u`.
  have hpu : rhoNew R r u = R (Real.arccos u) := rhoNew_of_nonneg hu0.le
  have hpn : rhoNew R r (-u) = r (Real.arccos u) := by
    rw [rhoNew_of_neg (by linarith : -u < 0), neg_neg]
  rw [hpu, hpn]
  -- Read off the first two-power equation at the normal angle `arccos u`.
  have hαmem : Real.arccos u ∈ Set.Icc 0 (Real.pi / 2) :=
    ⟨Real.arccos_nonneg u, (Real.arccos_le_pi_div_two).mpr hu0.le⟩
  have hcos : Real.cos (Real.arccos u) = u := Real.cos_arccos (by linarith) hu1.le
  have hsys := (hRsys (Real.arccos u) hαmem).1
  rw [hcos] at hsys
  have hGluePhi : GluePhi n ρa (Real.arccos u)
      = 2 * Work.OddRadon.radonInverse n (GlueF n ρa) u := by
    simp only [GluePhi, hcos]
  rw [hGluePhi] at hsys
  rw [show u ^ 2 / 2 * (R (Real.arccos u) ^ (2 * n + 2) + r (Real.arccos u) ^ (2 * n + 2))
        = (R (Real.arccos u) ^ (2 * n + 2) + r (Real.arccos u) ^ (2 * n + 2)) * u ^ 2 / 2
      by ring, hsys]
  ring

end Work.OddCurve.LowSlope
