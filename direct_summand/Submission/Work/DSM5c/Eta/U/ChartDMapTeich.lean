import Mathlib
import Submission.Work.DSM5c.Eta.U.Setup
import Submission.Work.DSM5c.ChartFunctor

universe a

namespace Work.DSM5c.Eta.U

theorem chartDMap_teich {p : ℕ} [Fact p.Prime] {W : Type a} [CommRing W] [Fact ¬IsUnit (p : W)]
    [IsAdicComplete (Ideal.span {(p : W)}) W] {ι : Type a} [DecidableEq ι]
    (Q : DSMap.PerfectoidData p W)
    (hθ : Function.Surjective (WittVector.fontaineTheta (p := p) (R := W)))
    (t : ι → W) (tr : ι → ℕ → W) (htr0 : ∀ i, tr i 0 = t i)
    (htr : ∀ i k, tr i (k + 1) ^ p = tr i k) (j₀ : ι) (e : ℕ)
    {S T : Finset ι} (h : S ⊆ T) (y : ↥(Work.DSM5c.tiltChart Q t tr htr0 htr j₀ e S)) :
    Work.DSM5c.chartDMap Q hθ t tr htr0 htr j₀ e h (Work.DSM5c.Eta.U.teich Q t tr htr0 htr j₀ e S y)
      = Work.DSM5c.Eta.U.teich Q t tr htr0 htr j₀ e T
          (Work.DSM5c.tiltChartRes Q t tr htr0 htr j₀ e h y) := by
  show Work.DSM5c.untiltOf.map (Work.DSM5c.chartPhi Q t tr htr0 htr j₀ e S)
      (Work.DSM5c.chartPhi Q t tr htr0 htr j₀ e T)
      (Work.DSM5c.tiltChartRes Q t tr htr0 htr j₀ e h)
      (RingHom.ext fun r => Work.DSM5c.tiltChartRes_algebraMap Q t tr htr0 htr j₀ e h r)
      (Work.DSM5c.untiltOf.mk (Work.DSM5c.chartPhi Q t tr htr0 htr j₀ e S)
        (WittVector.teichmuller p y)) = _
  rw [Work.DSM5c.untiltOf.map_apply, WittVector.map_teichmuller, Work.DSM5c.Eta.U.teich]

end Work.DSM5c.Eta.U
