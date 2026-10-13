import Mathlib
import Submission.Work.DSM5c.ChartFunctor
import Submission.Work.DSM5c.Cech.chartCoaug_isCocycle

namespace Work.DSM5c.Cech

open CategoryTheory DSMap DSMap.Mix DSMap.Mix2

universe u

/-- **Universe-polymorphic restatement of `Work.DSM5c.Cech.chartCoaug_isCocycle`.**

The original is stated at `Type 0`; the frozen node `DSMap.Mix2.area_M5c` lives at `Type a`
(`W : Type a`, `ι : Type a`), so the assembly in `Submission/Work/DSM5c/Main.lean` needs this
declaration at an arbitrary universe.  The proof transfers verbatim: the original file already
contains the universe-polymorphic `Work.DSM5c.Cech.cech_coaug_map_d01` (the honest coaugmentation is
a `0`-cocycle and `Č η` is a chain map), of which this is the specialisation to
`P = Work.DSM5c.chartD …`; so
`import Submission.Work.DSM5c.Cech.chartCoaug_isCocycle` (and `Mathlib`,
`Submission.Work.DSM5c.ChartFunctor`) and close the goal with `exact cech_coaug_map_d01 t _ η w`.
Keep the original file. -/
theorem chartCoaug_isCocycleU {p : ℕ} [Fact p.Prime] {W : Type u} [CommRing W] [Fact ¬IsUnit (p : W)]
    [IsAdicComplete (Ideal.span {(p : W)}) W] {ι : Type u} [DecidableEq ι]
    (Q : DSMap.PerfectoidData p W)
    (hθ : Function.Surjective (WittVector.fontaineTheta (p := p) (R := W)))
    (t : ι → W) (tr : ι → ℕ → W) (htr0 : ∀ i, tr i 0 = t i)
    (htr : ∀ i k, tr i (k + 1) ^ p = tr i k) (j₀ : ι) (e : ℕ)
    (η : DSMap.Mix2.chartPresheaf t ⟶
      Work.DSM5c.chartD (p := p) (W := W) Q hθ t tr htr0 htr j₀ e)
    (hη : ∀ (S : (Finset ι)ᵒᵖᵒᵖ) (w : W),
      letI := Work.DSM5c.chartDAlg (p := p) (W := W) Q hθ t tr htr0 htr j₀ e S.unop.unop
      η.app S (algebraMap W (DSMap.Mix2.chartRing t S.unop.unop) w) =
        w • (1 : Work.DSM5c.untiltOf (p := p) (W := W)
          (Work.DSM5c.tiltChart Q t tr htr0 htr j₀ e S.unop.unop)
          (Work.DSM5c.chartPhi Q t tr htr0 htr j₀ e S.unop.unop)))
    (w : W) :
    (((cechComplexFunctor (chartIdx ι)).obj
        (Work.DSM5c.chartD (p := p) (W := W) Q hθ t tr htr0 htr j₀ e)).d 0 1).hom
      ((chartCoaugW t ≫
        ((cechComplexFunctor (chartIdx ι)).map η).f 0).hom w) = 0 := by
  exact cech_coaug_map_d01 t _ η w

end Work.DSM5c.Cech
