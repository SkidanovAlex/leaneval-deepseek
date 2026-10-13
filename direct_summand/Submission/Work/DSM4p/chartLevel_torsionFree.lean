import Mathlib
import Submission.Work.DSM4p.Chart

/-!
# DSM4p — `p`-torsion-freeness of the chart levels

The chart levels `D n = chartLevel hgr ϖ n ⊆ B[1/g]` of `Submission/Work/DSM4p/Chart.lean` are
subalgebras of the localisation `B[1/g]` (`g = gr 0`).  A localisation of a `p`-torsion-free ring
is again `p`-torsion-free (localisation is exact / flat over the base), and a subring of a
`p`-torsion-free ring is `p`-torsion-free.  Hence, whenever `p` is a nonzerodivisor on `B`, it is a
nonzerodivisor on every chart level:

  `IsSMulRegular (chartLevel hgr ϖ n) (p : chartLevel hgr ϖ n)`.

This is the torsion-freeness hypothesis needed to apply the estimates of
`Submission/Work/DSM4p/Estimate.lean`.
-/

namespace Work.DSM4p

universe a

/-- `p` is a nonzerodivisor on the ambient ring `B[1/g]` of the chart model, whenever it is a
nonzerodivisor on `B`: `Localization.Away (gr 0)` is flat over `B`, hence its “multiplication by
`p`” is injective as soon as the one of `B` is. -/
theorem isSMulRegular_chartAmbient {p : ℕ} [Fact p.Prime] {B : Type a} [CommRing B]
    (hp : IsSMulRegular B p) (gr : ℕ → B) :
    IsSMulRegular (ChartAmbient gr) (p : ChartAmbient gr) := by
  have hp' : IsSMulRegular B (p : B) := by
    intro x y h
    refine hp ?_
    simpa only [smul_eq_mul, nsmul_eq_mul] using h
  have h := IsSMulRegular.of_isLocalization (S := ChartAmbient gr)
    (p := Submonoid.powers (gr 0)) (R := B) (x := (p : B)) hp'
  simpa only [map_natCast] using h

/-- A subalgebra of a ring in which `p` is a nonzerodivisor is again `p`-torsion-free with respect
to its own scalar `p : ↥D`. -/
theorem isSMulRegular_subalgebra_natCast {p : ℕ} {B : Type a} [CommRing B] {A : Type a}
    [CommRing A] [Algebra B A] (D : Subalgebra B A) (h : IsSMulRegular A (p : A)) :
    IsSMulRegular D (p : D) := by
  intro x y hxy
  apply Subtype.ext
  apply h
  have h' := congrArg (fun z : D => (z : A)) hxy
  simpa only [smul_eq_mul, Subalgebra.coe_mul, SubringClass.coe_natCast] using h'

/-- **Every chart level is `p`-torsion-free.**  The chart level `chartLevel hgr ϖ n` is a
subalgebra of the localisation `B[1/g]`, which is `p`-torsion-free as soon as `B` is, and
torsion-freeness passes to subrings. -/
theorem chartLevel_torsionFree {p : ℕ} [Fact p.Prime] {B : Type a} [CommRing B]
    (hp : IsSMulRegular B p) (gr : ℕ → B) (hgr : Work.DSM4p.IsRootSystem p gr) (ϖ : ℕ → B) (n : ℕ) :
    IsSMulRegular (Work.DSM4p.chartLevel hgr ϖ n) (p : Work.DSM4p.chartLevel hgr ϖ n) :=
  isSMulRegular_subalgebra_natCast _ (isSMulRegular_chartAmbient hp gr)

end Work.DSM4p
