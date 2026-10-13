import Mathlib
import Submission.Work.DSM5c.Lp.ThetaCoord
import Submission.Work.DSM5c.Lp.ThetaBasicU
import Submission.Work.DSM5c.Lp.chartDToLp_existsU
import Submission.Work.DSM5b.CycleDefs

namespace Work.DSM5c.Lp

set_option maxHeartbeats 4000000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.dupNamespace false
set_option linter.style.haveILetI false

namespace Work.DSM5c.Lp

open CategoryTheory DSMap DSMap.Mix DSMap.Mix2

universe u

variable {p : ℕ} [Fact p.Prime] {W : Type u} [CommRing W] [Fact ¬IsUnit (p : W)]
  [IsAdicComplete (Ideal.span {(p : W)}) W] {ι : Type u} [Finite ι] [DecidableEq ι]

/-- **The component of the chart coaugmentation `chartCoaugW t` at a `0`-simplex.**  This is the
`0`-simplex case of `Work.DSM5b.ccCoaug_apply`, restated in the `cechFam`/`cechIdx` normal form used
by `Submission/Work/DSM5c/Lp/ThetaCoord.lean`. -/
theorem ThetaCoaug_chartCoaugW_π (t : ι → W) (w : W) (y : Fin (0 + 1) → ι) :
    (CategoryTheory.Limits.Pi.π
        (cechFam (ι := ι) (DSMap.Mix2.chartPresheaf t) 0) y).hom
        ((DSMap.Mix2.chartCoaugW t).hom w) =
      algebraMap W ↥(DSMap.Mix2.chartRing t ((cechIdx (ι := ι) 0 y).unop.unop)) w :=
  Work.DSM5b.ccCoaug_apply W ι t w y

/-- **The component of the perfected chart coaugmentation `perfChartCoaug` at a `0`-simplex.** -/
theorem ThetaCoaug_perfChartCoaug_π
    (Q : DSMap.PerfectoidData p W)
    (t : ι → W) (tr : ι → ℕ → W) (htr0 : ∀ i, tr i 0 = t i)
    (htr : ∀ i k, tr i (k + 1) ^ p = tr i k) (j₀ : ι) (e : ℕ)
    (a : PreTilt W p) (y : Fin (0 + 1) → ι) :
    (CategoryTheory.Limits.Pi.π
        (cechFam (ι := ι)
          (perfChartPresheaf p (chartTiltGen Q t tr htr0 htr j₀ e)) 0) y).hom
        ((perfChartCoaug p (chartTiltGen Q t tr htr0 htr j₀ e)).hom a) =
      algebraMap (PreTilt W p)
        ↥(tiltChart Q t tr htr0 htr j₀ e ((cechIdx (ι := ι) 0 y).unop.unop)) a := by
  rw [DSMap.Mix2.perfChartCoaug]
  exact Work.DSM5b.ccPiLift_apply
    (f := cechFam (ι := ι)
      (perfChartPresheaf p (chartTiltGen Q t tr htr0 htr j₀ e)) 0)
    (p := fun z => ModuleCat.ofHom (Algebra.linearMap (PreTilt W p)
      ↥(tiltChart Q t tr htr0 htr j₀ e ((cechIdx (ι := ι) 0 z).unop.unop)))) y a

/-- **The coaugmentation identity for the transport `Θ`.**  For the diagonal mod-`p` chart
coaugmentation `ē := chartCoaugW t ≫ (Č η).f 0 ≫ (Č chartLQEta).f 0` (whose component at `{i}` is
`w • 1 ∈ L_{i}`) and any representative `x : PreTilt W p` of `pb2Equiv (mk w)` in
`W♭ ⧸ (ϖ♭)^p`, the transport `Θ_0` sends `ē.hom w` to the tilt-side coaugmentation
`chartLpRCoaug.hom x` (whose component at `{i}` is the class of `x`).  Blueprint:
`Submission/Work/DSM5c/Lp/probe/Stmts.lean` (`stmt_Theta_coaug`).  Ingredients:
`Work.DSM5c.Lp.chartLRingHom_eq_mk_chartPhiU` (`ThetaBasicU.lean`) and the identities
`chartLQEta.app = mkQ` (`chartLQEta_app_eq`), the W-linearity `hη` of `η`,
`chartCmpRingHom_algebraMap'` (`chartDToLp_exists.lean`) and `perfChartToLpR_app_mk`
(`ChartLpRQuot.lean`). -/
theorem Theta_coaugU {p : ℕ} [Fact p.Prime] {W : Type u} [CommRing W] [Fact ¬IsUnit (p : W)]
    [IsAdicComplete (Ideal.span {(p : W)}) W] {ι : Type u} [Finite ι] [DecidableEq ι]
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
    (w : W) (x : PreTilt W p)
    (hx : Ideal.Quotient.mk (Ideal.span {Work.DSM5c.tiltVarpi Q ^ p}) x =
      Work.DSM5c.pb2Equiv Q (Ideal.Quotient.mk (Ideal.span {(p : W)}) w)) :
    Work.DSM5c.Lp.Theta Q hθ t tr htr0 htr j₀ e 0
        ((((cechComplexFunctor (chartIdx ι)).map
          (Work.DSM5c.Lp.chartLQEta Q hθ t tr htr0 htr j₀ e)).f 0).hom
          ((((cechComplexFunctor (chartIdx ι)).map η).f 0).hom ((chartCoaugW t).hom w))) =
      (Work.DSM5c.Lp.chartLpRCoaug Q t tr htr0 htr j₀ e).hom x := by
  refine (cech_pi_eq_iff (P := chartLpR Q t tr htr0 htr j₀ e) (q := 0)).mpr fun y => ?_
  rw [Theta_π Q hθ t tr htr0 htr j₀ e 0 _ y]
  set S0 : Finset ι := (cechIdx (ι := ι) 0 y).unop.unop with hS0
  rw [cech_map_π_apply (chartLQEta Q hθ t tr htr0 htr j₀ e) 0 _ y]
  rw [cech_map_π_apply η 0 _ y]
  rw [ThetaCoaug_chartCoaugW_π t w y]
  rw [hη (cechIdx (ι := ι) 0 y) w]
  rw [chartLQEta_app_eq, chartCmpMap_mk]
  letI : Algebra W (untiltOf (tiltChart Q t tr htr0 htr j₀ e S0)
      (chartPhi Q t tr htr0 htr j₀ e S0)) := chartDAlg Q hθ t tr htr0 htr j₀ e S0
  have h1 : chartCmpRingHom Q hθ t tr htr0 htr j₀ e S0 (w • 1) =
      chartLRingHom Q t tr htr0 htr j₀ e S0 w := by
    rw [show (w • (1 : untiltOf (tiltChart Q t tr htr0 htr j₀ e S0)
        (chartPhi Q t tr htr0 htr j₀ e S0))) =
        algebraMap W (untiltOf (tiltChart Q t tr htr0 htr j₀ e S0)
          (chartPhi Q t tr htr0 htr j₀ e S0)) w from by
      rw [Algebra.smul_def, mul_one]]
    exact chartCmpRingHom_algebraMap' Q hθ t tr htr0 htr j₀ e S0 w
  rw [h1, chartLRingHom_eq_mk_chartPhiU Q t tr htr0 htr j₀ e S0 w x hx]
  rw [chartLpRCoaug, ModuleCat.comp_apply]
  rw [cech_map_π_apply (perfChartToLpR Q t tr htr0 htr j₀ e) 0 _ y]
  rw [ThetaCoaug_perfChartCoaug_π Q t tr htr0 htr j₀ e x y]
  exact (perfChartToLpR_app_mk Q t tr htr0 htr j₀ e (cechIdx (ι := ι) 0 y)
    (chartPhi Q t tr htr0 htr j₀ e S0 x)).symm

end Work.DSM5c.Lp

universe u

open CategoryTheory DSMap DSMap.Mix DSMap.Mix2

/-- Restatement of `Work.DSM5c.Lp.Work.DSM5c.Lp.Theta_coaugU` under the name
`Work.DSM5c.Lp.Theta_coaugU` announced for this lemma by the request (`Work.DSM5c.Lp` is the
namespace attached to the module `Submission.Work.DSM5c.Lp.Theta_coaugU`); the declaration above is
the primitive one. -/
theorem Theta_coaugU {p : ℕ} [Fact p.Prime] {W : Type u} [CommRing W] [Fact ¬IsUnit (p : W)]
    [IsAdicComplete (Ideal.span {(p : W)}) W] {ι : Type u} [Finite ι] [DecidableEq ι]
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
    (w : W) (x : PreTilt W p)
    (hx : Ideal.Quotient.mk (Ideal.span {Work.DSM5c.tiltVarpi Q ^ p}) x =
      Work.DSM5c.pb2Equiv Q (Ideal.Quotient.mk (Ideal.span {(p : W)}) w)) :
    Work.DSM5c.Lp.Theta Q hθ t tr htr0 htr j₀ e 0
        ((((cechComplexFunctor (chartIdx ι)).map
          (Work.DSM5c.Lp.chartLQEta Q hθ t tr htr0 htr j₀ e)).f 0).hom
          ((((cechComplexFunctor (chartIdx ι)).map η).f 0).hom ((chartCoaugW t).hom w))) =
      (Work.DSM5c.Lp.chartLpRCoaug Q t tr htr0 htr j₀ e).hom x :=
  Work.DSM5c.Lp.Work.DSM5c.Lp.Theta_coaugU Q hθ t tr htr0 htr j₀ e η hη w x hx

end Work.DSM5c.Lp
