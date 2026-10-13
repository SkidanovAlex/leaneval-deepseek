import Mathlib
import Submission.Work.DSM5c.Lp.ChartCmpMap
import Submission.Work.DSPB1.All

/-!
# DSM5c/Lp — universe-polymorphic comparison lemmas for the transport `Θ`

Universe-polymorphic restatements (at `Type u`) of the three ring-level computations that
underpin the transport `Θ` of `Submission/Work/DSM5c/Lp/ThetaCoord.lean`:

* `Work.DSM5c.Lp.chartCmpMap_mapU` — naturality of the mod-`p` comparison `chartCmpMap` in `S`
  (the `Type 0` original is `Work.DSM5c.Lp.chartCmpMap_map`);
* `Work.DSM5c.Lp.chartLRingHom_eq_mk_chartPhiU` — `chartLRingHom` on a chosen representative
  (`Work.DSM5c.Lp.chartLRingHom_eq_mk_chartPhi`);
* `Work.DSM5c.Lp.chartLRingHom_varpiU` — the *vector match*: the class of `ϖ_k` in
  `L_S = R_S ⧸ (φ_S (ϖ♭)^p)` under `chartLAlg` is the class of the tilt
  `(ϖ♭)^{1/p^k} = varpiTiltShift Q k` (`Work.DSM5c.Lp.chartLRingHom_varpi`).

The originals live in modules pinned at `Type 0` (and `ThetaCmp.lean` also carries a
`maxHeartbeats` off the build guard's limit); the assembly of the M5c node lives at `Type a`, so
the copies below are needed verbatim.  The proofs transfer unchanged.
-/

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 800000
set_option allowUnsafeReducibility true
set_option backward.isDefEq.respectTransparency false

attribute [local reducible] Work.DSM5c.chartTiltGen Work.DSM5c.tiltChart
  Work.DSM5c.Lp.chartLpRObj Work.DSM5c.Lp.chartLpROfHom
  DSMap.Mix2.perfChartRing DSMap.Mix2.perfChartPresheaf DSMap.Mix2.locPresheaf
  Work.DSM5c.Lp.chartLQObj Work.DSM5c.Lp.chartLQOfHom Work.DSM5c.Lp.chartLQEta
  Work.DSM5c.Lp.chartCmpLinear Work.DSM5c.Lp.chartDpTop

namespace Work.DSM5c.Lp

open CategoryTheory DSMap DSMap.Mix DSMap.Mix2
open CategoryTheory.Limits Opposite

universe u

variable {p : ℕ} [Fact p.Prime] {W : Type u} [CommRing W] [Fact ¬IsUnit (p : W)]
  [IsAdicComplete (Ideal.span {(p : W)}) W] {ι : Type u} [Finite ι] [DecidableEq ι]

/-- **Naturality of the mod-`p` comparison along a restriction** (universe-polymorphic). -/
theorem chartCmpMap_mapU (Q : DSMap.PerfectoidData p W)
    (hθ : Function.Surjective (WittVector.fontaineTheta (p := p) (R := W)))
    (t : ι → W) (tr : ι → ℕ → W) (htr0 : ∀ i, tr i 0 = t i)
    (htr : ∀ i k, tr i (k + 1) ^ p = tr i k) (j₀ : ι) (e : ℕ)
    {S T : (Finset ι)ᵒᵖᵒᵖ} (f : S ⟶ T)
    (x : ↥(chartLQObj Q hθ t tr htr0 htr j₀ e S)) :
    chartCmpMap Q hθ t tr htr0 htr j₀ e T.unop.unop
        ((chartLQOfHom Q hθ t tr htr0 htr j₀ e f).hom x) =
      (chartLpROfHom Q t tr htr0 htr j₀ e f).hom
        (chartCmpMap Q hθ t tr htr0 htr j₀ e S.unop.unop x) := by
  letI := chartDAlg Q hθ t tr htr0 htr j₀ e S.unop.unop
  letI := chartDAlg Q hθ t tr htr0 htr j₀ e T.unop.unop
  obtain ⟨d, rfl⟩ := Submodule.Quotient.mk_surjective
    (chartDpTop Q hθ t tr htr0 htr j₀ e S.unop.unop) x
  rw [chartLQOfHom_mk, chartCmpMap_mk, chartCmpMap_mk]
  exact (chartCmpRingHom_naturality Q hθ t tr htr0 htr j₀ e
    (leOfHom f.unop.unop) d).symm

/-- **The defining description of `chartLRingHom` on a chosen representative** (universe-polymorphic
copy of `Work.DSM5c.Lp.chartLRingHom_eq_mk_chartPhi`). -/
theorem chartLRingHom_eq_mk_chartPhiU
    (Q : DSMap.PerfectoidData p W) (t : ι → W) (tr : ι → ℕ → W) (htr0 : ∀ i, tr i 0 = t i)
    (htr : ∀ i k, tr i (k + 1) ^ p = tr i k) (j₀ : ι) (e : ℕ) (S : Finset ι) (w : W)
    (x : PreTilt W p)
    (hx : Ideal.Quotient.mk (Ideal.span {tiltVarpi Q ^ p}) x =
      pb2Equiv (p := p) Q (Ideal.Quotient.mk (Ideal.span {(p : W)}) w)) :
    chartLRingHom Q t tr htr0 htr j₀ e S w =
      Ideal.Quotient.mk (chartLIdeal Q t tr htr0 htr j₀ e S)
        (chartPhi Q t tr htr0 htr j₀ e S x) := by
  simp only [chartLRingHom, RingHom.comp_apply]
  rw [show (pb2Equiv (p := p) Q).toRingHom (Ideal.Quotient.mk (Ideal.span {(p : W)}) w)
      = Ideal.Quotient.mk (Ideal.span {tiltVarpi Q ^ p}) x from hx.symm]
  rw [Ideal.Quotient.lift_mk]
  rfl

/-- **The vector match** (universe-polymorphic copy of `Work.DSM5c.Lp.chartLRingHom_varpi`): the
class of `ϖ_k` in `L_S = R_S ⧸ (φ_S(ϖ♭)^p)` is the class of the tilt
`(ϖ♭)^{1/p^k} = varpiTiltShift Q k`. -/
theorem chartLRingHom_varpiU (Q : DSMap.PerfectoidData p W)
    (t : ι → W) (tr : ι → ℕ → W) (htr0 : ∀ i, tr i 0 = t i)
    (htr : ∀ i k, tr i (k + 1) ^ p = tr i k) (j₀ : ι) (e : ℕ) (S : Finset ι) (k : ℕ) :
    chartLRingHom Q t tr htr0 htr j₀ e S (Q.ϖ k) =
      algebraMap (PreTilt W p)
        (tiltChart Q t tr htr0 htr j₀ e S ⧸ chartLIdeal Q t tr htr0 htr j₀ e S)
        ((frobeniusEquiv (PreTilt W p) p).symm^[k] (tiltVarpi Q)) := by
  have hx : Ideal.Quotient.mk (Ideal.span {tiltVarpi Q ^ p})
      (Work.DSPB1.varpiTiltShift Q k) =
      pb2Equiv Q (Ideal.Quotient.mk (Ideal.span {(p : W)}) (Q.ϖ k)) := by
    have h := pb2Equiv_mk_untilt Q (Work.DSPB1.varpiTiltShift Q k)
    rw [Work.DSPB1.varpiTiltShift_untilt Q k] at h
    exact h.symm
  refine (chartLRingHom_eq_mk_chartPhiU Q t tr htr0 htr j₀ e S (Q.ϖ k)
    (Work.DSPB1.varpiTiltShift Q k) hx).trans ?_
  have h2 : (frobeniusEquiv (PreTilt W p) p).symm^[k] (tiltVarpi Q) =
      Work.DSPB1.varpiTiltShift Q k := by
    rw [tiltVarpi_eq_varpiTilt, ← Work.DSPB1.varpiTiltShift_eq_symm]
  rw [h2]
  rw [IsScalarTower.algebraMap_apply (PreTilt W p)
      (↥(tiltChart Q t tr htr0 htr j₀ e S))
      (↥(tiltChart Q t tr htr0 htr j₀ e S) ⧸ chartLIdeal Q t tr htr0 htr j₀ e S),
    Ideal.Quotient.algebraMap_eq]
  rfl

end Work.DSM5c.Lp
