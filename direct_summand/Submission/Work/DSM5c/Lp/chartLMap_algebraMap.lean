import Mathlib
import Submission.Work.DSM5c.ChartLp

namespace Work.DSM5c.Lp

open CategoryTheory DSMap DSMap.Mix DSMap.Mix2

/-- **The defining description of `chartLRingHom` on a chosen representative**:
`chartLRingHom Q … S w` is the class in `L_S = R_S ⧸ (φ_S (ϖ♭)^p)` of `(chartPhi … S) x`, where
`x : PreTilt W p` represents `pb2Equiv Q (Ideal.Quotient.mk _ w)` in `W♭ ⧸ (ϖ♭)^p`
(`hx` is exactly `Ideal.Quotient.mk_surjective`'s witness statement).  This is the computation with
which one compares `chartLRingHom` for different `S`, the representative `x` being
`S`-independent. -/
theorem chartLRingHom_eq_mk_chartPhi {p : ℕ} [Fact p.Prime] {W : Type} [CommRing W]
    [Fact ¬IsUnit (p : W)] {ι : Type} [DecidableEq ι]
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

/-- **`chartLMap` is `W`-linear for the `W`-algebra structures `chartLAlg`** (through PB2).  This is
what makes `S ↦ L_S = R_S ⧸ (φ_S (ϖ♭)^p)` a presheaf of `W`-*modules* (`Work.DSM5c.chartLp`), the
codomain of the termwise surjection `Dp ⟶ Lp` of the M5c transport
(`Submission/Work/DSM5c/ChartLp.lean`).

Proof sketch: `chartLAlg = Algebra.mk (chartLRingHom …)`, and
`chartLRingHom Q … S w` is the class of `(chartPhi … S) x`, where `x` represents
`pb2Equiv Q (Ideal.Quotient.mk _ w)` in `W♭ ⧸ (ϖ♭)^p` (`Classical.choose` of
`Ideal.Quotient.mk_surjective`).  Then `chartLMap_mk` and `tiltChartRes_algebraMap` finish. -/
theorem chartLMap_algebraMap {p : ℕ} [Fact p.Prime] {W : Type} [CommRing W]
    [Fact ¬IsUnit (p : W)] [IsAdicComplete (Ideal.span {(p : W)}) W] {ι : Type} [DecidableEq ι]
    (Q : DSMap.PerfectoidData p W) (t : ι → W) (tr : ι → ℕ → W) (htr0 : ∀ i, tr i 0 = t i)
    (htr : ∀ i k, tr i (k + 1) ^ p = tr i k) (j₀ : ι) (e : ℕ) {S T : Finset ι} (h : S ⊆ T) (w : W) :
    letI := Work.DSM5c.chartLAlg Q t tr htr0 htr j₀ e S
    letI := Work.DSM5c.chartLAlg Q t tr htr0 htr j₀ e T
    Work.DSM5c.chartLMap Q t tr htr0 htr j₀ e h (algebraMap W _ w) = algebraMap W _ w := by
  obtain ⟨x, hx⟩ := Ideal.Quotient.mk_surjective (I := Ideal.span {tiltVarpi Q ^ p})
    (pb2Equiv (p := p) Q (Ideal.Quotient.mk (Ideal.span {(p : W)}) w))
  change Work.DSM5c.chartLMap Q t tr htr0 htr j₀ e h
      (Work.DSM5c.chartLRingHom Q t tr htr0 htr j₀ e S w) =
    Work.DSM5c.chartLRingHom Q t tr htr0 htr j₀ e T w
  rw [chartLRingHom_eq_mk_chartPhi Q t tr htr0 htr j₀ e S w x hx,
    chartLRingHom_eq_mk_chartPhi Q t tr htr0 htr j₀ e T w x hx]
  rw [Work.DSM5c.chartLMap_mk]
  exact congrArg (Ideal.Quotient.mk _)
    (Work.DSM5c.tiltChartRes_algebraMap Q t tr htr0 htr j₀ e h x)

end Work.DSM5c.Lp
