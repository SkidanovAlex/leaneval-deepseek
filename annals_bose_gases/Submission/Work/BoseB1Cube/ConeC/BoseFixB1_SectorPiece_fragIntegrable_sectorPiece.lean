import ChallengeDeps
import Submission.Work.BoseB1Cube.ConeC.BoseFixB1_SectorPiece_pairFrags_sectorPiece
import Submission.Work.BoseFixB1.SectorPiece.fragsIntegrable_of_measurable_bound
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB1.SectorPiece.fragIntegrable_sectorPiece`

Integrability over the centred box `abox N ℓ` of the seven pair-fragment integrands
`Work.BoseFixB1S.fg0 … fg4` (`Work.BoseFixB1S.BoxPotDefs`) of the box-potential split at the
**singular localised sliding kernels** `wSmallPair M ℓ d u f` of FS `eq:HBU`, for the *sector
piece* `sectorPiece (dlBox ℓ d u) k Φ` of a continuous state `Φ`.

The analytic content — a bounded measurable slot multiplier times `wSmallPair M ℓ d u f (x i) (x j)`
is integrable once `f` is integrable and supported in `ball 0 R0` with `R0 ≤ (ℓd)/16` — is the
delegated `Work.BoseFixB1.SectorPiece.fragsIntegrable_of_measurable_bound`
(`Submission/Work/BoseFixB1/SectorPiece/fragsIntegrable_of_measurable_bound.lean`), which is the
state-generic form of `Work.BoseFixB1.Clean.boxFragmentsIntegrable`: the state `Ψ` is only assumed
**measurable and bounded on the box** (no continuity), and the volume `boxMass ℓ d u` is *not*
assumed positive (when it vanishes, `abs_boxPInd_le_nonneg` bounds the projections).

This file supplies the two facts about the sector piece that make the state-generic lemma
applicable to `Ψ = 1_{n_{B(u)} = k}·Φ`, with `B(u) = dlBox ℓ d u`:

* `measurable_sectorPiece` — `sectorPiece B k Φ = 1_{sectorSet B k}·Φ` is measurable
  (`FockBridge.sectorSet_measurable`);
* `abs_sectorPiece_le` — `|sectorPiece B k Φ x| ≤ |Φ x|`, so the bound of `Φ` on the compact box
  `abox N ℓ` (from `Continuous Φ`) bounds the sector piece as well.

The sign/positivity hypotheses on `v` are used only to produce the integrability and the support of
the numerators `g₂ v h`, `g₀ v h`, `v` inside the state-generic lemma.
-/

namespace Work.BoseFixB1.SectorPiece

/-- Measurability of a sector piece: `sectorPiece B k Φ = 1_{n_B = k}·Φ` for a measurable box `B`
and a measurable state `Φ`. -/
private theorem measurable_sectorPiece {N : ℕ} {B : Set (EuclideanSpace ℝ (Fin 3))}
    (hB : MeasurableSet B) (k : ℕ) {Φ : Submission.BoseGases.X N → ℝ} (hΦ : Measurable Φ) :
    Measurable (Work.FockBridge.sectorPiece B k Φ) := by
  simpa only [Work.FockBridge.sectorPiece] using
    hΦ.indicator (Work.FockBridge.sectorSet_measurable B hB k)

/-- The sector piece is pointwise dominated by the state: `|1_{n_B = k}·Φ| ≤ |Φ|`. -/
private theorem abs_sectorPiece_le {N : ℕ} (B : Set (EuclideanSpace ℝ (Fin 3))) (k : ℕ)
    (Φ : Submission.BoseGases.X N → ℝ) (x : Submission.BoseGases.X N) :
    |Work.FockBridge.sectorPiece B k Φ x| ≤ |Φ x| := by
  rw [Work.FockBridge.sectorPiece]
  by_cases hx : x ∈ Work.FockBridge.sectorSet B k
  · rw [Set.indicator_of_mem hx]
  · rw [Set.indicator_of_notMem hx, abs_zero]
    positivity

theorem fragIntegrable_sectorPiece {v : EuclideanSpace ℝ (Fin 3) → ℝ} {R0 : ℝ}
    (hR0 : 0 < R0) (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R0)
    (hv : 0 ≤ v) (hvrad : _root_.BoseGases.IsRadial v) (hv1 : MeasureTheory.MemLp v 1)
    (h : Work.UBB.ScatSol v) {M : ℕ} (hM : 1 ≤ M) {ℓ d : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d)
    (hR : R0 ≤ ℓ * d / 16) (hRχ : R0 ≤ ℓ * Submission.BoseGases.chiR0)
    (u : EuclideanSpace ℝ (Fin 3)) {N : ℕ} (k : ℕ) {Φ : Submission.BoseGases.X N → ℝ}
    (hΦc : Continuous Φ) {i j : Fin N} (hij : i ≠ j) :
    (MeasureTheory.IntegrableOn (fun x : Submission.BoseGases.X N =>
        Work.BoseFixB1S.fg0 (Work.SmallBoxSliding.boxMass ℓ d u) (Submission.BoseGases.dlBox ℓ d u)
          (Submission.BoseGases.wSmallPair M ℓ d u (Submission.BoseGases.g2 v h))
          (Work.FockBridge.sectorPiece (Submission.BoseGases.dlBox ℓ d u) k Φ) i j x)
        (Submission.BoseGases.abox N ℓ) MeasureTheory.volume
      ∧ MeasureTheory.IntegrableOn (fun x : Submission.BoseGases.X N =>
        Work.BoseFixB1S.fg1 (Work.SmallBoxSliding.boxMass ℓ d u) (Submission.BoseGases.dlBox ℓ d u)
          (Submission.BoseGases.wSmallPair M ℓ d u (Submission.BoseGases.g2 v h))
          (Work.FockBridge.sectorPiece (Submission.BoseGases.dlBox ℓ d u) k Φ) i j x)
        (Submission.BoseGases.abox N ℓ) MeasureTheory.volume
      ∧ MeasureTheory.IntegrableOn (fun x : Submission.BoseGases.X N =>
        Work.BoseFixB1S.fg2a (Work.SmallBoxSliding.boxMass ℓ d u) (Submission.BoseGases.dlBox ℓ d u)
          (Submission.BoseGases.wSmallPair M ℓ d u (Submission.BoseGases.g2 v h))
          (Work.FockBridge.sectorPiece (Submission.BoseGases.dlBox ℓ d u) k Φ) i j x)
        (Submission.BoseGases.abox N ℓ) MeasureTheory.volume
      ∧ MeasureTheory.IntegrableOn (fun x : Submission.BoseGases.X N =>
        Work.BoseFixB1S.fg2b (Work.SmallBoxSliding.boxMass ℓ d u) (Submission.BoseGases.dlBox ℓ d u)
          (Submission.BoseGases.wSmallPair M ℓ d u (Submission.BoseGases.g2 v h))
          (Work.FockBridge.sectorPiece (Submission.BoseGases.dlBox ℓ d u) k Φ) i j x)
        (Submission.BoseGases.abox N ℓ) MeasureTheory.volume
      ∧ MeasureTheory.IntegrableOn (fun x : Submission.BoseGases.X N =>
        Work.BoseFixB1S.fg2c (Work.SmallBoxSliding.boxMass ℓ d u) (Submission.BoseGases.dlBox ℓ d u)
          (Submission.BoseGases.wSmallPair M ℓ d u (Submission.BoseGases.g0 v h))
          (Work.FockBridge.sectorPiece (Submission.BoseGases.dlBox ℓ d u) k Φ) i j x)
        (Submission.BoseGases.abox N ℓ) MeasureTheory.volume
      ∧ MeasureTheory.IntegrableOn (fun x : Submission.BoseGases.X N =>
        Work.BoseFixB1S.fg3 (Work.SmallBoxSliding.boxMass ℓ d u) (Submission.BoseGases.dlBox ℓ d u)
          (Submission.BoseGases.wSmallPair M ℓ d u (Submission.BoseGases.g0 v h))
          (Work.FockBridge.sectorPiece (Submission.BoseGases.dlBox ℓ d u) k Φ) i j x)
        (Submission.BoseGases.abox N ℓ) MeasureTheory.volume
      ∧ MeasureTheory.IntegrableOn (fun x : Submission.BoseGases.X N =>
        Work.BoseFixB1S.fg4 (Work.SmallBoxSliding.boxMass ℓ d u) (Submission.BoseGases.dlBox ℓ d u)
          (Submission.BoseGases.wSmallPair M ℓ d u v)
          (Submission.BoseGases.omC (Classical.choose h))
          (Work.FockBridge.sectorPiece (Submission.BoseGases.dlBox ℓ d u) k Φ) i j x)
        (Submission.BoseGases.abox N ℓ) MeasureTheory.volume) := by
  -- the state `Φ` is continuous hence bounded on the compact box
  obtain ⟨C, hCbd⟩ :=
    (Submission.BoseGases.abox_compact N hℓ).exists_bound_of_continuousOn hΦc.continuousOn
  have hCabs : ∀ x ∈ Submission.BoseGases.abox N ℓ, |Φ x| ≤ C := fun x hx => by
    simpa [Real.norm_eq_abs] using hCbd x hx
  -- the sector piece is measurable and inherits the bound
  have hΨm : Measurable (Work.FockBridge.sectorPiece (Submission.BoseGases.dlBox ℓ d u) k Φ) :=
    measurable_sectorPiece (Work.SmallBoxSliding.measurableSet_dlBox ℓ d u) k hΦc.measurable
  have hΨb : ∀ x ∈ Submission.BoseGases.abox N ℓ,
      |Work.FockBridge.sectorPiece (Submission.BoseGases.dlBox ℓ d u) k Φ x| ≤ C :=
    fun x hx => le_trans (abs_sectorPiece_le _ k Φ x) (hCabs x hx)
  exact fragsIntegrable_of_measurable_bound hR0 hv_supp hv hvrad hv1 h hM hℓ hd hR hRχ u
    hΨm hΨb hij

end Work.BoseFixB1.SectorPiece
