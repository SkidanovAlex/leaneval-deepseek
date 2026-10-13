import Mathlib.Algebra.Module.Pi
import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Submission.Work.FTS.RegExportIface.Defs
import Submission.Work.FTS.FinalV2.Defs
import Submission.Work.FTS.RegPkgGal.R5Parts

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open Filter Set
open scoped Topology

namespace Work.FTS_RegExport.RXR1

/-! ## Local vocabulary for `hj_cluster`

`Gs α g = gS α (tauExt g)` is the sanitised right-Taylor family on which the R1 block is read, and
`Ps α Φs E g = psiR α Φs E (tauExt g)` the stream function of the R5 package.  The remaining
abbreviations decompose the right-hand side of the fake-time equation at `τ = 0` into its five
elementary pieces, so that the `R5Parts` jet / `z`-derivative fields apply to them verbatim.  The
profile exponent of the dynamic equation is `pExp α = 3α`, which is what `R5Parts` itself uses. -/

/-- The sanitised right-Taylor family. -/
abbrev Gs (α : ℝ) (g : Work.FTS.Galerkin.Fam) : Work.FTS.Galerkin.Fam :=
  Work.FTS.FinalV2.gS α (Work.FTS.FinalV2.tauExt g)

/-- The R5 stream function of the right-Taylor family. -/
abbrev Ps (α : ℝ) (Φs : Work.FTS.Galerkin.Fn) (E : Work.FTS.Galerkin.Fn →ₗ[ℝ] Work.FTS.Galerkin.Fn)
    (g : Work.FTS.Galerkin.Fam) : Work.FTS.Galerkin.Fam :=
  Work.FTS.RegExportIface.psiR α Φs E (Work.FTS.FinalV2.tauExt g)

/-- The within-filter of the cluster: `(z,τ) → (0,τ₀)` with `z > 0`. -/
abbrev Filt (τ₀ : ℝ) : Filter (ℝ × ℝ) :=
  nhdsWithin ((0 : ℝ), τ₀) (Set.prod (Set.Ioi (0 : ℝ)) Set.univ)

abbrev RP1 (α : ℝ) (G : Work.FTS.Galerkin.Fam) (z θ : ℝ) : ℝ :=
  -(Work.Coercivity.LGammaT (Work.FTS.Regularity.pExp α) (Work.FTS.Regularity.gSlice G 0) z θ)

abbrev RP2 (α : ℝ) (G : Work.FTS.Galerkin.Fam) (z θ : ℝ) : ℝ :=
  Work.Construction.N0 (Work.FTS.Regularity.pExp α)
    (Work.Construction.Ftau (Work.FTS.Regularity.pExp α) G 0) (Work.FTS.Regularity.gSlice G 0) z θ

abbrev RP3 (α : ℝ) (G Φ : Work.FTS.Galerkin.Fam) (z θ : ℝ) : ℝ :=
  Work.Construction.N (Work.FTS.Regularity.pExp α)
    (Work.Construction.Ftau (Work.FTS.Regularity.pExp α) G 0) (Work.FTS.Regularity.gSlice Φ 0) z θ

abbrev RP4 (α : ℝ) (G Φ : Work.FTS.Galerkin.Fam) (z θ : ℝ) : ℝ :=
  Work.Construction.Nstar (Work.FTS.Galerkin.muDyn (Work.FTS.Regularity.pExp α) Φ G 0)
    (Work.FTS.Galerkin.lamDyn (Work.FTS.Regularity.pExp α) Φ G 0)
    (Work.FTS.Regularity.gSlice G 0) z θ

abbrev mbar0 (α : ℝ) (G Φ : Work.FTS.Galerkin.Fam) : ℝ :=
  Work.Construction.mubar
    (Work.Construction.N0 (Work.FTS.Regularity.pExp α)
      (Work.Construction.Ftau (Work.FTS.Regularity.pExp α) G 0) (Work.FTS.Regularity.gSlice G 0))
    (Work.Construction.N (Work.FTS.Regularity.pExp α)
      (Work.Construction.Ftau (Work.FTS.Regularity.pExp α) G 0) (Work.FTS.Regularity.gSlice Φ 0))

/-- The right-hand side of the fake-time equation at `τ = 0`. -/
abbrev RHSo (α : ℝ) (G Φ : Work.FTS.Galerkin.Fam) (z θ : ℝ) : ℝ :=
  Work.FTS.Galerkin.dynLin (Work.FTS.Regularity.pExp α) G 0 z θ
    + Work.FTS.Galerkin.dynRHS (Work.FTS.Regularity.pExp α) Φ G 0 z θ

/-- `Galerkin.slice` and `Regularity.gSlice` are the same family slice (definitionally). -/
theorem slice_eq_gSlice (g : Work.FTS.Galerkin.Fam) (τ : ℝ) :
    Work.FTS.Galerkin.slice g τ = Work.FTS.Regularity.gSlice g τ := rfl

/-- The decomposition of the right-hand side into its five elementary pieces. -/
theorem RHSo_eq {α : ℝ} {G Φ : Work.FTS.Galerkin.Fam} (z θ : ℝ) :
    RHSo α G Φ z θ = RP1 α G z θ
      + (-(mbar0 α G Φ) * Work.Construction.AK (Work.FTS.Regularity.pExp α) z θ
        + RP2 α G z θ + RP3 α G Φ z θ + RP4 α G Φ z θ) := by
  simp only [RHSo, RP1, RP2, RP3, RP4, mbar0, Work.FTS.Galerkin.dynLin, Work.FTS.Galerkin.dynRHS,
    Work.Construction.gRHS, slice_eq_gSlice]

end Work.FTS_RegExport.RXR1
