/-
Copyright: work module for the Elgindi finite-time singularity project.

# `FkTileAux/fkPairingDefs` — the definitions and radial bounds for the top slot `(0,6,6)`

The supporting vocabulary of `FkTileAux.fkPairingTop`.  `T0 f z = ∫_θ (D_z^6 f z θ)²` and
`TT f z = w(z)² T₀ f z` are the two radial factors of the majorant, and `topG` is the
dominating density.  The two analytic inputs are

* `fkAeTop` — the level-six radial calculus of the angular moment,
  `D_z^6 (FK f) = FK (D_z^6 f)` a.e. (`QangAe6` through `DzIter_FK_eq_ae` and `DzIter_rad`);
* `A_sq_le_T` — the angular Cauchy–Schwarz bound `(FK (D_z^6 f) z)² ≤ 16 T₀(z)`
  (`FkAux.FKdzIter_sq_le`);
* `aesm_DzdIter_FK` — a.e. strong measurability of `z ↦ D_z^6 (FK f) z` on `Iz`.

Everything rests on `[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.MeasureTheory.Integral.Prod
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.Defs
import Submission.Work.FTS.TransportS.Slots
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6SupAux.DzIter_FK_eq_ae
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6BWork.rowAux
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6BWork.FkAux.FKdzIter_sq_le
import Submission.Work.Spaces.HkSq_terms
import Submission.Work.Spaces.sin_two_rpow

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.FkTileAux

open Work.FTS.StrongPersist.H6Rows.Npair6BWork (PM aesm_mixed)

set_option autoImplicit false
set_option maxHeartbeats 3200000

/-- `T₀ f z = ∫_θ (D_z^6 f z θ)²`, the *unweighted* angular energy of the sixth `D_z`-iterate. -/
def T0 (f : ℝ → ℝ → ℝ) (z : ℝ) : ℝ :=
  ∫ θ in Work.Spaces.Iθ, (Work.Spaces.DzIter 6 f z θ) ^ 2

/-- `TT f z = w(z)² T₀ f z`, the `ρ = w²` (i.e. `leafOne`-)weighted angular energy. -/
def TT (f : ℝ → ℝ → ℝ) (z : ℝ) : ℝ :=
  (Work.Spaces.w z) ^ 2 * T0 f z

/-- The dominating density of the top slot:
`(a_f/2) · (16 · leafEta · T₀ + leafEta · (D_z^6 f)²)`. -/
def topG (af : ℝ) (f : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ :=
  fun z θ => (af / 2) * (16 * (Work.FTS.TransportS.leafEta z θ * T0 f z)
    + Work.FTS.TransportS.leafEta z θ * (Work.Spaces.DzIter 6 f z θ) ^ 2)

/-- The level-six radial calculus of the angular moment: `D_z^6 (FK f) = FK (D_z^6 f)` almost
everywhere in `z` (`QangAe6`, together with `DzIter_rad` and `FK = Qang · 0`). -/
theorem fkAeTop {α : ℝ} {f : ℝ → ℝ → ℝ}
    (hsm : Work.FTS.EllipticEst.SmoothOpen f) (hmem : Work.Spaces.HkMem α 6 f) :
    ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz),
      Work.Elliptic.DzdIter 6 (fun z => Work.Construction.FK f z) z
        = Work.Construction.FK (Work.Spaces.DzIter 6 f) z := by
  have h := Work.FTS.StrongPersist.H6Rows.Npair6SupAux.DzIter_FK_eq_ae (α := α) hsm hmem 6 le_rfl
  filter_upwards [h] with z hz
  rw [← Work.Elliptic.DzIter_rad (fun z => Work.Construction.FK f z) 6 z 0]
  exact hz 0

/-- `(D_z^6 (FK f) z)² ≤ 16 T₀(z)` almost everywhere: the a.e. identity together with the
angular Cauchy–Schwarz bound on `FK (D_z^6 f)`. -/
theorem A_sq_le_T {α : ℝ} {f : ℝ → ℝ → ℝ}
    (hsm : Work.FTS.EllipticEst.SmoothOpen f) (hmem : Work.Spaces.HkMem α 6 f) :
    ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz),
      (Work.Elliptic.DzdIter 6 (fun z => Work.Construction.FK f z) z) ^ 2
        ≤ 16 * T0 f z := by
  have hone : ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz), 0 < z := by
    have h : (MeasureTheory.volume.restrict Work.Spaces.Iz)
        = MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ)) :=
      MeasureTheory.Measure.restrict_congr_set
        (MeasureTheory.Ioi_ae_eq_Ici (μ := MeasureTheory.volume) (a := (0 : ℝ))).symm
    rw [h]
    exact MeasureTheory.ae_restrict_mem measurableSet_Ioi
  filter_upwards [fkAeTop hsm hmem, hone] with z hz hzpos
  rw [hz, T0]
  exact Work.FTS.StrongPersist.H6Rows.Npair6BWork.FkAux.FKdzIter_sq_le (α := α) hsm hmem 6 le_rfl
    hzpos

/-- The radial factor `z ↦ D_z^6 (FK f) z` is a.e. strongly measurable on `Iz`: its a.e. value
`FK (D_z^6 f)` is an integral of the jointly measurable `(z,θ) ↦ D_z^6 f z θ · K θ`. -/
theorem aesm_DzdIter_FK {α : ℝ} {f : ℝ → ℝ → ℝ}
    (hsm : Work.FTS.EllipticEst.SmoothOpen f) (hmem : Work.Spaces.HkMem α 6 f) :
    MeasureTheory.AEStronglyMeasurable (fun z : ℝ =>
      Work.Elliptic.DzdIter 6 (fun z => Work.Construction.FK f z) z)
      (MeasureTheory.volume.restrict Work.Spaces.Iz) := by
  have hK : MeasureTheory.AEStronglyMeasurable (fun p : ℝ × ℝ => Work.Spaces.K p.2) PM := by
    have hm : Measurable (fun p : ℝ × ℝ => Work.Spaces.K p.2) := by
      simp only [Work.Spaces.K]
      fun_prop
    exact hm.aestronglyMeasurable
  have h1 : MeasureTheory.AEStronglyMeasurable
      (fun p : ℝ × ℝ => Work.Spaces.DzIter 6 f p.1 p.2 * Work.Spaces.K p.2) PM :=
    (aesm_mixed hsm 6 0).mul hK
  have h2 : MeasureTheory.AEStronglyMeasurable
      (fun z : ℝ => ∫ θ, Work.Spaces.DzIter 6 f z θ * Work.Spaces.K θ
        ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ))
      (MeasureTheory.volume.restrict Work.Spaces.Iz) :=
    h1.integral_prod_right'
  refine h2.congr ?_
  filter_upwards [fkAeTop hsm hmem] with z hz
  exact hz.symm

end Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.FkTileAux
