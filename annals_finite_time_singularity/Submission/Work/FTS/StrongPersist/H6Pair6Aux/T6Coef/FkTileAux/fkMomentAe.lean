import Mathlib.MeasureTheory.Integral.Prod
import Submission.Work.Construction.Defs
import Submission.Work.Elliptic.L12Aux
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.Spaces.aesm_of_continuousOn_Qd
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6SupAux.DzIter_FK_eq_ae
import Submission.Work.FTS.OpenPkg.QangOpen

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# Almost-everywhere strong measurability of the `D_z`-iterates of the angular moment `FK f`

`Work.Construction.FK f z = ∫_θ K(θ)·f(z,θ) dθ` is the zeroth angular moment of `f`, i.e. a
function of `z` alone (`FK_eq_Qang_apply`: `FK f = Qang f 0`).  The claim of this file is that
for `f` in the honest open-quadrant class `Work.FTS.EllipticEst.SmoothOpen` with weighted energy
`Work.Spaces.HkMem α 6 f`, and for every `b₁ ≤ 6`, the `b₁`-th radial iterate
`DzdIter b₁ (FK f) = (z∂_z)^{b₁}(FK f)` — pushed forward to the square `ℝ × ℝ` by the first
projection — is almost everywhere strongly measurable for the product of the restrictions of
Lebesgue measure to `Iz = [0,∞)` and `Iθ = [0,π/2]`.

There is no analysis here beyond two identifications.

* **The a.e. identity on the half-line.**  `FK f` and `Qang f 0` are the *same* function of `z`
  (`FK_eq_Qang_apply`), so their `z∂_z`-iterates agree at every `z > 0`
  (`DzdIter_congr_Ioi`); and the level-six `z`-calculus of the angular moments
  (`QangAe6`) identifies those iterates with the higher moments `Qang f b₁` almost everywhere.
  Hence `DzdIter b₁ (FK f) = Qang f b₁` a.e. on the half-line, and since `Iz \ (0,∞) = {0}` is
  null the `0 < z` proviso can be dropped after restricting to `Iz`.

* **Strong measurability of the moments.**  `Qang f b₁ z = ∫_θ Ktheta θ · D_z^{b₁}f(z,θ) dθ`
  is the `θ`-integral of a function which is *continuous* on the open quadrant
  (`continuousOn_Ktheta_DzIter_open`, from `SmoothOpen f` alone, at any level `b₁`), hence —
  by `aesm_of_continuousOn_Qd` + `AEStronglyMeasurable.integral_prod_right'` — an almost
  everywhere strongly measurable function of `z` on `Iz`.  No `HkMem` hypothesis is needed for
  this half (only the a.e. identity above consumes it).

* **Push-forward.**  A function of `z` alone which is a.e. strongly measurable on `Iz` is a.e.
  strongly measurable for `(volume.restrict Iz).prod (volume.restrict Iθ)`: the first projection
  is quasi-measure-preserving (`Measure.quasiMeasurePreserving_fst`), so
  `AEStronglyMeasurable.comp_quasiMeasurePreserving` applies.  (Note the product measure is
  *not* finite, so this step genuinely uses the quasi-measure-preserving form rather than a
  Fubini statement.)

The proof is complete and rests on `[propext, Classical.choice, Quot.sound]`.
-/

namespace Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.FkTileAux

open MeasureTheory Set Filter
open scoped Real Topology

theorem fkMomentAe : ∀ (α : ℝ) (f : ℝ → ℝ → ℝ) (b₁ : ℕ),
    Work.FTS.EllipticEst.SmoothOpen f → Work.Spaces.HkMem α 6 f → b₁ ≤ 6 →
    MeasureTheory.AEStronglyMeasurable
      (fun p : ℝ × ℝ => Work.Elliptic.DzdIter b₁ (fun z => Work.Construction.FK f z) p.1)
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) := by
  intro α f b₁ hsm hmem hb
  -- ## the a.e. identity `D_z^{b₁}(FK f) = Qang f b₁` on the open half-line
  have hpoint : ∀ᵐ z ∂(MeasureTheory.volume),
      0 < z → Work.Elliptic.DzdIter b₁ (fun z => Work.Construction.FK f z) z
        = Work.Elliptic.Qang f b₁ z := by
    filter_upwards [Work.FTS.StrongPersist.QangAe6 (α := α) (g := f) hsm hmem] with z hz
    intro hzpos
    calc Work.Elliptic.DzdIter b₁ (fun z => Work.Construction.FK f z) z
        = Work.Elliptic.DzdIter b₁ (fun z => Work.Elliptic.Qang f 0 z) z :=
          Work.FTS.StrongPersist.DzdIter_congr_Ioi
            (fun y _ => Work.FTS.StrongPersist.H6Rows.Npair6SupAux.FK_eq_Qang_apply f y)
            b₁ z hzpos
      _ = Work.Elliptic.Qang f b₁ z := hz hzpos b₁ (Finset.mem_range.mpr (by omega))
  -- ## the same identity restricted to `Iz` (where `z = 0` may be discarded),
  -- in the direction needed for `AEStronglyMeasurable.congr`
  have hrest : ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz),
      Work.Elliptic.Qang f b₁ z
        = Work.Elliptic.DzdIter b₁ (fun z => Work.Construction.FK f z) z := by
    have hIz : MeasurableSet Work.Spaces.Iz := measurableSet_Ici
    rw [MeasureTheory.ae_restrict_iff' hIz]
    filter_upwards [hpoint, MeasureTheory.Measure.ae_ne volume (0 : ℝ)] with z hz hne hzI
    exact (hz (lt_of_le_of_ne hzI (Ne.symm hne))).symm
  -- ## `z ↦ Qang f b₁ z` is a.e. strongly measurable on `Iz`
  have hQ : MeasureTheory.AEStronglyMeasurable (fun z => Work.Elliptic.Qang f b₁ z)
      (MeasureTheory.volume.restrict Work.Spaces.Iz) := by
    have h := (Work.Spaces.aesm_of_continuousOn_Qd
        (fun p : ℝ × ℝ => Work.Elliptic.Ktheta p.2 * Work.Spaces.DzIter b₁ f p.1 p.2)
        (Work.FTS.OpenPkg.QangOpen.continuousOn_Ktheta_DzIter_open hsm b₁)).integral_prod_right'
    simpa only [Work.Elliptic.Qang] using h
  -- ## so is `z ↦ D_z^{b₁}(FK f) z`
  have hF : MeasureTheory.AEStronglyMeasurable
      (fun z => Work.Elliptic.DzdIter b₁ (fun z => Work.Construction.FK f z) z)
      (MeasureTheory.volume.restrict Work.Spaces.Iz) :=
    hQ.congr hrest
  -- ## push forward along the (quasi-measure-preserving) first projection
  exact hF.comp_quasiMeasurePreserving
    (Measure.quasiMeasurePreserving_fst
      (μ := MeasureTheory.volume.restrict Work.Spaces.Iz)
      (ν := MeasureTheory.volume.restrict Work.Spaces.Iθ))

end Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.FkTileAux
