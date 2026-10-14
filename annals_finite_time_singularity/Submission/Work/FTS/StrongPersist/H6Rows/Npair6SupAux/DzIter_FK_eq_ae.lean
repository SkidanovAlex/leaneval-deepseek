import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.FTS.StrongPersist.N6_fkH
import Submission.Work.FTS.TransportS.t3SlotGuarded

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongPersist.H6Rows.Npair6SupAux

open MeasureTheory

/-! ## `D_z^j (FK f) = FK (D_z^j f)` almost everywhere

`FK f z = ∫_θ K(θ)·f(z,θ) dθ = Qang f 0 z` is the angular moment of `f` (`FK_eq_Qang`), while
`Qang f j z = ∫_θ K(θ)·D_z^j f (z,θ) dθ` is its `j`-th angular moment.  The level-six
`z`-calculus `QangAe6` identifies the `D_z`-iterates of the radial function `q := Qang f 0`
with the higher moments, `D_z^j q = Qang f j`, almost everywhere (for `j ≤ 6`).  Reading the
same identity through `FK_eq_Qang` — once for `f` and once for `D_z^j f` — gives the claim:

* `D_z^j (FK f) = D_z^j q` because `FK f = q` as functions of `z`
  (`Work.Elliptic.DzIter_rad` converts the two-dimensional `D_z`-iterates of the radial
  function `(z,θ) ↦ q z` into the one-dimensional ones `DzdIter` of `q`);
* `D_z^j q = Qang f j` a.e. (`QangAe6`);
* `Qang f j = Qang (D_z^j f) 0 = FK (D_z^j f)` (`DzIter_zero` and `FK_eq_Qang`).

Only `z ∈ (0,∞)` is needed for the middle step and `Iz \ (0,∞) = {0}` is null. -/

/-- The pointwise form of `FK_eq_Qang`: `FK g y = Qang g 0 y` for every `y`. -/
theorem FK_eq_Qang_apply (g : ℝ → ℝ → ℝ) (y : ℝ) :
    Work.Construction.FK g y = Work.Elliptic.Qang g 0 y :=
  congrFun (congrFun (Work.FTS.StrongPersist.FK_eq_Qang g) y) 0

/-- `Qang (D_z^j f) 0 = Qang f j`, i.e. the `j`-th angular moment of `f` is the zeroth
angular moment of its `j`-th `D_z`-iterate.  (`DzIter 0` is the identity definitionally.) -/
theorem Qang_DzIter_zero (f : ℝ → ℝ → ℝ) (j : ℕ) :
    Work.Elliptic.Qang (Work.Spaces.DzIter j f) 0 = Work.Elliptic.Qang f j :=
  funext fun _ => rfl

theorem DzIter_FK_eq_ae {α : ℝ} {f : ℝ → ℝ → ℝ} (hf : Work.FTS.EllipticEst.SmoothOpen f)
    (hm : Work.Spaces.HkMem α 6 f) (j : ℕ) (hj : j ≤ 6) :
    ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz), ∀ θ : ℝ,
      Work.Spaces.DzIter j (fun z (_ : ℝ) => Work.Construction.FK f z) z θ
        = Work.Construction.FK (Work.Spaces.DzIter j f) z := by
  -- the a.e. level-six `z`-calculus of the angular moment `q = Qang f 0`
  have hae := Work.FTS.StrongPersist.QangAe6 hf hm
  -- `FK f = q` as functions of `z` alone
  have hFKwt : (fun w : ℝ => Work.Construction.FK f w)
      = fun w => Work.Elliptic.Qang f 0 w :=
    funext (FK_eq_Qang_apply f)
  -- transfer to a.e. statements on `Iz`, discarding the null point `z = 0`
  rw [MeasureTheory.ae_restrict_iff' (s := Work.Spaces.Iz) measurableSet_Ici]
  filter_upwards [hae, MeasureTheory.Measure.ae_ne volume (0 : ℝ)] with z hzQ hne hzI
  intro θ
  have hzpos : 0 < z := lt_of_le_of_ne (show (0 : ℝ) ≤ z from hzI) (Ne.symm hne)
  -- two-dimensional `D_z`-iterates of a radial function are one-dimensional ones
  have hrad : Work.Spaces.DzIter j (fun z (_ : ℝ) => Work.Construction.FK f z) z θ
      = Work.Elliptic.DzdIter j (fun w : ℝ => Work.Construction.FK f w) z :=
    Work.Elliptic.DzIter_rad (fun w : ℝ => Work.Construction.FK f w) j z θ
  rw [hrad, hFKwt, hzQ hzpos j (Finset.mem_range.mpr (by omega : j < 7))]
  -- the last step: `Qang f j = Qang (D_z^j f) 0 = FK (D_z^j f)`
  rw [FK_eq_Qang_apply (Work.Spaces.DzIter j f) z]
  exact congrFun (Qang_DzIter_zero f j) z

end Work.FTS.StrongPersist.H6Rows.Npair6SupAux
