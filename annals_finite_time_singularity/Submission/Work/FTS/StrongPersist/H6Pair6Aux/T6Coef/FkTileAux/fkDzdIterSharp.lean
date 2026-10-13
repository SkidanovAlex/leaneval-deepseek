import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.Defs
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6SupAux.DzIter_FK_eq_ae
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6BWork.FkAux.fkDzdIterSqLe

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The sharp a.e. pointwise bound on the `D_z`-iterates of the angular moment `FK f`

`FK f z = ∫_θ K(θ)·f(z,θ) dθ` is the zeroth angular moment of `f`; it is a function of `z`
alone.  The claim of this file is that for `f` in the honest open quadrant class
(`Work.FTS.EllipticEst.SmoothOpen`) with weighted energy `ℋ⁶` *and* `ℋ⁷`
(`Work.Spaces.HkMem`), and for `b ≤ 5`, the `b`-th radial iterate
`DzdIter b (FK f) = (z∂_z)^b (FK f)` is bounded almost everywhere in `z` by
`C·√(HkSq α (b+1) f)`, with a universal constant `C`.

This is obtained from the *squared* a.e. statement of the sibling
`Work.FTS.StrongPersist.H6Rows.Npair6BWork.FkAux.fkDzdIterSqLe` — which reads, for `b ≤ 6`,

`(D_z^b (FK f))² ≤ C₁·HkSq α (b+1) f` a.e. on `Iz`

— by two elementary steps:

* `D_z`-iterates of the *radial* function `(z,θ) ↦ FK f z` are the one-dimensional iterates
  `DzdIter` (`Work.Elliptic.DzIter_rad`, at `θ = 0`), so the sibling's `DzIter`-statement is
  literally about `DzdIter b (FK f)`;
* `|x| = √(x²)` and `√(ab) = √a·√b` turn the squared bound into the linear one, with the
  constant `√C₁` and the factor `√(HkSq α (b+1) f)`.

The statement here is *weaker* than the sibling's (`b ≤ 5`, `α ∈ (0,1]`, same data), so
nothing new is needed beyond the square root bookkeeping.
-/

namespace Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.FkTileAux

theorem fkDzdIterSharp : ∃ C : ℝ, 0 < C ∧ ∀ α ∈ Set.Ioc 0 1, ∀ (f : Work.FTS.Galerkin.Fn),
    Work.FTS.EllipticEst.SmoothOpen f → Work.Spaces.HkMem α 6 f → Work.Spaces.HkMem α 7 f →
    ∀ b : ℕ, b ≤ 5 → ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz),
      |Work.Elliptic.DzdIter b (fun z => Work.Construction.FK f z) z|
        ≤ C * Real.sqrt (Work.Spaces.HkSq α (b + 1) f) := by
  obtain ⟨C₁, hC₁pos, hC₁⟩ := Work.FTS.StrongPersist.H6Rows.Npair6BWork.FkAux.fkDzdIterSqLe
  refine ⟨Real.sqrt C₁, Real.sqrt_pos.mpr hC₁pos, ?_⟩
  intro α hα f hsm hm6 hm7 b hb
  have hb6 : b ≤ 6 := by omega
  filter_upwards [hC₁ hα.1 hsm hm6 hm7 b hb6] with z hz
  -- the two-dimensional `D_z`-iterates of a radial function are the one-dimensional ones
  rw [Work.Elliptic.DzIter_rad (fun w => Work.Construction.FK f w) b z 0] at hz
  calc |Work.Elliptic.DzdIter b (fun w => Work.Construction.FK f w) z|
      = Real.sqrt ((Work.Elliptic.DzdIter b (fun w => Work.Construction.FK f w) z) ^ 2) :=
        (Real.sqrt_sq_eq_abs _).symm
    _ ≤ Real.sqrt (C₁ * Work.Spaces.HkSq α (b + 1) f) := Real.sqrt_le_sqrt hz
    _ = Real.sqrt C₁ * Real.sqrt (Work.Spaces.HkSq α (b + 1) f) :=
        Real.sqrt_mul hC₁pos.le _

end Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.FkTileAux
