import Mathlib
import Submission.Work.Thom.ThomClass
import Submission.Work.Thom.Glue
import Submission.Work.Thom.ChartOrientation
import Submission.Work.Thom.localThomMap_cup_zero
import Submission.Work.Thom.chartCoeff_nonZeroDivisor

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

/-!
# The local Thom map of a Thom class over a chart piece is injective in degree `0`

For a real bundle `Z → B` of rank `n`, a Thom class `T` of `Z` and a chart index `i`, the class
`T.τ` restricted to the piece over any `W ⊆ Z.baseSet i` has an injective local Thom map in degree
`0`.  Equivalently (by the H⁰-linearity of the local Thom map, `Work.Thom.localThomMap_cup_zero`)
the coefficient of the restricted class with respect to the explicit chart class
`Work.Thom.localThomOfChart` is a non-zero-divisor; that statement is the delegated crux
`Work.Thom.chartCoeff_nonZeroDivisor`.

See `CRUX_PLAN.md` in this directory for the route to the crux (it uses the separating condition
`Work.Thom.openThom_eq_zero_of_baseSet_rank` together with the H⁰-evaluation toolkit).
-/

namespace Work.ThomBordism.Grassmann

noncomputable section

theorem localThomMapChartInjective {B : Type} [TopologicalSpace B] {F : Type}
    [NormedAddCommGroup F] [NormedSpace ℝ F] {ι : Type} [FiniteDimensional ℝ F]
    (Z : Work.TangentClasses.RealBundle B F ι) {n : ℕ} (hrank : Z.rank = n)
    (T : Work.Thom.ThomClass Z n) (i : ι) (W : Set B) (hW : W ⊆ Z.baseSet i) :
    Function.Injective (Work.Thom.localThomMap Z n W ((Work.Thom.PieceRes Z W n).hom T.τ) 0) := by
  -- the continuous linear equivalence `F ≃ ℝⁿ` supplied by the rank hypothesis
  have hfr : Module.finrank ℝ F = Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) := by
    rw [finrank_euclideanSpace_fin]
    exact hrank
  let e : F ≃L[ℝ] EuclideanSpace ℝ (Fin n) :=
    ContinuousLinearEquiv.ofFinrankEq (𝕜 := ℝ) (E := F) (F := EuclideanSpace ℝ (Fin n)) hfr
  -- the explicit chart class over `W`, with its Thom property, and the coefficient of `T.τ|_W`
  let τ'' : Work.Thom.PieceCoh Z W n := (Work.Thom.localThomOfChart Z n e i W hW).τ
  have hτ'' : ∀ k, Function.Bijective (Work.Thom.localThomMap Z n W τ'' k) :=
    (Work.Thom.localThomOfChart Z n e i W hW).isThom
  obtain ⟨c, hc⟩ := (hτ'' 0).2
    ((Nat.zero_add n).symm ▸ ((Work.Thom.PieceRes Z W n).hom T.τ))
  -- put the cast on the side needed by the crux and by the H⁰-linearity
  have hc' : (Work.Thom.PieceRes Z W n).hom T.τ
      = (Nat.zero_add n) ▸ (Work.Thom.localThomMap Z n W τ'' 0 c) := by
    rw [hc, eqRec_eq_cast, eqRec_eq_cast, cast_cast, cast_eq]
  -- the crux: the coefficient is a non-zero-divisor
  have hcrux : ∀ x : Work.Thom.Coh ℤ 0 ↥W,
      Work.Cohomology.cupH' ℤ (TopCat.toSSet.obj (TopCat.of ↥W)) 0 0 x c = 0 → x = 0 :=
    Work.Thom.chartCoeff_nonZeroDivisor Z hrank T i W hW e c (by simpa only [τ''] using hc')
  -- the restricted class is the chart class multiplied by the coefficient
  have hlin : ∀ x : Work.Thom.Coh ℤ 0 ↥W,
      Work.Thom.localThomMap Z n W ((Work.Thom.PieceRes Z W n).hom T.τ) 0 x
        = Work.Thom.localThomMap Z n W τ'' 0
            (Work.Cohomology.cupH' ℤ (TopCat.toSSet.obj (TopCat.of ↥W)) 0 0 x c) := by
    intro x
    rw [hc']
    exact Work.Thom.localThomMap_cup_zero Z n W τ'' x c
  -- conclude
  intro x y hxy
  rw [hlin x, hlin y] at hxy
  have h3 : Work.Cohomology.cupH' ℤ (TopCat.toSSet.obj (TopCat.of ↥W)) 0 0 x c
      = Work.Cohomology.cupH' ℤ (TopCat.toSSet.obj (TopCat.of ↥W)) 0 0 y c :=
    (hτ'' 0).1 hxy
  have h4 : Work.Cohomology.cupH' ℤ (TopCat.toSSet.obj (TopCat.of ↥W)) 0 0 (x - y) c = 0 := by
    rw [map_sub, LinearMap.sub_apply, h3, sub_self]
  exact sub_eq_zero.mp (hcrux (x - y) h4)

end

end Work.ThomBordism.Grassmann
