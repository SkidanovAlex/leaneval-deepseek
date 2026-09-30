import Mathlib
import Submission.Work.Final.All
import Submission.Work.LCSmooth.contMDiffOn_chrB
import Submission.Work.RiemLib.ChartCurvCont
import Submission.Work.RiemLib.CoeffSmooth2

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.LCSmooth

/-- Multiplying a `C^n` map into `E4` by a constant is `C^n` (local copy of the private helper of
`Submission/Work/LCSmooth/contMDiffOn_chrB.lean`, which is not exported).

Mathlib's `ContMDiffOn.const_smul` would give this from the instance
`ContMDiffConstSMul Work.Space.I4 n ℝ Work.Space.E4`, which is not registered (the class is
stated for a general action `Γ` on a manifold `M`, and the scalar action of `ℝ` on its own model
space is not covered by any instance).  The map `x ↦ c • x` is a continuous linear map, so we
compose with it directly. -/
private lemma contMDiffOn_const_smul_E4' {M : Type*} [TopologicalSpace M]
    [ChartedSpace Work.Space.E4 M] {n : WithTop ℕ∞} {s : Set M}
    (c : ℝ) {f : M → Work.Space.E4}
    (hf : ContMDiffOn Work.Space.I4 Work.Space.I4 n f s) :
    ContMDiffOn Work.Space.I4 Work.Space.I4 n (fun q => c • f q) s := by
  have h1 : ContMDiffOn Work.Space.I4 Work.Space.I4 n
      (fun x : Work.Space.E4 => c • x) Set.univ :=
    ((c • (1 : Work.Space.E4 →L[ℝ] Work.Space.E4)).contMDiffOn (s := Set.univ)).congr
      (fun x _ => by simp)
  exact (h1.comp hf (fun _ _ => Set.mem_univ _)).congr (fun q _ => rfl)

/-- **The derivative of the chart Christoffel symbol in the base point is also `C^∞`.**

`Submission.ChartCurv.dB C.cov x₀ p v a b` is the derivative of the Christoffel symbol
`q ↦ Submission.ChartCurv.chrB C.cov x₀ q a b` at `p` in the direction of the frame vector with
coordinates `v`.  On the chart source, that derivative is again a `C^∞` function of the base point
`p`, for fixed `v`, `a`, `b`.

This is the second piece of the "smooth coefficients" chapter behind the Koszul route: it is what
one differentiates once more to obtain the coordinate formula for the curvature tensor
(`Submission.ChartCurv.curvVec_eq_chart` uses `dB`).

Proof route.  On the chart source the chart representative of `p ↦ dB C.cov x₀ p v a b` is
`x ↦ ∑ᵢ ∑ⱼ ((coord i) a * (coord j) b) • fderiv ℝ (chrEntryModel C.cov x₀ i j) x v`: the frame
vector `frameVector x₀ p v` has the *constant* chart coordinates `v`, so
`mvfderiv_frameVector_eq_fderiv` (`Submission.Work.RiemLib.ChartCurvCont`) converts the `mvfderiv`
defining `dB` into the `fderiv` of the chart representative of `chrB`, and the latter expands in
the Christoffel entries (`Submission.ChartCurv.chrB_eq_sum_gammaEntry`,
`Submission.ChartCurv.mvfderiv_chrB_apply` in `Submission.Work.RiemLib.ChartCurvCont`).  Each
`chrEntryModel` is `C^∞` on the (open) chart target — this is the coordinate form of
`Work.LCSmooth.contMDiffOn_chrB`, which is proved in
`Submission/Work/LCSmooth/contMDiffOn_chrB.lean` — and `ContDiffOn.fderiv_of_isOpen` therefore
gives a `C^∞` function of `x`, evaluated at the constant `v`.  The nearby results
`Submission.ChartCurvCont.continuousAt_dB_prod` and
`CoeffSmooth2.contDiffOn_dB_along_Ioo` follow the same route and can be copied. -/
theorem contMDiffOn_dB {M : Type*} [TopologicalSpace M] [T2Space M]
    [ChartedSpace Work.Space.E4 M] [Work.Final.ChartedRiem M]
    [C : Work.Final.ChartedRiemConn M] (x₀ : M) (v a b : Work.Space.E4) :
    ContMDiffOn Work.Space.I4 Work.Space.I4 Work.Final.smoothGrade
      (fun q : M ↦ Submission.ChartCurv.dB C.cov x₀ q v a b)
      (chartAt Work.Space.E4 x₀).source := by
  classical
  -- The chart formula for `dB`: on the chart source, `dB` is the basis combination of the
  -- derivatives of the (fixed) coordinate models `chrEntryModel`.
  have hkey : ∀ q ∈ (chartAt Work.Space.E4 x₀).source,
      Submission.ChartCurv.dB C.cov x₀ q v a b
        = ∑ i, ∑ j, (((Module.finBasis ℝ Work.Space.E4).coord i) a *
            ((Module.finBasis ℝ Work.Space.E4).coord j) b) •
            fderiv ℝ (Submission.ChartCurvCont.chrEntryModel C.cov x₀ i j)
              ((extChartAt Work.Space.I4 x₀) q) v := by
    intro q hq
    rw [Submission.ChartCurv.dB,
      Submission.ChartCurv.mvfderiv_chrB_apply (cov := C.cov) x₀ q a b v hq]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [Submission.ChartCurvCont.mvfderiv_frameVector_eq_fderiv (I := Work.Space.I4) x₀ hq
      (Submission.ChartCurv.mdifferentiableAt_gammaEntry (cov := C.cov) x₀ i j hq) v]
    rfl
  -- Each summand is `C^∞` in the base point.
  have hG : ∀ i j : Fin (Module.finrank ℝ Work.Space.E4),
      ContMDiffOn Work.Space.I4 Work.Space.I4 Work.Final.smoothGrade
        (fun q : M => fderiv ℝ (Submission.ChartCurvCont.chrEntryModel C.cov x₀ i j)
          ((extChartAt Work.Space.I4 x₀) q) v)
        (chartAt Work.Space.E4 x₀).source := by
    intro i j
    -- The coordinate model of a Christoffel entry is `C^∞` on the chart target, hence so is its
    -- `fderiv` (the target is open).
    have hcd : ContDiffOn ℝ Work.Final.smoothGrade (fun x : Work.Space.E4 =>
        fderiv ℝ (Submission.ChartCurvCont.chrEntryModel C.cov x₀ i j) x)
        (extChartAt Work.Space.I4 x₀).target :=
      (Submission.Coeff.contDiffOn_chrEntryModel_infty (cov := C.cov) x₀ i j).fderiv_of_isOpen
        (isOpen_extChartAt_target (I := Work.Space.I4) x₀) (le_of_eq (by simp))
    have hmd : ContMDiffOn (modelWithCornersSelf ℝ Work.Space.E4)
        (modelWithCornersSelf ℝ (Work.Space.E4 →L[ℝ] Work.Space.E4)) Work.Final.smoothGrade
        (fun x : Work.Space.E4 =>
          fderiv ℝ (Submission.ChartCurvCont.chrEntryModel C.cov x₀ i j) x)
        (extChartAt Work.Space.I4 x₀).target := hcd.contMDiffOn
    have hinner : ContMDiffOn Work.Space.I4 (modelWithCornersSelf ℝ Work.Space.E4)
        Work.Final.smoothGrade (fun q : M => (extChartAt Work.Space.I4 x₀) q)
        (chartAt Work.Space.E4 x₀).source :=
      contMDiffOn_extChartAt (I := Work.Space.I4) (x := x₀) (n := Work.Final.smoothGrade)
    have hsub : (chartAt Work.Space.E4 x₀).source ⊆
        (fun q : M => (extChartAt Work.Space.I4 x₀) q) ⁻¹' (extChartAt Work.Space.I4 x₀).target :=
      fun q hq => (extChartAt Work.Space.I4 x₀).map_source (by rwa [extChartAt_source])
    have hcomp := hmd.comp hinner hsub
    exact hcomp.clm_apply (contMDiffOn_const (c := v))
  refine ContMDiffOn.congr ?_ (fun q hq => hkey q hq)
  refine contMDiffOn_finsetSum (t := Finset.univ) (f := fun i q => ∑ j,
    (((Module.finBasis ℝ Work.Space.E4).coord i) a *
      ((Module.finBasis ℝ Work.Space.E4).coord j) b) •
      fderiv ℝ (Submission.ChartCurvCont.chrEntryModel C.cov x₀ i j)
        ((extChartAt Work.Space.I4 x₀) q) v) ?_
  intro i _
  refine contMDiffOn_finsetSum (t := Finset.univ) (f := fun j q =>
    (((Module.finBasis ℝ Work.Space.E4).coord i) a *
      ((Module.finBasis ℝ Work.Space.E4).coord j) b) •
      fderiv ℝ (Submission.ChartCurvCont.chrEntryModel C.cov x₀ i j)
        ((extChartAt Work.Space.I4 x₀) q) v) ?_
  intro j _
  exact contMDiffOn_const_smul_E4' _ (hG i j)

end Work.LCSmooth
