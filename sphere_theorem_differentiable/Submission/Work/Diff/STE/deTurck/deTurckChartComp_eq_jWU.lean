import Mathlib
import Submission.Work.Diff.STE.LieMet
import Submission.Work.Diff.EXT.koszulPair_eq_sKz
import Submission.Work.Diff.EXT.rmChartExpr_eq_jRm_jet
import Submission.Work.Diff.STE.deTurck.koszulPair_eq_jKz

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The chart components of the DeTurck field agree with the jet-level `jWU`

`Work.Diff.STE.DeTurck.deTurckChartComp g gbar x₀ p k` is the `k`-th coordinate of the DeTurck
field `W(g) = tr_g(∇^g - ∇^{gbar})` in the coordinate frame of the chart at `x₀`, i.e. the double
sum `∑_{ab} γ^{ab}(Γ^k_{ab} - Γ̃^k_{ab})` of Gram-matrix inverses against the Christoffel symbols
`chrCoord`.  `Work.Diff.STE.DeTurck.jWU` is the same expression written in the *scalar jet*
vocabulary of `Submission.Work.Diff.EXT.ricJetDefs`, in which all the analytic content of the
DeTurck trick (`pPhi`, `pPhi_decomp`) is phrased.  This file records the dictionary.

At `p = (extChartAt I x₀).symm y` there are two identifications, and after them the target identity
is purely the definitional unfolding of the two double sums:

* `GramInv_eq_jInv_at`: the inverse Gram matrix of the coordinate frame at `p` is the inverse of
  the chart matrix `chartMatFun g x₀ y` (`jInv`).  This is `rfl`: `GramM` and `chartMatFun` are the
  same matrix, written with the two abbreviations `cFrame`/`frameVector`.
* `koszulPair_eq_jKz_at`, `chrCoord_eq_jGamU_at`: the Koszul pairing `koszulPair` of the coordinate
  frame is the scalar `jKz` built from the first jet of the chart matrix, hence the upper
  Christoffel symbols `chrCoord` are `jGamU`.  This is
  `Work.Diff.EXT.koszulPair_eq_sKz` (`koszulPair = sKz ∘ dJet1`) composed with the definitional
  identity `sKz ∘ dJet1 = jKz`.
-/

namespace Work.Diff.STE.deTurck

/-- **The Gram-matrix dictionary**: the inverse Gram matrix of the coordinate frame at the chart
point of `y` is the inverse of the chart matrix `chartMatFun g x₀ y`. -/
theorem GramInv_eq_jInv_at
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]
    (g : Submission.Diff.SMet I M) (x₀ : M) (y : E) :
    Work.Diff.GE.GramInv (fun _ : ℝ => g) (I := I) x₀ 0 ((extChartAt I x₀).symm y)
      = Work.Diff.EXT.jInv (Work.Diff.EXT.chartMatFun (I := I) g x₀ y) := rfl

/-- **The Koszul dictionary**: the geometric Koszul pairing of the coordinate frame at the chart
point of `y` is the scalar expression `jKz` of the first jet of the chart matrix. -/
theorem koszulPair_eq_jKz_at
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]
    [I.Boundaryless] [T2Space M]
    (g : Submission.Diff.SMet I M) (x₀ : M) {y : E} (hy : y ∈ (extChartAt I x₀).target)
    (a b c : Fin (Module.finrank ℝ E)) :
    Work.Diff.GE.koszulPair (fun _ : ℝ => g) (I := I) x₀ a b c 0 ((extChartAt I x₀).symm y)
      = Work.Diff.EXT.jKz (fderiv ℝ (Work.Diff.EXT.chartMatFun (I := I) g x₀) y) a b c := by
  rw [Work.Diff.EXT.koszulPair_eq_sKz (I := I) g x₀ hy a b c]
  rfl

/-- **The Christoffel-symbol dictionary**: the upper Christoffel symbols `Γ^k_{ab}` of the
coordinate frame at the chart point of `y` are `jGamU` applied to the value and the first jet of
the chart matrix. -/
theorem chrCoord_eq_jGamU_at
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]
    [I.Boundaryless] [T2Space M]
    (g : Submission.Diff.SMet I M) (x₀ : M) {y : E} (hy : y ∈ (extChartAt I x₀).target)
    (k a b : Fin (Module.finrank ℝ E)) :
    Work.Diff.GE.chrCoord (fun _ : ℝ => g) (I := I) x₀ k a b 0 ((extChartAt I x₀).symm y)
      = Work.Diff.EXT.jGamU (Work.Diff.EXT.chartMatFun (I := I) g x₀ y)
          (fderiv ℝ (Work.Diff.EXT.chartMatFun (I := I) g x₀) y) k a b := by
  simp only [Work.Diff.GE.chrCoord, Work.Diff.EXT.jGamU, GramInv_eq_jInv_at,
    koszulPair_eq_jKz_at g x₀ hy]

theorem deTurckChartComp_eq_jWU
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]
    [I.Boundaryless] [T2Space M]
    (g gbar : Submission.Diff.SMet I M) (x₀ : M) {y : E} (hy : y ∈ (extChartAt I x₀).target)
    (k : Fin (Module.finrank ℝ E)) :
    Work.Diff.STE.DeTurck.deTurckChartComp g gbar x₀ ((extChartAt I x₀).symm y) k
      = Work.Diff.STE.DeTurck.jWU (Work.Diff.EXT.chartMatFun (I := I) g x₀ y)
          (fderiv ℝ (Work.Diff.EXT.chartMatFun (I := I) g x₀) y)
          (Work.Diff.EXT.chartMatFun (I := I) gbar x₀ y)
          (fderiv ℝ (Work.Diff.EXT.chartMatFun (I := I) gbar x₀) y) k := by
  simp only [Work.Diff.STE.DeTurck.deTurckChartComp, Work.Diff.STE.DeTurck.jWU,
    Work.Diff.GE.chrCoord, Work.Diff.EXT.jGamU, GramInv_eq_jInv_at,
    koszulPair_eq_jKz_at _ x₀ hy]

end Work.Diff.STE.deTurck
