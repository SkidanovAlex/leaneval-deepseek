import Mathlib
import Submission.Work.Diff.EXT.ConnCov.aComp_jets_of_chartMat_jets
import Submission.Work.Diff.EXT.koszulPair_eq_sKz
import Submission.Work.Diff.EXT.chartMat_fderiv_basis

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.EXT.ConnCov

/-!
The explicit formula for the first chart derivative of the chart matrix of a metric family `G` in
terms of the chart array `aComp` of the *lowered* connection difference `g_t(∇^{g_t} − ∇^{g_0})`
and of the *fixed* Christoffel symbols of `G 0`.

Route.  `Work.Diff.EXT.sKz (Work.Diff.EXT.dJet1 (G t) x₀ y) a b c` is the Koszul combination
`½(∂_a g_{bc} + ∂_b g_{ac} − ∂_c g_{ab})` of the first coordinate partials of the chart matrix
(`Work.Diff.EXT.kz_fderiv_chartMatFun_apply`) and
`Work.Diff.EXT.ConnCov.aComp_eq_sKz_sub` gives
`sKz a b c = aComp a b c + Σ_p (chartMat)_{cp} (cGam (G 0))^p_{ab}`.
The elementary identity `∂_m g_{ij} = sKz m i j + sKz m j i` (Koszul algebra, using the symmetry of
the derivative matrix `Work.Diff.EXT.kz_chartMatFun_swap`) then gives the stated formula.
-/

theorem fderiv_chartMat_eq_aComp_coef
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]
    [I.Boundaryless] [T2Space M]
    (G : ℝ → Submission.Diff.SMet I M) (x₀ : M) (t : ℝ) {y : E}
    (hy : y ∈ (extChartAt I x₀).target) (i j m : Fin (Module.finrank ℝ E)) :
    fderiv ℝ (fun y' : E => Work.Diff.EXT.chartMat (I := I) (M := M) G x₀ t y' i j) y
        ((Module.finBasis ℝ E) m)
      = (Work.Diff.EXT.aComp G x₀ t y m i j + Work.Diff.EXT.aComp G x₀ t y m j i)
        + ∑ p : Fin (Module.finrank ℝ E),
            (Work.Diff.GE.GramM G x₀ t (Work.Diff.EXT.pt (I := I) x₀ y) i p
                * Work.Diff.GE.cGam (G 0) x₀ (Work.Diff.EXT.pt (I := I) x₀ y) p m j
              + Work.Diff.GE.GramM G x₀ t (Work.Diff.EXT.pt (I := I) x₀ y) j p
                * Work.Diff.GE.cGam (G 0) x₀ (Work.Diff.EXT.pt (I := I) x₀ y) p m i) := by
  classical
  -- The chart matrix and the Gram matrix of the coordinate frame at the chart centre agree.
  have hcm : ∀ (l p : Fin (Module.finrank ℝ E)),
      Work.Diff.EXT.chartMat (I := I) (M := M) G x₀ t y l p
        = Work.Diff.GE.GramM G x₀ t (Work.Diff.EXT.pt (I := I) x₀ y) l p := fun l p => rfl
  -- The left-hand side is the `(i,j)` coefficient of the Fréchet derivative of the chart matrix.
  have hstep : fderiv ℝ (fun y' : E => Work.Diff.EXT.chartMat (I := I) (M := M) G x₀ t y' i j) y
        ((Module.finBasis ℝ E) m)
      = (fderiv ℝ (Work.Diff.EXT.chartMatFun (I := I) (G t) x₀) y
          ((Module.finBasis ℝ E) m)) i j :=
    (Work.Diff.EXT.kz_fderiv_chartMatFun_apply (I := I) (M := M) (G t) x₀ hy m i j).symm
  -- Koszul algebra: `∂_m g_{ij} = sKz m i j + sKz m j i`, using the symmetry of the derivative
  -- matrix in its two matrix indices.
  have hLid : (fderiv ℝ (Work.Diff.EXT.chartMatFun (I := I) (G t) x₀) y
        ((Module.finBasis ℝ E) m)) i j
      = Work.Diff.EXT.sKz (Work.Diff.EXT.dJet1 (G t) x₀ y) m i j
        + Work.Diff.EXT.sKz (Work.Diff.EXT.dJet1 (G t) x₀ y) m j i := by
    have h1 := Work.Diff.EXT.kz_chartMatFun_swap (I := I) (M := M) (G t) x₀ hy i m j
    have h2 := Work.Diff.EXT.kz_chartMatFun_swap (I := I) (M := M) (G t) x₀ hy j m i
    have h3 := Work.Diff.EXT.kz_chartMatFun_swap (I := I) (M := M) (G t) x₀ hy m j i
    simp only [Work.Diff.EXT.sKz, Work.Diff.EXT.dJet1]
    rw [h1, h2, h3]
    ring
  -- Each Koszul combination is the corresponding `aComp` plus the lowering of the *fixed*
  -- Christoffel symbol of `G 0`.
  have hsKz1 : Work.Diff.EXT.sKz (Work.Diff.EXT.dJet1 (G t) x₀ y) m i j
      = Work.Diff.EXT.aComp G x₀ t y m i j
        + ∑ p : Fin (Module.finrank ℝ E),
            Work.Diff.GE.GramM G x₀ t (Work.Diff.EXT.pt (I := I) x₀ y) j p
              * Work.Diff.GE.cGam (G 0) x₀ (Work.Diff.EXT.pt (I := I) x₀ y) p m i := by
    have h := aComp_eq_sKz_sub (I := I) (M := M) G x₀ t hy m i j
    have hsum : (∑ p : Fin (Module.finrank ℝ E),
          Work.Diff.EXT.chartMat (I := I) (M := M) G x₀ t y j p
            * Work.Diff.GE.cGam (G 0) x₀ (Work.Diff.EXT.pt (I := I) x₀ y) p m i)
        = (∑ p : Fin (Module.finrank ℝ E),
            Work.Diff.GE.GramM G x₀ t (Work.Diff.EXT.pt (I := I) x₀ y) j p
              * Work.Diff.GE.cGam (G 0) x₀ (Work.Diff.EXT.pt (I := I) x₀ y) p m i) :=
      Finset.sum_congr rfl (fun p _ => by rw [hcm])
    rw [h, hsum]
    ring
  have hsKz2 : Work.Diff.EXT.sKz (Work.Diff.EXT.dJet1 (G t) x₀ y) m j i
      = Work.Diff.EXT.aComp G x₀ t y m j i
        + ∑ p : Fin (Module.finrank ℝ E),
            Work.Diff.GE.GramM G x₀ t (Work.Diff.EXT.pt (I := I) x₀ y) i p
              * Work.Diff.GE.cGam (G 0) x₀ (Work.Diff.EXT.pt (I := I) x₀ y) p m j := by
    have h := aComp_eq_sKz_sub (I := I) (M := M) G x₀ t hy m j i
    have hsum : (∑ p : Fin (Module.finrank ℝ E),
          Work.Diff.EXT.chartMat (I := I) (M := M) G x₀ t y i p
            * Work.Diff.GE.cGam (G 0) x₀ (Work.Diff.EXT.pt (I := I) x₀ y) p m j)
        = (∑ p : Fin (Module.finrank ℝ E),
            Work.Diff.GE.GramM G x₀ t (Work.Diff.EXT.pt (I := I) x₀ y) i p
              * Work.Diff.GE.cGam (G 0) x₀ (Work.Diff.EXT.pt (I := I) x₀ y) p m j) :=
      Finset.sum_congr rfl (fun p _ => by rw [hcm])
    rw [h, hsum]
    ring
  rw [hstep, hLid, hsKz1, hsKz2, Finset.sum_add_distrib]
  ring

end Work.Diff.EXT.ConnCov
