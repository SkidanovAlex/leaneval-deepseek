import Mathlib
import Submission.Work.Diff.EXT.CovRicAux
import Submission.Work.Diff.EXT.evolK_bridges
import Submission.Work.Diff.Evol.covRic_eq_sum_covRm_fin
import Submission.Work.Diff.EXT.SmConnVar

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.EXT.ConnCov

/-- **Shi-type bound for `∇Ric` along a Ricci flow.**  If `G` is a Ricci flow on `[0,T)`
(`0 < T`) with `|Rm| ≤ C` up to time `T`, and Shi's a priori estimates
(`Work.Diff.EXT.ShiBounds`) are available, then `∇Ric` is bounded on the *collapsed* time
interval `[T/2, T)` by a constant times the product of the three metric norms.

The route: `(∇_v Ric)(a,b) = ∑_m (∇_v Rm)(e_m, a, e_m, b)` in a `g`-orthonormal frame
(`Work.Diff.Evol.covRic_eq_sum_covRm_fin`), which by Cauchy–Schwarz bounds `∇Ric` by
`n √|∇Rm|²` times the three norms (`Work.Diff.EXT.covRic_bound_of_trace`); Shi's estimate at
`k = 1` gives `|∇Rm|² ≤ C₁` on `[T/2, T)`
(`Work.Diff.EXT.ShiBounds`, and `Work.Diff.EXT.curvNormK_one_eq_dRmNormSq`). -/
theorem covRicBoundShi
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]
    [I.Boundaryless] [T2Space M]
    (hLC : Submission.Diff.LCSmooth I M)
    (G : ℝ → Submission.Diff.SMet I M) (T C : ℝ) (hT : 0 < T)
    (hflow : Submission.Diff.IsRicciFlow G T)
    (hbound : ∀ t ∈ Set.Ico 0 T, Submission.Diff.CurvBound (G t) C)
    (hShi : Work.Diff.EXT.ShiBounds (I := I) (M := M)) :
    ∃ C0 : ℝ, 0 ≤ C0 ∧ ∀ t ∈ Set.Ico (T / 2) T, ∀ x : M, ∀ u v w : TangentSpace I x,
      |Work.Diff.Evol.covRic (G t) x u v w| ≤ C0 * Real.sqrt ((G t).inner x u u)
        * Real.sqrt ((G t).inner x v v) * Real.sqrt ((G t).inner x w w) := by
  classical
  -- ### the contracted second Bianchi identity, in the chosen orthonormal frame
  have hsum : ∀ (g : Submission.Diff.SMet I M) (x : M) (v a b : TangentSpace I x),
      Work.Diff.Evol.covRic g x v a b
        = (Finset.univ : Finset (Fin (Module.finrank ℝ E))).sum
            (fun m => Submission.Diff.covRm g x v (Submission.Diff.onFrame g x m) a
              (Submission.Diff.onFrame g x m) b) :=
    fun g x v a b =>
      Work.Diff.Evol.covRic_eq_sum_covRm_fin (I := I) (M := M) hLC g x
        (Submission.Diff.onFrame g x) (Work.Diff.GE.isONFrame_onFrame g x) v a b
  -- ### `|∇Ric| ≤ C₁ √|∇Rm|² |·| |·| |·|`
  obtain ⟨C₁, hC₁0, hbnd⟩ := Work.Diff.EXT.covRic_bound_of_trace (I := I) (M := M) hLC hsum
  -- ### Shi's estimate at `k = 1` on the collapsed interval `[T/2, T)`
  have hσ : 0 < T / 2 := by linarith
  have hσT : T / 2 < T := by linarith
  obtain ⟨Ck, hCk⟩ := hShi G T C (T / 2) hT hflow hbound hσ hσT 1
  refine ⟨C₁ * Real.sqrt (max Ck 0), mul_nonneg hC₁0 (Real.sqrt_nonneg _), ?_⟩
  intro t ht x u v w
  have hd : Submission.Diff.dRmNormSq (G t) x ≤ max Ck 0 := by
    rw [← Work.Diff.EXT.curvNormK_one_eq_dRmNormSq (I := I) (M := M) (G t) x]
    exact le_trans (hCk t ht x) (le_max_left _ _)
  have hs : Real.sqrt (Submission.Diff.dRmNormSq (G t) x) ≤ Real.sqrt (max Ck 0) :=
    Real.sqrt_le_sqrt hd
  have hu : 0 ≤ Real.sqrt ((G t).inner x u u) := Real.sqrt_nonneg _
  have hv : 0 ≤ Real.sqrt ((G t).inner x v v) := Real.sqrt_nonneg _
  have hw : 0 ≤ Real.sqrt ((G t).inner x w w) := Real.sqrt_nonneg _
  exact le_trans (hbnd (G t) x u v w)
    (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hs hC₁0) hu) hv) hw)

end Work.Diff.EXT.ConnCov
