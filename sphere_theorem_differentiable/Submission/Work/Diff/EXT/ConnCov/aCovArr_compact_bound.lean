import Mathlib
import Submission.Work.Diff.EXT.christoffel_bounds_of_core

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Uniform boundedness of the chart recursion `aCovArr` on a compact set

`Work.Diff.EXT.aCovArr G x₀ t k v i j l` is the chart recursion computing the `k`-th covariant
derivative (with respect to the fixed background connection `∇^{G 0}`) of the lowered connection
difference `g_t(∇^{g_t} − ∇^{g_0})`, read through the chart at `x₀`.  Its level-`k` term is a
function of the chart coordinate `y : E`.

The main theorem `aCovArr_compact_bound` states that, for a fixed `t`, every level of this
recursion is *bounded on every compact `K` contained in the chart target* — with a single constant
`A` valid for all level-`k` multi-indices `v` and all three tensor slots `i j l`.

## Route

This is a corollary of the smoothness of the levels, which is proved (for all levels at once) in
`Work.Diff.EXT.CBound.aCovArr_contDiffAt`: at every point of the (open, because `I` is boundaryless)
chart target `U := (extChartAt I x₀).target`, the function
`y ↦ aCovArr G x₀ t k v i j l y` is `C^∞`.  (The recursion is *inverted* in that proof:
`aCovArr (m+1) = fderiv (aCovArr m)(cBasis ·) − corrFun`, and both terms are smooth as soon as the
level-`m` terms are, with the base level `aComp` a sum of products of smooth chart data.)

Hence each level is `C^∞` on the open set `U`, so it is continuous on `U`, so continuous on the
compact `K ⊆ U`, so bounded there.  The only remaining point is that the bound must be *uniform* in
the level-`k` multi-index `v : Fin k → Fin n` and in `i j l`; since all of these range over finite
types, we take the sum of the finitely many individual bounds.
-/

namespace Work.Diff.EXT.ConnCov

theorem aCovArr_compact_bound
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]
    [I.Boundaryless] [T2Space M]
    (G : ℝ → Submission.Diff.SMet I M) (x₀ : M) (t : ℝ) (k : ℕ) (K : Set E)
    (hK : IsCompact K) (hKt : K ⊆ (extChartAt I x₀).target) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ u ∈ K, ∀ (v : Fin k → Fin (Module.finrank ℝ E))
      (i j l : Fin (Module.finrank ℝ E)),
      |Work.Diff.EXT.aCovArr G x₀ t k v i j l u| ≤ A := by
  classical
  -- every level of the recursion is `C^∞` on the chart target
  have hsmooth : ∀ (m : ℕ) (v : Fin m → Fin (Module.finrank ℝ E))
      (i j l : Fin (Module.finrank ℝ E)),
      ContDiffOn ℝ (⊤ : ℕ∞) (fun y : E => Work.Diff.EXT.aCovArr G x₀ t m v i j l y)
        (extChartAt I x₀).target := by
    intro m v i j l y hy
    exact (Work.Diff.EXT.CBound.aCovArr_contDiffAt (I := I) (M := M) G x₀
      (extChartAt I x₀).target (fun z hz => hz) m v i j l t hy).contDiffWithinAt
  -- hence every level is bounded on `K`, with a bound depending on the multi-index
  have hper : ∀ (v : Fin k → Fin (Module.finrank ℝ E)) (i j l : Fin (Module.finrank ℝ E)),
      ∃ C : ℝ, 0 ≤ C ∧ ∀ y ∈ K, |Work.Diff.EXT.aCovArr G x₀ t k v i j l y| ≤ C := by
    intro v i j l
    have hcont : ContinuousOn (fun y : E => Work.Diff.EXT.aCovArr G x₀ t k v i j l y) K :=
      ((hsmooth k v i j l).continuousOn).mono hKt
    obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hcont
    exact ⟨max C 0, le_max_right _ _,
      fun y hy => le_trans (by simpa only [Real.norm_eq_abs] using hC y hy) (le_max_left _ _)⟩
  choose C hC using hper
  -- the uniform constant: the sum of the finitely many individual bounds
  let F : ((Fin k → Fin (Module.finrank ℝ E)) × Fin (Module.finrank ℝ E) ×
      Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E)) → ℝ :=
    fun p => C p.1 p.2.1 p.2.2.1 p.2.2.2
  have hF0 : ∀ p, 0 ≤ F p := fun p => (hC p.1 p.2.1 p.2.2.1 p.2.2.2).1
  have hFb : ∀ p, F p ≤ ∑ q, F q := fun p =>
    Finset.single_le_sum (fun q _ => hF0 q) (Finset.mem_univ p)
  refine ⟨∑ p, F p, Finset.sum_nonneg (fun p _ => hF0 p), ?_⟩
  intro u hu v i j l
  exact le_trans ((hC v i j l).2 u hu) (hFb ⟨v, i, j, l⟩)

end Work.Diff.EXT.ConnCov
