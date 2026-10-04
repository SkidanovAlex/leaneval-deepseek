import Mathlib
import Submission.Work.Diff.L.Defs
import Submission.Work.Diff.L.Stmt
import Submission.Work.Diff.GE.curvbasic

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

namespace Work.Diff.L

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology
open Bundle ContDiff Set VectorField CovariantDerivative Metric

/-- **Positive scalar curvature.**  If every sectional curvature of the metric `g`, measured with
`g.inner` and the curvature `curv (lcOf g)`, is `> 1`, then the scalar curvature of `g` is `> n(n-1)`.

Route: `scalAt g x = scalAlg (rmFrame g x (onFrame g x))` by definition and
`scalAlg R = ∑ᵢ ∑ⱼ R i j i j`.  The diagonal terms vanish (`rmVec_antisymm` with `i = j`), and for
`i ≠ j` one has `R i j i j = g.inner x (rmVec (lcOf g) x (eᵢ) (eⱼ) (eⱼ)) (eᵢ) = secCurvAt g x (eᵢ) (eⱼ)`
*by definition*, which is `> 1` by applying `hpinch` to the smooth extensions `smoothExt x (e i)`,
`smoothExt x (e j)` (`rmVec_eq_curvVec` + `curvVec_eq`, `Work.Diff.GE.smoothExt_cmdiff/_apply`).
There are `n(n-1)` off-diagonal pairs, each contributing `> 1`. -/
theorem scalAt_ge_of_curv_pos
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I (((⊤ : ℕ∞) : WithTop ℕ∞)) M] [I.Boundaryless] [T2Space M]
    (hdim : 2 ≤ Module.finrank ℝ E)
    (g : Submission.Diff.SMet I M)
    (hcov : CovariantDerivative.ContMDiffCovariantDerivative (Submission.Diff.lcOf g)
      (((⊤ : ℕ∞) : WithTop ℕ∞)))
    (hpinch : ∀ (X Y : Π x : M, TangentSpace I x), Work.Diff.L.SmoothField X →
      Work.Diff.L.SmoothField Y → ∀ x : M,
      g.inner x (X x) (X x) = 1 → g.inner x (Y x) (Y x) = 1 → g.inner x (X x) (Y x) = 0 →
      (1 : ℝ) < g.inner x
        (LeanEval.Geometry.SphereTheorem.curv (Submission.Diff.lcOf g) X Y Y x) (X x)) :
    ∀ x : M, (Module.finrank ℝ E : ℝ) * ((Module.finrank ℝ E : ℝ) - 1)
      < Submission.Diff.scalAt g x := by
  intro x
  letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
  haveI : IsContMDiffRiemannianBundle I (((⊤ : ℕ∞) : WithTop ℕ∞)) E
      (fun x : M ↦ TangentSpace I x) := inferInstance
  -- The scalar curvature is the sum of the frame components `R i j i j`, and each of those is a
  -- sectional curvature.
  have hscal : Submission.Diff.scalAt g x
      = ∑ i : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
          secCurvAt g x (onFrame g x i) (onFrame g x j) := rfl
  -- The diagonal terms vanish by antisymmetry of the curvature in its first two arguments.
  have hdiag : ∀ i : Fin (Module.finrank ℝ E),
      secCurvAt g x (onFrame g x i) (onFrame g x i) = 0 := by
    intro i
    have h := Work.Diff.GE.rmVec_antisymm (lcOf g) hcov x
      (onFrame g x i) (onFrame g x i) (onFrame g x i)
    have h3 : (2 : ℝ) • rmVec (lcOf g) x (onFrame g x i) (onFrame g x i) (onFrame g x i) = 0 := by
      rw [two_smul]
      nth_rewrite 1 [h]
      abel
    have hz : rmVec (lcOf g) x (onFrame g x i) (onFrame g x i) (onFrame g x i) = 0 := by
      rcases smul_eq_zero.mp h3 with h4 | h4
      · norm_num at h4
      · exact h4
    simp [secCurvAt, hz]
  -- Every off-diagonal term is a sectional curvature of an orthonormal pair, hence `> 1`.
  have hsec : ∀ i j : Fin (Module.finrank ℝ E), i ≠ j →
      (1 : ℝ) < secCurvAt g x (onFrame g x i) (onFrame g x j) := by
    intro i j hij
    have he : IsONFrame g x (onFrame g x) := onFrame_isONFrame g x
    have h1 : g.inner x (smoothExt x (onFrame g x i) x) (smoothExt x (onFrame g x i) x) = 1 := by
      rw [Work.Diff.GE.smoothExt_apply]
      simpa using he i i
    have h2 : g.inner x (smoothExt x (onFrame g x j) x) (smoothExt x (onFrame g x j) x) = 1 := by
      rw [Work.Diff.GE.smoothExt_apply]
      simpa using he j j
    have h3 : g.inner x (smoothExt x (onFrame g x i) x) (smoothExt x (onFrame g x j) x) = 0 := by
      rw [Work.Diff.GE.smoothExt_apply, Work.Diff.GE.smoothExt_apply, he i j, ite_eq_right hij]
    have hp := hpinch (smoothExt x (onFrame g x i)) (smoothExt x (onFrame g x j))
      (Work.Diff.GE.smoothExt_cmdiff x (onFrame g x i))
      (Work.Diff.GE.smoothExt_cmdiff x (onFrame g x j)) x h1 h2 h3
    simpa only [secCurvAt, rmVec, Work.Diff.GE.smoothExt_apply] using hp
  rw [hscal]
  -- Split off the diagonal.
  have hsplit : (∑ i : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
        secCurvAt g x (onFrame g x i) (onFrame g x j))
      = ∑ i : Fin (Module.finrank ℝ E), ∑ j ∈ Finset.univ.erase i,
          secCurvAt g x (onFrame g x i) (onFrame g x j) := by
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [← Finset.sum_erase_add (s := (Finset.univ : Finset (Fin (Module.finrank ℝ E))))
      (f := fun j => secCurvAt g x (onFrame g x i) (onFrame g x j)) (Finset.mem_univ i),
      hdiag i, add_zero]
  rw [hsplit]
  -- Each off-diagonal sum has `n - 1` terms, each contributing more than `1`.
  have hlt : (∑ i : Fin (Module.finrank ℝ E), ∑ j ∈ Finset.univ.erase i, (1 : ℝ))
      < ∑ i : Fin (Module.finrank ℝ E), ∑ j ∈ Finset.univ.erase i,
          secCurvAt g x (onFrame g x i) (onFrame g x j) := by
    refine Finset.sum_lt_sum_of_nonempty ?_ ?_
    · rw [← Finset.card_pos, Finset.card_univ, Fintype.card_fin]
      omega
    · intro i _
      refine Finset.sum_lt_sum_of_nonempty ?_ ?_
      · rw [← Finset.card_pos, Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ,
          Fintype.card_fin]
        omega
      · intro j hj
        exact hsec i j (Finset.mem_erase.mp hj).1.symm
  have hconst : (∑ i : Fin (Module.finrank ℝ E), ∑ j ∈ Finset.univ.erase i, (1 : ℝ))
      = (Module.finrank ℝ E : ℝ) * ((Module.finrank ℝ E : ℝ) - 1) := by
    have hinner : ∀ i : Fin (Module.finrank ℝ E),
        (∑ j ∈ Finset.univ.erase i, (1 : ℝ)) = ((Module.finrank ℝ E - 1 : ℕ) : ℝ) := by
      intro i
      rw [Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul, mul_one]
    calc (∑ i : Fin (Module.finrank ℝ E), ∑ j ∈ Finset.univ.erase i, (1 : ℝ))
        = ∑ _i : Fin (Module.finrank ℝ E), ((Module.finrank ℝ E - 1 : ℕ) : ℝ) :=
          Finset.sum_congr rfl (fun i _ => hinner i)
      _ = (Module.finrank ℝ E) • ((Module.finrank ℝ E - 1 : ℕ) : ℝ) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
      _ = (Module.finrank ℝ E : ℝ) * ((Module.finrank ℝ E : ℝ) - 1) := by
          rw [nsmul_eq_mul, Nat.cast_pred (by omega : 0 < Module.finrank ℝ E)]
  calc (Module.finrank ℝ E : ℝ) * ((Module.finrank ℝ E : ℝ) - 1)
      = (∑ i : Fin (Module.finrank ℝ E), ∑ j ∈ Finset.univ.erase i, (1 : ℝ)) := hconst.symm
    _ < ∑ i : Fin (Module.finrank ℝ E), ∑ j ∈ Finset.univ.erase i,
          secCurvAt g x (onFrame g x i) (onFrame g x j) := hlt


end Work.Diff.L
