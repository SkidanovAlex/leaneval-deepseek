import Mathlib
import Submission.Work.Diff.EXT.ConnCov.ChartTowerDefs
import Submission.Work.Diff.EXT.christoffel_bounds_of_core

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Joint smoothness of the chart tower `tower3Arr`

`Work.Diff.EXT.ConnCov.tower3Arr G x₀ t A m v i j l` is the chart recursion of a `(0,3)`-array
`A` with respect to the *fixed* background connection `cGam (G 0)`: level `0` is the base `A`,
and every level is the chart derivative of the previous level in the direction `v 0`, corrected
by the four Christoffel contractions of the coordinate frame.

In this file we prove that if the base `A` is *jointly* smooth in `(t, y)` at `(t, y)` — for
`y` in the chart target `(extChartAt I x₀).target`, which is exactly the set on which the
coefficient functions `y' ↦ cGam (G 0) x₀ (pt x₀ y') k i j` are smooth
(`Work.Diff.EXT.CBound.cGam_contDiffAt_of_target`) — then so is every level of the tower.

The proof is an induction on the level.  The only analytic input is the general fact
`contDiffAt_fderiv_slice_apply` below: the *slice* derivative of a jointly `C^∞` function is
jointly `C^∞`.  This is `ContDiffAt.fderiv` (the uncurried form of the chain rule) followed by the
evaluation at a constant vector, which avoids any use of Clairaut/Schwarz and needs no
differentiability bookkeeping.
-/

set_option maxHeartbeats 800000
set_option linter.unusedSectionVars false

open scoped Manifold ContDiff Bundle Topology BigOperators
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter

namespace Work.Diff.EXT.ConnCov

/-- **The slice derivative of a jointly smooth function is jointly smooth.**  If
`Φ : ℝ × E → ℝ` is `C^∞` at `(t, y)` then, for every fixed `c : E`, the function
`p ↦ fderiv ℝ (fun y' ↦ Φ (p.1, y')) p.2 c` is `C^∞` at `(t, y)`.

This is `ContDiffAt.fderiv` applied to the family `p ↦ (y' ↦ Φ (p.1, y'))` (whose uncurrying is
`(p, y') ↦ Φ (p.1, y')`, a composition of `Φ` with the continuous linear map
`(p, y') ↦ (p.1, y')`), followed by the evaluation of the resulting continuous linear map at the
constant vector `c`. -/
lemma contDiffAt_fderiv_slice_apply
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {Φ : ℝ × E → ℝ} {t : ℝ} {y : E}
    (hΦ : ContDiffAt ℝ (⊤ : ℕ∞) Φ (t, y)) (c : E) :
    ContDiffAt ℝ (⊤ : ℕ∞) (fun p : ℝ × E => fderiv ℝ (fun y' : E => Φ (p.1, y')) p.2 c)
      (t, y) := by
  have hg : ContDiffAt ℝ (⊤ : ℕ∞) (fun q : (ℝ × E) × E => (q.1.1, q.2)) ((t, y), y) := by
    fun_prop
  have hun : ContDiffAt ℝ (⊤ : ℕ∞) (fun q : (ℝ × E) × E => Φ (q.1.1, q.2)) ((t, y), y) :=
    hΦ.comp ((t, y), y) hg
  have hf := hun.fderiv (f := fun (p : ℝ × E) (y' : E) => Φ (p.1, y'))
    (g := fun p : ℝ × E => p.2) contDiffAt_snd (m := (⊤ : ℕ∞)) (n := (⊤ : ℕ∞)) (by simp)
  exact hf.clm_apply contDiffAt_const

theorem tower3Arr_jointSmooth
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]
    [I.Boundaryless] [T2Space M]
    (G : ℝ → Submission.Diff.SMet I M) (x₀ : M) {t : ℝ} {y : E}
    (hy : y ∈ (extChartAt I x₀).target)
    (A : ℝ → E → Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → ℝ)
    (hsm : ∀ (i j l : Fin (Module.finrank ℝ E)),
      ContDiffAt ℝ (⊤ : ℕ∞) (fun p : ℝ × E => A p.1 p.2 i j l) (t, y)) :
    ∀ (m : ℕ) (v : Fin m → Fin (Module.finrank ℝ E)) (i j l : Fin (Module.finrank ℝ E)),
      ContDiffAt ℝ (⊤ : ℕ∞) (fun p : ℝ × E =>
        Work.Diff.EXT.ConnCov.tower3Arr (I := I) (M := M) G x₀ p.1 (A p.1) m v i j l p.2) (t, y) := by
  intro m
  induction m with
  | zero =>
    -- Level `0` is the base array itself.
    intro v i j l
    simpa using hsm i j l
  | succ m ih =>
    intro v i j l
    -- The coefficient functions `p ↦ cGam (G 0) x₀ (pt x₀ p.2) q a (v 0)` are smooth at `(t, y)`.
    have hGam : ∀ (q a : Fin (Module.finrank ℝ E)),
        ContDiffAt ℝ (⊤ : ℕ∞) (fun p : ℝ × E =>
          Work.Diff.GE.cGam (G 0) x₀ (Work.Diff.EXT.pt (I := I) x₀ p.2) q a (v 0)) (t, y) :=
      fun q a => ContDiffAt.comp (f := fun p : ℝ × E => p.2)
        (g := fun y' : E =>
          Work.Diff.GE.cGam (G 0) x₀ (Work.Diff.EXT.pt (I := I) x₀ y') q a (v 0))
        (t, y)
        (Work.Diff.EXT.CBound.cGam_contDiffAt_of_target (I := I) (M := M) (G 0) x₀ hy q a (v 0))
        contDiffAt_snd
    -- The derivative term: the slice derivative of the level-`m` array.
    have hFd : ContDiffAt ℝ (⊤ : ℕ∞) (fun p : ℝ × E =>
        fderiv ℝ (fun y' : E => Work.Diff.EXT.ConnCov.tower3Arr (I := I) (M := M) G x₀ p.1
            (A p.1) m (fun s => v s.succ) i j l y') p.2
          (Work.Diff.GE.cBasis (E := E) (v 0))) (t, y) :=
      contDiffAt_fderiv_slice_apply
        (Φ := fun p : ℝ × E => Work.Diff.EXT.ConnCov.tower3Arr (I := I) (M := M) G x₀ p.1
          (A p.1) m (fun s => v s.succ) i j l p.2)
        (ih (fun s => v s.succ) i j l) _
    -- The four Christoffel-contraction sums.
    have hS1 : ContDiffAt ℝ (⊤ : ℕ∞) (fun p : ℝ × E =>
        ∑ r : Fin m, ∑ q : Fin (Module.finrank ℝ E),
          Work.Diff.GE.cGam (G 0) x₀ (Work.Diff.EXT.pt (I := I) x₀ p.2) q (v r.succ) (v 0)
            * Work.Diff.EXT.ConnCov.tower3Arr (I := I) (M := M) G x₀ p.1 (A p.1) m
                (Function.update (fun s => v s.succ) r q) i j l p.2) (t, y) := by
      refine ContDiffAt.sum (s := Finset.univ) ?_
      intro r _
      refine ContDiffAt.sum (s := Finset.univ) ?_
      intro q _
      exact (hGam q (v r.succ)).mul (ih (Function.update (fun s => v s.succ) r q) i j l)
    have hS2 : ContDiffAt ℝ (⊤ : ℕ∞) (fun p : ℝ × E =>
        ∑ q : Fin (Module.finrank ℝ E),
          Work.Diff.GE.cGam (G 0) x₀ (Work.Diff.EXT.pt (I := I) x₀ p.2) q i (v 0)
            * Work.Diff.EXT.ConnCov.tower3Arr (I := I) (M := M) G x₀ p.1 (A p.1) m
                (fun s => v s.succ) q j l p.2) (t, y) := by
      refine ContDiffAt.sum (s := Finset.univ) ?_
      intro q _
      exact (hGam q i).mul (ih (fun s => v s.succ) q j l)
    have hS3 : ContDiffAt ℝ (⊤ : ℕ∞) (fun p : ℝ × E =>
        ∑ q : Fin (Module.finrank ℝ E),
          Work.Diff.GE.cGam (G 0) x₀ (Work.Diff.EXT.pt (I := I) x₀ p.2) q j (v 0)
            * Work.Diff.EXT.ConnCov.tower3Arr (I := I) (M := M) G x₀ p.1 (A p.1) m
                (fun s => v s.succ) i q l p.2) (t, y) := by
      refine ContDiffAt.sum (s := Finset.univ) ?_
      intro q _
      exact (hGam q j).mul (ih (fun s => v s.succ) i q l)
    have hS4 : ContDiffAt ℝ (⊤ : ℕ∞) (fun p : ℝ × E =>
        ∑ q : Fin (Module.finrank ℝ E),
          Work.Diff.GE.cGam (G 0) x₀ (Work.Diff.EXT.pt (I := I) x₀ p.2) q l (v 0)
            * Work.Diff.EXT.ConnCov.tower3Arr (I := I) (M := M) G x₀ p.1 (A p.1) m
                (fun s => v s.succ) i j q p.2) (t, y) := by
      refine ContDiffAt.sum (s := Finset.univ) ?_
      intro q _
      exact (hGam q l).mul (ih (fun s => v s.succ) i j q)
    -- Assemble the recursion step.
    have hmain : ContDiffAt ℝ (⊤ : ℕ∞) (fun p : ℝ × E =>
        fderiv ℝ (fun y' : E => Work.Diff.EXT.ConnCov.tower3Arr (I := I) (M := M) G x₀ p.1
            (A p.1) m (fun s => v s.succ) i j l y') p.2
          (Work.Diff.GE.cBasis (E := E) (v 0))
        - (∑ r : Fin m, ∑ q : Fin (Module.finrank ℝ E),
          Work.Diff.GE.cGam (G 0) x₀ (Work.Diff.EXT.pt (I := I) x₀ p.2) q (v r.succ) (v 0)
            * Work.Diff.EXT.ConnCov.tower3Arr (I := I) (M := M) G x₀ p.1 (A p.1) m
                (Function.update (fun s => v s.succ) r q) i j l p.2)
        - (∑ q : Fin (Module.finrank ℝ E),
          Work.Diff.GE.cGam (G 0) x₀ (Work.Diff.EXT.pt (I := I) x₀ p.2) q i (v 0)
            * Work.Diff.EXT.ConnCov.tower3Arr (I := I) (M := M) G x₀ p.1 (A p.1) m
                (fun s => v s.succ) q j l p.2)
        - (∑ q : Fin (Module.finrank ℝ E),
          Work.Diff.GE.cGam (G 0) x₀ (Work.Diff.EXT.pt (I := I) x₀ p.2) q j (v 0)
            * Work.Diff.EXT.ConnCov.tower3Arr (I := I) (M := M) G x₀ p.1 (A p.1) m
                (fun s => v s.succ) i q l p.2)
        - (∑ q : Fin (Module.finrank ℝ E),
          Work.Diff.GE.cGam (G 0) x₀ (Work.Diff.EXT.pt (I := I) x₀ p.2) q l (v 0)
            * Work.Diff.EXT.ConnCov.tower3Arr (I := I) (M := M) G x₀ p.1 (A p.1) m
                (fun s => v s.succ) i j q p.2)) (t, y) :=
      (((hFd.sub hS1).sub hS2).sub hS3).sub hS4
    simpa only [tower3Arr_succ] using hmain

end Work.Diff.EXT.ConnCov
