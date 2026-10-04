import Mathlib
import Submission.Work.Diff.EXT.ConnCov.Kit
import Submission.Work.Diff.EXT.ATower.Defs
import Submission.Work.Diff.EXT.ATower.tower_value_defs
import Submission.Work.Diff.EXT.ATower.tower_value_dep
import Submission.Work.Diff.EXT.ATower.tvd_germ_step
import Submission.Work.Diff.EXT.covK_germ

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Germ-locality of the tower of `∂_t aOf`

The target `Work.Diff.EXT.ConnCov.tower_dAOfBase_congr_germ` says that the value at `x` of the
`k`-th `∇^{G 0}`-covariant derivative of the base `dAOfBase G t` (the time derivative of the
lowered connection difference, evaluated at time `t`) depends only on the *germs* of the `k + 3`
argument fields at `x`.

This is the level-`0` input of the general germ-locality statement for the packed tower
`Work.Diff.EXT.ATower.tvdP`:

* `aOf_germ_congr`: `aOf G s A B C x` depends only on the germs of `A`, `B`, `C` at `x`
  (for the field `B` this is `Work.Diff.EXT.lcOf_congr_germ`, for `A` and `C` only the *values*
  at `x` matter, and an eventual equality gives equality of the values);
* `dAOfBase_germ`: the base `dAOfBase G t` itself is germ-determined;
* `tvdGermT_all_of_germ`: the induction on `k` along the packed recursion, using the
  (already proved) induction step `Work.Diff.EXT.ATower.tvd_germ_step`; the `k = 0` case is
  exactly the germ-determinacy of the base.

The induction needs *no* smoothness hypothesis: `mvfderiv` and `lcOf` are both germ-determined.
-/

set_option linter.unusedSectionVars false

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology BigOperators
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter

namespace Work.Diff.EXT.ConnCov

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M] [T2Space M]

/-- **Germ-locality of the lowered connection difference.**  `aOf G s A B C x` depends only on the
germs of the three fields at `x`: the field `B` enters through `lcOf` (germ-determined by
`Work.Diff.EXT.lcOf_congr_germ`), while `A` and `C` enter only through their *values* at `x`. -/
theorem aOf_germ_congr (G : ℝ → SMet I M) (s : ℝ) {A A' B B' C C' : Π y : M, TangentSpace I y}
    {x : M} (hA : A =ᶠ[𝓝 x] A') (hB : B =ᶠ[𝓝 x] B') (hC : C =ᶠ[𝓝 x] C') :
    aOf G s A B C x = aOf G s A' B' C' x := by
  simp only [aOf]
  rw [Work.Diff.EXT.lcOf_congr_germ (G s) hB, Work.Diff.EXT.lcOf_congr_germ (G 0) hB,
    hA.eq_of_nhds, hC.eq_of_nhds]

/-- **Germ-locality of the base `dAOfBase G t`**: the time derivative at `t` of
`aOf G · A B C x` depends only on the germs of `A`, `B`, `C` at `x`. -/
theorem dAOfBase_germ (G : ℝ → SMet I M) (t : ℝ) :
    ∀ (b0 : Fin 0 → (Π y : M, TangentSpace I y)) (A A' B B' C C' : Π y : M, TangentSpace I y)
      (x : M), A =ᶠ[𝓝 x] A' → B =ᶠ[𝓝 x] B' → C =ᶠ[𝓝 x] C' →
      dAOfBase G t b0 A B C x = dAOfBase G t b0 A' B' C' x := by
  intro b0 A A' B B' C C' x hA hB hC
  simp only [dAOfBase]
  rw [show (fun s : ℝ => aOf G s A B C x) = (fun s : ℝ => aOf G s A' B' C' x) from
    funext (fun s => aOf_germ_congr G s hA hB hC)]

/-- **Germ-locality of the packed tower `tvdP` from germ-locality of the base.**  The induction is
the packed recursion; the step is the already-proved `Work.Diff.EXT.ATower.tvd_germ_step`. -/
theorem tvdGermT_all_of_germ (g : SMet I M) (base : Work.Diff.EXT.ATower.Op3 (I := I) (M := M) 0)
    (hbase : ∀ (b0 : Fin 0 → (Π y : M, TangentSpace I y))
      (A A' B B' C C' : Π y : M, TangentSpace I y) (x : M),
      A =ᶠ[𝓝 x] A' → B =ᶠ[𝓝 x] B' → C =ᶠ[𝓝 x] C' →
      base b0 A B C x = base b0 A' B' C' x) :
    ∀ k, Work.Diff.EXT.ATower.tvdGermT (I := I) (M := M) g base k := by
  intro k
  induction k with
  | zero =>
      intro F F' x h
      simp only [Work.Diff.EXT.ATower.tvdP]
      exact hbase _ _ _ _ _ _ _ _ (h _) (h _) (h _)
  | succ k ih => exact Work.Diff.EXT.ATower.tvd_germ_step (I := I) (M := M) g base k ih

theorem tower_dAOfBase_congr_germ
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]
    [I.Boundaryless] [T2Space M]
    (G : ℝ → Submission.Diff.SMet I M) (t : ℝ) (k : ℕ)
    (v v' : Fin k → (Π y : M, TangentSpace I y))
    (A A' B B' C C' : Π y : M, TangentSpace I y) (x : M)
    (hvv : ∀ j, Filter.EventuallyEq (nhds x) (v j) (v' j))
    (hA : Filter.EventuallyEq (nhds x) A A') (hB : Filter.EventuallyEq (nhds x) B B')
    (hC : Filter.EventuallyEq (nhds x) C C') :
    Work.Diff.EXT.ATower.tower (Submission.Diff.lcOf (G 0))
        (Work.Diff.EXT.ConnCov.dAOfBase G t) k v A B C x
      = Work.Diff.EXT.ATower.tower (Submission.Diff.lcOf (G 0))
        (Work.Diff.EXT.ConnCov.dAOfBase G t) k v' A' B' C' x := by
  have hger : Work.Diff.EXT.ATower.tvdGermT (I := I) (M := M) (G 0) (dAOfBase G t) k :=
    tvdGermT_all_of_germ (G 0) (dAOfBase G t) (dAOfBase_germ G t) k
  -- the packed tuples agree in the germ at `x`
  have hpack : ∀ j : Fin (k + 3),
      Work.Diff.EXT.ATower.tvdPack v A B C j =ᶠ[𝓝 x]
        Work.Diff.EXT.ATower.tvdPack v' A' B' C' j := by
    intro j
    refine Fin.addCases (motive := fun j => Work.Diff.EXT.ATower.tvdPack v A B C j =ᶠ[𝓝 x]
      Work.Diff.EXT.ATower.tvdPack v' A' B' C' j) ?_ ?_ j
    · intro i
      simp only [Work.Diff.EXT.ATower.tvdPack_castAdd]
      exact hvv i
    · intro j'
      simp only [Work.Diff.EXT.ATower.tvdPack_natAdd]
      fin_cases j' <;> assumption
  have hgerm := hger (Work.Diff.EXT.ATower.tvdPack v A B C)
    (Work.Diff.EXT.ATower.tvdPack v' A' B' C') x hpack
  -- convert the packed statement back into `tower`
  rw [← Work.Diff.EXT.ATower.tvdTp_pack (G 0) (dAOfBase G t) v A B C,
    ← Work.Diff.EXT.ATower.tvdTp_pack (G 0) (dAOfBase G t) v' A' B' C',
    ← Work.Diff.EXT.ATower.tvdP_eq_tvdTp (G 0) (dAOfBase G t) k
        (Work.Diff.EXT.ATower.tvdPack v A B C),
    ← Work.Diff.EXT.ATower.tvdP_eq_tvdTp (G 0) (dAOfBase G t) k
        (Work.Diff.EXT.ATower.tvdPack v' A' B' C')]
  exact hgerm

end Work.Diff.EXT.ConnCov
