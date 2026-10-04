import Mathlib
import Submission.Diff.Evol
import Submission.Work.Diff.GE.NablaRm
import Submission.Work.Diff.GE.ReactionDefs
import Submission.Work.Diff.GE.frame_deps

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Vocabulary for the fixed-vector evolution of `∇Rm` (definitions)
-/

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology BigOperators
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter

namespace Work.Diff.GE

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ((⊤ : ENat) : WithTop ENat) M]
  [I.Boundaryless] [T2Space M] [CompactSpace M]

/-- The variation of the Levi-Civita connection in the direction `v`, as a function of time:
`s ↦ ∇^{G s}_{(smoothExt x v)} (smoothExt x a) (x)`. -/
noncomputable def connVar (G : ℝ → SMet I M) (x : M) (a : TangentSpace I x)
    (v : TangentSpace I x) (s : ℝ) : E :=
  ((lcOf (G s) (smoothExt x a) x v : TangentSpace I x) : E)

/-- The predicted time derivative of the fixed-vector component `s ↦ covRm (G s) x v a b c d`. -/
noncomputable def covRmTimeDeriv
    (F : Curv4 (Module.finrank ℝ E) → Curv4 (Module.finrank ℝ E))
    (G : ℝ → SMet I M) (t : ℝ) (x : M) (v a b c d : TangentSpace I x) : ℝ :=
  Work.Diff.GE.covLapRmAt (G t) x v a b c d
    + Work.Diff.GE.covReactionFormAt F (G t) x v a b c d
    - rmP (G t) x (((deriv (connVar G x a v) t : E) : TangentSpace I x)) b c d
    - rmP (G t) x a (((deriv (connVar G x b v) t : E) : TangentSpace I x)) c d
    - rmP (G t) x a b (((deriv (connVar G x c v) t : E) : TangentSpace I x)) d
    - rmP (G t) x a b c (((deriv (connVar G x d v) t : E) : TangentSpace I x))

/-- As `covRmTimeDeriv`, but with one-sided derivatives, so that it also makes sense at `t = 0`. -/
noncomputable def covRmTimeDerivWithin
    (F : Curv4 (Module.finrank ℝ E) → Curv4 (Module.finrank ℝ E))
    (G : ℝ → SMet I M) (T t : ℝ) (x : M) (v a b c d : TangentSpace I x) : ℝ :=
  Work.Diff.GE.covLapRmAt (G t) x v a b c d
    + Work.Diff.GE.covReactionFormAt F (G t) x v a b c d
    - rmP (G t) x (((derivWithin (connVar G x a v) (Set.Ico 0 T) t : E) : TangentSpace I x)) b c d
    - rmP (G t) x a (((derivWithin (connVar G x b v) (Set.Ico 0 T) t : E)
        : TangentSpace I x)) c d
    - rmP (G t) x a b (((derivWithin (connVar G x c v) (Set.Ico 0 T) t : E)
        : TangentSpace I x)) d
    - rmP (G t) x a b c (((derivWithin (connVar G x d v) (Set.Ico 0 T) t : E)
        : TangentSpace I x))

/-- At a point of the interior of `Ico 0 T` the two definitions agree. -/
theorem covRmTimeDerivWithin_eq (F) {G : ℝ → SMet I M} {T t : ℝ} (ht : t ∈ Set.Ioo 0 T)
    (x : M) (v a b c d : TangentSpace I x) :
    covRmTimeDerivWithin F G T t x v a b c d = covRmTimeDeriv F G t x v a b c d := by
  have hmem : Set.Ico (0:ℝ) T ∈ 𝓝 t :=
    Filter.mem_of_superset (IsOpen.mem_nhds isOpen_Ioo ht) Set.Ioo_subset_Ico_self
  have h1 : derivWithin (connVar G x a v) (Set.Ico 0 T) t = deriv (connVar G x a v) t :=
    derivWithin_of_mem_nhds hmem
  have h2 : derivWithin (connVar G x b v) (Set.Ico 0 T) t = deriv (connVar G x b v) t :=
    derivWithin_of_mem_nhds hmem
  have h3 : derivWithin (connVar G x c v) (Set.Ico 0 T) t = deriv (connVar G x c v) t :=
    derivWithin_of_mem_nhds hmem
  have h4 : derivWithin (connVar G x d v) (Set.Ico 0 T) t = deriv (connVar G x d v) t :=
    derivWithin_of_mem_nhds hmem
  simp only [covRmTimeDerivWithin, covRmTimeDeriv, h1, h2, h3, h4]

/-- `rmP` on a `4`-tuple of vectors. -/
noncomputable def rmP4 (g : SMet I M) (x : M) (p : Fin 4 → TangentSpace I x) : ℝ :=
  rmP g x (p 0) (p 1) (p 2) (p 3)

/-- `rmP4` is additive in one slot. -/
theorem rmP4_update_add (hLC : LCSmooth I M) (g : SMet I M) (x : M)
    (p : Fin 4 → TangentSpace I x) (j : Fin 4) (u v : TangentSpace I x) :
    rmP4 g x (Function.update p j (u + v))
      = rmP4 g x (Function.update p j u) + rmP4 g x (Function.update p j v) := by
  fin_cases j <;>
    simp only [rmP4, Function.update_apply, Fin.isValue, Fin.reduceEq, ↓reduceIte,
      Fin.mk_one, Fin.reduceFinMk, rmP_add_fst g hLC, rmP_add_snd g hLC, rmP_add_thd g hLC,
      rmP_add_fth g hLC]

/-- `rmP4` is homogeneous in one slot. -/
theorem rmP4_update_smul (hLC : LCSmooth I M) (g : SMet I M) (x : M)
    (p : Fin 4 → TangentSpace I x) (j : Fin 4) (c : ℝ) (u : TangentSpace I x) :
    rmP4 g x (Function.update p j (c • u)) = c * rmP4 g x (Function.update p j u) := by
  fin_cases j <;>
    simp only [rmP4, Function.update_apply, Fin.isValue, Fin.reduceEq, ↓reduceIte,
      Fin.mk_one, Fin.reduceFinMk, rmP_smul_fst g hLC, rmP_smul_snd g hLC, rmP_smul_thd g hLC,
      rmP_smul_fth g hLC]

end Work.Diff.GE
