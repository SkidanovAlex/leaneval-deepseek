import Mathlib
import Submission.Work.Diff.EXT.evolX.compLadderDefs
import Submission.Work.Diff.EXT.jetSmoothDefs
import Submission.Work.Diff.EXT.evolX.jetAllPrecomp
import Submission.Work.Diff.EXT.evolX.opJetSmooth_lapOpE

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# `JetSmoothOp` for the pairing of the frame-expanded curvature vector `Zsk`

`Work.Diff.EXT.JetSmoothOp g K S x` (`Submission/Work/Diff/EXT/jetSmoothDefs.lean`) is the
regularity predicate of the jet calculus: for every jet order `l` and every tuple `F` of smooth
fields, the function `y ↦ jetAll g l K S F y` is mdifferentiable near `x`.  It is exactly the
hypothesis under which `jetAll` is *linear* in the operator
(`Work.Diff.EXT.jetAll_sub_of_JetSmoothOp`), hence the hypothesis needed by the composition ladder
(`Work.Diff.EXT.evolX.substOp_jets_le_v2`) to split the tower `ckt g k`, with one slot filled by the
value of a vector-valued operator, into the pairing of that operator with the curvature vector
`Zsk g W k s`.

Here we discharge it for the operator

`pairVec g (Zsk g W k s)` (arity `k + 4`),

the pairing of the frame-expanded curvature vector `Zsk` (`compLadderDefs.lean`).

## The proof

The *value* of the operator on a tuple `F` of smooth fields is, by the definition of `Zsk` and the
`ℝ`-bilinearity of the metric pairing, the finite sum

`y ↦ ∑ m, (ckt g k (update (F ∘ σ) s (W m)) y) * g.inner y (W m y) (F (last) y)`,

a sum of *products* of `C^∞` functions:

* `y ↦ ckt g k (…) y` is `C^∞` because the tower is `C^∞` on tuples of smooth fields
  (`Work.Diff.EXT.tensProp_all`), the tuple here being given by the slot relabelling
  `σ i = (skipMap k s i).castSucc` of the smooth tuple `F` and the smooth frame field `W`;
* `y ↦ g.inner y (W m y) (F (last) y)` is `C^∞` because the metric pairing of two smooth sections
  is (`Work.Diff.EXT.evolX.pairing_cmdiff`).

Consequently all the jets of the operator are `C^∞` on tuples of smooth fields
(`Work.Diff.EXT.evolX.jetAll_contMDiff_of_base`), which is `JetSmoothOp` up to replacing `C^∞` by
`MDifferentiableAt`.

Nothing here uses that `W` is an *orthonormal* frame (`hON`) or the hypothesis `hTs`: the identity
`⟪Zsk …, D⟫ = ckt g k (… D …)`, which is what makes `pairVec g (Zsk …)` the tower up to a slot
relabelling, is used elsewhere (`Work.Diff.EXT.evolX.ZskPair`,
`Work.Diff.EXT.evolX.pairVecZskStrongAt`); for smoothness the raw frame sum suffices.
-/

set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology BigOperators
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter

namespace Work.Diff.EXT.evolX

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M] [T2Space M]

/-- **The metric pairing of two smooth sections is smooth**: `y ↦ g.inner y (X y) (Y y)` is `C^∞`
for `X`, `Y` of class `C^∞`.  (Global form of `Work.EXT.pairing_contMDiffAt`.) -/
theorem pairing_cmdiff (g : Submission.Diff.SMet I M)
    {X Y : Work.Diff.EXT.TField (I := I) (M := M)}
    (hX : Work.Diff.EXT.SmoothF (I := I) (M := M) X)
    (hY : Work.Diff.EXT.SmoothF (I := I) (M := M) Y) :
    CMDiff ∞ (fun y : M => g.inner y (X y) (Y y)) := by
  letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
  haveI : IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x) := inferInstance
  exact ContMDiff.inner_bundle (F := E) (E := fun x : M ↦ TangentSpace I x) (b := (id : M → M))
    (v := X) (w := Y) hX hY

/-- **The value of `pairVec g (Zsk g W k s)` is a sum of products in smooth fields.**  For a tuple
`F` of smooth fields, the pairing of the frame-expanded curvature vector with the last slot is the
finite sum `∑ m, (ckt g k (…)) · ⟪W m, F last⟫`. -/
theorem pairVec_Zsk_eq_sum (g : Submission.Diff.SMet I M)
    (W : Fin (Module.finrank ℝ E) → Work.Diff.EXT.TField (I := I) (M := M)) {k : ℕ}
    (s : Fin (k + 4)) (F : Fin ((k + 3) + 1) → Work.Diff.EXT.TField (I := I) (M := M)) :
    pairVec (I := I) (M := M) g (Zsk (I := I) (M := M) g W k s) F
      = fun y : M => ∑ m : Fin (Module.finrank ℝ E),
          (Work.Diff.EXT.ckt (I := I) (M := M) g k
            (Function.update (fun i : Fin (k + 4) => F (skipMap k s i).castSucc) s (W m)) y)
          * (g.inner y (W m y) (F (Fin.last (k + 3)) y)) := by
  funext y
  simp only [pairVec, Zsk, map_sum, map_smul, sum_apply, smul_apply, smul_eq_mul]

/-- The `m`-th summand of the value of `pairVec g (Zsk g W k s)` is `C^∞` in the base point, on
tuples of smooth fields. -/
theorem contMDiff_pairVec_Zsk_term (hLC : Submission.Diff.LCSmooth I M)
    (g : Submission.Diff.SMet I M)
    (W : Fin (Module.finrank ℝ E) → Work.Diff.EXT.TField (I := I) (M := M))
    (hW : ∀ i, Work.Diff.EXT.SmoothF (I := I) (M := M) (W i)) {k : ℕ} (s : Fin (k + 4))
    (F : Fin ((k + 3) + 1) → Work.Diff.EXT.TField (I := I) (M := M))
    (hF : ∀ i, Work.Diff.EXT.SmoothF (I := I) (M := M) (F i))
    (m : Fin (Module.finrank ℝ E)) :
    CMDiff ∞ (fun y : M =>
      (Work.Diff.EXT.ckt (I := I) (M := M) g k
        (Function.update (fun i : Fin (k + 4) => F (skipMap k s i).castSucc) s (W m)) y)
      * (g.inner y (W m y) (F (Fin.last (k + 3)) y))) := by
  have hΨ : ∀ i : Fin (k + 4), Work.Diff.EXT.SmoothF (I := I) (M := M)
      ((fun i : Fin (k + 4) => F (skipMap k s i).castSucc) i) :=
    fun i => hF _
  have hA : CMDiff ∞ (fun y : M => Work.Diff.EXT.ckt (I := I) (M := M) g k
      (Function.update (fun i : Fin (k + 4) => F (skipMap k s i).castSucc) s (W m)) y) :=
    (Work.Diff.EXT.tensProp_all (I := I) (M := M) hLC g k _
      (Work.Diff.EXT.smoothF_update' (I := I) (M := M) hΨ s (hW m))).1
  have hB : CMDiff ∞ (fun y : M => g.inner y (W m y) (F (Fin.last (k + 3)) y)) :=
    pairing_cmdiff (I := I) (M := M) g (hW m) (hF (Fin.last (k + 3)))
  exact hA.mul hB

theorem pairVecZskJetSmooth
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M] [T2Space M]
    (hLC : Submission.Diff.LCSmooth I M) (g : Submission.Diff.SMet I M) (x : M)
    (W : Fin (Module.finrank ℝ E) → Work.Diff.EXT.TField (I := I) (M := M))
    (hW : ∀ i, Work.Diff.EXT.SmoothF (I := I) (M := M) (W i))
    (hON : Filter.Eventually (fun y : M =>
        Submission.Diff.IsONFrame g y (fun i => W i y)) (nhds x))
    {k : ℕ} (s : Fin (k + 4))
    (hTs : Work.Diff.EXT.JetSmoothOp (I := I) (M := M) g (k + 4)
      (Work.Diff.EXT.ckt (I := I) (M := M) g k) x) :
    Work.Diff.EXT.JetSmoothOp (I := I) (M := M) g (k + 4)
      (Work.Diff.EXT.evolX.pairVec (I := I) (M := M) g
        (Work.Diff.EXT.evolX.Zsk (I := I) (M := M) g W k s)) x := by
  have hbase : ∀ F : Fin ((k + 3) + 1) → Work.Diff.EXT.TField (I := I) (M := M),
      (∀ i, Work.Diff.EXT.SmoothF (I := I) (M := M) (F i)) →
      CMDiff ∞ (Work.Diff.EXT.evolX.pairVec (I := I) (M := M) g
        (Work.Diff.EXT.evolX.Zsk (I := I) (M := M) g W k s) F) := by
    intro F hF
    rw [pairVec_Zsk_eq_sum (I := I) (M := M) g W s F]
    refine ContMDiff.sum (t := Finset.univ)
      (f := fun m : Fin (Module.finrank ℝ E) => fun y : M =>
        (Work.Diff.EXT.ckt (I := I) (M := M) g k
          (Function.update (fun i : Fin (k + 4) => F (skipMap k s i).castSucc) s (W m)) y)
        * (g.inner y (W m y) (F (Fin.last (k + 3)) y))) ?_
    intro m _
    exact contMDiff_pairVec_Zsk_term (I := I) (M := M) hLC g W hW s F hF m
  have hj := Work.Diff.EXT.evolX.jetAll_contMDiff_of_base (I := I) (M := M) hLC g
    (S := Work.Diff.EXT.evolX.pairVec (I := I) (M := M) g
      (Work.Diff.EXT.evolX.Zsk (I := I) (M := M) g W k s)) hbase
  filter_upwards with y
  intro l F hF
  exact (hj l F hF).contMDiffAt.mdifferentiableAt (by simp)

end Work.Diff.EXT.evolX
