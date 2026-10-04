import Mathlib
import Submission.Work.Diff.Evol.Deps

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.Evol

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology
open Bundle ContDiff Set VectorField CovariantDerivative Metric

/-- The `Classical.epsilon`-chosen extension `smoothExt x u` is a smooth field.  (Local copy, so
that this file does not have to import either of the two mutually incompatible `Work.Diff.GE`
chains.) -/
theorem smoothExt_cmdiff_evol
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
    (x : M) (u : TangentSpace I x) : CMDiff ∞ (T% (smoothExt x u)) :=
  (Classical.epsilon_spec (Commons.Geometry.Manifold.VectorField.exists_contMDiff_section_apply_eq
    (I := I) (M := M) u)).1

/-- Along a Ricci flow, `dtMet G t = −2 Ric(G t)`. -/
theorem dtMet_eq_neg_two_ricAt
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [I.Boundaryless] [T2Space M]
    (G : ℝ → SMet I M) (T : ℝ) (hflow : IsRicciFlow G T) {t : ℝ} (ht : t ∈ Ioo 0 T)
    (x : M) (u v : TangentSpace I x) :
    dtMet G t x u v = -2 * ricAt (lcOf (G t)) x u v := by
  have hmem : t ∈ Ico (0 : ℝ) T := ⟨le_of_lt ht.1, ht.2⟩
  have hnb : Ico (0 : ℝ) T ∈ 𝓝 t :=
    Filter.mem_of_superset (isOpen_Ioo.mem_nhds ht) Ioo_subset_Ico_self
  rw [dtMet, ((hflow.2 t hmem x u v).hasDerivAt hnb).deriv]

theorem rmP_fixed_deriv
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [I.Boundaryless] [T2Space M]
    (hLC : LCSmooth I M) (hLV : LCVariation I M) (hCV : CurvVariation I M)
    (G : ℝ → SMet I M) (T : ℝ) (hflow : IsRicciFlow G T) {t : ℝ} (ht : t ∈ Ioo 0 T)
    (x : M) (a b c d : TangentSpace I x) :
    HasDerivAt (fun s ↦ rmP (G s) x a b c d)
      (-2 * ricAt (lcOf (G t)) x (rmVec (lcOf (G t)) x a b d) c
        + (G t).inner x (covDLC G t (smoothExt x a) (smoothExt x b) (smoothExt x d) x
            - covDLC G t (smoothExt x b) (smoothExt x a) (smoothExt x d) x) c) t := by
  -- joint smoothness on the open interval
  have hJs : JointSmooth G (Ioo 0 T) :=
    hflow.1.mono (Set.prod_mono Ioo_subset_Ico_self (Subset.refl _))
  have hJopen : IsOpen (Ioo 0 T) := isOpen_Ioo
  -- the fixed-vector derivative of `s ↦ R^{G s}(a,b)d`, from the first variation of the curvature
  have hF : HasDerivAt (fun s : ℝ ↦ rmVec (lcOf (G s)) x a b d)
      (covDLC G t (smoothExt x a) (smoothExt x b) (smoothExt x d) x
        - covDLC G t (smoothExt x b) (smoothExt x a) (smoothExt x d) x) t := by
    have h := hCV G (Ioo 0 T) hJopen hJs t ht
      (smoothExt x a) (smoothExt x b) (smoothExt x d)
      (smoothExt_cmdiff_evol x a) (smoothExt_cmdiff_evol x b) (smoothExt_cmdiff_evol x d) x
    simpa only [rmVec] using h
  -- product rule against the moving metric
  have hmove := Work.Diff.T.hasDerivAt_metric_inner_moving (G := G) (J := Ioo 0 T)
      hJopen hJs ht hF c
  rw [dtMet_eq_neg_two_ricAt G T hflow ht x (rmVec (lcOf (G t)) x a b d) c] at hmove
  simpa only [rmP] using hmove

end Work.Diff.Evol
