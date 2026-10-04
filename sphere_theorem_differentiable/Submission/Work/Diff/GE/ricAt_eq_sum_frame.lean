import Mathlib
import Submission.Work.Diff.GE.curvbasic
import Submission.Work.Diff.GE.Frame
import Submission.Work.Diff.GE.frame_deps

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The pointwise trace identity for the Ricci tensor

`ricAt (lcOf g) x u v` is the trace of the endomorphism `w ↦ R(w,u)v` written in the **fixed**
basis `Module.finBasis ℝ E` of the model space `E`, while the metric trace in an orthonormal frame
`e` of `TₓM` reads `∑ m, rmP g x (e m) u (e m) v = ∑ m, g.inner x (R(e m,u)v) (e m)`.

This file proves that the two agree — the basis-independence of the trace of an endomorphism:

`ricAt (lcOf g) x u v = ∑ m, rmP g x (e m) u (e m) v`

for every `g`-orthonormal frame `e` of `TₓM`.

The proof identifies both sides with `LinearMap.trace ℝ E T` for the linear map
`T w = rmVec (lcOf g) x w u v` (linearity in the first slot: `Work.Diff.GE.rmVec_add_left`,
`Work.Diff.GE.rmVec_smul_left`).  The `finBasis` side uses
`LinearMap.trace_eq_matrix_trace` (whose diagonal entries are `b.coord i (T (b i))`), and the
orthonormal side promotes `e` to an orthonormal basis
(`basisOfOrthonormalOfCardEqFinrank`, as in `Work.Diff.GE.sum_inner_smul_eq_self`) and applies
`LinearMap.trace_eq_sum_inner` plus `g.symm`.  The `finrank ℝ E = 0` case is degenerate: both sums
are empty.
-/

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

open scoped Manifold ContDiff Bundle Topology
open Bundle ContDiff Set VectorField CovariantDerivative Metric

namespace Work.Diff.GE

-- The pointwise trace identity for the Ricci tensor: in an orthonormal frame `e`,
--   `ricAt (lcOf g) x u v = ∑ m, g.inner x (rmVec (lcOf g) x (e m) u v) (e m)`
-- (equivalently `∑ m, rmP g x (e m) u (e m) v`), i.e. the frozen trace `ricAt` — the trace of
-- `w ↦ R(w,u)v` in the fixed basis `Module.finBasis ℝ E` of the model space — is the metric trace
-- in the orthonormal frame.  This is the "trace of an endomorphism is basis-independent" fact.
theorem ricAt_eq_sum_frame
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ((⊤ : ENat) : WithTop ENat) M] [T2Space M]
    (hLC : Submission.Diff.LCSmooth I M)
    (g : Submission.Diff.SMet I M) (x : M)
    (e : Fin (Module.finrank ℝ E) → TangentSpace I x) (he : Submission.Diff.IsONFrame g x e)
    (u v : TangentSpace I x) :
    Submission.Diff.ricAt (Submission.Diff.lcOf g) x u v
      = (Finset.univ : Finset (Fin (Module.finrank ℝ E))).sum
          (fun m => Submission.Diff.rmP g x (e m) u (e m) v) := by
  by_cases hn : Module.finrank ℝ E = 0
  · -- degenerate case: both sums are empty
    haveI : IsEmpty (Fin (Module.finrank ℝ E)) := by rw [hn]; infer_instance
    simp only [Submission.Diff.ricAt, Finset.univ_eq_empty, Finset.sum_empty]
  · -- the non-degenerate case: `e` is an orthonormal basis
    letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
    haveI : IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x) := inferInstance
    obtain ⟨hcovne, -, -⟩ := hLC g
    obtain ⟨hcov⟩ := hcovne
    -- the instance inner product is the metric `g.inner`
    have hconv : ∀ a b : TangentSpace I x, Inner.inner ℝ a b = g.inner x a b := fun a b => rfl
    -- `T w = R(w,u)v`, linear in its first slot
    let T : E →ₗ[ℝ] E :=
      { toFun := fun w => Submission.Diff.rmVec (Submission.Diff.lcOf g) x w u v
        map_add' := fun a b =>
          Work.Diff.GE.rmVec_add_left (Submission.Diff.lcOf g) hcov x a b u v
        map_smul' := fun c a =>
          Work.Diff.GE.rmVec_smul_left (Submission.Diff.lcOf g) hcov x c a u v }
    -- the left-hand side is the sum of the diagonal entries of `T` in `Module.finBasis ℝ E`
    have hleft : Submission.Diff.ricAt (Submission.Diff.lcOf g) x u v
        = ∑ i, (Module.finBasis ℝ E).coord i (T ((Module.finBasis ℝ E) i)) := rfl
    have hmatrix : (∑ i, (Module.finBasis ℝ E).coord i (T ((Module.finBasis ℝ E) i)))
        = Matrix.trace (LinearMap.toMatrix (Module.finBasis ℝ E) (Module.finBasis ℝ E) T) := by
      simp only [Matrix.trace, Matrix.diag_apply, LinearMap.toMatrix_apply,
        Module.Basis.coord_apply]
    have htrace : Matrix.trace (LinearMap.toMatrix (Module.finBasis ℝ E) (Module.finBasis ℝ E) T)
        = LinearMap.trace ℝ E T :=
      (LinearMap.trace_eq_matrix_trace ℝ (Module.finBasis ℝ E) T).symm
    have hbridge : LinearMap.trace ℝ E T = LinearMap.trace ℝ (TangentSpace I x) T := rfl
    -- promote `e` to an orthonormal basis
    have hnpos : 0 < Module.finrank ℝ E := Nat.pos_of_ne_zero hn
    haveI : Nonempty (Fin (Module.finrank ℝ E)) := Fin.pos_iff_nonempty.mp hnpos
    have hon : Orthonormal ℝ e := by
      rw [orthonormal_iff_ite]
      intro i j
      rw [hconv (e i) (e j)]
      exact he i j
    let c : Module.Basis (Fin (Module.finrank ℝ E)) ℝ (TangentSpace I x) :=
      basisOfOrthonormalOfCardEqFinrank hon (by rw [Fintype.card_fin]; rfl)
    have hc : (c : Fin (Module.finrank ℝ E) → TangentSpace I x) = e :=
      coe_basisOfOrthonormalOfCardEqFinrank hon _
    have honc : Orthonormal ℝ (c : Fin (Module.finrank ℝ E) → TangentSpace I x) := by
      rw [hc]; exact hon
    -- the trace in the orthonormal basis is the sum of the metric pairings
    have hsuminner : LinearMap.trace ℝ (TangentSpace I x) T
        = ∑ i, Inner.inner ℝ (e i) (T (e i)) := by
      have h := LinearMap.trace_eq_sum_inner T (c.toOrthonormalBasis honc)
      rw [Module.Basis.coe_toOrthonormalBasis c honc, hc] at h
      exact h
    have hfinal : (∑ i, Inner.inner ℝ (e i) (T (e i)))
        = ∑ i, Submission.Diff.rmP g x (e i) u (e i) v := by
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [hconv (e i) (T (e i)), g.symm x (e i) (T (e i))]
      rfl
    exact hleft.trans (hmatrix.trans (htrace.trans (hbridge.trans (hsuminner.trans hfinal))))

end Work.Diff.GE
