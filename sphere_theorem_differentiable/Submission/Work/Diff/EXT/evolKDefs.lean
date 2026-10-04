import Mathlib
import Submission.Work.Diff.EXT.curvDefs
import Submission.Work.Diff.EXT.covKRmExt_tensorial

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Vocabulary for the `k`-th order Shi estimate (area `EXT`, target `Work.Diff.EXT.EvolK`)

`Work.Diff.EXT.EvolK` (defined in `local_ext_of_bounded_curv.lean`) is Hamilton's evolution
inequality for `|∇^k Rm|²` along a Ricci flow, in the form needed by the maximum principle:
for every `k ≥ 1` there is a universal constant `c` such that the right derivative `D` of
`s ↦ |∇^k Rm|²(G s)(x)` is at most `Δ|∇^k Rm|²(G t)(x) + c(1+Σ_{i<k}A_i)(|∇^kRm|²(G t)(x) + 1)`,
whenever `|∇^i Rm|² ≤ A_i` on `[σ,T)` for `i < k`.

The shared vocabulary `covKRm` (the value of `∇^k Rm` on `k` derivative slots and the four
curvature slots) is imported from `Submission.Work.Diff.EXT.curvDefs`, and the tensoriality of the
tower (the value of `covKRmExt` depends only on the values of the fields at the point) is the
*proved* `Work.Diff.EXT.covKRmExt_tensorial` of `Submission/Work/Diff/EXT/covKRmExt_tensorial.lean`
(under `[T2Space M]`, with `LCSmooth I M` available from `[T2Space M]` alone through
`Work.EXT.lcSmooth_noBoundary`); it is imported here so that all consumers of this module have it.
This file adds

* `lapCovKRm g x k u a b c d` — the corresponding component of the *rough* Laplacian
  `Δ∇^k Rm = Σ_m ∇_m ∇_m ∇^k Rm` (traced in the frame `onFrame g x`);
* `EvolCompK k` — the *componentwise* evolution estimate for `∇^k Rm` in a moving orthonormal
  frame, from which `EvolK` is assembled (the `k = 1` case is EV2's analytic core,
  `Work.Diff.GE.covRm_frame_evol_abs`).

The assembly of `EvolK` from `EvolCompK` is in `evolK_of_flow.lean`.
-/

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology BigOperators
open Bundle ContDiff Set VectorField CovariantDerivative Metric

namespace Work.Diff.EXT

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]

/-- The component of the rough Laplacian `Δ∇^k Rm = Σ_m ∇_m ∇_m ∇^k Rm` of the `k`-th covariant
derivative of the curvature, traced in the frame `onFrame g x`. -/
noncomputable def lapCovKRm (g : SMet I M) (x : M) (k : ℕ)
    (u : Fin k → TangentSpace I x) (a b c d : TangentSpace I x) : ℝ :=
  ∑ m : Fin (Module.finrank ℝ E),
    covKRm g x (k + 2) (Fin.cons (onFrame g x m) (Fin.cons (onFrame g x m) u)) a b c d

/-- `|∇^k Rm|² ≥ 0`. -/
theorem curvNormK_nonneg (g : SMet I M) (x : M) (k : ℕ) : 0 ≤ curvNormK g x k :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ =>
    Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _

/-- The componentwise evolution estimate for `∇^k Rm` in a moving orthonormal frame: there is a
constant `C ≥ 0` such that along every Ricci flow `G` on `[0,T)`, at every `t ∈ [0,T)`, `x : M`
and every frame family `e` which is `G s`-orthonormal near `t`, starts at `onFrame (G t) x` and
moves with `G t`-lengths bounded by `K' |Rm|²`, each component of `∇^k Rm` is differentiable in
`s` at `t` and its derivative differs from the corresponding component of the rough Laplacian
`Δ∇^k Rm` by at most `C (1+K') (1 + Σ_{j<k} |∇^j Rm|²) (1 + √|∇^k Rm|²)`.

The lower-order factor is the *linear* sum `1 + Σ_{j<k} f_j` of the lower norms (not its square
root) and the top factor is `1 + √f_k` (not `√f_k`).  Both are forced by the reaction
`∂ₜ∇^k Rm − Δ∇^k Rm = Σ_{i+j=k} ∇^iRm ∗ ∇^jRm`: the pairs with `i,j ≤ k−1` (present from `k = 2`,
e.g. `(∇Rm) ∗ (∇Rm)`) are only bounded by `Σ_{i+j=k,i,j<k}√(f_if_j) ≤ C_k Σ_{j<k} f_j`, and they do
not vanish where `∇^k Rm = 0`.  For `k = 1` the bound is implied (up to a constant) by the GE-area
result `Work.Diff.GE.covRm_frame_evol_abs`, whose bound `C(1+K')√f_0√f_1` is of this shape. -/

def EvolCompK (k : ℕ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧
    ∀ (G : ℝ → SMet I M) (T : ℝ), IsRicciFlow G T → ∀ t ∈ Set.Ico 0 T, ∀ x : M,
      ∀ (e : ℝ → Fin (Module.finrank ℝ E) → TangentSpace I x)
        (edot : Fin (Module.finrank ℝ E) → TangentSpace I x) (K' : ℝ), 0 ≤ K' →
        (∀ i, e t i = onFrame (G t) x i) →
        (∀ i, (G t).inner x (edot i) (edot i) ≤ K' * rmNormSq (G t) x) →
        (∀ᶠ s in nhdsWithin t (Set.Ico 0 T), IsONFrame (G s) x (e s)) →
        (∀ i, HasDerivWithinAt (fun s ↦ e s i) (edot i) (Set.Ico 0 T) t) →
        ∀ (u : Fin k → Fin (Module.finrank ℝ E)) (i j l m : Fin (Module.finrank ℝ E)),
          ∃ D : ℝ,
            HasDerivWithinAt
              (fun s ↦ covKRm (G s) x k (fun r ↦ e s (u r)) (e s i) (e s j) (e s l) (e s m))
              D (Set.Ico 0 T) t ∧
            |D - lapCovKRm (G t) x k (fun r ↦ onFrame (G t) x (u r))
                    (onFrame (G t) x i) (onFrame (G t) x j) (onFrame (G t) x l)
                    (onFrame (G t) x m)|
              ≤ C * (1 + K') * (1 + ∑ j' ∈ Finset.range k, curvNormK (G t) x j')
                  * (1 + Real.sqrt (curvNormK (G t) x k))

/-- The *fixed-vector* form of the componentwise evolution estimate for `∇^k Rm`: along every Ricci
flow, at every `t ∈ [0,T)` and `x`, each component of `∇^k Rm` on five *fixed* tangent vectors has a
right derivative `D` bounded by the corresponding component of the rough Laplacian plus
`C (1 + Σ_{j<k} f_j) (1 + √f_k) · (product of the `G t`-norms of the vectors)`.

Compared with `EvolCompK` there is no frame family and no velocity hypothesis — the `s`-dependence
is only through the metric — and the bound is the one-sided form given directly by the evolution
equation `∂ₜ∇^kRm = Δ∇^kRm + R_k` with `|R_k| ≤ C Σ_{i+j=k}|∇^iRm||∇^jRm|`.  The two-sided
fixed-vector form follows from this one-sided form by the antisymmetry of `∇^kRm` in its first two
curvature slots (`Work.Diff.EXT.covKRmExt_antisymm_pair1`), and the moving-frame form `EvolCompK k`
then follows by expanding the frame in the fixed one (`e s j = Σ_r c (s) j r • e t r`) and using the
multilinearity of `covKRm` (the `(1+K')` factor absorbs the frame velocity). -/
def EvolCompKFix (k : ℕ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧
    ∀ (G : ℝ → SMet I M) (T : ℝ), IsRicciFlow G T → ∀ t ∈ Set.Ico 0 T, ∀ x : M,
      ∀ (u : Fin k → TangentSpace I x) (a b c d : TangentSpace I x),
        ∃ D : ℝ,
          HasDerivWithinAt (fun s => covKRm (G s) x k u a b c d) D (Set.Ico 0 T) t ∧
          D ≤ lapCovKRm (G t) x k u a b c d
              + C * (1 + ∑ j ∈ Finset.range k, curvNormK (G t) x j)
                  * (1 + Real.sqrt (curvNormK (G t) x k))
                  * ((∏ r : Fin k, Real.sqrt ((G t).inner x (u r) (u r)))
                      * Real.sqrt ((G t).inner x a a) * Real.sqrt ((G t).inner x b b)
                      * Real.sqrt ((G t).inner x c c) * Real.sqrt ((G t).inner x d d))

end Work.Diff.EXT
