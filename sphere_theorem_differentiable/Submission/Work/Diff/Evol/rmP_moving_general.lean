import Mathlib
import Submission.Work.Diff.Evol.rmFrameHelpers
import Submission.Work.Diff.GE.NablaRm

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Derivative of `s ↦ Rm^{G s}(A s, B s, C s, D s)` (moving vectors, general frame expansion)

`Work.Diff.Evol.rmP_moving_general`: if the four vectors of the curvature component move, then the
derivative is the product rule applied to the expansion of the four vectors in the *fixed* frame `f`
(which is `G t`-orthonormal, `hon`), combined with the fixed-vector derivatives `Dc` of `hD`.

The expansion `v = ∑ p, ⟪f p, v⟫_{G t} f p` (`Work.Diff.GE.sum_inner_smul_eq_self`) is valid at
every time `s` (the frame `f` is fixed), and `rmP` is `4`-linear (`rmP_expand4`), so
`s ↦ rmP (G s) x (A s) (B s) (C s) (D s)` is the `4`-fold sum of products of the coefficient
functions `s ↦ ⟪f p, A s⟫` (whose derivative is `⟪f p, A'⟫`, `hasDerivAt_inner_moving`) with the
fixed-vector components `s ↦ rmP (G s) x (f p) (f q) (f r) (f u)` (whose derivatives are `Dc`).
-/

set_option maxHeartbeats 1600000

namespace Work.Diff.Evol

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology
open Bundle ContDiff Set VectorField CovariantDerivative Metric

theorem rmP_moving_general
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
      [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]
      [I.Boundaryless] [T2Space M]
    (hLC : Submission.Diff.LCSmooth I M) (G : ℝ → Submission.Diff.SMet I M) (t : ℝ) (x : M)
    (f : Fin (Module.finrank ℝ E) → TangentSpace I x)
    (hn : 0 < Module.finrank ℝ E)
    (A B C D : ℝ → E) (A' B' C' D' : E)
    (Dc : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) →
          Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → ℝ)
    (hon : ∀ i j, (G t).inner x (f i) (f j) = if i = j then (1 : ℝ) else 0)
    (hA : HasDerivAt A A' t) (hB : HasDerivAt B B' t)
    (hC : HasDerivAt C C' t) (hD4 : HasDerivAt D D' t)
    (hD : ∀ p q r u, HasDerivAt (fun s ↦ Submission.Diff.rmP (G s) x (f p) (f q) (f r) (f u))
                          (Dc p q r u) t) :
    HasDerivAt (fun s ↦ Submission.Diff.rmP (G s) x (A s) (B s) (C s) (D s))
      (∑ p, ∑ q, ∑ r, ∑ u,
        ((((G t).inner x (f p) A') * (((G t).inner x (f q) (B t)) * (((G t).inner x (f r) (C t)) * (((G t).inner x (f u) (D t)) * Submission.Diff.rmP (G t) x (f p) (f q) (f r) (f u))))) + ((G t).inner x (f p) (A t)) * ((((G t).inner x (f q) B') * (((G t).inner x (f r) (C t)) * (((G t).inner x (f u) (D t)) * Submission.Diff.rmP (G t) x (f p) (f q) (f r) (f u)))) + ((G t).inner x (f q) (B t)) * ((((G t).inner x (f r) C') * (((G t).inner x (f u) (D t)) * Submission.Diff.rmP (G t) x (f p) (f q) (f r) (f u))) + ((G t).inner x (f r) (C t)) * ((((G t).inner x (f u) D') * Submission.Diff.rmP (G t) x (f p) (f q) (f r) (f u)) + ((G t).inner x (f u) (D t)) * Dc p q r u))))) t := by
  classical
  -- ## Step 1.  Expansion of the four moving vectors in the fixed `G t`-orthonormal frame `f`.
  have hkey : ∀ s : ℝ, rmP (G s) x (A s) (B s) (C s) (D s)
      = ∑ p, ∑ q, ∑ r, ∑ u,
          (G t).inner x (f p) (A s) * ((G t).inner x (f q) (B s) *
            ((G t).inner x (f r) (C s) * ((G t).inner x (f u) (D s) *
              rmP (G s) x (f p) (f q) (f r) (f u)))) := by
    intro s
    have hAe : (∑ p, (G t).inner x (f p) (A s) • f p) = A s :=
      Work.Diff.GE.sum_inner_smul_eq_self (G t) x hn f hon (A s)
    have hBe : (∑ q, (G t).inner x (f q) (B s) • f q) = B s :=
      Work.Diff.GE.sum_inner_smul_eq_self (G t) x hn f hon (B s)
    have hCe : (∑ r, (G t).inner x (f r) (C s) • f r) = C s :=
      Work.Diff.GE.sum_inner_smul_eq_self (G t) x hn f hon (C s)
    have hDe : (∑ u, (G t).inner x (f u) (D s) • f u) = D s :=
      Work.Diff.GE.sum_inner_smul_eq_self (G t) x hn f hon (D s)
    conv_lhs => rw [← hAe, ← hBe, ← hCe, ← hDe]
    exact rmP_expand4 hLC (G s) x (fun p => (G t).inner x (f p) (A s))
      (fun q => (G t).inner x (f q) (B s)) (fun r => (G t).inner x (f r) (C s))
      (fun u => (G t).inner x (f u) (D s)) f
  -- ## Step 2.  Derivatives of the four coefficient families.
  have hAc : ∀ p : Fin (Module.finrank ℝ E),
      HasDerivAt (fun s : ℝ => (G t).inner x (f p) (A s)) ((G t).inner x (f p) A') t :=
    fun p => hasDerivAt_inner_moving (G := G) (t := t) (x := x) (u := f p) hA
  have hBc : ∀ q : Fin (Module.finrank ℝ E),
      HasDerivAt (fun s : ℝ => (G t).inner x (f q) (B s)) ((G t).inner x (f q) B') t :=
    fun q => hasDerivAt_inner_moving (G := G) (t := t) (x := x) (u := f q) hB
  have hCc : ∀ r : Fin (Module.finrank ℝ E),
      HasDerivAt (fun s : ℝ => (G t).inner x (f r) (C s)) ((G t).inner x (f r) C') t :=
    fun r => hasDerivAt_inner_moving (G := G) (t := t) (x := x) (u := f r) hC
  have hDc : ∀ u : Fin (Module.finrank ℝ E),
      HasDerivAt (fun s : ℝ => (G t).inner x (f u) (D s)) ((G t).inner x (f u) D') t :=
    fun u => hasDerivAt_inner_moving (G := G) (t := t) (x := x) (u := f u) hD4
  -- ## Step 3.  The product rule, term by term.
  let b : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) →
      Fin (Module.finrank ℝ E) → ℝ → ℝ := fun p q r u s =>
    (G t).inner x (f p) (A s) * ((G t).inner x (f q) (B s) *
      ((G t).inner x (f r) (C s) * ((G t).inner x (f u) (D s) *
        rmP (G s) x (f p) (f q) (f r) (f u))))
  let b' : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) →
      Fin (Module.finrank ℝ E) → ℝ := fun p q r u =>
    ((((G t).inner x (f p) A') * (((G t).inner x (f q) (B t)) * (((G t).inner x (f r) (C t)) * (((G t).inner x (f u) (D t)) * Submission.Diff.rmP (G t) x (f p) (f q) (f r) (f u))))) + ((G t).inner x (f p) (A t)) * ((((G t).inner x (f q) B') * (((G t).inner x (f r) (C t)) * (((G t).inner x (f u) (D t)) * Submission.Diff.rmP (G t) x (f p) (f q) (f r) (f u)))) + ((G t).inner x (f q) (B t)) * ((((G t).inner x (f r) C') * (((G t).inner x (f u) (D t)) * Submission.Diff.rmP (G t) x (f p) (f q) (f r) (f u))) + ((G t).inner x (f r) (C t)) * ((((G t).inner x (f u) D') * Submission.Diff.rmP (G t) x (f p) (f q) (f r) (f u)) + ((G t).inner x (f u) (D t)) * Dc p q r u))))
  have hb : ∀ p q r u, HasDerivAt (b p q r u) (b' p q r u) t := by
    intro p q r u
    dsimp only [b, b']
    refine ((hAc p).mul ((hBc q).mul ((hCc r).mul ((hDc u).mul (hD p q r u))))).congr_deriv ?_
    simp only [Pi.mul_apply]
  have hsum := hasDerivAt_sum4 b b' hb
  -- ## Step 4.  Transport along the expansion of Step 1.
  have hfun : (fun s : ℝ => rmP (G s) x (A s) (B s) (C s) (D s))
      = (fun s : ℝ => ∑ p, ∑ q, ∑ r, ∑ u, b p q r u s) := by
    funext s
    rw [hkey s]
  rw [← hfun] at hsum
  simpa only [b'] using hsum

end Work.Diff.Evol
