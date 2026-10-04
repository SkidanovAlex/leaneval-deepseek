import Mathlib
import Submission.Work.Diff.Evol.cv_prelim
import Submission.Work.Diff.Evol.cv_section
import Submission.Work.Diff.Evol.cv_dLC
import Submission.Work.Diff.Evol.cv_product
import Submission.Work.Diff.GE.curv_var_prelim
import Submission.Work.Diff.T.hasDerivAt_of_eventually_system
import Submission.Work.Diff.EXT.mvfderiv_metric_pairing_split
import Submission.Work.Diff.EXT.contMDiffAt_metric_pairing
import Submission.Work.Diff.T.metric_family_deriv

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The product rule `∂ₜ ∇^t_X (∇^t_Y Z) = ∇^{t₀}_X (dLC Y Z) + dLC X (∇^{t₀}_Y Z)`

`cv_compose_lcOf_deriv`: for fixed smooth fields `X`, `Y`, `Z` the curve
`t ↦ ∇^{G t}_X(∇^{G t}_Y Z)(x)` is differentiable at `t₀` with derivative
`∇^{G t₀}_X(∂ₜ∇^{G t₀}_Y Z)(x) + (∂ₜ∇^{G t₀}_X)(∇^{G t₀}_Y Z)(x)`.

The proof tests the curve against a `(G t₀)`-orthonormal basis of `TₓM` (extended to globally
smooth fields) and solves the resulting linear system, exactly as in
`Work.Diff.T.lc_variation`.
-/

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1000000

namespace Work.Diff.Evol

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [I.Boundaryless] [T2Space M]

/-- Smoothness of a metric pairing of fields that are smooth only at the point. -/
theorem cv_metric_pairing_at_loc {g : SMet I M} {Y Z : Π y : M, TangentSpace I y} {x : M}
    (hY : CMDiffAt ∞ (T% Y) x) (hZ : CMDiffAt ∞ (T% Z) x) :
    CMDiffAt ∞ (fun y : M ↦ g.inner y (Y y) (Z y)) x := by
  have hJ := Work.Diff.EXT.contMDiffAt_metric_pairing (I := I) (M := M)
    (G := fun _ : ℝ ↦ g) (J := Set.univ) isOpen_univ (cv_jointSmooth_const (I := I) (M := M) g)
    (t₀ := 0) trivial (x := x) hY hZ
  exact cv_slice_of_joint (I := I) (M := M) hJ

/-- Expansion of a vector in a `(G t₀)`-orthonormal basis: `v = ∑ j, ⟪v, b j⟫ • b j`. -/
theorem cv_sum_repr {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ V) (v : V) :
    ∑ j, inner ℝ v (b j) • b j = v := by
  conv_rhs => rw [← OrthonormalBasis.sum_repr' b v]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [real_inner_comm v (b j)]

/-- **The product rule for the composed connection.** -/
theorem cv_compose_lcOf_deriv
    (hLC : LCSmooth I M) (hLV : LCVariation I M)
    {G : ℝ → SMet I M} {J : Set ℝ} (hJopen : IsOpen J) (hJs : JointSmooth G J)
    {t₀ : ℝ} (ht₀ : t₀ ∈ J)
    (X Y Z : Π y : M, TangentSpace I y) (hX : CMDiff ∞ (T% X)) (hY : CMDiff ∞ (T% Y))
    (hZ : CMDiff ∞ (T% Z)) (x : M) :
    HasDerivAt (fun t : ℝ ↦ lcOf (G t) (fun y : M ↦ lcOf (G t) Z y (Y y)) x (X x))
      (lcOf (G t₀) (fun y : M ↦ dLC G t₀ Y Z y) x (X x)
        + dLC G t₀ X (fun y : M ↦ lcOf (G t₀) Z y (Y y)) x) t₀ := by
  classical
  letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨(G t₀).toRiemannianMetric⟩
  haveI : IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x) := inferInstance
  have hWsm : CMDiff ∞ (T% (fun y : M ↦ lcOf (G t₀) Z y (Y y))) :=
    cv_lcOf_arg_smooth (I := I) (M := M) hLC (G t₀) hY hZ
  have hOsm : CMDiffAt ∞ (T% (fun y : M ↦ dLC G t₀ Y Z y)) x :=
    cv_dLC_smooth (I := I) (M := M) hLC hLV hJopen hJs ht₀ Y Z hY hZ x
  -- the orthonormal basis at `x` and globally smooth fields through it
  let b : OrthonormalBasis (Fin (Module.finrank ℝ E)) ℝ (TangentSpace I x) :=
    stdOrthonormalBasis ℝ (TangentSpace I x)
  have hSec : ∀ j : Fin (Module.finrank ℝ E), ∃ W : Π y : M, TangentSpace I y,
      CMDiff ∞ (T% W) ∧ W x = b j :=
    fun j ↦ Commons.Geometry.Manifold.VectorField.exists_contMDiff_section_apply_eq (b j)
  choose F hFs hFv using hSec
  -- ## the algebraic form of `cv_RjPrime`
  have hkey : ∀ (Fj : Π y : M, TangentSpace I y), CMDiff ∞ (T% Fj) →
      cv_RjPrime G t₀ X Y Z Fj x
        = dtMet G t₀ x (lcOf (G t₀) (fun y : M ↦ lcOf (G t₀) Z y (Y y)) x (X x)) (Fj x)
          + (G t₀).inner x (dLC G t₀ X (fun y : M ↦ lcOf (G t₀) Z y (Y y)) x) (Fj x)
          + (G t₀).inner x (lcOf (G t₀) (fun y : M ↦ dLC G t₀ Y Z y) x (X x)) (Fj x) := by
    intro Fj hFj
    have hmd1 : MDifferentiableAt I 𝓘(ℝ, ℝ)
        (fun y : M ↦ dtMet G t₀ y (lcOf (G t₀) Z y (Y y)) (Fj y)) x :=
      (Work.Diff.T.dtMet_pairing_smooth hJopen hJs ht₀ hWsm hFj x).mdifferentiableAt (by simp)
    have hmd2 : MDifferentiableAt I 𝓘(ℝ, ℝ)
        (fun y : M ↦ (G t₀).inner y (dLC G t₀ Y Z y) (Fj y)) x :=
      (cv_metric_pairing_at_loc (I := I) (M := M) (g := G t₀) hOsm hFj.contMDiffAt).mdifferentiableAt
        (by simp)
    have hsplit : mvfderiv I (fun y : M ↦ dtMet G t₀ y (lcOf (G t₀) Z y (Y y)) (Fj y)
          + (G t₀).inner y (dLC G t₀ Y Z y) (Fj y)) x (X x)
        = mvfderiv I (fun y : M ↦ dtMet G t₀ y (lcOf (G t₀) Z y (Y y)) (Fj y)) x (X x)
          + mvfderiv I (fun y : M ↦ (G t₀).inner y (dLC G t₀ Y Z y) (Fj y)) x (X x) := by
      have h := mvfderiv_add (g := fun y : M ↦ dtMet G t₀ y (lcOf (G t₀) Z y (Y y)) (Fj y))
        (g' := fun y : M ↦ (G t₀).inner y (dLC G t₀ Y Z y) (Fj y)) hmd1 hmd2
      exact congrArg (fun L : TangentSpace I x →L[ℝ] ℝ ↦ L (X x)) h
    have hA := Work.Diff.GE.dtMet_compat (I := I) (M := M) hLC hLV hJopen hJs ht₀
      (P := fun y : M ↦ lcOf (G t₀) Z y (Y y)) (Q := Fj) (X := X) hWsm hFj hX x
    have hB := Work.Diff.EXT.mvfderiv_metric_pairing_split (I := I) (M := M) hLC (G t₀)
      (W := fun y : M ↦ dLC G t₀ Y Z y) (Z := Fj) (y := x) (v := X x)
      (hOsm.mdifferentiableAt (by simp)) (hFj.contMDiffAt.mdifferentiableAt (by simp))
    simp only [cv_RjPrime]
    rw [hsplit, hA, hB]
    ring
  -- ## expansion of `u_t` in the basis
  have hExp (t : ℝ) :
      lcOf (G t) (fun y : M ↦ lcOf (G t) Z y (Y y)) x (X x)
        = ∑ j, ((G t₀).inner x
            (lcOf (G t) (fun y : M ↦ lcOf (G t) Z y (Y y)) x (X x)) (b j)) • b j := by
    conv_lhs => rw [← OrthonormalBasis.sum_repr' b
      (lcOf (G t) (fun y : M ↦ lcOf (G t) Z y (Y y)) x (X x))]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    congr 1
    exact real_inner_comm _ _
  -- ## the (exact) linear system solved by the coefficients
  have hident (t : ℝ) (j : Fin (Module.finrank ℝ E)) :
      (G t₀).inner x (lcOf (G t) (fun y : M ↦ lcOf (G t) Z y (Y y)) x (X x)) (b j)
        = (G t).inner x (lcOf (G t) (fun y : M ↦ lcOf (G t) Z y (Y y)) x (X x)) (F j x)
          - ∑ k, ((G t₀).inner x
                (lcOf (G t) (fun y : M ↦ lcOf (G t) Z y (Y y)) x (X x)) (b k))
              * ((G t).inner x (b k) (b j) - (G t₀).inner x (b k) (b j)) := by
    have h2 : (G t).inner x (lcOf (G t) (fun y : M ↦ lcOf (G t) Z y (Y y)) x (X x)) (F j x)
        = ∑ k, ((G t₀).inner x
              (lcOf (G t) (fun y : M ↦ lcOf (G t) Z y (Y y)) x (X x)) (b k))
            * ((G t).inner x (b k) (b j)) := by
      rw [hFv j]
      conv_lhs => rw [hExp t]
      exact Work.Diff.T.inner_sum_smul G t x Finset.univ
        (fun k ↦ (G t₀).inner x
          (lcOf (G t) (fun y : M ↦ lcOf (G t) Z y (Y y)) x (X x)) (b k))
        (fun k ↦ b k) (b j)
    have h3 : (G t₀).inner x (lcOf (G t) (fun y : M ↦ lcOf (G t) Z y (Y y)) x (X x)) (b j)
        = ∑ k, ((G t₀).inner x
              (lcOf (G t) (fun y : M ↦ lcOf (G t) Z y (Y y)) x (X x)) (b k))
            * ((G t₀).inner x (b k) (b j)) := by
      conv_lhs => rw [hExp t]
      exact Work.Diff.T.inner_sum_smul G t₀ x Finset.univ
        (fun k ↦ (G t₀).inner x
          (lcOf (G t) (fun y : M ↦ lcOf (G t) Z y (Y y)) x (X x)) (b k))
        (fun k ↦ b k) (b j)
    have h4 : ∑ k, ((G t₀).inner x
            (lcOf (G t) (fun y : M ↦ lcOf (G t) Z y (Y y)) x (X x)) (b k))
          * ((G t).inner x (b k) (b j) - (G t₀).inner x (b k) (b j))
        = (∑ k, ((G t₀).inner x
              (lcOf (G t) (fun y : M ↦ lcOf (G t) Z y (Y y)) x (X x)) (b k))
            * ((G t).inner x (b k) (b j)))
          - ∑ k, ((G t₀).inner x
              (lcOf (G t) (fun y : M ↦ lcOf (G t) Z y (Y y)) x (X x)) (b k))
              * ((G t₀).inner x (b k) (b j)) := by
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun k _ ↦ by ring
    rw [h4, ← h3, ← h2]
    ring
  -- ## differentiability of the coefficients
  have hsumTot (j : Fin (Module.finrank ℝ E)) :
      ∑ k, ((G t₀).inner x
            (lcOf (G t₀) (fun y : M ↦ lcOf (G t₀) Z y (Y y)) x (X x)) (b k))
          * dtMet G t₀ x (b k) (b j)
        = dtMet G t₀ x
            (lcOf (G t₀) (fun y : M ↦ lcOf (G t₀) Z y (Y y)) x (X x)) (b j) := by
    rw [← Work.Diff.T.dtMet_sum_fst Finset.univ hJopen hJs ht₀ x
      (fun k ↦ (G t₀).inner x
        (lcOf (G t₀) (fun y : M ↦ lcOf (G t₀) Z y (Y y)) x (X x)) (b k))
      (fun k ↦ b k) (b j)]
    rw [← hExp t₀]
  have hderiv (j : Fin (Module.finrank ℝ E)) :
      HasDerivAt (fun t : ℝ ↦ (G t₀).inner x
          (lcOf (G t) (fun y : M ↦ lcOf (G t) Z y (Y y)) x (X x)) (b j))
        (cv_RjPrime G t₀ X Y Z (F j) x
          - ∑ k, ((G t₀).inner x
                (lcOf (G t₀) (fun y : M ↦ lcOf (G t₀) Z y (Y y)) x (X x)) (b k))
              * dtMet G t₀ x (b k) (b j)) t₀ :=
    Work.Diff.T.hasDerivAt_of_eventually_system
      (ι := Fin (Module.finrank ℝ E))
      (Ψ := fun t (j : Fin (Module.finrank ℝ E)) ↦
        (G t₀).inner x (lcOf (G t) (fun y : M ↦ lcOf (G t) Z y (Y y)) x (X x)) (b j))
      (K := fun t (j : Fin (Module.finrank ℝ E)) ↦
        (G t).inner x (lcOf (G t) (fun y : M ↦ lcOf (G t) Z y (Y y)) x (X x)) (F j x))
      (A := fun k (j : Fin (Module.finrank ℝ E)) t ↦
        (G t).inner x (b k) (b j) - (G t₀).inner x (b k) (b j))
      (K' := fun j ↦ cv_RjPrime G t₀ X Y Z (F j) x)
      (h := fun k j ↦ dtMet G t₀ x (b k) (b j))
      (fun k j ↦ sub_self _)
      (Filter.Eventually.of_forall hident)
      (fun j ↦ cv_Rj_deriv (I := I) (M := M) hLC hLV hJopen hJs ht₀ X Y Z hX hY hZ x (F j) (hFs j))
      (fun k j ↦ (Work.Diff.T.metric_family_deriv hJopen hJs ht₀ x (b k) (b j)).sub_const _)
      j
  -- ## the derivative of the composed connection
  have hFderiv : HasDerivAt (fun t : ℝ ↦ lcOf (G t) (fun y : M ↦ lcOf (G t) Z y (Y y)) x (X x))
      (∑ j, (cv_RjPrime G t₀ X Y Z (F j) x
        - ∑ k, ((G t₀).inner x
              (lcOf (G t₀) (fun y : M ↦ lcOf (G t₀) Z y (Y y)) x (X x)) (b k))
            * dtMet G t₀ x (b k) (b j)) • b j) t₀ := by
    have h1sum := HasDerivAt.sum (u := Finset.univ) fun j _ ↦ (hderiv j).smul_const (b j)
    have hfun : (∑ j ∈ Finset.univ, fun t ↦ ((G t₀).inner x
          (lcOf (G t) (fun y : M ↦ lcOf (G t) Z y (Y y)) x (X x)) (b j)) • b j)
        = (fun t ↦ ∑ j, ((G t₀).inner x
            (lcOf (G t) (fun y : M ↦ lcOf (G t) Z y (Y y)) x (X x)) (b j)) • b j) :=
      funext fun t ↦ Finset.sum_apply _ _ _
    rw [hfun] at h1sum
    exact h1sum.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t ↦ hExp t)
  -- ## identification of the derivative
  refine hFderiv.congr_deriv ?_
  have hsum1 : ∀ j : Fin (Module.finrank ℝ E),
      cv_RjPrime G t₀ X Y Z (F j) x
        - ∑ k, ((G t₀).inner x
              (lcOf (G t₀) (fun y : M ↦ lcOf (G t₀) Z y (Y y)) x (X x)) (b k))
            * dtMet G t₀ x (b k) (b j)
      = (G t₀).inner x (dLC G t₀ X (fun y : M ↦ lcOf (G t₀) Z y (Y y)) x) (b j)
        + (G t₀).inner x (lcOf (G t₀) (fun y : M ↦ dLC G t₀ Y Z y) x (X x)) (b j) := by
    intro j
    rw [hsumTot j, hkey (F j) (hFs j), hFv j]
    ring
  have hstep : (∑ j, (cv_RjPrime G t₀ X Y Z (F j) x
        - ∑ k, ((G t₀).inner x
              (lcOf (G t₀) (fun y : M ↦ lcOf (G t₀) Z y (Y y)) x (X x)) (b k))
            * dtMet G t₀ x (b k) (b j)) • b j)
      = (∑ j, ((G t₀).inner x
            (dLC G t₀ X (fun y : M ↦ lcOf (G t₀) Z y (Y y)) x)) (b j) • b j)
        + ∑ j, ((G t₀).inner x
            (lcOf (G t₀) (fun y : M ↦ dLC G t₀ Y Z y) x (X x))) (b j) • b j := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [hsum1 j, add_smul]
  have hs1 : (∑ j, ((G t₀).inner x
        (dLC G t₀ X (fun y : M ↦ lcOf (G t₀) Z y (Y y)) x)) (b j) • b j)
      = dLC G t₀ X (fun y : M ↦ lcOf (G t₀) Z y (Y y)) x :=
    cv_sum_repr b (dLC G t₀ X (fun y : M ↦ lcOf (G t₀) Z y (Y y)) x)
  have hs2 : (∑ j, ((G t₀).inner x
        (lcOf (G t₀) (fun y : M ↦ dLC G t₀ Y Z y) x (X x))) (b j) • b j)
      = lcOf (G t₀) (fun y : M ↦ dLC G t₀ Y Z y) x (X x) :=
    cv_sum_repr b (lcOf (G t₀) (fun y : M ↦ dLC G t₀ Y Z y) x (X x))
  rw [hstep, hs1, hs2, add_comm]

end Work.Diff.Evol
