import Mathlib
import Submission.Diff.Evol
import Submission.Work.Diff.T.lcOf_apply_inner_koszul
import Submission.Work.Diff.T.lc_variation
import Submission.Work.Diff.T.metric_family_deriv
import Submission.Work.Diff.T.hasDerivAt_metric_inner_moving
import Submission.Work.Diff.T.dtMet_pairing_smooth

set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Preliminaries for the first variation of the curvature

Short, shared lemmas about the `t`-derivative of the Levi-Civita connection family `lcOf (G t)`,
used by `Work.Diff.GE.curv_variation_neutral` and by the lemmas delegated for it.

* `hasDerivAt_lcOf_fixed` : for fixed smooth fields `Y`, `Z`, the curve `t ↦ ∇^{G t}_Y Z (x)` has
  derivative `dLC G t₀ Y Z x` (this is just the hypothesis `LCVariation` re-read through the
  definition of `dLC`).
* `lcOf_metric_compat_pairing` : metric compatibility of `lcOf g`, in the explicit `g.inner` form.
* `lcOf_metric_pairing` : the derivative form `g(∇_X Y, Z) = X·g(Y,Z) − g(Y, ∇_X Z)`.
* `dLC_pairing` : the pairing form of the derivative of Koszul's formula.
* `dLC_sub_fst` : linearity of `dLC` in its first (direction) slot.
* `dtMet_compat` : the metric compatibility of the *derivative* of the metric family.
-/

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

namespace Work.Diff.GE

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [I.Boundaryless] [T2Space M]

/-- **The derivative of the Levi-Civita connection family on two fixed smooth fields.**
For globally smooth `Y`, `Z` the curve `t ↦ ∇^{G t}_Y Z (x)` is differentiable at `t₀` with
derivative `dLC G t₀ Y Z x`.  (This is `LCVariation`, read through the definition of `dLC`.) -/
theorem hasDerivAt_lcOf_fixed (hLV : LCVariation I M) {G : ℝ → SMet I M} {J : Set ℝ}
    (hJopen : IsOpen J) (hJs : JointSmooth G J) {t₀ : ℝ} (ht₀ : t₀ ∈ J)
    {Y Z : Π x : M, TangentSpace I x} (hY : CMDiff ∞ (T% Y)) (hZ : CMDiff ∞ (T% Z)) (x : M) :
    HasDerivAt (fun t ↦ ((lcOf (G t) Z x (Y x) : TangentSpace I x) : E))
      ((dLC G t₀ Y Z x : TangentSpace I x) : E) t₀ := by
  letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨(G t₀).toRiemannianMetric⟩
  obtain ⟨A, hA, -⟩ := hLV G J hJopen hJs t₀ ht₀ Y Z hY hZ x
  have hA' : A = dLC G t₀ Y Z x := by
    rw [dLC]
    exact (HasDerivAt.deriv hA).symm
  exact hA.congr_deriv hA'

/-- **Metric compatibility of `lcOf g`** in the explicit-inner-product form. -/
theorem lcOf_metric_compat_pairing (hLC : LCSmooth I M) (g : SMet I M)
    {P Q X : Π y : M, TangentSpace I y} (hP : CMDiff ∞ (T% P)) (hQ : CMDiff ∞ (T% Q))
    (hX : CMDiff ∞ (T% X)) (x : M) :
    mvfderiv I (fun y : M ↦ g.inner y (P y) (Q y)) x (X x)
      = g.inner x (lcOf g P x (X x)) (Q x)
        + g.inner x (P x) (lcOf g Q x (X x)) := by
  letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
  haveI : IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x) := inferInstance
  exact (hLC g).2.2 P Q hP hQ x (X x)

/-- **The Leibniz rule for `lcOf g`**, solved for the first slot. -/
theorem lcOf_metric_pairing (hLC : LCSmooth I M) (g : SMet I M)
    {X Y Z : Π y : M, TangentSpace I y} (hX : CMDiff ∞ (T% X)) (hY : CMDiff ∞ (T% Y))
    (hZ : CMDiff ∞ (T% Z)) (x : M) :
    g.inner x (lcOf g Y x (X x)) (Z x)
      = mvfderiv I (fun y : M ↦ g.inner y (Y y) (Z y)) x (X x)
        - g.inner x (Y x) (lcOf g Z x (X x)) := by
  have h := lcOf_metric_compat_pairing hLC g hY hZ hX x
  linarith [h]

/-- **The pairing form of the derivative of Koszul's formula.** -/
theorem dLC_pairing (hLV : LCVariation I M) {G : ℝ → SMet I M} {J : Set ℝ}
    (hJopen : IsOpen J) (hJs : JointSmooth G J) {t₀ : ℝ} (ht₀ : t₀ ∈ J)
    {Y Z W : Π x : M, TangentSpace I x} (hY : CMDiff ∞ (T% Y)) (hZ : CMDiff ∞ (T% Z))
    (hW : CMDiff ∞ (T% W)) (x : M) :
    (G t₀).inner x (dLC G t₀ Y Z x) (W x)
      = (1 / 2 : ℝ) * Work.Diff.T.dtKoszulForm G t₀ Y Z W x
        - dtMet G t₀ x (lcOf (G t₀) Z x (Y x)) (W x) := by
  have hkos : ∀ t : ℝ, Work.Diff.T.koszulForm G Y Z W x t
      = 2 * ((G t).inner x (lcOf (G t) Z x (Y x)) (W x)) := by
    intro t
    have h := Work.Diff.T.lcOf_apply_inner_koszul (G := G) t Y Z W hY hZ hW x
    simp only [Work.Diff.T.koszulForm]
    linarith [h]
  have hd1 := Work.Diff.T.hasDerivAt_koszulForm (G := G) (J := J) hJopen hJs ht₀ Y Z W hY hZ hW x
  have hd2 : HasDerivAt (fun t ↦ 2 * ((G t).inner x (lcOf (G t) Z x (Y x)) (W x)))
      (2 * (dtMet G t₀ x (lcOf (G t₀) Z x (Y x)) (W x)
        + (G t₀).inner x (dLC G t₀ Y Z x) (W x))) t₀ :=
    (Work.Diff.T.hasDerivAt_metric_inner_moving (G := G) (J := J) hJopen hJs ht₀
      (hasDerivAt_lcOf_fixed (I := I) (M := M) hLV hJopen hJs ht₀ hY hZ x) (W x)).const_mul 2
  have huniq := hd1.unique
    (hd2.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t ↦ (hkos t)))
  linarith [huniq]

/-- **Linearity of `dLC` in its first (direction) slot.** -/
theorem dLC_sub_fst (hLV : LCVariation I M) {G : ℝ → SMet I M} {J : Set ℝ}
    (hJopen : IsOpen J) (hJs : JointSmooth G J) {t₀ : ℝ} (ht₀ : t₀ ∈ J)
    {U V W : Π x : M, TangentSpace I x}
    (hU : CMDiff ∞ (T% U)) (hV : CMDiff ∞ (T% V)) (hW : CMDiff ∞ (T% W)) (x : M) :
    dLC G t₀ (fun y : M ↦ U y - V y) W x = dLC G t₀ U W x - dLC G t₀ V W x := by
  letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨(G t₀).toRiemannianMetric⟩
  have h1 := hasDerivAt_lcOf_fixed (I := I) (M := M) hLV hJopen hJs ht₀ hU hW x
  have h2 := hasDerivAt_lcOf_fixed (I := I) (M := M) hLV hJopen hJs ht₀ hV hW x
  have h3 : HasDerivAt (fun t ↦ ((lcOf (G t) W x (U x - V x) : TangentSpace I x) : E))
      (((dLC G t₀ U W x : TangentSpace I x) : E)
        - ((dLC G t₀ V W x : TangentSpace I x) : E)) t₀ := by
    refine (h1.sub h2).congr_of_eventuallyEq (Filter.Eventually.of_forall fun t ↦ ?_)
    exact congrArg (fun z : TangentSpace I x ↦ (z : E))
      (map_sub (lcOf (G t) W x) (U x) (V x))
  have h4 : deriv (fun t ↦ ((lcOf (G t) W x (U x - V x) : TangentSpace I x) : E)) t₀
      = ((dLC G t₀ U W x : TangentSpace I x) : E)
        - ((dLC G t₀ V W x : TangentSpace I x) : E) :=
    HasDerivAt.deriv h3
  rw [dLC, dLC, dLC]
  exact h4

/-- **Metric compatibility of `t ↦ dtMet G t₀`.** -/
theorem dtMet_compat (hLC : LCSmooth I M) (hLV : LCVariation I M) {G : ℝ → SMet I M} {J : Set ℝ}
    (hJopen : IsOpen J) (hJs : JointSmooth G J) {t₀ : ℝ} (ht₀ : t₀ ∈ J)
    {P Q X : Π x : M, TangentSpace I x} (hP : CMDiff ∞ (T% P)) (hQ : CMDiff ∞ (T% Q))
    (hX : CMDiff ∞ (T% X)) (x : M) :
    mvfderiv I (fun y : M ↦ dtMet G t₀ y (P y) (Q y)) x (X x)
      = dtMet G t₀ x (lcOf (G t₀) P x (X x)) (Q x)
        + dtMet G t₀ x (P x) (lcOf (G t₀) Q x (X x))
        + (G t₀).inner x (dLC G t₀ X P x) (Q x)
        + (G t₀).inner x (P x) (dLC G t₀ X Q x) := by
  have hd1 : HasDerivAt (fun t ↦ mvfderiv I (fun y : M ↦ (G t).inner y (P y) (Q y)) x (X x))
      (mvfderiv I (fun y : M ↦ dtMet G t₀ y (P y) (Q y)) x (X x)) t₀ :=
    Work.Diff.T.hasDerivAt_mvfderiv_inner (G := G) (J := J) hJopen hJs ht₀ hP hQ x (X x)
  have hcompat : ∀ t : ℝ, mvfderiv I (fun y : M ↦ (G t).inner y (P y) (Q y)) x (X x)
      = (G t).inner x (lcOf (G t) P x (X x)) (Q x)
        + (G t).inner x (P x) (lcOf (G t) Q x (X x)) :=
    fun t ↦ lcOf_metric_compat_pairing hLC (G t) hP hQ hX x
  have hP1 := Work.Diff.T.hasDerivAt_metric_inner_moving (G := G) (J := J) hJopen hJs ht₀
    (hasDerivAt_lcOf_fixed (I := I) (M := M) hLV hJopen hJs ht₀ hX hP x) (Q x)
  have hP2 := Work.Diff.T.hasDerivAt_metric_inner_moving (G := G) (J := J) hJopen hJs ht₀
    (hasDerivAt_lcOf_fixed (I := I) (M := M) hLV hJopen hJs ht₀ hX hQ x) (P x)
  have hP2' : HasDerivAt (fun t ↦ (G t).inner x (P x) (lcOf (G t) Q x (X x)))
      (dtMet G t₀ x (P x) (lcOf (G t₀) Q x (X x))
        + (G t₀).inner x (P x) (dLC G t₀ X Q x)) t₀ := by
    have h := hP2.congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun t ↦ (G t).symm x (P x) (lcOf (G t) Q x (X x)))
    refine h.congr_deriv ?_
    rw [show dtMet G t₀ x (P x) (lcOf (G t₀) Q x (X x))
          = dtMet G t₀ x (lcOf (G t₀) Q x (X x)) (P x) from
        Work.Diff.T.dtMet_comm G t₀ x (P x) (lcOf (G t₀) Q x (X x)),
      show (G t₀).inner x (P x) (dLC G t₀ X Q x)
          = (G t₀).inner x (dLC G t₀ X Q x) (P x) from
        (G t₀).symm x (P x) (dLC G t₀ X Q x)]
  have hd2 := hP1.add hP2'
  have huniq := hd1.unique (hd2.congr_of_eventuallyEq
    (Filter.Eventually.of_forall fun t ↦ (hcompat t)))
  linarith [huniq]

end Work.Diff.GE
