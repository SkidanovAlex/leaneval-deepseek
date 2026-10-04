import Mathlib
import Submission.Work.Diff.T.lcOf_apply_inner_koszul
import Submission.Work.Diff.T.lc_variation
import Submission.Work.Diff.T.dtMet_pairing_smooth
import Submission.Work.Diff.T.metric_pairing_smooth
import Submission.Work.Diff.T.metric_family_deriv
import Submission.Work.Diff.T.hasDerivAt_metric_inner_moving
import Submission.Work.Diff.Evol.clairaut_mvfderiv
import Submission.Work.Diff.EXT.contMDiffAt_mvfderiv_along_field
import Submission.Work.Diff.EXT.contMDiffAt_mvfderiv_along_field_at
import Submission.Work.Diff.EXT.contMDiffAt_metric_pairing

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Preliminaries for the first variation of the curvature

* `cv_mlieBracket_cmdiff` — the Lie bracket of smooth fields is smooth.
* `cv_koszulForm_joint`, `cv_lcOf_pairing_joint` — joint smoothness of the Koszul form and of
  the pairings of `∇^{G t}_Y Z`.
* `cv_bilin_curve_littleO` — little-o for a bilinear-form curve applied to a little-o direction.
* `cv_metric_inner_moving_pair` — product rule for the metric family against two moving vectors.
* `cv_dtKoszulForm_at` — `y ↦ dtKoszulForm G t₀ Y Z W y` is smooth.
-/

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 1000000

namespace Work.Diff.Evol

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter Asymptotics

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [I.Boundaryless] [T2Space M]

/-- The Lie bracket of two smooth fields is a smooth field. -/
theorem cv_mlieBracket_cmdiff
    {U V : Π y : M, TangentSpace I y} (hU : CMDiff ∞ (T% U)) (hV : CMDiff ∞ (T% V)) :
    CMDiff ∞ (T% (mlieBracket I U V)) := by
  haveI : IsManifold I (minSmoothness ℝ 2) M := by
    rw [minSmoothness_of_isRCLikeNormedField]; infer_instance
  haveI : IsManifold I ((∞ : ℕ∞ω) + 1) M := by
    have h : (∞ : ℕ∞ω) + 1 = ∞ := by simp
    rw [h]; infer_instance
  intro y
  exact (hU y).mlieBracket_vectorField (hV y) (by simp)

/-- **Joint smoothness of the Koszul form.** -/
theorem cv_koszulForm_joint
    {G : ℝ → SMet I M} {J : Set ℝ} (hJopen : IsOpen J) (hJs : JointSmooth G J)
    {t₀ : ℝ} (ht₀ : t₀ ∈ J)
    (X Y Z : Π y : M, TangentSpace I y)
    (hX : CMDiff ∞ (T% X)) (hY : CMDiff ∞ (T% Y)) (hZ : CMDiff ∞ (T% Z)) (x : M) :
    ContMDiffAt (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M ↦ Work.Diff.T.koszulForm G X Y Z p.2 p.1) (t₀, x) := by
  have hXa : Work.Diff.EXT.SmoothFieldAt I M X x := hX.contMDiffAt
  have hYa : Work.Diff.EXT.SmoothFieldAt I M Y x := hY.contMDiffAt
  have hZa : Work.Diff.EXT.SmoothFieldAt I M Z x := hZ.contMDiffAt
  have hXsm : Work.Diff.EXT.SmoothField I M X := hX
  have hYsm : Work.Diff.EXT.SmoothField I M Y := hY
  have hZsm : Work.Diff.EXT.SmoothField I M Z := hZ
  have h1 : ContMDiffAt (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M ↦ mvfderiv I (fun y : M ↦ (G p.1).inner y (Y y) (Z y)) p.2 (X p.2)) (t₀, x) :=
    Work.Diff.EXT.contMDiffAt_mvfderiv_along_field (I := I) (M := M)
      (Φ := fun p : ℝ × M ↦ (G p.1).inner p.2 (Y p.2) (Z p.2)) (A := X)
      (Work.Diff.EXT.contMDiffAt_metric_pairing (I := I) (M := M) hJopen hJs ht₀ hYa hZa) hXsm
  have h2 : ContMDiffAt (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M ↦ mvfderiv I (fun y : M ↦ (G p.1).inner y (Z y) (X y)) p.2 (Y p.2)) (t₀, x) :=
    Work.Diff.EXT.contMDiffAt_mvfderiv_along_field (I := I) (M := M)
      (Φ := fun p : ℝ × M ↦ (G p.1).inner p.2 (Z p.2) (X p.2)) (A := Y)
      (Work.Diff.EXT.contMDiffAt_metric_pairing (I := I) (M := M) hJopen hJs ht₀ hZa hXa) hYsm
  have h3 : ContMDiffAt (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M ↦ mvfderiv I (fun y : M ↦ (G p.1).inner y (X y) (Y y)) p.2 (Z p.2)) (t₀, x) :=
    Work.Diff.EXT.contMDiffAt_mvfderiv_along_field (I := I) (M := M)
      (Φ := fun p : ℝ × M ↦ (G p.1).inner p.2 (X p.2) (Y p.2)) (A := Z)
      (Work.Diff.EXT.contMDiffAt_metric_pairing (I := I) (M := M) hJopen hJs ht₀ hXa hYa) hZsm
  have hbr1 : CMDiff ∞ (T% (mlieBracket I X Z)) := cv_mlieBracket_cmdiff hX hZ
  have hbr2 : CMDiff ∞ (T% (mlieBracket I Y X)) := cv_mlieBracket_cmdiff hY hX
  have hbr3 : CMDiff ∞ (T% (mlieBracket I Z Y)) := cv_mlieBracket_cmdiff hZ hY
  have h4 : ContMDiffAt (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M ↦ (G p.1).inner p.2 (Y p.2) (mlieBracket I X Z p.2)) (t₀, x) :=
    Work.Diff.EXT.contMDiffAt_metric_pairing (I := I) (M := M) hJopen hJs ht₀ hYa hbr1.contMDiffAt
  have h5 : ContMDiffAt (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M ↦ (G p.1).inner p.2 (Z p.2) (mlieBracket I Y X p.2)) (t₀, x) :=
    Work.Diff.EXT.contMDiffAt_metric_pairing (I := I) (M := M) hJopen hJs ht₀ hZa hbr2.contMDiffAt
  have h6 : ContMDiffAt (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M ↦ (G p.1).inner p.2 (X p.2) (mlieBracket I Z Y p.2)) (t₀, x) :=
    Work.Diff.EXT.contMDiffAt_metric_pairing (I := I) (M := M) hJopen hJs ht₀ hXa hbr3.contMDiffAt
  have hmain := ((((h1.add h2).sub h3).sub h4).sub h5).add h6
  refine hmain.congr_of_eventuallyEq (Filter.Eventually.of_forall fun p ↦ ?_)
  simp only [Work.Diff.T.koszulForm, Pi.add_apply]

/-- **Joint smoothness of the pairing of `∇^{G t}_Y Z` with a fixed field.** -/
theorem cv_lcOf_pairing_joint
    {G : ℝ → SMet I M} {J : Set ℝ} (hJopen : IsOpen J) (hJs : JointSmooth G J)
    {t₀ : ℝ} (ht₀ : t₀ ∈ J)
    (Y Z F : Π y : M, TangentSpace I y)
    (hY : CMDiff ∞ (T% Y)) (hZ : CMDiff ∞ (T% Z)) (hF : CMDiff ∞ (T% F)) (x : M) :
    ContMDiffAt (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M ↦ (G p.1).inner p.2 (lcOf (G p.1) Z p.2 (Y p.2)) (F p.2)) (t₀, x) := by
  have hkos := cv_koszulForm_joint (I := I) (M := M) hJopen hJs ht₀ Y Z F hY hZ hF x
  have hhalf : ContMDiffAt (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M ↦ (1 / 2 : ℝ) * Work.Diff.T.koszulForm G Y Z F p.2 p.1) (t₀, x) :=
    (contMDiffAt_const (c := (1 / 2 : ℝ))).mul hkos
  refine hhalf.congr_of_eventuallyEq (Filter.Eventually.of_forall fun p ↦ ?_)
  have key := Work.Diff.T.lcOf_apply_inner_koszul (G := G) p.1 Y Z F hY hZ hF p.2
  simp only [Work.Diff.T.koszulForm] at key ⊢
  exact key

/-- A smooth function on `M`, seen as a function of `(t, y)`, is jointly smooth. -/
theorem cv_jointSmoothAt_of_slice {φ : M → ℝ} {x : M} (hφ : CMDiffAt ∞ φ x) (t₀ : ℝ) :
    ContMDiffAt (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞ (fun p : ℝ × M ↦ φ p.2) (t₀, x) := by
  have h2 : ContMDiffAt ((𝓘(ℝ,ℝ)).prod I) I ∞ (Prod.snd : ℝ × M → M) (t₀, x) :=
    contMDiffAt_snd (I := 𝓘(ℝ,ℝ)) (J := I)
  exact ContMDiffAt.comp (t₀, x) hφ h2

/-- The slice at a fixed time of a jointly smooth function is smooth. -/
theorem cv_slice_of_joint {Φ : ℝ × M → ℝ} {t₀ : ℝ} {x : M}
    (h : ContMDiffAt (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞ Φ (t₀, x)) :
    CMDiffAt ∞ (fun y : M ↦ Φ (t₀, y)) x := by
  have h2 : ContMDiffAt I ((𝓘(ℝ,ℝ)).prod I) ∞ (fun y : M ↦ ((t₀, y) : ℝ × M)) x :=
    contMDiffAt_const.prodMk contMDiffAt_id
  exact ContMDiffAt.comp x h h2

/-- The spatial derivative of a jointly smooth family along a smooth field, sliced at a fixed
time, is smooth. -/
theorem cv_mvfderiv_slice {Φ : ℝ × M → ℝ} {t₀ : ℝ} {x : M}
    {V : Π y : M, TangentSpace I y}
    (hΦ : ContMDiffAt (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞ Φ (t₀, x)) (hV : CMDiff ∞ (T% V)) :
    CMDiffAt ∞ (fun y : M ↦ mvfderiv I (fun z : M ↦ Φ (t₀, z)) y (V y)) x := by
  have hjoint := Work.Diff.EXT.contMDiffAt_mvfderiv_along_field (I := I) (M := M)
    (Φ := Φ) (A := V) hΦ hV
  have h2 : ContMDiffAt I ((𝓘(ℝ,ℝ)).prod I) ∞ (fun y : M ↦ ((t₀, y) : ℝ × M)) x :=
    contMDiffAt_const.prodMk contMDiffAt_id
  exact ContMDiffAt.comp x hjoint h2

/-- **Smoothness in the space variable of the Koszul-form derivative.** -/
theorem cv_dtKoszulForm_at
    {G : ℝ → SMet I M} {J : Set ℝ} (hJopen : IsOpen J) (hJs : JointSmooth G J)
    {t₀ : ℝ} (ht₀ : t₀ ∈ J)
    (X Y Z : Π y : M, TangentSpace I y)
    (hX : CMDiff ∞ (T% X)) (hY : CMDiff ∞ (T% Y)) (hZ : CMDiff ∞ (T% Z)) (x : M) :
    CMDiffAt ∞ (fun y : M ↦ Work.Diff.T.dtKoszulForm G t₀ X Y Z y) x := by
  have hbr1 : CMDiff ∞ (T% (mlieBracket I X Z)) := cv_mlieBracket_cmdiff hX hZ
  have hbr2 : CMDiff ∞ (T% (mlieBracket I Y X)) := cv_mlieBracket_cmdiff hY hX
  have hbr3 : CMDiff ∞ (T% (mlieBracket I Z Y)) := cv_mlieBracket_cmdiff hZ hY
  have hsm : ∀ {P Q : Π y : M, TangentSpace I y}, CMDiff ∞ (T% P) → CMDiff ∞ (T% Q) →
      ContMDiffAt (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
        (fun p : ℝ × M ↦ dtMet G t₀ p.2 (P p.2) (Q p.2)) (t₀, x) := by
    intro P Q hP hQ
    have h1 : CMDiffAt ∞ (fun y : M ↦ dtMet G t₀ y (P y) (Q y)) x :=
      Work.Diff.T.dtMet_pairing_smooth hJopen hJs ht₀ hP hQ x
    have h2 : ContMDiffAt ((𝓘(ℝ,ℝ)).prod I) I ∞ (Prod.snd : ℝ × M → M) (t₀, x) :=
      contMDiffAt_snd (I := 𝓘(ℝ,ℝ)) (J := I)
    exact ContMDiffAt.comp (t₀, x) h1 h2
  have t1 : CMDiffAt ∞
      (fun y : M ↦ mvfderiv I (fun z : M ↦ dtMet G t₀ z (Y z) (Z z)) y (X y)) x :=
    cv_mvfderiv_slice (I := I) (M := M) (hsm hY hZ) hX
  have t2 : CMDiffAt ∞
      (fun y : M ↦ mvfderiv I (fun z : M ↦ dtMet G t₀ z (Z z) (X z)) y (Y y)) x :=
    cv_mvfderiv_slice (I := I) (M := M) (hsm hZ hX) hY
  have t3 : CMDiffAt ∞
      (fun y : M ↦ mvfderiv I (fun z : M ↦ dtMet G t₀ z (X z) (Y z)) y (Z y)) x :=
    cv_mvfderiv_slice (I := I) (M := M) (hsm hX hY) hZ
  have t4 : CMDiffAt ∞
      (fun y : M ↦ dtMet G t₀ y (Y y) (mlieBracket I X Z y)) x :=
    cv_slice_of_joint (I := I) (M := M) (hsm hY hbr1)
  have t5 : CMDiffAt ∞
      (fun y : M ↦ dtMet G t₀ y (Z y) (mlieBracket I Y X y)) x :=
    cv_slice_of_joint (I := I) (M := M) (hsm hZ hbr2)
  have t6 : CMDiffAt ∞
      (fun y : M ↦ dtMet G t₀ y (X y) (mlieBracket I Z Y y)) x :=
    cv_slice_of_joint (I := I) (M := M) (hsm hX hbr3)
  have hmain := ((((t1.add t2).sub t3).sub t4).sub t5).add t6
  refine hmain.congr_of_eventuallyEq (Filter.Eventually.of_forall fun y ↦ ?_)
  simp only [Work.Diff.T.dtKoszulForm, Pi.add_apply, Pi.sub_apply]

/-- **Little-o for a bilinear-form curve applied to a little-o direction and a bounded moving
point.**  If `Δ = o(t - t₀)` and, for every `w`, `t ↦ B t w (U t)` is continuous at `t₀`, then
`t ↦ B t (Δ t) (U t)` is `o(t - t₀)`. -/
theorem cv_bilin_curve_littleO
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {ι : Type*} [Fintype ι] (b : Module.Basis ι ℝ V)
    {B : ℝ → V →L[ℝ] V →L[ℝ] ℝ} {t₀ : ℝ} {Δ U : ℝ → V}
    (hΔ : IsLittleO (𝓝 t₀) Δ (fun t ↦ t - t₀))
    (hB : ∀ w : V, ContinuousAt (fun t ↦ B t w (U t)) t₀) :
    IsLittleO (𝓝 t₀) (fun t ↦ B t (Δ t) (U t)) (fun t ↦ t - t₀) := by
  classical
  have hfin : FiniteDimensional ℝ V := Module.Finite.of_basis b
  have hcoord : ∀ i : ι, IsLittleO (𝓝 t₀) (fun t ↦ b.repr (Δ t) i) (fun t ↦ t - t₀) := by
    intro i
    have h := (((b.coord i).toContinuousLinearMap).isBigO_comp Δ (𝓝 t₀)).trans_isLittleO hΔ
    simpa [Module.Basis.coord_apply] using h
  have hbdd : ∀ i : ι, IsBigO (𝓝 t₀) (fun t ↦ B t (b i) (U t)) (fun _ : ℝ ↦ (1 : ℝ)) := by
    intro i
    refine (isBigO_one_iff (F := ℝ)).mpr ?_
    have h := ((continuous_abs.tendsto _).comp (hB (b i))).isBoundedUnder_le
    simpa [Real.norm_eq_abs, Function.comp_def] using h
  have hterm : ∀ i : ι,
      IsLittleO (𝓝 t₀) (fun t ↦ b.repr (Δ t) i * (B t (b i) (U t))) (fun t ↦ t - t₀) := by
    intro i
    have h := (hcoord i).mul_isBigO (hbdd i)
    simpa [mul_one] using h
  have hsum : IsLittleO (𝓝 t₀)
      (fun t ↦ ∑ i, b.repr (Δ t) i * (B t (b i) (U t))) (fun t ↦ t - t₀) := by
    have h := IsLittleO.sum (s := Finset.univ)
      (A := fun i t ↦ b.repr (Δ t) i * (B t (b i) (U t))) (fun i _ ↦ hterm i)
    have heq : (∑ i, (fun t ↦ b.repr (Δ t) i * (B t (b i) (U t)))) =
        fun t ↦ ∑ i, b.repr (Δ t) i * (B t (b i) (U t)) := by
      funext t
      simp [Finset.sum_apply]
    rwa [heq] at h
  have hfun : (fun t ↦ B t (Δ t) (U t))
      = fun t ↦ ∑ i, b.repr (Δ t) i * (B t (b i) (U t)) := by
    funext t
    conv_lhs => rw [← b.sum_repr (Δ t)]
    simp only [map_sum, map_smul, sum_apply, smul_apply, smul_eq_mul]
  rw [hfun]
  exact hsum

/-- **Product rule for the metric family against two moving vectors.**  Here one single moving
vector is paired against the time-dependent metric with the other slot fixed, and the increment of
the second vector is split off. -/
theorem cv_metric_inner_moving_pair
    {G : ℝ → SMet I M} {J : Set ℝ} (hJopen : IsOpen J) (hJs : JointSmooth G J)
    {t₀ : ℝ} (ht₀ : t₀ ∈ J) {x : M}
    {F H : ℝ → TangentSpace I x} {A B : TangentSpace I x}
    (hF : HasDerivAt F A t₀) (hH : HasDerivAt H B t₀) :
    HasDerivAt (fun t : ℝ ↦ (G t).inner x (F t) (H t))
      (dtMet G t₀ x (F t₀) (H t₀) + (G t₀).inner x A (H t₀) + (G t₀).inner x (F t₀) B) t₀ := by
  letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨(G t₀).toRiemannianMetric⟩
  classical
  let η : ℝ → TangentSpace I x := fun t ↦ (H t - H t₀) - (t - t₀) • B
  have hη : IsLittleO (𝓝 t₀) η (fun t ↦ t - t₀) := hH.isLittleO
  -- the little-o increment
  have h3 : HasDerivAt (fun t : ℝ ↦ (G t).inner x (F t) (η t)) 0 t₀ := by
    have hsym : (fun t : ℝ ↦ (G t).inner x (F t) (η t))
        = fun t : ℝ ↦ (G t).inner x (η t) (F t) := by
      funext t
      exact (G t).symm x (F t) (η t)
    rw [hsym]
    have hBcont : ∀ w : TangentSpace I x, ContinuousAt (fun t ↦ (G t).inner x w (F t)) t₀ :=
      fun w ↦ by
        have h := (Work.Diff.T.hasDerivAt_metric_inner_moving (I := I) (M := M) hJopen hJs ht₀
          hF w).continuousAt
        have hsym2 : (fun t : ℝ ↦ (G t).inner x (F t) w)
            = fun t : ℝ ↦ (G t).inner x w (F t) := by
          funext t
          exact (G t).symm x (F t) w
        rwa [hsym2] at h
    have hlit := cv_bilin_curve_littleO (V := TangentSpace I x) (b := Module.finBasis ℝ E)
      (B := fun t : ℝ ↦ (G t).inner x) (Δ := η) (U := F) hη hBcont
    have hzero : (fun t : ℝ ↦ (G t).inner x (η t) (F t)) t₀ = 0 := by
      show (G t₀).inner x ((H t₀ - H t₀) - (t₀ - t₀) • B) (F t₀) = 0
      have h0 : (H t₀ - H t₀) - (t₀ - t₀) • B = (0 : TangentSpace I x) := by
        rw [sub_self, sub_self, zero_smul, sub_zero]
      rw [h0, map_zero]
      exact zero_apply _
    exact HasDerivAt.of_isLittleO (by simpa [hzero] using hlit)
  -- the fixed second slot
  have h1 : HasDerivAt (fun t : ℝ ↦ (G t).inner x (F t) (H t₀))
      (dtMet G t₀ x (F t₀) (H t₀) + (G t₀).inner x A (H t₀)) t₀ :=
    Work.Diff.T.hasDerivAt_metric_inner_moving (I := I) (M := M) hJopen hJs ht₀ hF (H t₀)
  -- the linear part in the increment
  have h2 : HasDerivAt (fun t : ℝ ↦ (t - t₀) * ((G t).inner x (F t) B))
      ((G t₀).inner x (F t₀) B) t₀ := by
    have hc := Work.Diff.T.hasDerivAt_metric_inner_moving (G := G) (J := J) hJopen hJs ht₀ hF B
    have h := ((hasDerivAt_id t₀).sub_const t₀).mul hc
    refine h.congr_deriv ?_
    simp only [id_eq]
    ring
  have hdecomp : (fun t : ℝ ↦ (G t).inner x (F t) (H t₀)
        + ((t - t₀) * ((G t).inner x (F t) B) + (G t).inner x (F t) (η t)))
      = fun t : ℝ ↦ (G t).inner x (F t) (H t) := by
    funext t
    have hsplit : H t = H t₀ + ((t - t₀) • B + η t) := by
      show H t = H t₀ + ((t - t₀) • B + ((H t - H t₀) - (t - t₀) • B))
      rw [add_comm ((t - t₀) • B) ((H t - H t₀) - (t - t₀) • B), sub_add_cancel,
        add_comm (H t₀) (H t - H t₀)]
      exact (sub_add_cancel (H t) (H t₀)).symm
    rw [hsplit, map_add, map_add, map_smul, smul_eq_mul]
  have hmain := h1.add (h2.add h3)
  refine hmain.congr_deriv ?_ |>.congr_of_eventuallyEq ?_
  · ring
  · exact Filter.Eventually.of_forall (fun t ↦ (congrFun hdecomp t).symm)

end Work.Diff.Evol
