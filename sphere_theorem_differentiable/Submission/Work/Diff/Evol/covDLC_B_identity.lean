
import Mathlib
import Submission.Work.Diff.Evol.Deps
import Submission.Work.Diff.Evol.RicPhi
import Submission.Work.Diff.Evol.covRic_eq_sum_covRm_fin
import Submission.Work.Diff.Evol.cv_dLC
import Submission.Work.Diff.GE.curv_var_prelim
import Submission.Work.Diff.GE.Kato3.CovRmKit
import Submission.Work.Diff.GE.covRic_eq_sum_covRm
import Submission.Commons.Geometry.Manifold.Riemannian.metricCompatible_scaleMetric

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The "second Bianchi" identity for the first variation of the Levi-Civita connection

`covDLC G t X Y Z x = (∇_X A)(Y,Z)(x)` is the covariant derivative of the first variation
`A = ∂ₜ∇` of the Levi-Civita connection along a family `G` of metrics.  This file proves

`⟨(∇_X A)(Y,Z) − (∇_Y A)(X,Z), W⟩
   = −(∇_X∇_Y Ric)(Z,W) − (∇_X∇_Z Ric)(Y,W) + (∇_X∇_W Ric)(Y,Z)`

whenever `∂ₜ G = −2 Ric(G)` (a Ricci flow), expressed in the workspace's pointwise objects:
the left-hand side is the target theorem `covDLC_B_identity` and the right-hand side is the
combination of `cov2Ric` (the `Ext` pattern of `∇²Ric`) appearing in its statement.

Structure of the proof (all helpers below are proved here):

* `Work.Diff.Evol.covDLC_B_dRicPhi_eq_sum_covRm_field`: the `Ext` pattern `dRicPhi` of `∇Ric` is the
  metric trace of `∇Rm` for *arbitrary* smooth fields in its two slots (compactness-free version of
  `Work.Diff.GE.dRicPhi_eq_sum_covRm`, using `covRic_onFrame_family` and the pointwise trace
  identity `ricAt_eq_sum_frame_ovf`);
* `dRicPhi_congr_val`: consequently `dRicPhi` depends only on the *values* of its field slots at the
  base point; `cov2Ric_eq_cov2RicExt` transfers this to `cov2Ric` (the pointwise presentation) and
  is what connects `cov2Ric` with the field-level `cov2RicExt`;
* `Work.Diff.Evol.covDLC_B_ricF_smooth`, `dRicPhi_smooth_field`: smoothness of `Ric` and of `dRicPhi`
  along smooth fields (needed to split derivatives);
* `Work.Diff.Evol.covDLC_B_dLC_pairing_ric`: `⟨∂ₜ∇_Y Z, W⟩
  = −((∇_Y Ric)(Z,W) + (∇_Z Ric)(Y,W) − (∇_W Ric)(Y,Z))` (Koszul's formula differentiated in `t`);
* `covDLC_pairing_eq_cov2RicExt`: the expansion of `⟨(∇_X A)(Y,Z), W⟩` in terms of three `cov2RicExt`
  patterns — the Leibniz corrections cancel;
* the target `covDLC_B_identity`: combine the two expansions (for `(X,Y,Z) = (a,b,d)` and
  `(b,a,d)`) with `cov2Ric_eq_cov2RicExt` and finish by linear arithmetic.
-/

namespace Work.Diff.Evol

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology
open Bundle ContDiff Set VectorField CovariantDerivative Metric

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1000000

section

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [I.Boundaryless] [T2Space M]


/-! ## Helper: `dRicPhi` is the trace of `∇Rm` for arbitrary fields (tensoriality of `∇Ric`)

The `Ext` pattern `dRicPhi` of `∇Ric` (`Submission/Work/Diff/Evol/RicPhi.lean`) depends only on the
*values* at the base point of its two field slots: it equals the metric trace of `∇Rm` in any
orthonormal frame.  This is the key ingredient that lets one convert between the pointwise
(`covRic`/`cov2Ric`) and field-level (`dRicPhi`/`cov2RicExt`) presentations. -/

/-- The `Ext` pattern `dRicPhi` of `∇Ric` is the metric trace of `∇Rm` for arbitrary smooth fields
`Y`, `Z` and any `g`-orthonormal frame `e` at `x` (compactness-free version of
`Work.Diff.GE.dRicPhi_eq_sum_covRm`). -/
theorem covDLC_B_dRicPhi_eq_sum_covRm_field (hLC : LCSmooth I M) (g : SMet I M) (x : M)
    (v : TangentSpace I x) (e : Fin (Module.finrank ℝ E) → TangentSpace I x)
    (he : IsONFrame g x e) (Y Z : Π y : M, TangentSpace I y)
    (hY : CMDiff ∞ (T% Y)) (hZ : CMDiff ∞ (T% Z)) :
    dRicPhi g x v Y Z
      = (Finset.univ : Finset (Fin (Module.finrank ℝ E))).sum
          (fun m => covRm g x v (e m) (Y x) (e m) (Z x)) := by
  classical
  have hVs : ∀ i : Work.Diff.GE.katoIdx E, CMDiff ∞ (T% (smoothExt x (e i))) :=
    fun i => Work.Diff.GE.smoothExt_cmdiff x (e i)
  have hVON : IsONFrame g x (fun i => smoothExt x (e i) x) := by
    have h : (fun i => smoothExt x (e i) x) = e := by
      funext i; exact Work.Diff.GE.smoothExt_apply x (e i)
    rw [h]; exact he
  obtain ⟨hWs0, hWON0, hWx0⟩ :=
    Work.Diff.GE.covRic_onFrame_family g x (fun i => smoothExt x (e i)) hVs hVON
  set W : Work.Diff.GE.katoIdx E → Π y : M, TangentSpace I y :=
    Work.Diff.GE.katoFrame g x (fun i => smoothExt x (e i)) with hWdef
  have hWs : ∀ i : Work.Diff.GE.katoIdx E, CMDiff ∞ (T% (W i)) := fun i => by
    rw [hWdef]; exact hWs0 i
  have hWON : ∀ᶠ y in 𝓝 x, IsONFrame g y (fun i => W i y) := by rw [hWdef]; exact hWON0
  have hWx : ∀ i : Work.Diff.GE.katoIdx E, W i x = e i := by
    intro i; rw [hWx0 i, Work.Diff.GE.smoothExt_apply]
  have hONx : IsONFrame g x (fun m => W m x) := hWON.self_of_nhds
  have hsm : ∀ m : Work.Diff.GE.katoIdx E,
      CMDiff ∞ (fun y : M => rmP g y (W m y) (Y y) (W m y) (Z y)) :=
    fun m => Work.Diff.GE.rmP_fields_smooth hLC g (hWs m) hY (hWs m) hZ
  have hagree : (ricF g Y Z)
      =ᶠ[𝓝 x] (fun y : M => ∑ m, rmP g y (W m y) (Y y) (W m y) (Z y)) := by
    filter_upwards [hWON] with y hy
    simpa only [ricF] using
      ricAt_eq_sum_frame_ovf (I := I) (M := M) hLC g y (fun m => W m y) hy (Y y) (Z y)
  have hkey : mvfderiv I (ricF g Y Z) x v
      = ∑ m, mvfderiv I (fun y : M => rmP g y (W m y) (Y y) (W m y) (Z y)) x v := by
    have h := Work.Diff.GE.mvfderiv_congr_eventuallyEq (I := I) hagree
    exact (congrArg (fun L : TangentSpace I x →L[ℝ] ℝ => L v) h).trans
      (Work.Diff.GE.Kato3.mvfderiv_sum Finset.univ _ hsm x v)
  have hric : mvfderiv I (ricF g Y Z) x v
      = dRicPhi g x v Y Z + ricAt (lcOf g) x (lcOf g Y x v) (Z x)
        + ricAt (lcOf g) x (Y x) (lcOf g Z x v) :=
    mvfderiv_ricF_eq g x v Y Z
  have hdRm : ∀ m : Work.Diff.GE.katoIdx E,
      Work.Diff.GE.dRmPhi g x v (W m) Y (W m) Z
        = mvfderiv I (fun y : M => rmP g y (W m y) (Y y) (W m y) (Z y)) x v
          - rmP g x (lcOf g (W m) x v) (Y x) (W m x) (Z x)
          - rmP g x (W m x) (lcOf g Y x v) (W m x) (Z x)
          - rmP g x (W m x) (Y x) (lcOf g (W m) x v) (Z x)
          - rmP g x (W m x) (Y x) (W m x) (lcOf g Z x v) := by
    intro m
    simp only [Work.Diff.GE.dRmPhi]
  have h1 : (∑ m : Work.Diff.GE.katoIdx E, Work.Diff.GE.dRmPhi g x v (W m) Y (W m) Z)
      + (∑ m, rmP g x (lcOf g (W m) x v) (Y x) (W m x) (Z x))
      + (∑ m, rmP g x (W m x) (lcOf g Y x v) (W m x) (Z x))
      + (∑ m, rmP g x (W m x) (Y x) (lcOf g (W m) x v) (Z x))
      + (∑ m, rmP g x (W m x) (Y x) (W m x) (lcOf g Z x v))
      = ∑ m, mvfderiv I (fun y : M => rmP g y (W m y) (Y y) (W m y) (Z y)) x v := by
    simp only [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [hdRm m]
    ring
  have hPR : (∑ m : Work.Diff.GE.katoIdx E,
        rmP g x (lcOf g (W m) x v) (Y x) (W m x) (Z x))
      + (∑ m, rmP g x (W m x) (Y x) (lcOf g (W m) x v) (Z x)) = 0 :=
    Work.Diff.GE.covRic_frame_correction_zero hLC g x v W hWs hWON (Y x) (Z x)
  have hQr : (∑ m : Work.Diff.GE.katoIdx E,
        rmP g x (W m x) (lcOf g Y x v) (W m x) (Z x))
      = ricAt (lcOf g) x (lcOf g Y x v) (Z x) :=
    (ricAt_eq_sum_frame_ovf (I := I) (M := M) hLC g x (fun m => W m x) hONx
      (lcOf g Y x v) (Z x)).symm
  have hYr : (∑ m : Work.Diff.GE.katoIdx E,
        rmP g x (W m x) (Y x) (W m x) (lcOf g Z x v))
      = ricAt (lcOf g) x (Y x) (lcOf g Z x v) :=
    (ricAt_eq_sum_frame_ovf (I := I) (M := M) hLC g x (fun m => W m x) hONx
      (Y x) (lcOf g Z x v)).symm
  have h2 : (∑ m : Work.Diff.GE.katoIdx E,
        mvfderiv I (fun y : M => rmP g y (W m y) (Y y) (W m y) (Z y)) x v)
      = dRicPhi g x v Y Z
        + ricAt (lcOf g) x (lcOf g Y x v) (Z x)
        + ricAt (lcOf g) x (Y x) (lcOf g Z x v) := by
    rw [← hkey, hric]
  have hmain : dRicPhi g x v Y Z
      = ∑ m : Work.Diff.GE.katoIdx E, Work.Diff.GE.dRmPhi g x v (W m) Y (W m) Z := by
    linarith [h1, h2, hPR, hQr, hYr]
  have hper : ∀ m : Work.Diff.GE.katoIdx E,
      Work.Diff.GE.dRmPhi g x v (W m) Y (W m) Z
        = covRm g x v (e m) (Y x) (e m) (Z x) := by
    intro m
    have h := Work.Diff.GE.Kato3.covRm_field_form (X₁ := W m) (X₂ := Y) (X₃ := W m) (X₄ := Z)
      hLC g x v (hWs m) hY (hWs m) hZ
    rw [hWx m] at h
    exact h.symm
  rw [hmain]
  exact Finset.sum_congr rfl (fun m _ => hper m)


/-- **`dRicPhi` depends only on the values of its two field slots at the base point.** -/
theorem dRicPhi_congr_val (hLC : LCSmooth I M) (g : SMet I M) (x : M) (v : TangentSpace I x)
    {A A₁ B B₁ : Π y : M, TangentSpace I y}
    (hA : CMDiff ∞ (T% A)) (hA₁ : CMDiff ∞ (T% A₁))
    (hB : CMDiff ∞ (T% B)) (hB₁ : CMDiff ∞ (T% B₁))
    (hAx : A x = A₁ x) (hBx : B x = B₁ x) :
    dRicPhi g x v A B = dRicPhi g x v A₁ B₁ := by
  rw [covDLC_B_dRicPhi_eq_sum_covRm_field hLC g x v (onFrame g x)
        (Work.Diff.GE.isONFrame_onFrame g x) A B hA hB,
      covDLC_B_dRicPhi_eq_sum_covRm_field hLC g x v (onFrame g x)
        (Work.Diff.GE.isONFrame_onFrame g x) A₁ B₁ hA₁ hB₁,
      hAx, hBx]

/-- **`cov2Ric` in the field-level (`Ext`) presentation**: the pointwise second covariant derivative
of the Ricci tensor on the chosen smooth extensions is the `Ext` pattern `cov2RicExt` on the same
extensions. -/
theorem cov2Ric_eq_cov2RicExt (hLC : LCSmooth I M) (g : SMet I M) (x : M)
    (v w a b : TangentSpace I x) :
    cov2Ric g x v w a b
      = cov2RicExt g x v (smoothExt x v) (smoothExt x w) (smoothExt x a) (smoothExt x b) := by
  have hAs : CMDiff ∞ (T% (smoothExt x a)) := Work.Diff.GE.smoothExt_cmdiff x a
  have hBs : CMDiff ∞ (T% (smoothExt x b)) := Work.Diff.GE.smoothExt_cmdiff x b
  have hVs : CMDiff ∞ (T% (smoothExt x v)) := Work.Diff.GE.smoothExt_cmdiff x v
  -- the integrand
  have hfun : (fun y : M ↦ covRic g y (smoothExt x w y) (smoothExt x a y) (smoothExt x b y))
      = fun y : M ↦ dRicPhi g y (smoothExt x w y) (smoothExt x a) (smoothExt x b) := by
    funext y
    rw [covRic_eq_dRicPhi]
    exact dRicPhi_congr_val hLC g y (smoothExt x w y)
      (Work.Diff.GE.smoothExt_cmdiff y (smoothExt x a y)) hAs
      (Work.Diff.GE.smoothExt_cmdiff y (smoothExt x b y)) hBs
      (Work.Diff.GE.smoothExt_apply y (smoothExt x a y))
      (Work.Diff.GE.smoothExt_apply y (smoothExt x b y))
  -- the three corrections
  have hc1 : covRic g x (lcOf g (smoothExt x w) x v) a b
      = dRicPhi g x (lcOf g (smoothExt x w) x v) (smoothExt x a) (smoothExt x b) :=
    covRic_eq_dRicPhi g x _ a b
  have hc2 : covRic g x w (lcOf g (smoothExt x a) x v) b
      = dRicPhi g x (smoothExt x w x)
          (fun y : M ↦ lcOf g (smoothExt x a) y (smoothExt x v y)) (smoothExt x b) := by
    have h1 : CMDiff ∞ (T% (fun y : M ↦ lcOf g (smoothExt x a) y (smoothExt x v y))) :=
      cv_lcOf_arg_smooth hLC g hVs hAs
    have h2 : CMDiff ∞ (T% (smoothExt x (lcOf g (smoothExt x a) x v))) :=
      Work.Diff.GE.smoothExt_cmdiff x _
    have hcongr := dRicPhi_congr_val hLC g x w h2 h1 hBs hBs
      (by simp only [Work.Diff.GE.smoothExt_apply]) rfl
    rw [covRic_eq_dRicPhi]
    simpa only [Work.Diff.GE.smoothExt_apply] using hcongr
  have hc3 : covRic g x w a (lcOf g (smoothExt x b) x v)
      = dRicPhi g x (smoothExt x w x) (smoothExt x a)
          (fun y : M ↦ lcOf g (smoothExt x b) y (smoothExt x v y)) := by
    have h1 : CMDiff ∞ (T% (fun y : M ↦ lcOf g (smoothExt x b) y (smoothExt x v y))) :=
      cv_lcOf_arg_smooth hLC g hVs hBs
    have h2 : CMDiff ∞ (T% (smoothExt x (lcOf g (smoothExt x b) x v))) :=
      Work.Diff.GE.smoothExt_cmdiff x _
    have hcongr := dRicPhi_congr_val hLC g x w hAs hAs h2 h1 rfl
      (by simp only [Work.Diff.GE.smoothExt_apply])
    rw [covRic_eq_dRicPhi]
    simpa only [Work.Diff.GE.smoothExt_apply] using hcongr
  simp only [cov2Ric, cov2RicExt]
  rw [hfun, hc1, hc2, hc3]


/-! ## Helper: the pairing of `dLC` with the Ricci tensor

`∂ₜ ∇_Y Z`, paired with a smooth field `W`, is minus the first covariant derivative of `Ric`:
`⟨∂ₜ∇_Y Z, W⟩ = -((∇_Y Ric)(Z,W) + (∇_Z Ric)(Y,W) - (∇_W Ric)(Y,Z))`
whenever `∂ₜ G = -2 Ric(G)`.  This is `dLC_pairing` (Koszul) combined with the algebraic identity
`variation_algebra` behind the first-variation contract. -/

/-- `covDerivSym2` is linear in the bilinear form `h`. -/
theorem covDerivSym2_const_mul'
    (cov : CovariantDerivative I E (TangentSpace I (M := M))) (c : ℝ)
    (h : Π y : M, TangentSpace I y → TangentSpace I y → ℝ)
    (X Y Z : Π y : M, TangentSpace I y) (x : M) :
    covDerivSym2 cov (fun y a b ↦ c * h y a b) X Y Z x
      = c * covDerivSym2 cov h X Y Z x := by
  have hfun : (fun y : M ↦ c * h y (Y y) (Z y))
      = (fun y : M ↦ c • (fun y' : M ↦ h y' (Y y') (Z y')) y) := by
    funext y
    rw [smul_eq_mul]
  rw [covDerivSym2, covDerivSym2, hfun,
    Commons.Geometry.Manifold.Riemannian.mvfderiv_const_smul]
  simp only [smul_apply, smul_eq_mul]
  ring

/-- `covDerivSym2` with the Ricci tensor in the role of `h` is the `Ext` pattern `dRicPhi` of `∇Ric`. -/
theorem covDerivSym2_ricAt_eq_dRicPhi' (g : SMet I M) (x : M)
    (X Y Z : Π y : M, TangentSpace I y) :
    covDerivSym2 (lcOf g) (fun y a b ↦ ricAt (lcOf g) y a b) X Y Z x
      = dRicPhi g x (X x) Y Z := by
  rw [covDerivSym2, dRicPhi]
  rfl

/-- **The pairing of the first variation of the connection with `Ric`.** -/
theorem covDLC_B_dLC_pairing_ric
    (hLV : LCVariation I M) {G : ℝ → SMet I M} {J : Set ℝ} (hJopen : IsOpen J)
    (hJs : JointSmooth G J) {t₀ : ℝ} (ht₀ : t₀ ∈ J)
    (hdt : ∀ (y : M) (u v : TangentSpace I y),
      dtMet G t₀ y u v = -2 * ricAt (lcOf (G t₀)) y u v)
    (Y Z W : Π y : M, TangentSpace I y) (hY : CMDiff ∞ (T% Y)) (hZ : CMDiff ∞ (T% Z))
    (hW : CMDiff ∞ (T% W)) (x : M) :
    (G t₀).inner x (dLC G t₀ Y Z x) (W x)
      = -(dRicPhi (G t₀) x (Y x) Z W + dRicPhi (G t₀) x (Z x) Y W
          - dRicPhi (G t₀) x (W x) Y Z) := by
  have hdp := Work.Diff.GE.dLC_pairing (I := I) (M := M) hLV hJopen hJs ht₀ hY hZ hW x
  have hva := Work.Diff.T.variation_algebra (I := I) (M := M) (x := x) hJopen hJs ht₀
    Y Z W hY hZ hW
  have hcongr : ∀ (A B C : Π y : M, TangentSpace I y), CMDiff ∞ (T% A) → CMDiff ∞ (T% B) →
      CMDiff ∞ (T% C) →
      covDerivSym2 (lcOf (G t₀)) (dtMet G t₀) A B C x
        = -2 * dRicPhi (G t₀) x (A x) B C := by
    intro A B C hA hB hC
    have hfun : dtMet G t₀ = fun y a b ↦ (-2 : ℝ) * ricAt (lcOf (G t₀)) y a b := by
      funext y a b
      exact hdt y a b
    rw [hfun, covDerivSym2_const_mul', covDerivSym2_ricAt_eq_dRicPhi']
  rw [hcongr Y Z W hY hZ hW, hcongr Z Y W hZ hY hW, hcongr W Y Z hW hY hZ] at hva
  linarith [hdp, hva]


/-! ## Helper: smoothness of `Ric` and of the `Ext` pattern `dRicPhi` -/

/-- The Ricci tensor of a smooth metric, evaluated on two smooth fields, is smooth. -/
theorem covDLC_B_ricF_smooth (hLC : LCSmooth I M) (g : SMet I M) (V Z : Π y : M, TangentSpace I y)
    (hV : CMDiff ∞ (T% V)) (hZ : CMDiff ∞ (T% Z)) :
    CMDiff ∞ (ricF g V Z) := by
  intro y
  have hVs : ∀ i : Work.Diff.GE.katoIdx E, CMDiff ∞ (T% (smoothExt y (onFrame g y i))) :=
    fun i => Work.Diff.GE.smoothExt_cmdiff y (onFrame g y i)
  have hVON : IsONFrame g y (fun i => smoothExt y (onFrame g y i) y) := by
    have h : (fun i => smoothExt y (onFrame g y i) y) = onFrame g y := by
      funext i; exact Work.Diff.GE.smoothExt_apply y (onFrame g y i)
    rw [h]; exact Work.Diff.GE.isONFrame_onFrame g y
  obtain ⟨hWs0, hWON0, -⟩ :=
    Work.Diff.GE.covRic_onFrame_family g y (fun i => smoothExt y (onFrame g y i)) hVs hVON
  set W : Work.Diff.GE.katoIdx E → Π z : M, TangentSpace I z :=
    Work.Diff.GE.katoFrame g y (fun i => smoothExt y (onFrame g y i)) with hWdef
  have hWs : ∀ i : Work.Diff.GE.katoIdx E, CMDiff ∞ (T% (W i)) := fun i => by
    rw [hWdef]; exact hWs0 i
  have hWON : ∀ᶠ z in 𝓝 y, IsONFrame g z (fun i => W i z) := by rw [hWdef]; exact hWON0
  have hsum : CMDiff ∞ (fun z : M ↦ ∑ m : Work.Diff.GE.katoIdx E,
      rmP g z (W m z) (V z) (W m z) (Z z)) := by
    apply ContMDiff.sum
    intro m _
    exact Work.Diff.GE.rmP_fields_smooth hLC g (hWs m) hV (hWs m) hZ
  have hagree : (fun z : M ↦ ∑ m : Work.Diff.GE.katoIdx E,
      rmP g z (W m z) (V z) (W m z) (Z z)) =ᶠ[𝓝 y] ricF g V Z := by
    filter_upwards [hWON] with z hz
    exact (ricAt_eq_sum_frame_ovf (I := I) (M := M) hLC g z (fun m => W m z) hz
      (V z) (Z z)).symm
  exact (hsum y).congr_of_eventuallyEq hagree.symm

/-- The `Ext` pattern `dRicPhi` of `∇Ric`, as a function of the base point, is smooth when its
direction and its two field slots are smooth. -/
theorem dRicPhi_smooth_field (hLC : LCSmooth I M) (g : SMet I M)
    (A B D : Π y : M, TangentSpace I y) (hA : CMDiff ∞ (T% A)) (hB : CMDiff ∞ (T% B))
    (hD : CMDiff ∞ (T% D)) :
    CMDiff ∞ (fun y : M ↦ dRicPhi g y (D y) A B) := by
  have hric : CMDiff ∞ (ricF g A B) := covDLC_B_ricF_smooth hLC g A B hA hB
  have hDA : CMDiff ∞ (T% (fun y : M ↦ lcOf g A y (D y))) := cv_lcOf_arg_smooth hLC g hD hA
  have hDB : CMDiff ∞ (T% (fun y : M ↦ lcOf g B y (D y))) := cv_lcOf_arg_smooth hLC g hD hB
  have h1 : CMDiff ∞ (fun y : M ↦ mvfderiv I (ricF g A B) y (D y)) :=
    Commons.Geometry.Manifold.VectorField.mvfderiv_apply_contMDiff hric hD
  have h2 : CMDiff ∞ (ricF g (fun y : M ↦ lcOf g A y (D y)) B) :=
    covDLC_B_ricF_smooth hLC g _ B hDA hB
  have h3 : CMDiff ∞ (ricF g A (fun y : M ↦ lcOf g B y (D y))) :=
    covDLC_B_ricF_smooth hLC g A _ hA hDB
  have hfun : (fun y : M ↦ dRicPhi g y (D y) A B)
      = fun y : M ↦ mvfderiv I (ricF g A B) y (D y)
          - ricF g (fun y : M ↦ lcOf g A y (D y)) B y
          - ricF g A (fun y : M ↦ lcOf g B y (D y)) y := by
    funext y
    simp only [dRicPhi, ricF]
  rw [hfun]
  exact (h1.sub h2).sub h3

/-- `mvfderiv` of `-(f + g - h)`. -/
theorem mvfderiv_neg_sum_sub (f g h : M → ℝ) (hf : CMDiff ∞ f) (hg : CMDiff ∞ g)
    (hh : CMDiff ∞ h) (x : M) (v : TangentSpace I x) :
    mvfderiv I (fun y : M ↦ -(f y + g y - h y)) x v
      = -(mvfderiv I f x v + mvfderiv I g x v - mvfderiv I h x v) := by
  have hf' : MDiffAt f x := hf.mdifferentiableAt (by simp)
  have hg' : MDiffAt g x := hg.mdifferentiableAt (by simp)
  have hh' : MDiffAt h x := hh.mdifferentiableAt (by simp)
  have hfg' : MDiffAt (fun y : M ↦ f y + g y) x := (hf.add hg).mdifferentiableAt (by simp)
  have e1 : mvfderiv I (fun y : M ↦ -(f y + g y - h y)) x v
      = - mvfderiv I (fun y : M ↦ f y + g y - h y) x v := by
    show mvfderiv I (-(fun y : M ↦ f y + g y - h y)) x v = _
    exact congrArg (fun L : TangentSpace I x →L[ℝ] ℝ => L v)
      (mvfderiv_neg (I := I) (g := fun y : M ↦ f y + g y - h y) (x := x))
  have e2 : mvfderiv I (fun y : M ↦ f y + g y - h y) x v
      = mvfderiv I (fun y : M ↦ f y + g y) x v - mvfderiv I h x v := by
    show mvfderiv I ((fun y : M ↦ f y + g y) - h) x v = _
    exact congrArg (fun L : TangentSpace I x →L[ℝ] ℝ => L v) (mvfderiv_sub hfg' hh')
  have e3 : mvfderiv I (fun y : M ↦ f y + g y) x v
      = mvfderiv I f x v + mvfderiv I g x v := by
    show mvfderiv I (f + g) x v = _
    exact congrArg (fun L : TangentSpace I x →L[ℝ] ℝ => L v) (mvfderiv_add hf' hg')
  rw [e1, e2, e3]


/-! ## The covariant derivative of the pairing `⟨dLC(Y,Z), W⟩`

This is the heart of the computation: expanding `covDLC` (the covariant derivative of the first
variation of the connection, written with the metric pairing), using the pointwise formula
`⟨dLC(Y,Z), W⟩ = -((∇_Y Ric)(Z,W) + (∇_Z Ric)(Y,W) - (∇_W Ric)(Y,Z))` of `covDLC_B_dLC_pairing_ric`, one
obtains `-(∇_X∇_Y Ric)(Z,W) - (∇_X∇_Z Ric)(Y,W) + (∇_X∇_W Ric)(Y,Z)`; the nine Leibniz corrections
cancel exactly, leaving the three `Ext` patterns `cov2RicExt`. -/

/-- The covariant derivative of the pairing of the first variation of the connection with a smooth
field, in terms of the `Ext` patterns `cov2RicExt` of `∇²Ric`. -/
theorem covDLC_pairing_eq_cov2RicExt
    (hLC : LCSmooth I M) (hLV : LCVariation I M) {G : ℝ → SMet I M} {J : Set ℝ}
    (hJopen : IsOpen J) (hJs : JointSmooth G J) {t₀ : ℝ} (ht₀ : t₀ ∈ J)
    (hdt : ∀ (y : M) (u v : TangentSpace I y),
      dtMet G t₀ y u v = -2 * ricAt (lcOf (G t₀)) y u v)
    (X Y Z W : Π y : M, TangentSpace I y) (hX : CMDiff ∞ (T% X)) (hY : CMDiff ∞ (T% Y))
    (hZ : CMDiff ∞ (T% Z)) (hW : CMDiff ∞ (T% W)) (x : M) :
    (G t₀).inner x (covDLC G t₀ X Y Z x) (W x)
      = -((cov2RicExt (G t₀) x (X x) X Y Z W) + (cov2RicExt (G t₀) x (X x) X Z Y W)
          - (cov2RicExt (G t₀) x (X x) X W Y Z)) := by
  have hDLC : CMDiff ∞ (T% (fun y : M ↦ dLC G t₀ Y Z y)) :=
    fun y => cv_dLC_smooth (I := I) (M := M) hLC hLV hJopen hJs ht₀ Y Z hY hZ y
  have hYX : CMDiff ∞ (T% (fun y : M ↦ lcOf (G t₀) Y y (X y))) :=
    cv_lcOf_arg_smooth (I := I) (M := M) hLC (G t₀) hX hY
  have hZX : CMDiff ∞ (T% (fun y : M ↦ lcOf (G t₀) Z y (X y))) :=
    cv_lcOf_arg_smooth (I := I) (M := M) hLC (G t₀) hX hZ
  have hWX : CMDiff ∞ (T% (fun y : M ↦ lcOf (G t₀) W y (X y))) :=
    cv_lcOf_arg_smooth (I := I) (M := M) hLC (G t₀) hX hW
  have hf1 : CMDiff ∞ (fun y : M ↦ dRicPhi (G t₀) y (Y y) Z W) :=
    dRicPhi_smooth_field (I := I) (M := M) hLC (G t₀) Z W Y hZ hW hY
  have hf2 : CMDiff ∞ (fun y : M ↦ dRicPhi (G t₀) y (Z y) Y W) :=
    dRicPhi_smooth_field (I := I) (M := M) hLC (G t₀) Y W Z hY hW hZ
  have hf3 : CMDiff ∞ (fun y : M ↦ dRicPhi (G t₀) y (W y) Y Z) :=
    dRicPhi_smooth_field (I := I) (M := M) hLC (G t₀) Y Z W hY hZ hW
  -- the pointwise formula for the pairing
  have hpt : ∀ y : M, (G t₀).inner y (dLC G t₀ Y Z y) (W y)
      = -(dRicPhi (G t₀) y (Y y) Z W + dRicPhi (G t₀) y (Z y) Y W
          - dRicPhi (G t₀) y (W y) Y Z) :=
    fun y => covDLC_B_dLC_pairing_ric (I := I) (M := M) hLV hJopen hJs ht₀ hdt Y Z W hY hZ hW y
  -- metric compatibility: the derivative of the pairing
  have hpair : (G t₀).inner x (lcOf (G t₀) (fun y : M ↦ dLC G t₀ Y Z y) x (X x)) (W x)
      = mvfderiv I (fun y : M ↦ (G t₀).inner y (dLC G t₀ Y Z y) (W y)) x (X x)
        - (G t₀).inner x (dLC G t₀ Y Z x) (lcOf (G t₀) W x (X x)) :=
    Work.Diff.GE.lcOf_metric_pairing (I := I) (M := M) hLC (G t₀) hX hDLC hW x
  -- the derivative of the pairing, via the pointwise formula
  have hderiv : mvfderiv I (fun y : M ↦ (G t₀).inner y (dLC G t₀ Y Z y) (W y)) x (X x)
      = -(mvfderiv I (fun y : M ↦ dRicPhi (G t₀) y (Y y) Z W) x (X x)
          + mvfderiv I (fun y : M ↦ dRicPhi (G t₀) y (Z y) Y W) x (X x)
          - mvfderiv I (fun y : M ↦ dRicPhi (G t₀) y (W y) Y Z) x (X x)) := by
    have hfun : (fun y : M ↦ (G t₀).inner y (dLC G t₀ Y Z y) (W y))
        = fun y : M ↦ -(dRicPhi (G t₀) y (Y y) Z W + dRicPhi (G t₀) y (Z y) Y W
            - dRicPhi (G t₀) y (W y) Y Z) := funext hpt
    rw [hfun]
    exact mvfderiv_neg_sum_sub (I := I) (M := M)
      (f := fun y : M ↦ dRicPhi (G t₀) y (Y y) Z W)
      (g := fun y : M ↦ dRicPhi (G t₀) y (Z y) Y W)
      (h := fun y : M ↦ dRicPhi (G t₀) y (W y) Y Z) hf1 hf2 hf3 x (X x)
  -- the three pairing corrections
  have hc1 := covDLC_B_dLC_pairing_ric (I := I) (M := M) hLV hJopen hJs ht₀ hdt
    (fun y : M ↦ lcOf (G t₀) Y y (X y)) Z W hYX hZ hW x
  have hc2 := covDLC_B_dLC_pairing_ric (I := I) (M := M) hLV hJopen hJs ht₀ hdt
    Y (fun y : M ↦ lcOf (G t₀) Z y (X y)) W hY hZX hW x
  have hc3 := covDLC_B_dLC_pairing_ric (I := I) (M := M) hLV hJopen hJs ht₀ hdt
    Y Z (fun y : M ↦ lcOf (G t₀) W y (X y)) hY hZ hWX x
  -- expand `covDLC` and distribute the subtraction
  have hexp : (G t₀).inner x (covDLC G t₀ X Y Z x) (W x)
      = (G t₀).inner x (lcOf (G t₀) (fun y : M ↦ dLC G t₀ Y Z y) x (X x)) (W x)
        - (G t₀).inner x (dLC G t₀ (fun y : M ↦ lcOf (G t₀) Y y (X y)) Z x) (W x)
        - (G t₀).inner x (dLC G t₀ Y (fun y : M ↦ lcOf (G t₀) Z y (X y)) x) (W x) := by
    rw [covDLC]
    simp only [map_sub, sub_apply]
  rw [hexp, hpair, hderiv, hc1, hc2, hc3]
  simp only [cov2RicExt]
  ring

end

theorem covDLC_B_identity
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [I.Boundaryless] [T2Space M]
    (hLC : LCSmooth I M) (hLV : LCVariation I M)
    (G : ℝ → SMet I M) (T : ℝ) (hflow : IsRicciFlow G T) {t : ℝ} (ht : t ∈ Ioo 0 T)
    (x : M) (a b c d : TangentSpace I x) :
    (G t).inner x (covDLC G t (smoothExt x a) (smoothExt x b) (smoothExt x d) x
        - covDLC G t (smoothExt x b) (smoothExt x a) (smoothExt x d) x) c
      = -cov2Ric (G t) x a b d c - cov2Ric (G t) x a d b c + cov2Ric (G t) x a c b d
        + cov2Ric (G t) x b a d c + cov2Ric (G t) x b d a c - cov2Ric (G t) x b c a d := by
  have hmem : t ∈ Set.Ico (0 : ℝ) T := ⟨le_of_lt ht.1, ht.2⟩
  have hnb : Set.Ico (0 : ℝ) T ∈ 𝓝 t :=
    Filter.mem_of_superset (isOpen_Ioo.mem_nhds ht) Set.Ioo_subset_Ico_self
  have hdt : ∀ (y : M) (u v : TangentSpace I y),
      dtMet G t y u v = -2 * ricAt (lcOf (G t)) y u v := by
    intro y u v
    have hd : HasDerivAt (fun s : ℝ ↦ (G s).inner y u v)
        (-2 * ricAt (lcOf (G t)) y u v) t :=
      (hflow.2 t hmem y u v).hasDerivAt hnb
    rw [dtMet, hd.deriv]
  have hJopen : IsOpen (Set.Ioo (0 : ℝ) T) := isOpen_Ioo
  have hJs : JointSmooth G (Set.Ioo (0 : ℝ) T) :=
    hflow.1.mono (Set.prod_mono Set.Ioo_subset_Ico_self (Subset.refl _))
  have h1 := covDLC_pairing_eq_cov2RicExt (I := I) (M := M) hLC hLV hJopen hJs ht hdt
    (smoothExt x a) (smoothExt x b) (smoothExt x d) (smoothExt x c)
    (Work.Diff.GE.smoothExt_cmdiff x a) (Work.Diff.GE.smoothExt_cmdiff x b)
    (Work.Diff.GE.smoothExt_cmdiff x d) (Work.Diff.GE.smoothExt_cmdiff x c) x
  have h2 := covDLC_pairing_eq_cov2RicExt (I := I) (M := M) hLC hLV hJopen hJs ht hdt
    (smoothExt x b) (smoothExt x a) (smoothExt x d) (smoothExt x c)
    (Work.Diff.GE.smoothExt_cmdiff x b) (Work.Diff.GE.smoothExt_cmdiff x a)
    (Work.Diff.GE.smoothExt_cmdiff x d) (Work.Diff.GE.smoothExt_cmdiff x c) x
  have key : (G t).inner x (covDLC G t (smoothExt x a) (smoothExt x b) (smoothExt x d) x
        - covDLC G t (smoothExt x b) (smoothExt x a) (smoothExt x d) x) (smoothExt x c x)
      = -cov2Ric (G t) x a b d c - cov2Ric (G t) x a d b c + cov2Ric (G t) x a c b d
        + cov2Ric (G t) x b a d c + cov2Ric (G t) x b d a c - cov2Ric (G t) x b c a d := by
    simp only [map_sub, sub_apply]
    rw [h1, h2]
    simp only [Work.Diff.GE.smoothExt_apply]
    rw [← cov2Ric_eq_cov2RicExt (I := I) (M := M) hLC (G t) x a b d c,
      ← cov2Ric_eq_cov2RicExt (I := I) (M := M) hLC (G t) x a d b c,
      ← cov2Ric_eq_cov2RicExt (I := I) (M := M) hLC (G t) x a c b d,
      ← cov2Ric_eq_cov2RicExt (I := I) (M := M) hLC (G t) x b a d c,
      ← cov2Ric_eq_cov2RicExt (I := I) (M := M) hLC (G t) x b d a c,
      ← cov2Ric_eq_cov2RicExt (I := I) (M := M) hLC (G t) x b c a d]
    ring
  simpa only [Work.Diff.GE.smoothExt_apply] using key

end Work.Diff.Evol
