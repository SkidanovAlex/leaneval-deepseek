import Mathlib
import Submission.Diff.Evol
import Submission.Work.Diff.Evol.Vocab
import Submission.Work.Diff.Evol.lcOf_transition_second
import Submission.Work.Diff.Evol.lcOf_second_congr_value
import Submission.Work.Diff.Evol.FrameExp
import Submission.Work.Diff.Evol.FrameData
import Submission.Work.Diff.Evol.smooth_skew_jet1
import Submission.Work.Diff.Evol.smooth_skew_jet2
import Submission.Work.Diff.Evol.exp_chain_rule
import Submission.Work.Diff.Evol.transHess_skew
import Submission.Work.Diff.Evol.transHess_bilinear
import Submission.Work.Diff.GE.exists_ON_frame_field_eq
import Submission.Work.Diff.GE.curvbasic
import Submission.Work.Diff.GE.kato_mvfderiv_inner_lc
import Submission.Work.EXT.sum_inner_smul_eq_self_of_isONFrame
import Submission.Work.Diff.Evol.frame_exists_first

set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# A frame field parallel to first and second order at `x`, by explicit matrix corrections

This module proves `Work.Diff.Evol.frame_exists` (a smooth frame field on `M`, orthonormal near
`x`, taking the prescribed values `e i` at `x`, and *parallel at `x` to first and second order*) by
an explicit two-step matrix correction rather than by parallel transport.

The construction (no orthogonality, no exponential map and no skewness is needed):

* `F` — any globally smooth frame field with `F i x = e i` (`Work.Diff.GE.exists_ON_frame_field_eq`);
* `Ω v p i = ⟪∇_v (F i), e p⟫` — the connection form at `x`; `mat_jet1` produces a smooth matrix
  function `A₁` with `A₁ x = 1` and `dA₁ x = -Ω`, and `Ef₁ i = ∑ p (A₁) p i • F p` then has
  `Ef₁ i x = e i` and `∇_v Ef₁ i = 0` for every `v`;
* the bilinear form `Ψ(v,w) p i = -⟪∇_{V_v}∇_{V_w} Ef₁ i, e p⟫` (`V v` a *linear* family of smooth
  fields with `V v x = v`, built from a basis and `smoothExt`), realised by `mat_jet2` as the second
  derivative at `x` of a smooth matrix function `C` with `C x = 1`, `dC x = 0`; then
  `Ef₂ i = ∑ p C p i • Ef₁ p` has `Ef₂ i x = e i`, `∇_v Ef₂ i = 0` and `∇_W∇_W Ef₂ i = 0` for
  every smooth `W`: the second-order Leibniz rule `lcOf_transition_second` turns the second
  covariant derivative of the sum into `∑ p [Ψ(v,v) p i • e p + δ_pi • ∇_W∇_W Ef₁ p]`, and the two
  terms cancel because `∇_W∇_W Ef₁ i` is tensorial in `W` (`lcOf_second_congr_value`: it depends
  only on `W x`) and `e` is orthonormal at `x`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology BigOperators Matrix Matrix.Norms.Operator
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter

namespace Work.Diff.Evol

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I (((⊤ : ℕ∞) : WithTop ℕ∞)) M] [I.Boundaryless] [T2Space M] [CompactSpace M]

/-! ## 1. A linear family of globally smooth fields with prescribed value at `x` -/

/-- The linear family of globally smooth fields `V v` with `V v x = v`: expand `v` in the standard
basis, and extend each basis vector to a globally smooth field. -/
noncomputable def linFieldFamily (x : M) (v : TangentSpace I x) : Π y : M, TangentSpace I y :=
  fun y => ∑ k : Fin (Module.finrank ℝ E),
    ((Module.finBasis ℝ E).coord k v)
      • (smoothExt (I := I) (M := M) x (((Module.finBasis ℝ E k : E) : TangentSpace I x)) y)

theorem linFieldFamily_smooth (x : M) (v : TangentSpace I x) :
    SmoothField I M (linFieldFamily x v) := by
  refine smoothF_sum Finset.univ _ (fun k _ => ?_)
  exact smoothF_smul (f := fun _ : M => (Module.finBasis ℝ E).coord k v) contMDiff_const
    (Work.Diff.GE.smoothExt_cmdiff (I := I) (M := M) x ((Module.finBasis ℝ E k : E) : TangentSpace I x))

theorem linFieldFamily_apply_self (x : M) (v : TangentSpace I x) :
    linFieldFamily x v x = v := by
  have hstep : ∀ k : Fin (Module.finrank ℝ E),
      ((Module.finBasis ℝ E).coord k) v
          • (smoothExt (I := I) (M := M) x (((Module.finBasis ℝ E k : E) : TangentSpace I x)) x)
        = ((Module.finBasis ℝ E).coord k) v
          • (((Module.finBasis ℝ E k : E) : TangentSpace I x)) := by
    intro k
    rw [Work.Diff.GE.smoothExt_apply (I := I) (M := M)]
  have h : (∑ k : Fin (Module.finrank ℝ E),
      ((Module.finBasis ℝ E).coord k) v
        • (smoothExt (I := I) (M := M) x (((Module.finBasis ℝ E k : E) : TangentSpace I x)) x)) = v := by
    rw [Finset.sum_congr rfl (fun k _ => hstep k)]
    simp only [Module.Basis.coord_apply]
    exact Module.Basis.sum_repr (Module.finBasis ℝ E) v
  simpa only [linFieldFamily] using h

theorem linFieldFamily_linear (x : M) (r s : ℝ) (v w : TangentSpace I x) :
    linFieldFamily x (r • v + s • w) = r • linFieldFamily x v + s • linFieldFamily x w := by
  funext y
  have hcoef : ∀ k : Fin (Module.finrank ℝ E),
      ((Module.finBasis ℝ E).coord k) (r • v + s • w)
        = r * ((Module.finBasis ℝ E).coord k) v + s * ((Module.finBasis ℝ E).coord k) w := by
    intro k
    rw [map_add, map_smul, map_smul]
    rfl
  show (∑ k, ((Module.finBasis ℝ E).coord k) (r • v + s • w)
      • (smoothExt (I := I) (M := M) x (((Module.finBasis ℝ E k : E) : TangentSpace I x)) y))
    = r • (∑ k, ((Module.finBasis ℝ E).coord k) v
        • (smoothExt (I := I) (M := M) x (((Module.finBasis ℝ E k : E) : TangentSpace I x)) y))
      + s • (∑ k, ((Module.finBasis ℝ E).coord k) w
        • (smoothExt (I := I) (M := M) x (((Module.finBasis ℝ E k : E) : TangentSpace I x)) y))
  rw [Finset.smul_sum, Finset.smul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [hcoef k, add_smul, smul_smul, smul_smul]

/-! ## 2. The first-order Leibniz rule for a finite sum of sections -/

/-- The first-order Leibniz rule for `∇` applied to `∑ i, a i • X i`, evaluated at `x`. -/
theorem lcOf_sum_smul {ι : Type*} (g : SMet I M) (s : Finset ι) (a : ι → M → ℝ)
    (X : ι → Π y : M, TangentSpace I y) (v : Π y : M, TangentSpace I y) (x : M)
    (ha : ∀ i ∈ s, CMDiff ∞ (a i)) (hX : ∀ i ∈ s, SmoothField I M (X i))
    (hv : SmoothField I M v) :
    lcOf g (fun y => ∑ i ∈ s, (a i y) • (X i y)) x (v x)
      = ∑ i ∈ s, ((mvfderiv I (a i) x (v x)) • (X i x) + (a i x) • lcOf g (X i) x (v x)) := by
  have haX : ∀ i ∈ s, SmoothField I M ((a i) • (X i)) :=
    fun i hi => (ha i hi).smul_section (hX i hi)
  have h1 := dirF_sum (g := g) s (fun i => (a i) • (X i)) v haX
  have h1' : (fun y : M => ∑ i ∈ s, ((a i) • (X i)) y)
      = (fun y : M => ∑ i ∈ s, a i y • (X i y)) := rfl
  rw [h1'] at h1
  have h2 : ∀ i ∈ s, dirF g ((a i) • (X i)) v
      = (a i) • dirF g (X i) v + (fun y : M => mvfderiv I (a i) y (v y)) • (X i) :=
    fun i hi => dirF_smul g (ha i hi) (hX i hi)
  have h3 := congrFun h1 x
  simp only [dirF, Finset.sum_apply] at h3
  rw [h3]
  refine Finset.sum_congr rfl (fun i hi => ?_)
  have h4 := congrFun (h2 i hi) x
  simp only [dirF, Pi.add_apply, Pi.smul_apply] at h4 ⊢
  rw [h4]
  exact add_comm _ _

/-! ## 3. The constant shift of a matrix function and the frame it produces -/

/-- `A` with the identity added: `A + 1`. -/
noncomputable def addId {n : ℕ} (A : M → (Fin n → Fin n → ℝ)) : M → (Fin n → Fin n → ℝ) :=
  fun y p i => (if p = i then (1 : ℝ) else 0) + A y p i

theorem addId_smooth {n : ℕ} {A : M → (Fin n → Fin n → ℝ)} (hA : SmoothMap I M A) :
    SmoothMap I M (addId A) := by
  have h1 : addId A = (fun _ : M => fun p i : Fin n => (if p = i then (1 : ℝ) else 0)) + A := by
    funext y p i
    simp [addId, Pi.add_apply]
  rw [h1]
  exact contMDiff_const.add hA

theorem addId_apply {n : ℕ} (A : M → (Fin n → Fin n → ℝ)) (y : M) (p i : Fin n) :
    addId A y p i = (if p = i then (1 : ℝ) else 0) + A y p i := rfl

/-- The frame obtained from a frame `F` and a matrix-valued function `A`: `i ↦ ∑ p A p i • F p`. -/
noncomputable def frameStep {n : ℕ} (A : M → (Fin n → Fin n → ℝ))
    (F : Fin n → Π y : M, TangentSpace I y) : Fin n → Π y : M, TangentSpace I y :=
  fun i y => ∑ p, (A y p i) • (F p y)

theorem frameStep_smooth {n : ℕ} (A : M → (Fin n → Fin n → ℝ)) (hA : SmoothMap I M A)
    (F : Fin n → Π y : M, TangentSpace I y) (hF : ∀ i, SmoothField I M (F i)) :
    ∀ i, SmoothField I M (frameStep A F i) := by
  intro i
  refine smoothF_sum Finset.univ _ (fun p _ => ?_)
  exact smoothF_smul (smoothMap_eval hA p i) (hF p)

/-- The covariant derivative of `frameStep A F i` at `x` in a direction `v`. -/
theorem lcOf_frameStep (g : SMet I M) {n : ℕ} (A : M → (Fin n → Fin n → ℝ))
    (hA : SmoothMap I M A) (F : Fin n → Π y : M, TangentSpace I y)
    (hF : ∀ i, SmoothField I M (F i)) (x : M) (i : Fin n) (v : TangentSpace I x) :
    lcOf g (frameStep A F i) x v
      = ∑ p, ((mvfderiv I (fun y : M => A y p i) x v) • (F p x)
          + (A x p i) • lcOf g (F p) x v) := by
  have h := lcOf_sum_smul (I := I) (M := M) g Finset.univ (fun p : Fin n => fun y : M => A y p i)
    F (smoothExt (I := I) (M := M) x v) x (fun p _ => smoothMap_eval hA p i)
    (fun p _ => hF p) (Work.Diff.GE.smoothExt_cmdiff (I := I) (M := M) x v)
  have hfun : frameStep A F i = (fun y : M => ∑ p : Fin n, (A y p i) • (F p y)) := rfl
  rw [hfun]
  simpa only [Work.Diff.GE.smoothExt_apply (I := I) (M := M)] using h

/-! ## 4. The symmetrised field-form second derivative: symmetry, diagonal, skewness -/

variable (g : SMet I M) (x : M)

/-- `transHess` is symmetric in its two directions (it is the symmetrisation by construction). -/
theorem transHess_symm {n : ℕ} (F : Fin n → Π y : M, TangentSpace I y)
    (v w : TangentSpace I x) (p i : Fin n) :
    transHess g x F v w p i = transHess g x F w v p i := by
  unfold transHess
  ring

/-- On the diagonal the symmetrised second derivative is the field-form one. -/
theorem transHess_self {n : ℕ} (F : Fin n → Π y : M, TangentSpace I y)
    (v : TangentSpace I x) (p i : Fin n) :
    transHess g x F v v p i
      = g.inner x (lcOf g (fun y : M => lcOf g (F i) y (smoothExt x v y)) x v) (F p x) := by
  unfold transHess
  ring

/-- The candidate second derivative of the correction matrix: minus the symmetrised second
derivative of the frame. -/
noncomputable def bq (F : Fin (Module.finrank ℝ E) → Π y : M, TangentSpace I y)
    (v w : TangentSpace I x) (p i : Fin (Module.finrank ℝ E)) : ℝ :=
  - transHess g x F v w p i

theorem bq_symm (F : Fin (Module.finrank ℝ E) → Π y : M, TangentSpace I y)
    (v w : TangentSpace I x) : bq g x F v w = bq g x F w v := by
  funext p i
  simp only [bq, Pi.neg_apply]
  rw [transHess_symm]

/-- The diagonal of `bq` is the (negated) field-form second derivative, paired with the frame. -/
theorem bq_diag (F : Fin (Module.finrank ℝ E) → Π y : M, TangentSpace I y)
    (v : TangentSpace I x) (p i : Fin (Module.finrank ℝ E)) :
    bq g x F v v p i
      = - g.inner x (lcOf g (fun y : M => lcOf g (F i) y (smoothExt x v y)) x v) (F p x) := by
  simp only [bq]
  rw [transHess_self]

/-- `bq` is skew in its two matrix indices, being minus the (skew) `transHess`. -/
theorem bq_skew (hLC : LCSmooth I M) (F : Fin (Module.finrank ℝ E) → Π y : M, TangentSpace I y)
    (hF : ∀ i, SmoothField I M (F i)) (hON : ONFrameNear I M g x F)
    (h0 : ∀ (i : Fin (Module.finrank ℝ E)) (v : TangentSpace I x), lcOf g (F i) x v = 0)
    (v w : TangentSpace I x) (p i : Fin (Module.finrank ℝ E)) :
    bq g x F v w i p = -(bq g x F v w p i) := by
  have h := transHess_skew (I := I) (M := M) hLC g x F hF hON h0 v w p i
  simp only [bq, Pi.neg_apply]
  linarith

/-! ## 5. The matrix exponential, read entrywise -/

/-- The matrix exponential, with the matrix algebra structure kept explicit. -/
noncomputable abbrev matExpK {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  NormedSpace.exp A

/-! ## 5b. The second-order jet, with the matrix type explicit -/

/-- The second-order jet realisation of `Work.Diff.Evol.smooth_skew_jet2`, stated with the explicit
matrix type (so that the matrix algebra and operator-norm instances are the ones used by the
matrix exponential). -/
theorem smooth_skew_jet2_matrix
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I (((⊤ : ℕ∞) : WithTop ℕ∞)) M] [I.Boundaryless] [T2Space M]
    {n : ℕ} (x : M) (Q : TangentSpace I x → TangentSpace I x → Matrix (Fin n) (Fin n) ℝ)
    (hQlin1 : ∀ (r s : ℝ) (v₁ v₂ : TangentSpace I x) (w : TangentSpace I x),
      Q (r • v₁ + s • v₂) w = r • Q v₁ w + s • Q v₂ w)
    (hQlin2 : ∀ (r s : ℝ) (v : TangentSpace I x) (w₁ w₂ : TangentSpace I x),
      Q v (r • w₁ + s • w₂) = r • Q v w₁ + s • Q v w₂)
    (hQsym : ∀ v w : TangentSpace I x, Q v w = Q w v)
    (hQsk : ∀ (v w : TangentSpace I x) (p i : Fin n), Q v w i p = -(Q v w p i)) :
    ∃ B : M → Matrix (Fin n) (Fin n) ℝ,
      SmoothMap I M B ∧ B x = 0 ∧
      (∀ y : M, Matrix.transpose (B y) = -(B y)) ∧
      (∀ v : TangentSpace I x, mvfderiv I B x v = 0) ∧
      (∀ (W : Π y : M, TangentSpace I y), SmoothField I M W →
        mvfderiv I (fun y : M => mvfderiv I B y (W y)) x (W x) = Q (W x) (W x)) := by
  classical
  obtain ⟨φ, hφsm, hφx, hφderiv⟩ := chartMap_smooth (I := I) (M := M) x
  obtain ⟨Qp, hQp⟩ := Q_pack (V := E) (F := Matrix (Fin n) (Fin n) ℝ) Q hQlin1 hQlin2
  have hTinv : (mvfderiv I (extChartAt I x) x).IsInvertible := by
    rw [mvfderiv_eq_mfderiv_self]
    exact isInvertible_mfderiv_extChartAt (mem_extChartAt_source x)
  have hφinv : (mvfderiv I φ x).IsInvertible := by
    rw [hφderiv]
    exact hTinv
  set S : E →L[ℝ] E := (mvfderiv I φ x).inverse with hSdef
  have hST : ∀ v : TangentSpace I x, S (mvfderiv I φ x v) = v := fun v =>
    hφinv.inverse_apply_self v
  let P₀ : E →ₗ[ℝ] (E →L[ℝ] Matrix (Fin n) (Fin n) ℝ) :=
    { toFun := fun z => (Qp (S z)).comp S
      map_add' := by
        intro a b
        ext h
        simp only [ContinuousLinearMap.comp_apply, add_apply, map_add]
      map_smul' := by
        intro c a
        refine ContinuousLinearMap.ext fun h => ?_
        show (Qp (S (c • a))) (S h) = c • ((Qp (S a)) (S h))
        rw [map_smul, map_smul, ContinuousLinearMap.smul_apply] }
  let P : E →L[ℝ] (E →L[ℝ] Matrix (Fin n) (Fin n) ℝ) := P₀.toContinuousLinearMap
  have hP : ∀ z : E, P z = (Qp (S z)).comp S := fun z => rfl
  have hPz : ∀ z : E, (P z) z = Qp (S z) (S z) := by
    intro z
    simp only [hP, ContinuousLinearMap.comp_apply]
  have hQpsk : ∀ (v w : E) (p i : Fin n), Qp v w i p = -(Qp v w p i) := by
    intro v w p i
    rw [hQp v w]
    exact hQsk v w p i
  have hφmd : MDifferentiableAt I (modelWithCornersSelf ℝ E) φ x :=
    hφsm.mdifferentiableAt (by simp)
  refine ⟨quadMap P ∘ φ, ?_, ?_, ?_, ?_, ?_⟩
  · exact (contDiff_quadMap P).contMDiff.comp hφsm
  · show quadMap P (φ x) = 0
    rw [hφx, quadMap_zero]
  · intro y
    have hsk : Matrix.transpose ((P (φ y)) (φ y)) = -((P (φ y)) (φ y)) := by
      ext p i
      rw [Matrix.transpose_apply]
      show (P (φ y)) (φ y) i p = -((P (φ y)) (φ y) p i)
      rw [hPz, hQpsk]
    show Matrix.transpose (quadMap P (φ y)) = -(quadMap P (φ y))
    have hq : quadMap P (φ y) = (1 / 2 : ℝ) • ((P (φ y)) (φ y)) := rfl
    rw [hq, Matrix.transpose_smul, hsk, smul_neg]
  · intro v
    have hpoint0 : mvfderiv I (quadMap P ∘ φ) x v
        = (fderiv ℝ (quadMap P) (φ x)) (mvfderiv I φ x v) := by
      rw [mvfderiv_comp (x := x) (mdifferentiableAt_quadMap P (φ x)) hφmd,
        mvfderiv_eq_fderiv]
      rfl
    rw [hpoint0, fderiv_quadMap, hφx, quadDeriv_zero]
    exact ContinuousLinearMap.zero_apply (mvfderiv I φ x v)
  · intro W hW
    set V : M → E := fun y : M => mvfderiv I φ y (W y) with hVdef
    have hVsm : ContMDiff I (modelWithCornersSelf ℝ E) ∞ V := by
      rw [hVdef]
      exact Commons.Geometry.Manifold.VectorField.mvfderiv_apply_contMDiff hφsm hW
    have hVmd : MDifferentiableAt I (modelWithCornersSelf ℝ E) V x :=
      hVsm.mdifferentiableAt (by simp)
    have hAmd : MDifferentiableAt I (modelWithCornersSelf ℝ (E →L[ℝ] Matrix (Fin n) (Fin n) ℝ))
        (quadDeriv P ∘ φ) x :=
      (((quadDeriv P).contMDiff.comp hφsm).contMDiffAt).mdifferentiableAt (by simp)
    have hpoint : ∀ y : M,
        mvfderiv I (quadMap P ∘ φ) y (W y) = (quadDeriv P ∘ φ) y (V y) := by
      intro y
      have hfy : MDifferentiableAt I (modelWithCornersSelf ℝ E) φ y :=
        hφsm.mdifferentiableAt (by simp)
      rw [mvfderiv_comp (x := y) (mdifferentiableAt_quadMap P (φ y)) hfy,
        mvfderiv_eq_fderiv, fderiv_quadMap]
      rfl
    rw [show (fun y : M => mvfderiv I (quadMap P ∘ φ) y (W y))
        = (fun y : M => (quadDeriv P ∘ φ) y (V y)) from funext hpoint]
    rw [mvfderiv_clm_apply hAmd hVmd (W x)]
    have hAx : (quadDeriv P ∘ φ) x = 0 := by
      show quadDeriv P (φ x) = 0
      rw [hφx, quadDeriv_zero]
    rw [hAx, zero_apply, add_zero]
    have hAval : mvfderiv I (quadDeriv P ∘ φ) x (W x) = quadDeriv P (V x) := by
      rw [mvfderiv_comp (x := x) (mdifferentiableAt_quadDeriv P (φ x)) hφmd,
        mvfderiv_eq_fderiv, ContinuousLinearMap.fderiv]
      rfl
    have hVx : V x = mvfderiv I φ x (W x) := by rw [hVdef]
    rw [hAval, hVx, quadDeriv_apply_self, hPz, hST]
    exact hQp (W x) (W x)

/-! ## 6. The second-order step -/

/-- The second-order Leibniz rule for `∇` applied to `∑ i, a i • X i` with *scalar* coefficient
families, evaluated at `x`. -/
theorem lcOf_sum_smul2 {ι : Type*} (g : SMet I M) (hLC : LCSmooth I M) (s : Finset ι)
    (a : ι → M → ℝ)
    (X : ι → Π y : M, TangentSpace I y) (W : Π y : M, TangentSpace I y) (x : M)
    (ha : ∀ i ∈ s, CMDiff ∞ (a i)) (hX : ∀ i ∈ s, SmoothField I M (X i))
    (hW : SmoothField I M W) :
    lcOf g (fun y : M => lcOf g (fun z : M => ∑ i ∈ s, (a i z) • (X i z)) y (W y)) x (W x)
      = ∑ i ∈ s, ((mvfderiv I (fun y : M => mvfderiv I (a i) y (W y)) x (W x)) • (X i x)
          + (2 : ℝ) • ((mvfderiv I (a i) x (W x)) • lcOf g (X i) x (W x))
          + (a i x) • (lcOf g (fun y : M => lcOf g (X i) y (W y)) x (W x))) := by
  have h := dirF_second_sum g hLC s a X W ha hX hW
  have hx := congrFun h x
  simp only [dirF, Finset.sum_apply, Pi.add_apply, Pi.smul_apply] at hx ⊢
  exact hx

/-- The chain rule for a continuous linear functional applied to a section. -/
theorem mvfderiv_clm_comp {F₂ : Type*} [NormedAddCommGroup F₂] [NormedSpace ℝ F₂]
    (φ : F₂ →L[ℝ] ℝ) {G : M → F₂} {x : M} (hG : MDiffAt G x) (v : TangentSpace I x) :
    mvfderiv I (fun y : M => φ (G y)) x v = φ (mvfderiv I G x v) := by
  have h1 : MDiffAt (fun _ : M => φ) x := mdifferentiableAt_const
  have h := mvfderiv_clm_apply (I := I) (M := M) h1 hG v
  rw [h, mvfderiv_const]
  simp

/-- The `(p,i)` entry of the exponential of a smooth matrix family is smooth. -/
theorem smooth_entry_exp {n : ℕ} {B : M → Matrix (Fin n) (Fin n) ℝ}
    (hB : SmoothMap I M B) (p i : Fin n) :
    CMDiff ∞ (fun y : M => (NormedSpace.exp (B y)) p i) := by
  have hExp : SmoothMap I M (fun y : M => NormedSpace.exp (B y)) :=
    exp_contDiff.comp_contMDiff hB
  have h := (ContinuousLinearMap.contMDiff
    (FrameFirst.matEntryCLM n p i)).comp hExp
  have hfun : (fun y : M => (NormedSpace.exp (B y)) p i)
      = (fun y : M => FrameFirst.matEntryCLM n p i (NormedSpace.exp (B y))) := by
    funext y
    exact (FrameFirst.matEntryCLM_apply p i _).symm
  rw [hfun]
  exact h

theorem frame_exists_step2
    (hLC : LCSmooth I M) (e : Fin (Module.finrank ℝ E) → TangentSpace I x)
    (he : IsONFrame g x e)
    (hTHb : ∀ (F : Fin (Module.finrank ℝ E) → Π y : M, TangentSpace I y),
      (∀ i, SmoothField I M (F i)) →
      (∀ (i : Fin (Module.finrank ℝ E)) (v : TangentSpace I x), lcOf g (F i) x v = 0) →
      (∀ (r s : ℝ) (v₁ v₂ : TangentSpace I x) (w : TangentSpace I x)
          (p i : Fin (Module.finrank ℝ E)),
          transHess g x F (r • v₁ + s • v₂) w p i
            = r * transHess g x F v₁ w p i + s * transHess g x F v₂ w p i) ∧
      (∀ (r s : ℝ) (v : TangentSpace I x) (w₁ w₂ : TangentSpace I x)
          (p i : Fin (Module.finrank ℝ E)),
          transHess g x F v (r • w₁ + s • w₂) p i
            = r * transHess g x F v w₁ p i + s * transHess g x F v w₂ p i))
    (hfirst : ∃ Ef₁ : Fin (Module.finrank ℝ E) → Π y : M, TangentSpace I y,
      (∀ i, Ef₁ i x = e i) ∧ (∀ i, SmoothField I M (Ef₁ i)) ∧ ONFrameNear I M g x Ef₁ ∧
      (∀ (i : Fin (Module.finrank ℝ E)) (v : TangentSpace I x), lcOf g (Ef₁ i) x v = 0)) :
    ∃ Ef : Fin (Module.finrank ℝ E) → Π y : M, TangentSpace I y,
      (∀ i, Ef i x = e i) ∧ (∀ i, SmoothField I M (Ef i)) ∧ ONFrameNear I M g x Ef ∧
      (∀ (i : Fin (Module.finrank ℝ E)) (v : TangentSpace I x), lcOf g (Ef i) x v = 0) ∧
      (∀ (i : Fin (Module.finrank ℝ E)) (W : Π y : M, TangentSpace I y),
        SmoothField I M W → lcOf g (fun y : M => lcOf g (Ef i) y (W y)) x (W x) = 0) := by
  classical
  obtain ⟨Ef₁, hval₁, hsm₁, hON₁, hpar₁⟩ := hfirst
  have hQlin1 : ∀ (r s : ℝ) (v₁ v₂ w : TangentSpace I x),
      bq g x Ef₁ (r • v₁ + s • v₂) w = r • bq g x Ef₁ v₁ w + s • bq g x Ef₁ v₂ w := by
    intro r s v₁ v₂ w
    funext p i
    have h := (hTHb Ef₁ hsm₁ hpar₁).1 r s v₁ v₂ w p i
    simp only [bq, Pi.neg_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [h]
    ring
  have hQlin2 : ∀ (r s : ℝ) (v : TangentSpace I x) (w₁ w₂ : TangentSpace I x),
      bq g x Ef₁ v (r • w₁ + s • w₂) = r • bq g x Ef₁ v w₁ + s • bq g x Ef₁ v w₂ := by
    intro r s v w₁ w₂
    funext p i
    have h := (hTHb Ef₁ hsm₁ hpar₁).2 r s v w₁ w₂ p i
    simp only [bq, Pi.neg_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [h]
    ring
  -- the skew correction of the second order, with the explicit matrix type
  obtain ⟨B₂, hB₂sm, hB₂x, hB₂sk, hB₂d, hB₂d2⟩ :=
    smooth_skew_jet2_matrix (I := I) (M := M) (n := Module.finrank ℝ E) x (bq g x Ef₁)
      hQlin1 hQlin2 (bq_symm g x Ef₁) (bq_skew g x hLC Ef₁ hsm₁ hON₁ hpar₁)
  -- the scalar coefficient family
  let a : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → M → ℝ :=
    fun p i y => (NormedSpace.exp (B₂ y)) p i
  have hasm : ∀ p i, CMDiff ∞ (a p i) := by
    intro p i
    have h := smooth_entry_exp (I := I) (M := M) (B := B₂) hB₂sm p i
    exact h
  have hax : ∀ p i : Fin (Module.finrank ℝ E), a p i x = (if p = i then (1 : ℝ) else 0) := by
    intro p i
    show (NormedSpace.exp (B₂ x)) p i = _
    rw [hB₂x, NormedSpace.exp_zero]
    show (1 : Matrix (Fin (Module.finrank ℝ E)) (Fin (Module.finrank ℝ E)) ℝ) p i
      = (if p = i then (1 : ℝ) else 0)
    rw [Matrix.one_apply]
  have had : ∀ (p i : Fin (Module.finrank ℝ E)) (v : TangentSpace I x),
      mvfderiv I (a p i) x v = 0 := by
    intro p i v
    have h1 := FrameFirst.mvfderiv_entry_exp' (I := I) (B := B₂) hB₂sm x p i v
    rw [h1]
    have h2 : mvfderiv I (fun y : M => FrameFirst.matExp (B₂ y)) x v = 0 := by
      rw [(exp_chain_rule (𝔸 := Matrix (Fin (Module.finrank ℝ E)) (Fin (Module.finrank ℝ E)) ℝ)
        (fun y : M => B₂ y) hB₂sm x hB₂x).1 v, hB₂d v]
    rw [h2]
    rfl
  have hExpSm := exp_contDiff.comp_contMDiff hB₂sm
  have had2 : ∀ (p i : Fin (Module.finrank ℝ E)) (W : Π y : M, TangentSpace I y),
      SmoothField I M W →
      mvfderiv I (fun y : M => mvfderiv I (a p i) y (W y)) x (W x)
        = bq g x Ef₁ (W x) (W x) p i := by
    intro p i W hW
    have hVsm := Commons.Geometry.Manifold.VectorField.mvfderiv_apply_contMDiff hExpSm hW
    have hVmd := hVsm.mdifferentiableAt (x := x) (by simp)
    have hpoint : (fun y : M => mvfderiv I (a p i) y (W y))
        = (fun y : M => FrameFirst.matEntryCLM (Module.finrank ℝ E) p i
            (mvfderiv I (fun z : M => NormedSpace.exp (B₂ z)) y (W y))) := by
      funext y
      rw [FrameFirst.mvfderiv_entry_exp' (I := I) (B := B₂) hB₂sm y p i (W y)]
      rfl
    have hstep : mvfderiv I (fun y : M => FrameFirst.matEntryCLM (Module.finrank ℝ E) p i
          (mvfderiv I (fun z : M => NormedSpace.exp (B₂ z)) y (W y))) x (W x)
        = FrameFirst.matEntryCLM (Module.finrank ℝ E) p i
          (mvfderiv I (fun y : M => mvfderiv I (fun z : M => NormedSpace.exp (B₂ z)) y (W y))
            x (W x)) :=
      mvfderiv_clm_comp (I := I) (M := M)
        (FrameFirst.matEntryCLM (Module.finrank ℝ E) p i) hVmd (W x)
    rw [hpoint, hstep]
    have h2 : mvfderiv I (fun y : M => mvfderiv I (fun z : M => NormedSpace.exp (B₂ z)) y (W y))
        x (W x) = bq g x Ef₁ (W x) (W x) := by
      have hexp := (exp_chain_rule (𝔸 := Matrix (Fin (Module.finrank ℝ E))
        (Fin (Module.finrank ℝ E)) ℝ) (fun y : M => B₂ y) hB₂sm x hB₂x).2 W hW
      rw [hB₂d2 W hW, hB₂d (W x), zero_mul, add_zero] at hexp
      exact hexp
    rw [h2]
    rfl
  -- the corrected frame
  let Ef₂ : Fin (Module.finrank ℝ E) → Π y : M, TangentSpace I y :=
    fun i y => ∑ p, (a p i y) • (Ef₁ p y)
  have hval₂ : ∀ i, Ef₂ i x = e i := by
    intro i
    show (∑ p : Fin (Module.finrank ℝ E), (a p i x) • (Ef₁ p x)) = e i
    rw [Finset.sum_eq_single i]
    · rw [hax i i, if_pos rfl, one_smul, hval₁ i]
    · intro p _ hp
      rw [hax p i, if_neg hp, zero_smul]
    · intro hi
      exact absurd (Finset.mem_univ i) hi
  have hsm₂ : ∀ i, SmoothField I M (Ef₂ i) := by
    intro i
    refine smoothF_sum Finset.univ _ (fun p _ => ?_)
    exact smoothF_smul (hasm p i) (hsm₁ p)
  have hON₂ : ONFrameNear I M g x Ef₂ := by
    filter_upwards [hON₁] with y hyON
    intro i j
    show g.inner y (∑ k, (a k i y) • Ef₁ k y) (∑ l, (a l j y) • Ef₁ l y)
      = if i = j then (1 : ℝ) else 0
    have hsk : Matrix.transpose (B₂ y) = -(B₂ y) := hB₂sk y
    have hM : Matrix.transpose (NormedSpace.exp (B₂ y)) * NormedSpace.exp (B₂ y) = 1 :=
      exp_transpose_mul_exp (B₂ y) hsk
    have hinner : ∀ k : Fin (Module.finrank ℝ E),
        (∑ l, ((a k i y) * (a l j y)) * g.inner y (Ef₁ k y) (Ef₁ l y))
          = (a k i y) * (a k j y) := by
      intro k
      rw [Finset.sum_eq_single k]
      · rw [hyON k k, if_pos rfl, mul_one]
      · intro l _ hl
        rw [hyON k l, if_neg (fun h : k = l => hl h.symm), mul_zero]
      · intro hk
        exact absurd (Finset.mem_univ k) hk
    have hsum : (∑ k, (a k i y) * (a k j y))
        = (Matrix.transpose (NormedSpace.exp (B₂ y)) * NormedSpace.exp (B₂ y)) i j := by
      rw [Matrix.mul_apply]
      exact Finset.sum_congr rfl (fun k _ => by rw [Matrix.transpose_apply])
    rw [FrameFirst.inner_sum_sum g y (fun k => a k i y) (fun l => a l j y) (fun k => Ef₁ k y),
      Finset.sum_congr rfl (fun k _ => hinner k), hsum, hM, Matrix.one_apply]
  have hpar₂ : ∀ (i : Fin (Module.finrank ℝ E)) (v : TangentSpace I x), lcOf g (Ef₂ i) x v = 0 := by
    intro i v
    have h := lcOf_sum_smul (I := I) (M := M) g Finset.univ (fun p => a p i) Ef₁
      (smoothExt x v) x (fun p _ => hasm p i) (fun p _ => hsm₁ p)
      (Work.Diff.GE.smoothExt_cmdiff x v)
    have hL : lcOf g (Ef₂ i) x v
        = lcOf g (fun y : M => ∑ p, a p i y • Ef₁ p y) x ((smoothExt x v) x) := by
      rw [Work.Diff.GE.smoothExt_apply]
    rw [hL, h]
    simp only [Work.Diff.GE.smoothExt_apply]
    refine Finset.sum_eq_zero (fun p _ => ?_)
    rw [had p i v, zero_smul, hpar₁ p v, smul_zero, add_zero]
  have hpar2₂ : ∀ (i : Fin (Module.finrank ℝ E)) (W : Π y : M, TangentSpace I y),
      SmoothField I M W → lcOf g (fun y : M => lcOf g (Ef₂ i) y (W y)) x (W x) = 0 := by
    intro i W hW
    have h := lcOf_sum_smul2 (I := I) (M := M) g hLC Finset.univ (fun p => a p i) Ef₁ W x
      (fun p _ => hasm p i) (fun p _ => hsm₁ p) hW
    rw [show lcOf g (fun y : M => lcOf g (Ef₂ i) y (W y)) x (W x)
        = lcOf g (fun y : M => lcOf g (fun z : M => ∑ p, a p i z • Ef₁ p z) y (W y))
            x (W x) from rfl, h]
    have hterm : ∀ p : Fin (Module.finrank ℝ E),
        ((mvfderiv I (fun y : M => mvfderiv I (a p i) y (W y)) x (W x)) • (Ef₁ p x)
            + (2 : ℝ) • ((mvfderiv I (a p i) x (W x)) • lcOf g (Ef₁ p) x (W x))
            + (a p i x) • (lcOf g (fun y : M => lcOf g (Ef₁ p) y (W y)) x (W x)))
          = (bq g x Ef₁ (W x) (W x) p i) • (Ef₁ p x)
            + (if p = i then (1 : ℝ) else 0)
              • (lcOf g (fun y : M => lcOf g (Ef₁ p) y (W y)) x (W x)) := by
      intro p
      rw [had2 p i W hW, had p i (W x), hax p i]
      simp only [zero_smul, smul_zero, add_zero]
    have hsecond : (∑ p : Fin (Module.finrank ℝ E),
          (if p = i then (1 : ℝ) else 0)
            • (lcOf g (fun y : M => lcOf g (Ef₁ p) y (W y)) x (W x)))
        = lcOf g (fun y : M => lcOf g (Ef₁ i) y (W y)) x (W x) := by
      rw [Finset.sum_eq_single i]
      · rw [if_pos rfl, one_smul]
      · intro p _ hp
        rw [if_neg hp, zero_smul]
      · intro hi
        exact absurd (Finset.mem_univ i) hi
    rw [Finset.sum_congr rfl (fun p _ => hterm p), Finset.sum_add_distrib, hsecond]
    · have hdiag : (∑ p : Fin (Module.finrank ℝ E),
            (bq g x Ef₁ (W x) (W x) p i) • (Ef₁ p x))
          = - (lcOf g (fun y : M => lcOf g (Ef₁ i) y (smoothExt x (W x) y)) x (W x)) := by
        have h1 : ∀ p : Fin (Module.finrank ℝ E),
            (bq g x Ef₁ (W x) (W x) p i) • (Ef₁ p x)
              = - ((g.inner x (lcOf g (fun y : M => lcOf g (Ef₁ i) y (smoothExt x (W x) y))
                    x (W x)) (e p)) • e p) := by
          intro p
          rw [bq_diag, hval₁ p, neg_smul]
        rw [Finset.sum_congr rfl (fun p _ => h1 p), Finset.sum_neg_distrib]
        congr 1
        exact Work.EXT.sum_inner_smul_eq_self_of_isONFrame g x e he _
      rw [hdiag]
      have hY : lcOf g (fun y : M => lcOf g (Ef₁ i) y (smoothExt x (W x) y)) x (W x)
          = lcOf g (fun y : M => lcOf g (Ef₁ i) y (W y)) x (W x) :=
        by
          simpa only [Work.Diff.GE.smoothExt_apply] using
            lcOf_second_congr_value (I := I) (M := M) hLC g x (Ef₁ i) (hsm₁ i) (hpar₁ i)
              (smoothExt x (W x)) W (Work.Diff.GE.smoothExt_cmdiff x (W x)) hW
              (Work.Diff.GE.smoothExt_apply x (W x))
      rw [← hY]
      exact neg_add_cancel _
  exact ⟨Ef₂, hval₂, hsm₂, hON₂, hpar₂, hpar2₂⟩


/-! ## 7. The frame exists theorem -/

theorem frame_exists_mat
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I (((⊤ : ℕ∞) : WithTop ℕ∞)) M] [I.Boundaryless] [T2Space M] [CompactSpace M]
    (hLC : Submission.Diff.LCSmooth I M) (g : Submission.Diff.SMet I M) (x : M)
    (e : Fin (Module.finrank ℝ E) → TangentSpace I x) (he : Submission.Diff.IsONFrame g x e) :
    ∃ Ef : Fin (Module.finrank ℝ E) → Π y : M, TangentSpace I y,
      (∀ i, Ef i x = e i) ∧ (∀ i, Work.Diff.Evol.SmoothField I M (Ef i)) ∧
      Work.Diff.Evol.ONFrameNear I M g x Ef ∧
      (∀ (i : Fin (Module.finrank ℝ E)) (v : TangentSpace I x),
        Submission.Diff.lcOf g (Ef i) x v = 0) ∧
      (∀ (i : Fin (Module.finrank ℝ E)) (W : Π y : M, TangentSpace I y),
        Work.Diff.Evol.SmoothField I M W →
        Submission.Diff.lcOf g (fun y : M ↦ Submission.Diff.lcOf g (Ef i) y (W y)) x (W x) = 0) :=
  frame_exists_step2 (I := I) (M := M) g x hLC e he
    (fun F hF hF0 => transHess_bilinear (I := I) (M := M) g x F hF hF0)
    (frame_exists_first (I := I) (M := M) hLC g x e he)

end Work.Diff.Evol
