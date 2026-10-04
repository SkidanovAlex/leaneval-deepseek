import Mathlib
import Submission.Work.Diff.GE.CFQDefs
import Submission.Work.Diff.GE.qPair_rot_eq_qPairGen
import Submission.Work.Diff.GE.rmFrame_eq_rot
import Submission.Work.Diff.GE.rmNormSq_eq_N4_of_basis
import Submission.Work.Diff.GE.norms_defs
import Submission.Work.Diff.GE.FrameIndep
import Submission.Work.Diff.GE.dRmNormSq_eq_N5_of_basis
import Submission.Work.Diff.GE.rot_frobsq

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# `⟪Rm, Q(Rm)⟫` in the coordinate frame of a chart

The frozen quantity `Submission.Diff.qPairAt (G t) y = ⟪Rm, Q(Rm)⟫` is computed in the
`Classical.epsilon`-chosen orthonormal frame `onFrame (G t) y` (`rmC`).  For the regularity
(`REG`) and continuity arguments one needs it instead in the *coordinate frame* of the chart at
`x₀`: `rmC4 G x₀ t y` are the curvature components in `cFrame x₀ · y`, and `GramM G x₀ t y` is the
Gram matrix of that frame for the metric `G t`.  This file proves

  `qPairAt (G t) y = qPairGen (GramM G x₀ t y) (rmC4 G x₀ t y)`,

the `qPair`-analogue of `rmNormSq_eq_N4_of_basis` (`|Rm|² = N4 GramM rmC4`).

Proof.  Let `f = onFrame (G t) y` (orthonormal), `e = cFrame x₀ · y` (the coordinate frame, a basis
at every point of the chart: `span_cFrame_eq_top`, below) and `A` the matrix of coordinates of `e`
in `f`, so that `A * Aᵀ = GramM` (Parseval, `mul_transpose_eq_gram`) and `A` is invertible
(`isUnit_det_basis_repr`).  Multilinearity of the curvature gives `rmC4 = rot A (rmC)` and the
algebraic content is the identity `qPairGen (A * Aᵀ) (rot A R) = qPair R` (`qPairGen_gram_rot`,
proved here as `qPairGen_gram_rot_aux`), the Gram-matrix companion of `frobSq_rot`.

The identity `⟪Rm, Q(Rm)⟫(A Aᵀ)(rot A R) = ⟪Rm, Q(Rm)⟫(R)` is the characterisation of `qPairGen`:
`qPair_rot_eq_qPairGen` says `qPair (rot M C) = qPairGen Γ C` whenever `M Γ Mᵀ = 1`; taking
`M := A⁻¹`, `Γ := A * Aᵀ` (so that `A⁻¹ (A Aᵀ) (A⁻¹)ᵀ = 1`) gives
`qPairGen (A * Aᵀ) (rot A R) = qPair (rot A⁻¹ (rot A R))`, and `rot` is a multiplicative unital
action (`rot_mul`, `rot_one`), so `rot A⁻¹ (rot A R) = rot (A⁻¹ A) R = rot 1 R = R`.
-/

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology Matrix
open Bundle ContDiff Set VectorField CovariantDerivative Metric

namespace Work.Diff.GE

/-! ## The action `rot` on 4-index arrays is multiplicative and unital

`rot A R` is the fourfold Kronecker matrix `A ⊗ A ⊗ A ⊗ A` acting on the flattened array `R`; both
facts below are read off from `Work.Diff.GE.rot_eq_mulVec`. -/

private lemma kmat_one {n : ℕ} : kmat (1 : Matrix (Fin n) (Fin n) ℝ) = 1 := by
  simp only [kmat, kA, Matrix.one_kronecker_one]

private lemma kmat_mul {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℝ) :
    kmat (A * B) = kmat A * kmat B := by
  have h1 : kA (A * B) = kA A * kA B := by
    simp only [kA]
    exact Matrix.mul_kronecker_mul A B A B
  simp only [kmat, h1]
  exact Matrix.mul_kronecker_mul (kA A) (kA B) (kA A) (kA B)

private lemma rot_one {n : ℕ} (R : Curv4 n) : rot (1 : Matrix (Fin n) (Fin n) ℝ) R = R := by
  have h : vecOf (rot (1 : Matrix (Fin n) (Fin n) ℝ) R) = vecOf R := by
    rw [rot_eq_mulVec, kmat_one, Matrix.one_mulVec]
  funext i j k l
  exact congrFun h ⟨(i, j), (k, l)⟩

private lemma rot_mul {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℝ) (R : Curv4 n) :
    rot (A * B) R = rot A (rot B R) := by
  have h : vecOf (rot (A * B) R) = vecOf (rot A (rot B R)) := by
    rw [rot_eq_mulVec (A * B) R, rot_eq_mulVec A (rot B R), rot_eq_mulVec B R, kmat_mul,
      Matrix.mulVec_mulVec]
  funext i j k l
  exact congrFun h ⟨(i, j), (k, l)⟩

/-! ## The Gram form of `qPairGen` -/

private lemma qPairGen_gram_rot_aux {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : IsUnit A.det)
    (R : Curv4 n) : qPairGen (A * Matrix.transpose A) (rot A R) = qPair R := by
  have hAt : IsUnit (Matrix.transpose A).det := by rwa [Matrix.det_transpose]
  -- `M := A⁻¹` inverts the Gram matrix `A * Aᵀ` in the sense of `qPair_rot_eq_qPairGen`
  have hM : A⁻¹ * (A * Matrix.transpose A) * Matrix.transpose A⁻¹ = 1 := by
    rw [Matrix.transpose_nonsing_inv]
    rw [← Matrix.mul_assoc A⁻¹ A (Matrix.transpose A)]
    rw [Matrix.mul_assoc (A⁻¹ * A) (Matrix.transpose A) (Matrix.transpose A)⁻¹]
    rw [Matrix.nonsing_inv_mul A hA, Matrix.one_mul, Matrix.mul_nonsing_inv (Matrix.transpose A) hAt]
  have hq := qPair_rot_eq_qPairGen (A * Matrix.transpose A) (A⁻¹) (rot A R) hM
  rw [← hq]
  rw [← rot_mul, Matrix.nonsing_inv_mul A hA]
  exact congrArg qPair (rot_one R)

/-! ## The coordinate frame of a chart spans the tangent space -/

private lemma span_cFrame_eq_top
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ((⊤ : ENat) : WithTop ENat) M]
    (x₀ : M) {y : M} (hy : y ∈ (chartAt H x₀).source) :
    Submodule.span ℝ (Set.range (fun i => cFrame (I := I) x₀ i y)) = ⊤ := by
  -- the inverse of the chart trivialisation at `y` is an isomorphism `E ≃ T_yM`
  let φ : E →ₗ[ℝ] TangentSpace I y :=
    { toFun := fun v => (trivializationAt E (TangentSpace I) x₀).symmL ℝ y v
      map_add' := fun v w => map_add ((trivializationAt E (TangentSpace I) x₀).symmL ℝ y) v w
      map_smul' := fun c v => map_smul ((trivializationAt E (TangentSpace I) x₀).symmL ℝ y) c v }
  have hinj : Function.Injective φ := by
    intro v w h
    have hv := Trivialization.continuousLinearMapAt_symmL
      (e := trivializationAt E (TangentSpace I) x₀) (R := ℝ) hy v
    have hw := Trivialization.continuousLinearMapAt_symmL
      (e := trivializationAt E (TangentSpace I) x₀) (R := ℝ) hy w
    have h' : (trivializationAt E (TangentSpace I) x₀).symmL ℝ y v
        = (trivializationAt E (TangentSpace I) x₀).symmL ℝ y w := h
    calc v = (trivializationAt E (TangentSpace I) x₀).continuousLinearMapAt ℝ y
            ((trivializationAt E (TangentSpace I) x₀).symmL ℝ y v) := hv.symm
      _ = (trivializationAt E (TangentSpace I) x₀).continuousLinearMapAt ℝ y
            ((trivializationAt E (TangentSpace I) x₀).symmL ℝ y w) := by rw [h']
      _ = w := hw
  have hsurj : Function.Surjective φ := LinearMap.injective_iff_surjective.mp hinj
  have himg : Set.range (fun i => cFrame (I := I) x₀ i y)
      = φ '' (Set.range (cBasis (E := E))) := by
    ext v
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨cBasis i, ⟨i, rfl⟩, rfl⟩
    · rintro ⟨u, ⟨i, rfl⟩, rfl⟩
      exact ⟨i, rfl⟩
  rw [himg, Submodule.span_image, Module.Basis.span_eq, Submodule.map_top,
    LinearMap.range_eq_top.mpr hsurj]

/-! ## The target -/

theorem qPairAt_eq_qPairGen_Gram
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ((⊤ : ENat) : WithTop ENat) M] [I.Boundaryless] [T2Space M]
    (hLC : Submission.Diff.LCSmooth I M) (G : ℝ → Submission.Diff.SMet I M) (x₀ : M)
    {y : M} (hy : y ∈ (chartAt H x₀).source) (t : ℝ) :
    Submission.Diff.qPairAt (G t) y
      = Work.Diff.GE.qPairGen (Work.Diff.GE.GramM (I := I) G x₀ t y)
          (Work.Diff.GE.rmC4 (I := I) G x₀ t y) := by
  classical
  rcases Nat.eq_zero_or_pos (Module.finrank ℝ E) with h0 | hpos
  · -- no indices at all: both sides are empty sums / empty traces
    haveI : IsEmpty (Fin (Module.finrank ℝ E)) := by rw [h0]; infer_instance
    have hq : Submission.Diff.qPairAt (G t) y = 0 := by
      simp only [Submission.Diff.qPairAt, Submission.Diff.rmC, Submission.Diff.Alg.qPair,
        Finset.univ_eq_empty, Finset.sum_empty]
    have hp : Work.Diff.GE.qPairGen (Work.Diff.GE.GramM (I := I) G x₀ t y)
        (Work.Diff.GE.rmC4 (I := I) G x₀ t y) = 0 := by
      simp only [Work.Diff.GE.qPairGen, Matrix.trace, Matrix.diag_apply, Finset.univ_eq_empty,
        Finset.sum_empty, mul_zero, add_zero, sub_zero]
    rw [hq, hp]
  · haveI : Nonempty (Fin (Module.finrank ℝ E)) := Fin.pos_iff_nonempty.mp hpos
    letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨(G t).toRiemannianMetric⟩
    haveI : IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x) := inferInstance
    haveI : FiniteDimensional ℝ (TangentSpace I y) := inferInstanceAs (FiniteDimensional ℝ E)
    -- the coordinate frame of the chart at `x₀` and its Gram matrix
    let e : Fin (Module.finrank ℝ E) → TangentSpace I y := fun i => cFrame (I := I) x₀ i y
    have hb : Submodule.span ℝ (Set.range e) = ⊤ := span_cFrame_eq_top (I := I) x₀ hy
    -- the chosen frame is orthonormal, hence a basis of the tangent space
    have hon : Orthonormal ℝ (onFrame (G t) y) := by
      rw [orthonormal_iff_ite]
      intro i j
      rw [show Inner.inner ℝ (onFrame (G t) y i) (onFrame (G t) y j)
            = (G t).inner y (onFrame (G t) y i) (onFrame (G t) y j) from rfl]
      exact isONFrame_onFrame (G t) y i j
    have hcard : Fintype.card (Fin (Module.finrank ℝ E))
        = Module.finrank ℝ (TangentSpace I y) := by rw [Fintype.card_fin]; rfl
    let b : Module.Basis (Fin (Module.finrank ℝ E)) ℝ (TangentSpace I y) :=
      basisOfOrthonormalOfCardEqFinrank hon hcard
    have hbcoe : ⇑b = onFrame (G t) y := coe_basisOfOrthonormalOfCardEqFinrank hon hcard
    -- coordinates of the coordinate frame in the orthonormal frame
    let A : Matrix (Fin (Module.finrank ℝ E)) (Fin (Module.finrank ℝ E)) ℝ :=
      fun i j => b.repr (e i) j
    have hAexp : ∀ i, e i = ∑ j, A i j • onFrame (G t) y j := by
      intro i
      have h := b.sum_repr (e i)
      rw [hbcoe] at h
      exact h.symm
    have hdet : IsUnit A.det := isUnit_det_basis_repr b e hb
    -- the Gram matrix of `e` is `A * Aᵀ` (Parseval)
    have hGram : A * Matrix.transpose A = GramM (I := I) G x₀ t y := by
      rw [mul_transpose_eq_gram y (onFrame (G t) y) e (isONFrame_onFrame (G t) y) A hAexp]
      ext i j
      rfl
    -- the curvature components in `e` are the `rot A`-image of those in the orthonormal frame
    have hrot : rmFrame (G t) y e = rot A (rmFrame (G t) y (onFrame (G t) y)) :=
      rmFrame_eq_rot hLC (G t) y (onFrame (G t) y) e A hAexp
    have key := qPairGen_gram_rot_aux A hdet (rmFrame (G t) y (onFrame (G t) y))
    rw [show Submission.Diff.qPairAt (G t) y
        = qPair (rmFrame (G t) y (onFrame (G t) y)) from rfl]
    rw [show Work.Diff.GE.rmC4 (I := I) G x₀ t y = rmFrame (G t) y e from rfl]
    rw [← hGram, hrot]
    exact key.symm

end Work.Diff.GE
