import Mathlib
import Submission.Work.Diff.GE.bianchi_kato_defs
import Submission.Work.Diff.GE.curv4_trace
import Submission.Work.Diff.GE.FrameIndep
import Submission.Work.Diff.GE.rot_invariance
import Submission.Work.Diff.GE.isAlgCurv_rmFrame
import Submission.Work.Diff.GE.covRxn.mvfderiv_rmFrameField
import Submission.Work.Diff.GE.kato_geodesic_frame
import Submission.Work.Diff.EXT.laplAt_curvNormK_eq
import Submission.Work.Diff.GE.Kato3.CovRmKit

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Kato's identity for `|Rm°|²` (`Work.Diff.GE.gradSq_rmoNormSq`)

The frozen `gradSq g (rmoNormSq g) x = ∑ₘ (∂ₘ |Rm°|²)²` is the squared gradient of the
trace-free squared curvature norm `rmoNormSq g y = frobSqTF (rmC g y)`, computed in the
`Classical.epsilon`-chosen frame `onFrame g x`.  The target identifies it with the sum of squares of
`2⟪Rm°, ∇ₘRm°⟫ = 2 ∑ᵢⱼₖₗ (Rm°)ᵢⱼₖₗ (∇ₘRm°)ᵢⱼₖₗ`, the trace-free parts `tfRm g x` (of `rmC g x`)
and `tfDRm g x (onFrame g x m)` (of the array `(∇ₘRm)ᵢⱼₖₗ = covRm g x (onFrame g x m) i j k l`) being
those of `Work.Diff.GE.bianchi_kato_defs`.

The argument: take the *geodesic* orthonormal frame field `W` at `x` of
`Work.Diff.GE.kato_geodesic_frame` (globally smooth, `g`-orthonormal near `x`, equal to
`onFrame g x` at `x`, and with `∇_{Wₘx}Wⱼ = 0`).  Since `frobSqTF` is independent of the orthonormal
frame, `rmoNormSq g` agrees near `x` with the smooth function
`y ↦ frobSqTF (rmFrameField g W y)`, so the derivative may be computed with the latter.  Because the
frame is geodesic at `x`, the frame-motion corrections in `Work.Diff.GE.covRxn.mvfderiv_rmFrameField`
vanish and the derivative of the curvature array is exactly the array of `covRm`.  The chain rule
(`Work.Diff.GE.fderiv_frobSqTF`) and the elementary pairing identity for trace-free parts
(`Work.Diff.GE.tf_pairing`) then give `2⟪Rm°, ∇ₘRm°⟫` for each `m`.
-/

namespace Work.Diff.GE

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology BigOperators
open Bundle ContDiff Set VectorField CovariantDerivative Metric

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1600000

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]

/-! ## Elementary calculus: the derivative of `frobSqTF` -/

/-- Evaluation of the `(i,j,k,l)`-component of a curvature array, as a continuous linear map. -/
def projC4 {n : ℕ} (i j k l : Fin n) : Curv4 n →L[ℝ] ℝ where
  toFun R := R i j k l
  map_add' a b := rfl
  map_smul' c a := rfl

lemma projC4_apply {n : ℕ} (i j k l : Fin n) (R : Curv4 n) : projC4 i j k l R = R i j k l := rfl

/-- The derivative of `frobSq R = ∑ᵢⱼₖₗ Rᵢⱼₖₗ²`. -/
lemma hasFDerivAt_frobSq {n : ℕ} (R : Curv4 n) :
    HasFDerivAt (fun X : Curv4 n => ∑ i, ∑ j, ∑ k, ∑ l, (X i j k l)^2)
      (∑ i, ∑ j, ∑ k, ∑ l, (2 * R i j k l) • (projC4 i j k l)) R := by
  have H4 : ∀ i j k : Fin n, HasFDerivAt (fun X : Curv4 n => ∑ l, X i j k l ^ 2)
      (∑ l, (2 * R i j k l) • projC4 i j k l) R := by
    intro i j k
    refine HasFDerivAt.fun_sum (u := Finset.univ) (fun l _ => ?_)
    have h := ((projC4 i j k l).hasFDerivAt (x := R)).pow 2
    rw [show (2 : ℕ) • (projC4 i j k l) R ^ (2 - 1) = (2 : ℝ) * R i j k l from by
      rw [projC4_apply]; norm_num] at h
    exact h
  have H3 : ∀ i j : Fin n, HasFDerivAt (fun X : Curv4 n => ∑ k, ∑ l, X i j k l ^ 2)
      (∑ k, ∑ l, (2 * R i j k l) • projC4 i j k l) R := by
    intro i j
    refine HasFDerivAt.fun_sum (u := Finset.univ) (fun k _ => H4 i j k)
  have H2 : ∀ i : Fin n, HasFDerivAt (fun X : Curv4 n => ∑ j, ∑ k, ∑ l, X i j k l ^ 2)
      (∑ j, ∑ k, ∑ l, (2 * R i j k l) • projC4 i j k l) R := by
    intro i
    refine HasFDerivAt.fun_sum (u := Finset.univ) (fun j _ => H3 i j)
  refine HasFDerivAt.fun_sum (u := Finset.univ) (fun i _ => H2 i)

/-- `frobSqTF` is differentiable (it is a polynomial in the coefficients). -/
lemma differentiableAt_frobSqTF {n : ℕ} (R : Curv4 n) : DifferentiableAt ℝ frobSqTF R := by
  have h1 : HasFDerivAt (fun X : Curv4 n => ∑ i, ∑ j, ∑ k, ∑ l, (X i j k l)^2)
      (∑ i, ∑ j, ∑ k, ∑ l, (2 * R i j k l) • (projC4 i j k l)) R := hasFDerivAt_frobSq R
  have hlin : HasFDerivAt (fun X : Curv4 n => ∑ i, ∑ j, X i j i j)
      (∑ i, ∑ j, projC4 i j i j) R := by
    have h := (∑ i, ∑ j, projC4 i j i j).hasFDerivAt (x := R)
    rw [show (⇑(∑ i, ∑ j, projC4 i j i j) : Curv4 n → ℝ) = fun X => ∑ i, ∑ j, X i j i j from by
      funext X; simp only [_root_.sum_apply, projC4_apply]] at h
    exact h
  have hsq : HasFDerivAt (fun X : Curv4 n => (∑ i, ∑ j, X i j i j)^2)
      ((2 * (∑ i, ∑ j, R i j i j)) • (∑ i, ∑ j, projC4 i j i j)) R := by
    have h := hlin.pow 2
    rw [show (2 : ℕ) • (∑ i, ∑ j, R i j i j) ^ (2 - 1)
        = (2 : ℝ) * (∑ i, ∑ j, R i j i j) from by norm_num] at h
    exact h
  have hfun : frobSqTF = fun X : Curv4 n =>
      (∑ i, ∑ j, ∑ k, ∑ l, X i j k l ^ 2)
        - (2 / ((n : ℝ) * ((n : ℝ) - 1))) * (∑ i, ∑ j, X i j i j) ^ 2 := by
    funext X
    simp only [frobSqTF, frobSq, scalAlg, div_eq_mul_inv]
    ring
  have hmain : HasFDerivAt frobSqTF
      ((∑ i, ∑ j, ∑ k, ∑ l, (2 * R i j k l) • projC4 i j k l)
        - ((2 / ((n : ℝ) * ((n : ℝ) - 1)))
            • ((2 * (∑ i, ∑ j, R i j i j)) • (∑ i, ∑ j, projC4 i j i j)))) R := by
    rw [hfun]
    exact h1.sub (hsq.const_mul (2 / ((n : ℝ) * ((n : ℝ) - 1))))
  exact hmain.differentiableAt

/-- **The derivative of `frobSqTF`.**  With `frobSqTF R = |R|² - 2 (scalAlg R)²/(n(n-1))` the
squared distance of the array `R` to the constant-curvature line, the Fréchet derivative of
`frobSqTF` at `R`, evaluated on `A`, is `2 ∑ᵢⱼₖₗ Rᵢⱼₖₗ Aᵢⱼₖₗ - 4 (scalAlg R)(∑ᵢⱼ Aᵢⱼᵢⱼ)/(n(n-1))`. -/
theorem fderiv_frobSqTF {n : ℕ} (R A : Curv4 n) :
    fderiv ℝ frobSqTF R A
      = 2 * (∑ i, ∑ j, ∑ k, ∑ l, R i j k l * A i j k l)
        - 4 * scalAlg R * (∑ i, ∑ j, A i j i j) / ((n : ℝ) * ((n : ℝ) - 1)) := by
  have hquad := hasFDerivAt_frobSq (n := n) R
  have hlin : HasFDerivAt (fun X : Curv4 n => ∑ i, ∑ j, X i j i j)
      (∑ i, ∑ j, projC4 i j i j) R := by
    have h := (∑ i, ∑ j, projC4 i j i j).hasFDerivAt (x := R)
    rw [show (⇑(∑ i, ∑ j, projC4 i j i j) : Curv4 n → ℝ) = fun X => ∑ i, ∑ j, X i j i j from by
      funext X; simp only [_root_.sum_apply, projC4_apply]] at h
    exact h
  have hsq : HasFDerivAt (fun X : Curv4 n => (∑ i, ∑ j, X i j i j)^2)
      ((2 * (∑ i, ∑ j, R i j i j)) • (∑ i, ∑ j, projC4 i j i j)) R := by
    have h := hlin.pow 2
    rw [show (2 : ℕ) • (∑ i, ∑ j, R i j i j) ^ (2 - 1)
        = (2 : ℝ) * (∑ i, ∑ j, R i j i j) from by norm_num] at h
    exact h
  have hfun : frobSqTF = fun X : Curv4 n =>
      (∑ i, ∑ j, ∑ k, ∑ l, X i j k l ^ 2)
        - (2 / ((n : ℝ) * ((n : ℝ) - 1))) * (∑ i, ∑ j, X i j i j) ^ 2 := by
    funext X
    simp only [frobSqTF, frobSq, scalAlg, div_eq_mul_inv]
    ring
  have hmain : HasFDerivAt frobSqTF
      ((∑ i, ∑ j, ∑ k, ∑ l, (2 * R i j k l) • projC4 i j k l)
        - ((2 / ((n : ℝ) * ((n : ℝ) - 1)))
            • ((2 * (∑ i, ∑ j, R i j i j)) • (∑ i, ∑ j, projC4 i j i j)))) R := by
    rw [hfun]
    exact hquad.sub (hsq.const_mul (2 / ((n : ℝ) * ((n : ℝ) - 1))))
  rw [hmain.fderiv]
  simp only [_root_.sub_apply, _root_.smul_apply, _root_.sum_apply, projC4_apply, smul_eq_mul]
  rw [show (∑ i, ∑ j, ∑ k, ∑ l, 2 * R i j k l * A i j k l)
      = 2 * (∑ i, ∑ j, ∑ k, ∑ l, R i j k l * A i j k l) from by
    simp only [mul_assoc, Finset.mul_sum]]
  simp only [scalAlg]
  rw [div_eq_mul_inv]
  ring

/-! ## The pairing identity for the trace-free parts -/

/-- **Pairing identity for the trace-free parts.**  For a curvature array `R` antisymmetric in its
first pair and an array `A` antisymmetric in its last pair, the pairing of the trace-free parts
`R° = R - (scalAlg R/(n(n-1))) Iso n`, `A° = A - ((∑ᵢⱼ Aᵢⱼᵢⱼ)/(n(n-1))) Iso n` is the elementary
contraction `2 ∑ R A - 4 (scalAlg R)(∑ᵢⱼ Aᵢⱼᵢⱼ)/(n(n-1))`. -/
theorem tf_pairing {n : ℕ} (R A : Curv4 n)
    (hR : ∀ i j k l, R j i k l = - R i j k l)
    (hA : ∀ i j k l, A i j l k = - A i j k l) :
    2 * (∑ i, ∑ j, ∑ k, ∑ l, R i j k l * A i j k l)
        - 4 * scalAlg R * (∑ i, ∑ j, A i j i j) / ((n : ℝ) * ((n : ℝ) - 1))
      = 2 * (∑ i, ∑ j, ∑ k, ∑ l,
          (R i j k l - (scalAlg R / ((n : ℝ) * ((n : ℝ) - 1))) * Iso n i j k l)
            * (A i j k l - ((∑ i', ∑ j', A i' j' i' j') / ((n : ℝ) * ((n : ℝ) - 1)))
                * Iso n i j k l)) := by
  have hRIso : (∑ i, ∑ j, ∑ k, ∑ l, R i j k l * Iso n i j k l) = 2 * scalAlg R :=
    rm_iso_trace R hR
  have hAIso : (∑ i, ∑ j, ∑ k, ∑ l, A i j k l * Iso n i j k l) = 2 * (∑ i, ∑ j, A i j i j) := by
    have h1 : (∑ i, ∑ j, ∑ k, ∑ l, A i j k l * Iso n i j k l)
        = ∑ i, ∑ j, (A i j i j - A i j j i) := by
      refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
      exact iso_pairing_step A i j
    rw [h1]
    have h2 : ∀ i j, A i j j i = - A i j i j := by
      intro i j
      have := hA i j j i
      linarith
    calc (∑ i, ∑ j, (A i j i j - A i j j i)) = ∑ i, ∑ j, (2 * A i j i j) := by
          refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
          rw [h2 i j]; ring
      _ = 2 * (∑ i, ∑ j, A i j i j) := by
          simp only [Finset.mul_sum]
  have hIsoIso : (∑ i, ∑ j, ∑ k, ∑ l, Iso n i j k l * Iso n i j k l)
      = 2 * ((n : ℝ) * ((n : ℝ) - 1)) := iso_norm_sq n
  have hexp : ∀ a b : ℝ,
      (∑ i, ∑ j, ∑ k, ∑ l, (R i j k l - a * Iso n i j k l) * (A i j k l - b * Iso n i j k l))
        = (∑ i, ∑ j, ∑ k, ∑ l, R i j k l * A i j k l)
          - b * (∑ i, ∑ j, ∑ k, ∑ l, R i j k l * Iso n i j k l)
          - a * (∑ i, ∑ j, ∑ k, ∑ l, A i j k l * Iso n i j k l)
          + a * b * (∑ i, ∑ j, ∑ k, ∑ l, Iso n i j k l * Iso n i j k l) := by
    intro a b
    have hp : ∀ i j k l, (R i j k l - a * Iso n i j k l) * (A i j k l - b * Iso n i j k l)
        = R i j k l * A i j k l - b * (R i j k l * Iso n i j k l)
          - a * (A i j k l * Iso n i j k l) + a * b * (Iso n i j k l * Iso n i j k l) := by
      intro i j k l; ring
    simp only [hp, Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum]
  rw [hexp (scalAlg R / ((n : ℝ) * ((n : ℝ) - 1)))
    ((∑ i, ∑ j, A i j i j) / ((n : ℝ) * ((n : ℝ) - 1))), hRIso, hAIso, hIsoIso]
  by_cases hd : (n : ℝ) * ((n : ℝ) - 1) = 0
  · rw [hd]
    simp only [div_zero, mul_zero, zero_mul, sub_zero, add_zero]
  · field_simp
    ring

/-! ## The frame-independence of `frobSqTF` and the localisation of `rmoNormSq` -/

/-- `frobSqTF (rmFrame g x e)` does not depend on the choice of `g`-orthonormal frame `e`. -/
theorem frobSqTF_rmFrame_eq_of_isONFrame (hLC : LCSmooth I M) (g : SMet I M) (x : M)
    (e e' : Fin (Module.finrank ℝ E) → TangentSpace I x)
    (he : IsONFrame g x e) (he' : IsONFrame g x e') :
    frobSqTF (rmFrame g x e) = frobSqTF (rmFrame g x e') := by
  obtain ⟨A, hA, hAe⟩ := onFrame_orthogonal_change g x e e' he he'
  rw [rmFrame_eq_rot hLC g x e e' A hAe]
  exact (rot_invariance A hA (rmFrame g x e)).2.2.2.symm

/-- Near `x`, the frozen `rmoNormSq g` agrees with the expression computed in the frame field `W`. -/
theorem rmoNormSq_eventuallyEq_rmFrameField (hLC : LCSmooth I M) (g : SMet I M) (x : M)
    (W : Π y : M, Fin (Module.finrank ℝ E) → TangentSpace I y)
    (hON : ∀ᶠ y in 𝓝 x, IsONFrame g y (W y)) :
    rmoNormSq g =ᶠ[𝓝 x] fun y => frobSqTF (Rxn.rmFrameField g W y) := by
  filter_upwards [hON] with y hy
  show frobSqTF (rmFrame g y (onFrame g y)) = frobSqTF (Rxn.rmFrameField g W y)
  rw [show Rxn.rmFrameField g W y = rmFrame g y (W y) from rfl]
  exact (frobSqTF_rmFrame_eq_of_isONFrame hLC g y (W y) (onFrame g y) hy
    (isONFrame_onFrame g y)).symm

/-- Functions which agree near `x` have the same derivative at `x`. -/
theorem mvfderiv_congr_of_eventuallyEq {f₁ f : M → ℝ} {x : M} (hL : f₁ =ᶠ[𝓝 x] f) :
    mvfderiv I f₁ x = mvfderiv I f x := by
  have hx : f₁ x = f x := hL.self_of_nhds
  have h := Filter.EventuallyEq.mfderiv_eq (I := I) (I' := 𝓘(ℝ, ℝ)) (f := f) (f₁ := f₁) hL
  simp only [mvfderiv]
  rw [h, hx]
  rfl


/-! ## A geodesic orthonormal frame field at `x`

`Work.Diff.GE.kato_geodesic_frame` (and its counterpart `Work.Diff.EXT.geodesic_frame_aux`) provide
globally smooth vector fields which are a `g`-orthonormal frame near `x`, agree with `onFrame g x`
at `x`, and are *geodesic* at `x` (`∇_{W m x} W j = 0`).  Its proof rests on the jet correction
`Work.Diff.EXT.lcOf_jet_correction_aux` (a smooth field with prescribed value and vanishing
covariant derivative at `x`), which in turn rests on a covector jet lemma.  The ingredients are
reproduced here without the `[I.Boundaryless]`/`[CompactSpace M]` hypotheses carried by the
original statements (they are not needed for the argument), so that the result is available in the
generality of the frozen statement.
-/

/-- **A globally smooth function with prescribed value and derivative at a point.** -/
theorem jetCov (x : M) (ξ : TangentSpace I x →L[ℝ] ℝ) :
    ∃ f : M → ℝ, CMDiff ∞ f ∧ f x = 0 ∧ mvfderiv I f x = ξ := by
  classical
  set D : TangentSpace I x →L[ℝ] E := mfderiv I 𝓘(ℝ,E) (extChartAt I x) x with hDdef
  have hD : D.IsInvertible :=
    isInvertible_mfderiv_extChartAt (I := I) (x := x) (mem_extChartAt_source x)
  set ℓ : E →L[ℝ] ℝ := ξ.comp D.inverse with hℓdef
  have hℓD : ℓ.comp D = ξ := by
    ext v
    simp only [ContinuousLinearMap.comp_apply, hℓdef]
    rw [hD.inverse_apply_self v]
  obtain ⟨ψ, -, hψsupp⟩ : ∃ ψ : SmoothBumpFunction I x,
      True ∧ tsupport (ψ : M → ℝ) ⊆ (chartAt H x).source :=
    (SmoothBumpFunction.nhds_basis_tsupport (I := I) x).mem_iff.mp
      ((chartAt H x).open_source.mem_nhds (mem_chart_source H x))
  set g : M → ℝ := fun y => ℓ ((extChartAt I x) y - (extChartAt I x) x) with hg
  have hgOn : ContMDiffOn I 𝓘(ℝ,ℝ) ∞ g (chartAt H x).source := by
    have h1 : ContMDiffOn I 𝓘(ℝ,E) ∞ (fun y : M => (extChartAt I x) y - (extChartAt I x) x)
        (chartAt H x).source :=
      (contMDiffOn_extChartAt (I := I) (x := x)).sub_const _
    exact (ℓ.contMDiff).comp_contMDiffOn h1
  have hgcd : CMDiff ∞ (fun y : M => (ψ : M → ℝ) y • g y) := ψ.contMDiff_smul hgOn
  have hgd : MDifferentiableAt I 𝓘(ℝ,ℝ) g x :=
    ((hgOn x (mem_chart_source H x)).contMDiffAt
      ((chartAt H x).open_source.mem_nhds (mem_chart_source H x))).mdifferentiableAt (by simp)
  have hψd : MDifferentiableAt I 𝓘(ℝ,ℝ) (fun y : M => (ψ : M → ℝ) y) x :=
    ψ.contMDiff.mdifferentiableAt (by simp)
  have hg0 : g x = 0 := by simp [hg, map_sub]
  have hψx : (ψ : M → ℝ) x = 1 := SmoothBumpFunction.eq_one ψ
  have hgderiv : mvfderiv I g x = ξ := by
    rw [hg, Work.Diff.C.mvfderiv_affine_chart]
    exact hℓD
  refine ⟨fun y => (ψ : M → ℝ) y * g y, ?_, ?_, ?_⟩
  · simpa only [smul_eq_mul] using hgcd
  · simp only [hg, SmoothBumpFunction.eq_one, sub_self, map_zero, mul_zero]
  · have hmul := mvfderiv_mul (f := fun y : M => (ψ : M → ℝ) y) (g := g) hψd hgd
    show mvfderiv I ((fun y : M => (ψ : M → ℝ) y) * g) x = ξ
    rw [hmul, hψx, hg0, one_smul, zero_smul, add_zero]
    exact hgderiv

/-- **Jet correction for the Levi-Civita connection.**  Every tangent vector at `x` extends to a
globally smooth vector field `Y` with `Y x = u` and `∇Y|_x = 0`. -/
theorem lcOf_jetCorrection (g : SMet I M) (x : M) (u : TangentSpace I x) :
    ∃ Y : Π y : M, TangentSpace I y,
      CMDiff ∞ (T% Y) ∧ Y x = u ∧ lcOf g Y x = 0 := by
  classical
  set b : Module.Basis (Fin (Module.finrank ℝ E)) ℝ (TangentSpace I x) :=
    Module.finBasis ℝ (TangentSpace I x) with hb
  set Z : Π y : M, TangentSpace I y := smoothExt x u with hZ
  have hZs : CMDiff ∞ (T% Z) := smoothExt_cmdiff x u
  have hZx : Z x = u := smoothExt_apply x u
  set A : TangentSpace I x →L[ℝ] TangentSpace I x := lcOf g Z x with hA
  have hf : ∀ i : Fin (Module.finrank ℝ E),
      ∃ f : M → ℝ, CMDiff ∞ f ∧ f x = 0 ∧
        mvfderiv I f x = LinearMap.toContinuousLinearMap (b.coord i) :=
    fun i => jetCov x (LinearMap.toContinuousLinearMap (b.coord i))
  choose f hfs hfx hfderiv using hf
  set W' : Fin (Module.finrank ℝ E) → Π y : M, TangentSpace I y :=
    fun i => smoothExt x (-(A (b i))) with hW'
  have hW's : ∀ i, CMDiff ∞ (T% (W' i)) :=
    fun i => smoothExt_cmdiff x (-(A (b i)))
  have hW'x : ∀ i, W' i x = -(A (b i)) :=
    fun i => smoothExt_apply x (-(A (b i)))
  set S : Π y : M, TangentSpace I y := ∑ i, f i • W' i with hS
  have hSs : CMDiff ∞ (T% S) := by
    rw [hS]
    have key : ∀ t : Finset (Fin (Module.finrank ℝ E)), CMDiff ∞ (T% (∑ i ∈ t, f i • W' i)) := by
      intro t
      induction t using Finset.induction_on with
      | empty =>
        rw [Finset.sum_empty]
        exact cmDiff_zeroField (I := I) (M := M)
      | insert a t ha ih =>
        rw [Finset.sum_insert ha]
        exact ((hfs a).smul_section (hW's a)).add_section ih
    exact key Finset.univ
  have hSx : S x = 0 := by
    rw [hS]
    simp only [Finset.sum_apply, Pi.smul_apply']
    refine Finset.sum_eq_zero (fun i _ => ?_)
    rw [hfx i, zero_smul]
  have hSderiv : lcOf g S x = -A := by
    ext v
    rw [hS, kato_lcOf_sum_apply g x Finset.univ f W'
      (fun i _ => hfs i) (fun i _ => hW's i) v]
    have hterm : ∀ i : Fin (Module.finrank ℝ E),
        f i x • lcOf g (W' i) x v + mvfderiv I (f i) x v • W' i x
          = -(b.coord i v) • (A (b i)) := by
      intro i
      rw [hfx i, zero_smul, zero_add, hfderiv i, hW'x i]
      simp only [LinearMap.coe_toContinuousLinearMap', Module.Basis.coord_apply]
      rw [smul_neg, neg_smul]
    rw [Finset.sum_congr rfl (fun i _ => hterm i)]
    have hrep : (∑ i, (b.coord i v) • b i) = v := by
      simpa only [Module.Basis.coord_apply] using b.sum_repr v
    have hgoal : -(A v) = ∑ i : Fin (Module.finrank ℝ E), (-(b.coord i v)) • (A (b i)) := by
      conv_lhs => rw [← hrep]
      rw [map_sum, ← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [map_smul, ← neg_smul]
    exact hgoal.symm
  refine ⟨Z + S, ?_, ?_, ?_⟩
  · exact hZs.add_section hSs
  · show Z x + S x = u
    rw [hZx, hSx, add_zero]
  · have h1 : MDiffAt (T% Z) x := hZs.contMDiffAt.mdifferentiableAt (by simp)
    have h2 : MDiffAt (T% S) x := hSs.contMDiffAt.mdifferentiableAt (by simp)
    rw [(lcOf g).isCovariantDerivativeOn.add h1 h2, hSderiv, ← hA]
    exact add_neg_cancel A

/-- **A geodesic orthonormal frame at a point.**  There are globally smooth vector fields `W i` which
are a `g`-orthonormal frame near `x`, with `W i x = onFrame g x i` and `∇_{W m x} W j = 0`. -/
theorem geodesicFrame (g : SMet I M) (x : M) :
    ∃ W : Fin (Module.finrank ℝ E) → (Π y : M, TangentSpace I y),
      (∀ i, CMDiff ∞ (T% (W i))) ∧
      (∀ᶠ y in 𝓝 x, IsONFrame g y (fun i => W i y)) ∧
      (∀ i, W i x = onFrame g x i) ∧
      (∀ m j, lcOf g (W j) x (W m x) = 0) := by
  classical
  set e : katoIdx E → TangentSpace I x := onFrame g x with hedef
  have he : IsONFrame g x e := isONFrame_onFrame g x
  choose V hVs hVx hVc using fun i => lcOf_jetCorrection g x (e i)
  have key : ∀ m : ℕ, ∀ i : katoIdx E, i.val < m →
      (CMDiff ∞ (T% (katoFrame g x V i)))
      ∧ (katoFrame g x V i x = V i x)
      ∧ (lcOf g (katoFrame g x V i) x = 0)
      ∧ (∀ᶠ y in 𝓝 x, g.inner y (katoFrame g x V i y) (katoFrame g x V i y) = 1)
      ∧ (∀ᶠ y in 𝓝 x, ∀ k, k.val < i.val →
          g.inner y (katoFrame g x V i y) (katoFrame g x V k y) = 0) := by
    intro m
    induction m with
    | zero => intro i hi; exact absurd hi (Nat.not_lt_zero _)
    | succ m ih =>
      intro i hi
      rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hlt | heq
      · exact ih i hlt
      · have hIH : ∀ j, j.val < i.val →
            (CMDiff ∞ (T% (katoFrame g x V j)))
            ∧ (katoFrame g x V j x = V j x)
            ∧ (lcOf g (katoFrame g x V j) x = 0)
            ∧ (∀ᶠ y in 𝓝 x, g.inner y (katoFrame g x V j y) (katoFrame g x V j y) = 1)
            ∧ (∀ᶠ y in 𝓝 x, ∀ k, k.val < j.val →
                g.inner y (katoFrame g x V j y) (katoFrame g x V k y) = 0) :=
          fun j hj => ih j (by rw [← heq]; exact hj)
        obtain ⟨hUs, hGs⟩ :=
          kato_smooth g V (katoFrame g x V) i (hVs i) (fun j hj => (hIH j hj).1)
        have hON : ∀ j, j.val < i.val → g.inner x (V i x) (V j x) = 0 := by
          intro j hj
          have hne : i ≠ j := by
            intro hij; rw [← hij] at hj; exact absurd hj (Nat.lt_irrefl _)
          rw [hVx i, hVx j, he i j, ite_eq_right hne]
        have hUx : katoU g V (katoFrame g x V) i x = V i x :=
          katoU_apply_x g x V (katoFrame g x V) i (fun j hj => (hIH j hj).2.1) hON
        have hV1 : g.inner x (V i x) (V i x) = 1 := by
          rw [hVx i, he i i, ite_eq_left rfl]
        have hfx : 0 < katoGram g V (katoFrame g x V) i x := by
          rw [katoGram_apply_x g x V (katoFrame g x V) i hUx hV1]; norm_num
        obtain ⟨hFpos, hFs, hCs, hCeq, hFx, hFeq⟩ :=
          kato_smooth_norm g x V (katoFrame g x V) i hGs hfx
        have hUc : lcOf g (katoU g V (katoFrame g x V) i) x = 0 :=
          katoU_cov_zero g x V (katoFrame g x V) i (hVs i)
            (fun j hj => (hIH j hj).1) (hVc i) (fun j hj => (hIH j hj).2.2.1)
            (fun j hj => (hIH j hj).2.1) hON
        have hdf := katoGram_mvfderiv_zero g x V (katoFrame g x V) i hUs hUc
        have hψs : CMDiff ∞ (katoBump (I := I) (katoGram g V (katoFrame g x V) i) x) :=
          (katoBump_spec hGs hfx).1
        have hdF := katoNorm_mvfderiv_zero g x V (katoFrame g x V) i hGs hψs hdf
        have hdC := katoC_mvfderiv_zero g x V (katoFrame g x V) i hFs hFpos hdF
        have hCx : katoC g x V (katoFrame g x V) i x = 1 :=
          katoC_apply_x g x V (katoFrame g x V) i
            (by rw [hFx, katoGram_apply_x g x V (katoFrame g x V) i hUx hV1])
        have hWx : katoFrame g x V i x = V i x := by
          rw [katoFrame_eq g x V i]
          show katoC g x V (katoFrame g x V) i x • katoU g V (katoFrame g x V) i x = V i x
          rw [hCx, hUx, one_smul]
        have hWs : CMDiff ∞ (T% (katoFrame g x V i)) := by
          rw [katoFrame_eq g x V i]
          exact hCs.smul_section hUs
        have hWc : lcOf g (katoFrame g x V i) x = 0 := by
          have hUsd : MDiffAt (T% (katoU g V (katoFrame g x V) i)) x :=
            hUs.contMDiffAt.mdifferentiableAt (by simp)
          have hCsd : MDifferentiableAt I 𝓘(ℝ,ℝ) (katoC g x V (katoFrame g x V) i) x :=
            hCs.contMDiffAt.mdifferentiableAt (by simp)
          have hdC0 : mvfderiv I (katoC g x V (katoFrame g x V) i) x = 0 := by
            ext v; exact hdC v
          rw [katoFrame_eq g x V i,
            show katoStep g x V (katoFrame g x V) i
              = (katoC g x V (katoFrame g x V) i) • (katoU g V (katoFrame g x V) i) from rfl,
            (lcOf g).isCovariantDerivativeOn.leibniz hUsd hCsd, hdC0, hUc, hCx]
          simp
        have hdiag_prev : ∀ᶠ y in 𝓝 x, ∀ j, j.val < i.val →
            g.inner y (katoFrame g x V j y) (katoFrame g x V j y) = 1 := by
          rw [Filter.eventually_all]
          intro j
          by_cases hj : j.val < i.val
          · filter_upwards [(hIH j hj).2.2.2.1] with y hy
            exact fun _ => hy
          · exact Filter.Eventually.of_forall fun y h => absurd h hj
        have hoff_prev : ∀ᶠ y in 𝓝 x, ∀ j, j.val < i.val → ∀ k, k.val < j.val →
            g.inner y (katoFrame g x V j y) (katoFrame g x V k y) = 0 := by
          rw [Filter.eventually_all]
          intro j
          by_cases hj : j.val < i.val
          · filter_upwards [(hIH j hj).2.2.2.2] with y hy
            exact fun _ => hy
          · exact Filter.Eventually.of_forall fun y h => absurd h hj
        have hbump1 : ∀ᶠ y in 𝓝 x,
            katoBump (I := I) (katoGram g V (katoFrame g x V) i) x y = 1 :=
          (katoBump_spec hGs hfx).2.2.2.2
        have hfpos_ev : ∀ᶠ y in 𝓝 x, 0 < katoGram g V (katoFrame g x V) i y :=
          (hGs x).continuousAt.preimage_mem_nhds (isOpen_Ioi.mem_nhds hfx)
        have hdiag_i : ∀ᶠ y in 𝓝 x,
            g.inner y (katoFrame g x V i y) (katoFrame g x V i y) = 1 := by
          filter_upwards [hbump1, hfpos_ev, hdiag_prev, hoff_prev] with y hb hf hp ho
          rw [katoFrame_eq g x V i]
          exact (kato_orthonormal_algebra g x V (katoFrame g x V) i y hb hf hp ho).1
        have hoff_i : ∀ᶠ y in 𝓝 x, ∀ k, k.val < i.val →
            g.inner y (katoFrame g x V i y) (katoFrame g x V k y) = 0 := by
          filter_upwards [hbump1, hfpos_ev, hdiag_prev, hoff_prev] with y hb hf hp ho
          intro k hk
          rw [katoFrame_eq g x V i]
          exact (kato_orthonormal_algebra g x V (katoFrame g x V) i y hb hf hp ho).2 k hk
        exact ⟨hWs, hWx, hWc, hdiag_i, hoff_i⟩
  refine ⟨katoFrame g x V, ?_, ?_, ?_, ?_⟩
  · intro i
    exact (key (i.val + 1) i (Nat.lt_succ_self _)).1
  · refine isONFrame_of_diag_off g x (katoFrame g x V) ?_ ?_
    · rw [Filter.eventually_all]
      intro i
      exact (key (i.val + 1) i (Nat.lt_succ_self _)).2.2.2.1
    · rw [Filter.eventually_all]
      intro i
      exact (key (i.val + 1) i (Nat.lt_succ_self _)).2.2.2.2
  · intro i
    rw [(key (i.val + 1) i (Nat.lt_succ_self _)).2.1]
    exact hVx i
  · intro m j
    rw [(key (m.val + 1) m (Nat.lt_succ_self _)).2.1,
      (key (j.val + 1) j (Nat.lt_succ_self _)).2.2.1]
    rw [hVx m]
    rfl

/-! ## The derivative of the curvature array in a geodesic frame field -/

/-- For a smooth frame field `W` whose covariant derivative at `x` in the direction `v` vanishes,
the derivative of the curvature array `y ↦ rmFrameField g W y` is the array of `covRm`.  This is
`Work.Diff.GE.covRxn.mvfderiv_rmFrameField` with the four frame-motion corrections killed. -/
theorem mvfderiv_rmFrameField_eq_covRm (hLC : LCSmooth I M) (g : SMet I M) (x : M)
    (W : Π y : M, Fin (Module.finrank ℝ E) → TangentSpace I y)
    (hW : ∀ i, Rxn.SmoothField (fun y : M => W y i)) (v : TangentSpace I x)
    (hWx : ∀ i, W x i = onFrame g x i)
    (hconn : ∀ i, lcOf g (fun y : M => W y i) x v = 0) :
    mvfderiv I (fun y : M => Rxn.rmFrameField g W y) x v
      = fun i j k l =>
          covRm g x v (onFrame g x i) (onFrame g x j) (onFrame g x k) (onFrame g x l) := by
  have h0f : ∀ a b c d : TangentSpace I x, rmP g x 0 b c d = 0 := by
    intro a b c d
    rw [show (0 : TangentSpace I x) = (0 : ℝ) • a from (zero_smul ℝ a).symm,
      rmP_smul_fst (g := g) hLC x (0 : ℝ) a b c d]
    simp
  have h0s : ∀ a b c d : TangentSpace I x, rmP g x a 0 c d = 0 := by
    intro a b c d
    rw [show (0 : TangentSpace I x) = (0 : ℝ) • b from (zero_smul ℝ b).symm,
      rmP_smul_snd (g := g) hLC x (0 : ℝ) a b c d]
    simp
  have h0t : ∀ a b c d : TangentSpace I x, rmP g x a b 0 d = 0 := by
    intro a b c d
    rw [show (0 : TangentSpace I x) = (0 : ℝ) • c from (zero_smul ℝ c).symm,
      rmP_smul_thd (g := g) hLC x (0 : ℝ) a b c d]
    simp
  have h0h : ∀ a b c d : TangentSpace I x, rmP g x a b c 0 = 0 := by
    intro a b c d
    rw [show (0 : TangentSpace I x) = (0 : ℝ) • d from (zero_smul ℝ d).symm,
      rmP_smul_fth (g := g) hLC x (0 : ℝ) a b c d]
    simp
  rw [covRxn.mvfderiv_rmFrameField (I := I) (M := M) hLC g W hW x v]
  funext i j k l
  rw [hWx i, hWx j, hWx k, hWx l, hconn i, hconn j, hconn k, hconn l]
  rw [h0f (onFrame g x i) (onFrame g x j) (onFrame g x k) (onFrame g x l),
    h0s (onFrame g x i) (onFrame g x j) (onFrame g x k) (onFrame g x l),
    h0t (onFrame g x i) (onFrame g x j) (onFrame g x k) (onFrame g x l),
    h0h (onFrame g x i) (onFrame g x j) (onFrame g x k) (onFrame g x l)]
  simp

/-! ## The main identity -/

/-- **Kato: the gradient of `|Rm°|²` is `2⟪Rm°, ∇Rm°⟫`.** -/
theorem gradSq_rmoNormSq
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I ∞ M]
    (hLC : LCSmooth I M) (g : SMet I M) (x : M) :
    gradSq g (rmoNormSq g) x
      = ∑ m, (2 * ∑ i, ∑ j, ∑ k, ∑ l,
          tfRm g x i j k l * tfDRm g x (onFrame g x m) i j k l) ^ 2 := by
  classical
  -- the geodesic orthonormal frame field at `x`
  obtain ⟨W₀, hW₀sm, hW₀ON, hW₀x, hW₀geo⟩ := geodesicFrame (I := I) (M := M) g x
  let W : Π y : M, Fin (Module.finrank ℝ E) → TangentSpace I y := fun y i => W₀ i y
  have hWsm : ∀ i, Rxn.SmoothField (fun y : M => W y i) := fun i => hW₀sm i
  have hWON : ∀ᶠ y in 𝓝 x, IsONFrame g y (W y) := hW₀ON
  have hWx : ∀ i, W x i = onFrame g x i := fun i => hW₀x i
  have hWconn : ∀ (i m : Fin (Module.finrank ℝ E)),
      lcOf g (fun y : M => W y i) x (onFrame g x m) = 0 := by
    intro i m
    rw [← hWx m]
    exact hW₀geo m i
  -- the localisation
  have hev : rmoNormSq g =ᶠ[𝓝 x] fun y => frobSqTF (Rxn.rmFrameField g W y) :=
    rmoNormSq_eventuallyEq_rmFrameField hLC g x W hWON
  have hder : mvfderiv I (rmoNormSq g) x
      = mvfderiv I (fun y => frobSqTF (Rxn.rmFrameField g W y)) x :=
    mvfderiv_congr_of_eventuallyEq hev
  -- the derivative of the curvature array in the geodesic frame
  have hRm_mdiff : MDifferentiableAt I 𝓘(ℝ, Curv4 (Module.finrank ℝ E))
      (fun y : M => Rxn.rmFrameField g W y) x :=
    (covRxn.contMDiffAt_rmFrameField (I := I) (M := M) hLC g W hWsm x).mdifferentiableAt (by simp)
  have hRmx : Rxn.rmFrameField g W x = rmC g x := by
    funext i j k l
    show rmP g x (W x i) (W x j) (W x k) (W x l)
      = rmP g x (onFrame g x i) (onFrame g x j) (onFrame g x k) (onFrame g x l)
    rw [hWx i, hWx j, hWx k, hWx l]
  have hAlgCurv : IsAlgCurv (rmC g x) :=
    isAlgCurv_rmFrame (I := I) (M := M) g ((hLC g).1.some) ((hLC g).2.1) ((hLC g).2.2) x
      (onFrame g x)
  -- the derivative of `frobSqTF ∘ Rm`
  have hchain : ∀ m : Fin (Module.finrank ℝ E),
      mvfderiv I (fun y => frobSqTF (Rxn.rmFrameField g W y)) x (onFrame g x m)
        = 2 * (∑ i, ∑ j, ∑ k, ∑ l,
            tfRm g x i j k l * tfDRm g x (onFrame g x m) i j k l) := by
    intro m
    have hG : MDifferentiableAt 𝓘(ℝ, Curv4 (Module.finrank ℝ E)) 𝓘(ℝ, ℝ) frobSqTF
        (Rxn.rmFrameField g W x) :=
      (differentiableAt_frobSqTF (Rxn.rmFrameField g W x)).mdifferentiableAt
    have hcomp : mvfderiv I (fun y => frobSqTF (Rxn.rmFrameField g W y)) x (onFrame g x m)
        = fderiv ℝ frobSqTF (Rxn.rmFrameField g W x)
            (mvfderiv I (fun y => Rxn.rmFrameField g W y) x (onFrame g x m)) := by
      rw [show (fun y : M => frobSqTF (Rxn.rmFrameField g W y))
          = frobSqTF ∘ (fun y : M => Rxn.rmFrameField g W y) from rfl]
      rw [mvfderiv_comp_apply (I := 𝓘(ℝ, Curv4 (Module.finrank ℝ E))) (I' := I)
        (f := fun y : M => Rxn.rmFrameField g W y) (g := frobSqTF) x hG hRm_mdiff
        (onFrame g x m)]
      rw [mvfderiv_eq_fderiv]
      rfl
    rw [hcomp,
      mvfderiv_rmFrameField_eq_covRm (I := I) (M := M) hLC g x W hWsm (onFrame g x m) hWx
        (fun i => hWconn i m),
      fderiv_frobSqTF, hRmx]
    -- the algebra
    have hA : ∀ i j k l : Fin (Module.finrank ℝ E),
        covRm g x (onFrame g x m) (onFrame g x i) (onFrame g x j) (onFrame g x l)
            (onFrame g x k)
          = - covRm g x (onFrame g x m) (onFrame g x i) (onFrame g x j) (onFrame g x k)
              (onFrame g x l) := by
      intro i j k l
      have h := Kato3.covRm_skew_last (I := I) (M := M) hLC g x (onFrame g x m) (onFrame g x i)
        (onFrame g x j) (onFrame g x k) (onFrame g x l)
      linarith
    rw [tf_pairing (rmC g x)
      (fun i j k l => covRm g x (onFrame g x m) (onFrame g x i) (onFrame g x j)
        (onFrame g x k) (onFrame g x l)) hAlgCurv.1 hA]
    simp only [tfRm, tfDRm, scalAt]
  -- assemble
  simp only [gradSq]
  rw [show (∑ i, (mvfderiv I (rmoNormSq g) x (onFrame g x i)) ^ 2)
      = ∑ i, (mvfderiv I (fun y => frobSqTF (Rxn.rmFrameField g W y)) x
          (onFrame g x i)) ^ 2 from by rw [hder]]
  exact Finset.sum_congr rfl (fun m _ => by rw [hchain m])

end Work.Diff.GE
