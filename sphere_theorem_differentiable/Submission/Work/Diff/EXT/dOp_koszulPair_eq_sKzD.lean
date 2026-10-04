import Mathlib
import Submission.Work.Diff.EXT.ricPhiPartialDefs
import Submission.Work.Diff.GE.norms_defs
import Submission.Work.Diff.T.mvfderiv_frameVector_real
import Submission.Work.Diff.T.clairaut_fderiv_apply
import Submission.Work.Diff.EXT.contMDiffAt_mvfderiv_gen
import Submission.Work.Diff.EXT.contDiffAt_chartMat_of_jointSmooth
import Submission.Commons.Geometry.Manifold.Riemannian.metricCompatible_scaleMetric

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The second coordinate derivative of the Koszul pairing

`Work.Diff.GE.koszulPair (fun _ => g) x₀ b d c` is the *lowered* Koszul Christoffel pairing
`½(∂_b g_{dc} + ∂_d g_{bc} - ∂_c g_{bd})`, read in the coordinate frame of the chart at `x₀`; its
first coordinate derivative in the direction `a` is the corresponding combination
`sKzD (dJet2 g x₀ y) a b d c` of the second coordinate partials of the chart matrix
`chartMatFun g x₀`.

The proof has three layers.

* `kz_contMDiffAt_pair`: the metric coefficients of the chart frame are `C^∞` at every point of the
  chart source (Mathlib's `ContMDiffAt.clm_bundle_apply₂` for the metric `g`).
* `kz_mvfderiv_pair_eq`: the first coordinate partial of those coefficients is the corresponding
  coordinate partial of the chart matrix — `Work.Diff.T.mvfderiv_frameVector_real` combined with the
  definition of `chartMatFun` and the commutation of `fderiv` with a matrix component.
* `kz_second`: consequently the *second* coordinate partial of the coefficients, written as a
  manifold derivative of a manifold derivative, is the corresponding second partial of the chart
  matrix.  The inner derivative is differentiable along the chart (from
  `Work.Diff.EXT.contMDiffAt_mvfderiv_gen`), the outer derivative is read in the chart by
  `Work.Diff.T.mvfderiv_frameVector_real`, the chart representative is replaced by the equivalent
  one via `Filter.EventuallyEq.fderiv_eq`, and the resulting Fréchet derivative is identified with
  `dJet2` by `kz_fderiv_fderiv_apply_coord`.
-/

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology BigOperators
open Bundle ContDiff Set VectorField CovariantDerivative Metric

namespace Work.Diff.EXT

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [CompleteSpace E]
variable {H' : Type*} [TopologicalSpace H'] {I : ModelWithCorners ℝ E H'}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H' M] [IsManifold I (⊤ : ℕ∞) M]
variable [I.Boundaryless] [T2Space M]

/-! ### The metric coefficients of the chart frame are smooth -/

/-- The metric coefficients of `g` in the coordinate frame of the chart at `x₀` are `C^∞` at every
point of the chart source. -/
lemma kz_contMDiffAt_pair (g : Submission.Diff.SMet I M) (x₀ : M) {p : M}
    (hp : p ∈ (chartAt H' x₀).source) (i j : Fin (Module.finrank ℝ E)) :
    ContMDiffAt I 𝓘(ℝ,ℝ) ∞
      (fun q : M => g.inner q (cvec (I := I) x₀ q (bB (E := E) i))
        (cvec (I := I) x₀ q (bB (E := E) j))) p := by
  have hψ : CMDiffAt ∞ (fun m : M => TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
      (E := fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) m (g.inner m)) p :=
    g.contMDiff.contMDiffAt
  have hv : CMDiffAt ∞ (fun m : M => TotalSpace.mk' E
      (E := fun x : M => TangentSpace I x) m (cvec (I := I) x₀ m (bB (E := E) i))) p :=
    contMDiffAt_frameVector (I := I) x₀ (bB (E := E) i) hp
  have hw : CMDiffAt ∞ (fun m : M => TotalSpace.mk' E
      (E := fun x : M => TangentSpace I x) m (cvec (I := I) x₀ m (bB (E := E) j))) p :=
    contMDiffAt_frameVector (I := I) x₀ (bB (E := E) j) hp
  have hmain := ContMDiffAt.clm_bundle_apply₂ (𝕜 := ℝ) (B := M) (F₁ := E) (F₂ := E) (F₃ := ℝ)
    (E₁ := fun x : M => TangentSpace I x) (E₂ := fun x : M => TangentSpace I x)
    (E₃ := Bundle.Trivial M ℝ) (b := id) (ψ := fun m : M => g.inner m)
    (v := fun m : M => cvec (I := I) x₀ m (bB (E := E) i))
    (w := fun m : M => cvec (I := I) x₀ m (bB (E := E) j)) (x := p) hψ hv hw
  simp only [contMDiffAt_totalSpace] at hmain
  exact hmain.2

/-- The chart matrix of a smooth metric is `C^∞` as a function of the chart coordinate. -/
lemma kz_contDiffAt_chartMatFun (g : Submission.Diff.SMet I M) (x₀ : M) {y : E}
    (hy : y ∈ (extChartAt I x₀).target) :
    ContDiffAt ℝ (⊤ : ℕ∞) (chartMatFun g x₀) y := by
  have hsymm : ContMDiffAt 𝓘(ℝ,E) I ∞ (extChartAt I x₀).symm y :=
    (contMDiffOn_extChartAt_symm (I := I) x₀).contMDiffAt
      ((isOpen_extChartAt_target (I := I) x₀).mem_nhds hy)
  rw [contDiffAt_pi]
  intro a
  rw [contDiffAt_pi]
  intro b
  have hp : (extChartAt I x₀).symm y ∈ (chartAt H' x₀).source := by
    have h1 : (extChartAt I x₀).symm y ∈ (extChartAt I x₀).source :=
      (extChartAt I x₀).map_target hy
    rwa [extChartAt_source] at h1
  have hcomp := (kz_contMDiffAt_pair (I := I) g x₀ hp a b).comp y hsymm
  refine (contMDiffAt_iff_contDiffAt.mp ?_)
  exact hcomp.congr_of_eventuallyEq (Filter.Eventually.of_forall (fun y' => rfl))

/-! ### `fderiv` and matrix components -/

/-- **`fderiv` of a matrix component.**  Differentiation commutes with reading a component of a
matrix-valued function. -/
lemma kz_fderiv_eval_coord {Φ : E → MatE (E := E)} {y : E} (hd : DifferentiableAt ℝ Φ y)
    (w : E) (i j : Fin (Module.finrank ℝ E)) :
    fderiv ℝ (fun x : E => Φ x i j) y w = (fderiv ℝ Φ y w) i j := by
  have hd1 : DifferentiableAt ℝ (fun x : E => Φ x i) y := by
    simpa only [Function.comp_def, ContinuousLinearMap.proj_apply] using
      (ContinuousLinearMap.proj i).differentiableAt.comp y hd
  have hd2 : DifferentiableAt ℝ (fun x : E => Φ x i j) y := by
    simpa only [Function.comp_def, ContinuousLinearMap.proj_apply] using
      (ContinuousLinearMap.proj j).differentiableAt.comp y hd1
  rw [fderiv_apply (𝕜 := ℝ) (x := y) (Φ := fun x : E => Φ x i) hd1 j,
    fderiv_apply (𝕜 := ℝ) (x := y) (Φ := Φ) hd i]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply]

/-! ### First coordinate derivative of the coefficients -/

/-- **The first coordinate partial of the metric coefficients is the corresponding partial of the
chart matrix.** -/
lemma kz_mvfderiv_pair_eq (g : Submission.Diff.SMet I M) (x₀ : M) {y : E}
    (hy : y ∈ (extChartAt I x₀).target) (i j k : Fin (Module.finrank ℝ E)) :
    mvfderiv I (fun q : M => g.inner q (cvec (I := I) x₀ q (bB (E := E) i))
        (cvec (I := I) x₀ q (bB (E := E) j)))
      ((extChartAt I x₀).symm y)
      (cvec (I := I) x₀ ((extChartAt I x₀).symm y) (bB (E := E) k))
      = (fderiv ℝ (chartMatFun g x₀) y (bB (E := E) k)) i j := by
  have hp : (extChartAt I x₀).symm y ∈ (chartAt H' x₀).source := by
    have h1 : (extChartAt I x₀).symm y ∈ (extChartAt I x₀).source :=
      (extChartAt I x₀).map_target hy
    rwa [extChartAt_source] at h1
  have hd : MDifferentiableAt I 𝓘(ℝ,ℝ)
      (fun q : M => g.inner q (cvec (I := I) x₀ q (bB (E := E) i))
        (cvec (I := I) x₀ q (bB (E := E) j))) ((extChartAt I x₀).symm y) :=
    (kz_contMDiffAt_pair (I := I) g x₀ hp i j).mdifferentiableAt (by simp)
  have h := Work.Diff.T.mvfderiv_frameVector_real (I := I) x₀ hp
    (g := fun q : M => g.inner q (cvec (I := I) x₀ q (bB (E := E) i))
      (cvec (I := I) x₀ q (bB (E := E) j))) hd (bB (E := E) k)
  have hchart : (extChartAt I x₀) ((extChartAt I x₀).symm y) = y :=
    (extChartAt I x₀).right_inv hy
  rw [hchart] at h
  have hfun : (fun x : E => g.inner ((extChartAt I x₀).symm x)
        (cvec (I := I) x₀ ((extChartAt I x₀).symm x) (bB (E := E) i))
        (cvec (I := I) x₀ ((extChartAt I x₀).symm x) (bB (E := E) j)))
      = (fun x : E => chartMatFun g x₀ x i j) := rfl
  rw [hfun] at h
  have h2 := kz_fderiv_eval_coord (Φ := chartMatFun g x₀)
    ((kz_contDiffAt_chartMatFun (I := I) g x₀ hy).differentiableAt (by simp))
    (bB (E := E) k) i j
  rw [h2] at h
  exact h

/-! ### The first derivative is differentiable along the chart -/

/-- The coordinate derivative of the metric coefficients of the chart frame, as a function of the
base point, is differentiable at every point of the chart source. -/
lemma kz_diff_mvfderiv_pair (g : Submission.Diff.SMet I M) (x₀ : M) {y : E}
    (hy : y ∈ (extChartAt I x₀).target) (i j k : Fin (Module.finrank ℝ E)) :
    MDifferentiableAt I 𝓘(ℝ,ℝ)
      (fun q : M => mvfderiv I (fun q' : M => g.inner q' (cvec (I := I) x₀ q' (bB (E := E) i))
        (cvec (I := I) x₀ q' (bB (E := E) j))) q
        (cvec (I := I) x₀ q (bB (E := E) k))) ((extChartAt I x₀).symm y) := by
  have hp : (extChartAt I x₀).symm y ∈ (chartAt H' x₀).source := by
    have h1 : (extChartAt I x₀).symm y ∈ (extChartAt I x₀).source :=
      (extChartAt I x₀).map_target hy
    rwa [extChartAt_source] at h1
  have hc := kz_contMDiffAt_pair (I := I) g x₀ hp i j
  have hX : ContMDiffAt I I.tangent ∞
      (fun q : M => (⟨q, cvec (I := I) x₀ q (bB (E := E) k)⟩ : TangentBundle I M))
      ((extChartAt I x₀).symm y) :=
    contMDiffAt_frameVector (I := I) x₀ (bB (E := E) k) hp
  have h := contMDiffAt_mvfderiv_gen (I := I)
    (f := fun q : M => g.inner q (cvec (I := I) x₀ q (bB (E := E) i))
      (cvec (I := I) x₀ q (bB (E := E) j)))
    (X := fun q : M => cvec (I := I) x₀ q (bB (E := E) k)) hc hX
  exact h.mdifferentiableAt (by simp)

/-! ### A second Fréchet-derivative computation on the model space -/

/-- **The component of a second derivative.**  The derivative of the `(i,j)`-component of
`x ↦ fderiv Φ x v` is the `(i,j)`-component of the second derivative of `Φ`, applied to `v`. -/
lemma kz_fderiv_fderiv_apply_coord {Φ : E → MatE (E := E)} {y : E}
    (hΦ : ContDiffAt ℝ 2 Φ y) (v w : E) (i j : Fin (Module.finrank ℝ E)) :
    fderiv ℝ (fun x : E => (fderiv ℝ Φ x v) i j) y w
      = ((fderiv ℝ (fun x : E => fderiv ℝ Φ x) y w) v) i j := by
  have h1 : ContDiffAt ℝ 1 (fun x : E => fderiv ℝ Φ x) y :=
    hΦ.fderiv_right (m := 1) (by norm_num)
  have hd : DifferentiableAt ℝ (fun x : E => fderiv ℝ Φ x) y :=
    h1.differentiableAt (by norm_num)
  have hdV : DifferentiableAt ℝ (fun x : E => fderiv ℝ Φ x v) y := by
    simpa only [Function.comp_def, ContinuousLinearMap.apply_apply] using
      (ContinuousLinearMap.apply ℝ (MatE (E := E)) v).differentiableAt.comp y hd
  have hsw : fderiv ℝ (fun x : E => fderiv ℝ Φ x v) y
      = (fderiv ℝ (fun x : E => fderiv ℝ Φ x) y).flip v := by
    rw [fderiv_clm_apply (c := fun x : E => fderiv ℝ Φ x) (u := fun _ : E => v) hd
      (differentiableAt_const v)]
    have hz : fderiv ℝ (fun _ : E => v) y = 0 := (hasFDerivAt_const (𝕜 := ℝ) v y).fderiv
    rw [hz]
    simp
  rw [kz_fderiv_eval_coord (Φ := fun x : E => fderiv ℝ Φ x v) hdV w i j, hsw]
  simp only [ContinuousLinearMap.flip_apply]

/-! ### Second coordinate derivative of the coefficients -/

/-- **The second coordinate partial of the metric coefficients is the corresponding second partial
of the chart matrix.** -/
lemma kz_second (g : Submission.Diff.SMet I M) (x₀ : M) {y : E}
    (hy : y ∈ (extChartAt I x₀).target) (i j k l : Fin (Module.finrank ℝ E)) :
    mvfderiv I (fun q : M => mvfderiv I
        (fun q' : M => g.inner q' (cvec (I := I) x₀ q' (bB (E := E) i))
          (cvec (I := I) x₀ q' (bB (E := E) j))) q
        (cvec (I := I) x₀ q (bB (E := E) k)))
      ((extChartAt I x₀).symm y)
      (cvec (I := I) x₀ ((extChartAt I x₀).symm y) (bB (E := E) l))
      = (dJet2 g x₀ y l k) i j := by
  have hp : (extChartAt I x₀).symm y ∈ (chartAt H' x₀).source := by
    have h1 : (extChartAt I x₀).symm y ∈ (extChartAt I x₀).source :=
      (extChartAt I x₀).map_target hy
    rwa [extChartAt_source] at h1
  have hK := kz_diff_mvfderiv_pair (I := I) g x₀ hy i j k
  have h := Work.Diff.T.mvfderiv_frameVector_real (I := I) x₀ hp
    (g := fun q : M => mvfderiv I
      (fun q' : M => g.inner q' (cvec (I := I) x₀ q' (bB (E := E) i))
        (cvec (I := I) x₀ q' (bB (E := E) j))) q
      (cvec (I := I) x₀ q (bB (E := E) k))) hK (bB (E := E) l)
  have hchart : (extChartAt I x₀) ((extChartAt I x₀).symm y) = y :=
    (extChartAt I x₀).right_inv hy
  rw [hchart] at h
  have hev : (fun x : E => mvfderiv I
        (fun q' : M => g.inner q' (cvec (I := I) x₀ q' (bB (E := E) i))
          (cvec (I := I) x₀ q' (bB (E := E) j)))
        ((extChartAt I x₀).symm x) (cvec (I := I) x₀ ((extChartAt I x₀).symm x) (bB (E := E) k)))
      =ᶠ[𝓝 y] (fun x : E => (fderiv ℝ (chartMatFun g x₀) x (bB (E := E) k)) i j) := by
    filter_upwards [(isOpen_extChartAt_target (I := I) x₀).mem_nhds hy] with x hx
    exact kz_mvfderiv_pair_eq (I := I) g x₀ hx i j k
  rw [hev.fderiv_eq] at h
  have h2 : ContDiffAt ℝ 2 (chartMatFun g x₀) y :=
    (kz_contDiffAt_chartMatFun (I := I) g x₀ hy).of_le (by norm_num)
  rw [kz_fderiv_fderiv_apply_coord (hΦ := h2) (v := bB (E := E) k) (w := bB (E := E) l) i j] at h
  simpa only [dJet2] using h

/-! ### Linearity of `mvfderiv` on real-valued functions -/

/-- `mvfderiv` is additive on real-valued functions. -/
lemma kz_mvfderiv_add {f g : M → ℝ} {x : M} {v : TangentSpace I x}
    (hf : MDifferentiableAt I 𝓘(ℝ,ℝ) f x) (hg : MDifferentiableAt I 𝓘(ℝ,ℝ) g x) :
    mvfderiv I (fun y : M => f y + g y) x v = mvfderiv I f x v + mvfderiv I g x v := by
  rw [show (fun y : M => f y + g y) = f + g from rfl, mvfderiv_add hf hg]
  rfl

/-- `mvfderiv` of a difference of real-valued functions. -/
lemma kz_mvfderiv_sub {f g : M → ℝ} {x : M} {v : TangentSpace I x}
    (hf : MDifferentiableAt I 𝓘(ℝ,ℝ) f x) (hg : MDifferentiableAt I 𝓘(ℝ,ℝ) g x) :
    mvfderiv I (fun y : M => f y - g y) x v = mvfderiv I f x v - mvfderiv I g x v := by
  rw [show (fun y : M => f y - g y) = f - g from rfl, mvfderiv_sub hf hg]
  rfl

/-- `mvfderiv` is homogeneous for real-valued functions. -/
lemma kz_mvfderiv_const_mul (c : ℝ) {f : M → ℝ} {x : M} {v : TangentSpace I x}
    (_hf : MDifferentiableAt I 𝓘(ℝ,ℝ) f x) :
    mvfderiv I (fun y : M => c * f y) x v = c * mvfderiv I f x v := by
  have hfun : (fun y : M => c * f y) = (fun y : M => c • f y) := by
    funext y
    exact (smul_eq_mul c (f y)).symm
  rw [hfun, Commons.Geometry.Manifold.Riemannian.mvfderiv_const_smul c f x,
    ContinuousLinearMap.smul_apply, smul_eq_mul]

/-! ### The target -/

theorem dOp_koszulPair_eq_sKzD
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H' : Type*} [TopologicalSpace H'] {I : ModelWithCorners ℝ E H'}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H' M] [IsManifold I (⊤ : ℕ∞) M]
    [I.Boundaryless] [T2Space M]
    (g : Submission.Diff.SMet I M) (x₀ : M) {y : E} (hy : y ∈ (extChartAt I x₀).target)
    (a b c d : Fin (Module.finrank ℝ E)) :
    Work.Diff.GE.dOp (I := I) x₀ a (Work.Diff.GE.koszulPair (I := I) (fun _ : ℝ => g) x₀ b d c)
        0 ((extChartAt I x₀).symm y)
      = Work.Diff.EXT.sKzD (Work.Diff.EXT.dJet2 g x₀ y) a b d c := by
  -- the metric pairing is symmetric: `g_{cb} = g_{bc}`
  have hsym : (fun q' : M => g.inner q' (cvec (I := I) x₀ q' (bB (E := E) c))
        (cvec (I := I) x₀ q' (bB (E := E) b)))
      = (fun q' : M => g.inner q' (cvec (I := I) x₀ q' (bB (E := E) b))
        (cvec (I := I) x₀ q' (bB (E := E) c))) := by
    funext q'
    exact g.symm q' (cvec (I := I) x₀ q' (bB (E := E) c)) (cvec (I := I) x₀ q' (bB (E := E) b))
  -- the coordinate derivative of the Koszul pairing, unfolded
  have hunfold : Work.Diff.GE.dOp (I := I) x₀ a (Work.Diff.GE.koszulPair (I := I) (fun _ : ℝ => g) x₀ b d c)
        0 ((extChartAt I x₀).symm y)
      = mvfderiv I (fun q : M => (1 / 2 : ℝ) *
          (mvfderiv I (fun q' : M => g.inner q' (cvec (I := I) x₀ q' (bB (E := E) d)) (cvec (I := I) x₀ q' (bB (E := E) c))) q (cvec (I := I) x₀ q (bB (E := E) b))
            + mvfderiv I (fun q' : M => g.inner q' (cvec (I := I) x₀ q' (bB (E := E) c)) (cvec (I := I) x₀ q' (bB (E := E) b))) q (cvec (I := I) x₀ q (bB (E := E) d))
            - mvfderiv I (fun q' : M => g.inner q' (cvec (I := I) x₀ q' (bB (E := E) b)) (cvec (I := I) x₀ q' (bB (E := E) d))) q (cvec (I := I) x₀ q (bB (E := E) c))))
          ((extChartAt I x₀).symm y) (cvec (I := I) x₀ ((extChartAt I x₀).symm y) (bB (E := E) a)) := rfl
  rw [hunfold, hsym]
  -- the three differentiated coefficients are differentiable
  have hA : MDifferentiableAt I 𝓘(ℝ,ℝ) (fun q : M => mvfderiv I (fun q' : M => g.inner q' (cvec (I := I) x₀ q' (bB (E := E) d)) (cvec (I := I) x₀ q' (bB (E := E) c))) q (cvec (I := I) x₀ q (bB (E := E) b))) ((extChartAt I x₀).symm y) :=
    kz_diff_mvfderiv_pair (I := I) g x₀ hy d c b
  have hB : MDifferentiableAt I 𝓘(ℝ,ℝ) (fun q : M => mvfderiv I (fun q' : M => g.inner q' (cvec (I := I) x₀ q' (bB (E := E) b)) (cvec (I := I) x₀ q' (bB (E := E) c))) q (cvec (I := I) x₀ q (bB (E := E) d))) ((extChartAt I x₀).symm y) :=
    kz_diff_mvfderiv_pair (I := I) g x₀ hy b c d
  have hC : MDifferentiableAt I 𝓘(ℝ,ℝ) (fun q : M => mvfderiv I (fun q' : M => g.inner q' (cvec (I := I) x₀ q' (bB (E := E) b)) (cvec (I := I) x₀ q' (bB (E := E) d))) q (cvec (I := I) x₀ q (bB (E := E) c))) ((extChartAt I x₀).symm y) :=
    kz_diff_mvfderiv_pair (I := I) g x₀ hy b d c
  -- split the outer derivative into the three summands
  rw [kz_mvfderiv_const_mul (c := (1 / 2 : ℝ)) (f := fun q : M => mvfderiv I (fun q' : M => g.inner q' (cvec (I := I) x₀ q' (bB (E := E) d)) (cvec (I := I) x₀ q' (bB (E := E) c))) q (cvec (I := I) x₀ q (bB (E := E) b)) + mvfderiv I (fun q' : M => g.inner q' (cvec (I := I) x₀ q' (bB (E := E) b)) (cvec (I := I) x₀ q' (bB (E := E) c))) q (cvec (I := I) x₀ q (bB (E := E) d)) - mvfderiv I (fun q' : M => g.inner q' (cvec (I := I) x₀ q' (bB (E := E) b)) (cvec (I := I) x₀ q' (bB (E := E) d))) q (cvec (I := I) x₀ q (bB (E := E) c))) ((hA.add hB).sub hC)]
  rw [kz_mvfderiv_sub (f := fun q : M => mvfderiv I (fun q' : M => g.inner q' (cvec (I := I) x₀ q' (bB (E := E) d)) (cvec (I := I) x₀ q' (bB (E := E) c))) q (cvec (I := I) x₀ q (bB (E := E) b)) + mvfderiv I (fun q' : M => g.inner q' (cvec (I := I) x₀ q' (bB (E := E) b)) (cvec (I := I) x₀ q' (bB (E := E) c))) q (cvec (I := I) x₀ q (bB (E := E) d)))
      (g := fun q : M => mvfderiv I (fun q' : M => g.inner q' (cvec (I := I) x₀ q' (bB (E := E) b)) (cvec (I := I) x₀ q' (bB (E := E) d))) q (cvec (I := I) x₀ q (bB (E := E) c))) (hA.add hB) hC,
    kz_mvfderiv_add (f := fun q : M => mvfderiv I (fun q' : M => g.inner q' (cvec (I := I) x₀ q' (bB (E := E) d)) (cvec (I := I) x₀ q' (bB (E := E) c))) q (cvec (I := I) x₀ q (bB (E := E) b)))
      (g := fun q : M => mvfderiv I (fun q' : M => g.inner q' (cvec (I := I) x₀ q' (bB (E := E) b)) (cvec (I := I) x₀ q' (bB (E := E) c))) q (cvec (I := I) x₀ q (bB (E := E) d))) hA hB]
  -- identify each second coordinate derivative with a chart matrix second partial
  rw [kz_second (I := I) g x₀ hy d c b a,
    kz_second (I := I) g x₀ hy b c d a,
    kz_second (I := I) g x₀ hy b d c a]
  rw [Work.Diff.EXT.sKzD]

end

end Work.Diff.EXT
