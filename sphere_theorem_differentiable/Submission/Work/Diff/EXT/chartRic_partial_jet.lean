import Mathlib
import Submission.Work.Diff.EXT.splice_defs
import Submission.Work.Diff.GE.rmP_jointSmooth
import Submission.Work.Diff.EXT.cGram_chrB_chrB_eq_sum_koszul
import Submission.Work.Diff.EXT.ricPhiPartialDefs
import Submission.Work.Diff.GE.norms_defs
import Submission.Work.Diff.GE.koszul
import Submission.Work.Diff.GE.cGram_eq_sum_gramInv
import Submission.Work.Diff.GE.cGram_chrB_eq_koszulPair
import Submission.Work.Diff.GE.Frame
import Submission.Work.Diff.T.lc_smooth
import Submission.Work.Diff.T.mvfderiv_frameVector_real
import Submission.Work.Diff.T.clairaut_fderiv_apply
import Submission.Work.Diff.EXT.kosDefs
import Submission.Work.Diff.EXT.contMDiffAt_metric_pairing
import Submission.Work.Diff.EXT.chartRicPhi_smooth
import Submission.Work.Diff.EXT.ricAt_invGram_chart
import Submission.Commons.Geometry.Manifold.VectorBundle.CovariantDerivative.contDiffOn_chartSpray
import Submission.ChartCurv

set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff Bundle Topology BigOperators
open Bundle ContDiff Set VectorField CovariantDerivative Metric

namespace Work.Diff.EXT

section Smoothness

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [CompleteSpace E]
variable {H' : Type*} [TopologicalSpace H'] {I : ModelWithCorners ℝ E H'}
variable {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H' M]
  [IsManifold I (⊤ : ℕ∞) M] [I.Boundaryless]

/-- The constant family `t ↦ g` of a smooth metric is jointly smooth. -/
lemma jointSmooth_const (g : Submission.Diff.SMet I M) :
    Submission.Diff.JointSmooth (fun _ : ℝ => g) Set.univ := by
  have h : ContMDiff (𝓘(ℝ,ℝ).prod I) (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
      ((fun b : M => Bundle.TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ) b (g.inner b)) ∘
        (Prod.snd : ℝ × M → M)) :=
    g.contMDiff.comp contMDiff_snd
  simpa only [Submission.Diff.JointSmooth, Set.univ_prod_univ, Function.comp_def] using
    h.contMDiffOn

/-- The coordinate-frame vector field of the chart at `x₀` is smooth at every point of the chart. -/
lemma smoothFieldAt_cvec (x₀ : M) (v : E) {p : M} (hp : p ∈ (chartAt H' x₀).source) :
    SmoothFieldAt I M (fun q => cvec (I := I) x₀ q v) p :=
  (Commons.Geometry.Manifold.VectorBundle.CovariantDerivative.contMDiffOn_trivializationAt_symmL_section (I := I) x₀ v).contMDiffAt
    ((chartAt H' x₀).open_source.mem_nhds hp)

/-- The metric coefficients in the coordinate frame of the chart at `x₀` are smooth at every point
of the chart. -/
lemma contMDiffAt_metric_coeff (g : Submission.Diff.SMet I M) (x₀ : M) {p : M}
    (hp : p ∈ (chartAt H' x₀).source) (i j : Fin (Module.finrank ℝ E)) :
    ContMDiffAt I 𝓘(ℝ,ℝ) ∞
      (fun q : M => g.inner q (cvec (I := I) x₀ q (bB (E := E) i))
        (cvec (I := I) x₀ q (bB (E := E) j))) p := by
  have hres := contMDiffAt_metric_pairing (I := I) (G := fun _ : ℝ => g) (J := Set.univ)
    isOpen_univ (jointSmooth_const (I := I) g) (Set.mem_univ 0)
    (smoothFieldAt_cvec (I := I) x₀ (bB (E := E) i) hp)
    (smoothFieldAt_cvec (I := I) x₀ (bB (E := E) j) hp)
  have hc : ContMDiffAt I (𝓘(ℝ,ℝ).prod I) ∞ (fun q : M => ((0 : ℝ), q)) p :=
    (contMDiffAt_const : ContMDiffAt I 𝓘(ℝ,ℝ) ∞ (fun _ : M => (0 : ℝ)) p).prodMk
      contMDiffAt_id
  simpa only [Function.comp_def] using hres.comp p hc

/-- **The chart matrix of a smooth metric is smooth as a function of the chart coordinate.** -/
lemma contDiffAt_chartMatFun (g : Submission.Diff.SMet I M) (x₀ : M) {y : E}
    (hy : y ∈ (extChartAt I x₀).target) :
    ContDiffAt ℝ ∞ (chartMatFun g x₀) y := by
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
  have hcomp := (contMDiffAt_metric_coeff (I := I) g x₀ hp a b).comp y hsymm
  refine (contMDiffAt_iff_contDiffAt.mp ?_)
  refine hcomp.congr_of_eventuallyEq (Filter.Eventually.of_forall (fun y' => ?_))
  rfl

end Smoothness

section Jet

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [CompleteSpace E]
variable {H' : Type*} [TopologicalSpace H'] {I : ModelWithCorners ℝ E H'}
variable {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H' M]
  [IsManifold I (⊤ : ℕ∞) M] [I.Boundaryless]

/-- The scalar `2`-jet of the chart matrix, as computed by `sJetData`, is the packaged jet
`chartJet`: the only non-definitional point is that the derivative of `y' ↦ (fderiv A y') v` is the
second derivative of `A` evaluated on `v`. -/
lemma sJetData_chartMat (g : Submission.Diff.SMet I M) (x₀ : M) {y : E}
    (hy : y ∈ (extChartAt I x₀).target) :
    sJetData (fun p : ℝ × E => chartMatFun g x₀ p.2) (0, y) = chartJet g x₀ y := by
  have h2 : ContDiffAt ℝ (2 : ℕ∞) (chartMatFun g x₀) y :=
    (contDiffAt_chartMatFun g x₀ hy).of_le (by norm_num)
  refine Prod.ext rfl (Prod.ext rfl ?_)
  funext k l
  show fderiv ℝ (fun y' : E => fderiv ℝ (chartMatFun g x₀) y' (bB (E := E) l)) y
      (bB (E := E) k)
    = (fderiv ℝ (fun y' : E => fderiv ℝ (chartMatFun g x₀) y') y (bB (E := E) k))
        (bB (E := E) l)
  have hd : DifferentiableAt ℝ (fun y' : E => fderiv ℝ (chartMatFun g x₀) y') y :=
    ((h2.fderiv_right (m := 1) (by norm_num))).differentiableAt (by norm_num)
  have h :=
    (ContinuousLinearMap.apply ℝ (MatE (E := E)) (bB (E := E) l)).hasFDerivAt.comp y
      hd.hasFDerivAt
  have hfe : fderiv ℝ (fun y' : E => (fderiv ℝ (chartMatFun g x₀) y') (bB (E := E) l)) y
      = (ContinuousLinearMap.apply ℝ (MatE (E := E)) (bB (E := E) l)).comp
          (fderiv ℝ (fun y' : E => fderiv ℝ (chartMatFun g x₀) y') y) := h.fderiv
  rw [hfe]
  rfl

end Jet

section Entry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
variable {ι : Type*} [Fintype ι]

/-- The derivative of a component of a map into a product is the component of the derivative. -/
lemma fderiv_apply_entry (A : E → (ι → F)) {y : E} (hA : DifferentiableAt ℝ A y) (i : ι)
    (v : E) : fderiv ℝ (fun x : E => A x i) y v = (fderiv ℝ A y v) i := by
  have h := ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ι => F) i).hasFDerivAt.comp y
    hA.hasFDerivAt)
  have h' : (fun x : E => A x i)
      = ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ι => F) i) ∘ A) := rfl
  rw [h', h.fderiv]
  rfl

/-- A component of a differentiable map into a product is differentiable. -/
lemma differentiableAt_entry (A : E → (ι → F)) {y : E} (hA : DifferentiableAt ℝ A y)
    (i : ι) : DifferentiableAt ℝ (fun x : E => A x i) y :=
  ((((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ι => F) i).hasFDerivAt).comp y
    hA.hasFDerivAt)).differentiableAt

/-- A component of a smooth map into a product is smooth. -/
lemma contDiffAt_entry {A : E → (ι → F)} {y : E} (hA : ContDiffAt ℝ ∞ A y) (i : ι) :
    ContDiffAt ℝ ∞ (fun x : E => A x i) y := by
  have h : ContDiffAt ℝ ∞ ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ι => F) i) ∘ A) y :=
    ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ι => F) i).contDiff.contDiffAt).comp y hA
  refine h.congr_of_eventuallyEq (Filter.Eventually.of_forall (fun z => ?_))
  rfl

/-- The derivative of a component, with the smoothness hypothesis. -/
lemma fderiv_entry_eq {A : E → (ι → F)} {y : E} (hA : ContDiffAt ℝ ∞ A y) (i : ι) (v : E) :
    fderiv ℝ (fun x : E => A x i) y v = (fderiv ℝ A y v) i :=
  fderiv_apply_entry A (hA.differentiableAt (by simp)) i v

end Entry

section Bridges

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [CompleteSpace E]
variable {H' : Type*} [TopologicalSpace H'] {I : ModelWithCorners ℝ E H'}
variable {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H' M]
  [IsManifold I (⊤ : ℕ∞) M] [I.Boundaryless]

/-- The Koszul pairing `Γ_{abc}` of the chart frame, read at the chart coordinate `y`, is the
Koszul combination `sKz` of the first coordinate partials of the chart matrix. -/
lemma koszulPair_eq_sKz_self (g : Submission.Diff.SMet I M) (x₀ : M) {y : E}
    (hy : y ∈ (extChartAt I x₀).target) (a b c : Fin (Module.finrank ℝ E)) :
    Work.Diff.GE.koszulPair (I := I) (fun _ : ℝ => g) x₀ a b c 0
        ((extChartAt I x₀).symm y)
      = sKz (dJet1 g x₀ y) a b c := by
  set p : M := (extChartAt I x₀).symm y with hp_def
  have hp : p ∈ (chartAt H' x₀).source := by
    have h1 : p ∈ (extChartAt I x₀).source := (extChartAt I x₀).map_target hy
    rwa [extChartAt_source] at h1
  have hchart : (extChartAt I x₀) p = y := (extChartAt I x₀).right_inv hy
  have key : ∀ m n k : Fin (Module.finrank ℝ E),
      mvfderiv I (fun q : M => g.inner q (cvec (I := I) x₀ q (bB (E := E) m))
          (cvec (I := I) x₀ q (bB (E := E) n))) p (cvec (I := I) x₀ p (bB (E := E) k))
        = fderiv ℝ (chartMatFun g x₀) y (bB (E := E) k) m n := by
    intro m n k
    have h := Work.Diff.T.mvfderiv_frameVector_real (I := I) x₀ hp
      (g := fun q : M => g.inner q (cvec (I := I) x₀ q (bB (E := E) m))
        (cvec (I := I) x₀ q (bB (E := E) n)))
      ((contMDiffAt_metric_coeff g x₀ hp m n).mdifferentiableAt (by simp))
      (bB (E := E) k)
    rw [hchart] at h
    have hd : DifferentiableAt ℝ (chartMatFun g x₀) y :=
      (contDiffAt_chartMatFun g x₀ hy).differentiableAt (by simp)
    have hfun : (fun x : E => g.inner ((extChartAt I x₀).symm x)
          (cvec (I := I) x₀ ((extChartAt I x₀).symm x) (bB (E := E) m))
          (cvec (I := I) x₀ ((extChartAt I x₀).symm x) (bB (E := E) n)))
        = (fun x : E => chartMatFun g x₀ x m n) := rfl
    rw [hfun] at h
    rw [h, fderiv_apply_entry (fun x : E => chartMatFun g x₀ x m)
      (differentiableAt_entry (fun x : E => chartMatFun g x₀ x) hd m) n,
      fderiv_apply_entry (fun x : E => chartMatFun g x₀ x) hd m]
  have hsym : ∀ m n k : Fin (Module.finrank ℝ E),
      mvfderiv I (fun q : M => g.inner q (cvec (I := I) x₀ q (bB (E := E) m))
          (cvec (I := I) x₀ q (bB (E := E) n))) p (cvec (I := I) x₀ p (bB (E := E) k))
        = mvfderiv I (fun q : M => g.inner q (cvec (I := I) x₀ q (bB (E := E) n))
          (cvec (I := I) x₀ q (bB (E := E) m))) p (cvec (I := I) x₀ p (bB (E := E) k)) := by
    intro m n k
    have hF : (fun q : M => g.inner q (cvec (I := I) x₀ q (bB (E := E) m))
          (cvec (I := I) x₀ q (bB (E := E) n)))
        = (fun q : M => g.inner q (cvec (I := I) x₀ q (bB (E := E) n))
          (cvec (I := I) x₀ q (bB (E := E) m))) := by
      funext q
      exact g.symm q _ _
    rw [hF]
  simp only [Work.Diff.GE.koszulPair, sKz, dJet1, Work.Diff.GE.cFrame_apply]
  rw [key b c a, hsym c a b, key a c b, key a b c]

/-- **Reading a manifold derivative in the chart**: if `F` agrees on the chart at `x₀` with the
pull-back of a smooth function `G` of the chart coordinate, then the manifold derivative of `F` in a
coordinate direction is the Fréchet derivative of `G`. -/
lemma mvfderiv_eq_fderiv_of_eq_on_chart (x₀ : M) {p : M} (hp : p ∈ (chartAt H' x₀).source)
    {F : M → ℝ} {G : E → ℝ} (hG : ContDiffAt ℝ ∞ G ((extChartAt I x₀) p))
    (hpoint : ∀ q ∈ (chartAt H' x₀).source, F q = G ((extChartAt I x₀) q)) (v : E) :
    mvfderiv I F p (cvec (I := I) x₀ p v) = fderiv ℝ G ((extChartAt I x₀) p) v := by
  have hmd : MDifferentiableAt I 𝓘(ℝ,ℝ) F p := by
    have hev : F =ᶠ[𝓝 p] (fun q => G ((extChartAt I x₀) q)) :=
      Filter.eventually_of_mem ((chartAt H' x₀).open_source.mem_nhds hp)
        (fun q hq => hpoint q hq)
    have hchartAt : ContMDiffAt I 𝓘(ℝ,E) ∞ (extChartAt I x₀) p :=
      (contMDiffOn_extChartAt (I := I) (x := x₀) (n := ∞)).contMDiffAt
        ((chartAt H' x₀).open_source.mem_nhds hp)
    have hcomp : ContMDiffAt I 𝓘(ℝ,ℝ) ∞ (fun q => G ((extChartAt I x₀) q)) p :=
      hG.contMDiffAt.comp p hchartAt
    exact (hcomp.congr_of_eventuallyEq hev).mdifferentiableAt (by simp)
  have hpsrc : p ∈ (extChartAt I x₀).source := by rw [extChartAt_source]; exact hp
  have hpchart : (extChartAt I x₀) p ∈ (extChartAt I x₀).target :=
    (extChartAt I x₀).map_source hpsrc
  have heq : G =ᶠ[𝓝 ((extChartAt I x₀) p)] (fun x : E => F ((extChartAt I x₀).symm x)) := by
    filter_upwards [(isOpen_extChartAt_target (I := I) x₀).mem_nhds hpchart] with x hx
    have hxs : (extChartAt I x₀).symm x ∈ (extChartAt I x₀).source := (extChartAt I x₀).map_target hx
    have hsrc : (extChartAt I x₀).symm x ∈ (chartAt H' x₀).source := by
      rwa [extChartAt_source] at hxs
    rw [hpoint _ hsrc, (extChartAt I x₀).right_inv hx]
  rw [Work.Diff.T.mvfderiv_frameVector_real (I := I) x₀ hp hmd v,
    ← Filter.EventuallyEq.fderiv_eq (𝕜 := ℝ) heq]

/-- The manifold derivative of a metric coefficient in a coordinate direction, read at a point of
the chart, is the corresponding coordinate partial derivative of the chart matrix. -/
lemma mvfderiv_metric_coeff_eq (g : Submission.Diff.SMet I M) (x₀ : M) {q : M}
    (hq : q ∈ (chartAt H' x₀).source) (m n k : Fin (Module.finrank ℝ E)) :
    mvfderiv I (fun q' : M => g.inner q' (cvec (I := I) x₀ q' (bB (E := E) m))
        (cvec (I := I) x₀ q' (bB (E := E) n))) q (cvec (I := I) x₀ q (bB (E := E) k))
      = fderiv ℝ (chartMatFun g x₀) ((extChartAt I x₀) q) (bB (E := E) k) m n := by
  have hqsrc : q ∈ (extChartAt I x₀).source := by rw [extChartAt_source]; exact hq
  have hyq : (extChartAt I x₀) q ∈ (extChartAt I x₀).target :=
    (extChartAt I x₀).map_source hqsrc
  rw [mvfderiv_eq_fderiv_of_eq_on_chart (I := I) (x₀ := x₀) (p := q)
    (F := fun q' : M => g.inner q' (cvec (I := I) x₀ q' (bB (E := E) m))
      (cvec (I := I) x₀ q' (bB (E := E) n)))
    (G := fun z : E => chartMatFun g x₀ z m n)
    hq (contDiffAt_entry (contDiffAt_entry (contDiffAt_chartMatFun g x₀ hyq) m) n)
    (fun q' hq' => by
      have hsrc : q' ∈ (extChartAt I x₀).source := by
        rw [extChartAt_source (I := I) (H := H') (x := x₀)]
        exact hq'
      rw [Work.Diff.EXT.chartMatFun, (extChartAt I x₀).left_inv hsrc])
    (bB (E := E) k)]
  have hd : DifferentiableAt ℝ (chartMatFun g x₀) ((extChartAt I x₀) q) :=
    (contDiffAt_chartMatFun g x₀ hyq).differentiableAt (by simp)
  rw [fderiv_apply_entry (fun z : E => chartMatFun g x₀ z m)
      (differentiableAt_entry (fun z : E => chartMatFun g x₀ z) hd m) n,
    fderiv_apply_entry (fun z : E => chartMatFun g x₀ z) hd m]

/-- The Fréchet derivative, in a coordinate direction, of the first coordinate partial of the chart
matrix is the corresponding second coordinate partial. -/
lemma fderiv_second_entry (g : Submission.Diff.SMet I M) (x₀ : M) {y : E}
    (hy : y ∈ (extChartAt I x₀).target) (k l i j : Fin (Module.finrank ℝ E)) :
    fderiv ℝ (fun z : E => fderiv ℝ (chartMatFun g x₀) z (bB (E := E) l) i j) y
        (bB (E := E) k)
      = dJet2 g x₀ y k l i j := by
  have hA : ContDiffAt ℝ ∞ (chartMatFun g x₀) y := contDiffAt_chartMatFun g x₀ hy
  have hA2' : ContDiffAt ℝ (2 : ℕ∞) (chartMatFun g x₀) y := hA.of_le (by norm_num)
  have hA2 : DifferentiableAt ℝ (fun z : E => fderiv ℝ (chartMatFun g x₀) z) y :=
    ((hA2'.fderiv_right (m := 1) (by norm_num))).differentiableAt (by norm_num)
  have h1 : fderiv ℝ (fun z : E => (fderiv ℝ (chartMatFun g x₀) z) (bB (E := E) l)) y
      = (ContinuousLinearMap.apply ℝ (MatE (E := E)) (bB (E := E) l)).comp
          (fderiv ℝ (fun z : E => fderiv ℝ (chartMatFun g x₀) z) y) := by
    have h := (ContinuousLinearMap.apply ℝ (MatE (E := E)) (bB (E := E) l)).hasFDerivAt.comp y
      hA2.hasFDerivAt
    have h' : (fun z : E => fderiv ℝ (chartMatFun g x₀) z (bB (E := E) l))
        = ((ContinuousLinearMap.apply ℝ (MatE (E := E)) (bB (E := E) l)) ∘
            fun z : E => fderiv ℝ (chartMatFun g x₀) z) := rfl
    rw [h', h.fderiv]
  have hd1 : DifferentiableAt ℝ (fun z : E => fderiv ℝ (chartMatFun g x₀) z (bB (E := E) l)) y :=
    (((ContinuousLinearMap.apply ℝ (MatE (E := E)) (bB (E := E) l)).differentiableAt).comp y hA2)
  have hd1i : DifferentiableAt ℝ
      (fun z : E => fderiv ℝ (chartMatFun g x₀) z (bB (E := E) l) i) y :=
    differentiableAt_entry (fun z : E => fderiv ℝ (chartMatFun g x₀) z (bB (E := E) l)) hd1 i
  rw [fderiv_apply_entry (fun z : E => fderiv ℝ (chartMatFun g x₀) z (bB (E := E) l) i) hd1i j,
    fderiv_apply_entry (fun z : E => fderiv ℝ (chartMatFun g x₀) z (bB (E := E) l)) hd1 i, h1]
  rfl

/-- The second manifold derivative of a metric coefficient in two coordinate directions, read at a
point of the chart, is the corresponding second coordinate partial of the chart matrix. -/
lemma mvfderiv2_metric_coeff_eq (g : Submission.Diff.SMet I M) (x₀ : M) {q : M}
    (hq : q ∈ (chartAt H' x₀).source) (i j k l : Fin (Module.finrank ℝ E)) :
    mvfderiv I (fun qa : M => mvfderiv I (fun qb : M => g.inner qb
        (cvec (I := I) x₀ qb (bB (E := E) i)) (cvec (I := I) x₀ qb (bB (E := E) j)))
        qa (cvec (I := I) x₀ qa (bB (E := E) l))) q (cvec (I := I) x₀ q (bB (E := E) k))
      = dJet2 g x₀ ((extChartAt I x₀) q) k l i j := by
  have hqsrc : q ∈ (extChartAt I x₀).source := by rw [extChartAt_source]; exact hq
  have hy : (extChartAt I x₀) q ∈ (extChartAt I x₀).target :=
    (extChartAt I x₀).map_source hqsrc
  have hA : ContDiffAt ℝ ∞ (chartMatFun g x₀) ((extChartAt I x₀) q) :=
    contDiffAt_chartMatFun g x₀ hy
  have h2 : ContDiffAt ℝ ∞ (fun z : E => fderiv ℝ (chartMatFun g x₀) z) ((extChartAt I x₀) q) := by
    simpa only [] using hA.fderiv_right (m := ∞) (by simp)
  have h3 : ContDiffAt ℝ ∞
      (fun z : E => fderiv ℝ (chartMatFun g x₀) z (bB (E := E) l)) ((extChartAt I x₀) q) :=
    (((ContinuousLinearMap.apply ℝ (MatE (E := E)) (bB (E := E) l)).contDiff.contDiffAt).comp
      ((extChartAt I x₀) q) h2).congr_of_eventuallyEq
        (Filter.Eventually.of_forall (fun z => rfl))
  have h4 : ContDiffAt ℝ ∞
      (fun z : E => (fderiv ℝ (chartMatFun g x₀) z (bB (E := E) l)) i) ((extChartAt I x₀) q) :=
    contDiffAt_entry h3 i
  have h5 : ContDiffAt ℝ ∞
      (fun z : E => fderiv ℝ (chartMatFun g x₀) z (bB (E := E) l) i j) ((extChartAt I x₀) q) :=
    contDiffAt_entry h4 j
  have hpoint : ∀ qa ∈ (chartAt H' x₀).source,
      (fun qa : M => mvfderiv I (fun qb : M => g.inner qb
            (cvec (I := I) x₀ qb (bB (E := E) i)) (cvec (I := I) x₀ qb (bB (E := E) j)))
          qa (cvec (I := I) x₀ qa (bB (E := E) l))) qa
        = (fun z : E => fderiv ℝ (chartMatFun g x₀) z (bB (E := E) l) i j) ((extChartAt I x₀) qa) :=
    fun qa hqa => mvfderiv_metric_coeff_eq (I := I) g x₀ hqa i j l
  rw [mvfderiv_eq_fderiv_of_eq_on_chart (I := I) (x₀ := x₀) (p := q)
    (F := fun qa : M => mvfderiv I (fun qb : M => g.inner qb
        (cvec (I := I) x₀ qb (bB (E := E) i)) (cvec (I := I) x₀ qb (bB (E := E) j)))
        qa (cvec (I := I) x₀ qa (bB (E := E) l)))
    (G := fun z : E => fderiv ℝ (chartMatFun g x₀) z (bB (E := E) l) i j)
    hq h5 hpoint (bB (E := E) k)]
  exact fderiv_second_entry (I := I) g x₀ hy k l i j


/-- The first coordinate partial of the chart matrix is smooth as a function of the chart
coordinate. -/
lemma contDiffAt_second_entry (g : Submission.Diff.SMet I M) (x₀ : M) {y : E}
    (hy : y ∈ (extChartAt I x₀).target) (l i j : Fin (Module.finrank ℝ E)) :
    ContDiffAt ℝ ∞ (fun z : E => fderiv ℝ (chartMatFun g x₀) z (bB (E := E) l) i j) y := by
  have hA : ContDiffAt ℝ ∞ (chartMatFun g x₀) y := contDiffAt_chartMatFun g x₀ hy
  have h2 : ContDiffAt ℝ ∞ (fun z : E => fderiv ℝ (chartMatFun g x₀) z) y := by
    simpa only [] using hA.fderiv_right (m := ∞) (by simp)
  have h3 : ContDiffAt ℝ ∞
      (fun z : E => fderiv ℝ (chartMatFun g x₀) z (bB (E := E) l)) y := by
    have h := ((ContinuousLinearMap.apply ℝ (MatE (E := E)) (bB (E := E) l)).contDiff.contDiffAt).comp y h2
    refine h.congr_of_eventuallyEq (Filter.Eventually.of_forall (fun z => ?_))
    rfl
  exact contDiffAt_entry (contDiffAt_entry h3 i) j

/-- The derivative of the chart matrix is symmetric in its two matrix indices. -/
lemma fderiv_chartMatFun_symm (g : Submission.Diff.SMet I M) (x₀ : M) {y : E}
    (hy : y ∈ (extChartAt I x₀).target) (v : E) (m n : Fin (Module.finrank ℝ E)) :
    fderiv ℝ (chartMatFun g x₀) y v m n = fderiv ℝ (chartMatFun g x₀) y v n m := by
  have hd : DifferentiableAt ℝ (chartMatFun g x₀) y :=
    (contDiffAt_chartMatFun g x₀ hy).differentiableAt (by simp)
  have hdm : DifferentiableAt ℝ (fun z : E => chartMatFun g x₀ z m) y :=
    differentiableAt_entry (fun z : E => chartMatFun g x₀ z) hd m
  have hdn : DifferentiableAt ℝ (fun z : E => chartMatFun g x₀ z n) y :=
    differentiableAt_entry (fun z : E => chartMatFun g x₀ z) hd n
  have hentry : (fun z : E => chartMatFun g x₀ z m n) = (fun z : E => chartMatFun g x₀ z n m) := by
    funext z
    rw [Work.Diff.EXT.chartMatFun]
    exact g.symm ((extChartAt I x₀).symm z) _ _
  have e1 : fderiv ℝ (fun z : E => chartMatFun g x₀ z m n) y v
      = (fderiv ℝ (chartMatFun g x₀) y v) m n := by
    rw [fderiv_apply_entry (fun z : E => chartMatFun g x₀ z m) hdm n,
      fderiv_apply_entry (fun z : E => chartMatFun g x₀ z) hd m]
  have e2 : fderiv ℝ (fun z : E => chartMatFun g x₀ z n m) y v
      = (fderiv ℝ (chartMatFun g x₀) y v) n m := by
    rw [fderiv_apply_entry (fun z : E => chartMatFun g x₀ z n) hdn m,
      fderiv_apply_entry (fun z : E => chartMatFun g x₀ z) hd n]
  rw [← e1, ← e2, hentry]

/-- **The derivative of the Koszul pairing is the second coordinate partial.** -/
lemma dOp_koszulPair_eq_sKzD_self (g : Submission.Diff.SMet I M) (x₀ : M) {y : E}
    (hy : y ∈ (extChartAt I x₀).target) (a b c d : Fin (Module.finrank ℝ E)) :
    Work.Diff.GE.dOp (I := I) x₀ a
        (Work.Diff.GE.koszulPair (I := I) (fun _ : ℝ => g) x₀ b d c) 0
        ((extChartAt I x₀).symm y)
      = sKzD (dJet2 g x₀ y) a b d c := by
  set p : M := (extChartAt I x₀).symm y with hp_def
  have hp : p ∈ (chartAt H' x₀).source := by
    have h1 : p ∈ (extChartAt I x₀).source := (extChartAt I x₀).map_target hy
    rwa [extChartAt_source] at h1
  have hchart : (extChartAt I x₀) p = y := (extChartAt I x₀).right_inv hy
  have hG : ContDiffAt ℝ ∞ (fun z : E => (1 / 2 : ℝ) •
      (fderiv ℝ (chartMatFun g x₀) z (bB (E := E) b) d c
        + fderiv ℝ (chartMatFun g x₀) z (bB (E := E) d) b c
        - fderiv ℝ (chartMatFun g x₀) z (bB (E := E) c) b d)) y :=
    ((((contDiffAt_second_entry g x₀ hy b d c).add
      (contDiffAt_second_entry g x₀ hy d b c)).sub
        (contDiffAt_second_entry g x₀ hy c b d)).const_smul (1 / 2 : ℝ))
  have hpoint : ∀ qa ∈ (chartAt H' x₀).source,
      (((Work.Diff.GE.koszulPair (I := I) (fun _ : ℝ => g) x₀ b d c)) 0) qa
        = (fun z : E => (1 / 2 : ℝ) •
            (fderiv ℝ (chartMatFun g x₀) z (bB (E := E) b) d c
              + fderiv ℝ (chartMatFun g x₀) z (bB (E := E) d) b c
              - fderiv ℝ (chartMatFun g x₀) z (bB (E := E) c) b d))
          ((extChartAt I x₀) qa) := by
    intro qa hqa
    have hqa' : qa ∈ (extChartAt I x₀).source := by rw [extChartAt_source]; exact hqa
    have hyq : (extChartAt I x₀) qa ∈ (extChartAt I x₀).target :=
      (extChartAt I x₀).map_source hqa'
    simp only [Work.Diff.GE.koszulPair, Work.Diff.GE.cFrame_apply]
    rw [mvfderiv_metric_coeff_eq (I := I) g x₀ hqa d c b,
      mvfderiv_metric_coeff_eq (I := I) g x₀ hqa c b d,
      mvfderiv_metric_coeff_eq (I := I) g x₀ hqa b d c,
      fderiv_chartMatFun_symm g x₀ hyq (bB (E := E) d) c b]
    ring_nf
  have hbridge := mvfderiv_eq_fderiv_of_eq_on_chart (I := I) (x₀ := x₀) (p := p)
    (F := ((Work.Diff.GE.koszulPair (I := I) (fun _ : ℝ => g) x₀ b d c)) 0)
    (G := fun z : E => (1 / 2 : ℝ) •
      (fderiv ℝ (chartMatFun g x₀) z (bB (E := E) b) d c
        + fderiv ℝ (chartMatFun g x₀) z (bB (E := E) d) b c
        - fderiv ℝ (chartMatFun g x₀) z (bB (E := E) c) b d))
    hp (by rw [hchart]; exact hG) hpoint (bB (E := E) a)
  rw [hchart] at hbridge
  have hf : fderiv ℝ (fun z : E => (1 / 2 : ℝ) •
      (fderiv ℝ (chartMatFun g x₀) z (bB (E := E) b) d c
        + fderiv ℝ (chartMatFun g x₀) z (bB (E := E) d) b c
        - fderiv ℝ (chartMatFun g x₀) z (bB (E := E) c) b d)) y (bB (E := E) a)
      = sKzD (dJet2 g x₀ y) a b d c := by
    have hD1 : HasFDerivAt
        (fun z : E => fderiv ℝ (chartMatFun g x₀) z (bB (E := E) b) d c)
        (fderiv ℝ (fun z : E => fderiv ℝ (chartMatFun g x₀) z (bB (E := E) b) d c) y) y :=
      ((contDiffAt_second_entry g x₀ hy b d c).differentiableAt (by simp)).hasFDerivAt
    have hD2 : HasFDerivAt
        (fun z : E => fderiv ℝ (chartMatFun g x₀) z (bB (E := E) d) b c)
        (fderiv ℝ (fun z : E => fderiv ℝ (chartMatFun g x₀) z (bB (E := E) d) b c) y) y :=
      ((contDiffAt_second_entry g x₀ hy d b c).differentiableAt (by simp)).hasFDerivAt
    have hD3 : HasFDerivAt
        (fun z : E => fderiv ℝ (chartMatFun g x₀) z (bB (E := E) c) b d)
        (fderiv ℝ (fun z : E => fderiv ℝ (chartMatFun g x₀) z (bB (E := E) c) b d) y) y :=
      ((contDiffAt_second_entry g x₀ hy c b d).differentiableAt (by simp)).hasFDerivAt
    have hcomb : HasFDerivAt (fun z : E => (1 / 2 : ℝ) •
        (fderiv ℝ (chartMatFun g x₀) z (bB (E := E) b) d c
          + fderiv ℝ (chartMatFun g x₀) z (bB (E := E) d) b c
          - fderiv ℝ (chartMatFun g x₀) z (bB (E := E) c) b d))
        ((1 / 2 : ℝ) • ((fderiv ℝ (fun z : E => fderiv ℝ (chartMatFun g x₀) z (bB (E := E) b) d c) y
            + fderiv ℝ (fun z : E => fderiv ℝ (chartMatFun g x₀) z (bB (E := E) d) b c) y)
          - fderiv ℝ (fun z : E => fderiv ℝ (chartMatFun g x₀) z (bB (E := E) c) b d) y)) y :=
      (((hD1.add hD2).sub hD3).const_smul (1 / 2 : ℝ))
    rw [hcomb.fderiv]
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.sub_apply,
      ContinuousLinearMap.smul_apply, sKzD]
    rw [fderiv_second_entry (I := I) g x₀ hy a b d c,
      fderiv_second_entry (I := I) g x₀ hy a d b c,
      fderiv_second_entry (I := I) g x₀ hy a c b d]
    rw [smul_eq_mul]
  show mvfderiv I (((Work.Diff.GE.koszulPair (I := I) (fun _ : ℝ => g) x₀ b d c)) 0) p
      (cvec (I := I) x₀ p (bB (E := E) a)) = sKzD (dJet2 g x₀ y) a b d c
  rw [hbridge, hf]


end Bridges

section Conversion

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [CompleteSpace E]
variable {H' : Type*} [TopologicalSpace H'] {I : ModelWithCorners ℝ E H'}
variable {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H' M]
  [IsManifold I (⊤ : ℕ∞) M] [I.Boundaryless]

/-- The Gram matrix of the chart frame of the constant family `t ↦ g` at `(0, p)` is the chart
matrix of `g` at the chart coordinate `y`. -/
lemma GramInv_const_eq (g : Submission.Diff.SMet I M) (x₀ : M) (y : E) :
    Work.Diff.GE.GramInv (I := I) (fun _ : ℝ => g) x₀ 0 ((extChartAt I x₀).symm y)
      = (Matrix.of (dJet0 g x₀ y))⁻¹ := by
  have hG : Work.Diff.GE.GramM (I := I) (fun _ : ℝ => g) x₀ 0 ((extChartAt I x₀).symm y)
      = Matrix.of (dJet0 g x₀ y) := rfl
  unfold Work.Diff.GE.GramInv
  rw [hG]

/-- **`rmChartExpr` in terms of the scalar `2`-jet**: the Koszul/Christoffel coordinate expression
for the curvature, whose ingredients are the frame-metric components and their coordinate
derivatives, is the scalar-jet curvature formula `sRm`. -/
lemma rmChartExpr_eq_sRm (g : Submission.Diff.SMet I M) (x₀ : M) {y : E}
    (hy : y ∈ (extChartAt I x₀).target) (a b c d : Fin (Module.finrank ℝ E)) :
    Work.Diff.GE.rmChartExpr (I := I) (fun _ : ℝ => g) x₀ a b c d 0
        ((extChartAt I x₀).symm y)
      = sRm (dJet0 g x₀ y) (dJet1 g x₀ y) (dJet2 g x₀ y) a b c d := by
  have hKz : ∀ m n o : Fin (Module.finrank ℝ E),
      Work.Diff.GE.koszulPair (I := I) (fun _ : ℝ => g) x₀ m n o 0
          ((extChartAt I x₀).symm y)
        = sKz (dJet1 g x₀ y) m n o := fun m n o => by
    exact koszulPair_eq_sKz_self g x₀ hy m n o
  have hKzD : ∀ a b c d : Fin (Module.finrank ℝ E),
      Work.Diff.GE.dOp (I := I) x₀ a
          (Work.Diff.GE.koszulPair (I := I) (fun _ : ℝ => g) x₀ b d c) 0
          ((extChartAt I x₀).symm y)
        = sKzD (dJet2 g x₀ y) a b d c := fun a b c d => by
    exact dOp_koszulPair_eq_sKzD_self g x₀ hy a b c d
  simp only [Work.Diff.GE.rmChartExpr, hKz, hKzD, GramInv_const_eq, sRm, sKz, sKzD, sInv]
  ring

end Conversion


section Ridge

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [CompleteSpace E]
variable {H' : Type*} [TopologicalSpace H'] {I : ModelWithCorners ℝ E H'}
variable {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H' M]
  [IsManifold I (⊤ : ℕ∞) M] [I.Boundaryless]

/-- `mvfderiv` only depends on the germ of the function. -/
theorem ridge_mvfderiv_congr_eventuallyEq {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f₁ f₂ : M → F} {x : M} (h : f₁ =ᶠ[𝓝 x] f₂) :
    mvfderiv I f₁ x = mvfderiv I f₂ x := by
  rw [mvfderiv, mvfderiv, h.eq_of_nhds, Filter.EventuallyEq.mfderiv_eq h]
  all_goals first | rfl | (ext v; rfl)

/-- The frame vector of the Christoffel symbol is the covariant derivative of the corresponding
coordinate frame field: `frameVector (Γ^m_{ab}) = ∇_{σ_a}σ_b`. -/
lemma ridge_frameVector_chrB
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
    (G : ℝ → Submission.Diff.SMet I M) (x₀ : M) (t : ℝ) {y : M}
    (hy : y ∈ (chartAt H' x₀).source) (a b : Fin (Module.finrank ℝ E)) :
    Submission.Geodesic.frameVector (I := I) x₀ y
        (Submission.ChartCurv.chrB (Submission.Diff.lcOf (G t)) x₀ y
          (Work.Diff.GE.cBasis (E := E) a) (Work.Diff.GE.cBasis (E := E) b))
      = (Submission.Diff.lcOf (G t))
          (Submission.Geodesic.frameSection (I := I) x₀ (Work.Diff.GE.cBasis (E := E) a)) y
          (Submission.Geodesic.frameVector (I := I) x₀ y (Work.Diff.GE.cBasis (E := E) b)) := by
  rw [Submission.ChartCurv.chrB_apply, Submission.Geodesic.christoffelEval_def]
  exact Bundle.Trivialization.symmL_continuousLinearMapAt _ (by simpa using hy) _

/-- **Product rule for the coordinate Christoffel pairing.**  On the chart source the Koszul
pairing is `⟨∇_{σ_B}σ_Dd, σ_K⟩`, so the left side is `∂_A⟨∇_{σ_B}σ_Dd, σ_K⟩`; metric
compatibility turns this into `⟨∇_A∇_Bσ_Dd, σ_K⟩ + ⟨∇_Bσ_Dd, ∇_Aσ_K⟩`, and both terms are written
in coordinates with `Submission.ChartCurv.cov_eq_frameVector_coordFun`. -/
theorem pcj_dOp_koszulPair_eq
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M]
    [IsManifold I (⊤ : ℕ∞) M] [I.Boundaryless]
    (hLC : Submission.Diff.LCSmooth I M) (G : ℝ → Submission.Diff.SMet I M) (x₀ : M) (t : ℝ)
    {y : M} (hy : y ∈ (chartAt H x₀).source) (A B Dd K : Fin (Module.finrank ℝ E)) :
    Work.Diff.GE.dOp (I := I) x₀ A (Work.Diff.GE.koszulPair (I := I) G x₀ B Dd K) t y
      = Work.Diff.GE.cGram (G t) x₀ y
          (Submission.ChartCurv.dB (Submission.Diff.lcOf (G t)) x₀ y
            (Work.Diff.GE.cBasis (E := E) A) (Work.Diff.GE.cBasis (E := E) Dd)
            (Work.Diff.GE.cBasis (E := E) B))
          (Work.Diff.GE.cBasis (E := E) K)
        + Work.Diff.GE.cGram (G t) x₀ y
            (Submission.ChartCurv.chrB (Submission.Diff.lcOf (G t)) x₀ y
              (Submission.ChartCurv.chrB (Submission.Diff.lcOf (G t)) x₀ y
                (Work.Diff.GE.cBasis (E := E) Dd) (Work.Diff.GE.cBasis (E := E) B))
              (Work.Diff.GE.cBasis (E := E) A))
            (Work.Diff.GE.cBasis (E := E) K)
        + Work.Diff.GE.cGram (G t) x₀ y
            (Submission.ChartCurv.chrB (Submission.Diff.lcOf (G t)) x₀ y
              (Work.Diff.GE.cBasis (E := E) Dd) (Work.Diff.GE.cBasis (E := E) B))
            (Submission.ChartCurv.chrB (Submission.Diff.lcOf (G t)) x₀ y
              (Work.Diff.GE.cBasis (E := E) K) (Work.Diff.GE.cBasis (E := E) A)) := by
  classical
  letI : Bundle.RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨(G t).toRiemannianMetric⟩
  haveI : IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x) := inferInstance
  haveI : (Submission.Diff.lcOf (G t)).ContMDiffCovariantDerivative ∞ := (hLC (G t)).1.some
  have hinn : ∀ (y' : M) (u v : TangentSpace I y'), Inner.inner ℝ u v = (G t).inner y' u v :=
    fun _ _ _ => rfl
  -- **step 1**: the left-hand side is `∂_A ⟪U, σ_K⟫` for `U = ∇_{σ_B}σ_Dd`
  set U : Π q : M, TangentSpace I q :=
    fun q => (Submission.Diff.lcOf (G t)) (Work.Diff.GE.cFrame (I := I) x₀ Dd) q
      (Work.Diff.GE.cFrame (I := I) x₀ B q) with hU
  set X : Π q : M, TangentSpace I q := Work.Diff.GE.cFrame (I := I) x₀ A with hX
  set V : Π q : M, TangentSpace I q := Work.Diff.GE.cFrame (I := I) x₀ K with hV
  have hstep1 : Work.Diff.GE.dOp (I := I) x₀ A (Work.Diff.GE.koszulPair (I := I) G x₀ B Dd K) t y
      = mvfderiv I (fun q : M => Inner.inner ℝ (U q) (V q)) y (X y) := by
    have hgerm0 : (fun q : M => Work.Diff.GE.koszulPair (I := I) G x₀ B Dd K t q)
        =ᶠ[𝓝 y] (fun q : M => Inner.inner ℝ (U q) (V q)) := by
      filter_upwards [(chartAt H x₀).open_source.mem_nhds hy] with q hq
      rw [← Work.Diff.GE.fPair_eq_koszul (I := I) G x₀ t hq B Dd K]
      simp only [Work.Diff.GE.fPair, Work.Diff.GE.cFrame_apply, hU, hV]
      exact (hinn q _ _).symm
    have hdOp : Work.Diff.GE.dOp (I := I) x₀ A (Work.Diff.GE.koszulPair (I := I) G x₀ B Dd K) t y
        = mvfderiv I (fun q : M => Work.Diff.GE.koszulPair (I := I) G x₀ B Dd K t q) y
            (Work.Diff.GE.cFrame (I := I) x₀ A y) := rfl
    have hXc : Work.Diff.GE.cFrame (I := I) x₀ A y = X y := congrFun hX.symm y
    have hmveq : mvfderiv I (fun q : M => Work.Diff.GE.koszulPair (I := I) G x₀ B Dd K t q) y
        = mvfderiv I (fun q : M => Inner.inner ℝ (U q) (V q)) y :=
      ridge_mvfderiv_congr_eventuallyEq (I := I) hgerm0
    rw [hdOp, hXc, hmveq]
  -- **step 2**: smooth extensions of the coordinate frame fields, and `W = ∇_{S_Dd}S_B`
  obtain ⟨SB, hSBsm, hSBeq⟩ :=
    Submission.ChartConnection.exists_contMDiff_section_eventuallyEq_frameSection
      (I := I) x₀ (Work.Diff.GE.cBasis (E := E) B) hy
  obtain ⟨SD, hSDsm, hSDeq⟩ :=
    Submission.ChartConnection.exists_contMDiff_section_eventuallyEq_frameSection
      (I := I) x₀ (Work.Diff.GE.cBasis (E := E) Dd) hy
  set W : Π q : M, TangentSpace I q :=
    fun q => (Submission.Diff.lcOf (G t)) SD q (SB q) with hW
  have hWsm : CMDiff ∞ (T% W) := by
    have h := Commons.Geometry.Manifold.VectorBundle.CovariantDerivative.contMDiff_cov_apply
      (Submission.Diff.lcOf (G t)) (inferInstance) hSDsm hSBsm
    simpa only [hW] using h
  have hWmd : MDiffAt (T% W) y := hWsm.contMDiffAt.mdifferentiableAt (by simp)
  -- the germ of `W` at `y` is the germ of `U`
  have hUW : U =ᶠ[𝓝 y] W := by
    obtain ⟨sD, hsDmem, hsD⟩ := Filter.eventually_iff_exists_mem.mp hSDeq
    obtain ⟨sB, hsBmem, hsB⟩ := Filter.eventually_iff_exists_mem.mp hSBeq
    set Ω : Set M := interior (sD ∩ sB ∩ (chartAt H x₀).source) with hΩ
    have hΩopen : IsOpen Ω := isOpen_interior
    have hΩmem : Ω ∈ 𝓝 y := hΩopen.mem_nhds (mem_interior_iff_mem_nhds.mpr
      (Filter.inter_mem (Filter.inter_mem hsDmem hsBmem)
        ((chartAt H x₀).open_source.mem_nhds hy)))
    have hΩsub : Ω ⊆ sD ∩ sB ∩ (chartAt H x₀).source := interior_subset
    filter_upwards [hΩmem] with q hq
    have hqsrc : q ∈ (chartAt H x₀).source := (hΩsub hq).2
    have hqD : SD =ᶠ[𝓝 q]
        Submission.Geodesic.frameSection (I := I) x₀ (Work.Diff.GE.cBasis (E := E) Dd) :=
      Filter.eventually_of_mem (hΩopen.mem_nhds hq) (fun r hr => hsD r ((hΩsub hr).1.1))
    have hcovD : (Submission.Diff.lcOf (G t)) SD q
        = (Submission.Diff.lcOf (G t))
            (Submission.Geodesic.frameSection (I := I) x₀ (Work.Diff.GE.cBasis (E := E) Dd)) q :=
      (Submission.Diff.lcOf (G t)).isCovariantDerivativeOn.congr_of_eventuallyEq
        (hSDsm.contMDiffAt.mdifferentiableAt (by simp))
        ((Work.Diff.EXT.contMDiffAt_frameVector (I := I) x₀ (Work.Diff.GE.cBasis (E := E) Dd)
          hqsrc).mdifferentiableAt (by simp))
        Filter.univ_mem hqD
    simp only [hU, hW, hcovD, hsB q ((hΩsub hq).1.2), Work.Diff.GE.cFrame]
  have hVmd : MDiffAt (T% V) y := by
    have h := (Work.Diff.EXT.contMDiffAt_frameVector (I := I) x₀ (Work.Diff.GE.cBasis (E := E) K)
      hy).mdifferentiableAt (by simp)
    simpa only [hV, Work.Diff.GE.cFrame, Submission.Geodesic.frameSection_eq_frameVector]
      using h
  -- a globally smooth extension of `σ_K`, so that metric compatibility can be applied
  obtain ⟨SK, hSKsm, hSKeq⟩ :=
    Submission.ChartConnection.exists_contMDiff_section_eventuallyEq_frameSection
      (I := I) x₀ (Work.Diff.GE.cBasis (E := E) K) hy
  have hSKmd : MDiffAt (T% SK) y := hSKsm.contMDiffAt.mdifferentiableAt (by simp)
  have hSKeqV : SK =ᶠ[𝓝 y] V := by
    filter_upwards [hSKeq] with q hq
    simp only [hq, hV, Work.Diff.GE.cFrame]
  -- **step 3**: metric compatibility (the Leibniz rule for the pairing)
  have hLeib : mvfderiv I (fun q : M => Inner.inner ℝ (U q) (V q)) y (X y)
      = Inner.inner ℝ ((Submission.Diff.lcOf (G t)) W y (X y)) (V y)
        + Inner.inner ℝ (U y) ((Submission.Diff.lcOf (G t)) V y (X y)) := by
    have hgerm2 : (fun q : M => Inner.inner ℝ (W q) (SK q))
        =ᶠ[𝓝 y] (fun q : M => Inner.inner ℝ (U q) (V q)) := by
      filter_upwards [hUW, hSKeqV] with q hq1 hq2
      simp only [hq1, hq2]
    have hmv : mvfderiv I (fun q : M => Inner.inner ℝ (U q) (V q)) y
        = mvfderiv I (fun q : M => Inner.inner ℝ (W q) (SK q)) y :=
      ridge_mvfderiv_congr_eventuallyEq (I := I) hgerm2.symm
    have hmetric := (hLC (G t)).2.2 W SK hWsm hSKsm y (X y)
    have hclm := (Submission.Diff.lcOf (G t)).isCovariantDerivativeOn.congr_of_eventuallyEq
      hSKmd hVmd Filter.univ_mem hSKeqV
    rw [hmv, hmetric]
    simp only [hUW.self_of_nhds, hSKeqV.self_of_nhds, hclm]
  -- **step 4**: compute the two terms
  have hcoordU : ∀ q ∈ (chartAt H x₀).source,
      Submission.ChartCurv.coordFun x₀ U q
        = Submission.ChartCurv.chrB (Submission.Diff.lcOf (G t)) x₀ q
            (Work.Diff.GE.cBasis (E := E) Dd) (Work.Diff.GE.cBasis (E := E) B) := by
    intro q hq
    rw [Submission.ChartCurv.coordFun_apply, hU, Submission.ChartCurv.chrB_apply,
      Submission.Geodesic.christoffelEval_def]
    rfl
  have hcoordWy : Submission.ChartCurv.coordFun x₀ W y
      = Submission.ChartCurv.chrB (Submission.Diff.lcOf (G t)) x₀ y
          (Work.Diff.GE.cBasis (E := E) Dd) (Work.Diff.GE.cBasis (E := E) B) := by
    rw [Submission.ChartCurv.coordFun_apply, ← hUW.self_of_nhds,
      ← Submission.ChartCurv.coordFun_apply]
    exact hcoordU y hy
  have hdcoord : mvfderiv I (Submission.ChartCurv.coordFun x₀ W) y
      = mvfderiv I (fun q : M => Submission.ChartCurv.chrB (Submission.Diff.lcOf (G t)) x₀ q
          (Work.Diff.GE.cBasis (E := E) Dd) (Work.Diff.GE.cBasis (E := E) B)) y := by
    refine ridge_mvfderiv_congr_eventuallyEq (I := I) ?_
    filter_upwards [hUW, (chartAt H x₀).open_source.mem_nhds hy] with q hq hqsrc
    rw [Submission.ChartCurv.coordFun_apply, ← hq, ← Submission.ChartCurv.coordFun_apply]
    exact hcoordU q hqsrc
  have hcovW : (Submission.Diff.lcOf (G t)) W y
        (Submission.Geodesic.frameVector (I := I) x₀ y (Work.Diff.GE.cBasis (E := E) A))
      = Submission.Geodesic.frameVector (I := I) x₀ y
          (Submission.ChartCurv.dB (Submission.Diff.lcOf (G t)) x₀ y
              (Work.Diff.GE.cBasis (E := E) A) (Work.Diff.GE.cBasis (E := E) Dd)
              (Work.Diff.GE.cBasis (E := E) B)
            + Submission.ChartCurv.chrB (Submission.Diff.lcOf (G t)) x₀ y
                (Submission.ChartCurv.chrB (Submission.Diff.lcOf (G t)) x₀ y
                  (Work.Diff.GE.cBasis (E := E) Dd) (Work.Diff.GE.cBasis (E := E) B))
                (Work.Diff.GE.cBasis (E := E) A)) := by
    rw [Submission.ChartCurv.cov_eq_frameVector_coordFun (x₀ := x₀) (W := W) hWsm hy
      (v := Work.Diff.GE.cBasis (E := E) A)]
    congr 1
    rw [hdcoord, hcoordWy]
    rfl
  have hUy : U y = Submission.Geodesic.frameVector (I := I) x₀ y
      (Submission.ChartCurv.chrB (Submission.Diff.lcOf (G t)) x₀ y
        (Work.Diff.GE.cBasis (E := E) Dd) (Work.Diff.GE.cBasis (E := E) B)) :=
    (ridge_frameVector_chrB (I := I) G x₀ t hy Dd B).symm
  have hVy : V y = Submission.Geodesic.frameVector (I := I) x₀ y
      (Work.Diff.GE.cBasis (E := E) K) := by
    rw [hV, Work.Diff.GE.cFrame_apply]
  have hXy : X y = Submission.Geodesic.frameVector (I := I) x₀ y
      (Work.Diff.GE.cBasis (E := E) A) := by
    rw [hX, Work.Diff.GE.cFrame_apply]
  have hcovV : (Submission.Diff.lcOf (G t)) V y
        (Submission.Geodesic.frameVector (I := I) x₀ y (Work.Diff.GE.cBasis (E := E) A))
      = Submission.Geodesic.frameVector (I := I) x₀ y
          (Submission.ChartCurv.chrB (Submission.Diff.lcOf (G t)) x₀ y
            (Work.Diff.GE.cBasis (E := E) K) (Work.Diff.GE.cBasis (E := E) A)) := by
    have h := ridge_frameVector_chrB (I := I) G x₀ t hy K A
    rw [hV]
    exact h.symm
  have ht1 : Inner.inner ℝ ((Submission.Diff.lcOf (G t)) W y (X y)) (V y)
      = Work.Diff.GE.cGram (G t) x₀ y
          (Submission.ChartCurv.dB (Submission.Diff.lcOf (G t)) x₀ y
            (Work.Diff.GE.cBasis (E := E) A) (Work.Diff.GE.cBasis (E := E) Dd)
            (Work.Diff.GE.cBasis (E := E) B))
          (Work.Diff.GE.cBasis (E := E) K)
        + Work.Diff.GE.cGram (G t) x₀ y
            (Submission.ChartCurv.chrB (Submission.Diff.lcOf (G t)) x₀ y
              (Submission.ChartCurv.chrB (Submission.Diff.lcOf (G t)) x₀ y
                (Work.Diff.GE.cBasis (E := E) Dd) (Work.Diff.GE.cBasis (E := E) B))
              (Work.Diff.GE.cBasis (E := E) A))
            (Work.Diff.GE.cBasis (E := E) K) := by
    rw [hXy, hcovW, hVy, hinn y]
    rw [← Work.Diff.GE.cGram_apply (G t) x₀ y _ (Work.Diff.GE.cBasis (E := E) K)]
    rw [Work.Diff.GE.cGram_add_fst]
  have ht2 : Inner.inner ℝ (U y) ((Submission.Diff.lcOf (G t)) V y (X y))
      = Work.Diff.GE.cGram (G t) x₀ y
          (Submission.ChartCurv.chrB (Submission.Diff.lcOf (G t)) x₀ y
            (Work.Diff.GE.cBasis (E := E) Dd) (Work.Diff.GE.cBasis (E := E) B))
          (Submission.ChartCurv.chrB (Submission.Diff.lcOf (G t)) x₀ y
            (Work.Diff.GE.cBasis (E := E) K) (Work.Diff.GE.cBasis (E := E) A)) := by
    rw [hUy, hXy, hcovV, hinn y]
    rw [← Work.Diff.GE.cGram_apply (G t) x₀ y _ _]
  rw [hstep1, hLeib, ht1, ht2]

end Ridge

section Target

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [CompleteSpace E]
variable {H' : Type*} [TopologicalSpace H'] {I : ModelWithCorners ℝ E H'}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H' M] [IsManifold I (⊤ : ℕ∞) M]
  [I.Boundaryless] [T2Space M]

/-- **`rmC4 = rmChartExpr`.**  The frozen coordinate-frame curvature components are the explicit
Koszul/Christoffel expression: expand `cCurv` in the coordinate frame and apply the product rule
`pcj_dOp_koszulPair_eq` to the two `dOp` terms and the γ-collapse
`cGram_chrB_chrB_eq_sum_koszul` to the two quadratic terms. -/
theorem pcj_rmC4_rmChartExpr
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H' : Type*} [TopologicalSpace H'] {I : ModelWithCorners ℝ E H'}
    {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H' M]
    [IsManifold I (⊤ : ℕ∞) M] [I.Boundaryless]
    (hLC : Submission.Diff.LCSmooth I M) (G : ℝ → Submission.Diff.SMet I M) (x₀ : M) (t : ℝ)
    {y : M} (hy : y ∈ (chartAt H' x₀).source) (i j k l : Fin (Module.finrank ℝ E)) :
    Work.Diff.GE.rmC4 (I := I) G x₀ t y i j k l
      = Work.Diff.GE.rmChartExpr (I := I) G x₀ i j k l t y := by
  letI : Bundle.RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨(G t).toRiemannianMetric⟩
  haveI : IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x) := inferInstance
  set g := G t with hg
  have hsplit : Work.Diff.GE.cCurv g x₀ y (Work.Diff.GE.cBasis (E := E) i)
        (Work.Diff.GE.cBasis (E := E) j) (Work.Diff.GE.cBasis (E := E) l)
      = (Submission.ChartCurv.dB (Submission.Diff.lcOf g) x₀ y (Work.Diff.GE.cBasis (E := E) i)
            (Work.Diff.GE.cBasis (E := E) l) (Work.Diff.GE.cBasis (E := E) j)
          + Submission.ChartCurv.chrB (Submission.Diff.lcOf g) x₀ y
              (Submission.ChartCurv.chrB (Submission.Diff.lcOf g) x₀ y
                (Work.Diff.GE.cBasis (E := E) l) (Work.Diff.GE.cBasis (E := E) j))
              (Work.Diff.GE.cBasis (E := E) i))
        - (Submission.ChartCurv.dB (Submission.Diff.lcOf g) x₀ y (Work.Diff.GE.cBasis (E := E) j)
            (Work.Diff.GE.cBasis (E := E) l) (Work.Diff.GE.cBasis (E := E) i)
          + Submission.ChartCurv.chrB (Submission.Diff.lcOf g) x₀ y
              (Submission.ChartCurv.chrB (Submission.Diff.lcOf g) x₀ y
                (Work.Diff.GE.cBasis (E := E) l) (Work.Diff.GE.cBasis (E := E) i))
              (Work.Diff.GE.cBasis (E := E) j)) := by
    simp only [Work.Diff.GE.cCurv]
    abel
  have hBi := pcj_dOp_koszulPair_eq (I := I) hLC G x₀ t hy i j l k
  have hBi' : Work.Diff.GE.cGram g x₀ y
          (Submission.ChartCurv.dB (Submission.Diff.lcOf g) x₀ y (Work.Diff.GE.cBasis (E := E) i)
            (Work.Diff.GE.cBasis (E := E) l) (Work.Diff.GE.cBasis (E := E) j))
          (Work.Diff.GE.cBasis (E := E) k)
        + Work.Diff.GE.cGram g x₀ y
            (Submission.ChartCurv.chrB (Submission.Diff.lcOf g) x₀ y
              (Submission.ChartCurv.chrB (Submission.Diff.lcOf g) x₀ y
                (Work.Diff.GE.cBasis (E := E) l) (Work.Diff.GE.cBasis (E := E) j))
              (Work.Diff.GE.cBasis (E := E) i))
            (Work.Diff.GE.cBasis (E := E) k)
      = Work.Diff.GE.dOp (I := I) x₀ i (Work.Diff.GE.koszulPair (I := I) G x₀ j l k) t y
        - Work.Diff.GE.cGram g x₀ y
            (Submission.ChartCurv.chrB (Submission.Diff.lcOf g) x₀ y
              (Work.Diff.GE.cBasis (E := E) l) (Work.Diff.GE.cBasis (E := E) j))
            (Submission.ChartCurv.chrB (Submission.Diff.lcOf g) x₀ y
              (Work.Diff.GE.cBasis (E := E) k) (Work.Diff.GE.cBasis (E := E) i)) := by
    linarith [hBi]
  have hBj := pcj_dOp_koszulPair_eq (I := I) hLC G x₀ t hy j i l k
  have hBj' : Work.Diff.GE.cGram g x₀ y
          (Submission.ChartCurv.dB (Submission.Diff.lcOf g) x₀ y (Work.Diff.GE.cBasis (E := E) j)
            (Work.Diff.GE.cBasis (E := E) l) (Work.Diff.GE.cBasis (E := E) i))
          (Work.Diff.GE.cBasis (E := E) k)
        + Work.Diff.GE.cGram g x₀ y
            (Submission.ChartCurv.chrB (Submission.Diff.lcOf g) x₀ y
              (Submission.ChartCurv.chrB (Submission.Diff.lcOf g) x₀ y
                (Work.Diff.GE.cBasis (E := E) l) (Work.Diff.GE.cBasis (E := E) i))
              (Work.Diff.GE.cBasis (E := E) j))
            (Work.Diff.GE.cBasis (E := E) k)
      = Work.Diff.GE.dOp (I := I) x₀ j (Work.Diff.GE.koszulPair (I := I) G x₀ i l k) t y
        - Work.Diff.GE.cGram g x₀ y
            (Submission.ChartCurv.chrB (Submission.Diff.lcOf g) x₀ y
              (Work.Diff.GE.cBasis (E := E) l) (Work.Diff.GE.cBasis (E := E) i))
            (Submission.ChartCurv.chrB (Submission.Diff.lcOf g) x₀ y
              (Work.Diff.GE.cBasis (E := E) k) (Work.Diff.GE.cBasis (E := E) j)) := by
    linarith [hBj]
  have hCi := cGram_chrB_chrB_eq_sum_koszul (I := I) hLC G x₀ t hy j l i k
  have hCj := cGram_chrB_chrB_eq_sum_koszul (I := I) hLC G x₀ t hy i l j k
  have h1 : Work.Diff.GE.rmC4 (I := I) G x₀ t y i j k l
      = Work.Diff.GE.cGram g x₀ y
          (Work.Diff.GE.cCurv g x₀ y (Work.Diff.GE.cBasis (E := E) i)
            (Work.Diff.GE.cBasis (E := E) j) (Work.Diff.GE.cBasis (E := E) l))
          (Work.Diff.GE.cBasis (E := E) k) := by
    rw [Work.Diff.GE.rmC4_eq_cRm (I := I) hLC G x₀ t hy i j k l]
    rfl
  rw [h1, hsplit, Work.Diff.GE.rmChartExpr]
  simp only [Work.Diff.GE.cGram_sub_fst, Work.Diff.GE.cGram_add_fst]
  rw [hBi', hBj', hCi, hCj]
  ring

end Target

section Target

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [CompleteSpace E]
variable {H' : Type*} [TopologicalSpace H'] {I : ModelWithCorners ℝ E H'}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H' M] [IsManifold I (⊤ : ℕ∞) M]
  [I.Boundaryless] [T2Space M]

theorem chartRic_partial_jet
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]
    [I.Boundaryless] [T2Space M] :
    ∃ Φ : E × (Work.Diff.EXT.MatE (E := E) ×
        (Fin (Module.finrank ℝ E) → Work.Diff.EXT.MatE (E := E)) ×
        (Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → Work.Diff.EXT.MatE (E := E))) →
        Work.Diff.EXT.MatE (E := E),
      ContDiffOn ℝ (⊤ : ℕ∞) Φ {z | (Matrix.of z.2.1).det ≠ 0} ∧
      ∀ (x₀ : M) (g : Submission.Diff.SMet I M) (y : E), y ∈ (extChartAt I x₀).target →
        Work.Diff.EXT.chartRicMat g x₀ y =
          Φ (y, Work.Diff.EXT.sJetData (fun p : ℝ × E => Work.Diff.EXT.chartMatFun g x₀ p.2) (0, y)) := by
  refine ⟨chartRicPhi, chartRicPhi_smooth, ?_⟩
  intro x₀ g y hy
  set p : M := (extChartAt I x₀).symm y with hp_def
  have hp : p ∈ (chartAt H x₀).source := by
    have h1 : p ∈ (extChartAt I x₀).source := (extChartAt I x₀).map_target hy
    rwa [extChartAt_source] at h1
  have hLC : Submission.Diff.LCSmooth I M := Work.Diff.T.lc_smooth
  rw [sJetData_chartMat g x₀ hy]
  funext i j
  have hAdef : Work.Diff.EXT.chartRicMat g x₀ y i j
      = Submission.Diff.ricAt (Submission.Diff.lcOf g) p
          (cvec (I := I) x₀ p (bB (E := E) i)) (cvec (I := I) x₀ p (bB (E := E) j)) := rfl
  rw [hAdef, ricAt_invGram_chart g x₀ hp i j]
  have hR : chartRicPhi (y, chartJet g x₀ y) i j
      = ∑ k, ∑ l, sInv (dJet0 g x₀ y) k l
          * sRm (dJet0 g x₀ y) (dJet1 g x₀ y) (dJet2 g x₀ y) k i l j := rfl
  rw [hR]
  refine Finset.sum_congr rfl (fun k _ => Finset.sum_congr rfl (fun l _ => ?_))
  have hterm : g.inner p
        (Submission.Diff.rmVec (Submission.Diff.lcOf g) p
          (cvec (I := I) x₀ p (bB (E := E) k)) (cvec (I := I) x₀ p (bB (E := E) i))
          (cvec (I := I) x₀ p (bB (E := E) j)))
        (cvec (I := I) x₀ p (bB (E := E) l))
      = sRm (dJet0 g x₀ y) (dJet1 g x₀ y) (dJet2 g x₀ y) k i l j := by
    have h1 : g.inner p
          (Submission.Diff.rmVec (Submission.Diff.lcOf g) p
            (cvec (I := I) x₀ p (bB (E := E) k)) (cvec (I := I) x₀ p (bB (E := E) i))
            (cvec (I := I) x₀ p (bB (E := E) j)))
          (cvec (I := I) x₀ p (bB (E := E) l))
        = Work.Diff.GE.rmC4 (I := I) (fun _ : ℝ => g) x₀ 0 p k i l j := rfl
    rw [h1, pcj_rmC4_rmChartExpr (I := I) hLC (fun _ : ℝ => g) x₀ 0 hp k i l j,
      rmChartExpr_eq_sRm (I := I) g x₀ hy k i l j]
  rw [hterm]
  congr 1

end Target

end Work.Diff.EXT
