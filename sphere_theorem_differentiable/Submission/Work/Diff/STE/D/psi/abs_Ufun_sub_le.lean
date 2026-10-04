import Mathlib
import Submission.Work.Diff.STE.D.psi.Core
import Submission.Work.Diff.STE.D.psi.Positivity
import Submission.Work.Diff.STE.D.psi.chartJetOf_genMap_affine
import Submission.Work.Diff.STE.D.psi.chartJetOf_jSym_bound
import Submission.Work.Diff.STE.D.psi.contDiffOn_secChartVal_chart
import Submission.Work.Diff.STE.D.psi.chartMatOf_pd_det_pos
import Submission.Work.Diff.STE.D.isSymm_genMap
import Submission.Work.Diff.STE.D.isSymm_addSec
import Submission.Work.Diff.Calc.taylor_bound_on_compact
import Submission.Work.Diff.STE.deTurck.posDef_gmat
import Submission.Work.Diff.STE.D.psi.JetAffine
import Submission.Work.Diff.STE.D.psi.abs_pref_le
import Submission.Work.Diff.STE.D.psi.abs_coord_factor_le
import Submission.Work.Diff.STE.D.psi.contDiffOn_joint_jetPairOf

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.STE.D.psi

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open Classical
open scoped Manifold ContDiff Bundle Topology BigOperators
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 8000000
set_option linter.unusedSectionVars false

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ((⊤ : ENat) : WithTop ENat) M] [T2Space M] [I.Boundaryless]
  {ι₀ : Type*} [Fintype ι₀] {g₀ : Submission.Diff.SMet I M} {ε : ℝ}

noncomputable section

/-! ## 0. Notation and the unfolded form of `Ufun` -/

/-- The coefficient space of the Galerkin scheme. -/
abbrev CS (ι₀ : Type*) [Fintype ι₀] (n : ℕ) (ε : ℝ) : Type _ :=
  Work.Diff.STE.B3.JIdx ι₀ n ε → ℝ

/-- The flat coordinate space. -/
abbrev Fl (n : ℕ) : Type _ := Fin n → ℝ

/-- The joint chart DeTurck expression: `Φ (c, y) = pPhiFun (jetPairOf g₀ D ε x₀ c (flatToE x₀ y))`.
It is the composite of the pair of jets with the chart DeTurck operator, so that its derivative in
the coefficients is the *linearisation* `pPhiFunD` evaluated on the corresponding direction. -/
noncomputable def PhiFun (g₀ : Submission.Diff.SMet I M)
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (ε : ℝ) (x₀ : M) :
    CS ι₀ (Module.finrank ℝ E) ε × Fl (Module.finrank ℝ E) →
      Work.Diff.EXT.MatE (E := E) :=
  fun q => Work.Diff.STE.D.pPhiFun (E := E)
    (Work.Diff.STE.D.jetPairOf (I := I) (M := M) g₀ D ε x₀ q.1
      (Work.Diff.STE.flatToE (I := I) x₀ q.2))

/-- The domain of the joint chart DeTurck expression: the flat point lies in the chart target and
the pair of jets in the smoothness locus of `pPhi`.  This is the set on which `PhiFun` is `C^∞`. -/
def JetDom (g₀ : Submission.Diff.SMet I M)
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (ε : ℝ) (x₀ : M) :
    Set (CS ι₀ (Module.finrank ℝ E) ε × Fl (Module.finrank ℝ E)) :=
  {q | Work.Diff.STE.flatToE (I := I) x₀ q.2 ∈ (extChartAt I x₀).target} ∩
    (fun q => Work.Diff.STE.D.jetPairOf (I := I) (M := M) g₀ D ε x₀ q.1
      (Work.Diff.STE.flatToE (I := I) x₀ q.2)) ⁻¹'
      Work.Diff.STE.deTurck.pPhiDom (E := E)

/-- The defining equation of `Ufun`, as a rewriting lemma. -/
@[simp] lemma Ufun_unfold (g₀ : Submission.Diff.SMet I M)
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (ε : ℝ)
    (z z' : Work.Diff.STE.B3.JIdx ι₀ (Module.finrank ℝ E) ε)
    (c₀ : Work.Diff.STE.B3.JIdx ι₀ (Module.finrank ℝ E) ε → ℝ)
    (y : Fin (Module.finrank ℝ E) → ℝ) :
    Work.Diff.STE.D.Ufun (I := I) (M := M) g₀ D ε z z' c₀ y =
      Work.Diff.STE.B3Data.psi (I := I) (M := M) D z.1 y *
        Real.sqrt (Work.Diff.STE.B3Data.dens (I := I) (M := M) D z.1 y) *
        ∑ j : Fin (Module.finrank ℝ E), ∑ k : Fin (Module.finrank ℝ E),
          Work.Diff.STE.D.coordCLM (I := I) (M := M) (D.x₀ z.1) (D.pt z.1 y) j
              (D.e z.1 z.2.1 (D.pt z.1 y))
            * Work.Diff.STE.D.coordCLM (I := I) (M := M) (D.x₀ z.1) (D.pt z.1 y) k
              (D.e z.1 z.2.2.1 (D.pt z.1 y))
            * (Work.Diff.STE.D.pPhiFunD (E := E)
                  (Work.Diff.STE.D.jetPairOf (I := I) (M := M) g₀ D ε (D.x₀ z.1) c₀
                    (Work.Diff.STE.flatToE (I := I) (D.x₀ z.1) y))
                  (Work.Diff.STE.D.jetDir (I := I) (M := M) g₀ D ε (D.x₀ z.1) z'
                    (Work.Diff.STE.flatToE (I := I) (D.x₀ z.1) y))) j k := rfl

/-! ## 1. The positivity ball -/

/-- **The positivity set of the Galerkin perturbation contains a ball around zero.** -/
lemma exists_isPos_ball_psi (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (ε : ℝ) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ c : CS ι₀ (Module.finrank ℝ E) ε,
      ‖c‖ < δ → Work.Diff.STE.D.IsPos (I := I) (M := M) g₀ D ε c := by
  have h : {c : CS ι₀ (Module.finrank ℝ E) ε |
      Work.Diff.STE.D.IsPos (I := I) (M := M) g₀ D ε c} ∈
      𝓝 (0 : CS ι₀ (Module.finrank ℝ E) ε) :=
    Work.Diff.STE.D.eventually_posDef (I := I) (M := M) D ε
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp h
  refine ⟨δ, hδ, fun c hc => hball ?_⟩
  rw [Metric.mem_ball, dist_zero_right]
  exact hc

/-! ## 2. Smoothness of the DeTurck expression and of the joint chart jet -/

/-- The set of pairs of jets on which the chart DeTurck expression is defined smoothly is open. -/
lemma isOpen_pPhiDom :
    IsOpen (Work.Diff.STE.deTurck.pPhiDom (E := E)) := by
  have h1 : Continuous fun w : Work.Diff.STE.deTurck.JetPair (E := E) =>
      (Matrix.of w.1.1).det :=
    Continuous.matrix_det (by fun_prop)
  have h2 : Continuous fun w : Work.Diff.STE.deTurck.JetPair (E := E) =>
      (Matrix.of w.2.1).det :=
    Continuous.matrix_det (by fun_prop)
  exact (isOpen_ne.preimage h1).inter (isOpen_ne.preimage h2)

/-- **The chart DeTurck expression is differentiable on its smoothness locus**, with derivative the
explicit linearisation `pPhiFunD`. -/
lemma hasFDerivAt_pPhiFun (w : Work.Diff.STE.deTurck.JetPair (E := E))
    (hw : w ∈ Work.Diff.STE.deTurck.pPhiDom (E := E)) :
    HasFDerivAt (Work.Diff.STE.D.pPhiFun (E := E))
      (Work.Diff.STE.D.pPhiFunD (E := E) w) w := by
  have h : ContDiffAt ℝ (⊤ : ℕ∞) (Work.Diff.STE.D.pPhiFun (E := E)) w :=
    (Work.Diff.STE.deTurck.contDiffOn_pPhi (E := E)).contDiffAt
      (isOpen_pPhiDom.mem_nhds hw)
  exact (h.differentiableAt (by simp)).hasFDerivAt

/-- **The joint chart jet is smooth on the chart-target locus.** -/
lemma contDiffOn_joint_jetPairOf' (hg : Work.Diff.STE.D.ChartData (I := I) (M := M) g₀.inner)
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (x₀ : M) :
    ContDiffOn ℝ (⊤ : ℕ∞)
      (fun q : CS ι₀ (Module.finrank ℝ E) ε × Fl (Module.finrank ℝ E) =>
        Work.Diff.STE.D.jetPairOf (I := I) (M := M) g₀ D ε x₀ q.1
          (Work.Diff.STE.flatToE (I := I) x₀ q.2))
      {q : CS ι₀ (Module.finrank ℝ E) ε × Fl (Module.finrank ℝ E) |
        Work.Diff.STE.flatToE (I := I) x₀ q.2 ∈ (extChartAt I x₀).target} :=
  Work.Diff.STE.D.psi.contDiffOn_joint_jetPairOf (I := I) (M := M) hg D x₀

/-- **The joint chart DeTurck expression is smooth on its domain.** -/
lemma contDiffOn_PhiFun (hg : Work.Diff.STE.D.ChartData (I := I) (M := M) g₀.inner)
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (x₀ : M) :
    ContDiffOn ℝ (⊤ : ℕ∞) (PhiFun (I := I) (M := M) g₀ D ε x₀)
      (JetDom (I := I) (M := M) g₀ D ε x₀) :=
  (Work.Diff.STE.deTurck.contDiffOn_pPhi (E := E)).comp
    ((contDiffOn_joint_jetPairOf' (I := I) (M := M) (ε := ε) hg D x₀).mono
      (fun q hq => hq.1))
    (fun q hq => hq.2)

/-- **The domain of the joint chart DeTurck expression is open.** -/
lemma isOpen_JetDom (hg : Work.Diff.STE.D.ChartData (I := I) (M := M) g₀.inner)
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (x₀ : M) :
    IsOpen (JetDom (I := I) (M := M) g₀ D ε x₀) := by
  have hU : IsOpen {q : CS ι₀ (Module.finrank ℝ E) ε × Fl (Module.finrank ℝ E) |
      Work.Diff.STE.flatToE (I := I) x₀ q.2 ∈ (extChartAt I x₀).target} :=
    (Work.Diff.STE.D.psi.isOpen_flatToE_preimage_target (I := I) x₀).preimage
      (continuous_snd : Continuous fun q : CS ι₀ (Module.finrank ℝ E) ε ×
        Fl (Module.finrank ℝ E) => q.2)
  have hcont := contDiffOn_joint_jetPairOf' (I := I) (M := M) (ε := ε) hg D x₀
  rw [isOpen_iff_mem_nhds]
  intro q hq
  have hqU : q ∈ {q : CS ι₀ (Module.finrank ℝ E) ε × Fl (Module.finrank ℝ E) |
      Work.Diff.STE.flatToE (I := I) x₀ q.2 ∈ (extChartAt I x₀).target} := hq.1
  have hc : ContinuousAt (fun q : CS ι₀ (Module.finrank ℝ E) ε × Fl (Module.finrank ℝ E) =>
      Work.Diff.STE.D.jetPairOf (I := I) (M := M) g₀ D ε x₀ q.1
        (Work.Diff.STE.flatToE (I := I) x₀ q.2)) q :=
    (hcont.continuousOn.continuousWithinAt hqU).continuousAt (hU.mem_nhds hqU)
  exact Filter.inter_mem (hU.mem_nhds hqU)
    (hc.preimage_mem_nhds (isOpen_pPhiDom.mem_nhds hq.2))

/-! ## 3. The domains: positivity implies membership in the smoothness locus -/

/-- **On the positivity set the pair of jets lies in the smoothness locus of `pPhi`.** -/
lemma jetPairOf_mem_pPhiDom (hg : Work.Diff.STE.D.ChartData (I := I) (M := M) g₀.inner)
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (x₀ : M)
    (c : CS ι₀ (Module.finrank ℝ E) ε) {y : Fl (Module.finrank ℝ E)}
    (hpos : Work.Diff.STE.D.IsPos (I := I) (M := M) g₀ D ε c)
    (hy : Work.Diff.STE.flatToE (I := I) x₀ y ∈ (extChartAt I x₀).target) :
    Work.Diff.STE.D.jetPairOf (I := I) (M := M) g₀ D ε x₀ c
      (Work.Diff.STE.flatToE (I := I) x₀ y) ∈ Work.Diff.STE.deTurck.pPhiDom (E := E) := by
  constructor
  · have hsrc : (extChartAt I x₀).symm (Work.Diff.STE.flatToE (I := I) x₀ y)
        ∈ (chartAt H x₀).source := by
      rw [← extChartAt_source (I := I) x₀]
      exact PartialEquiv.map_target (extChartAt I x₀) hy
    have hpd : (Matrix.of (Work.Diff.EXT.gmat (I := I) g₀ x₀
        ((extChartAt I x₀).symm (Work.Diff.STE.flatToE (I := I) x₀ y)))).PosDef :=
      Work.Diff.STE.deTurck.posDef_gmat (I := I) g₀ x₀ hsrc
    have h2 : (Work.Diff.STE.D.jetPairOf (I := I) (M := M) g₀ D ε x₀ c
        (Work.Diff.STE.flatToE (I := I) x₀ y)).1
        = Work.Diff.STE.D.chartJetOf (I := I) (M := M) g₀.inner x₀
          (Work.Diff.STE.flatToE (I := I) x₀ y) :=
      Work.Diff.STE.D.psi.jetPairOf_fst (I := I) (M := M) D x₀ c
        (Work.Diff.STE.flatToE (I := I) x₀ y)
    rw [h2]
    rw [Work.Diff.STE.D.psi.chartJetOf_fst_inner (I := I) (M := M)]
    exact ne_of_gt (Matrix.PosDef.det_pos hpd)
  · have hsymm : Work.Diff.STE.D.IsSymm (I := I)
        (Work.Diff.STE.D.addSec (I := I) g₀ (Work.Diff.STE.D.genMap (I := I) (M := M) D ε c)) :=
      Work.Diff.STE.D.isSymm_addSec (I := I) (ι₀ := ι₀)
        (Work.Diff.STE.D.genMap (I := I) (M := M) D ε c)
        (Work.Diff.STE.D.isSymm_genMap (I := I) (M := M) D ε c)
    have hpos' : ∀ (p : M) (v : TangentSpace I p), v ≠ 0 →
        0 < Work.Diff.STE.D.addSec (I := I) g₀
          (Work.Diff.STE.D.genMap (I := I) (M := M) D ε c) p v v := hpos
    have h2 : (Work.Diff.STE.D.jetPairOf (I := I) (M := M) g₀ D ε x₀ c
        (Work.Diff.STE.flatToE (I := I) x₀ y)).2
        = Work.Diff.STE.D.chartJetOf (I := I) (M := M)
          (Work.Diff.STE.D.addSec (I := I) g₀ (Work.Diff.STE.D.genMap (I := I) (M := M) D ε c))
          x₀ (Work.Diff.STE.flatToE (I := I) x₀ y) :=
      Work.Diff.STE.D.psi.jetPairOf_snd (I := I) (M := M) D x₀ c
        (Work.Diff.STE.flatToE (I := I) x₀ y)
    rw [h2]
    rw [Work.Diff.STE.D.psi.chartJetOf_fst (I := I) (M := M)]
    exact ne_of_gt (Work.Diff.STE.D.psi.chartMatOf_det_pos_of_posDef (I := I) (M := M) _ x₀
      hsymm hpos' hy)

/-! ## 4. The chain rule identity and the main estimate -/

/-- **The affine chart `c ↦ (c, y)`** of a normed space into a product with a fixed point has the
canonical inclusion as derivative. -/
lemma hasFDerivAt_pair_const {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] (c : X) (y : Y) :
    HasFDerivAt (fun c' : X => (c', y)) (ContinuousLinearMap.inl ℝ X Y) c := by
  have h1 : HasFDerivAt (fun c' : X => ((c', (0 : Y)) : X × Y))
      (ContinuousLinearMap.inl ℝ X Y) c :=
    (ContinuousLinearMap.inl ℝ X Y).hasFDerivAt
  have h2 : HasFDerivAt (fun _ : X => (((0 : X), y) : X × Y)) (0 : X →L[ℝ] X × Y) c :=
    hasFDerivAt_const (((0 : X), y) : X × Y) c
  have h3 : HasFDerivAt ((fun c' : X => ((c', (0 : Y)) : X × Y)) +
      fun _ : X => (((0 : X), y) : X × Y))
      ((ContinuousLinearMap.inl ℝ X Y) + (0 : X →L[ℝ] X × Y)) c := h1.add h2
  have h3' : HasFDerivAt ((fun c' : X => ((c', (0 : Y)) : X × Y)) +
      fun _ : X => (((0 : X), y) : X × Y)) (ContinuousLinearMap.inl ℝ X Y) c := by
    simpa only [add_zero] using h3
  refine h3'.congr_of_eventuallyEq ?_
  filter_upwards with c'
  simp [ContinuousLinearMap.inl_apply]

/-- **The chain rule identity**: the derivative of the joint chart DeTurck expression in the
direction of a basis vector of the coefficient space is the explicit linearisation of `pPhi`
evaluated on the corresponding direction vector. -/
lemma fderiv_PhiFun_apply_single (hg : Work.Diff.STE.D.ChartData (I := I) (M := M) g₀.inner)
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (x₀ : M)
    (z' : Work.Diff.STE.B3.JIdx ι₀ (Module.finrank ℝ E) ε)
    (c : CS ι₀ (Module.finrank ℝ E) ε) {y : Fl (Module.finrank ℝ E)}
    (hy : Work.Diff.STE.flatToE (I := I) x₀ y ∈ (extChartAt I x₀).target)
    (hdom : Work.Diff.STE.D.jetPairOf (I := I) (M := M) g₀ D ε x₀ c
      (Work.Diff.STE.flatToE (I := I) x₀ y) ∈ Work.Diff.STE.deTurck.pPhiDom (E := E)) :
    (fderiv ℝ (PhiFun (I := I) (M := M) g₀ D ε x₀) (c, y))
        ((Pi.single z' (1 : ℝ) : CS ι₀ (Module.finrank ℝ E) ε), (0 : Fl (Module.finrank ℝ E)))
      = Work.Diff.STE.D.pPhiFunD (E := E)
          (Work.Diff.STE.D.jetPairOf (I := I) (M := M) g₀ D ε x₀ c
            (Work.Diff.STE.flatToE (I := I) x₀ y))
          (Work.Diff.STE.D.jetDir (I := I) (M := M) g₀ D ε x₀ z'
            (Work.Diff.STE.flatToE (I := I) x₀ y)) := by
  have houter : HasFDerivAt
      (fun c : CS ι₀ (Module.finrank ℝ E) ε =>
        Work.Diff.STE.D.jetPairOf (I := I) (M := M) g₀ D ε x₀ c
          (Work.Diff.STE.flatToE (I := I) x₀ y))
      (Work.Diff.STE.D.psi.jetDirLin (I := I) (M := M) g₀ D ε x₀
        (Work.Diff.STE.flatToE (I := I) x₀ y)) c :=
    Work.Diff.STE.D.psi.hasFDerivAt_jetPairOf (I := I) (M := M) hg D ε x₀ c hy
  -- The derivative of the *partial* map, with the chart coordinate frozen:
  have hp : HasFDerivAt
      (fun c' : CS ι₀ (Module.finrank ℝ E) ε =>
        PhiFun (I := I) (M := M) g₀ D ε x₀ (c', y))
      ((Work.Diff.STE.D.pPhiFunD (E := E)
          (Work.Diff.STE.D.jetPairOf (I := I) (M := M) g₀ D ε x₀ c
            (Work.Diff.STE.flatToE (I := I) x₀ y))).comp
        (Work.Diff.STE.D.psi.jetDirLin (I := I) (M := M) g₀ D ε x₀
          (Work.Diff.STE.flatToE (I := I) x₀ y))) c :=
    HasFDerivAt.comp (g := Work.Diff.STE.D.pPhiFun (E := E)) c
      (hasFDerivAt_pPhiFun (E := E) _ hdom) houter
  -- The full derivative at `(c, y)`, restricted to the coefficient directions:
  have hΦsm : ContDiffAt ℝ (⊤ : ℕ∞) (PhiFun (I := I) (M := M) g₀ D ε x₀) (c, y) :=
    (contDiffOn_PhiFun (I := I) (M := M) (ε := ε) hg D x₀).contDiffAt
      ((isOpen_JetDom (I := I) (M := M) (ε := ε) hg D x₀).mem_nhds ⟨hy, hdom⟩)
  have hΦat : HasFDerivAt (PhiFun (I := I) (M := M) g₀ D ε x₀)
      (fderiv ℝ (PhiFun (I := I) (M := M) g₀ D ε x₀) (c, y)) (c, y) :=
    (hΦsm.differentiableAt (by simp)).hasFDerivAt
  have hinl : HasFDerivAt
      (fun c' : CS ι₀ (Module.finrank ℝ E) ε =>
        ((c', y) : CS ι₀ (Module.finrank ℝ E) ε × Fl (Module.finrank ℝ E)))
      (ContinuousLinearMap.inl ℝ (CS ι₀ (Module.finrank ℝ E) ε)
        (Fl (Module.finrank ℝ E))) c :=
    hasFDerivAt_pair_const c y
  have hcomp : HasFDerivAt
      (fun c' : CS ι₀ (Module.finrank ℝ E) ε =>
        PhiFun (I := I) (M := M) g₀ D ε x₀ (c', y))
      ((fderiv ℝ (PhiFun (I := I) (M := M) g₀ D ε x₀) (c, y)).comp
        (ContinuousLinearMap.inl ℝ (CS ι₀ (Module.finrank ℝ E) ε)
          (Fl (Module.finrank ℝ E)))) c :=
    HasFDerivAt.comp (g := PhiFun (I := I) (M := M) g₀ D ε x₀) c hΦat hinl
  have hkey : ((Work.Diff.STE.D.pPhiFunD (E := E)
        (Work.Diff.STE.D.jetPairOf (I := I) (M := M) g₀ D ε x₀ c
          (Work.Diff.STE.flatToE (I := I) x₀ y))).comp
      (Work.Diff.STE.D.psi.jetDirLin (I := I) (M := M) g₀ D ε x₀
        (Work.Diff.STE.flatToE (I := I) x₀ y)))
      = ((fderiv ℝ (PhiFun (I := I) (M := M) g₀ D ε x₀) (c, y)).comp
        (ContinuousLinearMap.inl ℝ (CS ι₀ (Module.finrank ℝ E) ε)
          (Fl (Module.finrank ℝ E)))) :=
    hp.unique hcomp
  calc (fderiv ℝ (PhiFun (I := I) (M := M) g₀ D ε x₀) (c, y))
        ((Pi.single z' (1 : ℝ) : CS ι₀ (Module.finrank ℝ E) ε), (0 : Fl (Module.finrank ℝ E)))
      = ((fderiv ℝ (PhiFun (I := I) (M := M) g₀ D ε x₀) (c, y)).comp
          (ContinuousLinearMap.inl ℝ (CS ι₀ (Module.finrank ℝ E) ε)
            (Fl (Module.finrank ℝ E)))) (Pi.single z' (1 : ℝ)) := by
        rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.inl_apply]
    _ = ((Work.Diff.STE.D.pPhiFunD (E := E)
          (Work.Diff.STE.D.jetPairOf (I := I) (M := M) g₀ D ε x₀ c
            (Work.Diff.STE.flatToE (I := I) x₀ y))).comp
        (Work.Diff.STE.D.psi.jetDirLin (I := I) (M := M) g₀ D ε x₀
          (Work.Diff.STE.flatToE (I := I) x₀ y))) (Pi.single z' (1 : ℝ)) := by
        rw [← hkey]
    _ = Work.Diff.STE.D.pPhiFunD (E := E)
          (Work.Diff.STE.D.jetPairOf (I := I) (M := M) g₀ D ε x₀ c
            (Work.Diff.STE.flatToE (I := I) x₀ y))
          (Work.Diff.STE.D.jetDir (I := I) (M := M) g₀ D ε x₀ z'
            (Work.Diff.STE.flatToE (I := I) x₀ y)) := by
        rw [ContinuousLinearMap.comp_apply, Work.Diff.STE.D.psi.jetDirLin_apply,
          Work.Diff.STE.D.psi.sum_single_smul]

/-- **The representation of `Ufun` through the derivative of the joint expression.** -/
lemma Ufun_eq_fderiv (hg : Work.Diff.STE.D.ChartData (I := I) (M := M) g₀.inner)
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (z z' : Work.Diff.STE.B3.JIdx ι₀ (Module.finrank ℝ E) ε)
    (c : CS ι₀ (Module.finrank ℝ E) ε) {y : Fl (Module.finrank ℝ E)}
    (hy : Work.Diff.STE.flatToE (I := I) (D.x₀ z.1) y ∈ (extChartAt I (D.x₀ z.1)).target)
    (hpos : Work.Diff.STE.D.IsPos (I := I) (M := M) g₀ D ε c) :
    Work.Diff.STE.D.Ufun (I := I) (M := M) g₀ D ε z z' c y =
      Work.Diff.STE.B3Data.psi (I := I) (M := M) D z.1 y *
        Real.sqrt (Work.Diff.STE.B3Data.dens (I := I) (M := M) D z.1 y) *
        ∑ j : Fin (Module.finrank ℝ E), ∑ k : Fin (Module.finrank ℝ E),
          Work.Diff.STE.D.coordCLM (I := I) (M := M) (D.x₀ z.1) (D.pt z.1 y) j
              (D.e z.1 z.2.1 (D.pt z.1 y))
            * Work.Diff.STE.D.coordCLM (I := I) (M := M) (D.x₀ z.1) (D.pt z.1 y) k
              (D.e z.1 z.2.2.1 (D.pt z.1 y))
            * ((fderiv ℝ (PhiFun (I := I) (M := M) g₀ D ε (D.x₀ z.1)) (c, y))
                ((Pi.single z' (1 : ℝ) : CS ι₀ (Module.finrank ℝ E) ε), (0 : Fl (Module.finrank ℝ E)))) j k := by
  rw [Ufun_unfold,
    fderiv_PhiFun_apply_single (I := I) (M := M) hg D (D.x₀ z.1) z' c hy
      (jetPairOf_mem_pPhiDom (I := I) (M := M) hg D (D.x₀ z.1) c hpos hy)]

theorem abs_Ufun_sub_le
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ((⊤ : ENat) : WithTop ENat) M] [T2Space M] [I.Boundaryless]
    {ι₀ : Type*} [Fintype ι₀] {g₀ : Submission.Diff.SMet I M}
    (hg : Work.Diff.STE.D.ChartData (I := I) (M := M) g₀.inner)
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (ε : ℝ)
    (z z' : Work.Diff.STE.B3.JIdx ι₀ (Module.finrank ℝ E) ε) :
    ∃ (δ C : ℝ), 0 < δ ∧ 0 ≤ C ∧
      ∀ (c₀ c₁ : Work.Diff.STE.B3.JIdx ι₀ (Module.finrank ℝ E) ε → ℝ),
        ‖c₀‖ < δ → ‖c₁‖ < δ →
        Work.Diff.STE.D.IsPos (I := I) (M := M) g₀ D ε c₀ →
        Work.Diff.STE.D.IsPos (I := I) (M := M) g₀ D ε c₁ →
        ∀ y : Fin (Module.finrank ℝ E) → ℝ,
          |Work.Diff.STE.D.Ufun (I := I) (M := M) g₀ D ε z z' c₀ y
            - Work.Diff.STE.D.Ufun (I := I) (M := M) g₀ D ε z z' c₁ y|
          ≤ C * ‖c₀ - c₁‖ := by
  classical
  obtain ⟨δp, hδp, hIsPos⟩ := exists_isPos_ball_psi (I := I) (M := M) D ε
  obtain ⟨Bpref, hBpref0, hBpref⟩ := Work.Diff.STE.D.psi.abs_pref_le (I := I) (M := M) D z.1
  obtain ⟨Ba, hBa0, hBa⟩ := Work.Diff.STE.D.psi.abs_coord_factor_le (I := I) (M := M) D z.1 z.2.1
  obtain ⟨Bb, hBb0, hBb⟩ := Work.Diff.STE.D.psi.abs_coord_factor_le (I := I) (M := M) D z.1 z.2.2.1
  have hn0 : (0 : ℝ) ≤ (Module.finrank ℝ E : ℝ) := Nat.cast_nonneg _
  -- smoothness of the joint expression and of its first derivative
  have hPhi := contDiffOn_PhiFun (I := I) (M := M) (ε := ε) hg D (D.x₀ z.1)
  have hDom_open := isOpen_JetDom (I := I) (M := M) (ε := ε) hg D (D.x₀ z.1)
  have hderiv1 : ContDiffOn ℝ 1
      (fderiv ℝ (PhiFun (I := I) (M := M) g₀ D ε (D.x₀ z.1)))
      (JetDom (I := I) (M := M) g₀ D ε (D.x₀ z.1)) :=
    hPhi.fderiv_of_isOpen hDom_open (by simp)
  have hderiv2 : ContDiffOn ℝ 0
      (fderiv ℝ (fderiv ℝ (PhiFun (I := I) (M := M) g₀ D ε (D.x₀ z.1))))
      (JetDom (I := I) (M := M) g₀ D ε (D.x₀ z.1)) :=
    hderiv1.fderiv_of_isOpen hDom_open (m := 0) (by simp)
  -- the compact set on which the second derivative is bounded
  have h0Ky : (0 : Fl (Module.finrank ℝ E))
      ∈ Work.Diff.STE.D.psi.Ky (I := I) (M := M) D z.1 := by
    refine ⟨?_, subset_closure ?_⟩
    · rw [Metric.mem_closedBall, dist_self]
      exact le_of_lt (D.hσ z.1)
    · rw [Function.mem_support, D.hχ1 z.1 (0 : Fl (Module.finrank ℝ E))
        (by simpa using le_of_lt (D.hσ z.1))]
      exact one_ne_zero
  have hKX : IsCompact (Metric.closedBall (0 : CS ι₀ (Module.finrank ℝ E) ε) (δp / 2) ×ˢ
      Work.Diff.STE.D.psi.Ky (I := I) (M := M) D z.1) := by
    have h1 : IsCompact (Metric.closedBall (0 : CS ι₀ (Module.finrank ℝ E) ε) (δp / 2)) :=
      isCompact_closedBall _ _
    exact h1.prod (Work.Diff.STE.D.psi.isCompact_Ky (I := I) (M := M) D z.1)
  have hKXs : ∀ q ∈ Metric.closedBall (0 : CS ι₀ (Module.finrank ℝ E) ε) (δp / 2) ×ˢ
      Work.Diff.STE.D.psi.Ky (I := I) (M := M) D z.1,
      q ∈ JetDom (I := I) (M := M) g₀ D ε (D.x₀ z.1) := by
    rintro q hq
    obtain ⟨hq1, hq2⟩ := hq
    have hq1' : ‖q.1‖ ≤ δp / 2 := by
      rwa [Metric.mem_closedBall, dist_zero_right] at hq1
    have hq2' : Work.Diff.STE.flatToE (I := I) (D.x₀ z.1) q.2
        ∈ (extChartAt I (D.x₀ z.1)).target :=
      Work.Diff.STE.D.psi.flatToE_mem_target_of_mem_Ky (I := I) (M := M) D hq2
    exact ⟨hq2', jetPairOf_mem_pPhiDom (I := I) (M := M) hg D (D.x₀ z.1) q.1
      (hIsPos q.1 (by linarith)) hq2'⟩
  obtain ⟨B₂, hB₂⟩ := hKX.exists_bound_of_continuousOn
    (f := fderiv ℝ (fderiv ℝ (PhiFun (I := I) (M := M) g₀ D ε (D.x₀ z.1))))
    (hderiv2.continuousOn.mono hKXs)
  have hB₂0 : 0 ≤ B₂ := le_trans (norm_nonneg _)
    (hB₂ (0, 0) ⟨by rw [Metric.mem_closedBall, dist_zero_right, norm_zero]; linarith, h0Ky⟩)
  have hC0 : 0 ≤ Bpref * ((Module.finrank ℝ E : ℝ) * (Module.finrank ℝ E : ℝ) * Ba * Bb) * B₂ :=
    mul_nonneg (mul_nonneg hBpref0
      (mul_nonneg (mul_nonneg (mul_nonneg hn0 hn0) hBa0) hBb0)) hB₂0
  refine ⟨δp / 2,
    Bpref * ((Module.finrank ℝ E : ℝ) * (Module.finrank ℝ E : ℝ) * Ba * Bb) * B₂,
    by linarith, hC0, ?_⟩
  intro c₀ c₁ hc₀ hc₁ hp₀ hp₁ y
  by_cases hy : y ∈ Work.Diff.STE.D.psi.Ky (I := I) (M := M) D z.1
  · -- the case where the localised weight can be nonzero
    have hy' : Work.Diff.STE.flatToE (I := I) (D.x₀ z.1) y
        ∈ (extChartAt I (D.x₀ z.1)).target :=
      Work.Diff.STE.D.psi.flatToE_mem_target_of_mem_Ky (I := I) (M := M) D hy
    have hc₀le : ‖c₀‖ ≤ δp / 2 := le_of_lt hc₀
    have hc₁le : ‖c₁‖ ≤ δp / 2 := le_of_lt hc₁
    have hmem₀ : (c₀, y) ∈ JetDom (I := I) (M := M) g₀ D ε (D.x₀ z.1) :=
      hKXs _ ⟨by rw [Metric.mem_closedBall, dist_zero_right]; exact hc₀le, hy⟩
    have hmem₁ : (c₁, y) ∈ JetDom (I := I) (M := M) g₀ D ε (D.x₀ z.1) :=
      hKXs _ ⟨by rw [Metric.mem_closedBall, dist_zero_right]; exact hc₁le, hy⟩
    -- the two-point mean value estimate for the derivative
    have hMVT : ‖fderiv ℝ (PhiFun (I := I) (M := M) g₀ D ε (D.x₀ z.1)) (c₀, y)
        - fderiv ℝ (PhiFun (I := I) (M := M) g₀ D ε (D.x₀ z.1)) (c₁, y)‖
        ≤ B₂ * ‖c₀ - c₁‖ := by
      have hsegKX : segment ℝ (c₁, y) (c₀, y)
          ⊆ Metric.closedBall (0 : CS ι₀ (Module.finrank ℝ E) ε) (δp / 2) ×ˢ
              Work.Diff.STE.D.psi.Ky (I := I) (M := M) D z.1 := by
        intro q hq
        obtain ⟨a, b, ha, hb, hab, hz⟩ := hq
        rw [← hz]
        refine ⟨?_, ?_⟩
        · rw [Metric.mem_closedBall, dist_zero_right]
          have hfst : (a • (c₁, y) + b • (c₀, y)).1 = a • c₁ + b • c₀ := by
            simp only [Prod.smul_mk, Prod.mk_add_mk]
          rw [hfst]
          calc ‖a • c₁ + b • c₀‖ ≤ ‖a • c₁‖ + ‖b • c₀‖ := norm_add_le _ _
            _ = a * ‖c₁‖ + b * ‖c₀‖ := by
                rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
                  abs_of_nonneg ha, abs_of_nonneg hb]
            _ ≤ a * (δp / 2) + b * (δp / 2) :=
                add_le_add (mul_le_mul_of_nonneg_left hc₁le ha)
                  (mul_le_mul_of_nonneg_left hc₀le hb)
            _ = δp / 2 := by rw [← add_mul, hab, one_mul]
        · have hsnd : (a • (c₁, y) + b • (c₀, y)).2 = y := by
            simp only [Prod.smul_mk, Prod.mk_add_mk]
            rw [← add_smul, hab, one_smul]
          rw [hsnd]
          exact hy
      have hseg : segment ℝ (c₁, y) (c₀, y)
          ⊆ JetDom (I := I) (M := M) g₀ D ε (D.x₀ z.1) :=
        fun q hq => hKXs q (hsegKX hq)
      have hbound : ∀ v ∈ segment ℝ (c₁, y) (c₀, y),
          ‖fderiv ℝ (fderiv ℝ (PhiFun (I := I) (M := M) g₀ D ε (D.x₀ z.1))) v‖ ≤ B₂ :=
        fun v hv => hB₂ v (hsegKX hv)
      have hdiff : ∀ v ∈ segment ℝ (c₁, y) (c₀, y),
          HasFDerivWithinAt (fderiv ℝ (PhiFun (I := I) (M := M) g₀ D ε (D.x₀ z.1)))
            (fderiv ℝ (fderiv ℝ (PhiFun (I := I) (M := M) g₀ D ε (D.x₀ z.1))) v)
            (segment ℝ (c₁, y) (c₀, y)) v := by
        intro v hv
        have hvD : v ∈ JetDom (I := I) (M := M) g₀ D ε (D.x₀ z.1) := hseg hv
        exact (((hderiv1.differentiableOn (by simp)).differentiableAt
          (hDom_open.mem_nhds hvD)).hasFDerivAt).hasFDerivWithinAt
      have hmain := Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le hdiff hbound
        (convex_segment (c₁, y) (c₀, y))
        (left_mem_segment ℝ (c₁, y) (c₀, y)) (right_mem_segment ℝ (c₁, y) (c₀, y))
      have hsub : (c₀, y) - (c₁, y) = (c₀ - c₁, (0 : Fl (Module.finrank ℝ E))) :=
        Prod.ext rfl (by simp)
      rw [hsub, Prod.norm_mk, norm_zero, max_eq_left (norm_nonneg _)] at hmain
      exact hmain
    -- the bound on the coefficients of the jet matrix
    have hentry : ∀ X : Work.Diff.EXT.MatE (E := E),
        |∑ j : Fin (Module.finrank ℝ E), ∑ k : Fin (Module.finrank ℝ E),
          Work.Diff.STE.D.coordCLM (I := I) (M := M) (D.x₀ z.1) (D.pt z.1 y) j
              (D.e z.1 z.2.1 (D.pt z.1 y))
            * Work.Diff.STE.D.coordCLM (I := I) (M := M) (D.x₀ z.1) (D.pt z.1 y) k
              (D.e z.1 z.2.2.1 (D.pt z.1 y))
            * X j k|
        ≤ ((Module.finrank ℝ E : ℝ) * (Module.finrank ℝ E : ℝ) * Ba * Bb) * ‖X‖ := by
      intro X
      calc |∑ j : Fin (Module.finrank ℝ E), ∑ k : Fin (Module.finrank ℝ E),
            Work.Diff.STE.D.coordCLM (I := I) (M := M) (D.x₀ z.1) (D.pt z.1 y) j
                (D.e z.1 z.2.1 (D.pt z.1 y))
              * Work.Diff.STE.D.coordCLM (I := I) (M := M) (D.x₀ z.1) (D.pt z.1 y) k
                (D.e z.1 z.2.2.1 (D.pt z.1 y))
              * X j k|
          ≤ ∑ j : Fin (Module.finrank ℝ E), |∑ k : Fin (Module.finrank ℝ E),
              Work.Diff.STE.D.coordCLM (I := I) (M := M) (D.x₀ z.1) (D.pt z.1 y) j
                  (D.e z.1 z.2.1 (D.pt z.1 y))
                * Work.Diff.STE.D.coordCLM (I := I) (M := M) (D.x₀ z.1) (D.pt z.1 y) k
                  (D.e z.1 z.2.2.1 (D.pt z.1 y))
                * X j k| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ j : Fin (Module.finrank ℝ E), ∑ k : Fin (Module.finrank ℝ E),
              |Work.Diff.STE.D.coordCLM (I := I) (M := M) (D.x₀ z.1) (D.pt z.1 y) j
                  (D.e z.1 z.2.1 (D.pt z.1 y))
                * Work.Diff.STE.D.coordCLM (I := I) (M := M) (D.x₀ z.1) (D.pt z.1 y) k
                  (D.e z.1 z.2.2.1 (D.pt z.1 y))
                * X j k| :=
            Finset.sum_le_sum fun j _ => Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ _j : Fin (Module.finrank ℝ E), ∑ _k : Fin (Module.finrank ℝ E),
              Ba * Bb * ‖X‖ := by
            refine Finset.sum_le_sum fun j _ => Finset.sum_le_sum fun k _ => ?_
            rw [abs_mul, abs_mul]
            exact mul_le_mul (mul_le_mul (hBa y hy j) (hBb y hy k) (abs_nonneg _) hBa0)
              (le_trans (norm_le_pi_norm (X j) k) (norm_le_pi_norm X j)) (abs_nonneg _)
              (mul_nonneg hBa0 hBb0)
        _ = ((Module.finrank ℝ E : ℝ) * (Module.finrank ℝ E : ℝ) * Ba * Bb) * ‖X‖ := by
            simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
            ring
    -- the bound on the derivative of the joint expression
    have hX : ‖((fderiv ℝ (PhiFun (I := I) (M := M) g₀ D ε (D.x₀ z.1)) (c₀, y))
        - (fderiv ℝ (PhiFun (I := I) (M := M) g₀ D ε (D.x₀ z.1)) (c₁, y)))
        ((Pi.single z' (1 : ℝ) : CS ι₀ (Module.finrank ℝ E) ε), (0 : Fl (Module.finrank ℝ E)))‖ ≤ B₂ * ‖c₀ - c₁‖ := by
      have he' : ‖(Pi.single z' (1 : ℝ) : CS ι₀ (Module.finrank ℝ E) ε)‖ ≤ 1 := by
        rw [pi_norm_le_iff_of_nonneg zero_le_one]
        intro j
        by_cases hj : j = z'
        · rw [hj, Pi.single_eq_same]
          norm_num
        · rw [Pi.single_eq_of_ne hj]
          simp
      have hε0 : (0 : ℝ) ≤ B₂ * ‖c₀ - c₁‖ := mul_nonneg hB₂0 (norm_nonneg _)
      calc ‖((fderiv ℝ (PhiFun (I := I) (M := M) g₀ D ε (D.x₀ z.1)) (c₀, y))
            - (fderiv ℝ (PhiFun (I := I) (M := M) g₀ D ε (D.x₀ z.1)) (c₁, y)))
            ((Pi.single z' (1 : ℝ) : CS ι₀ (Module.finrank ℝ E) ε), (0 : Fl (Module.finrank ℝ E)))‖
          ≤ ‖(fderiv ℝ (PhiFun (I := I) (M := M) g₀ D ε (D.x₀ z.1)) (c₀, y))
              - (fderiv ℝ (PhiFun (I := I) (M := M) g₀ D ε (D.x₀ z.1)) (c₁, y))‖
            * ‖((Pi.single z' (1 : ℝ) : CS ι₀ (Module.finrank ℝ E) ε), (0 : Fl (Module.finrank ℝ E)))‖ :=
              (fderiv ℝ (PhiFun (I := I) (M := M) g₀ D ε (D.x₀ z.1)) (c₀, y)
                - fderiv ℝ (PhiFun (I := I) (M := M) g₀ D ε (D.x₀ z.1)) (c₁, y)).le_opNorm
                  ((Pi.single z' (1 : ℝ) : CS ι₀ (Module.finrank ℝ E) ε),
                    (0 : Fl (Module.finrank ℝ E)))
        _ ≤ (B₂ * ‖c₀ - c₁‖) * 1 := by
            refine mul_le_mul hMVT ?_
              (norm_nonneg ((Pi.single z' (1 : ℝ) : CS ι₀ (Module.finrank ℝ E) ε),
                (0 : Fl (Module.finrank ℝ E)))) hε0
            have hnorm : ‖((Pi.single z' (1 : ℝ) : CS ι₀ (Module.finrank ℝ E) ε),
                  (0 : Fl (Module.finrank ℝ E)))‖
                = ‖(Pi.single z' (1 : ℝ) : CS ι₀ (Module.finrank ℝ E) ε)‖ := by
              rw [Prod.norm_mk, norm_zero, max_eq_left (norm_nonneg _)]
            rw [hnorm]
            exact he'
        _ = B₂ * ‖c₀ - c₁‖ := by ring
    -- the representation of `Ufun` through the derivative
    have hU₀ := Ufun_eq_fderiv (I := I) (M := M) hg D z z' c₀ (y := y) hy' hp₀
    have hU₁ := Ufun_eq_fderiv (I := I) (M := M) hg D z z' c₁ (y := y) hy' hp₁
    -- the difference of the two coefficient sums
    have hKey :
        (∑ j : Fin (Module.finrank ℝ E), ∑ k : Fin (Module.finrank ℝ E),
            Work.Diff.STE.D.coordCLM (I := I) (M := M) (D.x₀ z.1) (D.pt z.1 y) j
                (D.e z.1 z.2.1 (D.pt z.1 y))
              * Work.Diff.STE.D.coordCLM (I := I) (M := M) (D.x₀ z.1) (D.pt z.1 y) k
                (D.e z.1 z.2.2.1 (D.pt z.1 y))
              * ((fderiv ℝ (PhiFun (I := I) (M := M) g₀ D ε (D.x₀ z.1)) (c₀, y))
                  ((Pi.single z' (1 : ℝ) : CS ι₀ (Module.finrank ℝ E) ε), (0 : Fl (Module.finrank ℝ E)))) j k)
          - (∑ j : Fin (Module.finrank ℝ E), ∑ k : Fin (Module.finrank ℝ E),
            Work.Diff.STE.D.coordCLM (I := I) (M := M) (D.x₀ z.1) (D.pt z.1 y) j
                (D.e z.1 z.2.1 (D.pt z.1 y))
              * Work.Diff.STE.D.coordCLM (I := I) (M := M) (D.x₀ z.1) (D.pt z.1 y) k
                (D.e z.1 z.2.2.1 (D.pt z.1 y))
              * ((fderiv ℝ (PhiFun (I := I) (M := M) g₀ D ε (D.x₀ z.1)) (c₁, y))
                  ((Pi.single z' (1 : ℝ) : CS ι₀ (Module.finrank ℝ E) ε), (0 : Fl (Module.finrank ℝ E)))) j k)
          = ∑ j : Fin (Module.finrank ℝ E), ∑ k : Fin (Module.finrank ℝ E),
            Work.Diff.STE.D.coordCLM (I := I) (M := M) (D.x₀ z.1) (D.pt z.1 y) j
                (D.e z.1 z.2.1 (D.pt z.1 y))
              * Work.Diff.STE.D.coordCLM (I := I) (M := M) (D.x₀ z.1) (D.pt z.1 y) k
                (D.e z.1 z.2.2.1 (D.pt z.1 y))
              * (((fderiv ℝ (PhiFun (I := I) (M := M) g₀ D ε (D.x₀ z.1)) (c₀, y))
                  - (fderiv ℝ (PhiFun (I := I) (M := M) g₀ D ε (D.x₀ z.1)) (c₁, y)))
                  ((Pi.single z' (1 : ℝ) : CS ι₀ (Module.finrank ℝ E) ε), (0 : Fl (Module.finrank ℝ E)))) j k := by
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun k _ => ?_
      simp only [sub_apply, Pi.sub_apply]
      ring_nf
    have hfin : |Work.Diff.STE.D.Ufun (I := I) (M := M) g₀ D ε z z' c₀ y
        - Work.Diff.STE.D.Ufun (I := I) (M := M) g₀ D ε z z' c₁ y|
        ≤ Bpref * (((Module.finrank ℝ E : ℝ) * (Module.finrank ℝ E : ℝ) * Ba * Bb)
            * (B₂ * ‖c₀ - c₁‖)) := by
      rw [hU₀, hU₁, ← mul_sub, abs_mul]
      refine mul_le_mul (hBpref y) ?_ (abs_nonneg _) hBpref0
      rw [hKey]
      calc |∑ j : Fin (Module.finrank ℝ E), ∑ k : Fin (Module.finrank ℝ E),
            Work.Diff.STE.D.coordCLM (I := I) (M := M) (D.x₀ z.1) (D.pt z.1 y) j
                (D.e z.1 z.2.1 (D.pt z.1 y))
              * Work.Diff.STE.D.coordCLM (I := I) (M := M) (D.x₀ z.1) (D.pt z.1 y) k
                (D.e z.1 z.2.2.1 (D.pt z.1 y))
              * (((fderiv ℝ (PhiFun (I := I) (M := M) g₀ D ε (D.x₀ z.1)) (c₀, y))
                  - (fderiv ℝ (PhiFun (I := I) (M := M) g₀ D ε (D.x₀ z.1)) (c₁, y)))
                  ((Pi.single z' (1 : ℝ) : CS ι₀ (Module.finrank ℝ E) ε), (0 : Fl (Module.finrank ℝ E)))) j k|
          ≤ ((Module.finrank ℝ E : ℝ) * (Module.finrank ℝ E : ℝ) * Ba * Bb)
              * ‖((fderiv ℝ (PhiFun (I := I) (M := M) g₀ D ε (D.x₀ z.1)) (c₀, y))
                  - (fderiv ℝ (PhiFun (I := I) (M := M) g₀ D ε (D.x₀ z.1)) (c₁, y)))
                  ((Pi.single z' (1 : ℝ) : CS ι₀ (Module.finrank ℝ E) ε), (0 : Fl (Module.finrank ℝ E)))‖ := hentry _
        _ ≤ ((Module.finrank ℝ E : ℝ) * (Module.finrank ℝ E : ℝ) * Ba * Bb)
              * (B₂ * ‖c₀ - c₁‖) :=
            mul_le_mul_of_nonneg_left hX (mul_nonneg (mul_nonneg (mul_nonneg hn0 hn0) hBa0) hBb0)
    calc |Work.Diff.STE.D.Ufun (I := I) (M := M) g₀ D ε z z' c₀ y
          - Work.Diff.STE.D.Ufun (I := I) (M := M) g₀ D ε z z' c₁ y|
        ≤ Bpref * (((Module.finrank ℝ E : ℝ) * (Module.finrank ℝ E : ℝ) * Ba * Bb)
            * (B₂ * ‖c₀ - c₁‖)) := hfin
      _ = (Bpref * ((Module.finrank ℝ E : ℝ) * (Module.finrank ℝ E : ℝ) * Ba * Bb) * B₂)
            * ‖c₀ - c₁‖ := by ring
  · -- the case where the localised weight vanishes
    have hψ : Work.Diff.STE.B3Data.psi (I := I) (M := M) D z.1 y = 0 := by
      by_contra hne
      exact hy (Work.Diff.STE.D.psi.mem_Ky_of_psi_ne_zero (I := I) (M := M) D hne)
    have h0 : ∀ c : CS ι₀ (Module.finrank ℝ E) ε,
        Work.Diff.STE.D.Ufun (I := I) (M := M) g₀ D ε z z' c y = 0 := by
      intro c
      rw [Ufun_unfold, hψ, zero_mul, zero_mul]
    rw [h0 c₀, h0 c₁, sub_zero, abs_zero]
    exact mul_nonneg hC0 (norm_nonneg _)

end

end Work.Diff.STE.D.psi
