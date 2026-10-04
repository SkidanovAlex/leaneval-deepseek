/-
# The chart nonlinearity agrees with the jet-level DeTurck operator

The flat Cauchy problem is stated for the nonlinearity `chartNonlin bg` of
`Submission.Work.Diff.STE.Man.Defs`: the scalar principal part `secOpFlat` plus the lower-order
part `pN` evaluated at the background jets of the periodised chart matrix `bg` (and at the value
and the first jet of the unknown).  The *geometric* DeTurck operator, read in the chart at `x₀`,
is `Work.Diff.STE.DeTurck.pPhiJet`, which only sees the spatial `2`-jets `chartJet` of the chart
matrices of the metric and of the background metric.

This file proves `Work.Diff.STE.Man.chartNonlin_eq_pPhiJet`: when the unknown is the spatial
`2`-jet `jetM (u t) z` of a torus function `u t` which is (locally) the *real* chart matrix of a
metric `G` (`hG : chartMatFun G x₀ (chartCoordSymm I x₀ z') = reMatE (u t z')` near `z`), and when
the background `bg` is the periodised chart matrix of `g₀` (which agrees with
`flatChartMat g₀ x₀` on the ball of radius `r/2`), then

`chartNonlin bg (z, jetM (u t) z) = ofRealMat (pPhiJet G g₀ x₀ (chartCoordSymm I x₀ z))`.

The proof has three ingredients.

* *The background jets*: `bg` agrees near `z` with `chartMatFun g₀ x₀ ∘ chartCoordSymm`, so
  `dpd_of_eventuallyEq_comp` identifies its value and its first and second `dpd`-derivatives at
  `z` with the value and the first and second Fréchet derivatives of `chartMatFun g₀ x₀` at the
  chart point `chartCoordSymm I x₀ z` — which is precisely the content of the components of
  `chartJet`.
* *The foreground jets*: `hG` says that `reMatE ∘ u t` agrees near `z` with
  `chartMatFun G x₀ ∘ chartCoordSymm`, and hence (again by `dpd_of_eventuallyEq_comp`) the chart
  jets of `G` are the `reMatE`-images of the value and of the first and second coordinate
  derivatives of `u t` at `z`.  The passage through `reMatE` is a composition with the continuous
  linear map `reMatECLM : MatC n →L[ℝ] MatE` (push forward of the Fréchet derivative); see
  `dpd_reMatE` and `dpd_dpd_reMatE`.
* *The algebraic identity at fixed jets* is `chartNonlin_eq_pPhi`
  (`Submission/Work/Diff/STE/Man/Basic.lean`), which needs the jet-level symmetries and reality of
  the jets of `u t` implied by `husy` and `hure`: symmetry in the matrix indices (`pdM_symm`,
  `pdM_pdM_symm`), Clairaut (`pdM_pdM_comm`) and reality of the second derivatives
  (`im_pdM_pdM_eq_zero`).
-/
import Mathlib
import Submission.Work.Diff.STE.Man.BridgeInputs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

open Work.Diff.STE.Flat Work.Diff.STE.Man Work.Diff.STE.DeTurck Work.Diff.EXT Work.Diff.STE Filter
open scoped Manifold ContDiff Bundle Topology BigOperators
open Bundle ContDiff Set VectorField CovariantDerivative Metric

namespace Work.Diff.STE.Man

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 2000000

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]

/-! ## The continuous linear maps extracting entries and real parts -/

/-- The `(i,j)`-entry of a complex matrix, as a continuous linear map. -/
noncomputable def matEntryCLM (i j : Fin (dim E)) : MatC (dim E) →L[ℝ] ℂ :=
  (ContinuousLinearMap.proj (φ := fun _ : Fin (dim E) => ℂ) j).comp
    (ContinuousLinearMap.proj (φ := fun _ : Fin (dim E) => Fin (dim E) → ℂ) i)

@[simp] lemma matEntryCLM_apply (i j : Fin (dim E)) (A : MatC (dim E)) :
    matEntryCLM (E := E) i j A = A i j := by simp [matEntryCLM]

/-- The real matrix underlying a complex matrix, as a continuous linear map. -/
noncomputable def reMatECLM : MatC (dim E) →L[ℝ] MatE (E := E) :=
  ContinuousLinearMap.pi (fun i => ContinuousLinearMap.pi (fun j =>
    Complex.reCLM.comp (matEntryCLM (E := E) i j)))

@[simp] lemma reMatECLM_apply (A : MatC (dim E)) : reMatECLM (E := E) A = reMatE A := by
  funext i j
  simp [reMatECLM, reMatE]

/-! ## Small generalities -/

/-- An eventual statement is eventually eventual: a neighbourhood of `z` consists of points `z'`
which *have* a neighbourhood of their own contained in it. -/
lemma eventually_nhds_nhds {α : Type*} [TopologicalSpace α] {p : α → Prop} {z : α}
    (h : ∀ᶠ z' in nhds z, p z') : ∀ᶠ z' in nhds z, ∀ᶠ y in nhds z', p y := by
  obtain ⟨U, hU, hUsub⟩ := Filter.eventually_iff_exists_mem.mp h
  refine Filter.mem_of_superset (interior_mem_nhds.mpr hU) ?_
  intro z' hz'
  exact Filter.mem_of_superset (isOpen_interior.mem_nhds hz')
    (fun y hy => hUsub y (interior_subset hy))

/-- Two continuous linear maps agreeing on the canonical basis `bB` are equal. -/
lemma clm_ext_bB {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {f g : E →L[ℝ] F}
    (h : ∀ c : Fin (dim E), f (bB (E := E) c) = g (bB (E := E) c)) : f = g :=
  ContinuousLinearMap.coe_injective ((Module.finBasis ℝ E).ext h)

/-- Two continuous bilinear maps agreeing on pairs of canonical basis vectors are equal. -/
lemma bilin_ext_bB {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f g : E →L[ℝ] E →L[ℝ] F}
    (h : ∀ c d : Fin (dim E),
      f (bB (E := E) c) (bB (E := E) d) = g (bB (E := E) c) (bB (E := E) d)) : f = g := by
  refine clm_ext_bB (fun c => ?_)
  exact clm_ext_bB (fun d => h c d)

/-! ## Pushing `reMatE` through the Fréchet derivative -/

/-- The derivative of the real part of a matrix-valued function: it is the composition of
`reMatECLM` with the derivative. -/
lemma fderiv_reMatE (u : Torus (dim E)) (z : Fin (dim E) → ℝ) (hu : DifferentiableAt ℝ u z) :
    fderiv ℝ (fun z' => reMatE (u z')) z = (reMatECLM (E := E)).comp (fderiv ℝ u z) := by
  rw [show (fun z' => reMatE (u z')) = (reMatECLM (E := E)) ∘ u from by funext z'; simp]
  rw [fderiv_comp (x := z) (g := reMatECLM (E := E)) (f := u)
    (ContinuousLinearMap.differentiableAt _) hu]
  simp

/-- The entry `(i,j)` of the derivative of a matrix-valued function is the derivative of the entry
function. -/
lemma pdM_eq_fderiv (u : Torus (dim E)) (z : Fin (dim E) → ℝ)
    (hu : DifferentiableAt ℝ u z) (c : Fin (dim E)) :
    pdM c u z = fderiv ℝ u z (Pi.single c 1) := by
  funext i j
  show fderiv ℝ (fun y => u y i j) z (Pi.single c 1) = (fderiv ℝ u z (Pi.single c 1)) i j
  rw [show (fun y : Fin (dim E) → ℝ => u y i j) = (matEntryCLM (E := E) i j) ∘ u from by
    funext y; simp]
  rw [fderiv_comp (x := z) (g := matEntryCLM (E := E) i j) (f := u)
    (ContinuousLinearMap.differentiableAt _) hu]
  simp

/-- The derivative of `z' ↦ reMatE (D u (z') (e_d))`: the second derivative of `u`, composed with
`reMatECLM`. -/
lemma fderiv_reMatE_clm_apply (u : Torus (dim E)) (z : Fin (dim E) → ℝ)
    (hdf : DifferentiableAt ℝ (fderiv ℝ u) z) (d : Fin (dim E)) :
    fderiv ℝ (fun z' => reMatE (fderiv ℝ u z' (Pi.single d 1))) z
      = (reMatECLM (E := E)).comp ((fderiv ℝ (fderiv ℝ u) z).flip (Pi.single d 1)) := by
  rw [show (fun z' => reMatE (fderiv ℝ u z' (Pi.single d 1)))
      = (reMatECLM (E := E)) ∘ (fun z' => fderiv ℝ u z' (Pi.single d 1)) from by
    funext z'; simp]
  rw [fderiv_comp (x := z) (g := reMatECLM (E := E))
    (f := fun z' => fderiv ℝ u z' (Pi.single d 1)) (ContinuousLinearMap.differentiableAt _)
    (hdf.clm_apply (differentiableAt_const _))]
  simp only [ContinuousLinearMap.fderiv]
  congr 1
  rw [fderiv_clm_apply (c := fderiv ℝ u) (u := fun _ : Fin (dim E) → ℝ => Pi.single d 1)
    hdf (differentiableAt_const _)]
  simp

/-- The second coordinate derivative of `u` is the second Fréchet derivative of `u`. -/
lemma pdM_pdM_eq_fderiv (u : Torus (dim E)) (z : Fin (dim E) → ℝ)
    (hu : ContDiffAt ℝ (⊤ : ℕ∞) u z) (c d : Fin (dim E)) :
    pdM c (pdM d u) z = (fderiv ℝ (fderiv ℝ u) z (Pi.single c 1)) (Pi.single d 1) := by
  have hdf : DifferentiableAt ℝ (fderiv ℝ u) z :=
    (hu.fderiv_right (m := (⊤ : ℕ∞)) (by simp)).differentiableAt (by simp)
  funext i j
  have hev : (fun y => pdM d u y i j) =ᶠ[nhds z]
      (fun y => (fderiv ℝ u y (Pi.single d 1)) i j) := by
    filter_upwards [eventually_differentiableAt_of_contDiffAt hu] with y hy
    rw [pdM_eq_fderiv u y hy d]
  show (fderiv ℝ (fun y => pdM d u y i j) z) (Pi.single c 1) = _
  rw [hev.fderiv_eq]
  rw [show (fun y => (fderiv ℝ u y (Pi.single d 1)) i j)
      = (matEntryCLM (E := E) i j) ∘ (fun y => fderiv ℝ u y (Pi.single d 1)) from by
    funext y; simp]
  rw [fderiv_comp (x := z) (g := matEntryCLM (E := E) i j)
    (f := fun y => fderiv ℝ u y (Pi.single d 1)) (ContinuousLinearMap.differentiableAt _)
    (hdf.clm_apply (differentiableAt_const _))]
  simp only [ContinuousLinearMap.comp_apply]
  rw [fderiv_clm_apply (c := fderiv ℝ u) (u := fun _ : Fin (dim E) → ℝ => Pi.single d 1)
    hdf (differentiableAt_const _)]
  simp

/-- The first `dpd`-derivative of the real part of a matrix-valued function is the real part of its
first coordinate derivative. -/
lemma dpd_reMatE (u : Torus (dim E)) (z : Fin (dim E) → ℝ) (hu : DifferentiableAt ℝ u z)
    (c : Fin (dim E)) :
    dpd (E := E) c (fun z' => reMatE (u z')) z = reMatE (pdM c u z) := by
  show fderiv ℝ (fun z' => reMatE (u z')) z (Pi.single c 1) = _
  rw [fderiv_reMatE u z hu]
  simp only [ContinuousLinearMap.comp_apply, reMatECLM_apply]
  congr 1
  exact (pdM_eq_fderiv u z hu c).symm

/-- The second `dpd`-derivative of the real part of a matrix-valued function is the real part of its
second coordinate derivative. -/
lemma dpd_dpd_reMatE (u : Torus (dim E)) (z : Fin (dim E) → ℝ)
    (hu : ContDiffAt ℝ (⊤ : ℕ∞) u z) (c d : Fin (dim E)) :
    dpd (E := E) c (dpd (E := E) d (fun z' => reMatE (u z'))) z
      = reMatE (pdM c (pdM d u) z) := by
  have hdf : DifferentiableAt ℝ (fderiv ℝ u) z :=
    (hu.fderiv_right (m := (⊤ : ℕ∞)) (by simp)).differentiableAt (by simp)
  have hev : (fun z' => dpd (E := E) d (fun z'' => reMatE (u z'')) z')
      =ᶠ[nhds z] (fun z' => reMatE (fderiv ℝ u z' (Pi.single d 1))) := by
    filter_upwards [eventually_differentiableAt_of_contDiffAt hu] with z' hz'
    rw [dpd_reMatE u z' hz' d]
    congr 1
    exact pdM_eq_fderiv u z' hz' d
  show (fderiv ℝ (fun z' => dpd (E := E) d (fun z'' => reMatE (u z'')) z') z) (Pi.single c 1) = _
  rw [hev.fderiv_eq]
  rw [fderiv_reMatE_clm_apply u z hdf d]
  simp only [ContinuousLinearMap.comp_apply, reMatECLM_apply, ContinuousLinearMap.flip_apply]
  congr 1
  exact (pdM_pdM_eq_fderiv u z hu c d).symm

/-! ## Symmetry and reality of the jets of a locally symmetric real torus function -/

/-- The first jet of a locally symmetric matrix-valued function is symmetric in the matrix
indices. -/
lemma pdM_symm {u : Torus (dim E)} {z : Fin (dim E) → ℝ}
    (h : ∀ᶠ z' in nhds z, ∀ i j, u z' i j = u z' j i) (c i j : Fin (dim E)) :
    pdM c u z i j = pdM c u z j i := by
  have hev : (fun y => u y i j) =ᶠ[nhds z] (fun y => u y j i) := h.mono (fun z' hz' => hz' i j)
  show (fderiv ℝ (fun y => u y i j) z) (Pi.single c 1)
      = (fderiv ℝ (fun y => u y j i) z) (Pi.single c 1)
  rw [hev.fderiv_eq]

/-- The second jet of a locally symmetric matrix-valued function is symmetric in the matrix
indices. -/
lemma pdM_pdM_symm {u : Torus (dim E)} {z : Fin (dim E) → ℝ}
    (h : ∀ᶠ z' in nhds z, ∀ i j, u z' i j = u z' j i) (c d i j : Fin (dim E)) :
    pdM c (pdM d u) z i j = pdM c (pdM d u) z j i := by
  have h' := eventually_nhds_nhds h
  have hev : (fun y => pdM d u y i j) =ᶠ[nhds z] (fun y => pdM d u y j i) := by
    filter_upwards [h'] with y hy
    exact pdM_symm hy d i j
  show (fderiv ℝ (fun y => pdM d u y i j) z) (Pi.single c 1)
      = (fderiv ℝ (fun y => pdM d u y j i) z) (Pi.single c 1)
  rw [hev.fderiv_eq]

/-- The first coordinate derivative of a locally real matrix-valued function is real in each
entry. -/
lemma im_pdM_eq_zero_at {u : Torus (dim E)} {z : Fin (dim E) → ℝ}
    (hd : DifferentiableAt ℝ u z)
    (h : ∀ᶠ z' in nhds z, ∀ i j, (u z' i j).im = 0) (c i j : Fin (dim E)) :
    (pdM c u z i j).im = 0 :=
  im_pd_eq_zero (f := fun y => u y i j)
    ((ContinuousLinearMap.differentiableAt (matEntryCLM (E := E) i j)).comp z hd)
    (h.mono (fun z' hz' => hz' i j)) c

/-- The second coordinate derivative of a locally real matrix-valued function is real in each
entry. -/
lemma im_pdM_pdM_eq_zero {u : Torus (dim E)} {z : Fin (dim E) → ℝ}
    (hu : ContDiffAt ℝ (⊤ : ℕ∞) u z)
    (h : ∀ᶠ z' in nhds z, ∀ i j, (u z' i j).im = 0) (c d i j : Fin (dim E)) :
    (pdM c (pdM d u) z i j).im = 0 := by
  have hnear : ∀ᶠ y in nhds z, (pdM d u y i j).im = 0 := by
    filter_upwards [eventually_differentiableAt_of_contDiffAt hu, eventually_nhds_nhds h]
      with y hdy hsub
    exact im_pdM_eq_zero_at hdy hsub d i j
  have hfd : ContDiffAt ℝ (⊤ : ℕ∞) (fun y => u y i j) z :=
    contDiffAt_pi.mp (contDiffAt_pi.mp hu i) j
  have hdf : DifferentiableAt ℝ (fderiv ℝ (fun y => u y i j)) z :=
    (hfd.fderiv_right (m := (⊤ : ℕ∞)) (by simp)).differentiableAt (by simp)
  refine im_pd_eq_zero (f := fun y => (fderiv ℝ (fun y' => u y' i j) y) (Pi.single d 1))
    (hdf.clm_apply (differentiableAt_const _)) ?_ c
  exact hnear

/-! ## The target -/

theorem chartNonlin_eq_pPhiJet
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]
    (g₀ G : Submission.Diff.SMet I M) (x₀ : M) (r : ℝ) (hr : 0 < r) (hr1 : r ≤ 1 / 2)
    (u : ℝ → Work.Diff.STE.Flat.Torus (Work.Diff.STE.Man.dim E)) (t : ℝ)
    (z : Fin (Work.Diff.STE.Man.dim E) → ℝ)
    (hz : z ∈ Metric.ball (0 : Fin (Work.Diff.STE.Man.dim E) → ℝ) (r / 2))
    (hG : ∀ z' ∈ Metric.ball (0 : Fin (Work.Diff.STE.Man.dim E) → ℝ) (r / 2),
      Work.Diff.EXT.chartMatFun G x₀ (Work.Diff.STE.Man.chartCoordSymm I x₀ z')
        = Work.Diff.STE.Man.reMatE (u t z'))
    (hg₀ : ContDiffAt ℝ (⊤ : ℕ∞) (Work.Diff.EXT.chartMatFun g₀ x₀)
      (Work.Diff.STE.Man.chartCoordSymm I x₀ z))
    (hGsm : ContDiffAt ℝ (⊤ : ℕ∞) (Work.Diff.EXT.chartMatFun G x₀)
      (Work.Diff.STE.Man.chartCoordSymm I x₀ z))
    (hcont : ContDiffOn ℝ (⊤ : ℕ∞) (Work.Diff.STE.Man.flatChartMat g₀ x₀)
      (Metric.ball (0 : Fin (Work.Diff.STE.Man.dim E) → ℝ) (2 * r)))
    (hu : ContDiffAt ℝ (⊤ : ℕ∞) (u t) z)
    (hure : ∀ᶠ z' in nhds z, ∀ i j, (u t z' i j).im = 0)
    (husy : ∀ᶠ z' in nhds z, ∀ i j, u t z' i j = u t z' j i)
    (hdet : (Matrix.of (Work.Diff.STE.Man.reMatE (u t z))).det ≠ 0) :
    Work.Diff.STE.Man.chartNonlin (E := E) (Work.Diff.STE.Man.chartDatumR (I := I) g₀ x₀ r hr)
        (z, Work.Diff.STE.Flat.jetM (u t) z)
      = Work.Diff.STE.Man.ofRealMat
          (Work.Diff.STE.DeTurck.pPhiJet G g₀ x₀ (Work.Diff.STE.Man.chartCoordSymm I x₀ z)) := by
  -- the periodised chart datum agrees with the chart matrix of `g₀` near `z`
  have hcd : ∀ z' ∈ Metric.ball (0 : Fin (dim E) → ℝ) (r / 2),
      chartDatum (I := I) g₀ x₀ r hr z' = ofRealMat (flatChartMat g₀ x₀ z') :=
    (chartDatum_periodic_smooth g₀ x₀ r hr hr1 hcont).2.2.1
  have hbg_ev : (chartDatumR (I := I) g₀ x₀ r hr)
      =ᶠ[nhds z] fun z' => chartMatFun g₀ x₀ (chartCoordSymm I x₀ z') := by
    filter_upwards [Metric.isOpen_ball.mem_nhds hz] with z' hz'
    funext i j
    rw [show chartDatumR (I := I) g₀ x₀ r hr z' i j
        = reMatE (chartDatum (I := I) g₀ x₀ r hr z') i j from rfl, hcd z' hz']
    simp [reMatE, ofRealMat]
  -- the local metric `G` has the chart matrix `reMatE ∘ u t` near `z`
  have hW_ev : (fun z' => reMatE (u t z'))
      =ᶠ[nhds z] fun z' => chartMatFun G x₀ (chartCoordSymm I x₀ z') := by
    filter_upwards [Metric.isOpen_ball.mem_nhds hz] with z' hz'
    exact (hG z' hz').symm
  obtain ⟨hb1, hb2, hb3⟩ := dpd_of_eventuallyEq_comp (I := I) x₀ (chartMatFun g₀ x₀) z
    (chartDatumR (I := I) g₀ x₀ r hr) hg₀ hbg_ev
  obtain ⟨hG1, hG2, hG3⟩ := dpd_of_eventuallyEq_comp (I := I) x₀ (chartMatFun G x₀) z
    (fun z' => reMatE (u t z')) hGsm hW_ev
  -- the jet symmetries and the reality of the second jet of `u t`
  have hA : ∀ i j, u t z i j = u t z j i := fun i j => husy.self_of_nhds i j
  have hL : ∀ c i j, pdM c (u t) z i j = pdM c (u t) z j i :=
    fun c i j => pdM_symm husy c i j
  have hB1 : ∀ c d, pdM c (pdM d (u t)) z = pdM d (pdM c (u t)) z :=
    fun c d => pdM_pdM_comm hu c d
  have hB2 : ∀ c d i j, pdM c (pdM d (u t)) z i j = pdM c (pdM d (u t)) z j i :=
    fun c d i j => pdM_pdM_symm husy c d i j
  have hBim : ∀ c d i j, (pdM c (pdM d (u t)) z i j).im = 0 :=
    fun c d i j => im_pdM_pdM_eq_zero hu hure c d i j
  -- the algebraic step at fixed jets
  have hmain := chartNonlin_eq_pPhi (E := E) (chartDatumR (I := I) g₀ x₀ r hr) z (u t z)
    (fun c => pdM c (u t) z) (fun c d => pdM c (pdM d (u t)) z) hA hL hB1 hB2 hBim hdet
  have hjet : jetM (u t) z
      = ((u t z), (fun c => pdM c (u t) z), (fun c d => pdM c (pdM d (u t)) z)) := rfl
  rw [hjet, hmain]
  -- identify the background and the foreground jets with the chart jets
  have e1 : chartDatumR (I := I) g₀ x₀ r hr z = (chartJet g₀ x₀ (chartCoordSymm I x₀ z)).1 := hb1
  have e2 : linMatOf (E := E) (fun c => dpd (E := E) c (chartDatumR (I := I) g₀ x₀ r hr) z)
      = (chartJet g₀ x₀ (chartCoordSymm I x₀ z)).2.1 := by
    refine clm_ext_bB (fun c => ?_)
    rw [linMatOf_bB]
    rw [hb2 c]
    rfl
  have e3 : bilMatOf (E := E)
        (fun c d => dpd (E := E) c (dpd (E := E) d (chartDatumR (I := I) g₀ x₀ r hr)) z)
      = (chartJet g₀ x₀ (chartCoordSymm I x₀ z)).2.2 := by
    refine bilin_ext_bB (fun c d => ?_)
    rw [bilMatOf_bB]
    rw [hb3 c d]
    rfl
  have e4 : reMatE (u t z) = (chartJet G x₀ (chartCoordSymm I x₀ z)).1 := hG1
  have e5 : linMatOf (E := E) (fun c => reMatE (pdM c (u t) z))
      = (chartJet G x₀ (chartCoordSymm I x₀ z)).2.1 := by
    refine clm_ext_bB (fun c => ?_)
    rw [linMatOf_bB]
    rw [show (chartJet G x₀ (chartCoordSymm I x₀ z)).2.1 (bB (E := E) c)
        = fderiv ℝ (chartMatFun G x₀) (chartCoordSymm I x₀ z) (bB (E := E) c) from rfl,
      ← hG2 c]
    exact (dpd_reMatE (u t) z (hu.differentiableAt (by simp)) c).symm
  have e6 : bilMatOf (E := E) (fun c d => reMatE (pdM c (pdM d (u t)) z))
      = (chartJet G x₀ (chartCoordSymm I x₀ z)).2.2 := by
    refine bilin_ext_bB (fun c d => ?_)
    rw [bilMatOf_bB]
    rw [show (chartJet G x₀ (chartCoordSymm I x₀ z)).2.2 (bB (E := E) c) (bB (E := E) d)
        = (fderiv ℝ (fderiv ℝ (chartMatFun G x₀)) (chartCoordSymm I x₀ z))
            (bB (E := E) c) (bB (E := E) d) from rfl,
      ← hG3 c d]
    exact (dpd_dpd_reMatE (u t) z hu c d).symm
  apply congrArg ofRealMat
  rw [e1, e2, e3, e4, e5, e6]
  rfl

end

end Work.Diff.STE.Man
