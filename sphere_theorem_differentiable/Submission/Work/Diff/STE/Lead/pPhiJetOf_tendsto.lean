import Mathlib
import Submission.Work.Diff.STE.Lead.coordBound
import Submission.Work.Diff.STE.deTurck.contDiffOn_pPhi
import Submission.Work.Diff.STE.Lead.clm_norm_le_basis
import Submission.Work.Diff.STE.deTurck.posDef_gmat
import Submission.Work.Diff.STE.D.psi.chartMatOf_pd_det_pos

set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology BigOperators
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter

namespace Work.Diff.STE.Lead

set_option linter.unusedSectionVars false
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- `ContinuousAdd` for a seminormed additive group, with the *canonical* additive structure
(the type-class search does not find it for iterated continuous-linear-map types). -/
private lemma continuousAdd_of_seminormed (X : Type*) [SeminormedAddCommGroup X] :
    ContinuousAdd X := inferInstance

/-- Adding a constant to a sequence tending to `0` in a seminormed additive group. -/
private lemma tendsto_const_add_zero {X : Type*} [SeminormedAddCommGroup X] (a : X)
    {u : ℕ → X} (hu : Filter.Tendsto u Filter.atTop (nhds 0)) :
    Filter.Tendsto (fun n => a + u n) Filter.atTop (nhds a) := by
  haveI : ContinuousAdd X := continuousAdd_of_seminormed X
  simpa using (tendsto_const_nhds.add hu :
    Filter.Tendsto (fun n => a + u n) Filter.atTop (nhds (a + 0)))

private lemma jet2_slice_sub {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {u v : E → F} {s : Set E} (hs : IsOpen s) {y : E} (hy : y ∈ s)
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) u s) (hv : ContDiffOn ℝ (⊤ : ℕ∞) v s) :
    Work.Diff.EXT.jet2 (E := E) (fun p : ℝ × E => u p.2 - v p.2) (0, y) =
      Work.Diff.EXT.jet2 (E := E) (fun p : ℝ × E => u p.2) (0, y)
        - Work.Diff.EXT.jet2 (E := E) (fun p : ℝ × E => v p.2) (0, y) := by
  have htop : (↑(⊤ : ℕ∞) : WithTop ℕ∞) ≠ 0 := by simp
  have hya : ∀ᶠ y' in 𝓝 y, DifferentiableAt ℝ u y' := by
    filter_upwards [hs.mem_nhds hy] with y' hy'
    exact (hu.differentiableOn htop).differentiableAt (hs.mem_nhds hy')
  have hyb : ∀ᶠ y' in 𝓝 y, DifferentiableAt ℝ v y' := by
    filter_upwards [hs.mem_nhds hy] with y' hy'
    exact (hv.differentiableOn htop).differentiableAt (hs.mem_nhds hy')
  have hdu : DifferentiableAt ℝ u y := (hu.differentiableOn htop).differentiableAt (hs.mem_nhds hy)
  have hdv : DifferentiableAt ℝ v y := (hv.differentiableOn htop).differentiableAt (hs.mem_nhds hy)
  have hdu' : DifferentiableAt ℝ (fderiv ℝ u) y :=
    ((ContDiffOn.fderiv_of_isOpen hu hs (m := (⊤ : ℕ∞)) (by simp)).differentiableOn htop).differentiableAt
      (hs.mem_nhds hy)
  have hdv' : DifferentiableAt ℝ (fderiv ℝ v) y :=
    ((ContDiffOn.fderiv_of_isOpen hv hs (m := (⊤ : ℕ∞)) (by simp)).differentiableOn htop).differentiableAt
      (hs.mem_nhds hy)
  have hderiv : (fun y' => fderiv ℝ (fun y'' => u y'' - v y'') y')
      =ᶠ[𝓝 y] (fderiv ℝ u - fderiv ℝ v) := by
    filter_upwards [hya, hyb] with y' h1 h2
    exact fderiv_sub h1 h2
  simp only [Work.Diff.EXT.jet2, Prod.mk_sub_mk]
  refine Prod.ext rfl (Prod.ext ?_ ?_)
  · exact fderiv_sub hdu hdv
  · rw [Filter.EventuallyEq.fderiv_eq hderiv, fderiv_sub hdu' hdv']

variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ((⊤ : ENat) : WithTop ENat) M] [T2Space M] [I.Boundaryless]

private lemma chartJetOf_sub_of_chartData (h k : Work.Diff.STE.Bil (I := I) (M := M)) (x₀ : M)
    {y : E} (hy : y ∈ (extChartAt I x₀).target)
    (hh : Work.Diff.STE.D.ChartData (I := I) (M := M) h)
    (hk : Work.Diff.STE.D.ChartData (I := I) (M := M) k) :
    Work.Diff.STE.D.chartJetOf (I := I) (M := M) (h - k) x₀ y =
      Work.Diff.STE.D.chartJetOf (I := I) (M := M) h x₀ y
        - Work.Diff.STE.D.chartJetOf (I := I) (M := M) k x₀ y := by
  have hs : IsOpen (extChartAt I x₀).target := isOpen_extChartAt_target x₀
  rw [Work.Diff.STE.D.chartJetOf_eq, Work.Diff.STE.D.chartJetOf_eq, Work.Diff.STE.D.chartJetOf_eq]
  rw [show Work.Diff.STE.D.chartMatOf (I := I) (M := M) (h - k) x₀
      = fun y' => Work.Diff.STE.D.chartMatOf (I := I) (M := M) h x₀ y'
          - Work.Diff.STE.D.chartMatOf (I := I) (M := M) k x₀ y' from by
    funext y' i j
    simp only [Work.Diff.STE.D.chartMatOf_apply, Pi.sub_apply, sub_apply]]
  exact jet2_slice_sub (F := Work.Diff.EXT.MatE (E := E)) hs hy (hh x₀) (hk x₀)

/-- the (a,b)-entry of the fderiv of a matrix-valued function is the fderiv of the entry -/
private lemma fderiv_entry_eq' {F : E → Work.Diff.EXT.MatE (E := E)} {y : E}
    (hF : DifferentiableAt ℝ F y) (v : E) (a b : Fin (Module.finrank ℝ E)) :
    ((fderiv ℝ F y) v) a b = (fderiv ℝ (fun y' => F y' a b) y) v := by
  let L : Work.Diff.EXT.MatE (E := E) →L[ℝ] ℝ :=
    (ContinuousLinearMap.proj (φ := fun _ : Fin (Module.finrank ℝ E) => ℝ) b).comp
      (ContinuousLinearMap.proj (φ := fun _ : Fin (Module.finrank ℝ E) =>
        Fin (Module.finrank ℝ E) → ℝ) a)
  have hL : ∀ M : Work.Diff.EXT.MatE (E := E), L M = M a b := fun M => rfl
  have h1 : fderiv ℝ (fun y' => L (F y')) y = L.comp (fderiv ℝ F y) := by
    have hcomp := fderiv_comp (x := y) (g := L) (f := F) L.differentiableAt hF
    rw [ContinuousLinearMap.fderiv] at hcomp
    simpa [Function.comp_def] using hcomp
  have h2 : (fun y' : E => L (F y')) = fun y' => F y' a b := funext fun y' => hL _
  calc ((fderiv ℝ F y) v) a b = L ((fderiv ℝ F y) v) := (hL _).symm
    _ = (L.comp (fderiv ℝ F y)) v := rfl
    _ = (fderiv ℝ (fun y' => L (F y')) y) v := by rw [h1]
    _ = (fderiv ℝ (fun y' => F y' a b) y) v := by rw [h2]

private lemma contDiffAt_entry' {F : E → Work.Diff.EXT.MatE (E := E)} {y : E}
    (hF : ContDiffAt ℝ (⊤ : ℕ∞) F y) (a b : Fin (Module.finrank ℝ E)) :
    ContDiffAt ℝ (⊤ : ℕ∞) (fun y'' => F y'' a b) y := by
  have hL : ContDiff ℝ (⊤ : ℕ∞) (fun M : Work.Diff.EXT.MatE (E := E) => M a b) := by fun_prop
  simpa [Function.comp_def] using hL.contDiffAt.comp y hF

private lemma contDiffAt_entry_gen {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {F : X → Work.Diff.EXT.MatE (E := E)} {z : X}
    (hF : ContDiffAt ℝ (⊤ : ℕ∞) F z) (a b : Fin (Module.finrank ℝ E)) :
    ContDiffAt ℝ (⊤ : ℕ∞) (fun z' => F z' a b) z := by
  have hL : ContDiff ℝ (⊤ : ℕ∞) (fun M : Work.Diff.EXT.MatE (E := E) => M a b) := by fun_prop
  simpa [Function.comp_def] using hL.contDiffAt.comp z hF

private lemma fderiv_fderiv_entry_eq' {F : E → Work.Diff.EXT.MatE (E := E)} {y : E}
    (hF : ∀ᶠ y' in 𝓝 y, ContDiffAt ℝ (⊤ : ℕ∞) F y') (v w : E)
    (a b : Fin (Module.finrank ℝ E)) :
    ((fderiv ℝ (fun y' => fderiv ℝ F y') y v) w) a b
      = (fderiv ℝ (fun y' => fderiv ℝ (fun y'' => F y'' a b) y') y v) w := by
  have hFy : ContDiffAt ℝ (⊤ : ℕ∞) F y := hF.self_of_nhds
  have hdF : DifferentiableAt ℝ (fderiv ℝ F) y :=
    (hFy.fderiv_right (m := (⊤ : ℕ∞)) (by simp)).differentiableAt (by simp)
  have hdG : DifferentiableAt ℝ (fun y' => (fderiv ℝ F y') w) y :=
    hdF.clm_apply (differentiableAt_const w)
  have h2 : (fderiv ℝ (fderiv ℝ F) y).flip w
      = fderiv ℝ (fun y' => (fderiv ℝ F y') w) y := by
    rw [fderiv_clm_apply (c := fderiv ℝ F) (u := fun _ : E => w) hdF
      (differentiableAt_const w)]
    simp
  have h1 : (fderiv ℝ (fun y' => fderiv ℝ F y') y v) w
      = (fderiv ℝ (fun y' => (fderiv ℝ F y') w) y) v := by
    have hflip : ((fderiv ℝ (fderiv ℝ F) y).flip w) v
        = ((fderiv ℝ (fun y' => fderiv ℝ F y') y) v) w :=
      ContinuousLinearMap.flip_apply _ _ _
    rw [← hflip, h2]
  have h3 : (fun y' : E => ((fderiv ℝ F y') w) a b)
      =ᶠ[𝓝 y] fun y' => (fderiv ℝ (fun y'' => F y'' a b) y') w := by
    filter_upwards [hF] with y' hy'
    exact fderiv_entry_eq' (y := y') (hy'.differentiableAt (by simp)) w a b
  have h4 : (fderiv ℝ (fun y' => (fderiv ℝ F y') w) y) v a b
      = (fderiv ℝ (fun y' => ((fderiv ℝ F y') w) a b) y) v :=
    fderiv_entry_eq' (F := fun y' => (fderiv ℝ F y') w) (y := y) hdG v a b
  have hdG' : DifferentiableAt ℝ (fun y' : E => fderiv ℝ (fun y'' => F y'' a b) y') y :=
    ((contDiffAt_entry' hFy a b).fderiv_right (m := (⊤ : ℕ∞)) (by simp)).differentiableAt (by simp)
  calc ((fderiv ℝ (fun y' => fderiv ℝ F y') y v) w) a b
      = ((fderiv ℝ (fun y' => (fderiv ℝ F y') w) y) v) a b := by rw [h1]
    _ = (fderiv ℝ (fun y' => ((fderiv ℝ F y') w) a b) y) v := h4
    _ = (fderiv ℝ (fun y' => (fderiv ℝ (fun y'' => F y'' a b) y') w) y) v := by
        rw [h3.fderiv_eq]
    _ = (fderiv ℝ (fun y' => fderiv ℝ (fun y'' => F y'' a b) y') y v) w := by
        have hc := fderiv_clm_apply (c := fun y' => fderiv ℝ (fun y'' => F y'' a b) y')
          (u := fun _ : E => w) hdG' (differentiableAt_const w)
        rw [hc]
        simp [ContinuousLinearMap.flip_apply]

/-- **The jet of the chart matrix is bounded by an entrywise bound.** -/
private lemma norm_chartJetOf_le_of_entry_bounds
    (h : Work.Diff.STE.Bil (I := I) (M := M))
    (hsm : Work.Diff.STE.D.ChartData (I := I) (M := M) h)
    (x₀ : M) {y : E} (hy : y ∈ (extChartAt I x₀).target)
    {R : ℝ} (hR : 0 ≤ R)
    (hval : ∀ a b,
      |Work.Diff.STE.D.chartMatOf (I := I) (M := M) h x₀ y a b| ≤ R)
    (hder : ∀ a b (p : Fin (Module.finrank ℝ E)),
      |(fderiv ℝ (fun y' => Work.Diff.STE.D.chartMatOf (I := I) (M := M) h x₀ y' a b) y)
        (Work.Diff.EXT.bB (E := E) p)| ≤ R)
    (hder2 : ∀ a b (p q : Fin (Module.finrank ℝ E)),
      |(fderiv ℝ (fun y' => fderiv ℝ (fun y'' =>
          Work.Diff.STE.D.chartMatOf (I := I) (M := M) h x₀ y'' a b) y') y)
        (Work.Diff.EXT.bB (E := E) p) (Work.Diff.EXT.bB (E := E) q)| ≤ R)
    (K₁ K₂ : ℝ) (hK₁ : 0 ≤ K₁) (_hK₂ : 0 ≤ K₂)
    (hKb₁ : ∀ (T : E →L[ℝ] Work.Diff.EXT.MatE (E := E)) (R' : ℝ), 0 ≤ R' →
      (∀ p : Fin (Module.finrank ℝ E), ‖T (Work.Diff.EXT.bB (E := E) p)‖ ≤ R') →
      ‖T‖ ≤ K₁ * R')
    (hKb₂ : ∀ (T : E →L[ℝ] (E →L[ℝ] Work.Diff.EXT.MatE (E := E))) (R' : ℝ), 0 ≤ R' →
      (∀ p : Fin (Module.finrank ℝ E), ‖T (Work.Diff.EXT.bB (E := E) p)‖ ≤ R') →
      ‖T‖ ≤ K₂ * R') :
    ‖Work.Diff.STE.D.chartJetOf (I := I) (M := M) h x₀ y‖
      ≤ (max 1 (max K₁ (K₂ * K₁))) * R := by
  have hF : ∀ᶠ y' in 𝓝 y,
      ContDiffAt ℝ (⊤ : ℕ∞) (Work.Diff.STE.D.chartMatOf (I := I) (M := M) h x₀) y' :=
    Filter.eventually_iff_exists_mem.mpr
      ⟨(extChartAt I x₀).target, (isOpen_extChartAt_target (I := I) x₀).mem_nhds hy,
        fun y' hy' => (hsm x₀).contDiffAt ((isOpen_extChartAt_target (I := I) x₀).mem_nhds hy')⟩
  have hFy : DifferentiableAt ℝ (Work.Diff.STE.D.chartMatOf (I := I) (M := M) h x₀) y :=
    (hF.self_of_nhds).differentiableAt (by simp)
  have hA : ‖Work.Diff.STE.D.chartMatOf (I := I) (M := M) h x₀ y‖ ≤ R := by
    rw [pi_norm_le_iff_of_nonneg hR]
    intro a
    rw [pi_norm_le_iff_of_nonneg hR]
    intro b
    simpa only [Real.norm_eq_abs] using hval a b
  have hL : ‖fderiv ℝ (Work.Diff.STE.D.chartMatOf (I := I) (M := M) h x₀) y‖ ≤ K₁ * R := by
    refine hKb₁ _ R hR ?_
    intro p
    rw [pi_norm_le_iff_of_nonneg hR]
    intro a
    rw [pi_norm_le_iff_of_nonneg hR]
    intro b
    rw [fderiv_entry_eq' (F := Work.Diff.STE.D.chartMatOf (I := I) (M := M) h x₀) hFy
      (Work.Diff.EXT.bB (E := E) p) a b]
    simpa only [Real.norm_eq_abs] using hder a b p
  have hB : ‖fderiv ℝ (fun y' => fderiv ℝ
      (Work.Diff.STE.D.chartMatOf (I := I) (M := M) h x₀) y') y‖ ≤ K₂ * (K₁ * R) := by
    refine hKb₂ _ (K₁ * R) (mul_nonneg hK₁ hR) ?_
    intro p
    refine hKb₁ _ R hR ?_
    intro q
    rw [pi_norm_le_iff_of_nonneg hR]
    intro a
    rw [pi_norm_le_iff_of_nonneg hR]
    intro b
    rw [fderiv_fderiv_entry_eq' (F := Work.Diff.STE.D.chartMatOf (I := I) (M := M) h x₀) hF
      (Work.Diff.EXT.bB (E := E) p) (Work.Diff.EXT.bB (E := E) q) a b]
    simpa only [Real.norm_eq_abs] using hder2 a b p q
  have h1C : K₁ ≤ max 1 (max K₁ (K₂ * K₁)) := le_trans (le_max_left _ _) (le_max_right _ _)
  have h2C : K₂ * K₁ ≤ max 1 (max K₁ (K₂ * K₁)) :=
    le_trans (le_max_right _ _) (le_max_right _ _)
  have h0C : (1 : ℝ) ≤ max 1 (max K₁ (K₂ * K₁)) := le_max_left _ _ 
  have hA' : R ≤ (max 1 (max K₁ (K₂ * K₁))) * R := by
    simpa using mul_le_mul_of_nonneg_right h0C hR
  have hL' : K₁ * R ≤ (max 1 (max K₁ (K₂ * K₁))) * R :=
    mul_le_mul_of_nonneg_right h1C hR
  have hB' : K₂ * (K₁ * R) ≤ (max 1 (max K₁ (K₂ * K₁))) * R := by
    rw [show K₂ * (K₁ * R) = (K₂ * K₁) * R by ring]
    exact mul_le_mul_of_nonneg_right h2C hR
  rw [Work.Diff.STE.D.chartJetOf_eq]
  simp only [Work.Diff.EXT.jet2]
  rw [Prod.norm_def, Prod.norm_def]
  exact max_le (le_trans hA hA') (max_le (le_trans hL hL') (le_trans hB hB'))

/-! ## The core convergence of the chart jets -/

private lemma chartJetOf_tendsto_core
    {ι₀ : Type*} [Fintype ι₀] {g₀ : Submission.Diff.SMet I M}
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (k : ℕ)
    (hseq : ℕ → Work.Diff.STE.Bil (I := I) (M := M))
    (hlim : Work.Diff.STE.Bil (I := I) (M := M))
    (hsm_n : ∀ n, Work.Diff.STE.D.ChartData (I := I) (M := M) (hseq n))
    (hsm_l : Work.Diff.STE.D.ChartData (I := I) (M := M) hlim)
    (C : ℝ) (hC : 0 ≤ C)
    (hJetC : ∀ (h : Work.Diff.STE.Bil (I := I) (M := M)),
      Work.Diff.STE.D.ChartData (I := I) (M := M) h → ChartJetBound D k h C)
    (hconv : Filter.Tendsto (fun n : ℕ => D.BNorm k (hseq n - hlim)) Filter.atTop (nhds 0))
    (K₁ K₂ : ℝ) (hK₁ : 0 ≤ K₁) (hK₂ : 0 ≤ K₂)
    (hKb₁ : ∀ (T : E →L[ℝ] Work.Diff.EXT.MatE (E := E)) (R : ℝ), 0 ≤ R →
      (∀ p : Fin (Module.finrank ℝ E), ‖T (Work.Diff.EXT.bB (E := E) p)‖ ≤ R) →
      ‖T‖ ≤ K₁ * R)
    (hKb₂ : ∀ (T : E →L[ℝ] (E →L[ℝ] Work.Diff.EXT.MatE (E := E))) (R : ℝ), 0 ≤ R →
      (∀ p : Fin (Module.finrank ℝ E), ‖T (Work.Diff.EXT.bB (E := E) p)‖ ≤ R) →
      ‖T‖ ≤ K₂ * R)
    (i : ι₀) (x : M) (hx : x ∈ (extChartAt I (D.x₀ i)).source)
    (hz : ‖Work.Diff.STE.coord (I := I) (D.x₀ i) x‖ ≤ D.σ i)
    (hpsi_pos : 0 < D.psi i (Work.Diff.STE.coord (I := I) (D.x₀ i) x)) :
    Filter.Tendsto
      (fun n : ℕ => Work.Diff.STE.D.chartJetOf (I := I) (M := M) (hseq n) (D.x₀ i)
        ((extChartAt I (D.x₀ i)) x))
      Filter.atTop
      (nhds (Work.Diff.STE.D.chartJetOf (I := I) (M := M) hlim (D.x₀ i)
        ((extChartAt I (D.x₀ i)) x))) := by
  classical
  set y : E := (extChartAt I (D.x₀ i)) x with hy
  set z : Fin (Module.finrank ℝ E) → ℝ := Work.Diff.STE.coord (I := I) (D.x₀ i) x with hzdef
  have hz' : ‖z‖ ≤ D.σ i := hz
  have hpsi' : 0 < D.psi i z := hpsi_pos
  have hzy : Work.Diff.STE.flatToE (I := I) (D.x₀ i) z = y := by
    rw [hzdef, hy]
    exact Work.Diff.STE.Lead.flatToE_coord (I := I) (M := M) D hx
  have hyt : y ∈ (extChartAt I (D.x₀ i)).target := by
    rw [hy]
    exact PartialEquiv.map_source (extChartAt I (D.x₀ i)) hx
  have hsmDiff : ∀ n, Work.Diff.STE.D.ChartData (I := I) (M := M) (hseq n - hlim) := by
    intro n
    exact fun x₀' => (hsm_n n x₀').sub (hsm_l x₀')
  have hjetb : ∀ (n : ℕ) (a b : Fin (Module.finrank ℝ E)),
      (|Work.Diff.STE.D.chartMatOf (I := I) (M := M) (hseq n - hlim) (D.x₀ i) y a b|
          ≤ C * Real.sqrt (D.BNorm k (hseq n - hlim)) / (D.psi i z) ^ 3)
      ∧ (∀ p : Fin (Module.finrank ℝ E),
          |(fderiv ℝ (fun y' => Work.Diff.STE.D.chartMatOf (I := I) (M := M) (hseq n - hlim)
              (D.x₀ i) y' a b) y) (Work.Diff.EXT.bB (E := E) p)|
            ≤ C * Real.sqrt (D.BNorm k (hseq n - hlim)) / (D.psi i z) ^ 3)
      ∧ (∀ p q : Fin (Module.finrank ℝ E),
          |(fderiv ℝ (fun y' => fderiv ℝ (fun y'' =>
              Work.Diff.STE.D.chartMatOf (I := I) (M := M) (hseq n - hlim) (D.x₀ i) y'' a b) y')
              y) (Work.Diff.EXT.bB (E := E) p) (Work.Diff.EXT.bB (E := E) q)|
            ≤ C * Real.sqrt (D.BNorm k (hseq n - hlim)) / (D.psi i z) ^ 3) := by
    intro n a b
    have h := hJetC (hseq n - hlim) (hsmDiff n) i a b z (D.psi i z) hz' hpsi' le_rfl
    rw [hzy] at h
    exact h
  have hnorm : ∀ n : ℕ,
      ‖Work.Diff.STE.D.chartJetOf (I := I) (M := M) (hseq n - hlim) (D.x₀ i) y‖
        ≤ (max 1 (max K₁ (K₂ * K₁)))
            * (C * Real.sqrt (D.BNorm k (hseq n - hlim)) / (D.psi i z) ^ 3) := by
    intro n
    exact norm_chartJetOf_le_of_entry_bounds (hseq n - hlim) (hsmDiff n) (D.x₀ i) hyt
      (div_nonneg (mul_nonneg hC (Real.sqrt_nonneg _)) (by positivity))
      (fun a b => (hjetb n a b).1) (fun a b p => (hjetb n a b).2.1 p)
      (fun a b p q => (hjetb n a b).2.2 p q) K₁ K₂ hK₁ hK₂ hKb₁ hKb₂
  have hsq : Filter.Tendsto (fun n : ℕ => Real.sqrt (D.BNorm k (hseq n - hlim)))
      Filter.atTop (nhds 0) := by
    have h := hconv.sqrt
    rwa [Real.sqrt_zero] at h
  have h0 : Filter.Tendsto (fun n : ℕ => (max 1 (max K₁ (K₂ * K₁)))
      * (C * Real.sqrt (D.BNorm k (hseq n - hlim)) / (D.psi i z) ^ 3))
      Filter.atTop (nhds 0) := by
    have h := hsq.const_mul ((max 1 (max K₁ (K₂ * K₁))) * C / (D.psi i z) ^ 3)
    rw [mul_zero] at h
    refine h.congr' (Eventually.of_forall (fun n => ?_))
    ring
  have hres : Filter.Tendsto (fun n : ℕ => Work.Diff.STE.D.chartJetOf (I := I) (M := M)
      (hseq n - hlim) (D.x₀ i) y) Filter.atTop (nhds 0) :=
    squeeze_zero_norm (f := fun n : ℕ => Work.Diff.STE.D.chartJetOf (I := I) (M := M)
      (hseq n - hlim) (D.x₀ i) y) hnorm h0
  have hdec : ∀ n : ℕ, Work.Diff.STE.D.chartJetOf (I := I) (M := M) (hseq n) (D.x₀ i) y =
      Work.Diff.STE.D.chartJetOf (I := I) (M := M) hlim (D.x₀ i) y
        + Work.Diff.STE.D.chartJetOf (I := I) (M := M) (hseq n - hlim) (D.x₀ i) y := by
    intro n
    have h := chartJetOf_sub_of_chartData (I := I) (M := M) (hseq n) hlim (D.x₀ i) hyt
      (hsm_n n) hsm_l
    rw [h]
    abel
  rw [show (fun n : ℕ => Work.Diff.STE.D.chartJetOf (I := I) (M := M) (hseq n) (D.x₀ i) y)
      = fun n : ℕ => Work.Diff.STE.D.chartJetOf (I := I) (M := M) hlim (D.x₀ i) y
        + Work.Diff.STE.D.chartJetOf (I := I) (M := M) (hseq n - hlim) (D.x₀ i) y
      from funext hdec]
  exact tendsto_const_add_zero (Work.Diff.STE.D.chartJetOf (I := I) (M := M) hlim (D.x₀ i) y) hres


/-- **A section dominating `lam • g₀` has a nonsingular chart matrix.** -/
private lemma det_aux
    {g₀ : Submission.Diff.SMet I M}
    (h : Work.Diff.STE.Bil (I := I) (M := M)) (x₀ : M) {x : M}
    (hx : x ∈ (extChartAt I x₀).source)
    (hsym : ∀ (u v : TangentSpace I x), h x u v = h x v u)
    {lam : ℝ} (hlam : 0 < lam)
    (hell : ∀ v : TangentSpace I x, lam * g₀.inner x v v ≤ h x v v) :
    (Matrix.of (Work.Diff.STE.D.chartMatOf (I := I) (M := M) h x₀
      ((extChartAt I x₀) x))).det ≠ 0 := by
  classical
  have hbase : x ∈ (trivializationAt E (TangentSpace I) x₀).baseSet := by
    rw [TangentBundle.trivializationAt_baseSet]
    rwa [extChartAt_source] at hx
  let L : E →ₗ[ℝ] TangentSpace I x :=
    ((trivializationAt E (TangentSpace I) x₀).symmL ℝ x).toLinearMap
  have hL : Function.Injective L := by
    intro a b hab
    have hab' : (trivializationAt E (TangentSpace I) x₀).symmL ℝ x a
        = (trivializationAt E (TangentSpace I) x₀).symmL ℝ x b := hab
    have h1 := congrArg ((trivializationAt E (TangentSpace I) x₀).continuousLinearMapAt ℝ x) hab'
    simpa only [Trivialization.continuousLinearMapAt_symmL _ (R := ℝ) hbase a,
      Trivialization.continuousLinearMapAt_symmL _ (R := ℝ) hbase b] using h1
  have hpos : ∀ v : TangentSpace I x, v ≠ 0 → 0 < (h x v) v := by
    intro v hv
    have h1 : 0 < lam * g₀.inner x v v := mul_pos hlam (g₀.pos x v hv)
    linarith [hell v]
  have hpd := Work.Diff.STE.deTurck.posDef_gram_of_injective L hL (h x)
    (fun v w => hsym v w) hpos
  have hLb : ∀ i : Fin (Module.finrank ℝ E),
      L ((Module.finBasis ℝ E) i) = Submission.Geodesic.frameVector (I := I) x₀ x
        (Work.Diff.EXT.bB (E := E) i) := fun i => rfl
  have hmat : Matrix.of (fun i j : Fin (Module.finrank ℝ E) =>
      (h x (L ((Module.finBasis ℝ E) i))) (L ((Module.finBasis ℝ E) j)))
      = Matrix.of (Work.Diff.STE.D.chartMatOf (I := I) (M := M) h x₀ ((extChartAt I x₀) x)) := by
    ext i j
    simp only [Matrix.of_apply, Work.Diff.STE.D.chartMatOf_apply, hLb]
    rw [(extChartAt I x₀).left_inv hx]
  rw [hmat] at hpd
  exact (Matrix.PosDef.det_pos hpd).ne'

theorem pPhiJetOf_tendsto
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ((⊤ : ENat) : WithTop ENat) M] [T2Space M] [I.Boundaryless]
    {ι₀ : Type*} [Fintype ι₀] {g₀ : Submission.Diff.SMet I M}
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (k : ℕ)
    (hseq : ℕ → Work.Diff.STE.Bil (I := I) (M := M))
    (hlim : Work.Diff.STE.Bil (I := I) (M := M))
    (hsm_n : ∀ n, Work.Diff.STE.D.ChartData (I := I) (M := M) (hseq n))
    (hsm_l : Work.Diff.STE.D.ChartData (I := I) (M := M) hlim)
    (lam : ℝ) (hlam : 0 < lam)
    (hsym_l : ∀ (x : M) (u v : TangentSpace I x), hlim x u v = hlim x v u)
    (hell_l : ∀ (x : M) (v : TangentSpace I x), lam * g₀.inner x v v ≤ hlim x v v)
    (hconv : Filter.Tendsto (fun n : ℕ => D.BNorm k (hseq n - hlim)) Filter.atTop (nhds 0))
    (hJet : ∃ C : ℝ, 0 ≤ C ∧ ∀ (h : Work.Diff.STE.Bil (I := I) (M := M)),
      Work.Diff.STE.D.ChartData (I := I) (M := M) h → Work.Diff.STE.Lead.ChartJetBound D k h C)
    (i : ι₀) (x : M) (hx : x ∈ (extChartAt I (D.x₀ i)).source)
    (hz : ‖Work.Diff.STE.coord (I := I) (D.x₀ i) x‖ ≤ D.σ i)
    (hpsi_pos : 0 < D.psi i (Work.Diff.STE.coord (I := I) (D.x₀ i) x))
    (j l : Fin (Module.finrank ℝ E)) :
    Filter.Tendsto (fun n : ℕ => Work.Diff.STE.D.pPhiJetOf (I := I) (M := M) g₀ (hseq n) (D.x₀ i)
        ((extChartAt I (D.x₀ i)) x) j l)
      Filter.atTop (nhds (Work.Diff.STE.D.pPhiJetOf (I := I) (M := M) g₀ hlim (D.x₀ i)
        ((extChartAt I (D.x₀ i)) x) j l)) := by
  obtain ⟨C, hC, hJetC⟩ := hJet
  have hdet₁ : (Matrix.of (Work.Diff.STE.D.chartJetOf (I := I) (M := M) g₀.inner (D.x₀ i)
      ((extChartAt I (D.x₀ i)) x)).1).det ≠ 0 := by
    have hyt : (extChartAt I (D.x₀ i)) x ∈ (extChartAt I (D.x₀ i)).target :=
      PartialEquiv.map_source (extChartAt I (D.x₀ i)) hx
    exact (Work.Diff.STE.D.psi.chartMatOf_det_pos_of_posDef (I := I) (M := M) g₀.inner (D.x₀ i)
      (fun p u v => g₀.symm p u v) (fun p v hv => g₀.pos p v hv) hyt).ne'
  have hdet₂ : (Matrix.of (Work.Diff.STE.D.chartJetOf (I := I) (M := M) hlim (D.x₀ i)
      ((extChartAt I (D.x₀ i)) x)).1).det ≠ 0 :=
    det_aux (I := I) (M := M) (g₀ := g₀) hlim (D.x₀ i) hx (fun u v => hsym_l x u v) hlam (fun v => hell_l x v)
  obtain ⟨K₁, hK₁, hKb₁⟩ := clm_norm_le_basis (E := E)
  obtain ⟨K₂, hK₂, hKb₂⟩ := clm_norm_le_basis (E := E)
  have hjet := chartJetOf_tendsto_core (I := I) (M := M) D k hseq hlim hsm_n hsm_l C hC hJetC
    hconv K₁ K₂ hK₁ hK₂ (fun T R hR hb => hKb₁ T R hR hb) (fun T R hR hb => hKb₂ T R hR hb)
    i x hx hz hpsi_pos
  -- the pairs converge
  have hpair : Filter.Tendsto
      (fun n : ℕ => (Work.Diff.STE.D.chartJetOf (I := I) (M := M) g₀.inner (D.x₀ i)
          ((extChartAt I (D.x₀ i)) x),
        Work.Diff.STE.D.chartJetOf (I := I) (M := M) (hseq n) (D.x₀ i)
          ((extChartAt I (D.x₀ i)) x)))
      Filter.atTop
      (nhds (Work.Diff.STE.D.chartJetOf (I := I) (M := M) g₀.inner (D.x₀ i)
          ((extChartAt I (D.x₀ i)) x),
        Work.Diff.STE.D.chartJetOf (I := I) (M := M) hlim (D.x₀ i)
          ((extChartAt I (D.x₀ i)) x))) := by
    rw [Prod.tendsto_iff]
    exact ⟨tendsto_const_nhds, hjet⟩
  -- the DeTurck domain is open
  have hcontdet : Continuous fun w : (Work.Diff.EXT.MatE (E := E) × Work.Diff.STE.DeTurck.LinMat E ×
      Work.Diff.STE.DeTurck.BilMat E) × (Work.Diff.EXT.MatE (E := E) ×
        Work.Diff.STE.DeTurck.LinMat E × Work.Diff.STE.DeTurck.BilMat E) =>
      (Matrix.of w.2.1).det := by
    refine Continuous.matrix_det ?_
    exact continuous_pi fun a => continuous_pi fun b =>
      (continuous_apply b).comp ((continuous_apply a).comp
        (continuous_fst.comp continuous_snd))
  have hcontdetb : Continuous fun w : (Work.Diff.EXT.MatE (E := E) × Work.Diff.STE.DeTurck.LinMat E ×
      Work.Diff.STE.DeTurck.BilMat E) × (Work.Diff.EXT.MatE (E := E) ×
        Work.Diff.STE.DeTurck.LinMat E × Work.Diff.STE.DeTurck.BilMat E) =>
      (Matrix.of w.1.1).det := by
    refine Continuous.matrix_det ?_
    exact continuous_pi fun a => continuous_pi fun b =>
      (continuous_apply b).comp ((continuous_apply a).comp
        (continuous_fst.comp continuous_fst))
  have hopen : IsOpen {w : (Work.Diff.EXT.MatE (E := E) × Work.Diff.STE.DeTurck.LinMat E ×
        Work.Diff.STE.DeTurck.BilMat E) × (Work.Diff.EXT.MatE (E := E) ×
          Work.Diff.STE.DeTurck.LinMat E × Work.Diff.STE.DeTurck.BilMat E) |
      (Matrix.of w.1.1).det ≠ 0 ∧ (Matrix.of w.2.1).det ≠ 0} := by
    rw [Set.ofPred_and]
    exact ((isOpen_ne (x := (0:ℝ))).preimage hcontdetb).inter
      ((isOpen_ne (x := (0:ℝ))).preimage hcontdet)
  -- continuity of `pPhi` at the limit
  have hcont : ContDiffAt ℝ (⊤ : ℕ∞)
      (fun w : (Work.Diff.EXT.MatE (E := E) × Work.Diff.STE.DeTurck.LinMat E ×
          Work.Diff.STE.DeTurck.BilMat E) × (Work.Diff.EXT.MatE (E := E) ×
            Work.Diff.STE.DeTurck.LinMat E × Work.Diff.STE.DeTurck.BilMat E) =>
        Work.Diff.STE.DeTurck.pPhi w.1.1 w.1.2.1 w.1.2.2 w.2.1 w.2.2.1 w.2.2.2)
      (Work.Diff.STE.D.chartJetOf (I := I) (M := M) g₀.inner (D.x₀ i) ((extChartAt I (D.x₀ i)) x),
        Work.Diff.STE.D.chartJetOf (I := I) (M := M) hlim (D.x₀ i) ((extChartAt I (D.x₀ i)) x)) :=
    (Work.Diff.STE.deTurck.contDiffOn_pPhi (E := E)).contDiffAt (hopen.mem_nhds ⟨hdet₁, hdet₂⟩)
  have hcontjl : ContDiffAt ℝ (⊤ : ℕ∞)
      (fun w : (Work.Diff.EXT.MatE (E := E) × Work.Diff.STE.DeTurck.LinMat E ×
          Work.Diff.STE.DeTurck.BilMat E) × (Work.Diff.EXT.MatE (E := E) ×
            Work.Diff.STE.DeTurck.LinMat E × Work.Diff.STE.DeTurck.BilMat E) =>
        Work.Diff.STE.DeTurck.pPhi w.1.1 w.1.2.1 w.1.2.2 w.2.1 w.2.2.1 w.2.2.2 j l)
      (Work.Diff.STE.D.chartJetOf (I := I) (M := M) g₀.inner (D.x₀ i) ((extChartAt I (D.x₀ i)) x),
        Work.Diff.STE.D.chartJetOf (I := I) (M := M) hlim (D.x₀ i) ((extChartAt I (D.x₀ i)) x)) :=
    contDiffAt_entry_gen hcont j l
  have hlimP := hcontjl.continuousAt.tendsto.comp hpair
  refine hlimP.congr' (Eventually.of_forall (fun n => ?_))
  simp only [Function.comp_apply, Work.Diff.STE.D.pPhiJetOf_apply]


end Work.Diff.STE.Lead
