/-
# Uniform convergence of the jet-level DeTurck operator (v2)

This file proves `Work.Diff.STE.Lead.pPhiJetOf_uniform_v2`: the *uniform* convergence, on the
compact region `Ky D i ∩ {z | c ≤ D.psi i z}`, of the jet-level DeTurck operator
`pPhiJetOf g₀ (hs m)` to `pPhiJetOf g₀ U`, from the convergence `D.BNorm k (hs m - U) → 0`.

The structure is the same as that of `Work.Diff.STE.Lead.pPhiJetOf_uniform`, but the uniform jet
bound — the only input that was missing there — is proved here from the *sharp* chart-matrix jet
bound `Work.Diff.STE.Lead.chartMatJet_sharp` (fed with `Work.Diff.STE.Lead.mat_jet_bound_sqrt`):

* the difference of the chart jets is the chart jet of the difference of the sections;
* every entry of the chart matrix of `h = hs m - U` (value, first and second spatial derivative) is
  bounded by `C √(BNorm k h) / c³` at the points where `c ≤ D.psi i` (uniformly in `m`, since `C` is
  uniform in `h` and the bound is *linear* in `√(BNorm k h)`);
* the entrywise bound gives a norm bound for the whole `2`-jet
  (`norm_chartJetOf_le_of_entry_bounds`), whence `dist (jet (hs m)) (jet U) ≤ B √(BNorm k (hs m - U))`.

The remaining (already formalised) principle is: *a continuous function of a uniformly convergent
family converges uniformly on compacta* (`tendstoUniformlyOn_comp_of_continuousOn`), applied with
`Φ = pPhi`, which is `C^∞` on the locus where both chart matrices are invertible.
-/
import Mathlib
import Submission.Work.Diff.STE.Lead.chartMatJet_sharp
import Submission.Work.Diff.STE.Lead.mat_jet_bound
import Submission.Work.Diff.STE.Lead.clm_norm_le_basis
import Submission.Work.Diff.STE.Lead.jet2_sub
import Submission.Work.Diff.STE.Lead.coordBound
import Submission.Work.Diff.STE.deTurck.contDiffOn_pPhi
import Submission.Work.Diff.STE.D.psi.Basic
import Submission.Work.Diff.STE.D.psi.JetAffine
import Submission.Work.Diff.STE.B3.chartMatOf_posDef
import Submission.Work.Diff.STE.Lead.det_chartMatOf_ne_zero
import Submission.Work.Diff.STE.D.chartData_metric
import Submission.Work.Diff.STE.D.psi.chartMatOf_pd_det_pos
import Submission.Work.Diff.STE.Lead.deTurck_bound

set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology BigOperators Uniformity
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter

namespace Work.Diff.STE.Lead

set_option linter.unusedSectionVars false
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [CompleteSpace E]

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

/-- **Uniform convergence through a continuous function.**  Let `S` be a compact subset of `X`, `Ω` an
open subset of a pseudo-metric space `Y`, `Φ : Y → ℝ` a function continuous on `Ω`, and `P : X → Y` a
continuous map with `P '' S ⊆ Ω`.  If `Q n` converges to `P` uniformly on `S`, then `Φ ∘ Q n`
converges to `Φ ∘ P` uniformly on `S`.

The point is that `IsCompact.uniformContinuousAt_of_continuousAt` only needs `Φ` to be continuous at
the points of the *compact* set `P '' S`, not on the whole of `Y`: this is exactly the situation here,
where `Q n` eventually lies in a neighbourhood of `P '' S` contained in `Ω`. -/
private lemma tendstoUniformlyOn_comp_of_continuousOn
    {X Y : Type*} [TopologicalSpace X] [PseudoMetricSpace Y]
    {S : Set X} (hS : IsCompact S) {Ω : Set Y} (hΩ : IsOpen Ω) {Φ : Y → ℝ}
    (hΦ : ContinuousOn Φ Ω) {P : X → Y} (hP : ContinuousOn P S)
    (hPΩ : ∀ x ∈ S, P x ∈ Ω)
    {Q : ℕ → X → Y} (hQ : TendstoUniformlyOn Q P Filter.atTop S) :
    TendstoUniformlyOn (fun n x => Φ (Q n x)) (fun x => Φ (P x)) Filter.atTop S := by
  rw [Metric.tendstoUniformlyOn_iff] at hQ ⊢
  intro ε hε
  have hK : IsCompact (P '' S) := hS.image_of_continuousOn hP
  have hcont : ∀ a ∈ P '' S, ContinuousAt Φ a := by
    rintro a ⟨x, hx, rfl⟩
    exact hΦ.continuousAt (hΩ.mem_nhds (hPΩ x hx))
  have hmem : {x : Y × Y | x.1 ∈ P '' S → (Φ x.1, Φ x.2) ∈ {p : ℝ × ℝ | dist p.1 p.2 < ε}}
      ∈ 𝓤 Y :=
    hK.uniformContinuousAt_of_continuousAt Φ hcont (Metric.dist_mem_uniformity hε)
  rcases Metric.mem_uniformity_dist.mp hmem with ⟨δ, hδpos, hδ⟩
  filter_upwards [hQ δ hδpos] with n hn
  intro x hx
  exact hδ (hn x hx) ⟨x, hx, rfl⟩

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



/- **The uniform jet bound.**  The difference of the chart jets of two sections is the chart jet of
the difference (`chartJetOf_sub_of_chartData`), and the sharp jet bound for the chart matrix
(`chartMatJet_sharp`, fed with `mat_jet_bound_sqrt`) bounds every entry — the value, the first and
the second spatial derivative — by `C √(BNorm k (h₁ - h₂)) / c³` on the part of the `σ i`-ball where
the localised weight is at least `c > 0`.  Converting the entrywise bound into a norm bound for the
jet (`norm_chartJetOf_le_of_entry_bounds`) gives the claim. -/
set_option backward.isDefEq.respectTransparency true in
private theorem tmp_chartJet_sub_bound
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ((⊤ : ENat) : WithTop ENat) M] [T2Space M] [I.Boundaryless]
    {ι₀ : Type*} [Fintype ι₀] {g₀ : Submission.Diff.SMet I M}
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀)
    (hs : ℕ → Work.Diff.STE.Bil (I := I) (M := M))
    (U : Work.Diff.STE.Bil (I := I) (M := M))
    (hsm : ∀ m : ℕ, Work.Diff.STE.D.ChartData (I := I) (M := M) (hs m))
    (hsmU : Work.Diff.STE.D.ChartData (I := I) (M := M) U)
    (k : ℕ) (hk : Module.finrank ℝ E + 8 < 2 * k)
    (i : ι₀) (c : ℝ) (hc : 0 < c) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ (m : ℕ) (z : Fin (Module.finrank ℝ E) → ℝ),
      z ∈ Work.Diff.STE.D.psi.Ky (I := I) (M := M) D i → c ≤ D.psi i z →
      dist (Work.Diff.STE.D.chartJetOf (I := I) (M := M) (hs m) (D.x₀ i)
          (Work.Diff.STE.flatToE (I := I) (D.x₀ i) z))
        (Work.Diff.STE.D.chartJetOf (I := I) (M := M) U (D.x₀ i)
          (Work.Diff.STE.flatToE (I := I) (D.x₀ i) z))
        ≤ B * Real.sqrt (D.BNorm k (hs m - U)) := by
  classical
  obtain ⟨C_M, hC_M_nn, hMatSharp⟩ := mat_jet_bound_sqrt (I := I) (M := M) D k (by omega)
  obtain ⟨C, hC_nn, hC⟩ :=
    chartMatJet_sharp (I := I) (M := M) D k hk C_M hC_M_nn hMatSharp
  obtain ⟨K₁, hK₁, hKb₁⟩ := clm_norm_le_basis (E := E)
  obtain ⟨K₂, hK₂, hKb₂⟩ := clm_norm_le_basis (E := E)
  set K : ℝ := max 1 (max K₁ (K₂ * K₁)) with hKdef
  have hKnn : (0 : ℝ) ≤ K := by
    rw [hKdef]; exact le_trans zero_le_one (le_max_left _ _)
  refine ⟨K * C / c ^ 3, div_nonneg (mul_nonneg hKnn hC_nn) (by positivity), ?_⟩
  intro m z hzKy hzpsi
  have hy : Work.Diff.STE.flatToE (I := I) (D.x₀ i) z ∈ (extChartAt I (D.x₀ i)).target :=
    Work.Diff.STE.D.psi.flatToE_mem_target_of_mem_Ky (I := I) (M := M) D hzKy
  have hzσ : ‖z‖ ≤ D.σ i :=
    Work.Diff.STE.D.psi.norm_le_sigma_of_mem_Ky (I := I) (M := M) D hzKy
  have hsubsm : Work.Diff.STE.D.ChartData (I := I) (M := M) (hs m - U) :=
    fun x₀' => (hsm m x₀').sub (hsmU x₀')
  have hje : Work.Diff.STE.D.chartJetOf (I := I) (M := M) (hs m - U) (D.x₀ i)
      (Work.Diff.STE.flatToE (I := I) (D.x₀ i) z)
      = Work.Diff.STE.D.chartJetOf (I := I) (M := M) (hs m) (D.x₀ i)
          (Work.Diff.STE.flatToE (I := I) (D.x₀ i) z)
        - Work.Diff.STE.D.chartJetOf (I := I) (M := M) U (D.x₀ i)
          (Work.Diff.STE.flatToE (I := I) (D.x₀ i) z) :=
    chartJetOf_sub_of_chartData (hs m) U (D.x₀ i) hy (hsm m) hsmU
  have hent := fun a b => hC (hs m - U) hsubsm i a b z c hzσ hc hzpsi
  have hR_nn : (0 : ℝ) ≤ C * Real.sqrt (D.BNorm k (hs m - U)) / c ^ 3 :=
    div_nonneg (mul_nonneg hC_nn (Real.sqrt_nonneg _)) (by positivity)
  have hnorm : ‖Work.Diff.STE.D.chartJetOf (I := I) (M := M) (hs m - U) (D.x₀ i)
      (Work.Diff.STE.flatToE (I := I) (D.x₀ i) z)‖
      ≤ K * (C * Real.sqrt (D.BNorm k (hs m - U)) / c ^ 3) := by
    refine norm_chartJetOf_le_of_entry_bounds (hs m - U) hsubsm (D.x₀ i) hy hR_nn
      (fun a b => (hent a b).1) (fun a b p => (hent a b).2.1 p)
      (fun a b p q => (hent a b).2.2 p q) K₁ K₂ hK₁ hK₂
      (fun T R hR hb => hKb₁ T R hR hb) (fun T R hR hb => hKb₂ T R hR hb)
  have hdist : dist (Work.Diff.STE.D.chartJetOf (I := I) (M := M) (hs m) (D.x₀ i)
        (Work.Diff.STE.flatToE (I := I) (D.x₀ i) z))
      (Work.Diff.STE.D.chartJetOf (I := I) (M := M) U (D.x₀ i)
        (Work.Diff.STE.flatToE (I := I) (D.x₀ i) z))
      = ‖Work.Diff.STE.D.chartJetOf (I := I) (M := M) (hs m - U) (D.x₀ i)
        (Work.Diff.STE.flatToE (I := I) (D.x₀ i) z)‖ := by
    have h1 : dist (Work.Diff.STE.D.chartJetOf (I := I) (M := M) (hs m) (D.x₀ i)
          (Work.Diff.STE.flatToE (I := I) (D.x₀ i) z))
        (Work.Diff.STE.D.chartJetOf (I := I) (M := M) U (D.x₀ i)
          (Work.Diff.STE.flatToE (I := I) (D.x₀ i) z))
        = ‖Work.Diff.STE.D.chartJetOf (I := I) (M := M) (hs m) (D.x₀ i)
            (Work.Diff.STE.flatToE (I := I) (D.x₀ i) z)
          - Work.Diff.STE.D.chartJetOf (I := I) (M := M) U (D.x₀ i)
            (Work.Diff.STE.flatToE (I := I) (D.x₀ i) z)‖ :=
      dist_eq_norm
        (Work.Diff.STE.D.chartJetOf (I := I) (M := M) (hs m) (D.x₀ i)
          (Work.Diff.STE.flatToE (I := I) (D.x₀ i) z))
        (Work.Diff.STE.D.chartJetOf (I := I) (M := M) U (D.x₀ i)
          (Work.Diff.STE.flatToE (I := I) (D.x₀ i) z))
    rw [h1, ← hje]
  calc dist (Work.Diff.STE.D.chartJetOf (I := I) (M := M) (hs m) (D.x₀ i)
          (Work.Diff.STE.flatToE (I := I) (D.x₀ i) z))
        (Work.Diff.STE.D.chartJetOf (I := I) (M := M) U (D.x₀ i)
          (Work.Diff.STE.flatToE (I := I) (D.x₀ i) z))
      = ‖Work.Diff.STE.D.chartJetOf (I := I) (M := M) (hs m - U) (D.x₀ i)
          (Work.Diff.STE.flatToE (I := I) (D.x₀ i) z)‖ := hdist
    _ ≤ K * (C * Real.sqrt (D.BNorm k (hs m - U)) / c ^ 3) := hnorm
    _ = (K * C / c ^ 3) * Real.sqrt (D.BNorm k (hs m - U)) := by ring
theorem pPhiJetOf_uniform_v2
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ((⊤ : ENat) : WithTop ENat) M] [T2Space M] [I.Boundaryless]
    {ι₀ : Type*} [Fintype ι₀] {g₀ : Submission.Diff.SMet I M}
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀)
    (hs : ℕ → Work.Diff.STE.Bil (I := I) (M := M))
    (U : Work.Diff.STE.Bil (I := I) (M := M))
    (hsm : ∀ m : ℕ, Work.Diff.STE.D.ChartData (I := I) (M := M) (hs m))
    (hsmU : Work.Diff.STE.D.ChartData (I := I) (M := M) U)
    (hsymU : ∀ (x : M) (u v : TangentSpace I x), U x u v = U x v u)
    (hposU : ∀ (x : M) (v : TangentSpace I x), v ≠ 0 → 0 < U x v v)
    (c : ℝ) (hc : 0 < c)
    (hconv : ∀ k : ℕ, Filter.Tendsto (fun m : ℕ => D.BNorm k (hs m - U)) Filter.atTop (nhds 0)) :
    ∀ (i : ι₀) (j l : Fin (Module.finrank ℝ E)),
      TendstoUniformlyOn
        (fun (m : ℕ) (z : Fin (Module.finrank ℝ E) → ℝ) =>
          Work.Diff.STE.D.pPhiJetOf (I := I) (M := M) g₀ (hs m) (D.x₀ i)
            (Work.Diff.STE.flatToE (I := I) (D.x₀ i) z) j l)
        (fun (z : Fin (Module.finrank ℝ E) → ℝ) =>
          Work.Diff.STE.D.pPhiJetOf (I := I) (M := M) g₀ U (D.x₀ i)
            (Work.Diff.STE.flatToE (I := I) (D.x₀ i) z) j l)
        Filter.atTop
        (Work.Diff.STE.D.psi.Ky (I := I) (M := M) D i ∩
          {z : Fin (Module.finrank ℝ E) → ℝ | c ≤ D.psi i z}) := by
  classical
  -- the chart data of the background metric
  have hg0 : Work.Diff.STE.D.ChartData (I := I) (M := M) g₀.inner :=
    Work.Diff.STE.D.chartData_metric g₀
  intro i j l
  -- the region and its compactness
  set S : Set (Fin (Module.finrank ℝ E) → ℝ) :=
    Work.Diff.STE.D.psi.Ky (I := I) (M := M) D i ∩
      {z : Fin (Module.finrank ℝ E) → ℝ | c ≤ D.psi i z} with hSdef
  have hS : IsCompact S := by
    rw [hSdef]
    refine (Work.Diff.STE.D.psi.isCompact_Ky (I := I) (M := M) D i).of_isClosed_subset ?_
      Set.inter_subset_left
    exact (Work.Diff.STE.D.psi.isCompact_Ky (I := I) (M := M) D i).isClosed.inter
      (isClosed_le continuous_const (D.psi_contDiff i).continuous)
  -- the jet truncation order and the uniform bound
  set kk : ℕ := Module.finrank ℝ E + 9 with hkk
  have hk : Module.finrank ℝ E + 8 < 2 * kk := by rw [hkk]; omega
  obtain ⟨B, hBnn, hB⟩ :=
    tmp_chartJet_sub_bound (I := I) (M := M) D hs U hsm hsmU kk hk i c hc
  -- the ambient space of the jet pairs, and the jet maps
  let Yty : Type _ := (Work.Diff.EXT.MatE (E := E) × Work.Diff.STE.DeTurck.LinMat E ×
      Work.Diff.STE.DeTurck.BilMat E) ×
    (Work.Diff.EXT.MatE (E := E) × Work.Diff.STE.DeTurck.LinMat E ×
      Work.Diff.STE.DeTurck.BilMat E)
  let gj : (Fin (Module.finrank ℝ E) → ℝ) → Work.Diff.EXT.MatE (E := E) ×
      Work.Diff.STE.DeTurck.LinMat E × Work.Diff.STE.DeTurck.BilMat E :=
    fun z => Work.Diff.STE.D.chartJetOf (I := I) (M := M) g₀.inner (D.x₀ i)
      (Work.Diff.STE.flatToE (I := I) (D.x₀ i) z)
  let ju : (Fin (Module.finrank ℝ E) → ℝ) → Work.Diff.EXT.MatE (E := E) ×
      Work.Diff.STE.DeTurck.LinMat E × Work.Diff.STE.DeTurck.BilMat E :=
    fun z => Work.Diff.STE.D.chartJetOf (I := I) (M := M) U (D.x₀ i)
      (Work.Diff.STE.flatToE (I := I) (D.x₀ i) z)
  let jm : ℕ → (Fin (Module.finrank ℝ E) → ℝ) → Work.Diff.EXT.MatE (E := E) ×
      Work.Diff.STE.DeTurck.LinMat E × Work.Diff.STE.DeTurck.BilMat E :=
    fun m z => Work.Diff.STE.D.chartJetOf (I := I) (M := M) (hs m) (D.x₀ i)
      (Work.Diff.STE.flatToE (I := I) (D.x₀ i) z)
  let Pz : (Fin (Module.finrank ℝ E) → ℝ) → Yty := fun z => (gj z, ju z)
  let Qz : ℕ → (Fin (Module.finrank ℝ E) → ℝ) → Yty := fun m z => (gj z, jm m z)
  let Φ : Yty → ℝ :=
    fun w => Work.Diff.STE.DeTurck.pPhi w.1.1 w.1.2.1 w.1.2.2 w.2.1 w.2.2.1 w.2.2.2 j l
  let Ω : Set Yty := {w | (Matrix.of w.1.1).det ≠ 0 ∧ (Matrix.of w.2.1).det ≠ 0}
  -- the open set
  have hΩ : IsOpen Ω := by
    change IsOpen {w : Yty | (Matrix.of w.1.1).det ≠ 0 ∧ (Matrix.of w.2.1).det ≠ 0}
    rw [Set.ofPred_and]
    refine ((isOpen_ne (x := (0 : ℝ))).preimage ?_).inter
      ((isOpen_ne (x := (0 : ℝ))).preimage ?_)
    · refine Continuous.matrix_det ?_
      exact continuous_pi fun a => continuous_pi fun b =>
        (continuous_apply b).comp ((continuous_apply a).comp
          (continuous_fst.comp continuous_fst))
    · refine Continuous.matrix_det ?_
      exact continuous_pi fun a => continuous_pi fun b =>
        (continuous_apply b).comp ((continuous_apply a).comp
          (continuous_fst.comp continuous_snd))
  -- the map `Φ` is continuous on the open set
  have hΦ : ContinuousOn Φ Ω := by
    have hfull : ContinuousOn (fun w : Yty =>
        Work.Diff.STE.DeTurck.pPhi w.1.1 w.1.2.1 w.1.2.2 w.2.1 w.2.2.1 w.2.2.2) Ω :=
      (Work.Diff.STE.deTurck.contDiffOn_pPhi (E := E)).continuousOn
    have hproj : Continuous fun A : Work.Diff.EXT.MatE (E := E) => A j l := by fun_prop
    exact hproj.continuousOn.comp hfull (fun w _ => Set.mem_univ _)
  -- the limit pair takes its values in the open set
  have hPΩ : ∀ z ∈ S, Pz z ∈ Ω := by
    intro z hz
    have hzKy : z ∈ Work.Diff.STE.D.psi.Ky (I := I) (M := M) D i := hz.1
    have hzt : Work.Diff.STE.flatToE (I := I) (D.x₀ i) z ∈ (extChartAt I (D.x₀ i)).target :=
      Work.Diff.STE.D.psi.flatToE_mem_target_of_mem_Ky (I := I) (M := M) D hzKy
    have hpt : D.pt i z ∈ (extChartAt I (D.x₀ i)).source :=
      (extChartAt I (D.x₀ i)).map_target hzt
    have heq : (extChartAt I (D.x₀ i)) (D.pt i z) =
        Work.Diff.STE.flatToE (I := I) (D.x₀ i) z :=
      (extChartAt I (D.x₀ i)).right_inv hzt
    change (Matrix.of (gj z).1).det ≠ 0 ∧ (Matrix.of (ju z).1).det ≠ 0
    refine ⟨?_, ?_⟩
    · exact (Work.Diff.STE.D.psi.chartMatOf_det_pos_of_posDef (I := I) (M := M) g₀.inner
        (D.x₀ i) (fun p u v => g₀.symm p u v) (fun p v hv => g₀.pos p v hv) hzt).ne'
    · have h := Work.Diff.STE.Lead.det_chartMatOf_ne_zero_of_posDef (I := I) (M := M) U
        (D.x₀ i) hpt (fun u v => hsymU (D.pt i z) u v) (fun v hv => hposU (D.pt i z) v hv)
      rw [heq] at h
      exact h
  -- the limit pair is continuous on the region
  have hP : ContinuousOn Pz S := by
    have hsub : S ⊆ {z : Fin (Module.finrank ℝ E) → ℝ |
        Work.Diff.STE.flatToE (I := I) (D.x₀ i) z ∈ (extChartAt I (D.x₀ i)).target} :=
      fun z hz => Work.Diff.STE.D.psi.flatToE_mem_target_of_mem_Ky (I := I) (M := M) D hz.1
    have h1 : ContinuousOn (fun z => Work.Diff.STE.D.chartJetOf (I := I) (M := M) g₀.inner
        (D.x₀ i) (Work.Diff.STE.flatToE (I := I) (D.x₀ i) z)) S :=
      ((Work.Diff.STE.D.psi.contDiffOn_chartJetOf (I := I) (M := M) g₀.inner (D.x₀ i)
          (hg0 (D.x₀ i))).comp
        (Work.Diff.STE.contDiff_flatToE (I := I) (x₀ := D.x₀ i)).contDiffOn
        (fun z hz => hz)).continuousOn.mono hsub
    have h2 : ContinuousOn (fun z => Work.Diff.STE.D.chartJetOf (I := I) (M := M) U
        (D.x₀ i) (Work.Diff.STE.flatToE (I := I) (D.x₀ i) z)) S :=
      ((Work.Diff.STE.D.psi.contDiffOn_chartJetOf (I := I) (M := M) U (D.x₀ i)
          (hsmU (D.x₀ i))).comp
        (Work.Diff.STE.contDiff_flatToE (I := I) (x₀ := D.x₀ i)).contDiffOn
        (fun z hz => hz)).continuousOn.mono hsub
    exact h1.prodMk h2
  -- the pairs converge uniformly
  have hQ : TendstoUniformlyOn Qz Pz Filter.atTop S := by
    rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    have hsq : Filter.Tendsto (fun m : ℕ => Real.sqrt (D.BNorm kk (hs m - U)))
        Filter.atTop (nhds 0) := by
      have h := (hconv kk).sqrt
      rwa [Real.sqrt_zero] at h
    have hlim : Filter.Tendsto (fun m : ℕ => B * Real.sqrt (D.BNorm kk (hs m - U)))
        Filter.atTop (nhds 0) := by
      have h := hsq.const_mul B
      rwa [mul_zero] at h
    filter_upwards [hlim.eventually (isOpen_Iio.mem_nhds hε)] with m hm
    intro z hz
    have hb := hB m z hz.1 hz.2
    have hdist : dist (Pz z) (Qz m z) = dist (Work.Diff.STE.D.chartJetOf (I := I) (M := M) U
        (D.x₀ i) (Work.Diff.STE.flatToE (I := I) (D.x₀ i) z))
        (Work.Diff.STE.D.chartJetOf (I := I) (M := M) (hs m) (D.x₀ i)
          (Work.Diff.STE.flatToE (I := I) (D.x₀ i) z)) := by
      change dist (gj z, ju z) (gj z, jm m z) = dist (ju z) (jm m z)
      rw [Prod.dist_eq, dist_self, max_eq_right dist_nonneg]
    rw [hdist, dist_comm]
    exact lt_of_le_of_lt hb hm
  -- assemble
  have hmain := tendstoUniformlyOn_comp_of_continuousOn (X := Fin (Module.finrank ℝ E) → ℝ)
    (Y := Yty) hS hΩ hΦ hP hPΩ hQ
  refine (hmain.congr (Eventually.of_forall (fun m => fun z _ => ?_))).congr_right
    (fun z _ => ?_)
  · change Φ (Qz m z) = Work.Diff.STE.D.pPhiJetOf (I := I) (M := M) g₀ (hs m) (D.x₀ i)
      (Work.Diff.STE.flatToE (I := I) (D.x₀ i) z) j l
    simp only [Φ, Qz, gj, jm, Work.Diff.STE.D.pPhiJetOf_apply]
  · change Φ (Pz z) = Work.Diff.STE.D.pPhiJetOf (I := I) (M := M) g₀ U (D.x₀ i)
      (Work.Diff.STE.flatToE (I := I) (D.x₀ i) z) j l
    simp only [Φ, Pz, gj, ju, Work.Diff.STE.D.pPhiJetOf_apply]

end Work.Diff.STE.Lead
