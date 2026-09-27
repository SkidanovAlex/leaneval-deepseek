import Mathlib
import Submission.Work.Kernel.GreenCover
import Submission.Work.Kernel.exists_modelBump_chartBall
import Submission.Work.Drive.greenEnergyGlue
import Submission.Work.Drive.greenEnergyPairing
import Submission.Work.Drive.energyGreenRung
import Submission.Work.Drive.chartPoleIdentity
import Submission.Work.Analysis.Harmonic.integrable_inner_gradient_logNorm_sub
import Submission.Work.Kernel.greenCoverPairingAux
import Submission.Work.Kernel.pairIntegrable_of_honest_growth
import Submission.Work.Kernel.growth_bound_pole

open Set Metric MeasureTheory Filter
open scoped Manifold Topology Gradient

noncomputable section

set_option linter.unusedSectionVars false


namespace Work.Kernel

variable {X : Type*} [TopologicalSpace X] [T2Space X] [ChartedSpace ℂ X]
  [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X]




/-- **Integrability of a pairing term, in the chart of the weight.** -/
theorem pairIntegrable_piece_source {Ω K : Set X} {a b c : X} {N : ℕ}
    (E : GreenCover (Fin N) Ω K a b) (i₀ : Fin N)
    (hi₀mem : c ∈ (chartAt ℂ (E.y i₀)).source ∩
      (chartAt ℂ (E.y i₀)) ⁻¹' Metric.ball ((chartAt ℂ (E.y i₀)) (E.y i₀)) (E.s i₀))
    (hi₀nmem : ∀ i, i ≠ i₀ → c ∉ (chartAt ℂ (E.y i)) ⁻¹'
      Metric.closedBall ((chartAt ℂ (E.y i)) (E.y i)) (E.σ i))
    (hΩo : IsOpen Ω) (hcΩ : c ∈ Ω)
    {gC : X → ℝ} (hgC : Work.SimplyConnected.ABS.IsGreenOn Ω c gC)
    {ψ : X → ℝ} (hψsupp : tsupport ψ ⊆ K) (hψΩ : K ⊆ Ω)
    (hψC1 : ∀ k, ∀ x ∈ (chartAt ℂ (E.y k)).source,
      ContDiffAt ℝ 1 (ψ ∘ (chartAt ℂ (E.y k)).symm) ((chartAt ℂ (E.y k)) x))
    {θ : Fin N → X → ℝ}
    (hC1 : ∀ (t k : Fin N), ∀ x ∈ (chartAt ℂ (E.y k)).source,
      ContDiffAt ℝ 1 ((θ t) ∘ (chartAt ℂ (E.y k)).symm) ((chartAt ℂ (E.y k)) x))
    (hθsupp : ∀ t, tsupport (θ t) ⊆
      Submission.chartBall (chartAt ℂ (E.y t)) ((chartAt ℂ (E.y t)) (E.y t)) (E.σ t))
    (i t : Fin N) :
    Work.Drive.PairIntegrable (E.y i) (E.ρ i) (E.s i) (E.ψ i) gC (θ t * ψ) := by
  classical
  have hPhi : ∀ (k : Fin N), ∀ x ∈ (chartAt ℂ (E.y k)).source,
      ContDiffAt ℝ 1 ((θ t * ψ) ∘ (chartAt ℂ (E.y k)).symm) ((chartAt ℂ (E.y k)) x) := by
    intro k x hx
    have h1 : ((θ t * ψ) ∘ (chartAt ℂ (E.y k)).symm)
        = fun w : ℂ => (θ t) ((chartAt ℂ (E.y k)).symm w) * ψ ((chartAt ℂ (E.y k)).symm w) :=
      rfl
    rw [h1]
    exact (hC1 t k x hx).mul (hψC1 k x hx)
  have hgCharm : ∀ x ∈ Ω, x ≠ c → Submission.HarmonicOnXAt gC x :=
    fun x hx hxc => hgC.2.1 x ⟨hx, hxc⟩
  obtain ⟨hWcont, C₁, hC₁, hWbd⟩ := weight_continuous_bounded (x := E.y i) (ρ := E.ρ i)
    (σ := E.s i) (W := E.ψ i) (continuous_cover_weight E i) (E.hspos i).le
    (lt_trans (E.hsσ i) (E.hσρ i)) (E.htgt i)
  by_cases hi : i = i₀
  · subst i
    obtain ⟨C₂, hC₂, hcontσ, hbound⟩ :=
      growth_bound_pole E i₀ hΩo hcΩ hgC hi₀mem.1 (hPhi i₀)
    refine pairIntegrable_of_honest_growth (x := E.y i₀) (ρ := E.ρ i₀) (σ := E.s i₀)
      (W := E.ψ i₀) (f := gC) (g := θ t * ψ) (p := (chartAt ℂ (E.y i₀)) c)
      (C₁ := C₁) (C₂ := C₂) (E.hspos i₀).le (lt_trans (E.hsσ i₀) (E.hσρ i₀)) (E.htgt i₀)
      hWcont hWbd hC₁ hC₂ ?_ ?_
    · refine hcontσ.mono ?_
      intro z hz
      exact ⟨Metric.ball_subset_ball (le_of_lt (E.hsσ i₀)) hz.1, hz.2⟩
    · intro z hz hzp
      exact hbound z (Metric.ball_subset_ball (le_of_lt (E.hsσ i₀)) hz) hzp
  · have hav : ∀ z ∈ Metric.closedBall ((chartAt ℂ (E.y i)) (E.y i)) (E.σ i),
        (chartAt ℂ (E.y i)).symm z ≠ c := by
      intro z hz hcon
      have hzρ : z ∈ Metric.ball ((chartAt ℂ (E.y i)) (E.y i)) (E.ρ i) :=
        Metric.closedBall_subset_ball (E.hσρ i) hz
      have hright : (chartAt ℂ (E.y i)) ((chartAt ℂ (E.y i)).symm z) = z :=
        (chartAt ℂ (E.y i)).right_inv (E.htgt i hzρ)
      have hceq : (chartAt ℂ (E.y i)) c = z := by rw [← hcon]; exact hright
      exact hi₀nmem i hi (by rw [Set.mem_preimage, hceq]; exact hz)
    obtain ⟨C₂, hC₂, hcontσ, hbound⟩ :=
      growth_bound_away E hgCharm hΩo hav (hPhi i)
    refine pairIntegrable_of_honest_growth (x := E.y i) (ρ := E.ρ i) (σ := E.s i)
      (W := E.ψ i) (f := gC) (g := θ t * ψ) (p := (chartAt ℂ (E.y i)) (E.y i))
      (C₁ := C₁) (C₂ := C₂) (E.hspos i).le (lt_trans (E.hsσ i) (E.hσρ i)) (E.htgt i)
      hWcont hWbd hC₁ hC₂ ?_ ?_
    · exact hcontσ.mono (fun z hz => Metric.ball_subset_ball (le_of_lt (E.hsσ i)) hz.1)
    · intro z hz hzp
      exact hbound z (Metric.ball_subset_ball (le_of_lt (E.hsσ i)) hz) hzp

/-- **Integrability of a pairing term, in the chart of the test function.** -/
theorem pairIntegrable_piece_target {Ω K : Set X} {a b c : X} {N : ℕ}
    (E : GreenCover (Fin N) Ω K a b) (i₀ : Fin N)
    (hi₀mem : c ∈ (chartAt ℂ (E.y i₀)).source ∩
      (chartAt ℂ (E.y i₀)) ⁻¹' Metric.ball ((chartAt ℂ (E.y i₀)) (E.y i₀)) (E.s i₀))
    (hi₀nmem : ∀ i, i ≠ i₀ → c ∉ (chartAt ℂ (E.y i)) ⁻¹'
      Metric.closedBall ((chartAt ℂ (E.y i)) (E.y i)) (E.σ i))
    (hΩo : IsOpen Ω) (hcΩ : c ∈ Ω)
    {gC : X → ℝ} (hgC : Work.SimplyConnected.ABS.IsGreenOn Ω c gC)
    {ψ : X → ℝ} (hψsupp : tsupport ψ ⊆ K) (hψΩ : K ⊆ Ω)
    (hψC1 : ∀ k, ∀ x ∈ (chartAt ℂ (E.y k)).source,
      ContDiffAt ℝ 1 (ψ ∘ (chartAt ℂ (E.y k)).symm) ((chartAt ℂ (E.y k)) x))
    {θ : Fin N → X → ℝ}
    (hC1 : ∀ (t k : Fin N), ∀ x ∈ (chartAt ℂ (E.y k)).source,
      ContDiffAt ℝ 1 ((θ t) ∘ (chartAt ℂ (E.y k)).symm) ((chartAt ℂ (E.y k)) x))
    (hθsupp : ∀ t, tsupport (θ t) ⊆
      Submission.chartBall (chartAt ℂ (E.y t)) ((chartAt ℂ (E.y t)) (E.y t)) (E.σ t))
    (t i : Fin N) :
    Work.Drive.PairIntegrable (E.y t) (E.ρ t) (E.σ t) (E.ψ i) gC (θ t * ψ) := by
  classical
  have hPhi : ∀ (k : Fin N), ∀ x ∈ (chartAt ℂ (E.y k)).source,
      ContDiffAt ℝ 1 ((θ t * ψ) ∘ (chartAt ℂ (E.y k)).symm) ((chartAt ℂ (E.y k)) x) := by
    intro k x hx
    have h1 : ((θ t * ψ) ∘ (chartAt ℂ (E.y k)).symm)
        = fun w : ℂ => (θ t) ((chartAt ℂ (E.y k)).symm w) * ψ ((chartAt ℂ (E.y k)).symm w) :=
      rfl
    rw [h1]
    exact (hC1 t k x hx).mul (hψC1 k x hx)
  have hgCharm : ∀ x ∈ Ω, x ≠ c → Submission.HarmonicOnXAt gC x :=
    fun x hx hxc => hgC.2.1 x ⟨hx, hxc⟩
  obtain ⟨hWcont, C₁, hC₁, hWbd⟩ := weight_continuous_bounded (x := E.y t) (ρ := E.ρ t)
    (σ := E.σ t) (W := E.ψ i) (continuous_cover_weight E i)
    (lt_trans (E.hspos t) (E.hsσ t)).le (E.hσρ t) (E.htgt t)
  by_cases ht : t = i₀
  · subst t
    obtain ⟨C₂, hC₂, hcontσ, hbound⟩ :=
      growth_bound_pole E i₀ hΩo hcΩ hgC hi₀mem.1 (hPhi i₀)
    exact pairIntegrable_of_honest_growth (x := E.y i₀) (ρ := E.ρ i₀) (σ := E.σ i₀)
      (W := E.ψ i) (f := gC) (g := θ i₀ * ψ) (p := (chartAt ℂ (E.y i₀)) c)
      (C₁ := C₁) (C₂ := C₂) (lt_trans (E.hspos i₀) (E.hsσ i₀)).le (E.hσρ i₀) (E.htgt i₀)
      hWcont hWbd hC₁ hC₂ (by simpa [Set.sdiff_eq] using hcontσ) hbound
  · have hav : ∀ z ∈ Metric.closedBall ((chartAt ℂ (E.y t)) (E.y t)) (E.σ t),
        (chartAt ℂ (E.y t)).symm z ≠ c := by
      intro z hz hcon
      have hzρ : z ∈ Metric.ball ((chartAt ℂ (E.y t)) (E.y t)) (E.ρ t) :=
        Metric.closedBall_subset_ball (E.hσρ t) hz
      have hright : (chartAt ℂ (E.y t)) ((chartAt ℂ (E.y t)).symm z) = z :=
        (chartAt ℂ (E.y t)).right_inv (E.htgt t hzρ)
      have hceq : (chartAt ℂ (E.y t)) c = z := by rw [← hcon]; exact hright
      exact hi₀nmem t ht (by rw [Set.mem_preimage, hceq]; exact hz)
    obtain ⟨C₂, hC₂, hcontσ, hbound⟩ :=
      growth_bound_away E hgCharm hΩo hav (hPhi t)
    exact pairIntegrable_of_honest_growth (x := E.y t) (ρ := E.ρ t) (σ := E.σ t)
      (W := E.ψ i) (f := gC) (g := θ t * ψ) (p := (chartAt ℂ (E.y t)) (E.y t))
      (C₁ := C₁) (C₂ := C₂) (lt_trans (E.hspos t) (E.hsσ t)).le (E.hσρ t) (E.htgt t)
      hWcont hWbd hC₁ hC₂ (hcontσ.mono Set.sdiff_subset) hbound
/-- **The pole term of the telescoping.** -/
theorem theta_pole {Ω K : Set X} {a b c : X} {N : ℕ} (E : GreenCover (Fin N) Ω K a b)
    (i₀ : Fin N)
    (hi₀mem : c ∈ (chartAt ℂ (E.y i₀)).source ∩
      (chartAt ℂ (E.y i₀)) ⁻¹' Metric.ball ((chartAt ℂ (E.y i₀)) (E.y i₀)) (E.s i₀))
    (hi₀nmem : ∀ i, i ≠ i₀ → c ∉ (chartAt ℂ (E.y i)) ⁻¹'
      Metric.closedBall ((chartAt ℂ (E.y i)) (E.y i)) (E.σ i))
    (hΩo : IsOpen Ω) (hcΩ : c ∈ Ω)
    {gC : X → ℝ} (hgC : Work.SimplyConnected.ABS.IsGreenOn Ω c gC)
    {θ : Fin N → X → ℝ}
    (hθsupp : ∀ t, tsupport (θ t) ⊆
      Submission.chartBall (chartAt ℂ (E.y t)) ((chartAt ℂ (E.y t)) (E.y t)) (E.σ t))
    (hθsum : ∀ x ∈ K, ∑ t, θ t x = 1)
    {ψ : X → ℝ} (hψsupp : tsupport ψ ⊆ K) (hψΩ : K ⊆ Ω)
    (hψC1 : ∀ k, ∀ x ∈ (chartAt ℂ (E.y k)).source,
      ContDiffAt ℝ 1 (ψ ∘ (chartAt ℂ (E.y k)).symm) ((chartAt ℂ (E.y k)) x))
    (hC1 : ∀ (t k : Fin N), ∀ x ∈ (chartAt ℂ (E.y k)).source,
      ContDiffAt ℝ 1 ((θ t) ∘ (chartAt ℂ (E.y k)).symm) ((chartAt ℂ (E.y k)) x))
    (hθsmooth : ∀ t, ContMDiff (modelWithCornersSelf ℝ ℂ) (modelWithCornersSelf ℝ ℝ)
      (((⊤ : ℕ∞) : WithTop ℕ∞)) (θ t))
    (hintθ : ∀ i t, Work.Drive.PairIntegrable (E.y i) (E.ρ i) (E.s i) (E.ψ i) gC (θ t * ψ)) :
    Work.Drive.pairTerm (E.y i₀) (E.ρ i₀) (E.σ i₀) (fun _ => (1 : ℝ)) gC (θ i₀ * ψ)
      = 2 * Real.pi * ψ c := by
  classical
  set q : ℂ := (chartAt ℂ (E.y i₀)) c with hq
  set ctr : ℂ := (chartAt ℂ (E.y i₀)) (E.y i₀) with hctr
  set χ : X → ℝ := θ i₀ * ψ with hχ
  have hρpos : 0 < E.ρ i₀ := lt_trans (lt_trans (E.hspos i₀) (E.hsσ i₀)) (E.hσρ i₀)
  have hσpos : 0 < E.σ i₀ := lt_trans (E.hspos i₀) (E.hsσ i₀)
  have hsymm_q : (chartAt ℂ (E.y i₀)).symm q = c := by
    rw [hq]; exact (chartAt ℂ (E.y i₀)).left_inv hi₀mem.1
  have hqball : q ∈ Metric.ball ctr (E.ρ i₀) := by
    rw [hq, hctr]
    exact Metric.ball_subset_ball (le_of_lt (E.hσρ i₀))
      (Metric.ball_subset_ball (le_of_lt (E.hsσ i₀)) hi₀mem.2)
  have hχc1pt : ∀ y ∈ (chartAt ℂ (E.y i₀)).source,
      ContDiffAt ℝ 1 (χ ∘ (chartAt ℂ (E.y i₀)).symm) ((chartAt ℂ (E.y i₀)) y) := by
    intro y hy
    have h1 : (χ ∘ (chartAt ℂ (E.y i₀)).symm)
        = fun w : ℂ =>
          (θ i₀) ((chartAt ℂ (E.y i₀)).symm w) * ψ ((chartAt ℂ (E.y i₀)).symm w) := by
      rw [hχ]; rfl
    rw [h1]
    exact (hC1 i₀ i₀ y hy).mul (hψC1 i₀ y hy)
  have hχsupp : tsupport χ ⊆ (chartAt ℂ (E.y i₀)) ⁻¹' Metric.ball ctr (E.σ i₀) := by
    intro x hx
    have hx' : x ∈ tsupport (θ i₀ * ψ) := by rwa [hχ] at hx
    have h1 : x ∈ tsupport (θ i₀) := tsupport_mul_subset_left hx'
    have h2 : (chartAt ℂ (E.y i₀)) x ∈
        Metric.ball ((chartAt ℂ (E.y i₀)) (E.y i₀)) (E.σ i₀) := (hθsupp i₀ h1).2
    exact h2
  obtain ⟨hχc1, hχcs⟩ := clampedPullback_contDiff_hasCompactSupport (x := E.y i₀) (u := χ)
    (ρ := E.ρ i₀) (σ := E.σ i₀) hρpos (le_of_lt hσpos) (E.hσρ i₀)
    (E.htgt i₀) hχc1pt hχsupp
  have hsuppσ : tsupport (Work.Drive.clampedPullback (E.y i₀) (E.ρ i₀) χ) ⊆
      Metric.closedBall ctr (E.σ i₀) := by
    refine closure_minimal ?_ Metric.isClosed_closedBall
    intro z hz
    rw [Function.mem_support] at hz
    have hzρ : z ∈ Metric.ball ctr (E.ρ i₀) := by
      by_contra hcon
      exact hz (Work.Drive.clampedPullback_eq_zero_of_notMem_ball (u := χ) hcon)
    rw [Metric.mem_closedBall]
    have hχne : χ ((chartAt ℂ (E.y i₀)).symm z) ≠ 0 := by
      rw [← Work.Drive.clampedPullback_apply_of_mem (u := χ) hzρ]; exact hz
    have hy : (chartAt ℂ (E.y i₀)).symm z ∈ tsupport χ :=
      subset_tsupport _ (Function.mem_support.mpr hχne)
    have hball : (chartAt ℂ (E.y i₀)) ((chartAt ℂ (E.y i₀)).symm z) ∈
        Metric.ball ctr (E.σ i₀) := hχsupp hy
    rw [(chartAt ℂ (E.y i₀)).right_inv (E.htgt i₀ hzρ)] at hball
    exact le_of_lt hball
  -- the expansion of gC at the pole, in the pole chart
  obtain ⟨r, hrpos, Hloc, hHloctgt, hHlocharm, hHloceq⟩ :=
    greenExpansion_chart (Ω := Ω) (c := c) (y := E.y i₀) hΩo hcΩ hgC hi₀mem.1
  obtain ⟨R, hRpos, hRsub⟩ : ∃ R : ℝ, 0 < R ∧ Metric.ball q R ⊆ Metric.ball ctr (E.ρ i₀) := by
    obtain ⟨ε, hε, hεsub⟩ := Metric.mem_nhds_iff.mp (Metric.isOpen_ball.mem_nhds hqball)
    exact ⟨ε, hε, hεsub⟩
  set R' : ℝ := min R r with hR'
  have hR'pos : 0 < R' := lt_min hRpos hrpos
  have hR'sub : Metric.ball q R' ⊆ Metric.ball ctr (E.ρ i₀) :=
    (Metric.ball_subset_ball (min_le_left _ _)).trans hRsub
  have hR'le : R' ≤ r := min_le_right _ _
  set H₁ : ℂ → ℝ := fun z => gC ((chartAt ℂ (E.y i₀)).symm z) + Real.log ‖z - q‖ with hH₁
  have hH₁harm : ∀ z : ℂ, z ∈ Metric.ball ctr (E.ρ i₀) → z ≠ q →
      InnerProductSpace.HarmonicAt H₁ z := by
    intro z hzρ hzq
    have hzsrc : (chartAt ℂ (E.y i₀)).symm z ∈ (chartAt ℂ (E.y i₀)).source :=
      (chartAt ℂ (E.y i₀)).map_target (E.htgt i₀ hzρ)
    have hzΩ : (chartAt ℂ (E.y i₀)).symm z ∈ Ω := E.hballΩ i₀ ⟨hzsrc, by
      rw [Set.mem_preimage, (chartAt ℂ (E.y i₀)).right_inv (E.htgt i₀ hzρ)]; exact hzρ⟩
    have hzc : (chartAt ℂ (E.y i₀)).symm z ≠ c := by
      intro hcon
      refine hzq ?_
      rw [hq, ← hcon]
      exact ((chartAt ℂ (E.y i₀)).right_inv (E.htgt i₀ hzρ)).symm
    have hg : Submission.HarmonicOnXAt gC ((chartAt ℂ (E.y i₀)).symm z) :=
      hgC.2.1 _ ⟨hzΩ, hzc⟩
    have hgt : InnerProductSpace.HarmonicAt
        (fun w : ℂ => gC ((chartAt ℂ (E.y i₀)).symm w)) z := by
      have h1 := (Submission.HarmonicOnXAt_iff_chart (u := gC)
        (x := (chartAt ℂ (E.y i₀)).symm z) (y := E.y i₀) hzsrc).mp hg
      rwa [(chartAt ℂ (E.y i₀)).right_inv (E.htgt i₀ hzρ)] at h1
    have hlog : InnerProductSpace.HarmonicAt (fun w : ℂ => Real.log ‖w - q‖) z :=
      AnalyticAt.harmonicAt_log_norm (f := fun w : ℂ => w - q)
        (analyticAt_id.sub analyticAt_const) (sub_ne_zero.mpr hzq)
    have hsum : InnerProductSpace.HarmonicAt
        (fun w : ℂ => gC ((chartAt ℂ (E.y i₀)).symm w) + Real.log ‖w - q‖) z := hgt.add hlog
    exact hsum
  have hHloc_cont : ContinuousOn Hloc (Metric.closedBall q (R' / 2)) :=
    hHlocharm.continuousOn.mono
      ((Metric.closedBall_subset_ball (by linarith)).trans (Metric.ball_subset_ball hR'le))
  obtain ⟨M, hM⟩ := (isCompact_closedBall q (R' / 2)).exists_bound_of_continuousOn hHloc_cont
  have hbnd : ∀ z : ℂ, ‖z - q‖ < R' / 2 → z ≠ q → |H₁ z| ≤ M := by
    intro z hz hzq
    have h1 : z ∈ Metric.ball q R' := Metric.mem_ball.mpr (by rw [dist_eq_norm]; linarith)
    have h2 : z ∈ Metric.ball q r := Metric.ball_subset_ball hR'le h1
    have heq : H₁ z = Hloc z := by
      have h := hHloceq z h2 hzq
      simp only [hH₁]
      linarith
    rw [heq]
    exact hM z (Metric.mem_closedBall.mpr (by rw [dist_eq_norm]; linarith))
  have hharm0 : ∀ z : ℂ, ‖z - q‖ < R' / 2 → z ≠ q → InnerProductSpace.HarmonicAt H₁ z := by
    intro z hz hzq
    have h1 : z ∈ Metric.ball q R' := Metric.mem_ball.mpr (by rw [dist_eq_norm]; linarith)
    exact hH₁harm z (hR'sub h1) hzq
  obtain ⟨U, hUharm, hUeq⟩ := Work.Potential.removable_singularity_ball_center
    (u := H₁) (a := q) (R := R' / 2) (M := M) (by linarith) hharm0 hbnd
  set H : ℂ → ℝ := fun z => if z = q then U q else H₁ z with hH
  have hH_q : InnerProductSpace.HarmonicAt H q := by
    refine (InnerProductSpace.harmonicAt_congr_nhds ?_).mpr (hUharm q ?_)
    · filter_upwards [Metric.ball_mem_nhds q (by linarith : (0 : ℝ) < R' / 4)] with w hw
      by_cases hwq : w = q
      · rw [hwq]; simp only [hH, if_true]
      · have hw' : ‖w - q‖ < R' / 2 / 2 := by
          rw [Metric.mem_ball, dist_eq_norm] at hw; linarith
        have h1 : U w = H₁ w := hUeq w hw' hwq
        simp only [hH]; rw [if_neg hwq, h1]
    · rw [sub_self, norm_zero]; linarith
  have hH_off : ∀ z : ℂ, z ∈ Metric.ball ctr (E.ρ i₀) → z ≠ q →
      InnerProductSpace.HarmonicAt H z := by
    intro z hzρ hzq
    refine (InnerProductSpace.harmonicAt_congr_nhds ?_).mpr (hH₁harm z hzρ hzq)
    filter_upwards [isOpen_compl_singleton.mem_nhds hzq] with w hw
    have hwq : w ≠ q := by simpa using hw
    simp only [hH]; rw [if_neg hwq]
  have hH_eq : ∀ z : ℂ, z ∈ Metric.ball ctr (E.ρ i₀) → z ≠ q →
      gC ((chartAt ℂ (E.y i₀)).symm z) = -Real.log ‖z - q‖ + H z := by
    intro z hzρ hzq
    have h1 : H z = H₁ z := by simp only [hH]; rw [if_neg hzq]
    rw [h1]
    simp only [hH₁]
    ring
  have hH_supp : ∀ z ∈ tsupport (Work.Drive.clampedPullback (E.y i₀) (E.ρ i₀) χ),
      InnerProductSpace.HarmonicAt H z := by
    intro z hz
    have hzρ : z ∈ Metric.ball ctr (E.ρ i₀) :=
      Metric.closedBall_subset_ball (E.hσρ i₀) (hsuppσ hz)
    by_cases hzq : z = q
    · rw [hzq]; exact hH_q
    · exact hH_off z hzρ hzq
  have hPI : Work.Drive.PairIntegrable (E.y i₀) (E.ρ i₀) (E.σ i₀)
      (fun _ => (1 : ℝ)) gC χ := by
    obtain ⟨C₂, hC₂nn, hcontσ, hboundσ⟩ :=
      growth_bound_pole E i₀ hΩo hcΩ hgC hi₀mem.1 hχc1pt
    refine pairIntegrable_of_honest_growth (x := E.y i₀) (ρ := E.ρ i₀) (σ := E.σ i₀)
      (W := fun _ => (1 : ℝ)) (f := gC) (g := χ) (p := q) (C₁ := 1) (C₂ := C₂)
      (le_of_lt hσpos) (E.hσρ i₀) (E.htgt i₀) continuousOn_const ?_ zero_le_one hC₂nn ?_ hboundσ
    · intro z hz; simp
    · simpa [Set.sdiff_eq] using hcontσ
  have hint : Integrable (fun z : ℂ => inner (𝕜 := ℝ)
      (gradient (Work.Drive.clampedPullback (E.y i₀) (E.ρ i₀) gC) z)
      (gradient (Work.Drive.clampedPullback (E.y i₀) (E.ρ i₀) χ) z)) := by
    have hPI' : Integrable (fun z : ℂ =>
        Work.Drive.clampedPullback (E.y i₀) (E.σ i₀) (fun _ : X => (1 : ℝ)) z *
        inner (𝕜 := ℝ) (gradient (Work.Drive.clampedPullback (E.y i₀) (E.ρ i₀) gC) z)
          (gradient (Work.Drive.clampedPullback (E.y i₀) (E.ρ i₀) χ) z)) := hPI
    refine (integrable_congr ?_).mp hPI'
    filter_upwards [compl_mem_ae_iff.mpr
      (MeasureTheory.Measure.addHaar_sphere volume ctr (E.σ i₀))] with z hz
    have hzne : dist z ctr ≠ E.σ i₀ := fun hcon => hz (by rw [Metric.mem_sphere]; exact hcon)
    rcases lt_or_gt_of_ne hzne with hlt | hgt
    · rw [Work.Drive.clampedPullback_apply_of_mem (u := fun _ : X => (1 : ℝ))
        (Metric.mem_ball.mpr hlt), one_mul]
    · have hnot : z ∉ tsupport (Work.Drive.clampedPullback (E.y i₀) (E.ρ i₀) χ) := fun hcon =>
        (not_le.mpr hgt) (Metric.mem_closedBall.mp (hsuppσ hcon))
      rw [Work.Drive.clampedPullback_eq_zero_of_notMem_ball (u := fun _ : X => (1 : ℝ))
          (fun hcon => absurd (Metric.mem_ball.mp hcon) (not_lt.mpr (le_of_lt hgt))), zero_mul,
        Work.Analysis.Harmonic.gradient_eq_zero_of_notMem_tsupport hnot, inner_zero_right]
  have hi1 : Integrable (fun z : ℂ => inner (𝕜 := ℝ)
      (gradient (fun y : ℂ => -Real.log ‖y - q‖) z)
      (gradient (Work.Drive.clampedPullback (E.y i₀) (E.ρ i₀) χ) z)) :=
    Work.Analysis.Harmonic.integrable_inner_gradient_logNorm_sub (a := q) hχc1 hχcs
  have hi2 : Integrable (fun z : ℂ => inner (𝕜 := ℝ) (gradient H z)
      (gradient (Work.Drive.clampedPullback (E.y i₀) (E.ρ i₀) χ) z)) :=
    integrable_inner_gradient_of_harmonicOnSupport hH_supp hχc1 hχcs
  have hkey : Work.Drive.pairTerm (E.y i₀) (E.ρ i₀) (E.σ i₀) (fun _ => (1 : ℝ)) gC χ
      = 2 * Real.pi * Work.Drive.clampedPullback (E.y i₀) (E.ρ i₀) χ q :=
    pairTerm_pole_local (x₀ := E.y i₀) (f := gC) (χ := χ) (H := H) (p := q)
      (ρ := E.ρ i₀) (σ := E.σ i₀) (le_of_lt hσpos) (E.hσρ i₀) (E.htgt i₀) hχsupp
      hH_supp hH_eq hχc1 hχcs hi1 hi2 hint
  have hval : Work.Drive.clampedPullback (E.y i₀) (E.ρ i₀) χ q = ψ c := by
    rw [Work.Drive.clampedPullback_apply_of_mem (u := χ) hqball, hsymm_q]
    show (θ i₀ * ψ) c = ψ c
    by_cases hψc : ψ c = 0
    · simp [Pi.mul_apply, hψc]
    · have hcK : c ∈ K := hψsupp (subset_tsupport ψ (Function.mem_support.mpr hψc))
      have hsum := hθsum c hcK
      have hzero : ∀ t : Fin N, t ≠ i₀ → θ t c = 0 := by
        intro t ht
        by_contra hne
        have hmem : c ∈ tsupport (θ t) := subset_tsupport _ (Function.mem_support.mpr hne)
        have h1 : (chartAt ℂ (E.y t)) c ∈ Metric.ball ((chartAt ℂ (E.y t)) (E.y t)) (E.σ t) :=
          (hθsupp t hmem).2
        exact hi₀nmem t ht (Metric.ball_subset_closedBall h1)
      have h2 : ∑ t, θ t c = θ i₀ c :=
        Finset.sum_eq_single i₀ (fun t _ ht => hzero t ht)
          (fun h => absurd (Finset.mem_univ i₀) h)
      have h1 : θ i₀ c = 1 := by rw [h2] at hsum; exact hsum
      simp [Pi.mul_apply, h1]
  rw [hkey, hval]


theorem greenCover_pairing_eq_two_pi_mul {X : Type*} [TopologicalSpace X] [T2Space X]
    [ChartedSpace ℂ X] [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X]
    {Ω K : Set X} {a b c : X} {gC : X → ℝ} {N : ℕ} (E : Work.Kernel.GreenCover (Fin N) Ω K a b)
    (i₀ : Fin N)
    (hi₀mem : c ∈ (chartAt ℂ (E.y i₀)).source ∩
      (chartAt ℂ (E.y i₀)) ⁻¹' Metric.ball ((chartAt ℂ (E.y i₀)) (E.y i₀)) (E.s i₀))
    (hi₀nmem : ∀ i, i ≠ i₀ → c ∉ (chartAt ℂ (E.y i)) ⁻¹'
      Metric.closedBall ((chartAt ℂ (E.y i)) (E.y i)) (E.σ i))
    (hΩo : IsOpen Ω) (hΩc : IsCompact (closure Ω))
    (hgC : Work.SimplyConnected.ABS.IsGreenOn Ω c gC)
    {ψ : X → ℝ} (hψsupp : tsupport ψ ⊆ K) (hψΩ : K ⊆ Ω)
    (hψC1 : ∀ k, ∀ x ∈ (chartAt ℂ (E.y k)).source,
      ContDiffAt ℝ 1 (ψ ∘ (chartAt ℂ (E.y k)).symm) ((chartAt ℂ (E.y k)) x))
    (hint : ∀ i, Work.Drive.PairIntegrable (E.y i) (E.ρ i) (E.s i) (E.ψ i) gC ψ) :
    ∑ i, Work.Drive.pairTerm (E.y i) (E.ρ i) (E.s i) (E.ψ i) gC ψ = 2 * Real.pi * ψ c := by
  classical
  haveI : IsManifold (modelWithCornersSelf ℝ ℂ) ⊤ X :=
    Work.SimplyConnected.ABS.isManifold_self_model_real_infty
  -- the partition of unity subordinate to the chart balls
  obtain ⟨θ, hθsmooth, hθnn, hθle, hθsupp, hθsum⟩ := exists_theta_pou E
  have hC1 : ∀ (t k : Fin N), ∀ x ∈ (chartAt ℂ (E.y k)).source,
      ContDiffAt ℝ 1 ((θ t) ∘ (chartAt ℂ (E.y k)).symm) ((chartAt ℂ (E.y k)) x) :=
    fun t k => contDiffAt_chart_of_contMDiff (hθsmooth t) (E.y k)
  -- harmonicity of gC off the pole
  have hgCharm : ∀ x ∈ Ω, x ≠ c → Submission.HarmonicOnXAt gC x :=
    fun x hx hxc => hgC.2.1 x ⟨hx, hxc⟩
  have hcΩ : c ∈ Ω := E.hballΩ i₀ ⟨hi₀mem.1, Metric.ball_subset_ball
    (le_of_lt (lt_trans (E.hsσ i₀) (E.hσρ i₀))) hi₀mem.2⟩
  -- the test function is a sum of the localised pieces
  have hsum_fun : (∑ t : Fin N, θ t * ψ) = ψ := by
    funext x
    by_cases hx : ψ x = 0
    · simp only [Finset.sum_apply, Pi.mul_apply, hx, mul_zero, Finset.sum_const, smul_zero]
    · have hxK : x ∈ K := hψsupp (subset_tsupport ψ (Function.mem_support.mpr hx))
      have h1 : ∑ t, θ t x = 1 := hθsum x hxK
      calc (∑ t : Fin N, θ t * ψ) x = ∑ t, θ t x * ψ x := by
            simp only [Finset.sum_apply, Pi.mul_apply]
        _ = (∑ t, θ t x) * ψ x := (Finset.sum_mul (Finset.univ) (fun t => θ t x) (ψ x)).symm
        _ = 1 * ψ x := by rw [h1]
        _ = ψ x := one_mul _
  have hstep1 : (∑ i, Work.Drive.pairTerm (E.y i) (E.ρ i) (E.s i) (E.ψ i) gC ψ)
      = ∑ i, Work.Drive.pairTerm (E.y i) (E.ρ i) (E.s i) (E.ψ i) gC (∑ t, θ t * ψ) := by
    refine Finset.sum_congr rfl fun i _ => ?_
    exact congrArg (fun χ => Work.Drive.pairTerm (E.y i) (E.ρ i) (E.s i) (E.ψ i) gC χ)
      hsum_fun.symm
  -- certificates
  have hdiffθ : ∀ i t, ∀ᵐ z ∂(volume : Measure ℂ),
      DifferentiableAt ℝ (Work.Drive.clampedPullback (E.y i) (E.ρ i) (θ t * ψ)) z := by
    intro i t
    refine clampedPullback_differentiableAt_ae_of_differentiableOn (E.htgt i) ?_
    intro z hz
    have hzsrc : (chartAt ℂ (E.y i)).symm z ∈ (chartAt ℂ (E.y i)).source :=
      (chartAt ℂ (E.y i)).map_target (E.htgt i hz)
    have hright : (chartAt ℂ (E.y i)) ((chartAt ℂ (E.y i)).symm z) = z :=
      (chartAt ℂ (E.y i)).right_inv (E.htgt i hz)
    have h := (hC1 t i _ hzsrc).mul (hψC1 i _ hzsrc)
    rw [hright] at h
    have hfun : (fun w : ℂ => (θ t * ψ) ((chartAt ℂ (E.y i)).symm w))
        = (fun w : ℂ => (θ t) ((chartAt ℂ (E.y i)).symm w)
            * ψ ((chartAt ℂ (E.y i)).symm w)) := rfl
    rw [hfun]
    exact h.differentiableAt (by norm_num)
  have hintθ : ∀ i t, Work.Drive.PairIntegrable (E.y i) (E.ρ i) (E.s i) (E.ψ i)
      gC (θ t * ψ) := by
    intro i t
    exact pairIntegrable_piece_source E i₀ hi₀mem hi₀nmem hΩo hcΩ hgC hψsupp hψΩ hψC1 hC1
      hθsupp i t
  have hintθt : ∀ t i, Work.Drive.PairIntegrable (E.y t) (E.ρ t) (E.σ t) (E.ψ i)
      gC (θ t * ψ) := by
    intro t i
    exact pairIntegrable_piece_target E i₀ hi₀mem hi₀nmem hΩo hcΩ hgC hψsupp hψΩ hψC1 hC1
      hθsupp t i
  -- linearity in the third argument
  have hstep2 : (∑ i, Work.Drive.pairTerm (E.y i) (E.ρ i) (E.s i) (E.ψ i) gC (∑ t, θ t * ψ))
      = ∑ t, ∑ i, Work.Drive.pairTerm (E.y i) (E.ρ i) (E.s i) (E.ψ i) gC (θ t * ψ) := by
    rw [Finset.sum_congr rfl (fun i _ => Work.Drive.pairTerm_finset_sum Finset.univ
      (fun t _ => hdiffθ i t) (fun t _ => hintθ i t))]
    rw [Finset.sum_comm]
  -- the collapse in each chart
  have hstep3 : ∀ t : Fin N, (∑ i, Work.Drive.pairTerm (E.y i) (E.ρ i) (E.s i) (E.ψ i)
        gC (θ t * ψ))
      = Work.Drive.pairTerm (E.y t) (E.ρ t) (E.σ t) (fun _ => (1 : ℝ)) gC (θ t * ψ) := by
    intro t
    have h1 : (∑ i, Work.Drive.pairTerm (E.y i) (E.ρ i) (E.s i) (E.ψ i) gC (θ t * ψ))
        = ∑ i, Work.Drive.pairTerm (E.y t) (E.ρ t) (E.σ t) (E.ψ i) gC (θ t * ψ) := by
      refine Finset.sum_congr rfl fun i _ => ?_
      by_cases hit : i = t
      · subst hit
        exact pairTerm_clamp_weight E i
      · exact theta_transfer E i₀ hi₀nmem hθsupp hψsupp hgCharm hC1 hψC1 hit
    have h2 : (∑ i, Work.Drive.pairTerm (E.y t) (E.ρ t) (E.σ t) (E.ψ i) gC (θ t * ψ))
        = Work.Drive.pairTerm (E.y t) (E.ρ t) (E.σ t) (∑ i, E.ψ i) gC (θ t * ψ) :=
      (Work.Drive.pairTerm_weight_finset_sum Finset.univ (fun i _ => hintθt t i)).symm
    have h3 : Work.Drive.pairTerm (E.y t) (E.ρ t) (E.σ t) (∑ i, E.ψ i) gC (θ t * ψ)
        = Work.Drive.pairTerm (E.y t) (E.ρ t) (E.σ t) (fun _ => (1 : ℝ)) gC (θ t * ψ) :=
      Work.Drive.GreenRung.pairTerm_congr_weight (E.htgt t) (E.hσρ t) (fun y hy => by
        have hyK : y ∈ K := hψsupp (tsupport_mul_subset_right hy)
        have h1 : ∑ i, E.ψ i y = 1 := E.hsum y hyK
        have h2 : (∑ i, E.ψ i) y = 1 := by simpa using h1
        simpa using h2)
    rw [h1, h2, h3]
  -- the result
  rw [hstep1, hstep2]
  rw [Finset.sum_congr rfl (fun t _ => hstep3 t)]
  rw [Finset.sum_eq_single i₀]
  · exact theta_pole E i₀ hi₀mem hi₀nmem hΩo hcΩ hgC hθsupp hθsum hψsupp hψΩ hψC1 hC1
      hθsmooth hintθ
  · intro t _ ht
    exact theta_harmonic_zero E i₀ hi₀nmem hθsupp hψsupp hψΩ hgCharm hC1 hψC1 ht
  · intro h
    exact absurd (Finset.mem_univ i₀) h


end Work.Kernel