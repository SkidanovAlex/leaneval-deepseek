import Mathlib
import Submission.Diff.STEGal
import Submission.Work.Diff.STE.B3.BNorm_J_le
import Submission.Work.Diff.STE.B3.BNorm_J_le_uniform
import Submission.Work.Diff.STE.B3.BNorm_J_sub_le
import Submission.Work.Diff.STE.B3.bump_expansion_fixed
import Submission.Work.Diff.STE.B3.closure_Omega_goodSet
import Submission.Work.Diff.STE.B3.tMapFun_injOn_det
import Submission.Work.Diff.STE.B3.goodSet_smooth_noT2
import Submission.Work.Diff.STE.B3.STruncC_contDiff_periodic
import Submission.Work.Diff.STE.B3.fourierCoeff_periodization
import Submission.Work.Diff.STE.B3.CompSmooth
import Submission.Work.Diff.STE.B3.densGood
import Submission.Work.Diff.STE.Man.exists_sMet_of_chartData
import Submission.Work.Diff.STE.CSq_tail_le
import Submission.Work.Diff.STE.summable_weighted_fourierCoeff_of_contDiff
import Submission.Work.Diff.STE.summable_norm_of_CSq
import Submission.Work.Diff.EXT.glueDefs
import Submission.Work.Diff.STE.B3.dens_bound_sigma
import Submission.Work.Diff.STE.Lead.truncDiff_tendsto_uniform

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-! Guidance from the project lead (the requester):

CONTEXT: last layer of short_time_existence (owner H10, Diff/STE). The lead dispatched these pieces top-level so they run in parallel.
Vocabulary: Submission/Work/Diff/STE/B3/Comp.lean (R, Rper, CPair, BPair, BNorm, Rstar, STruncR, J), B3/Data.lean (B3Data: x₀, χ, ζ, e, dens,
psi), D/* (Galerkin, genMap, jSym, addSec, deTurckSec, ChartData, smetOf), and the lead's Submission/Diff/STEGal.lean (galState, IsGalSol,
GalUniform). REUSE the PROVED Layer A toolkit (Submission/Work/Diff/STE/*.lean; LayerA.lean lists it): CSq_trunc_le,
CSq_trunc_sub_le, friedrichs_commutator, CSq_period_comp_arg_le, CSq_conv_tame_le, CSq_comp_le, garding_vec_uniform,
gronwall_linear_bound, norm_seriesFun_le (Sobolev), CSq_tail_le (compactness), eq_zero_of_fourierCoeff_eq_zero, BPair_J_self,
BPair_Rstar, J_finite_rank, R_Rstar_expansion2 (chart transfer). Read DESIGN.md (sessions 6–8) first. Do not re-prove anything listed.
If a statement here is false as stated (e.g. a missing hypothesis on ρ or on B3Data), declare_false with the precise reason; the lead fixes it.
ROUTE (J_tendsto). J h − h = Σ_i R_i*((S_ε − 1) R_i h) + (Σ_i R_i* R_i h − h).
The second term vanishes: Σ_i R_i* R_i = id by the normalisation Σ ζ_i² = 1 and χ_i = 1 where ζ_i ≠ 0 (check the B3Data fields; if
this identity fails, report it).
The first is ≤ C Σ_i ‖(S_ε − 1) R_i h‖_k by the J_norm_le-type transfer bound. ‖(S_ε − 1) f‖_k → 0 for f with ‖f‖_{k+1} finite:
CSq_trunc_sub_le gives ≤ C ε ‖f‖_{k+1} (ρ(0) = 1, ρ smooth). R_i h is smooth and compactly supported, so every level is finite.
-/

namespace Work.Diff.STE.Lead

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg Submission.Diff.STEGal
open scoped Manifold ContDiff Bundle Topology BigOperators
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 400000

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ((⊤ : ENat) : WithTop ENat) M] [T2Space M] [I.Boundaryless] [CompactSpace M]
  {ι₀ : Type*} [Fintype ι₀] {g₀ : SMet I M}

section Smooth

variable (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀)
  {h : Bil (I := I) (M := M)}

/-- **`ChartData` gives smoothness of the section of the bundle of bilinear forms.**  This is the
first half of the `contMDiff` field of `Work.Diff.STE.D.smetOf`; neither symmetry nor positivity is
used. -/
lemma frameMat_contMDiffAt_of_chartData (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀)
    (hh : Work.Diff.STE.D.ChartData (I := I) (M := M) h) (x₀ : M) :
    ContMDiffAt I (𝓘(ℝ, Work.Diff.EXT.MatE (E := E))) (⊤ : ℕ∞)
      (fun x : M => Work.Diff.EXT.frameMat (I := I) x₀ x (h x)) x₀ := by
  have hchart := (hh x₀).contDiffAt (extChartAt_target_mem_nhds (I := I) x₀)
  have h1 : ContDiffAt ℝ (⊤ : ℕ∞)
      (fun y : E => Work.Diff.EXT.frameMat (I := I) x₀ ((extChartAt I x₀).symm y)
        (h ((extChartAt I x₀).symm y))) ((extChartAt I x₀) x₀) := by
    unfold Work.Diff.EXT.frameMat
    exact hchart
  have h2 : ContMDiffAt (𝓘(ℝ, E)) (𝓘(ℝ, Work.Diff.EXT.MatE (E := E))) (⊤ : ℕ∞)
      (fun y : E => Work.Diff.EXT.frameMat (I := I) x₀ ((extChartAt I x₀).symm y)
        (h ((extChartAt I x₀).symm y))) ((extChartAt I x₀) x₀) := h1.contMDiffAt
  have h3 := h2.comp x₀ (contMDiffAt_extChartAt (I := I) (x := x₀))
  refine h3.congr_of_eventuallyEq ?_
  filter_upwards [IsOpen.mem_nhds (chartAt H x₀).open_source (mem_chart_source H x₀)] with x hx
  have hx' : x ∈ (extChartAt I x₀).source := by rwa [extChartAt_source]
  simp only [Function.comp_apply]
  rw [show (extChartAt I x₀).symm ((extChartAt I x₀) x) = x from (extChartAt I x₀).left_inv hx']

/-- The section `x ↦ ⟨x, h x⟩` is `C^∞` at every point when `h` has smooth chart matrix. -/
lemma section_contMDiffAt_of_chartData (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀)
    (hh : Work.Diff.STE.D.ChartData (I := I) (M := M) h) (x₀ : M) :
    ContMDiffAt I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) (⊤ : ℕ∞)
      (fun x : M => TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
        (E := fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) x (h x)) x₀ :=
  Work.Diff.STE.Man.section_contMDiffAt_of_frameMat (I := I) (x₀ := x₀) (γ := h)
    (frameMat_contMDiffAt_of_chartData D hh x₀)

/-- The chart expression of the matrix of `h` in the frame `D.e i` is smooth on the chart target. -/
lemma matChart_contDiffOn_of_chartData (hh : Work.Diff.STE.D.ChartData (I := I) (M := M) h)
    (i : ι₀) (a b : Fin (Module.finrank ℝ E)) :
    ContDiffOn ℝ (⊤ : ℕ∞) (D.matChart i h a b) (extChartAt I (D.x₀ i)).target := by
  have hsec : ∀ x : M, ContMDiffAt I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) (⊤ : ℕ∞)
      (fun x : M => TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
        (E := fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) x (h x)) x :=
    fun x => section_contMDiffAt_of_chartData D hh x
  have hmat : ∀ x : M, ContMDiffAt I 𝓘(ℝ, ℝ) (⊤ : ℕ∞)
      (fun x : M => h x (D.e i a x) (D.e i b x)) x := by
    intro x
    have hψ := (hsec x).contMDiffWithinAt (s := Set.univ)
    have hv : ContMDiffWithinAt I (I.prod 𝓘(ℝ, E)) (⊤ : ℕ∞) (T% (D.e i a)) Set.univ x :=
      (D.hesm i a).contMDiffAt.contMDiffWithinAt
    have hw : ContMDiffWithinAt I (I.prod 𝓘(ℝ, E)) (⊤ : ℕ∞) (T% (D.e i b)) Set.univ x :=
      (D.hesm i b).contMDiffAt.contMDiffWithinAt
    have hres := hψ.clm_bundle_apply₂ (F₁ := E) (F₂ := E) hv hw
    simp only [contMDiffWithinAt_totalSpace] at hres
    exact hres.2
  have huniv : ContMDiffOn I 𝓘(ℝ, ℝ) (⊤ : ℕ∞)
      (fun x : M => h x (D.e i a x) (D.e i b x)) Set.univ :=
    fun x _ => (hmat x).contMDiffWithinAt
  have hcomp : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, ℝ) (⊤ : ℕ∞)
      (fun y : E => h ((extChartAt I (D.x₀ i)).symm y)
        (D.e i a ((extChartAt I (D.x₀ i)).symm y))
        (D.e i b ((extChartAt I (D.x₀ i)).symm y))) (extChartAt I (D.x₀ i)).target :=
    huniv.comp (contMDiffOn_extChartAt_symm (I := I) (x := D.x₀ i) (n := (⊤ : ℕ∞)))
      (fun y _ => Set.mem_univ _)
  have h' := hcomp.contDiffOn
  change ContDiffOn ℝ (⊤ : ℕ∞) (fun y => h ((extChartAt I (D.x₀ i)).symm y)
    (D.e i a ((extChartAt I (D.x₀ i)).symm y))
    (D.e i b ((extChartAt I (D.x₀ i)).symm y))) (extChartAt I (D.x₀ i)).target
  exact h'

/-- **The Layer B3 components of a section with smooth chart matrix are smooth.** -/
lemma R_contDiff_of_chartData (hh : Work.Diff.STE.D.ChartData (I := I) (M := M) h)
    (i : ι₀) (a b : Fin (Module.finrank ℝ E)) :
    ContDiff ℝ (⊤ : ℕ∞) (D.R i h a b) :=
  D.R_contDiff i h a b (Work.Diff.STE.B3.densGood (I := I) (M := M) D i)
    (matChart_contDiffOn_of_chartData D hh i a b)

end Smooth

section Expansion

open Work.Diff.STE.B3

variable (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀)
  (ρ : (Fin (Module.finrank ℝ E) → ℝ) → ℝ) (ε : ℝ)
  (h : Bil (I := I) (M := M))

/-- `tMapFun` lands in the open unit cube where `ζ i` does not vanish there. -/
lemma tMapFun_mem_cube_of_zeta_ne (i j : ι₀) {z : Fin (Module.finrank ℝ E) → ℝ}
    (hz : D.ζ i (D.pt j z) ≠ 0) :
    ∀ k : Fin (Module.finrank ℝ E),
      (Work.Diff.STE.D.tMapFun (I := I) (M := M) D i j z) k ∈ Set.Ioo (-(1 / 2 : ℝ)) (1 / 2) := by
  intro k
  obtain ⟨-, hlt⟩ := D.hζsupp i (D.pt j z) hz
  have h1 : ‖Work.Diff.STE.D.tMapFun (I := I) (M := M) D i j z‖ < D.σ i := hlt
  have h2 : ‖(Work.Diff.STE.D.tMapFun (I := I) (M := M) D i j z) k‖
      ≤ ‖Work.Diff.STE.D.tMapFun (I := I) (M := M) D i j z‖ := norm_le_pi_norm _ k
  have hσ : D.σ i ≤ 1 / 8 := by have := D.hσ2 i; linarith
  have h3 : ‖(Work.Diff.STE.D.tMapFun (I := I) (M := M) D i j z) k‖ < (1 / 2 : ℝ) := by
    linarith
  have h3' : |(Work.Diff.STE.D.tMapFun (I := I) (M := M) D i j z) k| < (1 / 2 : ℝ) := by
    rwa [Real.norm_eq_abs] at h3
  rw [Set.mem_Ioo]
  exact abs_lt.mp h3'

/-- On the open cube the raw truncation defect (relative to `R i h`) agrees with the periodised
one. -/
lemma rawDiff_eq_truncDiff_of_cube (i : ι₀) (c d : Fin (Module.finrank ℝ E))
    {y : Fin (Module.finrank ℝ E) → ℝ}
    (hy : ∀ k : Fin (Module.finrank ℝ E), y k ∈ Set.Ioo (-(1 / 2 : ℝ)) (1 / 2)) :
    ((rawDiff D ρ ε h i c d y : ℝ) : ℂ) = truncDiff D ρ ε h i c d y := by
  have hper := Rper_eq_of_mem_cube D h i c d hy
  simp only [rawDiff, truncDiff, hper, Complex.sub_re, Complex.ofReal_re]

/-- **The bumped cross-chart coefficients.**  For fixed `(i,j,a,b)` there are smooth bumps `φ c d`,
equal to `1` on the topological support of the explicit coefficient `coeffFun`, supported in
`goodSet D i j`, such that the bumped product `z ↦ φ c d z • coeffFun D i j a b c d z` is globally
`C^∞`, is supported in the open cube and is supported in `goodSet D i j`.

This is `Work.Diff.STE.B3.bump_expansion_fixed` with the bump *exposed*, so that the caller knows
that the bumped coefficient agrees with the raw `coeffFun` wherever the latter is non-zero (which is
what makes the raw coefficient bounded). -/
lemma exists_bumped_coeff (i j : ι₀) (a b : Fin (Module.finrank ℝ E)) :
    ∃ φ : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) →
        (Fin (Module.finrank ℝ E) → ℝ) → ℝ,
      (∀ c d, ContDiff ℝ (⊤ : ℕ∞) (φ c d)) ∧
      (∀ c d, tsupport (φ c d) ⊆ Work.Diff.STE.D.goodSet (I := I) (M := M) D i j) ∧
      (∀ c d z, z ∈ tsupport (Work.Diff.STE.D.coeffFun (I := I) (M := M) D i j a b c d) →
        φ c d z = 1) ∧
      (∀ c d, ContDiff ℝ (⊤ : ℕ∞) (fun z => ((φ c d z : ℝ) : ℂ) *
        ((Work.Diff.STE.D.coeffFun (I := I) (M := M) D i j a b c d z : ℝ) : ℂ))) := by
  have hgood := closure_Omega_goodSet (I := I) (M := M) D i j
  have hopen := (goodSet_smooth_noT2 (I := I) (M := M) D i j).1
  have hsmC := (goodSet_smooth_noT2 (I := I) (M := M) D i j).2.2 a b
  have hKU : ∀ c d : Fin (Module.finrank ℝ E),
      tsupport (Work.Diff.STE.D.coeffFun (I := I) (M := M) D i j a b c d)
        ⊆ Work.Diff.STE.D.goodSet (I := I) (M := M) D i j :=
    fun c d => (closure_mono (support_coeffFun_subset_Omega D i j a b c d)).trans hgood
  choose φ hφsm hφ1 hφsup hφsm2 using fun cd : Fin (Module.finrank ℝ E) ×
      Fin (Module.finrank ℝ E) =>
    Work.Diff.STE.D.bump_smul_smooth
      (tsupport (Work.Diff.STE.D.coeffFun (I := I) (M := M) D i j a b cd.1 cd.2))
      (Work.Diff.STE.D.goodSet (I := I) (M := M) D i j)
      (isCompact_tsupport_coeffFun D i j a b cd.1 cd.2) hopen (hKU cd.1 cd.2)
      (fun z => ((Work.Diff.STE.D.coeffFun (I := I) (M := M) D i j a b cd.1 cd.2 z : ℝ) : ℂ))
      (Complex.ofRealCLM.contDiff.comp_contDiffOn (hsmC cd.1 cd.2))
  exact ⟨fun c d => φ (c, d), fun c d => hφsm (c, d), fun c d => hφsup (c, d),
    fun c d z => hφ1 (c, d) z, fun c d => hφsm2 (c, d)⟩

/-- **The pointwise expansion of `J ρ ε h - h` in the chart `j`.**  The chart-`j` matrix of
`J ρ ε h - h` is a finite sum of bumped cross-chart coefficients times the *periodised* truncation
defects. -/
lemma R_J_sub_expansion (j : ι₀) (a b : Fin (Module.finrank ℝ E)) :
    ∃ G : ι₀ → Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) →
        (Fin (Module.finrank ℝ E) → ℝ) → ℂ,
      (∀ i c d, ContDiff ℝ (⊤ : ℕ∞) (G i c d)) ∧
      (∀ i c d, Function.support (G i c d) ⊆
        Set.pi Set.univ (fun _ : Fin (Module.finrank ℝ E) => Set.Ioo (-(1 / 2 : ℝ)) (1 / 2))) ∧
      (∀ i c d, IsCompact (tsupport (G i c d))) ∧
      (∀ i c d, tsupport (G i c d) ⊆ Work.Diff.STE.D.goodSet (I := I) (M := M) D i j) ∧
      (∀ i c d z, G i c d z ≠ 0 → D.ζ i (D.pt j z) ≠ 0) ∧
      (∀ i c d z, ‖Work.Diff.STE.D.coeffFun (I := I) (M := M) D i j a b c d z‖
        ≤ ‖G i c d z‖) ∧
      (∀ (ε : ℝ) (z : Fin (Module.finrank ℝ E) → ℝ),
        ((D.R j (D.J ρ ε h - h) a b z : ℝ) : ℂ)
          = ∑ i, ∑ c, ∑ d, G i c d z *
              truncDiff D ρ ε h i c d (Work.Diff.STE.D.tMapFun (I := I) (M := M) D i j z)) := by
  classical
  -- the bumps
  choose φ hφsm hφsup hφ1 hφsm2 using fun i : ι₀ =>
    exists_bumped_coeff (I := I) (M := M) D i j a b
  refine ⟨fun i c d z => ((φ i c d z : ℝ) : ℂ) *
      ((Work.Diff.STE.D.coeffFun (I := I) (M := M) D i j a b c d z : ℝ) : ℂ), ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i c d; exact hφsm2 i c d
  · -- the support lies in the open cube: `G = φ • coeffFun` and `coeffFun` vanishes off `ψ_j ≠ 0`
    intro i c d z hz
    have hz' : ((φ i c d z : ℝ) : ℂ) *
        ((Work.Diff.STE.D.coeffFun (I := I) (M := M) D i j a b c d z : ℝ) : ℂ) ≠ 0 := hz
    have h1 : ((Work.Diff.STE.D.coeffFun (I := I) (M := M) D i j a b c d z : ℝ) : ℂ) ≠ 0 :=
      (mul_ne_zero_iff.mp hz').2
    have h2 : Work.Diff.STE.D.coeffFun (I := I) (M := M) D i j a b c d z ≠ 0 := fun h0 =>
      h1 (by rw [h0, Complex.ofReal_zero])
    exact D.psi_supp j (fun h0 => h2 (coeffFun_eq_zero_of_psi_eq_zero D i j a b c d h0))
  · -- compact support, from the cube compactness
    intro i c d
    have hsub : tsupport ((fun i c d z => ((φ i c d z : ℝ) : ℂ) *
        ((Work.Diff.STE.D.coeffFun (I := I) (M := M) D i j a b c d z : ℝ) : ℂ)) i c d)
        ⊆ Set.pi Set.univ (fun _ : Fin (Module.finrank ℝ E) =>
          Set.Icc (-(1 / 2 : ℝ)) (1 / 2)) := by
      refine (closure_mono ?_).trans
        (closure_minimal (Set.pi_mono fun _ _ => Set.Ioo_subset_Icc_self)
          (isClosed_set_pi fun _ _ => isClosed_Icc))
      intro z hz
      have hz' : ((φ i c d z : ℝ) : ℂ) *
          ((Work.Diff.STE.D.coeffFun (I := I) (M := M) D i j a b c d z : ℝ) : ℂ) ≠ 0 := hz
      have h1 : ((Work.Diff.STE.D.coeffFun (I := I) (M := M) D i j a b c d z : ℝ) : ℂ) ≠ 0 :=
        (mul_ne_zero_iff.mp hz').2
      have h2 : Work.Diff.STE.D.coeffFun (I := I) (M := M) D i j a b c d z ≠ 0 := fun h0 =>
        h1 (by rw [h0, Complex.ofReal_zero])
      exact D.psi_supp j (fun h0 => h2 (coeffFun_eq_zero_of_psi_eq_zero D i j a b c d h0))
    exact (steB3_isCompact_closedCube (ι := Fin (Module.finrank ℝ E))).of_isClosed_subset
      (isClosed_tsupport _) hsub
  · -- the topological support lies in `goodSet`
    intro i c d z hz
    have hsub : tsupport ((fun i c d z => ((φ i c d z : ℝ) : ℂ) *
        ((Work.Diff.STE.D.coeffFun (I := I) (M := M) D i j a b c d z : ℝ) : ℂ)) i c d)
        ⊆ tsupport (φ i c d) ∪ tsupport (Work.Diff.STE.D.coeffFun (I := I) (M := M) D i j a b c d) := by
      refine (closure_mono ?_).trans (le_of_eq closure_union)
      intro w hw
      have hw' : ((φ i c d w : ℝ) : ℂ) *
          ((Work.Diff.STE.D.coeffFun (I := I) (M := M) D i j a b c d w : ℝ) : ℂ) ≠ 0 := hw
      exact Or.inl (Function.mem_support.mpr
        (fun h0 => hw' (by rw [h0, Complex.ofReal_zero, zero_mul])))
    rcases hsub hz with h1 | h1
    · exact hφsup i c d h1
    · exact (closure_mono (support_coeffFun_subset_Omega D i j a b c d)).trans
        (closure_Omega_goodSet (I := I) (M := M) D i j) h1
  · -- `G ≠ 0` forces `ζ i ∘ pt j ≠ 0`
    intro i c d z hz
    have hz' : ((φ i c d z : ℝ) : ℂ) *
        ((Work.Diff.STE.D.coeffFun (I := I) (M := M) D i j a b c d z : ℝ) : ℂ) ≠ 0 := hz
    have h1 : ((Work.Diff.STE.D.coeffFun (I := I) (M := M) D i j a b c d z : ℝ) : ℂ) ≠ 0 :=
      (mul_ne_zero_iff.mp hz').2
    have h2 : Work.Diff.STE.D.coeffFun (I := I) (M := M) D i j a b c d z ≠ 0 := fun h0 =>
      h1 (by rw [h0, Complex.ofReal_zero])
    exact fun h0 => h2 (coeffFun_eq_zero_of_zeta_eq_zero D i j a b c d h0)
  · -- the raw coefficient is bounded by the bumped one
    intro i c d z
    show ‖Work.Diff.STE.D.coeffFun (I := I) (M := M) D i j a b c d z‖ ≤
      ‖((φ i c d z : ℝ) : ℂ) *
        ((Work.Diff.STE.D.coeffFun (I := I) (M := M) D i j a b c d z : ℝ) : ℂ)‖
    by_cases h0 : Work.Diff.STE.D.coeffFun (I := I) (M := M) D i j a b c d z = 0
    · rw [h0, Complex.ofReal_zero, mul_zero, norm_zero, norm_zero]
    · rw [hφ1 i c d z (subset_closure (Function.mem_support.mpr h0)), Complex.ofReal_one,
        one_mul]
      exact le_of_eq (by simp)
  · intro ε z
    -- step 1: `J ρ ε h - h = Σ_i R_i* (rawDiff i)`
    have hJeq : D.J ρ ε h = ∑ i : ι₀, D.Rstar i (truncComp D ρ ε h i) := by
      rw [Work.Diff.STE.B3Data.J]
      refine Finset.sum_congr rfl fun i _ => ?_
      congr 1
    have hrecon : h = ∑ i : ι₀, D.Rstar i (compFun D h i) := (Rstar_R_eq_id D h).symm
    have hfun : D.J ρ ε h - h = ∑ i : ι₀, D.Rstar i (rawDiff D ρ ε h i) := by
      funext p
      rw [Pi.sub_apply, congrFun hJeq p, congrFun hrecon p, Finset.sum_apply, Finset.sum_apply,
        Finset.sum_apply]
      refine (Finset.sum_sub_distrib
        (fun i : ι₀ => D.Rstar i (truncComp D ρ ε h i) p)
        (fun i : ι₀ => D.Rstar i (compFun D h i) p)).symm.trans ?_
      refine Finset.sum_congr rfl fun i _ => ?_
      have h := congrFun (Rstar_sub D i (truncComp D ρ ε h i) (compFun D h i)).symm p
      simp only [Pi.sub_apply] at h
      exact h
    rw [hfun]
    rw [show D.R j (∑ i : ι₀, D.Rstar i (rawDiff D ρ ε h i)) a b z
        = ∑ i : ι₀, D.R j (D.Rstar i (rawDiff D ρ ε h i)) a b z from by
      simp only [Work.Diff.STE.B3Data.R, Work.Diff.STE.B3Data.mat, Finset.sum_apply, sum_apply,
        Finset.mul_sum]]
    push_cast
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [R_Rstar_expansion_pointwise_noT2 D i j a b (rawDiff D ρ ε h i) z]
    push_cast
    refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => ?_
    by_cases h0 : Work.Diff.STE.D.coeffFun (I := I) (M := M) D i j a b c d z = 0
    · have hG0 : ((φ i c d z : ℝ) : ℂ) *
          ((Work.Diff.STE.D.coeffFun (I := I) (M := M) D i j a b c d z : ℝ) : ℂ) = 0 := by
        rw [h0, Complex.ofReal_zero, mul_zero]
      simp only [h0, Complex.ofReal_zero, zero_mul, hG0]
      ring
    · have hφz : φ i c d z = 1 :=
        hφ1 i c d z (subset_closure (Function.mem_support.mpr h0))
      have hzeta : D.ζ i (D.pt j z) ≠ 0 := fun hz =>
        h0 (coeffFun_eq_zero_of_zeta_eq_zero D i j a b c d hz)
      have hcube := tMapFun_mem_cube_of_zeta_ne (I := I) (M := M) D i j hzeta
      rw [rawDiff_eq_truncDiff_of_cube D ρ ε h i c d hcube]
      simp only [hφz, Complex.ofReal_one, one_mul]

end Expansion

section SupBound

open Work.Diff.STE.B3

variable (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀)
  (ρ : (Fin (Module.finrank ℝ E) → ℝ) → ℝ)
  (h : Bil (I := I) (M := M))

/-- **Uniform bound for the chart components of `J ρ ε h - h`.**  Each component is bounded by a
fixed constant times the sum of the moduli of the periodised truncation defects at the chart
transition. -/
lemma R_J_sub_sup_le (j : ι₀) (a b : Fin (Module.finrank ℝ E)) :
    ∃ K : ι₀ → Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → ℝ,
      (∀ i c d, 0 ≤ K i c d) ∧ ∀ (ε : ℝ) (z : Fin (Module.finrank ℝ E) → ℝ),
        ‖D.R j (D.J ρ ε h - h) a b z‖ ≤ ∑ i, ∑ c, ∑ d, K i c d *
          ‖truncDiff D ρ ε h i c d (Work.Diff.STE.D.tMapFun (I := I) (M := M) D i j z)‖ := by
  classical
  obtain ⟨G, hGsm, hGsupp, hGcomp, hGgood, hGzeta, hGle, hid⟩ :=
    R_J_sub_expansion (I := I) (M := M) D ρ h j a b
  -- a uniform bound for the bumped coefficients
  have hbound : ∀ (i : ι₀) (c d : Fin (Module.finrank ℝ E)), ∃ Kg : ℝ, 0 ≤ Kg ∧
      ∀ z : Fin (Module.finrank ℝ E) → ℝ, ‖G i c d z‖ ≤ Kg := by
    intro i c d
    obtain ⟨C, hC⟩ := (hGcomp i c d).exists_bound_of_continuousOn
      (hGsm i c d).continuous.continuousOn
    refine ⟨max C 0, le_max_right _ _, fun z => ?_⟩
    by_cases hz : z ∈ tsupport (G i c d)
    · exact (hC z hz).trans (le_max_left _ _)
    · rw [image_eq_zero_of_notMem_tsupport hz, norm_zero]
      exact le_max_right _ _
  choose Kg hKgnn hKgb using hbound
  refine ⟨Kg, hKgnn, ?_⟩
  intro ε z
  have h1 : ‖((D.R j (D.J ρ ε h - h) a b z : ℝ) : ℂ)‖
      ≤ ∑ i, ∑ c, ∑ d, Kg i c d *
        ‖truncDiff D ρ ε h i c d (Work.Diff.STE.D.tMapFun (I := I) (M := M) D i j z)‖ := by
    rw [hid ε z]
    refine (norm_sum_le _ _).trans ?_
    refine Finset.sum_le_sum fun i _ => ?_
    refine (norm_sum_le _ _).trans ?_
    refine Finset.sum_le_sum fun c _ => ?_
    refine (norm_sum_le _ _).trans ?_
    refine Finset.sum_le_sum fun d _ => ?_
    exact (norm_mul_le _ _).trans
      (mul_le_mul_of_nonneg_right (hKgb i c d z) (norm_nonneg _))
  simpa using h1

/-- **The components of `J ρ ε h - h` converge uniformly to `0`.**  If the periodised truncation
defects converge uniformly to `0` (the conclusion of `truncDiff_tendsto_uniform`), then so does
every chart component of the difference `J ρ ε h - h`. -/
lemma R_J_sub_sup_tendsto (j : ι₀) (a b : Fin (Module.finrank ℝ E))
    (hTD : ∀ (i : ι₀) (c d : Fin (Module.finrank ℝ E)), ∀ δ : ℝ, 0 < δ →
      ∀ᶠ ε in nhdsWithin (0 : ℝ) (Set.Ioi 0), ∀ y : Fin (Module.finrank ℝ E) → ℝ,
        ‖truncDiff D ρ ε h i c d y‖ ≤ δ) :
    ∀ δ : ℝ, 0 < δ → ∀ᶠ ε in nhdsWithin (0 : ℝ) (Set.Ioi 0),
      ∀ z : Fin (Module.finrank ℝ E) → ℝ, ‖D.R j (D.J ρ ε h - h) a b z‖ ≤ δ := by
  obtain ⟨K, hKnn, hKb⟩ := R_J_sub_sup_le (I := I) (M := M) D ρ h j a b
  intro δ hδ
  set Ktot : ℝ := ∑ i, ∑ c, ∑ d, K i c d with hKtot
  have hKtotnn : 0 ≤ Ktot :=
    Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun c _ =>
      Finset.sum_nonneg fun d _ => hKnn i c d
  set δ' : ℝ := δ / (Ktot + 1) with hδ'def
  have hδ'pos : 0 < δ' := div_pos hδ (by linarith)
  have hδ'le : Ktot * δ' ≤ δ := by
    rw [hδ'def, mul_div_assoc']
    rw [div_le_iff₀ (by linarith : (0:ℝ) < Ktot + 1)]
    linarith
  have hev : ∀ᶠ ε in nhdsWithin (0 : ℝ) (Set.Ioi 0),
      ∀ (i : ι₀) (c d : Fin (Module.finrank ℝ E)) (y : Fin (Module.finrank ℝ E) → ℝ),
        ‖truncDiff D ρ ε h i c d y‖ ≤ δ' := by
    rw [Filter.eventually_all]
    intro i
    rw [Filter.eventually_all]
    intro c
    rw [Filter.eventually_all]
    intro d
    exact hTD i c d δ' hδ'pos
  filter_upwards [hev] with ε hε
  intro z
  refine (hKb ε z).trans ?_
  have hsum : (∑ i, ∑ c, ∑ d, K i c d *
      ‖truncDiff D ρ ε h i c d (Work.Diff.STE.D.tMapFun (I := I) (M := M) D i j z)‖)
      ≤ Ktot * δ' := by
    calc (∑ i, ∑ c, ∑ d, K i c d *
          ‖truncDiff D ρ ε h i c d (Work.Diff.STE.D.tMapFun (I := I) (M := M) D i j z)‖)
        ≤ ∑ i, ∑ c, ∑ d, K i c d * δ' := by
          refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun c _ =>
            Finset.sum_le_sum fun d _ => ?_
          exact mul_le_mul_of_nonneg_left (hε i c d _) (hKnn i c d)
      _ = Ktot * δ' := by rw [hKtot]; simp only [Finset.sum_mul]
  exact hsum.trans hδ'le

end SupBound

section Endgame

open Work.Diff.STE.B3

variable (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀)
  (ρ : (Fin (Module.finrank ℝ E) → ℝ) → ℝ)
  (h : Bil (I := I) (M := M))

/-- A smooth coefficient composed with the chart transition is smooth: the transition is only
smooth on the open set `goodSet`, which contains the support of the coefficient. -/
lemma contDiff_comp_tMapFun (i j : ι₀) (G : (Fin (Module.finrank ℝ E) → ℝ) → ℂ)
    (hG : ContDiff ℝ (⊤ : ℕ∞) G)
    (hGgood : tsupport G ⊆ Work.Diff.STE.D.goodSet (I := I) (M := M) D i j)
    (u : (Fin (Module.finrank ℝ E) → ℝ) → ℂ) (hu : ContDiff ℝ (⊤ : ℕ∞) u) :
    ContDiff ℝ (⊤ : ℕ∞)
      (fun z => G z * u (Work.Diff.STE.D.tMapFun (I := I) (M := M) D i j z)) := by
  rw [contDiff_iff_contDiffAt]
  intro z
  by_cases hz : z ∈ tsupport G
  · have hT : ContDiffAt ℝ (⊤ : ℕ∞) (Work.Diff.STE.D.tMapFun (I := I) (M := M) D i j) z :=
      ((goodSet_smooth_noT2 (I := I) (M := M) D i j).2.1).contDiffAt
        ((goodSet_smooth_noT2 (I := I) (M := M) D i j).1.mem_nhds (hGgood hz))
    exact (hG.contDiffAt).mul (hu.contDiffAt.comp z hT)
  · have hev : G =ᶠ[𝓝 z] (fun _ => (0 : ℂ)) := notMem_tsupport_iff_eventuallyEq.mp hz
    refine (contDiffAt_const (c := (0 : ℂ))).congr_of_eventuallyEq ?_
    filter_upwards [hev] with w hw
    rw [hw, zero_mul]

/-- `STruncR ρ ε f` is smooth when `f` is a smooth function supported in the open cube. -/
lemma contDiff_STruncR (f : (Fin (Module.finrank ℝ E) → ℝ) → ℝ)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hfsupp : Function.support f ⊆ Set.pi Set.univ
      (fun _ : Fin (Module.finrank ℝ E) => Set.Ioo (-(1 / 2 : ℝ)) (1 / 2)))
    (hρ : ∀ y, ‖ρ y‖ ≤ 1) (ε : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (fun z => Work.Diff.STE.B3Data.STruncR ρ ε f z) := by
  have h1 : ContDiff ℝ (⊤ : ℕ∞)
      (⇑Complex.reCLM ∘ (STruncC ρ ε f : (Fin (Module.finrank ℝ E) → ℝ) → ℂ)) :=
    (Complex.reCLM.contDiff).comp (STruncC_contDiff_periodic ρ hρ ε f hf hfsupp).1
  have h2 : ContDiff ℝ (⊤ : ℕ∞) (fun z => (STruncC ρ ε f z).re) := by
    convert h1 using 1
    funext z
    rfl
  simpa only [Work.Diff.STE.B3Data.STruncR, STruncC, Complex.ofReal_re] using h2

/-- **The chart components of `J ρ ε h - h` are smooth** whenever the chart components of `h`
are (and `ε > 0`, i.e. for every real `ε`). -/
lemma R_J_sub_contDiff (hsm : ∀ i c d, ContDiff ℝ (⊤ : ℕ∞) (D.R i h c d))
    (hρ : ∀ y : Fin (Module.finrank ℝ E) → ℝ, ‖ρ y‖ ≤ 1)
    (j : ι₀) (a b : Fin (Module.finrank ℝ E)) (ε : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (D.R j (D.J ρ ε h - h) a b) := by
  obtain ⟨G, hGsm, hGsupp, hGcomp, hGgood, hGzeta, hGle, hid⟩ :=
    R_J_sub_expansion (I := I) (M := M) D ρ h j a b
  have hsum : ContDiff ℝ (⊤ : ℕ∞) (fun z => ∑ i, ∑ c, ∑ d, G i c d z *
      truncDiff D ρ ε h i c d (Work.Diff.STE.D.tMapFun (I := I) (M := M) D i j z)) := by
    refine ContDiff.sum fun i _ => ContDiff.sum fun c _ => ContDiff.sum fun d _ => ?_
    exact contDiff_comp_tMapFun D i j (G i c d) (hGsm i c d) (hGgood i c d) _
      ((truncDiff_contDiff_periodic D ρ hρ ε h hsm i c d).1)
  have hre0 : ContDiff ℝ (⊤ : ℕ∞) (⇑Complex.reCLM ∘ (fun z => ∑ i, ∑ c, ∑ d, G i c d z *
      truncDiff D ρ ε h i c d (Work.Diff.STE.D.tMapFun (I := I) (M := M) D i j z))) :=
    (Complex.reCLM.contDiff).comp hsum
  have hre : ContDiff ℝ (⊤ : ℕ∞) (fun z => (∑ i, ∑ c, ∑ d, G i c d z *
      truncDiff D ρ ε h i c d (Work.Diff.STE.D.tMapFun (I := I) (M := M) D i j z)).re) := by
    convert hre0 using 1
    funext z
    rfl
  convert hre using 1
  funext z
  have hz := hid ε z
  rw [← hz, Complex.ofReal_re]

/-- `R j` is additive in the section. -/
lemma R_sub (X Y : Bil (I := I) (M := M)) (j : ι₀) (a b : Fin (Module.finrank ℝ E)) :
    D.R j (X - Y) a b = D.R j X a b - D.R j Y a b := by
  funext z
  simp only [Work.Diff.STE.B3Data.R, Work.Diff.STE.B3Data.mat, Pi.sub_apply, sub_apply]
  ring

/-- The chart components of `J ρ ε h` are smooth whenever those of `h` are. -/
lemma R_J_contDiff (hsm : ∀ i c d, ContDiff ℝ (⊤ : ℕ∞) (D.R i h c d))
    (hρ : ∀ y : Fin (Module.finrank ℝ E) → ℝ, ‖ρ y‖ ≤ 1)
    (j : ι₀) (a b : Fin (Module.finrank ℝ E)) (ε : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (D.R j (D.J ρ ε h) a b) := by
  have hJeq : D.J ρ ε h = ∑ i : ι₀, D.Rstar i (truncComp D ρ ε h i) := by
    rw [Work.Diff.STE.B3Data.J]
    refine Finset.sum_congr rfl fun i _ => ?_
    congr 1
  rw [hJeq]
  have hpt : ∀ z, D.R j (∑ i : ι₀, D.Rstar i (truncComp D ρ ε h i)) a b z
      = ∑ i : ι₀, D.R j (D.Rstar i (truncComp D ρ ε h i)) a b z := fun z => by
    simp only [Work.Diff.STE.B3Data.R, Work.Diff.STE.B3Data.mat, Finset.sum_apply, sum_apply,
      Finset.mul_sum]
  have hsum0 : ContDiff ℝ (⊤ : ℕ∞)
      (fun z => ∑ i : ι₀, D.R j (D.Rstar i (truncComp D ρ ε h i)) a b z) := by
    refine ContDiff.sum fun i _ => ?_
    obtain ⟨G, hGsm, hGsupp, hGcomp, hGgood, hid⟩ :=
      bump_expansion_fixed D i j a b (closure_Omega_goodSet D i j)
        ((goodSet_smooth_noT2 D i j).1) (fun c d => (goodSet_smooth_noT2 D i j).2.2 a b c d)
    have hsm2 : ∀ c d, ContDiff ℝ (⊤ : ℕ∞)
        (fun z => ((truncComp D ρ ε h i c d z : ℝ) : ℂ)) := fun c d =>
     Complex.ofRealCLM.contDiff.comp (contDiff_STruncR ρ (D.R i h c d) (hsm i c d)
        (R_support_cube D h i c d) hρ ε)
    have hsum : ContDiff ℝ (⊤ : ℕ∞) (fun z => ∑ c, ∑ d, G c d z *
        ((truncComp D ρ ε h i c d
          (Work.Diff.STE.D.tMapFun (I := I) (M := M) D i j z) : ℝ) : ℂ)) := by
      refine ContDiff.sum fun c _ => ContDiff.sum fun d _ => ?_
      exact contDiff_comp_tMapFun D i j (G c d) (hGsm c d) (hGgood c d) _ (hsm2 c d)
    have hre0 : ContDiff ℝ (⊤ : ℕ∞) (⇑Complex.reCLM ∘ (fun z => ∑ c, ∑ d, G c d z *
        ((truncComp D ρ ε h i c d
          (Work.Diff.STE.D.tMapFun (I := I) (M := M) D i j z) : ℝ) : ℂ))) :=
      (Complex.reCLM.contDiff).comp hsum
    have hre : ContDiff ℝ (⊤ : ℕ∞) (fun z => (∑ c, ∑ d, G c d z *
        ((truncComp D ρ ε h i c d
          (Work.Diff.STE.D.tMapFun (I := I) (M := M) D i j z) : ℝ) : ℂ)).re) := by
      convert hre0 using 1
      funext z
      rfl
    convert hre using 1
    funext z
    have hz := hid (truncComp D ρ ε h i) z
    rw [← hz, Complex.ofReal_re]
  convert hsum0 using 1
  funext z
  exact hpt z

/-- The flat chart component of a section with smooth chart components is integrable. -/
lemma integrable_R_of_contDiff (Z : Bil (I := I) (M := M)) (j : ι₀)
    (a b : Fin (Module.finrank ℝ E)) (hZ : ContDiff ℝ (⊤ : ℕ∞) (D.R j Z a b)) :
    MeasureTheory.Integrable (fun z => ((D.R j Z a b z : ℝ) : ℂ)) := by
  refine Continuous.integrable_of_hasCompactSupport
    (Complex.ofRealCLM.continuous.comp hZ.continuous) ?_
  show IsCompact (tsupport (fun z => ((D.R j Z a b z : ℝ) : ℂ)))
  have hsub : tsupport (fun z => ((D.R j Z a b z : ℝ) : ℂ)) ⊆
      Set.pi Set.univ (fun _ : Fin (Module.finrank ℝ E) =>
        Set.Icc (-(1 / 2 : ℝ)) (1 / 2)) := by
    refine (closure_mono ?_).trans
      (closure_minimal (Set.pi_mono fun _ _ => Set.Ioo_subset_Icc_self)
        (isClosed_set_pi fun _ _ => isClosed_Icc))
    intro z hz
    have hz' : D.R j Z a b z ≠ 0 := by
      intro h0
      exact hz (by show ((D.R j Z a b z : ℝ) : ℂ) = 0
                   rw [h0, Complex.ofReal_zero])
    exact D.psi_supp j (Function.mem_support.mpr (fun h0 => hz' (by
      show D.R j Z a b z = 0
      simp only [Work.Diff.STE.B3Data.R, h0, zero_mul])))
  exact (steB3_isCompact_closedCube (ι := Fin (Module.finrank ℝ E))).of_isClosed_subset
    (isClosed_tsupport _) hsub

end Endgame


section Endgame2

open Work.Diff.STE.B3

variable (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀)
  (ρ : (Fin (Module.finrank ℝ E) → ℝ) → ℝ)
  (h : Bil (I := I) (M := M))

/-- The periodisation of a chart component is smooth and `1`-periodic as soon as the component
is. -/
lemma Rper_contDiff_periodic_of_R (Z : Bil (I := I) (M := M)) (j : ι₀)
    (a b : Fin (Module.finrank ℝ E)) (hZ : ContDiff ℝ (⊤ : ℕ∞) (D.R j Z a b)) :
    ContDiff ℝ (⊤ : ℕ∞) (D.Rper j Z a b) ∧ Work.Diff.STE.Periodic1 (D.Rper j Z a b) := by
  have hF : ContDiff ℝ (⊤ : ℕ∞) (fun z => ((D.R j Z a b z : ℝ) : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp hZ
  have hFsupp : Function.support (fun z => ((D.R j Z a b z : ℝ) : ℂ)) ⊆
      Set.pi Set.univ (fun _ : Fin (Module.finrank ℝ E) => Set.Ioo (-(1 / 2 : ℝ)) (1 / 2)) := by
    intro z hz
    have hz' : D.R j Z a b z ≠ 0 := by
      intro h0
      exact hz (by show ((D.R j Z a b z : ℝ) : ℂ) = 0
                   rw [h0, Complex.ofReal_zero])
    exact D.psi_supp j (Function.mem_support.mpr (fun h0 => hz' (by
      show D.R j Z a b z = 0
      simp only [Work.Diff.STE.B3Data.R, h0, zero_mul])))
  have hper := periodization_contDiff_periodic (fun z => ((D.R j Z a b z : ℝ) : ℂ)) hF hFsupp
  refine ⟨?_, ?_⟩
  · change ContDiff ℝ (⊤ : ℕ∞) (fun x : Fin (Module.finrank ℝ E) → ℝ =>
      ∑' m : Fin (Module.finrank ℝ E) → ℤ, ((D.R j Z a b (x + Work.Diff.STE.iVec m) : ℝ) : ℂ))
    exact hper.1
  · change Work.Diff.STE.Periodic1 (fun x : Fin (Module.finrank ℝ E) → ℝ =>
      ∑' m : Fin (Module.finrank ℝ E) → ℤ, ((D.R j Z a b (x + Work.Diff.STE.iVec m) : ℝ) : ℂ))
    exact hper.2.1

/-- The Fourier coefficient of a periodised chart component as an integral over the centred
cube. -/
lemma fourierCoeff_Rper_eq_integral (Z : Bil (I := I) (M := M)) (j : ι₀)
    (a b : Fin (Module.finrank ℝ E)) (m : Fin (Module.finrank ℝ E) → ℤ)
    (hZ : ContDiff ℝ (⊤ : ℕ∞) (D.R j Z a b)) :
    Work.Diff.STE.fourierCoeff (D.Rper j Z a b) m
      = ∫ z, Work.Diff.STE.fourierExp (-m) z * ((D.R j Z a b z : ℝ) : ℂ) := by
  rw [show D.Rper j Z a b = (fun y : Fin (Module.finrank ℝ E) → ℝ =>
      ∑' k : Fin (Module.finrank ℝ E) → ℤ, ((D.R j Z a b (y + Work.Diff.STE.iVec k) : ℝ) : ℂ))
      from rfl]
  rw [Work.Diff.STE.B3.fourierCoeff_periodization _ m
    (fun z hz => D.psi_supp j (Function.mem_support.mpr (fun h0 => hz (by
      show ((D.R j Z a b z : ℝ) : ℂ) = 0
      simp only [Work.Diff.STE.B3Data.R, h0, zero_mul, Complex.ofReal_zero]))))
    (integrable_R_of_contDiff (I := I) (M := M) D Z j a b hZ)]
  have hzero : ∀ z ∉ Work.Diff.STE.B3Data.centreCube (E := E),
      Work.Diff.STE.fourierExp (-m) z * ((D.R j Z a b z : ℝ) : ℂ) = 0 := by
    intro z hz
    have hz' : D.R j Z a b z = 0 := by
      by_contra h0
      exact hz (Set.pi_mono (fun _ _ => Set.Ioo_subset_Ioc_self)
        (D.psi_supp j (Function.mem_support.mpr
          (fun h1 : D.psi j z = 0 => h0 (by
            show D.R j Z a b z = 0
            simp only [Work.Diff.STE.B3Data.R, h1, zero_mul])))))
    rw [hz', Complex.ofReal_zero, mul_zero]
  rw [show (∫ z in Set.pi Set.univ
        (fun _ : Fin (Module.finrank ℝ E) => Set.Ioc (-(1 / 2 : ℝ)) (1 / 2)),
        Work.Diff.STE.fourierExp (-m) z * ((D.R j Z a b z : ℝ) : ℂ))
      = ∫ z, Work.Diff.STE.fourierExp (-m) z * ((D.R j Z a b z : ℝ) : ℂ) from
    MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero hzero]

/-- **The Fourier coefficients are additive in the section**: the coefficient of the difference is
the difference of the coefficients. -/
lemma fourierCoeff_Rper_sub (X Y : Bil (I := I) (M := M)) (j : ι₀)
    (a b : Fin (Module.finrank ℝ E)) (m : Fin (Module.finrank ℝ E) → ℤ)
    (hXY : ContDiff ℝ (⊤ : ℕ∞) (D.R j (X - Y) a b))
    (hX : ContDiff ℝ (⊤ : ℕ∞) (D.R j X a b))
    (hY : ContDiff ℝ (⊤ : ℕ∞) (D.R j Y a b)) :
    Work.Diff.STE.fourierCoeff (D.Rper j (X - Y) a b) m
      = Work.Diff.STE.fourierCoeff (D.Rper j X a b) m
        - Work.Diff.STE.fourierCoeff (D.Rper j Y a b) m := by
  rw [fourierCoeff_Rper_eq_integral (I := I) (M := M) D (X - Y) j a b m hXY,
    fourierCoeff_Rper_eq_integral (I := I) (M := M) D X j a b m hX,
    fourierCoeff_Rper_eq_integral (I := I) (M := M) D Y j a b m hY]
  rw [show (fun z => Work.Diff.STE.fourierExp (-m) z * ((D.R j (X - Y) a b z : ℝ) : ℂ))
      = fun z => Work.Diff.STE.fourierExp (-m) z * ((D.R j X a b z : ℝ) : ℂ)
          - Work.Diff.STE.fourierExp (-m) z * ((D.R j Y a b z : ℝ) : ℂ) from by
    funext z
    simp only [R_sub (I := I) (M := M) D X Y j a b, Pi.sub_apply, Complex.ofReal_sub]
    ring]
  exact MeasureTheory.integral_sub
    (Work.Diff.STE.B3.integrable_fourierExp_mul (-m)
      (integrable_R_of_contDiff (I := I) (M := M) D X j a b hX))
    (Work.Diff.STE.B3.integrable_fourierExp_mul (-m)
      (integrable_R_of_contDiff (I := I) (M := M) D Y j a b hY))

/-- **Uniform bound on the level-`N` Fourier energy of the components of `J ρ ε h - h`.** -/
lemma CSq_N_le (hh : Work.Diff.STE.D.ChartData (I := I) (M := M) h)
    (hρ : ∀ y : Fin (Module.finrank ℝ E) → ℝ, ‖ρ y‖ ≤ 1)
    (j : ι₀) (a b : Fin (Module.finrank ℝ E)) (N : ℕ)
    (hN : Module.finrank ℝ E < 2 * N) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
      Work.Diff.STE.CSq N (Work.Diff.STE.fourierCoeff (D.Rper j (D.J ρ ε h - h) a b)) ≤ C := by
  have hsm : ∀ i c d, ContDiff ℝ (⊤ : ℕ∞) (D.R i h c d) := fun i c d =>
    R_contDiff_of_chartData (I := I) (M := M) D hh i c d
  obtain ⟨C₁, hC₁, hC₁b⟩ :=
    Work.Diff.STE.B3.BNorm_J_le_uniform (I := I) (M := M) D ρ hρ N hN
  -- the level-`N` family of the components of `h` is summable
  have hsh : Summable (fun m : Fin (Module.finrank ℝ E) → ℤ =>
      Work.Diff.STE.wt m ^ N *
        ‖Work.Diff.STE.fourierCoeff (D.Rper j h a b) m‖ ^ 2) :=
    summable_weighted_fourierCoeff_of_contDiff _ (Rper_contDiff_periodic_of_R D h j a b
      (hsm j a b)).1 (Rper_contDiff_periodic_of_R D h j a b (hsm j a b)).2 N
  -- the coefficient identity
  have hcoeff : ∀ (ε : ℝ) (m : Fin (Module.finrank ℝ E) → ℤ),
      Work.Diff.STE.fourierCoeff (D.Rper j (D.J ρ ε h - h) a b) m
        = Work.Diff.STE.fourierCoeff (D.Rper j (D.J ρ ε h) a b) m
          - Work.Diff.STE.fourierCoeff (D.Rper j h a b) m := by
    intro ε m
    exact fourierCoeff_Rper_sub (I := I) (M := M) D (D.J ρ ε h) h j a b m
      (R_J_sub_contDiff (I := I) (M := M) D ρ h hsm hρ j a b ε)
      (R_J_contDiff (I := I) (M := M) D ρ h hsm hρ j a b ε)
      (hsm j a b)
  refine ⟨2 * (C₁ * D.BNorm N h) + 2 * D.BNorm N h, ?_, fun ε hε hε1 => ?_⟩
  · have hBN : 0 ≤ D.BNorm N h :=
      Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun c _ =>
        Finset.sum_nonneg fun d _ => CSq_nonneg N _
    have h1 : 0 ≤ C₁ * D.BNorm N h := mul_nonneg hC₁ hBN
    linarith
  · -- the level-`N` summability of the pieces
    have hJper := Rper_contDiff_periodic_of_R (I := I) (M := M) D (D.J ρ ε h) j a b
      (R_J_contDiff (I := I) (M := M) D ρ h hsm hρ j a b ε)
    have hsJ : Summable (fun m : Fin (Module.finrank ℝ E) → ℤ =>
        Work.Diff.STE.wt m ^ N *
          ‖Work.Diff.STE.fourierCoeff (D.Rper j (D.J ρ ε h) a b) m‖ ^ 2) :=
      summable_weighted_fourierCoeff_of_contDiff _ hJper.1 hJper.2 N
    set Fj : (Fin (Module.finrank ℝ E) → ℤ) → ℝ := fun m =>
      2 * (Work.Diff.STE.wt m ^ N *
        ‖Work.Diff.STE.fourierCoeff (D.Rper j (D.J ρ ε h) a b) m‖ ^ 2) with hFj
    set Fh : (Fin (Module.finrank ℝ E) → ℤ) → ℝ := fun m =>
      2 * (Work.Diff.STE.wt m ^ N *
        ‖Work.Diff.STE.fourierCoeff (D.Rper j h a b) m‖ ^ 2) with hFh
    have hsJ' : Summable Fj := hsJ.mul_left 2
    have hsh' : Summable Fh := hsh.mul_left 2
    have hsum2 : Summable (fun m => Fj m + Fh m) := hsJ'.add hsh'
    have hpt : ∀ m : Fin (Module.finrank ℝ E) → ℤ,
        Work.Diff.STE.wt m ^ N *
            ‖Work.Diff.STE.fourierCoeff (D.Rper j (D.J ρ ε h - h) a b) m‖ ^ 2
          ≤ Fj m + Fh m := by
      intro m
      rw [hcoeff ε m]
      have h2 := norm_sub_le (Work.Diff.STE.fourierCoeff (D.Rper j (D.J ρ ε h) a b) m)
        (Work.Diff.STE.fourierCoeff (D.Rper j h a b) m)
      have h3 : ‖Work.Diff.STE.fourierCoeff (D.Rper j (D.J ρ ε h) a b) m
          - Work.Diff.STE.fourierCoeff (D.Rper j h a b) m‖ ^ 2
          ≤ (‖Work.Diff.STE.fourierCoeff (D.Rper j (D.J ρ ε h) a b) m‖
            + ‖Work.Diff.STE.fourierCoeff (D.Rper j h a b) m‖) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) h2 2
      have hA := norm_nonneg (Work.Diff.STE.fourierCoeff (D.Rper j (D.J ρ ε h) a b) m)
      have hB := norm_nonneg (Work.Diff.STE.fourierCoeff (D.Rper j h a b) m)
      have hsq : ‖Work.Diff.STE.fourierCoeff (D.Rper j (D.J ρ ε h) a b) m
          - Work.Diff.STE.fourierCoeff (D.Rper j h a b) m‖ ^ 2
          ≤ 2 * ‖Work.Diff.STE.fourierCoeff (D.Rper j (D.J ρ ε h) a b) m‖ ^ 2
            + 2 * ‖Work.Diff.STE.fourierCoeff (D.Rper j h a b) m‖ ^ 2 := by
        nlinarith [sq_nonneg (‖Work.Diff.STE.fourierCoeff (D.Rper j (D.J ρ ε h) a b) m‖
            - ‖Work.Diff.STE.fourierCoeff (D.Rper j h a b) m‖)]
      have hw : 0 ≤ Work.Diff.STE.wt m ^ N :=
        pow_nonneg (le_of_lt (Work.Diff.STE.wt_pos m)) N
      simp only [hFj, hFh]
      calc Work.Diff.STE.wt m ^ N *
            ‖Work.Diff.STE.fourierCoeff (D.Rper j (D.J ρ ε h) a b) m
              - Work.Diff.STE.fourierCoeff (D.Rper j h a b) m‖ ^ 2
          ≤ Work.Diff.STE.wt m ^ N *
              (2 * ‖Work.Diff.STE.fourierCoeff (D.Rper j (D.J ρ ε h) a b) m‖ ^ 2
                + 2 * ‖Work.Diff.STE.fourierCoeff (D.Rper j h a b) m‖ ^ 2) :=
            mul_le_mul_of_nonneg_left hsq hw
        _ = 2 * (Work.Diff.STE.wt m ^ N *
              ‖Work.Diff.STE.fourierCoeff (D.Rper j (D.J ρ ε h) a b) m‖ ^ 2)
            + 2 * (Work.Diff.STE.wt m ^ N *
              ‖Work.Diff.STE.fourierCoeff (D.Rper j h a b) m‖ ^ 2) := by ring
    have hsum1 : Summable (fun m : Fin (Module.finrank ℝ E) → ℤ =>
        Work.Diff.STE.wt m ^ N *
          ‖Work.Diff.STE.fourierCoeff (D.Rper j (D.J ρ ε h - h) a b) m‖ ^ 2) :=
      Summable.of_nonneg_of_le
        (fun m => mul_nonneg (pow_nonneg (le_of_lt (Work.Diff.STE.wt_pos m)) N) (sq_nonneg _))
        hpt hsum2
    have hle := Summable.tsum_le_tsum hpt hsum1 hsum2
    have hsplit : (∑' m : Fin (Module.finrank ℝ E) → ℤ, (Fj m + Fh m))
        = 2 * Work.Diff.STE.CSq N (Work.Diff.STE.fourierCoeff (D.Rper j (D.J ρ ε h) a b))
          + 2 * Work.Diff.STE.CSq N (Work.Diff.STE.fourierCoeff (D.Rper j h a b)) := by
      rw [Summable.tsum_add hsJ' hsh']
      congr 1
      · rw [show (∑' m : Fin (Module.finrank ℝ E) → ℤ, Fj m)
            = 2 * (∑' m : Fin (Module.finrank ℝ E) → ℤ,
                (Work.Diff.STE.wt m ^ N *
                  ‖Work.Diff.STE.fourierCoeff (D.Rper j (D.J ρ ε h) a b) m‖ ^ 2)) from
          Summable.tsum_mul_left (2 : ℝ) hsJ]
        rfl
      · rw [show (∑' m : Fin (Module.finrank ℝ E) → ℤ, Fh m)
            = 2 * (∑' m : Fin (Module.finrank ℝ E) → ℤ,
                (Work.Diff.STE.wt m ^ N *
                  ‖Work.Diff.STE.fourierCoeff (D.Rper j h a b) m‖ ^ 2)) from
          Summable.tsum_mul_left (2 : ℝ) hsh]
        rfl
    refine (hle.trans (le_of_eq hsplit)).trans ?_
    have hleJ : Work.Diff.STE.CSq N (Work.Diff.STE.fourierCoeff (D.Rper j (D.J ρ ε h) a b))
        ≤ D.BNorm N (D.J ρ ε h) := by
      change Work.Diff.STE.CSq N (Work.Diff.STE.fourierCoeff (D.Rper j (D.J ρ ε h) a b))
        ≤ ∑ i : ι₀, ∑ c : Fin (Module.finrank ℝ E), ∑ d : Fin (Module.finrank ℝ E),
            Work.Diff.STE.CSq N (Work.Diff.STE.fourierCoeff (D.Rper i (D.J ρ ε h) c d))
      exact sum3_single_le (fun i c d => Work.Diff.STE.CSq N
        (Work.Diff.STE.fourierCoeff (D.Rper i (D.J ρ ε h) c d)))
        (fun i c d => CSq_nonneg N _) j a b
    have hleh : Work.Diff.STE.CSq N (Work.Diff.STE.fourierCoeff (D.Rper j h a b))
        ≤ D.BNorm N h := by
      change Work.Diff.STE.CSq N (Work.Diff.STE.fourierCoeff (D.Rper j h a b))
        ≤ ∑ i : ι₀, ∑ c : Fin (Module.finrank ℝ E), ∑ d : Fin (Module.finrank ℝ E),
            Work.Diff.STE.CSq N (Work.Diff.STE.fourierCoeff (D.Rper i h c d))
      exact sum3_single_le (fun i c d => Work.Diff.STE.CSq N
        (Work.Diff.STE.fourierCoeff (D.Rper i h c d))) (fun i c d => CSq_nonneg N _) j a b
    have hJb := hC₁b ε hε hε1 h hsm
    have h2 : 2 * Work.Diff.STE.CSq N (Work.Diff.STE.fourierCoeff (D.Rper j (D.J ρ ε h) a b))
        ≤ 2 * (C₁ * D.BNorm N h) :=
      (mul_le_mul_of_nonneg_left hleJ (by norm_num)).trans
        (mul_le_mul_of_nonneg_left hJb (by norm_num))
    have h3 : 2 * Work.Diff.STE.CSq N (Work.Diff.STE.fourierCoeff (D.Rper j h a b))
        ≤ 2 * D.BNorm N h := mul_le_mul_of_nonneg_left hleh (by norm_num)
    linarith

end Endgame2

section Endgame3

open Work.Diff.STE.B3

variable (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀)
  (ρ : (Fin (Module.finrank ℝ E) → ℝ) → ℝ)
  (h : Bil (I := I) (M := M))

/-- The centred cube has volume `1`. -/
lemma vol_centreCube :
    (MeasureTheory.volume : MeasureTheory.Measure (Fin (Module.finrank ℝ E) → ℝ))
      (Work.Diff.STE.B3Data.centreCube) = 1 := by
  rw [Work.Diff.STE.B3Data.centreCube, Real.volume_pi_Ioc]
  trans ∏ _i : Fin (Module.finrank ℝ E), (1 : ENNReal)
  · exact Finset.prod_congr rfl (fun i _ => by
      rw [show (1 / 2 - -(1 / 2) : ℝ) = 1 by norm_num, ENNReal.ofReal_one])
  · simp

/-- A chart component whose values are bounded by `δ` has Fourier coefficients bounded by `δ`. -/
lemma fourierCoeff_Rper_le_sup (Z : Bil (I := I) (M := M)) (j : ι₀)
    (a b : Fin (Module.finrank ℝ E)) (hZ : ContDiff ℝ (⊤ : ℕ∞) (D.R j Z a b))
    {δ : ℝ} (hδ : ∀ z, ‖D.R j Z a b z‖ ≤ δ) (m : Fin (Module.finrank ℝ E) → ℤ) :
    ‖Work.Diff.STE.fourierCoeff (D.Rper j Z a b) m‖ ≤ δ := by
  rw [fourierCoeff_Rper_eq_integral (I := I) (M := M) D Z j a b m hZ]
  have hzero : ∀ z ∉ Work.Diff.STE.B3Data.centreCube (E := E),
      Work.Diff.STE.fourierExp (-m) z * ((D.R j Z a b z : ℝ) : ℂ) = 0 := by
    intro z hz
    have hz' : D.R j Z a b z = 0 := by
      by_contra h0
      exact hz (Set.pi_mono (fun _ _ => Set.Ioo_subset_Ioc_self)
        (D.psi_supp j (Function.mem_support.mpr
          (fun h1 : D.psi j z = 0 => h0 (by
            show D.R j Z a b z = 0
            simp only [Work.Diff.STE.B3Data.R, h1, zero_mul])))))
    rw [hz', Complex.ofReal_zero, mul_zero]
  rw [← MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero hzero]
  have hle : ‖∫ z in Work.Diff.STE.B3Data.centreCube (E := E),
      Work.Diff.STE.fourierExp (-m) z * ((D.R j Z a b z : ℝ) : ℂ)‖ ≤ δ := by
    refine (MeasureTheory.norm_setIntegral_le_of_norm_le_const
      (s := Work.Diff.STE.B3Data.centreCube (E := E))
      (f := fun z => Work.Diff.STE.fourierExp (-m) z * ((D.R j Z a b z : ℝ) : ℂ))
      (C := δ) ?_ ?_).trans (le_of_eq ?_)
    · rw [vol_centreCube]
      exact ENNReal.one_lt_top
    · intro z hz
      rw [norm_mul, Work.Diff.STE.norm_fourierExp, one_mul]
      simpa using hδ z
    · rw [MeasureTheory.measureReal_def, vol_centreCube, ENNReal.toReal_one, mul_one]
  exact hle

/-- The frequencies of the box `‖m‖ ≤ R` form a finite set. -/
lemma exists_finset_box (R : ℝ) :
    ∃ s : Finset (Fin (Module.finrank ℝ E) → ℤ),
      ∀ m : Fin (Module.finrank ℝ E) → ℤ, Work.Diff.STE.wt m ≤ R → m ∈ s := by
  refine ⟨Fintype.piFinset (fun _ : Fin (Module.finrank ℝ E) =>
    Finset.Icc (-(⌈R⌉ + 1)) (⌈R⌉ + 1)), fun m hm => ?_⟩
  rw [Fintype.mem_piFinset]
  intro k
  rw [Finset.mem_Icc]
  have h1 : ((m k : ℤ) : ℝ) ^ 2 ≤ R - 1 := by
    have h2 : (Work.Diff.STE.wt m : ℝ) = 1 + ∑ i, ((m i : ℤ) : ℝ) ^ 2 := rfl
    have h3 : ∑ i, ((m i : ℤ) : ℝ) ^ 2 ≤ R - 1 := by
      have := hm
      rw [h2] at this
      linarith
    exact (Finset.single_le_sum (f := fun i : Fin (Module.finrank ℝ E) =>
      ((m i : ℤ) : ℝ) ^ 2) (fun i _ => sq_nonneg _) (Finset.mem_univ k)).trans h3
  have h4 : |((m k : ℤ) : ℝ)| ≤ ((⌈R⌉ + 1 : ℤ) : ℝ) := by
    have h5 : |((m k : ℤ) : ℝ)| ≤ ((m k : ℤ) : ℝ) ^ 2 + 1 := by
      rcases le_total 0 ((m k : ℤ) : ℝ) with hx | hx
      · rw [abs_of_nonneg hx]
        nlinarith [sq_nonneg (((m k : ℤ) : ℝ) - 1)]
      · rw [abs_of_nonpos hx]
        nlinarith [sq_nonneg (((m k : ℤ) : ℝ) + 1)]
    have h6 : ((m k : ℤ) : ℝ) ^ 2 + 1 ≤ R := by linarith
    have h7 : R ≤ ((⌈R⌉ + 1 : ℤ) : ℝ) := by
      have h8 := Int.le_ceil R
      push_cast
      linarith
    linarith
  obtain ⟨hlo, hhi⟩ := abs_le.mp h4
  constructor
  · have : -(((⌈R⌉ + 1 : ℤ)) : ℝ) ≤ ((m k : ℤ) : ℝ) := by linarith
    exact_mod_cast this
  · have : ((m k : ℤ) : ℝ) ≤ (((⌈R⌉ + 1 : ℤ)) : ℝ) := by linarith
    exact_mod_cast this

end Endgame3

section Squeeze

open Work.Diff.STE.B3

variable (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀)
  (ρ : (Fin (Module.finrank ℝ E) → ℝ) → ℝ)
  (h : Bil (I := I) (M := M))

/-- **The squeeze**: the level-`k` Fourier energy of the components of `J ρ ε h - h` tends to `0`
as `ε → 0⁺`, provided the components converge *uniformly* to `0` and the next level is uniformly
bounded. -/
lemma CSq_k_tendsto (hh : Work.Diff.STE.D.ChartData (I := I) (M := M) h)
    (hρ : ∀ y : Fin (Module.finrank ℝ E) → ℝ, ‖ρ y‖ ≤ 1)
    (j : ι₀) (a b : Fin (Module.finrank ℝ E)) (k : ℕ)
    (hσ : ∀ δ : ℝ, 0 < δ → ∀ᶠ ε in nhdsWithin (0 : ℝ) (Set.Ioi 0),
      ∀ z : Fin (Module.finrank ℝ E) → ℝ, ‖D.R j (D.J ρ ε h - h) a b z‖ ≤ δ) :
    Filter.Tendsto (fun ε => Work.Diff.STE.CSq k
        (Work.Diff.STE.fourierCoeff (D.Rper j (D.J ρ ε h - h) a b)))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
  set r : ℕ := Module.finrank ℝ E + 1 with hr
  have h2r : Module.finrank ℝ E < 2 * r := by omega
  have hN : Module.finrank ℝ E < 2 * (k + 2 * r) := by omega
  have hsm : ∀ i c d, ContDiff ℝ (⊤ : ℕ∞) (D.R i h c d) := fun i c d =>
    R_contDiff_of_chartData (I := I) (M := M) D hh i c d
  obtain ⟨C, hC, hCb⟩ := CSq_N_le (I := I) (M := M) D ρ h hh hρ j a b (k + 2 * r) hN
  rw [tendsto_order]
  constructor
  · intro β hβ
    filter_upwards with ε
    exact lt_of_lt_of_le hβ (CSq_nonneg k _)
  · intro β hβ
    -- the frequency box
    obtain ⟨s, hs⟩ := exists_finset_box (E := E) (max 1 (4 * C / β + 1))
    set R : ℝ := max 1 (4 * C / β + 1) with hRdef
    have hR1 : 1 ≤ R := le_max_left _ _
    set S : ℝ := ∑ m ∈ s, Work.Diff.STE.wt m ^ k with hSdef
    have hSnn : 0 ≤ S :=
      Finset.sum_nonneg fun m _ => pow_nonneg (le_of_lt (Work.Diff.STE.wt_pos m)) k
    set δ₀ : ℝ := min 1 (β / (4 * (S + 1))) with hδ₀def
    have hSp : (0 : ℝ) < 4 * (S + 1) := by linarith
    have hδ₀pos : 0 < δ₀ := lt_min one_pos (div_pos hβ hSp)
    have hδ₀le : δ₀ ≤ β / (4 * (S + 1)) := min_le_right _ _
    have hδ₀le1 : δ₀ ≤ 1 := min_le_left _ _
    have hε1 : ∀ᶠ ε in nhdsWithin (0 : ℝ) (Set.Ioi 0), ε ≤ 1 := by
      filter_upwards [nhdsWithin_le_nhds (IsOpen.mem_nhds isOpen_Iio (by norm_num : (0:ℝ) < 1))]
        with ε hε
      exact le_of_lt hε
    have hpos : ∀ᶠ ε in nhdsWithin (0 : ℝ) (Set.Ioi 0), (0:ℝ) < ε := self_mem_nhdsWithin
    filter_upwards [hσ δ₀ hδ₀pos, hε1, hpos] with ε hσε hε1' hposε
    have hcoef : ∀ m : Fin (Module.finrank ℝ E) → ℤ,
        ‖Work.Diff.STE.fourierCoeff (D.Rper j (D.J ρ ε h - h) a b) m‖ ≤ δ₀ := fun m =>
      fourierCoeff_Rper_le_sup (I := I) (M := M) D (D.J ρ ε h - h) j a b
        (R_J_sub_contDiff (I := I) (M := M) D ρ h hsm hρ j a b ε) hσε m
    have hCN : Work.Diff.STE.CSq (k + 2 * r)
        (Work.Diff.STE.fourierCoeff (D.Rper j (D.J ρ ε h - h) a b)) ≤ C :=
      hCb ε hposε hε1'
    have hper := Rper_contDiff_periodic_of_R (I := I) (M := M) D (D.J ρ ε h - h) j a b
      (R_J_sub_contDiff (I := I) (M := M) D ρ h hsm hρ j a b ε)
    have hsumk : Summable (fun m : Fin (Module.finrank ℝ E) → ℤ =>
        Work.Diff.STE.wt m ^ k *
          ‖Work.Diff.STE.fourierCoeff (D.Rper j (D.J ρ ε h - h) a b) m‖ ^ 2) :=
      summable_weighted_fourierCoeff_of_contDiff _ hper.1 hper.2 k
    have hsumN : Summable (fun m : Fin (Module.finrank ℝ E) → ℤ =>
        Work.Diff.STE.wt m ^ (k + 2 * r) *
          ‖Work.Diff.STE.fourierCoeff (D.Rper j (D.J ρ ε h - h) a b) m‖ ^ 2) :=
      summable_weighted_fourierCoeff_of_contDiff _ hper.1 hper.2 (k + 2 * r)
    set g : (Fin (Module.finrank ℝ E) → ℤ) → ℝ := fun m =>
      Work.Diff.STE.wt m ^ k *
        ‖Work.Diff.STE.fourierCoeff (D.Rper j (D.J ρ ε h - h) a b) m‖ ^ 2 with hg
    have hgnn : ∀ m, 0 ≤ g m := fun m =>
      mul_nonneg (pow_nonneg (le_of_lt (Work.Diff.STE.wt_pos m)) k) (sq_nonneg _)
    have hsumg : Summable g := hsumk
    have hsplit := Summable.sum_add_tsum_compl (s := s) hsumg
    -- the low part
    have hlow : (∑ m ∈ s, g m) ≤ β / 4 := by
      calc (∑ m ∈ s, g m) ≤ ∑ m ∈ s, Work.Diff.STE.wt m ^ k * δ₀ ^ 2 := by
            refine Finset.sum_le_sum fun m _ => ?_
            rw [hg]
            refine mul_le_mul_of_nonneg_left ?_
              (pow_nonneg (le_of_lt (Work.Diff.STE.wt_pos m)) k)
            exact pow_le_pow_left₀ (norm_nonneg _) (hcoef m) 2
        _ = S * δ₀ ^ 2 := by rw [hSdef, Finset.sum_mul]
        _ ≤ β / 4 := by
          have h1 : δ₀ ^ 2 ≤ δ₀ := by nlinarith [hδ₀pos, hδ₀le1]
          have h2 : S * δ₀ ≤ S * (β / (4 * (S + 1))) :=
            mul_le_mul_of_nonneg_left hδ₀le hSnn
          have h3 : S * (β / (4 * (S + 1))) ≤ β / 4 := by
            have hSp1 : 0 < S + 1 := by linarith
            rw [show S * (β / (4 * (S + 1))) = (S / (S + 1)) * (β / 4) by
              field_simp]
            have hSS : S / (S + 1) ≤ 1 := (div_le_one hSp1).mpr (by linarith)
            calc (S / (S + 1)) * (β / 4) ≤ 1 * (β / 4) :=
                  mul_le_mul_of_nonneg_right hSS (by linarith [hβ])
              _ = β / 4 := one_mul _
          nlinarith [hSnn, hδ₀pos, h1, h2, h3]
    -- the high part
    have hA : (∑' m : ↑((↑s : Set (Fin (Module.finrank ℝ E) → ℤ))ᶜ), g m.1)
        = ∑' m, ((↑s : Set (Fin (Module.finrank ℝ E) → ℤ))ᶜ).indicator g m :=
      tsum_subtype _ _
    have hB : (∑' m : {m : Fin (Module.finrank ℝ E) → ℤ // R < Work.Diff.STE.wt m}, g m.1)
        = ∑' m, ({m : Fin (Module.finrank ℝ E) → ℤ | R < Work.Diff.STE.wt m}).indicator g m :=
      tsum_subtype _ _
    have htail1 : (∑' m : ↑((↑s : Set (Fin (Module.finrank ℝ E) → ℤ))ᶜ), g m.1)
        ≤ ∑' m : {m : Fin (Module.finrank ℝ E) → ℤ // R < Work.Diff.STE.wt m}, g m.1 := by
      rw [hA, hB]
      refine Summable.tsum_le_tsum (fun m => ?_) (hsumg.indicator _) (hsumg.indicator _)
      by_cases hm : m ∈ (↑s : Set (Fin (Module.finrank ℝ E) → ℤ))
      · rw [Set.indicator_of_notMem
          (s := (↑s : Set (Fin (Module.finrank ℝ E) → ℤ))ᶜ) (fun h => h hm)]
        exact Set.indicator_nonneg (s := {m : Fin (Module.finrank ℝ E) → ℤ |
          R < Work.Diff.STE.wt m}) (fun a _ => hgnn a) m
      · have hm' : m ∈ {m : Fin (Module.finrank ℝ E) → ℤ | R < Work.Diff.STE.wt m} := by
          by_contra h2
          exact hm (hs m (not_lt.mp h2))
        rw [Set.indicator_of_mem (s := (↑s : Set (Fin (Module.finrank ℝ E) → ℤ))ᶜ)
            (fun h => hm h),
          Set.indicator_of_mem
            (s := {m : Fin (Module.finrank ℝ E) → ℤ | R < Work.Diff.STE.wt m}) hm']
    have htail2 := CSq_tail_le (ι := Fin (Module.finrank ℝ E)) k r R hR1
      (Work.Diff.STE.fourierCoeff (D.Rper j (D.J ρ ε h - h) a b)) hsumN
    have htail3 : R ^ (-(2 * (r : ℤ))) * C ≤ β / 4 := by
      have hRpos : 0 < R := lt_of_lt_of_le one_pos hR1
      have h1 : R ^ (-(2 * (r : ℤ))) ≤ R⁻¹ := by
        rw [zpow_neg]
        refine inv_anti₀ hRpos ?_
        calc R = R ^ 1 := (pow_one R).symm
          _ ≤ R ^ (2 * r) := pow_le_pow_right₀ hR1 (by omega)
      have h2 : R⁻¹ ≤ (4 * C / β + 1)⁻¹ := by
        refine inv_anti₀ (by positivity) ?_
        exact le_max_right _ _
      have hden : (0 : ℝ) < 4 * C / β + 1 := by
        have : 0 ≤ 4 * C / β := div_nonneg (by linarith [hC]) hβ.le
        linarith
      have h3 : C / (4 * C / β + 1) ≤ β / 4 := by
        rw [div_le_iff₀ hden]
        have h4 : β / 4 * (4 * C / β + 1) = C + β / 4 := by
          field_simp
        rw [h4]
        linarith [hβ]
      calc R ^ (-(2 * (r : ℤ))) * C ≤ R⁻¹ * C := mul_le_mul_of_nonneg_right h1 hC
        _ ≤ (4 * C / β + 1)⁻¹ * C := mul_le_mul_of_nonneg_right h2 hC
        _ = C / (4 * C / β + 1) := by rw [div_eq_mul_inv]; ring
        _ ≤ β / 4 := h3
    have hCSq : Work.Diff.STE.CSq k
        (Work.Diff.STE.fourierCoeff (D.Rper j (D.J ρ ε h - h) a b))
        = (∑ m ∈ s, g m)
          + ∑' m : ↑((↑s : Set (Fin (Module.finrank ℝ E) → ℤ))ᶜ), g m.1 := hsplit.symm
    rw [hCSq]
    have h5 : R ^ (-(2 * (r : ℤ))) * Work.Diff.STE.CSq (k + 2 * r)
        (Work.Diff.STE.fourierCoeff (D.Rper j (D.J ρ ε h - h) a b)) ≤ β / 4 :=
      (mul_le_mul_of_nonneg_left hCN
        (zpow_nonneg (le_of_lt (lt_of_lt_of_le one_pos hR1)) _)).trans htail3
    have h4 : (∑' m : ↑((↑s : Set (Fin (Module.finrank ℝ E) → ℤ))ᶜ), g m.1) ≤ β / 4 :=
      htail1.trans (htail2.trans h5)
    linarith [hlow, h4]

end Squeeze

theorem J_tendsto
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ((⊤ : ENat) : WithTop ENat) M]
    [T2Space M] [I.Boundaryless] [CompactSpace M]
    {ι₀ : Type*} [Fintype ι₀] {g₀ : SMet I M}
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀)
    (ρ : (Fin (Module.finrank ℝ E) → ℝ) → ℝ) (hρ : ∀ y, ‖ρ y‖ ≤ 1)
    (hρ0 : ∀ y : Fin (Module.finrank ℝ E) → ℝ, 2 < ∑ i, (y i) ^ 2 → ρ y = 0)
    (hρs : ContDiff ℝ (⊤ : ℕ∞) ρ) (hρ1 : ρ 0 = 1)
    (k : ℕ) (h : Work.Diff.STE.Bil (I := I) (M := M)) (hh : Work.Diff.STE.D.ChartData (I := I) (M := M) h) :
    Filter.Tendsto (fun ε => D.BNorm k (D.J ρ ε h - h)) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
  have hsm : ∀ i c d, ContDiff ℝ (⊤ : ℕ∞) (D.R i h c d) := fun i c d =>
    R_contDiff_of_chartData (I := I) (M := M) D hh i c d
  have hρc : ContinuousAt ρ 0 := hρs.continuous.continuousAt
  have hTD : ∀ (i : ι₀) (c d : Fin (Module.finrank ℝ E)), ∀ δ : ℝ, 0 < δ →
      ∀ᶠ ε in nhdsWithin (0 : ℝ) (Set.Ioi 0),
        ∀ y : Fin (Module.finrank ℝ E) → ℝ, ‖Work.Diff.STE.B3.truncDiff D ρ ε h i c d y‖ ≤ δ := by
    intro i c d δ hδ
    filter_upwards [Work.Diff.STE.Lead.truncDiff_tendsto_uniform ρ hρ0 hρ hρc hρ1
      (D.R i h c d) (hsm i c d) (Work.Diff.STE.B3.R_support_cube D h i c d) δ hδ] with ε hε
    intro y
    have h1 : ‖Work.Diff.STE.B3.truncDiff D ρ ε h i c d y‖
        = |(STruncC ρ ε (D.R i h c d) y - D.Rper i h c d y).re| := by
      rw [Work.Diff.STE.B3.truncDiff_apply, Complex.norm_def, Complex.normSq_ofReal, ← sq]
      exact Real.sqrt_sq_eq_abs _
    refine (le_of_eq h1).trans ?_
    refine (Complex.abs_re_le_norm _).trans ?_
    exact hε y
  have hj : ∀ (j : ι₀) (a b : Fin (Module.finrank ℝ E)),
      Filter.Tendsto (fun ε => Work.Diff.STE.CSq k
        (Work.Diff.STE.fourierCoeff (D.Rper j (D.J ρ ε h - h) a b)))
        (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := fun j a b =>
    CSq_k_tendsto (I := I) (M := M) D ρ h hh hρ j a b k
      (R_J_sub_sup_tendsto (I := I) (M := M) D ρ h j a b hTD)
  have h1 : (fun ε => D.BNorm k (D.J ρ ε h - h))
      = fun ε => ∑ j : ι₀, ∑ a : Fin (Module.finrank ℝ E),
          ∑ b : Fin (Module.finrank ℝ E),
            Work.Diff.STE.CSq k (Work.Diff.STE.fourierCoeff (D.Rper j (D.J ρ ε h - h) a b)) :=
    rfl
  rw [h1]
  have h2 := tendsto_finset_sum Finset.univ (fun j _ => tendsto_finset_sum Finset.univ
    (fun a _ => tendsto_finset_sum Finset.univ (fun b _ => hj j a b)))
  simpa using h2

end Work.Diff.STE.Lead
