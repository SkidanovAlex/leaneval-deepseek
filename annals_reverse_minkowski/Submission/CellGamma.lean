import Mathlib
import Submission.CellContinuity
import Submission.Boundary
import Submission.Intrinsic
import Submission.StableCompact
import Submission.MatrixTopology

open Module Real MeasureTheory Filter
open scoped Real BigOperators InnerProductSpace Topology
set_option autoImplicit false
set_option maxHeartbeats 1000000

/-!
# (P3.2) continuity of the Voronoi-cell Gaussian mass along convergent basis matrices

With the pointwise stabilization of cell membership (`CellContinuity.cell_mem_eventual`,
P3.1c) and the discreteness/countability instances for `latticeOfMatrix A`
(`CellContinuity.latticeOfMatrix_discrete` / `_countable`, which make the tie set null via
`volume_tieSet_zero_of_matrix`), dominated convergence yields the continuity of

    ℒ ↦ γ_s(V(ℒ))    (γ_s := GaussianMeasure.gammaMass s, V := Voronoi.voronoi)

along matrices converging in the (product) matrix topology, at any nonsingular limit:

`gammaMass_tendsto_of_matrix_tendsto` — for `s > 0`, `det A₀ ≠ 0` and `Aₙ → A₀`
(entrywise), `γ_s(V(latticeOfMatrix Aₙ)) → γ_s(V(latticeOfMatrix A₀))`.

This is the analytic content of [B-ii]/P3.2: together with P2 compactness
(`StableCompact.stable_lattices_in_compact_set`) it yields that the infimum of
`γ_{1/t_m}(V(·))` over the stable full-rank rank-`m` lattices is attained at a stable
lattice, the global-minimizer input of the rank-`m` induction step
(`MainStable.gamma_stable_of_two_le`).

The proof runs entirely on the *matrix* side (no typeclass transport is needed):
the integrands are `Fₙ := 1_{V(latticeOfMatrix Aₙ)} · g`, `g := gaussianF (1/s)` (the
`γ_s = ∫ gaussianF (1/s)` bridge of `Boundary.gammaMass_eq_gaussianF_integral`), dominated
on the whole space by the integrable Gaussian; for a.e. `z` (`z` off the tie set of the
limit, which is null by `volume_tieSet_zero_of_matrix`), membership stabilizes eventually
(`cell_mem_eventual`), so `Fₙ(z) → F₀(z)`.
-/

noncomputable section
namespace Submission.CellGamma

variable {m : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin m)
local notation "VC" => Submission.Voronoi.voronoi

open Submission.CellContinuity
open Submission.StableCompact
open Submission.LatticeParam


open Submission.CellContinuity
open Submission.StableCompact
open Submission.LatticeParam

theorem gammaMass_tendsto_of_matrix_tendsto (s : ℝ) (hs : 0 < s)
    (A₀ : Matrix (Fin m) (Fin m) ℝ) (hdet₀ : A₀.det ≠ 0)
    (An : ℕ → Matrix (Fin m) (Fin m) ℝ)
    (hconv : Filter.Tendsto An Filter.atTop (𝓝 A₀)) :
    Filter.Tendsto (fun n : ℕ =>
        Submission.GaussianMeasure.gammaMass s (VC (latticeOfMatrix (An n))))
      Filter.atTop
      (𝓝 (Submission.GaussianMeasure.gammaMass s (VC (latticeOfMatrix A₀)))) := by
  classical
  have hu : 0 < 1 / s := one_div_pos.mpr hs
  let g : E → ℝ := fun z => Submission.Cvp.gaussianF (1 / s) z
  let F : ℕ → E → ℝ := fun n => (VC (latticeOfMatrix (An n))).indicator g
  let f : E → ℝ := (VC (latticeOfMatrix A₀)).indicator g
  have hgpos : ∀ x : E, 0 ≤ g x := by
    intro x
    exact Submission.Cvp.gaussianF_nonneg (1 / s) (le_of_lt hu) x
  have hgcont : Continuous g := by
    dsimp [g, Submission.Cvp.gaussianF]
    fun_prop
  have hgmeas : Measurable g := hgcont.measurable
  have hg_int : Integrable g := by
    simpa [g] using (Submission.Cvp.gaussianF_integrable (1 / s) hu)
  have hVmeas (A : Matrix (Fin m) (Fin m) ℝ) : MeasurableSet (VC (latticeOfMatrix A)) :=
    Submission.Voronoi.voronoi_measurable (latticeOfMatrix A)
  -- γ s (V A) = ∫ (V A).indicator g
  have hγ_int (A : Matrix (Fin m) (Fin m) ℝ) :
      Submission.GaussianMeasure.gammaMass s (VC (latticeOfMatrix A)) =
        ∫ x : E, (VC (latticeOfMatrix A)).indicator g x := by
    have hb : Submission.GaussianMeasure.gammaMass s (VC (latticeOfMatrix A)) =
        ∫ x in (VC (latticeOfMatrix A)), g x := by
      simpa [g] using (Submission.Boundary.gammaMass_eq_gaussianF_integral (m := m) s hs
        (VC (latticeOfMatrix A)))
    calc
      Submission.GaussianMeasure.gammaMass s (VC (latticeOfMatrix A)) =
          ∫ x in (VC (latticeOfMatrix A)), g x := hb
      _ = ∫ x : E, (VC (latticeOfMatrix A)).indicator g x := by
        exact (MeasureTheory.integral_indicator (hVmeas A)).symm
  -- measurability of the integrands
  have hFmeas : ∀ n : ℕ, AEStronglyMeasurable (F n) := by
    intro n
    dsimp [F]
    exact (Measurable.indicator hgmeas (hVmeas (An n))).aestronglyMeasurable
  -- domination: |F n z| ≤ g z pointwise
  have hbound_pt (n : ℕ) (z : E) : ‖F n z‖ ≤ g z := by
    dsimp [F]
    by_cases hz : z ∈ VC (latticeOfMatrix (An n))
    · have h1 : (VC (latticeOfMatrix (An n))).indicator g z = g z := by simp [Set.indicator, hz]
      rw [h1]
      rw [abs_of_nonneg (hgpos z)]
    · have h1 : (VC (latticeOfMatrix (An n))).indicator g z = 0 := by simp [Set.indicator, hz]
      rw [h1]
      simpa using hgpos z
  have h_bound : ∀ n : ℕ, ∀ᵐ z ∂(volume : Measure E), ‖F n z‖ ≤ g z := fun n =>
    Filter.Eventually.of_forall (hbound_pt n)
  -- pointwise convergence off the tie set
  have hpt (z : E) (hz : z ∉ Submission.VoronoiContinuity.tieSet (latticeOfMatrix A₀)) :
      Filter.Tendsto (fun n : ℕ => F n z) Filter.atTop (𝓝 (f z)) := by
    have hev : ∀ᶠ n in Filter.atTop,
        (z ∈ VC (latticeOfMatrix (An n)) ↔ z ∈ VC (latticeOfMatrix A₀)) :=
      cell_mem_eventual A₀ hdet₀ z hz An hconv
    have hconst : (fun n : ℕ => F n z) =ᶠ[Filter.atTop] fun _ : ℕ => f z := by
      refine hev.mono ?_
      intro n hn
      by_cases hz0 : z ∈ VC (latticeOfMatrix A₀)
      · have hzn : z ∈ VC (latticeOfMatrix (An n)) := hn.mpr hz0
        dsimp [F, f]
        simp [Set.indicator, hz0, hzn]
      · have hzn : z ∉ VC (latticeOfMatrix (An n)) := fun hzV => hz0 (hn.mp hzV)
        dsimp [F, f]
        simp [Set.indicator, hz0, hzn]
    exact Filter.Tendsto.congr' hconst.symm (tendsto_const_nhds (x := f z))
  have hlim_ae : ∀ᵐ z ∂(volume : Measure E),
      Filter.Tendsto (fun n : ℕ => F n z) Filter.atTop (𝓝 (f z)) := by
    rw [MeasureTheory.ae_iff]
    refine MeasureTheory.Measure.mono_null ?_ (volume_tieSet_zero_of_matrix A₀ hdet₀)
    intro z hz
    by_contra hzt
    exact hz (hpt z hzt)
  -- dominated convergence
  have hD : Filter.Tendsto (fun n : ℕ => ∫ x : E, F n x) Filter.atTop
      (𝓝 (∫ x : E, f x)) := by
    exact MeasureTheory.tendsto_integral_of_dominated_convergence (μ := (volume : Measure E))
      (F := F) (f := f) (bound := g) hFmeas hg_int h_bound hlim_ae
  have hfun_eq : (fun n : ℕ =>
        Submission.GaussianMeasure.gammaMass s (VC (latticeOfMatrix (An n)))) =
      fun n : ℕ => ∫ x : E, F n x := by
    funext n
    simpa [F] using hγ_int (An n)
  have hfγ : Submission.GaussianMeasure.gammaMass s (VC (latticeOfMatrix A₀)) = ∫ x : E, f x := by
    simpa [f] using hγ_int A₀
  rw [hfun_eq, hfγ]
  exact hD


/-- **Stable-family γ-continuity (transport form).**  If the lattices are represented by
basis matrices (`latticeOfMatrix Aₙ = ℒₙ`, `latticeOfMatrix A₀ = ℒ₀`) and `Aₙ → A₀` with
`det A₀ ≠ 0`, then the Voronoi-cell Gaussian masses converge:
`γ_s(V(ℒₙ)) → γ_s(V(ℒ₀))`.  This is the P3.2 statement in the form used by the
global-minimizer argument over stable lattices (cells transported through the equal
submodules by `Intrinsic.voronoi_congr`). -/
theorem gammaMass_tendsto_of_lattices (s : ℝ) (hs : 0 < s)
    (A₀ : Matrix (Fin m) (Fin m) ℝ) (hdet₀ : A₀.det ≠ 0)
    (ℒ₀ : Submodule ℤ (EuclideanSpace ℝ (Fin m))) (hℒ₀ : latticeOfMatrix A₀ = ℒ₀)
    (An : ℕ → Matrix (Fin m) (Fin m) ℝ)
    (ℒₙ : ℕ → Submodule ℤ (EuclideanSpace ℝ (Fin m)))
    (hℒₙ : ∀ n : ℕ, latticeOfMatrix (An n) = ℒₙ n)
    (hconv : Filter.Tendsto An Filter.atTop (𝓝 A₀)) :
    Filter.Tendsto (fun n : ℕ =>
        Submission.GaussianMeasure.gammaMass s (VC (ℒₙ n))) Filter.atTop
      (𝓝 (Submission.GaussianMeasure.gammaMass s (VC ℒ₀))) := by
  classical
  have h1 := gammaMass_tendsto_of_matrix_tendsto (m := m) s hs A₀ hdet₀ An hconv
  have hfun : (fun n : ℕ =>
        Submission.GaussianMeasure.gammaMass s (VC (latticeOfMatrix (An n)))) =
      fun n : ℕ => Submission.GaussianMeasure.gammaMass s (VC (ℒₙ n)) := by
    funext n
    exact congrArg (fun S : Set (EuclideanSpace ℝ (Fin m)) => Submission.GaussianMeasure.gammaMass s S)
      (Submission.Intrinsic.voronoi_congr (latticeOfMatrix (An n)) (ℒₙ n) (hℒₙ n))
  have hval : Submission.GaussianMeasure.gammaMass s (VC (latticeOfMatrix A₀)) =
      Submission.GaussianMeasure.gammaMass s (VC ℒ₀) := by
    exact congrArg (fun S : Set (EuclideanSpace ℝ (Fin m)) => Submission.GaussianMeasure.gammaMass s S)
      (Submission.Intrinsic.voronoi_congr (latticeOfMatrix A₀) ℒ₀ hℒ₀)
  rw [hfun, hval] at h1
  exact h1

/-- Any sequence of stable full-rank lattices admits representatives in one fixed compact
set `K` of basis matrices (`K` from `StableCompact.stable_lattices_in_compact_set`).  This
is the input of the subsequential compactness argument for the existence of a global
γ-minimizer over the stable family. -/
theorem stable_seq_repr_in_compact (ℒₙ : ℕ → Submodule ℤ (EuclideanSpace ℝ (Fin m)))
    (hDT : ∀ n : ℕ, DiscreteTopology (ℒₙ n))
    (hSt : ∀ n : ℕ, Submission.StableLattices.Stable (ℒₙ n))
    (hfin : ∀ n : ℕ, Module.finrank ℤ (ℒₙ n) = m) :
    ∃ (K : Set (Matrix (Fin m) (Fin m) ℝ)), IsCompact K ∧
      ∃ An : ℕ → Matrix (Fin m) (Fin m) ℝ,
        ∀ n : ℕ, An n ∈ K ∧ latticeOfMatrix (An n) = ℒₙ n := by
  classical
  rcases (Submission.StableCompact.stable_lattices_in_compact_set (m := m)) with ⟨K, hKc, hKrep⟩
  have hrep (n : ℕ) : ∃ A : Matrix (Fin m) (Fin m) ℝ, A ∈ K ∧ latticeOfMatrix A = ℒₙ n := by
    haveI : DiscreteTopology (ℒₙ n) := hDT n
    exact hKrep (ℒₙ n) (hSt n) (hfin n)
  refine ⟨K, hKc, ⟨fun n => Classical.choose (hrep n), fun n => Classical.choose_spec (hrep n)⟩⟩

/-- The δ-box around `A₀` (all entries within δ) is a neighborhood of `A₀` in the matrix
product topology.  (Reusable input of the deferred topological-continuity version of P3.2,
which needs the countably-generated-filter dominated convergence over `𝓝 A₀`.) -/
lemma box_mem_nhds (A₀ : Matrix (Fin m) (Fin m) ℝ) {δ : ℝ} (hδ : 0 < δ) :
    {A : Matrix (Fin m) (Fin m) ℝ | ∀ j i : Fin m, |A j i - A₀ j i| < δ} ∈ 𝓝 A₀ := by
  classical
  change ∀ᶠ A in 𝓝 A₀, ∀ j i : Fin m, |A j i - A₀ j i| < δ
  rw [Filter.eventually_all]
  intro j
  rw [Filter.eventually_all]
  intro i
  have hc : ContinuousAt (fun A : Matrix (Fin m) (Fin m) ℝ => A j i) A₀ :=
    (continuous_apply_apply j i).continuousAt
  have hb : Metric.ball (A₀ j i) δ ∈ 𝓝 (A₀ j i) := Metric.ball_mem_nhds (A₀ j i) hδ
  have hmem := hc.preimage_mem_nhds hb
  filter_upwards [hmem] with A hA
  simpa [Real.dist_eq] using hA

theorem continuousAt_gammaMass_of_matrix (s : ℝ) (hs : 0 < s)
    (A₀ : Matrix (Fin m) (Fin m) ℝ) (hdet₀ : A₀.det ≠ 0) :
    ContinuousAt (fun A : Matrix (Fin m) (Fin m) ℝ =>
      Submission.GaussianMeasure.gammaMass s (VC (latticeOfMatrix A))) A₀ := by
  classical
  have hu : 0 < 1 / s := one_div_pos.mpr hs
  let g : E → ℝ := fun z => Submission.Cvp.gaussianF (1 / s) z
  let F : Matrix (Fin m) (Fin m) ℝ → E → ℝ := fun A => (VC (latticeOfMatrix A)).indicator g
  have hgpos : ∀ x : E, 0 ≤ g x := by
    intro x
    exact Submission.Cvp.gaussianF_nonneg (1 / s) (le_of_lt hu) x
  have hgcont : Continuous g := by
    dsimp [g, Submission.Cvp.gaussianF]
    fun_prop
  have hgmeas : Measurable g := hgcont.measurable
  have hg_int : Integrable g := by
    simpa [g] using (Submission.Cvp.gaussianF_integrable (1 / s) hu)
  have hVmeas (A : Matrix (Fin m) (Fin m) ℝ) : MeasurableSet (VC (latticeOfMatrix A)) :=
    Submission.Voronoi.voronoi_measurable (latticeOfMatrix A)
  have hγ_int (A : Matrix (Fin m) (Fin m) ℝ) :
      Submission.GaussianMeasure.gammaMass s (VC (latticeOfMatrix A)) =
        ∫ x : E, (VC (latticeOfMatrix A)).indicator g x := by
    have hb : Submission.GaussianMeasure.gammaMass s (VC (latticeOfMatrix A)) =
        ∫ x in (VC (latticeOfMatrix A)), g x := by
      simpa [g] using (Submission.Boundary.gammaMass_eq_gaussianF_integral (m := m) s hs
        (VC (latticeOfMatrix A)))
    calc
      Submission.GaussianMeasure.gammaMass s (VC (latticeOfMatrix A)) =
          ∫ x in (VC (latticeOfMatrix A)), g x := hb
      _ = ∫ x : E, (VC (latticeOfMatrix A)).indicator g x := by
        exact (MeasureTheory.integral_indicator (hVmeas A)).symm
  -- measurability of the integrands (uniform in A)
  have hFmeasA (A : Matrix (Fin m) (Fin m) ℝ) : AEStronglyMeasurable (F A) := by
    dsimp [F]
    exact (Measurable.indicator hgmeas (hVmeas A)).aestronglyMeasurable
  have hbound_pt (A : Matrix (Fin m) (Fin m) ℝ) (z : E) : ‖F A z‖ ≤ g z := by
    dsimp [F]
    by_cases hz : z ∈ VC (latticeOfMatrix A)
    · have h1 : (VC (latticeOfMatrix A)).indicator g z = g z := by simp [Set.indicator, hz]
      rw [h1]
      rw [abs_of_nonneg (hgpos z)]
    · have h1 : (VC (latticeOfMatrix A)).indicator g z = 0 := by simp [Set.indicator, hz]
      rw [h1]
      simpa using hgpos z
  -- pointwise convergence off the tie set, for the nhds filter
  have hpt (z : E) (hz : z ∉ Submission.VoronoiContinuity.tieSet (latticeOfMatrix A₀)) :
      Filter.Tendsto (fun A : Matrix (Fin m) (Fin m) ℝ => F A z) (𝓝 A₀) (𝓝 (F A₀ z)) := by
    rcases cell_mem_stable A₀ hdet₀ z hz with ⟨δ, hδpos, hstab⟩
    have hboxev : {A : Matrix (Fin m) (Fin m) ℝ | ∀ j i : Fin m, |A j i - A₀ j i| < δ} ∈ 𝓝 A₀ :=
      box_mem_nhds A₀ hδpos
    have hconst : (fun A : Matrix (Fin m) (Fin m) ℝ => F A z) =ᶠ[𝓝 A₀] fun _ : Matrix (Fin m) (Fin m) ℝ => F A₀ z := by
      filter_upwards [hboxev] with A hA
      by_cases hz0 : z ∈ VC (latticeOfMatrix A₀)
      · have hzn : z ∈ VC (latticeOfMatrix A) := (hstab A hA).mpr hz0
        dsimp [F]
        simp [Set.indicator, hz0, hzn]
      · have hzn : z ∉ VC (latticeOfMatrix A) := fun hv => hz0 ((hstab A hA).mp hv)
        dsimp [F]
        simp [Set.indicator, hz0, hzn]
    exact Filter.Tendsto.congr' hconst.symm (tendsto_const_nhds (x := F A₀ z))
  have hlim_ae : ∀ᵐ z ∂(volume : Measure E),
      Filter.Tendsto (fun A : Matrix (Fin m) (Fin m) ℝ => F A z) (𝓝 A₀) (𝓝 (F A₀ z)) := by
    rw [MeasureTheory.ae_iff]
    refine MeasureTheory.Measure.mono_null ?_ (volume_tieSet_zero_of_matrix A₀ hdet₀)
    intro z hz
    by_contra hzt
    exact hz (hpt z hzt)
  -- dominated convergence over the neighborhood filter
  have hD : Filter.Tendsto (fun A : Matrix (Fin m) (Fin m) ℝ => ∫ x : E, F A x)
      (𝓝 A₀) (𝓝 (∫ x : E, F A₀ x)) := by
    refine MeasureTheory.tendsto_integral_filter_of_dominated_convergence (μ := (volume : Measure E))
      (ι := Matrix (Fin m) (Fin m) ℝ) (l := 𝓝 A₀) (F := F) (f := F A₀) (bound := g) ?_ ?_ hg_int hlim_ae
    · exact Filter.Eventually.of_forall hFmeasA
    · exact Filter.Eventually.of_forall (fun A => Filter.Eventually.of_forall (fun z => hbound_pt A z))
  -- convert to the γ-map: γ s (VC(latticeOfMatrix A)) = ∫ F A pointwise
  have hfun_eq : (fun A : Matrix (Fin m) (Fin m) ℝ =>
        Submission.GaussianMeasure.gammaMass s (VC (latticeOfMatrix A))) =
      fun A : Matrix (Fin m) (Fin m) ℝ => ∫ x : E, F A x := by
    funext A
    simpa [F] using hγ_int A
  have hfγ : Submission.GaussianMeasure.gammaMass s (VC (latticeOfMatrix A₀)) = ∫ x : E, F A₀ x := by
    simpa [F] using hγ_int A₀
  have hγcont : Filter.Tendsto (fun A : Matrix (Fin m) (Fin m) ℝ =>
        Submission.GaussianMeasure.gammaMass s (VC (latticeOfMatrix A)))
      (𝓝 A₀) (𝓝 (Submission.GaussianMeasure.gammaMass s (VC (latticeOfMatrix A₀)))) := by
    rw [hfun_eq]
    rw [hfγ]
    exact hD
  exact hγcont
