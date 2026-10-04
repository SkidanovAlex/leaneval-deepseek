/-
# Layer B3: smoothness of the global reconstruction `Gtot`

`Work.Diff.STE.B3.Gtot D h j z a b = ∑ i, Gterm D h j i z a b` is the global reconstruction of the
coordinate-frame chart matrix of a section `h` from the localised components `D.R i h`: each summand

`Gterm D h j i z a b =
  ζ i (pt j z) · (√(dens i (xiMap z)))⁻¹ · ∑_{cd} trCoef a c · trCoef b d · R i h c d (xiMap z)`

is built from `D.R i h`, which is what makes the jet bounds uniform in `h`.

The point of this file is that `Gtot D h j · a b` is `C^∞` on the ball of radius `2 σ j + δ`
(whose image under `pt j` lies in the chart target, `hδt`).  The subtlety is the *junk* issue of the
partial charts: the arguments `xiMap D j i z = coord_i (pt j z)` are only meaningful where
`pt j z` lies in the chart-`i` source, and the extended chart is arbitrary off its source.

The resolution is the *pointwise identity*

`Gterm D h j i z a b = GtermClean D h j i z a b`  (on the whole flat space)

where the clean form

`GtermClean D h j i z a b =
  (ζ i (pt j z)) ^ 2 · ∑_{cd} trCoef a c · trCoef b d · h (pt j z) (e i c) (e i d)`

is manifestly `C^∞` (the second `ζ i` and the whole `xiMap` dependence have been absorbed: on the
support of `ζ i ∘ pt j` the chart-`i` data is genuine, and off it both sides vanish).  Both sides
of the identity vanish when `ζ i (pt j z) = 0`, and when `ζ i (pt j z) ≠ 0` the point `pt j z` lies
in the chart-`i` source with `‖coord_i‖ < σ i` (`B3Data.hζsupp`), so `χ i = 1`, `pt i (xiMap) = pt j z`,
`dens i (xiMap) > 0`, and `R i h c d (xiMap) = ζ i (pt j z) · √(dens i (xiMap)) · h (pt j z) (e i c) (e i d)`.
-/
import Mathlib
import Submission.Work.Diff.STE.B3.CoeffDefs
import Submission.Work.Diff.STE.B3.CompSmooth
import Submission.Work.Diff.STE.B3.R_contDiff_of_chartData
import Submission.Work.Diff.STE.B3.continuousAt_mat_Rstar
import Submission.Work.Diff.STE.B3.BPairSmooth
import Submission.Work.EXT.exists_smooth_ONFrame

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology BigOperators Matrix
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter

namespace Work.Diff.STE.B3

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.unusedSectionVars false

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ((⊤ : ENat) : WithTop ENat) M] [T2Space M] [I.Boundaryless]
  {ι₀ : Type*} [Fintype ι₀] {g₀ : Submission.Diff.SMet I M}

/-- **The clean form of the `i`-th summand of the reconstruction**: the same summand with the
`xiMap`-dependence cancelled (the second factor `ζ i` and the chart matrix of `h` are evaluated at
the *genuine* point `pt j z`).  Unlike `Gterm`, it involves no `xiMap` at all, hence no junk from the
partial charts. -/
def GtermClean (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀)
    (h : Work.Diff.STE.Bil (I := I) (M := M)) (j i : ι₀)
    (z : Fin (Module.finrank ℝ E) → ℝ) (a b : Fin (Module.finrank ℝ E)) : ℝ :=
  (D.ζ i (D.pt j z)) ^ 2 * ∑ c, ∑ d,
    trCoef (I := I) (M := M) D j i z a c * trCoef (I := I) (M := M) D j i z b d
      * h (D.pt j z) (D.e i c (D.pt j z)) (D.e i d (D.pt j z))

/-- Elementary algebra: the cancellation of the factor `√(dens)` and of the linearity of the double
sum, in the form in which it appears in `Gterm_eq_clean`. -/
private lemma mul_inv_mul_sum_mul_eq_sq_mul_sum {Z R : ℝ} (hR : R ≠ 0)
    {ι κ : Type*} [Fintype ι] [Fintype κ] (f : ι → κ → ℝ) (g : ι → κ → ℝ) :
    Z * R⁻¹ * (∑ c, ∑ d, f c d * (Z * R * g c d))
      = Z ^ 2 * (∑ c, ∑ d, f c d * g c d) := by
  have hfac : (∑ c, ∑ d, f c d * (Z * R * g c d))
      = (Z * R) * ∑ c, ∑ d, f c d * g c d := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun c _ => ?_)
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun d _ => by ring)
  rw [hfac]
  calc Z * R⁻¹ * ((Z * R) * ∑ c, ∑ d, f c d * g c d)
      = (Z * Z) * (R⁻¹ * R) * (∑ c, ∑ d, f c d * g c d) := by ring
    _ = (Z * Z) * 1 * (∑ c, ∑ d, f c d * g c d) := by rw [inv_mul_cancel₀ hR]
    _ = Z ^ 2 * (∑ c, ∑ d, f c d * g c d) := by ring

/-- **The pointwise identity `Gterm = GtermClean`.**  Where the weight `ζ i ∘ pt j` vanishes both
sides vanish; where it does not, `pt j z` lies in the chart-`i` source with flat coordinate of norm
`< σ i`, so the cut-off `χ i` is `1`, `pt i (xiMap D j i z) = pt j z`, the density
`dens i (xiMap D j i z)` is positive and the localised component `R i h c d (xiMap D j i z)`
evaluates to `ζ i (pt j z) · √(dens i (xiMap D j i z)) · h (pt j z) (e i c) (e i d)`. -/
lemma Gterm_eq_clean
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀)
    (h : Work.Diff.STE.Bil (I := I) (M := M)) (j i : ι₀)
    (z : Fin (Module.finrank ℝ E) → ℝ) (a b : Fin (Module.finrank ℝ E)) :
    Gterm (I := I) (M := M) D h j i z a b = GtermClean (I := I) (M := M) D h j i z a b := by
  classical
  by_cases hζ : D.ζ i (D.pt j z) = 0
  · simp only [Gterm, GtermClean, hζ, zero_mul, mul_zero, pow_two]
  · obtain ⟨hsrc, hlt⟩ := D.hζsupp i (D.pt j z) hζ
    have hχ : D.χ i (xiMap D j i z) = 1 := by
      rw [xiMap]; exact D.hχ1 i _ (le_of_lt hlt)
    have hpt : D.pt i (xiMap D j i z) = D.pt j z := by
      rw [xiMap]; exact D.pt_coord i hsrc
    have htgt : flatToE (I := I) (D.x₀ i) (xiMap D j i z) ∈ (extChartAt I (D.x₀ i)).target := by
      rw [xiMap, flatToE_coord_cm]
      exact PartialEquiv.map_source (extChartAt I (D.x₀ i)) hsrc
    have hdpos : 0 < D.dens i (xiMap D j i z) := dens_pos_of_mem_target D i htgt
    have hroot : Real.sqrt (D.dens i (xiMap D j i z)) ≠ 0 := (Real.sqrt_pos.mpr hdpos).ne'
    have hRc : ∀ c d : Fin (Module.finrank ℝ E), D.R i h c d (xiMap D j i z)
        = D.ζ i (D.pt j z) * Real.sqrt (D.dens i (xiMap D j i z))
            * h (D.pt j z) (D.e i c (D.pt j z)) (D.e i d (D.pt j z)) := by
      intro c d
      rw [B3Data.R, B3Data.psi, B3Data.mat, hχ, hpt]
      ring
    have hmain : D.ζ i (D.pt j z) * (Real.sqrt (D.dens i (xiMap D j i z)))⁻¹ *
          (∑ c, ∑ d, trCoef (I := I) (M := M) D j i z a c
            * trCoef (I := I) (M := M) D j i z b d * D.R i h c d (xiMap D j i z))
        = (D.ζ i (D.pt j z)) ^ 2 *
          (∑ c, ∑ d, trCoef (I := I) (M := M) D j i z a c
            * trCoef (I := I) (M := M) D j i z b d
            * h (D.pt j z) (D.e i c (D.pt j z)) (D.e i d (D.pt j z))) := by
      have hsum : (∑ c, ∑ d, trCoef (I := I) (M := M) D j i z a c
            * trCoef (I := I) (M := M) D j i z b d * D.R i h c d (xiMap D j i z))
          = ∑ c, ∑ d, trCoef (I := I) (M := M) D j i z a c
              * trCoef (I := I) (M := M) D j i z b d
              * (D.ζ i (D.pt j z) * Real.sqrt (D.dens i (xiMap D j i z))
                * h (D.pt j z) (D.e i c (D.pt j z)) (D.e i d (D.pt j z))) := by
        refine Finset.sum_congr rfl (fun c _ => Finset.sum_congr rfl (fun d _ => ?_))
        rw [hRc]
      rw [hsum]
      exact mul_inv_mul_sum_mul_eq_sq_mul_sum hroot
        (fun c d => trCoef (I := I) (M := M) D j i z a c
          * trCoef (I := I) (M := M) D j i z b d)
        (fun c d => h (D.pt j z) (D.e i c (D.pt j z)) (D.e i d (D.pt j z)))
    simpa only [Gterm, GtermClean] using hmain

/-- `D.pt j z` lies in the source of the chart at `x₀ j` as soon as the flat coordinate of `z` lies
in the chart target (the `≤ 2 σ j` version is `B3Data.pt_mem_chart`). -/
lemma pt_mem_chart' (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (j : ι₀)
    {z : Fin (Module.finrank ℝ E) → ℝ}
    (hz : flatToE (I := I) (D.x₀ j) z ∈ (extChartAt I (D.x₀ j)).target) :
    D.pt j z ∈ (chartAt H (D.x₀ j)).source := by
  have h : D.pt j z ∈ (extChartAt I (D.x₀ j)).source := (extChartAt I (D.x₀ j)).map_target hz
  rwa [extChartAt_source] at h

/-- **The change-of-frame coefficients are smooth** at every `z` whose flat coordinate in the chart
at `x₀ j` lies in the chart target (this is the smoothness of the metric pairing of the
coordinate-frame field of chart `j` with the global frame field `e i c`). -/
lemma contDiffAt_trCoef
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (j i : ι₀)
    (a c : Fin (Module.finrank ℝ E)) {z : Fin (Module.finrank ℝ E) → ℝ}
    (hz : flatToE (I := I) (D.x₀ j) z ∈ (extChartAt I (D.x₀ j)).target) :
    ContDiffAt ℝ (⊤ : ℕ∞)
      (fun y : Fin (Module.finrank ℝ E) → ℝ => trCoef (I := I) (M := M) D j i y a c) z := by
  have hpt := D.contMDiffAt_pt j hz
  have hp : D.pt j z ∈ (chartAt H (D.x₀ j)).source := pt_mem_chart' D j hz
  have hX : Work.Diff.EXT.SmoothFieldAt I M
      (fun q : M => Submission.Geodesic.frameVector (I := I) (D.x₀ j) q
        (Work.Diff.EXT.bB (E := E) a)) (D.pt j z) :=
    smoothFieldAt_frameVector' (I := I) (D.x₀ j) (Work.Diff.EXT.bB (E := E) a) hp
  have hpair := Work.EXT.ONF.pairing g₀ (D.pt j z) hX ((D.hesm i c).contMDiffAt)
  have hcomp := hpair.comp z hpt
  exact contMDiffAt_iff_contDiffAt.mp hcomp

/-- **The chart matrix of `h` in the global frame `e i` is smooth along `pt j`** at every `z` whose
flat coordinate in the chart at `x₀ j` lies in the chart target: `h` is a smooth section of the
bundle of bilinear forms (`section_contMDiffAt_of_chartData`) and `e i c`, `e i d` are globally
smooth fields. -/
lemma contDiffAt_bilin_pt
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀)
    (h : Work.Diff.STE.Bil (I := I) (M := M))
    (hsmooth : Work.Diff.STE.D.ChartData (I := I) (M := M) h)
    (j i : ι₀) (c d : Fin (Module.finrank ℝ E)) {z : Fin (Module.finrank ℝ E) → ℝ}
    (hz : flatToE (I := I) (D.x₀ j) z ∈ (extChartAt I (D.x₀ j)).target) :
    ContDiffAt ℝ (⊤ : ℕ∞)
      (fun y : Fin (Module.finrank ℝ E) → ℝ =>
        h (D.pt j y) (D.e i c (D.pt j y)) (D.e i d (D.pt j y))) z := by
  have hpt := D.contMDiffAt_pt j hz
  have hsec := section_contMDiffAt_of_chartData hsmooth (D.pt j z)
  have hψ := hsec.contMDiffWithinAt (s := univ)
  have hv : ContMDiffWithinAt I (I.prod 𝓘(ℝ, E)) (⊤ : ℕ∞) (T% (D.e i c)) univ (D.pt j z) :=
    (D.hesm i c).contMDiffAt.contMDiffWithinAt
  have hw : ContMDiffWithinAt I (I.prod 𝓘(ℝ, E)) (⊤ : ℕ∞) (T% (D.e i d)) univ (D.pt j z) :=
    (D.hesm i d).contMDiffAt.contMDiffWithinAt
  have hres := hψ.clm_bundle_apply₂ (F₁ := E) (F₂ := E) hv hw
  simp only [contMDiffWithinAt_totalSpace] at hres
  have h2 : ContMDiffAt I 𝓘(ℝ, ℝ) (⊤ : ℕ∞)
      (fun x : M => h x (D.e i c x) (D.e i d x)) (D.pt j z) :=
    contMDiffWithinAt_univ.mp hres.2
  exact contMDiffAt_iff_contDiffAt.mp (h2.comp z hpt)

/-- **The clean summand is smooth** at every `z` whose flat coordinate in the chart at `x₀ j` lies
in the chart target.  All the factors — `ζ i ∘ pt j`, the change-of-frame coefficients `trCoef` and
the chart matrix of `h` in the frame `e i` — are smooth there. -/
lemma contDiffAt_GtermClean
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀)
    (h : Work.Diff.STE.Bil (I := I) (M := M))
    (hsmooth : Work.Diff.STE.D.ChartData (I := I) (M := M) h)
    (j i : ι₀) (a b : Fin (Module.finrank ℝ E)) {z : Fin (Module.finrank ℝ E) → ℝ}
    (hz : flatToE (I := I) (D.x₀ j) z ∈ (extChartAt I (D.x₀ j)).target) :
    ContDiffAt ℝ (⊤ : ℕ∞)
      (fun y : Fin (Module.finrank ℝ E) → ℝ => GtermClean (I := I) (M := M) D h j i y a b) z := by
  have hζ : ContDiffAt ℝ (⊤ : ℕ∞)
      (fun y : Fin (Module.finrank ℝ E) → ℝ => D.ζ i (D.pt j y)) z :=
    contMDiffAt_iff_contDiffAt.mp (((D.hζsm i).contMDiffAt).comp z (D.contMDiffAt_pt j hz))
  have hζ2 : ContDiffAt ℝ (⊤ : ℕ∞) (fun y => (D.ζ i (D.pt j y)) ^ 2) z := hζ.pow 2
  have hterm : ∀ c d : Fin (Module.finrank ℝ E), ContDiffAt ℝ (⊤ : ℕ∞)
      (fun y : Fin (Module.finrank ℝ E) → ℝ =>
        trCoef (I := I) (M := M) D j i y a c * trCoef (I := I) (M := M) D j i y b d
          * h (D.pt j y) (D.e i c (D.pt j y)) (D.e i d (D.pt j y))) z :=
    fun c d => ((contDiffAt_trCoef D j i a c hz).mul (contDiffAt_trCoef D j i b d hz)).mul
      (contDiffAt_bilin_pt D h hsmooth j i c d hz)
  have hsum : ContDiffAt ℝ (⊤ : ℕ∞)
      (fun y : Fin (Module.finrank ℝ E) → ℝ =>
        ∑ c, ∑ d, trCoef (I := I) (M := M) D j i y a c * trCoef (I := I) (M := M) D j i y b d
          * h (D.pt j y) (D.e i c (D.pt j y)) (D.e i d (D.pt j y))) z :=
    ContDiffAt.sum (s := Finset.univ)
      (fun c _ => ContDiffAt.sum (s := Finset.univ) (fun d _ => hterm c d))
  simpa only [GtermClean] using hζ2.mul hsum

theorem Gtot_contDiffOn
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ((⊤ : ENat) : WithTop ENat) M] [T2Space M] [I.Boundaryless]
    {ι₀ : Type*} [Fintype ι₀] {g₀ : Submission.Diff.SMet I M}
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (j : ι₀) (δ : ℝ) (hδ : 0 < δ)
    (hδt : ∀ (z : Fin (Module.finrank ℝ E) → ℝ), ‖z‖ ≤ 2 * D.σ j + δ →
      Work.Diff.STE.flatToE (I := I) (D.x₀ j) z ∈ (extChartAt I (D.x₀ j)).target) :
    ∀ (h : Work.Diff.STE.Bil (I := I) (M := M))
      (hsmooth : Work.Diff.STE.D.ChartData (I := I) (M := M) h) (a b : Fin (Module.finrank ℝ E)),
      ContDiffOn ℝ (⊤ : ℕ∞)
        (fun y : Fin (Module.finrank ℝ E) → ℝ =>
          Work.Diff.STE.B3.Gtot (I := I) (M := M) D h j y a b)
        (Metric.ball 0 (2 * D.σ j + δ)) := by
  intro h hsmooth a b y hy
  have hy' : ‖y‖ ≤ 2 * D.σ j + δ := by
    have hlt : ‖y‖ < 2 * D.σ j + δ := by
      have hb := Metric.mem_ball.mp hy
      rwa [dist_eq_norm, sub_zero] at hb
    linarith
  have hyt : Work.Diff.STE.flatToE (I := I) (D.x₀ j) y ∈ (extChartAt I (D.x₀ j)).target :=
    hδt y hy'
  refine (contDiffWithinAt_iff_contDiffAt ?_).mpr ?_
  · exact Metric.isOpen_ball.mem_nhds hy
  · have heq : (fun z : Fin (Module.finrank ℝ E) → ℝ => Gtot (I := I) (M := M) D h j z a b)
        = fun z => ∑ i : ι₀, GtermClean (I := I) (M := M) D h j i z a b := by
      funext z
      simp only [Gtot, Gterm_eq_clean]
    rw [heq]
    exact ContDiffAt.sum (s := Finset.univ)
      (fun i _ => contDiffAt_GtermClean D h hsmooth j i a b hyt)

end Work.Diff.STE.B3
