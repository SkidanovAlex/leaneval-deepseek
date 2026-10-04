import Mathlib
import Submission.Work.Diff.STE.B3.Comp
import Submission.Work.Diff.STE.B3.continuousAt_mat_Rstar
import Submission.Work.Diff.STE.B3.Rstar_R_eq_zeta_sq_free
import Submission.Work.Diff.STE.B3.dens_bound_sigma
import Submission.Work.Diff.STE.B3.BPairDefs
import Submission.Work.Diff.STE.B3.Rstar_apply

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Layer B3: continuity of the chart matrix of a section on the support of the cut-off

`D.mat j h a b z = h (pt j z) (e_j a (pt j z)) (e_j b (pt j z))` is the chart matrix of a bilinear
form section `h` in the `g₀`-orthonormal frame `e j` of the chart at `x₀ j`.

The target of this file is the statement that this chart matrix is continuous on the set where the
cut-off `χ j` of chart `j` does not vanish.  This is the *localised* set: the cut-off vanishes off a
neighbourhood of the chart, and on its support the chart is genuine in the sense that the flat
coordinate parametrisation `pt j` lands in the chart target — but the chart matrix alone is not
*defined* by a smooth construction, it is an evaluation of the (arbitrary) section `h`.

**The reduction.**  The only smoothness input about `h` is that the localised components
`R i h a b = ψ i · √(dens i) · mat i h a b` are smooth for every chart `i` (hypothesis `hsm`).
Since `Σ_i ζ_i ^ 2 = 1`, at every point `p` there is a chart `i` with `ζ i p ≠ 0`; and on
`{ζ i ≠ 0}` the *reconstruction identity* `Σ_i R_i^* R_i = id` (`Rstar_R_eq_zeta_sq_free`) inverts
the localised component (the weight and the square root of the density cancel):

`h p X Y = (ζ i p)⁻¹ · (√(dens i (coord i p)))⁻¹ · Σ_{ab} ⟪X, e_i a p⟫ ⟪Y, e_i b p⟫ · R i h a b (coord i p)`.

This is `Work.Diff.STE.B3.bil_eq_inv_zeta_sum` below.  Its right-hand side is a product of
continuous functions of `p` near a point `p₀` with `ζ i p₀ ≠ 0` (`ζ i` is smooth and nonzero there,
the flat coordinate `coord i` is continuous on the chart source, the density is continuous and
positive on the chart target, the metric pairings of smooth fields are continuous, and `R i h a b`
is continuous by hypothesis).  Hence `p ↦ h p (e j a p) (e j b p)` is continuous at every point of
`M`, and composing with the parametrisation `z ↦ pt j z` — continuous at `z₀` because `z₀` lies in
the topological support of `χ j`, which `hχtsup` maps into the chart target — gives the claim.
-/

noncomputable section

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology BigOperators
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter

namespace Work.Diff.STE.B3

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ((⊤ : ENat) : WithTop ENat) M]
  {ι₀ : Type*} [Fintype ι₀] {g₀ : Submission.Diff.SMet I M}

/-- Elementary algebra: if `(A * B⁻¹) * S = A ^ 2 * N` with `A ≠ 0` and `B ≠ 0`, then
`A⁻¹ * B⁻¹ * S = N`.  This is the cancellation of the weight `ζ i p` and of the square root of the
volume density `√(dens i)` in the pointwise inversion of the reconstruction identity. -/
private lemma inv_zeta_dens_cancel {A B S N : ℝ} (hA : A ≠ 0) (hB : B ≠ 0)
    (h : (A * B⁻¹) * S = A ^ 2 * N) : A⁻¹ * B⁻¹ * S = N := by
  have h1 : S = A * B * N := by
    have h2 : (A * B⁻¹) * (A * B * N) = A ^ 2 * N := by
      field_simp
    exact mul_left_cancel₀ (mul_ne_zero hA (inv_ne_zero hB)) (h.trans h2.symm)
  rw [h1]
  calc A⁻¹ * B⁻¹ * (A * B * N) = (A⁻¹ * A) * (B⁻¹ * B) * N := by ring
    _ = N := by rw [inv_mul_cancel₀ hA, inv_mul_cancel₀ hB]; ring

/-- **Pointwise inversion of the reconstruction identity.**  At a point `p` where the weight `ζ i`
of the chart `i` does not vanish, the value of a bilinear form `h` on two vectors `X`, `Y` is the
(weighted) double sum of the chart-`i` components `R i h` against the coefficients of `X`, `Y` in
the frame `e i`.

Indeed `hζsupp` puts `p` in the chart source of `x₀ i` with `‖coord i p‖ < σ i`, so the cut-off
`χ i` equals `1` at `coord i p`, the frame `e i` is `g₀`-orthonormal at `p`, the density is positive
there, and `Σ_i R_i^* R_i = id` (`Rstar_R_eq_zeta_sq_free`) specialises to the stated identity
after cancelling the weight and the square root of the density.

This is the `I.Boundaryless`-free form of the auxiliary lemma of
`Work.Diff.STE.B3.mat_eq_inv_zeta_sum`, with a general pair of vectors `X`, `Y`. -/
lemma bil_eq_inv_zeta_sum (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀)
    (h : Work.Diff.STE.Bil (I := I) (M := M)) (i : ι₀) (p : M)
    (X Y : TangentSpace I p) (hζ : D.ζ i p ≠ 0) :
    h p X Y
      = (D.ζ i p)⁻¹
        * (Real.sqrt (D.dens i (Work.Diff.STE.coord (I := I) (D.x₀ i) p)))⁻¹
        * ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
            g₀.inner p X (D.e i a p) * g₀.inner p Y (D.e i b p)
              * D.R i h a b (Work.Diff.STE.coord (I := I) (D.x₀ i) p) := by
  obtain ⟨hsrc, hlt⟩ := D.hζsupp i p hζ
  have h2 : ‖Work.Diff.STE.coord (I := I) (D.x₀ i) p‖ ≤ 2 * D.σ i := by
    have hσ := D.hσ i; linarith
  -- the density is positive at the flat coordinate of `p`
  have htgt : Work.Diff.STE.flatToE (I := I) (D.x₀ i) (Work.Diff.STE.coord (I := I) (D.x₀ i) p)
      ∈ (extChartAt I (D.x₀ i)).target := D.htarget i _ h2
  have hdens : 0 < D.dens i (Work.Diff.STE.coord (I := I) (D.x₀ i) p) :=
    dens_pos_of_mem_target D i htgt
  have hB : Real.sqrt (D.dens i (Work.Diff.STE.coord (I := I) (D.x₀ i) p)) ≠ 0 :=
    (Real.sqrt_pos.mpr hdens).ne'
  -- the cut-off is `1` on the `σ`-ball, where `ζ i` lives
  have hchi : D.χ i (Work.Diff.STE.coord (I := I) (D.x₀ i) p) = 1 :=
    D.hχ1 i _ (le_of_lt hlt)
  -- evaluate the reconstruction of the localised component: this is `ζ i ^ 2 * h`
  have hR := Rstar_R_eq_zeta_sq_free D h i p X Y
  have hRa := Rstar_apply D i (fun (a b : Fin (Module.finrank ℝ E))
      (z : Fin (Module.finrank ℝ E) → ℝ) => D.R i h a b z) p X Y
  have hcomb := hRa.symm.trans hR
  simp only [hchi, mul_one] at hcomb
  -- cancel the weight `ζ i p` and the square root of the density
  have hkey := inv_zeta_dens_cancel hζ hB hcomb
  rw [← hkey]
  congr 1
  apply Finset.sum_congr rfl; intro a _
  apply Finset.sum_congr rfl; intro b _
  ring

theorem mat_continuousOn_chi
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ((⊤ : ENat) : WithTop ENat) M]
    {ι₀ : Type*} [Fintype ι₀] {g₀ : Submission.Diff.SMet I M}
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀)
    (h : Work.Diff.STE.Bil (I := I) (M := M))
    (hsm : ∀ (i : ι₀) (a b : Fin (Module.finrank ℝ E)),
      ContDiff ℝ ((⊤ : ENat) : WithTop ENat) (D.R i h a b))
    (j : ι₀) (a b : Fin (Module.finrank ℝ E)) :
    ContinuousOn (D.mat j h a b) {z : Fin (Module.finrank ℝ E) → ℝ | D.χ j z ≠ 0} := by
  intro z₀ hz₀
  -- the parametrisation `z ↦ pt j z` is continuous at `z₀`: the flat coordinate `z₀` is in the
  -- chart target because `z₀` lies in the topological support of `χ j`
  have hztsup : z₀ ∈ tsupport (D.χ j) := subset_closure hz₀
  have harg : flatToE (I := I) (D.x₀ j) z₀ ∈ (extChartAt I (D.x₀ j)).target :=
    D.hχtsup j z₀ hztsup
  have hpt : ContinuousAt (fun z : Fin (Module.finrank ℝ E) → ℝ => D.pt j z) z₀ := by
    have hflat : ContinuousAt (fun z : Fin (Module.finrank ℝ E) → ℝ =>
        flatToE (I := I) (D.x₀ j) z) z₀ :=
      (flatToE_contDiff (I := I) (M := M) (D.x₀ j)).continuous.continuousAt
    have h := (continuousAt_extChartAt_symm'' (I := I) harg).comp hflat
    simpa only [B3Data.pt, Function.comp_def] using h
  -- the matrix of `h` in the frame `e j`, read as a function on `M`, is continuous at `pt j z₀`
  have hmat : ContinuousAt (fun p : M => h p (D.e j a p) (D.e j b p)) (D.pt j z₀) := by
    -- choose a chart `i₀` whose weight `ζ i₀` does not vanish at `pt j z₀`
    obtain ⟨i₀, hi₀⟩ : ∃ i : ι₀, D.ζ i (D.pt j z₀) ≠ 0 := by
      by_contra hc
      push Not at hc
      have hsum : ∑ i : ι₀, (D.ζ i (D.pt j z₀)) ^ 2 = 0 :=
        Finset.sum_eq_zero fun i _ => by rw [hc i]; norm_num
      have h1 := D.hζsq (D.pt j z₀)
      rw [hsum] at h1
      exact one_ne_zero h1.symm
    have hsrc : D.pt j z₀ ∈ (extChartAt I (D.x₀ i₀)).source := (D.hζsupp i₀ _ hi₀).1
    have hcoord : ContinuousAt (fun p : M => coord (I := I) (D.x₀ i₀) p) (D.pt j z₀) :=
      continuousAt_coord_of_mem_source hsrc
    have htgt : flatToE (I := I) (D.x₀ i₀) (coord (I := I) (D.x₀ i₀) (D.pt j z₀))
        ∈ (extChartAt I (D.x₀ i₀)).target := by
      rw [flatToE_coord_cm]
      exact PartialEquiv.map_source (extChartAt I (D.x₀ i₀)) hsrc
    have hdens : ContinuousAt (fun p : M => D.dens i₀ (coord (I := I) (D.x₀ i₀) p))
        (D.pt j z₀) :=
      (dens_continuousAt_of_mem_target D i₀ htgt).comp hcoord
    have hsqrtne : Real.sqrt (D.dens i₀ (coord (I := I) (D.x₀ i₀) (D.pt j z₀))) ≠ 0 :=
      (Real.sqrt_pos.mpr (dens_pos_of_mem_target D i₀ htgt)).ne'
    have hinv : ContinuousAt
        (fun p : M => (Real.sqrt (D.dens i₀ (coord (I := I) (D.x₀ i₀) p)))⁻¹) (D.pt j z₀) :=
      ContinuousAt.inv₀ (Real.continuous_sqrt.continuousAt.comp hdens) hsqrtne
    have hzeta : ContinuousAt (fun p : M => (D.ζ i₀ p)⁻¹) (D.pt j z₀) :=
      ContinuousAt.inv₀ (D.hζsm i₀).continuous.continuousAt hi₀
    -- the double sum over the frame of chart `i₀`
    have hinc1 : ∀ c : Fin (Module.finrank ℝ E),
        ContinuousAt (fun p : M => g₀.inner p (D.e j a p) (D.e i₀ c p)) (D.pt j z₀) :=
      fun c => continuousAt_inner_of_cmdiff ((D.hesm j a).contMDiffAt) ((D.hesm i₀ c).contMDiffAt)
    have hinc2 : ∀ d : Fin (Module.finrank ℝ E),
        ContinuousAt (fun p : M => g₀.inner p (D.e j b p) (D.e i₀ d p)) (D.pt j z₀) :=
      fun d => continuousAt_inner_of_cmdiff ((D.hesm j b).contMDiffAt) ((D.hesm i₀ d).contMDiffAt)
    have hRt : ∀ c d : Fin (Module.finrank ℝ E),
        ContinuousAt (fun p : M => D.R i₀ h c d (coord (I := I) (D.x₀ i₀) p)) (D.pt j z₀) :=
      fun c d => ((hsm i₀ c d).continuous.continuousAt).comp hcoord
    have hterm : ContinuousAt (fun p : M => fun c d : Fin (Module.finrank ℝ E) =>
        g₀.inner p (D.e j a p) (D.e i₀ c p) * g₀.inner p (D.e j b p) (D.e i₀ d p)
          * D.R i₀ h c d (coord (I := I) (D.x₀ i₀) p)) (D.pt j z₀) := by
      rw [continuousAt_pi]
      intro c
      rw [continuousAt_pi]
      intro d
      exact ((hinc1 c).mul (hinc2 d)).mul (hRt c d)
    have hsumlin : Continuous (fun v : Fin (Module.finrank ℝ E) →
        Fin (Module.finrank ℝ E) → ℝ => ∑ c, ∑ d, v c d) := by
      refine continuous_finsetSum Finset.univ (fun c _ => ?_)
      refine continuous_finsetSum Finset.univ (fun d _ => ?_)
      exact (continuous_apply d).comp (continuous_apply c)
    have hsum : ContinuousAt (fun p : M => ∑ c : Fin (Module.finrank ℝ E),
        ∑ d : Fin (Module.finrank ℝ E),
          g₀.inner p (D.e j a p) (D.e i₀ c p) * g₀.inner p (D.e j b p) (D.e i₀ d p)
            * D.R i₀ h c d (coord (I := I) (D.x₀ i₀) p)) (D.pt j z₀) :=
      hsumlin.continuousAt.comp hterm
    have hF : ContinuousAt (fun p : M => (D.ζ i₀ p)⁻¹
        * (Real.sqrt (D.dens i₀ (coord (I := I) (D.x₀ i₀) p)))⁻¹
        * ∑ c, ∑ d, g₀.inner p (D.e j a p) (D.e i₀ c p) * g₀.inner p (D.e j b p) (D.e i₀ d p)
            * D.R i₀ h c d (coord (I := I) (D.x₀ i₀) p)) (D.pt j z₀) :=
      (hzeta.mul hinv).mul hsum
    -- the two functions agree on the (open) set where `ζ i₀` does not vanish
    have hopen : IsOpen {p : M | D.ζ i₀ p ≠ 0} := isOpen_ne.preimage (D.hζsm i₀).continuous
    have hev : (fun p : M => (D.ζ i₀ p)⁻¹
        * (Real.sqrt (D.dens i₀ (coord (I := I) (D.x₀ i₀) p)))⁻¹
        * ∑ c, ∑ d, g₀.inner p (D.e j a p) (D.e i₀ c p) * g₀.inner p (D.e j b p) (D.e i₀ d p)
            * D.R i₀ h c d (coord (I := I) (D.x₀ i₀) p))
        =ᶠ[𝓝 (D.pt j z₀)] (fun p : M => h p (D.e j a p) (D.e j b p)) := by
      filter_upwards [hopen.mem_nhds hi₀] with p hp
      exact (bil_eq_inv_zeta_sum D h i₀ p (D.e j a p) (D.e j b p) hp).symm
    exact hF.congr hev
  exact (hmat.comp hpt).continuousWithinAt

end Work.Diff.STE.B3
