import Mathlib
import Submission.Work.Diff.STE.B3.Comp
import Submission.Work.Diff.STE.B3.Rstar_apply
import Submission.Work.Diff.STE.B3.Recon
import Submission.Work.Diff.STE.B3.dens_bound_sigma
import Submission.Work.Diff.STE.B3.BPairDefs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology BigOperators
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter

namespace Work.Diff.STE.B3

/- Route: the same statement (with a spurious `[I.Boundaryless]` hypothesis) is
`Work.Diff.STE.B3.Rstar_R_eq_zeta_sq` in `Submission/Work/Diff/STE/B3/sum_Rstar_R_eq_id.lean`;
the Boundaryless hypothesis is NOT needed: the proof uses only `D.hζsupp`, `D.hχ1`,
`D.psi_coord_eq_zeta`, `D.symm_flatToE_coord`, `D.heON`, `Work.Diff.STE.B3.dens_pos_of_mem_target`,
`Work.Diff.STE.B3.Rstar_apply`, and the reconstruction of `h` from its chart matrix in an
orthonormal frame.  The latter must be proved here without `[I.Boundaryless]` (the version
`Work.Diff.STE.B3Data.apply_eq_sum_mat` in `Diff/STE/B3/Recon.lean` carries it as an unused
auto-bound instance variable; its proof only uses
`Work.EXT.sum_inner_smul_eq_self_of_isONFrame` and
`Work.Diff.STE.fill.clm_apply_sum_smul_sum_smul`, both Boundaryless-free, plus `D.pt_coord`). -/

/-- **Reconstruction of a section from its chart matrix**, without the (unused) hypothesis
`[I.Boundaryless]` of `Work.Diff.STE.B3Data.apply_eq_sum_mat` (`Diff/STE/B3/Recon.lean`).

At a point `x` of the chart source of `x₀ i` where the frame `e i` is `g₀`-orthonormal, the value
of `h` on `u`, `v` is the double sum of the chart matrix against the coefficients of `u` and `v` in
that orthonormal frame.

The proof is the same as in `Recon.lean`: expand `u` and `v` in the orthonormal frame `e i`
(`Work.EXT.sum_inner_smul_eq_self_of_isONFrame`, which is Boundaryless-free), evaluate the bilinear
form on the two sums (`Work.Diff.STE.fill.clm_apply_sum_smul_sum_smul`), and identify the chart
matrix of `h` at `x` with `h x (e i a x) (e i b x)` (`D.pt_coord`). -/
theorem apply_eq_sum_mat_free
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ((⊤ : ENat) : WithTop ENat) M]
    {ι₀ : Type*} [Fintype ι₀] {g₀ : Submission.Diff.SMet I M}
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀)
    (i : ι₀) (h : Work.Diff.STE.Bil (I := I) (M := M)) {x : M}
    (hsrc : x ∈ (extChartAt I (D.x₀ i)).source)
    (hON : IsONFrame g₀ x (fun a => D.e i a x)) (u v : TangentSpace I x) :
    h x u v = ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
      D.mat i h a b (Work.Diff.STE.coord (I := I) (D.x₀ i) x)
        * g₀.inner x u (D.e i a x) * g₀.inner x v (D.e i b x) := by
  have hu : u = ∑ a : Fin (Module.finrank ℝ E),
      g₀.inner x u (D.e i a x) • D.e i a x :=
    (Work.EXT.sum_inner_smul_eq_self_of_isONFrame g₀ x (fun a => D.e i a x) hON u).symm
  have hv : v = ∑ b : Fin (Module.finrank ℝ E),
      g₀.inner x v (D.e i b x) • D.e i b x :=
    (Work.EXT.sum_inner_smul_eq_self_of_isONFrame g₀ x (fun a => D.e i a x) hON v).symm
  conv_lhs => rw [hu, hv]
  rw [Work.Diff.STE.fill.clm_apply_sum_smul_sum_smul (h x) _ _ _ _]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  have hmat : D.mat i h a b (Work.Diff.STE.coord (I := I) (D.x₀ i) x)
      = h x (D.e i a x) (D.e i b x) := by
    simp only [B3Data.mat]
    rw [D.pt_coord i hsrc]
  rw [hmat]
  ring

/-- **The individual reconstruction term.**  The reconstruction of the localised component `R_i h`
is `ζ_i ^ 2 · h` pointwise: the weight `ψ i = χ i · ζ i ∘ coord i`, the cut-off `χ i` (equal to `1`
on the `σ i`-ball, where `ζ i` lives) and the volume density `√(dens i)` (which cancels against the
`(√dens i)⁻¹` of the reconstruction) combine into `ζ i ^ 2`, and the chart matrix of `h` in the
`g₀`-orthonormal frame `e i` reconstructs `h`.

This is `Work.Diff.STE.B3.Rstar_R_eq_zeta_sq` of `Diff/STE/B3/sum_Rstar_R_eq_id.lean` with the
unused hypothesis `[I.Boundaryless]` removed. -/
theorem Rstar_R_eq_zeta_sq_free
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ((⊤ : ENat) : WithTop ENat) M]
    {ι₀ : Type*} [Fintype ι₀] {g₀ : Submission.Diff.SMet I M}
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀)
    (h : Work.Diff.STE.Bil (I := I) (M := M)) (i : ι₀) (p : M) (X Y : TangentSpace I p) :
    D.Rstar i (fun (a b : Fin (Module.finrank ℝ E)) (z : Fin (Module.finrank ℝ E) → ℝ) =>
        D.R i h a b z) p X Y = (D.ζ i p) ^ 2 * h p X Y := by
  by_cases hz : D.ζ i p = 0
  · rw [Rstar_apply D i _ p X Y, hz]
    simp
  · obtain ⟨hsrc, hlt⟩ := D.hζsupp i p hz
    -- the frame of chart `i` is `g₀`-orthonormal at `p`
    have hON : IsONFrame g₀ p (fun a => D.e i a p) := by
      have h2 : ‖coord (I := I) (D.x₀ i) p‖ ≤ 2 * D.σ i := by
        have hσ := D.hσ i; linarith
      have h0 := D.heON i (coord (I := I) (D.x₀ i) p) h2
      rwa [D.symm_flatToE_coord i hsrc] at h0
    -- the density is positive at the flat coordinate of `p`
    have htgt : flatToE (I := I) (D.x₀ i) (coord (I := I) (D.x₀ i) p)
        ∈ (extChartAt I (D.x₀ i)).target := by
      refine D.htarget i _ ?_
      have hσ := D.hσ i; linarith
    have hdens : 0 < D.dens i (coord (I := I) (D.x₀ i) p) := dens_pos_of_mem_target D i htgt
    have hsne : Real.sqrt (D.dens i (coord (I := I) (D.x₀ i) p)) ≠ 0 :=
      (Real.sqrt_pos.mpr hdens).ne'
    -- reconstruction of `h` from its chart matrix in the orthonormal frame `e i`
    have hmat : (∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
        D.mat i h a b (coord (I := I) (D.x₀ i) p)
          * g₀.inner p X (D.e i a p) * g₀.inner p Y (D.e i b p)) = h p X Y :=
      (apply_eq_sum_mat_free D i h hsrc hON X Y).symm
    -- factor the localised weight and the density out of the double sum
    have hfac : (∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
        D.R i h a b (coord (I := I) (D.x₀ i) p)
          * g₀.inner p X (D.e i a p) * g₀.inner p Y (D.e i b p))
        = (D.psi i (coord (I := I) (D.x₀ i) p)
            * Real.sqrt (D.dens i (coord (I := I) (D.x₀ i) p))) * (h p X Y) := by
      rw [← hmat, Finset.mul_sum]
      apply Finset.sum_congr rfl; intro a _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl; intro b _
      simp only [B3Data.R]; ring
    rw [Rstar_apply D i _ p X Y, hfac, D.hχ1 i _ (le_of_lt hlt), D.psi_coord_eq_zeta i hz]
    rw [mul_one]
    calc (D.ζ i p * (Real.sqrt (D.dens i (coord (I := I) (D.x₀ i) p)))⁻¹)
          * (D.ζ i p * Real.sqrt (D.dens i (coord (I := I) (D.x₀ i) p)) * (h p X Y))
        = (D.ζ i p) ^ 2 * ((Real.sqrt (D.dens i (coord (I := I) (D.x₀ i) p)))⁻¹
            * Real.sqrt (D.dens i (coord (I := I) (D.x₀ i) p))) * (h p X Y) := by ring
      _ = (D.ζ i p) ^ 2 * (h p X Y) := by rw [inv_mul_cancel₀ hsne, mul_one]

end Work.Diff.STE.B3
