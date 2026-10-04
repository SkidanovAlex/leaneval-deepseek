import Mathlib
import Submission.Work.Diff.STE.B3.Rstar_R_eq_zeta_sq_free

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.STE.Lead

/-- Reconstruction of a section from its localised components at a point `x` where `ζ i x ≠ 0`:
the chart `i` is then genuine at `x`, the localised weight at the flat coordinate of `x` is `ζ i x`,
and `h x u v` is recovered from the chart matrix in the `g₀`-orthonormal frame `e i`
(`apply_eq_sum_mat_free`); dividing by the factor `ψ i · √dens i = ζ i x · √dens i` gives the
identity. -/
theorem bil_apply_eq_sum_R
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ((⊤ : ENat) : WithTop ENat) M]
    {ι₀ : Type*} [Fintype ι₀] {g₀ : Submission.Diff.SMet I M}
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀)
    (i : ι₀) (x : M) (h : Work.Diff.STE.Bil (I := I) (M := M))
    (hζ : D.ζ i x ≠ 0) (u v : TangentSpace I x) :
    h x u v = (D.ζ i x * Real.sqrt (D.dens i (Work.Diff.STE.coord (I := I) (D.x₀ i) x)))⁻¹
      * (∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
          D.R i h a b (Work.Diff.STE.coord (I := I) (D.x₀ i) x)
            * g₀.inner x u (D.e i a x) * g₀.inner x v (D.e i b x)) := by
  -- `ζ i x ≠ 0` puts `x` in the chart source of `x₀ i`, inside the `σ i`-coordinate ball
  obtain ⟨hsrc, hlt⟩ := D.hζsupp i x hζ
  -- at that point the frame `e i` is `g₀`-orthonormal
  have hON : Submission.Diff.IsONFrame g₀ x (fun a => D.e i a x) := by
    have h2 : ‖Work.Diff.STE.coord (I := I) (D.x₀ i) x‖ ≤ 2 * D.σ i := by
      have hσ := D.hσ i
      linarith
    have h0 := D.heON i (Work.Diff.STE.coord (I := I) (D.x₀ i) x) h2
    rwa [D.symm_flatToE_coord i hsrc] at h0
  -- the flat coordinate of `x` lies in the chart target, so the density is positive there
  have htgt : Work.Diff.STE.flatToE (I := I) (D.x₀ i)
        (Work.Diff.STE.coord (I := I) (D.x₀ i) x) ∈ (extChartAt I (D.x₀ i)).target := by
    refine D.htarget i _ ?_
    have hσ := D.hσ i
    linarith
  have hdens : 0 < D.dens i (Work.Diff.STE.coord (I := I) (D.x₀ i) x) :=
    Work.Diff.STE.B3.dens_pos_of_mem_target D i htgt
  have hsne : Real.sqrt (D.dens i (Work.Diff.STE.coord (I := I) (D.x₀ i) x)) ≠ 0 :=
    (Real.sqrt_pos.mpr hdens).ne'
  -- reconstruction of `h` from its chart matrix in the `g₀`-orthonormal frame `e i`
  have hmat : (∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
      D.mat i h a b (Work.Diff.STE.coord (I := I) (D.x₀ i) x)
        * g₀.inner x u (D.e i a x) * g₀.inner x v (D.e i b x)) = h x u v :=
    (Work.Diff.STE.B3.apply_eq_sum_mat_free (I := I) (M := M) D i h hsrc hON u v).symm
  -- the localised component `R i h` is the chart matrix times `ψ i · √dens i`
  have hfac : (∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
      D.R i h a b (Work.Diff.STE.coord (I := I) (D.x₀ i) x)
        * g₀.inner x u (D.e i a x) * g₀.inner x v (D.e i b x))
      = (D.psi i (Work.Diff.STE.coord (I := I) (D.x₀ i) x)
          * Real.sqrt (D.dens i (Work.Diff.STE.coord (I := I) (D.x₀ i) x))) * (h x u v) := by
    rw [← hmat, Finset.mul_sum]
    apply Finset.sum_congr rfl; intro a _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl; intro b _
    simp only [Work.Diff.STE.B3Data.R]
    ring
  -- on the support of `ζ i` the localised weight is `ζ i`, and the two factors cancel
  rw [hfac, D.psi_coord_eq_zeta i hζ]
  exact (inv_mul_cancel_left₀ (mul_ne_zero hζ hsne) (h x u v)).symm

end Work.Diff.STE.Lead
