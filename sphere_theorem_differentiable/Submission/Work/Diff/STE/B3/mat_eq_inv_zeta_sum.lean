import Mathlib
import Submission.Work.Diff.STE.B3.Rstar_R_eq_zeta_sq_free
import Submission.Work.Diff.STE.B3.CompSmooth
import Submission.Work.Diff.STE.B3.Comp
import Submission.Work.Diff.STE.B3.Data

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.STE.B3

/-- Elementary algebra: if `(A * B⁻¹) * S = A ^ 2 * M` with `A ≠ 0` and `B ≠ 0`, then
`A⁻¹ * B⁻¹ * S = M`.  This is the cancellation of the weight `ζ_j p` and of the square root of the
volume density `√(dens_j)` in the pointwise reconstruction identity. -/
private lemma inv_mul_inv_mul_eq_of_mul_inv_mul_eq {A B S M : ℝ}
    (hA : A ≠ 0) (hB : B ≠ 0) (h : (A * B⁻¹) * S = A ^ 2 * M) :
    A⁻¹ * B⁻¹ * S = M := by
  have h1 : S = A * B * M := by
    have h2 : (A * B⁻¹) * (A * B * M) = A ^ 2 * M := by
      field_simp
    exact mul_left_cancel₀ (mul_ne_zero hA (inv_ne_zero hB)) (h.trans h2.symm)
  rw [h1]
  calc A⁻¹ * B⁻¹ * (A * B * M) = (A⁻¹ * A) * (B⁻¹ * B) * M := by ring
    _ = M := by rw [inv_mul_cancel₀ hA, inv_mul_cancel₀ hB]; ring

/-- **Pointwise inversion of the reconstruction identity.**  At a point `p` where the weight `ζ_j`
of the chart `j` does not vanish, the value of a bilinear form `h` on the two vectors `X`, `Y` is
the (weighted) double sum of the localised components `R_j h` against the coefficients of `X`, `Y`
in the frame `e_j`.

Indeed `hζsupp` puts `p` in the chart source of `x₀ j` with `‖coord_j p‖ < σ_j`, so the cut-off
`χ_j` equals `1` at `coord_j p`, the frame `e_j` is `g₀`-orthonormal at `p`, the density is
positive there, and `Σ_i R_i* R_i = id` (`Rstar_R_eq_zeta_sq_free`) specialises to the stated
identity after cancelling the weight and the square root of the density.

This is the localised form of the reconstruction identity `Σ_i R_i* R_i = id`, written for a single
chart `j`; the target theorem is its specialisation at `p = D.pt i z`, `X = D.e i c p`,
`Y = D.e i d p`. -/
private lemma mat_eq_inv_zeta_sum_aux
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ((⊤ : ENat) : WithTop ENat) M]
    {ι₀ : Type*} [Fintype ι₀] {g₀ : Submission.Diff.SMet I M}
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀)
    (h : Work.Diff.STE.Bil (I := I) (M := M)) (j : ι₀) (p : M) (X Y : TangentSpace I p)
    (hζ : D.ζ j p ≠ 0) :
    h p X Y
      = (D.ζ j p)⁻¹
        * (Real.sqrt (D.dens j (Work.Diff.STE.coord (I := I) (D.x₀ j) p)))⁻¹
        * ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
            g₀.inner p X (D.e j a p) * g₀.inner p Y (D.e j b p)
              * D.R j h a b (Work.Diff.STE.coord (I := I) (D.x₀ j) p) := by
  obtain ⟨hsrc, hlt⟩ := D.hζsupp j p hζ
  have h2 : ‖Work.Diff.STE.coord (I := I) (D.x₀ j) p‖ ≤ 2 * D.σ j := by
    have hσ := D.hσ j; linarith
  -- the frame `e_j` is `g₀`-orthonormal at `p`
  have hON : Submission.Diff.IsONFrame g₀ p (fun a => D.e j a p) := by
    have h0 := D.heON j (Work.Diff.STE.coord (I := I) (D.x₀ j) p) h2
    rwa [D.symm_flatToE_coord j hsrc] at h0
  -- the density is positive at the flat coordinate of `p`
  have htgt : Work.Diff.STE.flatToE (I := I) (D.x₀ j) (Work.Diff.STE.coord (I := I) (D.x₀ j) p)
      ∈ (extChartAt I (D.x₀ j)).target := D.htarget j _ h2
  have hdens : 0 < D.dens j (Work.Diff.STE.coord (I := I) (D.x₀ j) p) :=
    dens_pos_of_mem_target D j htgt
  have hB : Real.sqrt (D.dens j (Work.Diff.STE.coord (I := I) (D.x₀ j) p)) ≠ 0 :=
    (Real.sqrt_pos.mpr hdens).ne'
  -- the cut-off is `1` on the σ-ball, where `ζ_j` lives
  have hchi : D.χ j (Work.Diff.STE.coord (I := I) (D.x₀ j) p) = 1 :=
    D.hχ1 j _ (le_of_lt hlt)
  -- evaluate the reconstruction of the localised component: this is `ζ_j ^ 2 * h`
  have hR := Rstar_R_eq_zeta_sq_free D h j p X Y
  -- and expand the reconstruction in the frame of chart `j`
  have hRa : ((D.Rstar j (fun (a b : Fin (Module.finrank ℝ E))
        (z : Fin (Module.finrank ℝ E) → ℝ) => D.R j h a b z) p) X) Y
      = (D.ζ j p * D.χ j (Work.Diff.STE.coord (I := I) (D.x₀ j) p)
          * (Real.sqrt (D.dens j (Work.Diff.STE.coord (I := I) (D.x₀ j) p)))⁻¹)
        * ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
            D.R j h a b (Work.Diff.STE.coord (I := I) (D.x₀ j) p)
              * ((g₀.inner p) X) (D.e j a p) * ((g₀.inner p) Y) (D.e j b p) := by
    simpa only using Rstar_apply D j (fun a b z => D.R j h a b z) p X Y
  have hcomb := hRa.symm.trans hR
  simp only [hchi, mul_one] at hcomb
  -- cancel the weight `ζ_j p` and the square root of the density
  have hkey := inv_mul_inv_mul_eq_of_mul_inv_mul_eq hζ hB hcomb
  rw [← hkey]
  congr 1
  apply Finset.sum_congr rfl; intro a _
  apply Finset.sum_congr rfl; intro b _
  ring

theorem mat_eq_inv_zeta_sum
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ((⊤ : ENat) : WithTop ENat) M] [I.Boundaryless]
    {ι₀ : Type*} [Fintype ι₀] {g₀ : Submission.Diff.SMet I M}
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀)
    (h : Work.Diff.STE.Bil (I := I) (M := M)) (i j : ι₀) (c d : Fin (Module.finrank ℝ E))
    (z : Fin (Module.finrank ℝ E) → ℝ) (hz : ‖z‖ ≤ 2 * D.σ i)
    (hζ : D.ζ j (D.pt i z) ≠ 0) :
    D.mat i h c d z
      = (D.ζ j (D.pt i z))⁻¹
        * (Real.sqrt (D.dens j (Work.Diff.STE.coord (I := I) (D.x₀ j) (D.pt i z))))⁻¹
        * ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
            g₀.inner (D.pt i z) (D.e i c (D.pt i z)) (D.e j a (D.pt i z)) *
            g₀.inner (D.pt i z) (D.e i d (D.pt i z)) (D.e j b (D.pt i z)) *
            D.R j h a b (Work.Diff.STE.coord (I := I) (D.x₀ j) (D.pt i z)) :=
  mat_eq_inv_zeta_sum_aux D h j (D.pt i z) (D.e i c (D.pt i z)) (D.e i d (D.pt i z)) hζ

end Work.Diff.STE.B3
