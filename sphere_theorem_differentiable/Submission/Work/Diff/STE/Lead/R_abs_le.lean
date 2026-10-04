import Mathlib
import Submission.Work.Diff.STE.B3.BPairDefs
import Submission.Work.Diff.STE.B3.dens_bound_sigma

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.STE.Lead

theorem R_abs_le
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ((⊤ : ENat) : WithTop ENat) M] [T2Space M] [I.Boundaryless]
    {ι₀ : Type*} [Fintype ι₀] {g₀ : Submission.Diff.SMet I M}
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀)
    (h : Work.Diff.STE.Bil (I := I) (M := M)) (K C : ℝ) (hK : 0 ≤ K) (hC : 0 < C)
    (hdens : ∀ (i : ι₀) (z : Fin (Module.finrank ℝ E) → ℝ), ‖z‖ ≤ D.σ i → D.dens i z ≤ C)
    (hbound : ∀ (y : M) (u' v' : TangentSpace I y),
      |h y u' v'| ≤ K * Real.sqrt (g₀.inner y u' u') * Real.sqrt (g₀.inner y v' v')) :
    ∀ (i : ι₀) (a b : Fin (Module.finrank ℝ E)) (w : Fin (Module.finrank ℝ E) → ℝ),
      |D.R i h a b w| ≤ Real.sqrt C * K := by
  intro i a b w
  -- `D.R i h a b w = ψ i w · √(dens i w) · mat i h a b w`, and `ψ i w ≠ 0` forces the flat
  -- coordinate `w` into the `σ i`-ball, where `√(dens i w) ≤ √C`, while `|ψ i w| ≤ 1` and
  -- `|mat i h a b w| ≤ K`.
  by_cases hpsi : D.psi i w = 0
  · -- off the support of the localised weight the component vanishes
    rw [Work.Diff.STE.B3Data.R, hpsi, zero_mul, zero_mul, abs_zero]
    exact mul_nonneg (Real.sqrt_nonneg C) hK
  · have hσ : ‖w‖ < D.σ i := Work.Diff.STE.B3.norm_lt_sigma_of_psi_ne_zero D hpsi
    have hON : Submission.Diff.IsONFrame g₀ (D.pt i w)
        (fun a => D.e i a (D.pt i w)) :=
      Work.Diff.STE.B3.isONFrame_of_psi_ne_zero D hpsi
    -- `|ψ i w| = ζ i (pt i w) ≤ 1`
    have hζsq1 : (D.ζ i (D.pt i w)) ^ 2 ≤ 1 := by
      rw [← D.hζsq (D.pt i w)]
      exact Finset.single_le_sum (f := fun k : ι₀ => (D.ζ k (D.pt i w)) ^ 2)
        (fun k _ => sq_nonneg _) (Finset.mem_univ i)
    have hpsi_abs : |D.psi i w| ≤ 1 := by
      rw [Work.Diff.STE.B3.psi_eq_zeta_of_psi_ne_zero D hpsi]
      exact (sq_le_one_iff_abs_le_one _).mp hζsq1
    -- `√(dens i w) ≤ √C`
    have hdensw : D.dens i w ≤ C := hdens i w (le_of_lt hσ)
    have hsqrt : Real.sqrt (D.dens i w) ≤ Real.sqrt C := Real.sqrt_le_sqrt hdensw
    -- `|mat i h a b w| ≤ K`: the frame `e i` is `g₀`-orthonormal at `D.pt i w`
    have hmat : |D.mat i h a b w| ≤ K := by
      change |h (D.pt i w) (D.e i a (D.pt i w)) (D.e i b (D.pt i w))| ≤ K
      have hb := hbound (D.pt i w) (D.e i a (D.pt i w)) (D.e i b (D.pt i w))
      have h2 : g₀.inner (D.pt i w) (D.e i a (D.pt i w)) (D.e i a (D.pt i w)) = 1 := by
        rw [hON a a]; simp
      have h3 : g₀.inner (D.pt i w) (D.e i b (D.pt i w)) (D.e i b (D.pt i w)) = 1 := by
        rw [hON b b]; simp
      rwa [h2, h3, Real.sqrt_one, mul_one, mul_one] at hb
    rw [Work.Diff.STE.B3Data.R]
    have hprod : |D.psi i w| * Real.sqrt (D.dens i w) ≤ 1 * Real.sqrt C :=
      mul_le_mul hpsi_abs hsqrt (Real.sqrt_nonneg _) zero_le_one
    have hstep : |D.psi i w * Real.sqrt (D.dens i w) * D.mat i h a b w|
        ≤ (1 * Real.sqrt C) * K := by
      rw [abs_mul, abs_mul, abs_of_nonneg (Real.sqrt_nonneg (D.dens i w))]
      exact mul_le_mul hprod hmat (abs_nonneg _) (mul_nonneg zero_le_one (Real.sqrt_nonneg C))
    calc |D.psi i w * Real.sqrt (D.dens i w) * D.mat i h a b w|
        ≤ (1 * Real.sqrt C) * K := hstep
      _ = Real.sqrt C * K := by ring

end Work.Diff.STE.Lead
