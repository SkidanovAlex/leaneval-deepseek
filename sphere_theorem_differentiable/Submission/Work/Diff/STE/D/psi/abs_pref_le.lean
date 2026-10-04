import Mathlib
import Submission.Work.Diff.STE.B3.BPairDefs
import Submission.Work.Diff.STE.B3.dens_bound_sigma

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.STE.D.psi

theorem abs_pref_le
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ((⊤ : ENat) : WithTop ENat) M] [T2Space M] [I.Boundaryless]
    {ι₀ : Type*} [Fintype ι₀] {g₀ : Submission.Diff.SMet I M}
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (i : ι₀) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ y : Fin (Module.finrank ℝ E) → ℝ,
      |Work.Diff.STE.B3Data.psi (I := I) (M := M) D i y *
        Real.sqrt (Work.Diff.STE.B3Data.dens (I := I) (M := M) D i y)| ≤ B := by
  classical
  -- Uniform bound for the chart volume density on the closed flat `σ`-ball.
  obtain ⟨c, C, hc, hC, hb⟩ := Work.Diff.STE.B3.dens_bound_sigma (I := I) (M := M) D
  refine ⟨Real.sqrt C, Real.sqrt_nonneg C, fun y => ?_⟩
  by_cases hy : Work.Diff.STE.B3Data.psi (I := I) (M := M) D i y = 0
  · -- Off the support of `ψ i` the product vanishes.
    rw [hy, zero_mul, abs_zero]
    exact Real.sqrt_nonneg C
  · -- On the support of `ψ i`, `χ i = 1` and `‖y‖ < σ i`, so `ψ i y = ζ i (pt i y)` with
    -- `|ζ i (pt i y)| ≤ 1`, while `√(dens i y) ≤ √C` by the uniform density bound.
    have hsig : ‖y‖ ≤ D.σ i :=
      le_of_lt (Work.Diff.STE.B3.norm_lt_sigma_of_psi_ne_zero D hy)
    have hdens : Work.Diff.STE.B3Data.dens (I := I) (M := M) D i y ≤ C := (hb i y hsig).2
    have hzeta : |D.ζ i (D.pt i y)| ≤ 1 := by
      have hsq : (D.ζ i (D.pt i y)) ^ 2 ≤ 1 := by
        have hsingle : (D.ζ i (D.pt i y)) ^ 2
            ≤ ∑ j : ι₀, (D.ζ j (D.pt i y)) ^ 2 := by
          have h := Finset.single_le_sum (s := Finset.univ)
            (f := fun j : ι₀ => (D.ζ j (D.pt i y)) ^ 2)
            (fun j _ => sq_nonneg (D.ζ j (D.pt i y))) (Finset.mem_univ i)
          simpa using h
        rw [D.hζsq (D.pt i y)] at hsingle
        exact hsingle
      have hnn : 0 ≤ D.ζ i (D.pt i y) := D.hζnn i (D.pt i y)
      refine abs_le.mpr ⟨by linarith, ?_⟩
      nlinarith [hsq, hnn, sq_nonneg (D.ζ i (D.pt i y) - 1)]
    have hpsi : |Work.Diff.STE.B3Data.psi (I := I) (M := M) D i y| ≤ 1 := by
      rw [Work.Diff.STE.B3.psi_eq_zeta_of_psi_ne_zero (I := I) (M := M) D hy]
      exact hzeta
    calc |Work.Diff.STE.B3Data.psi (I := I) (M := M) D i y *
            Real.sqrt (Work.Diff.STE.B3Data.dens (I := I) (M := M) D i y)|
        = |Work.Diff.STE.B3Data.psi (I := I) (M := M) D i y| *
            Real.sqrt (Work.Diff.STE.B3Data.dens (I := I) (M := M) D i y) := by
          rw [abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
      _ ≤ 1 * Real.sqrt C :=
          mul_le_mul hpsi (Real.sqrt_le_sqrt hdens) (Real.sqrt_nonneg _) (by norm_num)
      _ = Real.sqrt C := one_mul _

end Work.Diff.STE.D.psi
