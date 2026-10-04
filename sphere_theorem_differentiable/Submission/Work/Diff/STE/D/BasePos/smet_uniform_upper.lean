import Mathlib
import Submission.Work.Diff.STE.D.Base.Defs
import Submission.Work.Diff.EXT.ConnCov.gram_lower_of_hmet

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.STE.D.BasePos

/-- **Upper bound for the chart quadratic form of a smooth metric on a compact set.**  For a smooth
metric `g` on `M`, a chart centre `x₀` and a compact subset `K'` of the *target* of the chart at `x₀`
there is `C > 0` with, for all `y ∈ K'` and all `a : E`,

  `g(p)(v_a, v_a) ≤ C ‖a‖²`,  `p = (extChartAt I x₀).symm y`,  `v_a = frameVector I x₀ p a`.

Intended proof: on `K'`, `g(p)(v_a,v_a) = ∑ᵢⱼ cᵢ cⱼ (chartMatFun g x₀ y)ᵢⱼ` with `c = bB.repr a`
(`Work.Diff.EXT.ConnCov.chartMatFun_qform_repr`); the entries `y ↦ chartMatFun g x₀ y i j` are
continuous on `K'` (`Work.Diff.EXT.contDiffAt_chartMatFun`), hence bounded there
(`IsCompact.exists_bound_of_continuousOn`); then
`|∑ᵢⱼ cᵢcⱼ Aᵢⱼ| ≤ (max |Aᵢⱼ|) (∑ᵢ|cᵢ|)² ≤ (max |Aᵢⱼ|) n ∑ᵢcᵢ² ≤ (max |Aᵢⱼ|) n K ‖a‖²`
with `K` from `Work.Diff.EXT.basis_coeff_norm_equiv`. -/
theorem smet_uniform_upper
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ((⊤ : ENat) : WithTop ENat) M] [T2Space M] [I.Boundaryless]
    (g : Submission.Diff.SMet I M) (x₀ : M) (K' : Set E) (hK'c : IsCompact K')
    (hK't : K' ⊆ (extChartAt I x₀).target) :
    ∃ C : ℝ, 0 < C ∧ ∀ y ∈ K', ∀ a : E,
      g.inner ((extChartAt I x₀).symm y)
        (Submission.Geodesic.frameVector (I := I) x₀ ((extChartAt I x₀).symm y) a)
        (Submission.Geodesic.frameVector (I := I) x₀ ((extChartAt I x₀).symm y) a)
      ≤ C * ‖a‖ ^ 2 := by
  classical
  -- The coefficient-norm equivalence: `∑ᵢ cᵢ² ≤ K1 ‖a‖²` for `c = bB.repr a`.
  obtain ⟨K1, K2, hK1pos, hK2pos, hbb⟩ :=
    Work.Diff.EXT.basis_coeff_norm_equiv (E := E) (Work.Diff.EXT.bB (E := E))
  -- Every entry of the chart matrix is continuous on `K'`, hence so is `y ↦ ∑ᵢⱼ ‖A y i j‖`.
  have hentry : ∀ i j : Fin (Module.finrank ℝ E),
      ContinuousOn (fun y : E => Work.Diff.EXT.chartMatFun g x₀ y i j) K' := by
    intro i j y hy
    exact (((continuous_apply j).comp (continuous_apply i)).continuousAt.comp
      (Work.Diff.EXT.contDiffAt_chartMatFun (I := I) (M := M) g x₀
        (hK't hy)).continuousAt).continuousWithinAt
  have hBcont : ContinuousOn
      (fun y : E => ∑ i, ∑ j, ‖Work.Diff.EXT.chartMatFun g x₀ y i j‖) K' := by
    refine continuousOn_finsetSum _ (fun i _ => ?_)
    refine continuousOn_finsetSum _ (fun j _ => ?_)
    exact continuous_norm.comp_continuousOn (hentry i j)
  -- Compactness bounds that sum.
  obtain ⟨M0, hM0⟩ := hK'c.exists_bound_of_continuousOn hBcont
  let Mb : ℝ := max M0 0
  have hMnn : 0 ≤ Mb := le_max_right M0 0
  refine ⟨Mb * ((Module.finrank ℝ E : ℝ) * K1) + 1, ?_, fun y hy a => ?_⟩
  · have : 0 ≤ Mb * ((Module.finrank ℝ E : ℝ) * K1) :=
      mul_nonneg hMnn (mul_nonneg (Nat.cast_nonneg _) hK1pos.le)
    linarith
  · have hle : (∑ i, ∑ j, ‖Work.Diff.EXT.chartMatFun g x₀ y i j‖) ≤ Mb := by
      have h1 := hM0 y hy
      have h2 : (0 : ℝ) ≤ ∑ i, ∑ j, ‖Work.Diff.EXT.chartMatFun g x₀ y i j‖ := by positivity
      rw [Real.norm_of_nonneg h2] at h1
      exact le_trans h1 (le_max_left _ _)
    -- `S = ∑ᵢ |cᵢ|` dominates every coefficient.
    set S : ℝ := ∑ k, |(Work.Diff.EXT.bB (E := E)).repr a k| with hSdef
    have hS : 0 ≤ S := by
      rw [hSdef]; exact Finset.sum_nonneg fun k _ => abs_nonneg _
    have hci : ∀ i : Fin (Module.finrank ℝ E),
        |(Work.Diff.EXT.bB (E := E)).repr a i| ≤ S := by
      intro i
      rw [hSdef]
      exact Finset.single_le_sum
        (f := fun k : Fin (Module.finrank ℝ E) => |(Work.Diff.EXT.bB (E := E)).repr a k|)
        (fun k _ => abs_nonneg _) (Finset.mem_univ i)
    -- Termwise bound `cᵢcⱼAᵢⱼ ≤ S² ‖Aᵢⱼ‖`.
    have hterm : ∀ i j : Fin (Module.finrank ℝ E),
        (Work.Diff.EXT.bB (E := E)).repr a i * (Work.Diff.EXT.bB (E := E)).repr a j
          * Work.Diff.EXT.chartMatFun g x₀ y i j
        ≤ S * S * ‖Work.Diff.EXT.chartMatFun g x₀ y i j‖ := by
      intro i j
      rw [Real.norm_eq_abs]
      have h := le_abs_self ((Work.Diff.EXT.bB (E := E)).repr a i
        * (Work.Diff.EXT.bB (E := E)).repr a j * Work.Diff.EXT.chartMatFun g x₀ y i j)
      rw [abs_mul, abs_mul] at h
      refine le_trans h (mul_le_mul_of_nonneg_right ?_ (abs_nonneg _))
      exact mul_le_mul (hci i) (hci j) (abs_nonneg _) hS
    have hsum1 : (∑ i, ∑ j, (Work.Diff.EXT.bB (E := E)).repr a i
          * (Work.Diff.EXT.bB (E := E)).repr a j * Work.Diff.EXT.chartMatFun g x₀ y i j)
        ≤ ∑ i, ∑ j, S * S * ‖Work.Diff.EXT.chartMatFun g x₀ y i j‖ :=
      Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hterm i j
    have hsum2 : (∑ i, ∑ j, S * S * ‖Work.Diff.EXT.chartMatFun g x₀ y i j‖)
        = S * S * (∑ i, ∑ j, ‖Work.Diff.EXT.chartMatFun g x₀ y i j‖) := by
      simp only [Finset.mul_sum]
    have hsum3 : (∑ i, ∑ j, S * S * ‖Work.Diff.EXT.chartMatFun g x₀ y i j‖) ≤ S * S * Mb := by
      rw [hsum2]
      exact mul_le_mul_of_nonneg_left hle (mul_nonneg hS hS)
    -- `S² ≤ n ∑ᵢ cᵢ²` (Cauchy–Schwarz) and `∑ᵢ cᵢ² ≤ K1 ‖a‖²`.
    have hS2 : S * S ≤ (Module.finrank ℝ E : ℝ)
        * ∑ k, (Work.Diff.EXT.bB (E := E)).repr a k ^ 2 := by
      have h := sq_sum_le_card_mul_sum_sq (s := Finset.univ)
        (f := fun k : Fin (Module.finrank ℝ E) => |(Work.Diff.EXT.bB (E := E)).repr a k|)
      simp only [Finset.card_univ, Fintype.card_fin, sq_abs] at h
      rw [show S * S = S ^ 2 by ring]
      exact h
    have hcoef : (∑ k, (Work.Diff.EXT.bB (E := E)).repr a k ^ 2) ≤ K1 * ‖a‖ ^ 2 := by
      have h := (hbb ((Work.Diff.EXT.bB (E := E)).repr a)).1
      rw [Module.Basis.sum_repr] at h
      exact h
    have hstep : S * S * Mb ≤ Mb * ((Module.finrank ℝ E : ℝ) * K1) * ‖a‖ ^ 2 := by
      calc S * S * Mb ≤ ((Module.finrank ℝ E : ℝ)
              * ∑ k, (Work.Diff.EXT.bB (E := E)).repr a k ^ 2) * Mb :=
            mul_le_mul_of_nonneg_right hS2 hMnn
        _ ≤ ((Module.finrank ℝ E : ℝ) * (K1 * ‖a‖ ^ 2)) * Mb :=
            mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left hcoef (Nat.cast_nonneg _)) hMnn
        _ = Mb * ((Module.finrank ℝ E : ℝ) * K1) * ‖a‖ ^ 2 := by ring
    -- Rewrite the metric square as the quadratic form of the chart matrix.
    have hquad := Work.Diff.EXT.ConnCov.chartMatFun_qform_repr (I := I) (M := M) g x₀ y a
    rw [← hquad]
    calc (∑ i, ∑ j, (Work.Diff.EXT.bB (E := E)).repr a i
          * (Work.Diff.EXT.bB (E := E)).repr a j * Work.Diff.EXT.chartMatFun g x₀ y i j)
        ≤ Mb * ((Module.finrank ℝ E : ℝ) * K1) * ‖a‖ ^ 2 := le_trans hsum1 (le_trans hsum3 hstep)
      _ ≤ (Mb * ((Module.finrank ℝ E : ℝ) * K1) + 1) * ‖a‖ ^ 2 :=
          mul_le_mul_of_nonneg_right (le_add_of_nonneg_right zero_le_one) (sq_nonneg _)

end Work.Diff.STE.D.BasePos
