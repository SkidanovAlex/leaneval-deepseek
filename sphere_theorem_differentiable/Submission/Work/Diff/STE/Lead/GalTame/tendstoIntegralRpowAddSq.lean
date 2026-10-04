import Mathlib
import Submission.Work.Diff.STE.Torus

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.STE.Lead.GalTame

open MeasureTheory Filter

/-- A continuous real-valued function is integrable on the half open unit cube, which is
contained in the compact closed cube `[0,1]^ι`. -/
private lemma integrableOn_unitCube_of_continuous_real {ι : Type*} [Fintype ι]
    {F : (ι → ℝ) → ℝ} (hF : Continuous F) :
    Integrable F (volume.restrict (Work.Diff.STE.unitCube (ι := ι))) := by
  have hC : IsCompact (Set.pi Set.univ (fun _ : ι => Set.Icc (0 : ℝ) 1)) :=
    isCompact_univ_pi (fun _ => isCompact_Icc)
  have hsub : Work.Diff.STE.unitCube (ι := ι) ⊆
      Set.pi Set.univ (fun _ : ι => Set.Icc (0 : ℝ) 1) := by
    intro x hx
    simp only [Work.Diff.STE.unitCube, Set.mem_pi, Set.mem_univ, true_implies] at hx ⊢
    exact fun j => ⟨le_of_lt (hx j).1, (hx j).2⟩
  exact (ContinuousOn.integrableOn_compact hC hF.continuousOn).mono_set hsub

/-- The shift `(1/(n+1))²` lies in `[0,1]`. -/
private lemma one_div_add_one_sq_mem {n : ℕ} :
    0 ≤ (1 / ((n : ℝ) + 1)) ^ 2 ∧ (1 / ((n : ℝ) + 1)) ^ 2 ≤ 1 := by
  have h0 : (0 : ℝ) ≤ 1 / ((n : ℝ) + 1) := by positivity
  have h1 : (1 : ℝ) / ((n : ℝ) + 1) ≤ 1 := by
    rw [div_le_one (by positivity)]
    exact le_add_of_nonneg_left (Nat.cast_nonneg n)
  exact ⟨pow_nonneg h0 2, pow_le_one₀ h0 h1⟩

/-- **The `ε → 0⁺` limit of the regularised integrals.**

For `s ≥ 0` and continuous nonnegative `N, M : (ι → ℝ) → ℝ`,
`n ↦ ∫_{cube} (N x + (1/(n+1))²)^s * M x` tends to `∫_{cube} (N x)^s * M x` as `n → ∞`.

This is the dominated-convergence step of the `ε`-regularisation proof of the sharp periodic
integration by parts (see `Submission/Work/Diff/STE/GN/ibp_rpow_complex.lean`, whose two remaining
limits are exactly this statement, at `N = ‖∂ᵢg‖²` with `M = ‖∂ᵢg‖²` resp. `M = ‖g‖·‖∂ᵢ∂ᵢg‖`).
Pointwise convergence is continuity of `t ↦ t^s` at `N x ≥ 0`; the dominating function
`(N x + 1)^s * M x` is continuous, hence integrable on the cube. -/
theorem tendstoIntegralRpowAddSq {ι : Type*} [Fintype ι] [DecidableEq ι]
    (s : ℝ) (hs : 0 ≤ s) (N M : (ι → ℝ) → ℝ)
    (hN : Continuous N) (hM : Continuous M) (hN0 : ∀ x, 0 ≤ N x) (hM0 : ∀ x, 0 ≤ M x) :
    Filter.Tendsto
      (fun n : ℕ => ∫ x in Work.Diff.STE.unitCube (ι := ι),
        (N x + (1 / ((n : ℝ) + 1)) ^ 2) ^ s * M x)
      Filter.atTop
      (nhds (∫ x in Work.Diff.STE.unitCube (ι := ι), (N x) ^ s * M x)) := by
  -- the integrand is continuous for every `n`
  have hcont : ∀ n : ℕ, Continuous
      (fun x : ι → ℝ => (N x + (1 / ((n : ℝ) + 1)) ^ 2) ^ s * M x) :=
    fun n => ((hN.add continuous_const).rpow_const (fun _ => Or.inr hs)).mul hM
  -- the dominating function
  set bound : (ι → ℝ) → ℝ := fun x => (N x + 1) ^ s * M x with hbound_def
  have hbound_cont : Continuous bound :=
    ((hN.add continuous_const).rpow_const (fun _ => Or.inr hs)).mul hM
  refine tendsto_integral_of_dominated_convergence
    (μ := volume.restrict (Work.Diff.STE.unitCube (ι := ι)))
    (bound := bound)
    (F := fun n x => (N x + (1 / ((n : ℝ) + 1)) ^ 2) ^ s * M x)
    (f := fun x => (N x) ^ s * M x) (fun n => (hcont n).aestronglyMeasurable) ?_ ?_ ?_
  · -- the dominating function is integrable on the cube
    exact integrableOn_unitCube_of_continuous_real hbound_cont
  · -- the domination, for every `n`
    intro n
    refine Eventually.of_forall fun x => ?_
    obtain ⟨hc0, hc1⟩ := one_div_add_one_sq_mem (n := n)
    have hle : N x + (1 / ((n : ℝ) + 1)) ^ 2 ≤ N x + 1 := by linarith
    have hnn : 0 ≤ N x + (1 / ((n : ℝ) + 1)) ^ 2 := by linarith [hN0 x]
    have hrpow : (N x + (1 / ((n : ℝ) + 1)) ^ 2) ^ s ≤ (N x + 1) ^ s :=
      Real.rpow_le_rpow hnn hle hs
    have hprod : 0 ≤ (N x + (1 / ((n : ℝ) + 1)) ^ 2) ^ s * M x :=
      mul_nonneg (Real.rpow_nonneg hnn s) (hM0 x)
    rw [Real.norm_eq_abs, abs_of_nonneg hprod]
    exact mul_le_mul_of_nonneg_right hrpow (hM0 x)
  · -- pointwise convergence
    refine Eventually.of_forall fun x => ?_
    have hc : Tendsto (fun n : ℕ => (1 / ((n : ℝ) + 1)) ^ 2) atTop (nhds 0) := by
      simpa using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).pow 2
    have hNx : Tendsto (fun n : ℕ => N x + (1 / ((n : ℝ) + 1)) ^ 2) atTop (nhds (N x)) := by
      simpa using tendsto_const_nhds.add hc
    exact (hNx.rpow_const (Or.inr hs)).mul_const (M x)

end Work.Diff.STE.Lead.GalTame
