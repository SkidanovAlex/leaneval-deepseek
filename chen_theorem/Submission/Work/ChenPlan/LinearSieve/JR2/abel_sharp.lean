import Mathlib
import Submission.Work.ChenPlan.LinearSieve.JR2.Defs
import Submission.Work.ChenPlan.LinearSieve.RIMain.abel_pointwise
import Submission.Work.ChenPlan.LinearSieve.RIMain.parts.sum_hprof_le_integral
import Submission.Work.ChenPlan.LinearSieve.Abel.abel_step_sum
import Submission.Work.ChenPlan.LinearSieve.RIMain.AuxLemmas.sum_nu_VfR_eq_range

open Finset
open scoped BigOperators

namespace Work.ChenPlan.LinearSieve.JR2

/-- The Abel/partial-summation step for the **sharp-normalised** linear sieve: the `RIMain.abel_pointwise`
estimate with the constant excess `(1+ε)` in place of `(1 + K/log u)`.  Blueprint:
`Submission/Work/ChenPlan/LinearSieve/RIMain/abel_pointwise.lean` (same proof, with the profile
`u ↦ (1+ε)·log Z/log u` instead of `hprof K Z u`), plus
`RIMain/parts/sum_hprof_le_integral.lean` (take `K = 0` and multiply by `1+ε`) and
`Abel/abel_step_sum.lean`, `RIMain/AuxLemmas/sum_nu_VfR_eq_range.lean`.  Needed by
`JR2/layer_sharp`. -/
theorem abel_sharp {A : BoundingSieve} {w Z ε : ℝ} (hε : 0 ≤ ε) (hw : 2 ≤ w) (hwZ : w < Z)
    (hV : ∀ u : ℝ, w ≤ u → u ≤ Z →
      Work.ChenPlan.LinearSieve.VfR A u
        ≤ Work.ChenPlan.LinearSieve.VfR A Z * ((1 + ε) * (Real.log Z / Real.log u)))
    {Φ : ℝ → ℝ} (hΦmono : ∀ a b : ℝ, w ≤ a → a ≤ b → b ≤ Z → Φ a ≤ Φ b)
    (hΦnn : ∀ a : ℝ, w ≤ a → a ≤ Z → 0 ≤ Φ a) :
    ∑ p ∈ A.prodPrimes.primeFactors.filter
        (fun p : ℕ => w ≤ (p : ℝ) ∧ (p : ℝ) < Z),
        A.nu p * Work.ChenPlan.LinearSieve.VfR A (p : ℝ) * Φ (p : ℝ)
      ≤ Work.ChenPlan.LinearSieve.VfR A Z * (ε * Φ Z
          + (1 + ε) * ∫ u in w..Z, Φ u * (Real.log Z / (u * (Real.log u) ^ 2))) := by
  classical
  have hwZle : w ≤ Z := le_of_lt hwZ
  have hZ1 : 1 < Z := lt_of_le_of_lt (by linarith) hwZ
  have hlogZne : Real.log Z ≠ 0 := ne_of_gt (Real.log_pos hZ1)
  have hVZpos : 0 < Work.ChenPlan.LinearSieve.VfR A Z :=
    Work.ChenPlan.LinearSieve.VfR_pos A Z
  have hVZnn : 0 ≤ Work.ChenPlan.LinearSieve.VfR A Z := le_of_lt hVZpos
  have hPmono : Monotone (RIMain.vEnum A w Z) := RIMain.vEnum_mono A w Z
  have hP0 : w ≤ RIMain.vEnum A w Z 0 := RIMain.le_vEnum A hwZle 0
  have hPn : RIMain.vEnum A w Z (RIMain.pSet A w Z).card = Z := RIMain.vEnum_card A w Z
  -- The sharp profile `u ↦ (1+ε)·log Z/log u = (1+ε)·hprof 0 Z u`.
  have hMT : ∀ k : ℕ, k ≤ (RIMain.pSet A w Z).card →
      RIMain.Vnorm A Z (RIMain.vEnum A w Z k)
        ≤ (1 + ε) * RIMain.hprof 0 Z (RIMain.vEnum A w Z k) := by
    intro k _
    have h1 : Work.ChenPlan.LinearSieve.VfR A (RIMain.vEnum A w Z k)
        ≤ Work.ChenPlan.LinearSieve.VfR A Z *
            ((1 + ε) * RIMain.hprof 0 Z (RIMain.vEnum A w Z k)) := by
      have h := hV _ (RIMain.le_vEnum A hwZle k) (RIMain.vEnum_le A w Z k)
      simpa [RIMain.hprof] using h
    rw [RIMain.Vnorm]
    exact (div_le_iff₀ hVZpos).mpr (by simpa [mul_comm] using h1)
  have hstep := Abel.abel_step_sum (n := (RIMain.pSet A w Z).card) (P := RIMain.vEnum A w Z)
    (M := RIMain.Vnorm A Z) (T := fun u => (1 + ε) * RIMain.hprof 0 Z u)
    hPmono hP0 hPn hMT hΦmono hΦnn
  have hTZ : (1 + ε) * RIMain.hprof 0 Z Z = 1 + ε := by
    rw [RIMain.hprof_Z hlogZne]
    simp
  have hstep' : ∑ k ∈ Finset.range (RIMain.pSet A w Z).card,
        (RIMain.Vnorm A Z (RIMain.vEnum A w Z k)
          - RIMain.Vnorm A Z (RIMain.vEnum A w Z (k + 1))) * Φ (RIMain.vEnum A w Z k)
      ≤ ε * Φ Z + ∑ k ∈ Finset.range (RIMain.pSet A w Z).card,
          ((1 + ε) * RIMain.hprof 0 Z (RIMain.vEnum A w Z k)
            - (1 + ε) * RIMain.hprof 0 Z (RIMain.vEnum A w Z (k + 1)))
            * Φ (RIMain.vEnum A w Z k) := by
    have h1 := hstep
    rw [hTZ, RIMain.Vnorm_Z A Z] at h1
    linarith [h1]
  -- The Abel sum of the drops of the sharp profile is bounded by its logarithmic integral.
  have hint := RIMain.parts.sum_hprof_le_integral (K := 0) (w := w) (Z := Z)
    (by norm_num) hw hwZle hPmono hP0 hPn (Φ := Φ) hΦmono hΦnn
  have hIntEq : (∫ u in w..Z,
        Φ u * (Real.log Z / (u * (Real.log u) ^ 2)) * (1 + 2 * 0 / Real.log u))
      = ∫ u in w..Z, Φ u * (Real.log Z / (u * (Real.log u) ^ 2)) := by
    refine intervalIntegral.integral_congr (fun u _ => ?_)
    simp
  rw [hIntEq] at hint
  have hint' : ∑ k ∈ Finset.range (RIMain.pSet A w Z).card,
        ((1 + ε) * RIMain.hprof 0 Z (RIMain.vEnum A w Z k)
          - (1 + ε) * RIMain.hprof 0 Z (RIMain.vEnum A w Z (k + 1)))
          * Φ (RIMain.vEnum A w Z k)
      ≤ (1 + ε) * ∫ u in w..Z, Φ u * (Real.log Z / (u * (Real.log u) ^ 2)) := by
    have h2 : ∑ k ∈ Finset.range (RIMain.pSet A w Z).card,
          ((1 + ε) * RIMain.hprof 0 Z (RIMain.vEnum A w Z k)
            - (1 + ε) * RIMain.hprof 0 Z (RIMain.vEnum A w Z (k + 1)))
            * Φ (RIMain.vEnum A w Z k)
        = (1 + ε) * ∑ k ∈ Finset.range (RIMain.pSet A w Z).card,
            (RIMain.hprof 0 Z (RIMain.vEnum A w Z k)
              - RIMain.hprof 0 Z (RIMain.vEnum A w Z (k + 1)))
              * Φ (RIMain.vEnum A w Z k) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun k _ => ?_)
      ring
    rw [h2]
    exact mul_le_mul_of_nonneg_left hint (by linarith)
  calc ∑ p ∈ A.prodPrimes.primeFactors.filter
        (fun p : ℕ => w ≤ (p : ℝ) ∧ (p : ℝ) < Z),
        A.nu p * Work.ChenPlan.LinearSieve.VfR A (p : ℝ) * Φ (p : ℝ)
      = Work.ChenPlan.LinearSieve.VfR A Z *
          ∑ k ∈ Finset.range (RIMain.pSet A w Z).card,
            (RIMain.Vnorm A Z (RIMain.vEnum A w Z k)
              - RIMain.Vnorm A Z (RIMain.vEnum A w Z (k + 1)))
              * Φ (RIMain.vEnum A w Z k) :=
        RIMain.aux.sum_nu_VfR_eq_range
    _ ≤ Work.ChenPlan.LinearSieve.VfR A Z * (ε * Φ Z
          + ∑ k ∈ Finset.range (RIMain.pSet A w Z).card,
              ((1 + ε) * RIMain.hprof 0 Z (RIMain.vEnum A w Z k)
                - (1 + ε) * RIMain.hprof 0 Z (RIMain.vEnum A w Z (k + 1)))
                * Φ (RIMain.vEnum A w Z k)) :=
        mul_le_mul_of_nonneg_left hstep' hVZnn
    _ ≤ Work.ChenPlan.LinearSieve.VfR A Z * (ε * Φ Z
          + (1 + ε) * ∫ u in w..Z, Φ u * (Real.log Z / (u * (Real.log u) ^ 2))) := by
        refine mul_le_mul_of_nonneg_left ?_ hVZnn
        linarith [hint']

end Work.ChenPlan.LinearSieve.JR2
