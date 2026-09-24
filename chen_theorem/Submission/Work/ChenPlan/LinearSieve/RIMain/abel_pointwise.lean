import Mathlib
import Submission.Work.ChenPlan.LinearSieve.FrameworkR
import Submission.Work.ChenPlan.LinearSieve.Abel.abel_sum_le
import Submission.Work.ChenPlan.LinearSieve.Abel.abel_step_sum
import Submission.Work.ChenPlan.LinearSieve.RIMain.abel_pointwise_defs
import Submission.Work.ChenPlan.LinearSieve.RIMain.AuxLemmas.sum_nu_VfR_eq_range
import Submission.Work.ChenPlan.LinearSieve.RIMain.parts.sum_hprof_le_integral

/-!
# The pointwise Abel estimate for the linear sieve (`RIMain.abel_pointwise`)

With `V(u) = VfR A u`, `S = {p ∣ P : w ≤ p < Z}` enumerated increasingly by `p_0 < p_1 < ⋯ < p_{n-1}`
(and `p_n := Z`), the sum `Σ_{w ≤ p < Z} ν(p) V(p) Φ(p)` is `V(Z)` times the Abel sum
`Σ_{k<n} (V(p_k)/V(Z) - V(p_{k+1})/V(Z)) Φ(p_k)`.  Comparing the normalised product
`u ↦ V(u)/V(Z)` with the extremal profile `hprof K Z u = (1 + K/log u)·log Z/log u` (hypothesis
`hV`) and applying the abstract Abel comparison `Abel.abel_step_sum` gives

`Σ ν(p)V(p)Φ(p) ≤ V(Z)·[(hprof K Z Z - 1)Φ Z + Σ_k (hprof(p_k) - hprof(p_{k+1}))Φ(p_k)]`,

and the remaining sum is bounded by the logarithmic integral with density
`log Z/(u log²u)·(1 + 2K/log u) = -d/du hprof K Z u`.
-/

open Finset
open scoped BigOperators

set_option autoImplicit false

namespace Work.ChenPlan.LinearSieve.RIMain

noncomputable section

/-! ## The main theorem -/

theorem abel_pointwise {A : BoundingSieve} {w Z K : ℝ} (hK : 0 ≤ K) (hw : 2 ≤ w)
    (hwZ : w < Z)
    (hV : ∀ u : ℝ, w ≤ u → u ≤ Z →
      Work.ChenPlan.LinearSieve.VfR A u ≤ Work.ChenPlan.LinearSieve.VfR A Z *
        ((1 + K / Real.log u) * (Real.log Z / Real.log u)))
    {Φ : ℝ → ℝ} (hΦmono : ∀ a b : ℝ, w ≤ a → a ≤ b → b ≤ Z → Φ a ≤ Φ b)
    (hΦnn : ∀ a : ℝ, w ≤ a → a ≤ Z → 0 ≤ Φ a) :
    ∑ p ∈ A.prodPrimes.primeFactors.filter (fun p : ℕ => w ≤ (p : ℝ) ∧ (p : ℝ) < Z),
        A.nu p * Work.ChenPlan.LinearSieve.VfR A (p : ℝ) * Φ (p : ℝ)
      ≤ Work.ChenPlan.LinearSieve.VfR A Z * ((K / Real.log Z) * Φ Z
          + ∫ u in w..Z, Φ u * (Real.log Z / (u * (Real.log u) ^ 2)) *
              (1 + 2 * K / Real.log u)) := by
  have hwZle : w ≤ Z := le_of_lt hwZ
  have hZ1 : 1 < Z := lt_of_le_of_lt (by linarith) hwZ
  have hlogZpos : 0 < Real.log Z := Real.log_pos hZ1
  have hlogZne : Real.log Z ≠ 0 := ne_of_gt hlogZpos
  have hPmono : Monotone (vEnum A w Z) := vEnum_mono A w Z
  have hP0 : w ≤ vEnum A w Z 0 := le_vEnum A hwZle 0
  have hPn : vEnum A w Z (pSet A w Z).card = Z := vEnum_card A w Z
  have hMT : ∀ k : ℕ, k ≤ (pSet A w Z).card →
      Vnorm A Z (vEnum A w Z k) ≤ hprof K Z (vEnum A w Z k) := by
    intro k _
    exact Vnorm_le_hprof (by simpa [hprof] using hV _ (le_vEnum A hwZle k) (vEnum_le A w Z k))
  have hstep := Abel.abel_step_sum (n := (pSet A w Z).card) (P := vEnum A w Z)
    (M := Vnorm A Z) (T := hprof K Z) hPmono hP0 hPn hMT hΦmono hΦnn
  have hstep' : ∑ k ∈ Finset.range (pSet A w Z).card,
        (Vnorm A Z (vEnum A w Z k) - Vnorm A Z (vEnum A w Z (k + 1)))
          * Φ (vEnum A w Z k)
      ≤ (K / Real.log Z) * Φ Z
        + ∑ k ∈ Finset.range (pSet A w Z).card,
            (hprof K Z (vEnum A w Z k) - hprof K Z (vEnum A w Z (k + 1)))
              * Φ (vEnum A w Z k) := by
    have h1 := hstep
    rw [hprof_Z hlogZne, Vnorm_Z] at h1
    linarith [h1]
  have hsum := parts.sum_hprof_le_integral (K := K) (w := w) (Z := Z) hK hw hwZle hPmono hP0 hPn
    (Φ := Φ) hΦmono hΦnn
  calc ∑ p ∈ A.prodPrimes.primeFactors.filter (fun p : ℕ => w ≤ (p : ℝ) ∧ (p : ℝ) < Z),
        A.nu p * Work.ChenPlan.LinearSieve.VfR A (p : ℝ) * Φ (p : ℝ)
      = VfR A Z * ∑ k ∈ Finset.range (pSet A w Z).card,
          (Vnorm A Z (vEnum A w Z k) - Vnorm A Z (vEnum A w Z (k + 1)))
            * Φ (vEnum A w Z k) := aux.sum_nu_VfR_eq_range
    _ ≤ VfR A Z * ((K / Real.log Z) * Φ Z
          + ∑ k ∈ Finset.range (pSet A w Z).card,
              (hprof K Z (vEnum A w Z k) - hprof K Z (vEnum A w Z (k + 1)))
                * Φ (vEnum A w Z k)) :=
        mul_le_mul_of_nonneg_left hstep' (VfR_nonneg A Z)
    _ ≤ VfR A Z * ((K / Real.log Z) * Φ Z
          + ∫ u in w..Z, Φ u * (Real.log Z / (u * (Real.log u) ^ 2)) *
              (1 + 2 * K / Real.log u)) := by
        refine mul_le_mul_of_nonneg_left ?_ (VfR_nonneg A Z)
        linarith [hsum]

end

end Work.ChenPlan.LinearSieve.RIMain
