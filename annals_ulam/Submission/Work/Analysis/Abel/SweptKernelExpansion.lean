import Mathlib
import Submission.Work.Analysis.Abel.SweptKernelDefs
import Submission.Work.Analysis.Abel.iteratedDeriv_rpow_sub

/-!
# The Leibniz expansion of the swept kernel

Two facts about `ks A p j x σ` (the explicit Leibniz expansion of
`∂_u^j ((σ-u)^p A u σ)` at `u = x`):

* `ks_eq_iteratedDeriv` : for `x < σ` and `A` smooth near `(x,σ)`, the expansion
  actually computes the iterated derivative of the slice `u ↦ (σ-u)^p * A u σ`;
* `ks_succ_expansion` : the identity expressing `ks A p (j+1)` as the `u`-derivative
  of `ks A p j`, namely
  `Σ_i lcoef j i (σ-x)^{p-i} ∂^{j-i+1}A - Σ_i lcoef j i (p-i) (σ-x)^{p-i-1} ∂^{j-i}A
     = ks A p (j+1) x σ`.
-/

namespace Work.Analysis.Abel

noncomputable section

/-- **The Leibniz expansion computes the iterated derivative.**
For `x < σ` (so that the factor `(σ-u)^p` is smooth near `u = x`) and `A` smooth near
`(x,σ)`, the `j`-th derivative of `u ↦ (σ-u)^p * A u σ` at `x` is `ks A p j x σ`. -/
theorem ks_eq_iteratedDeriv {A : ℝ → ℝ → ℝ} {p x σ : ℝ} (h : x < σ)
    (hA : ContDiffAt ℝ (⊤ : ℕ∞) (fun q : ℝ × ℝ => A q.1 q.2) (x, σ)) (j : ℕ) :
    iteratedDeriv j (fun u : ℝ => (σ - u) ^ p * A u σ) x = ks A p j x σ := by
  change iteratedDeriv j ((fun u : ℝ => (σ - u) ^ p) * (fun u : ℝ => A u σ)) x = ks A p j x σ
  have hpow : ContDiffAt ℝ (j : ℕ∞) (fun u : ℝ => (σ - u) ^ p) x := by
    have h1 : ContDiffAt ℝ (j : ℕ∞) (fun z : ℝ => z ^ p) (σ - x) :=
      Real.contDiffAt_rpow_const_of_ne (p := p) (by linarith)
    exact h1.comp x (contDiffAt_const.sub contDiffAt_id)
  have hslice : ContDiffAt ℝ (j : ℕ∞) (fun u : ℝ => A u σ) x := by
    have h2 : ContDiffAt ℝ (⊤ : ℕ∞) (fun u : ℝ => A u σ) x := by
      simpa [Function.comp_def] using hA.comp x (contDiffAt_id.prodMk contDiffAt_const)
    exact h2.of_le (WithTop.coe_le_coe.mpr le_top)
  rw [iteratedDeriv_mul (f := fun u : ℝ => (σ - u) ^ p) (g := fun u : ℝ => A u σ) hpow hslice]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [iteratedDeriv_rpow_sub h i]
  simp only [lcoef, pder]
  ring

/-- **The recurrence for the Leibniz coefficients in the swept expansion.**
The `(j+1)`-st expansion equals the `u`-derivative of the `j`-th one:
`Σ_i lcoef j i (σ-x)^{p-i} ∂^{j-i+1}A - Σ_i lcoef j i (p-i) (σ-x)^{p-i-1} ∂^{j-i}A
   = ks A p (j+1) x σ`. -/
theorem ks_succ_expansion (A : ℝ → ℝ → ℝ) (p : ℝ) (j : ℕ) (x σ : ℝ) :
    (∑ i ∈ Finset.range (j + 1), lcoef j i p * (σ - x) ^ (p - i) * pder A (j - i + 1) x σ)
      - (∑ i ∈ Finset.range (j + 1),
          lcoef j i p * (p - i) * (σ - x) ^ (p - i - 1) * pder A (j - i) x σ)
      = ks A p (j + 1) x σ := by
  rw [ks]
  let T1 : ℕ → ℝ := fun i => lcoef j i p * (σ - x) ^ (p - i) * pder A (j - i + 1) x σ
  let T2 : ℕ → ℝ := fun i => lcoef j i p * (p - i) * (σ - x) ^ (p - i - 1) * pder A (j - i) x σ
  let T3 : ℕ → ℝ := fun i => lcoef (j + 1) i p * (σ - x) ^ (p - i) * pder A (j + 1 - i) x σ
  change (∑ i ∈ Finset.range (j + 1), T1 i) - (∑ i ∈ Finset.range (j + 1), T2 i)
      = ∑ i ∈ Finset.range (j + 2), T3 i
  have h3 : (∑ i ∈ Finset.range (j + 2), T3 i)
      = (∑ i ∈ Finset.range j, T3 (i + 1)) + T3 (j + 1) + T3 0 := by
    rw [Finset.sum_range_succ', Finset.sum_range_succ]
  have h1 : (∑ i ∈ Finset.range (j + 1), T1 i)
      = (∑ i ∈ Finset.range j, T1 (i + 1)) + T1 0 := by
    rw [Finset.sum_range_succ']
  have h2 : (∑ i ∈ Finset.range (j + 1), T2 i) = (∑ i ∈ Finset.range j, T2 i) + T2 j := by
    rw [Finset.sum_range_succ]
  have h0 : T3 0 = T1 0 := by
    simp [T1, T3, lcoef]
  have hlast : T3 (j + 1) = - T2 j := by
    simp only [T3, T2]
    have hcj : lcoef (j + 1) (j + 1) p = - (lcoef j j p * (p - (j : ℝ))) := by
      rw [lcoef_succ j j p]
      rw [show lcoef j (j + 1) p = 0 by simp [lcoef]]
      ring
    rw [hcj]
    have hidx : j + 1 - (j + 1) = j - j := by omega
    have hexp : p - ((j : ℕ) : ℝ) - 1 = p - ↑(j + 1) := by push_cast; ring
    rw [hidx, ← hexp]
    ring
  have hmid : ∀ i ∈ Finset.range j, T3 (i + 1) = T1 (i + 1) - T2 i := by
    intro i hi
    have hi' : i < j := Finset.mem_range.mp hi
    simp only [T3, T1, T2]
    rw [lcoef_succ j i p]
    have hidx : j + 1 - (i + 1) = j - (i + 1) + 1 := by omega
    have hexp : p - ((i : ℕ) : ℝ) - 1 = p - ↑(i + 1) := by push_cast; ring
    rw [hidx, ← hexp]
    have hidx2 : j - (i + 1) + 1 = j - i := by omega
    rw [hidx2]
    ring
  have hsum : (∑ i ∈ Finset.range j, T3 (i + 1))
      = (∑ i ∈ Finset.range j, T1 (i + 1)) - (∑ i ∈ Finset.range j, T2 i) := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl (fun i hi => hmid i hi)
  rw [h3, h1, h2, h0, hlast, hsum]
  ring

end

end Work.Analysis.Abel
