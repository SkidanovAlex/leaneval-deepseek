import Mathlib
import Submission.Work.Diff.STE.Torus

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.STE.Lead

theorem CSq_trunc_sub_le_bound {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ρ : (ι → ℝ) → ℝ) (C : ℝ)
    (hρ : ∀ y : ι → ℝ, (ρ y - 1) ^ 2 ≤ C ^ 2 * ∑ i, (y i) ^ 2)
    (ε : ℝ) (hε : 0 < ε) (s : ℕ) (c : (ι → ℤ) → ℂ)
    (h : Summable (fun k : ι → ℤ => (Work.Diff.STE.wt k) ^ (s + 1) * ‖c k‖ ^ 2)) :
    Work.Diff.STE.CSq s (fun k => Work.Diff.STE.trunc ρ ε c k - c k)
      ≤ C ^ 2 * ε ^ 2 * Work.Diff.STE.CSq (s + 1) c := by
  classical
  have hεpos : 0 < ε := hε
  -- The multiplier error is `ρ (ε k) - 1`; the hypothesis `hρ` bounds its square by
  -- `C² ε² Σᵢ kᵢ²`, and `Σᵢ kᵢ² ≤ ⟨k⟩²` upgrades this to `C² ε² ⟨k⟩²`, which is exactly
  -- the gain of one Sobolev order.
  have hsum_smul : ∀ k : ι → ℤ,
      (∑ i, ((ε • (fun i => (k i : ℝ))) i) ^ 2) = ε ^ 2 * ∑ i, ((k i : ℝ)) ^ 2 := by
    intro k
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by
      simp only [Pi.smul_apply, smul_eq_mul]; ring
  have hkey : ∀ k : ι → ℤ,
      (ρ (ε • (fun i => (k i : ℝ))) - 1) ^ 2 ≤ C ^ 2 * ε ^ 2 * Work.Diff.STE.wt k := by
    intro k
    have h1 := hρ (ε • (fun i => (k i : ℝ)))
    rw [hsum_smul k] at h1
    have h4 : (∑ i, ((k i : ℝ)) ^ 2) ≤ Work.Diff.STE.wt k := by
      have hwt : Work.Diff.STE.wt k = 1 + ∑ i, ((k i : ℝ)) ^ 2 := rfl
      rw [hwt]; linarith
    have h3 : (0 : ℝ) ≤ C ^ 2 * ε ^ 2 := mul_nonneg (sq_nonneg C) (sq_nonneg ε)
    calc (ρ (ε • (fun i => (k i : ℝ))) - 1) ^ 2
        ≤ C ^ 2 * (ε ^ 2 * ∑ i, ((k i : ℝ)) ^ 2) := h1
      _ = C ^ 2 * ε ^ 2 * ∑ i, ((k i : ℝ)) ^ 2 := by ring
      _ ≤ C ^ 2 * ε ^ 2 * Work.Diff.STE.wt k := mul_le_mul_of_nonneg_left h4 h3
  -- The coefficients of the error.
  have hsub : ∀ k : ι → ℤ, Work.Diff.STE.trunc ρ ε c k - c k
      = (((ρ (ε • (fun i => (k i : ℝ))) - 1 : ℝ)) : ℂ) * c k := by
    intro k
    rw [Work.Diff.STE.trunc, Complex.ofReal_sub, Complex.ofReal_one]
    ring
  have hsq : ∀ k : ι → ℤ, ‖Work.Diff.STE.trunc ρ ε c k - c k‖ ^ 2
      = (ρ (ε • (fun i => (k i : ℝ))) - 1) ^ 2 * ‖c k‖ ^ 2 := by
    intro k
    rw [hsub k, norm_mul, mul_pow, Complex.sq_norm, Complex.normSq_ofReal]
    ring
  -- Pointwise estimate, term by term.
  have hpt : ∀ k : ι → ℤ, Work.Diff.STE.wt k ^ s * ‖Work.Diff.STE.trunc ρ ε c k - c k‖ ^ 2
      ≤ C ^ 2 * ε ^ 2 * (Work.Diff.STE.wt k ^ (s + 1) * ‖c k‖ ^ 2) := by
    intro k
    rw [hsq k]
    have hwk : (0 : ℝ) ≤ Work.Diff.STE.wt k ^ s :=
      pow_nonneg (le_of_lt (Work.Diff.STE.wt_pos k)) s
    calc Work.Diff.STE.wt k ^ s
            * ((ρ (ε • (fun i => (k i : ℝ))) - 1) ^ 2 * ‖c k‖ ^ 2)
        ≤ Work.Diff.STE.wt k ^ s * ((C ^ 2 * ε ^ 2 * Work.Diff.STE.wt k) * ‖c k‖ ^ 2) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right (hkey k) (sq_nonneg ‖c k‖)) hwk
      _ = C ^ 2 * ε ^ 2 * (Work.Diff.STE.wt k ^ (s + 1) * ‖c k‖ ^ 2) := by
          rw [pow_succ]; ring
  -- Summability and summation.
  have hGsum : Summable (fun k : ι → ℤ =>
      C ^ 2 * ε ^ 2 * (Work.Diff.STE.wt k ^ (s + 1) * ‖c k‖ ^ 2)) := h.mul_left _
  have hgsum : Summable (fun k : ι → ℤ =>
      Work.Diff.STE.wt k ^ s * ‖Work.Diff.STE.trunc ρ ε c k - c k‖ ^ 2) :=
    Summable.of_nonneg_of_le
      (fun k => mul_nonneg (pow_nonneg (le_of_lt (Work.Diff.STE.wt_pos k)) s) (sq_nonneg _))
      hpt hGsum
  have hle := Summable.tsum_le_tsum hpt hgsum hGsum
  have hCSq : Work.Diff.STE.CSq s (fun k => Work.Diff.STE.trunc ρ ε c k - c k)
      = ∑' k : ι → ℤ, Work.Diff.STE.wt k ^ s * ‖Work.Diff.STE.trunc ρ ε c k - c k‖ ^ 2 :=
    rfl
  have hfinal : (∑' k : ι → ℤ,
        C ^ 2 * ε ^ 2 * (Work.Diff.STE.wt k ^ (s + 1) * ‖c k‖ ^ 2))
      = C ^ 2 * ε ^ 2 * Work.Diff.STE.CSq (s + 1) c := by
    rw [Work.Diff.STE.CSq, tsum_mul_left]
  rw [hCSq]
  exact hle.trans (le_of_eq hfinal)

end Work.Diff.STE.Lead
