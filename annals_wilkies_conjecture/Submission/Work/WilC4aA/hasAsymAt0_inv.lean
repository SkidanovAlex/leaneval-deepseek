import Mathlib
import Submission.Work.WilC4aA.Defs

open Filter Topology Set

namespace Work.WilC4aA

theorem hasAsymAt0_inv {f : ℝ → ℝ} (hf : Work.WilC4aA.HasAsymAt0 f)
    (hne : ∀ᶠ s in nhdsWithin (0 : ℝ) (Set.Ioi 0), f s ≠ 0) :
    Work.WilC4aA.HasAsymAt0 f⁻¹ := by
  rcases hf with h0 | ⟨k, b, hb, hT⟩
  · -- `f` vanishes at `0⁺` and is eventually nonzero there: impossible.
    exfalso
    have hF : ∀ᶠ s in 𝓝[>] (0 : ℝ), False := by
      filter_upwards [h0, hne] with s hs hns
      exact hns hs
    obtain ⟨s, hs⟩ := hF.exists
    exact hs
  · -- `f s / s ^ k → b ≠ 0`, so `(f s)⁻¹ / s ^ (-k) → b⁻¹`.
    refine Or.inr ⟨-k, b⁻¹, inv_ne_zero hb, ?_⟩
    have hTinv : Tendsto (fun s : ℝ => (f s / s ^ (k : ℝ))⁻¹) (𝓝[>] (0 : ℝ)) (𝓝 b⁻¹) :=
      hT.inv₀ hb
    have heq : (fun s : ℝ => (f s)⁻¹ / s ^ (((-k : ℤ)) : ℝ)) =ᶠ[𝓝[>] (0 : ℝ)]
        (fun s : ℝ => (f s / s ^ (k : ℝ))⁻¹) := by
      filter_upwards [self_mem_nhdsWithin] with s hs
      have hs0 : (0 : ℝ) < s := hs
      have h1 : s ^ (((-k : ℤ)) : ℝ) = (s ^ ((k : ℤ) : ℝ))⁻¹ := by
        rw [Int.cast_neg, Real.rpow_neg (le_of_lt hs0)]
      rw [h1, div_inv_eq_mul, inv_div, div_eq_mul_inv, mul_comm]
    exact hTinv.congr' heq.symm

end Work.WilC4aA
