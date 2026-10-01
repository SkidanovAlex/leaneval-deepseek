import Mathlib
import Submission.Work.LinnikAreas.Density4.SsmSetup

namespace Work.LinnikAreas.Density4

theorem thetaS_Icc_eq (W : ℝ) (n : ℕ) (hn : n ≠ 0) :
    (thetaS W n : ℂ) = ∑ e ∈ Finset.Icc 1 (Nat.ceil W), (if e ∣ n then (thetaM W e : ℂ) else 0) := by
  classical
  -- terms of `thetaM` vanish beyond the cut-off `W ≤ ⌈W⌉`
  have hceil : W ≤ (Nat.ceil W : ℝ) := Nat.le_ceil W
  have hzero : ∀ d : ℕ, Nat.ceil W < d → (thetaM W d : ℂ) = 0 := by
    intro d hd
    have hWd : W < (d : ℝ) := lt_of_le_of_lt hceil (by exact_mod_cast hd)
    rw [thetaM, if_neg (not_le.mpr hWd)]
    simp
  -- the two index sets agree: positive divisors of `n` below `⌈W⌉`
  have hCD : (Finset.Icc 1 (Nat.ceil W)).filter (fun d => d ∣ n)
      = n.divisors.filter (fun d => d ≤ Nat.ceil W) := by
    ext d
    simp only [Finset.mem_filter, Finset.mem_Icc, Nat.mem_divisors]
    constructor
    · rintro ⟨⟨-, h2⟩, hdvd⟩
      exact ⟨⟨hdvd, hn⟩, h2⟩
    · rintro ⟨⟨hdvd, -⟩, h2⟩
      exact ⟨⟨Nat.pos_of_dvd_of_pos hdvd (Nat.pos_of_ne_zero hn), h2⟩, hdvd⟩
  -- the divisor sum may be truncated at `⌈W⌉`
  have hL : (∑ d ∈ n.divisors, (thetaM W d : ℂ))
      = ∑ d ∈ n.divisors.filter (fun d => d ≤ Nat.ceil W), (thetaM W d : ℂ) := by
    symm
    refine Finset.sum_subset (Finset.filter_subset _ _) ?_
    intro x hx hxn
    exact hzero x (lt_of_not_ge fun hle => hxn (Finset.mem_filter.mpr ⟨hx, hle⟩))
  -- the right-hand side is that same truncated divisor sum
  have hR : (∑ e ∈ Finset.Icc 1 (Nat.ceil W), (if e ∣ n then (thetaM W e : ℂ) else 0))
      = ∑ d ∈ n.divisors.filter (fun d => d ≤ Nat.ceil W), (thetaM W d : ℂ) := by
    rw [← Finset.sum_filter]
    exact Finset.sum_congr hCD (fun _ _ => rfl)
  rw [thetaS, Complex.ofReal_sum, hL, hR]

end Work.LinnikAreas.Density4
