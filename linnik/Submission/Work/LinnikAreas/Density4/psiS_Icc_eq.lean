import Mathlib
import Submission.Work.LinnikAreas.Density4.SsmSetup

namespace Work.LinnikAreas.Density4

open scoped BigOperators

/-- `ψ_d` vanishes for `d > V` (indeed for `d > ⌈V⌉`): it is the "else" branch of `psiM`. -/
private lemma psiM_eq_zero_of_ceil_lt {U V : ℝ} (hUV : U ≤ V) {d : ℕ} (hd : Nat.ceil V < d) :
    psiM U V d = 0 := by
  have hVd : V < (d : ℝ) := by
    have h1 := Nat.le_ceil V
    have h2 : (Nat.ceil V : ℝ) < (d : ℝ) := by exact_mod_cast hd
    linarith
  have h1 : ¬ ((d : ℝ) ≤ U) := by linarith
  have h2 : ¬ ((d : ℝ) ≤ V) := by linarith
  rw [psiM, if_neg h1, if_neg h2]

theorem psiS_Icc_eq (U V : ℝ) (hU : 0 < U) (hUV : U ≤ V) (n : ℕ) (hn : n ≠ 0) :
    (psiS U V n : ℂ) = ∑ d ∈ Finset.Icc 1 (Nat.ceil V), (if d ∣ n then (psiM U V d : ℂ) else 0) := by
  have hM : ∀ d : ℕ, Nat.ceil V < d → psiM U V d = 0 := fun d => psiM_eq_zero_of_ceil_lt hUV
  -- the range `{1,…,⌈V⌉}` cut by divisibility is the divisor set cut by `d ≤ ⌈V⌉`
  have hset : (Finset.Icc 1 (Nat.ceil V)).filter (fun d => d ∣ n)
      = n.divisors.filter (fun d => d ≤ Nat.ceil V) := by
    ext d
    simp only [Finset.mem_filter, Finset.mem_Icc, Nat.mem_divisors]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩
      exact ⟨⟨h3, hn⟩, h2⟩
    · rintro ⟨⟨h3, _⟩, h2⟩
      have hd1 : 1 ≤ d := Nat.pos_of_dvd_of_pos h3 (Nat.pos_of_ne_zero hn)
      exact ⟨⟨hd1, h2⟩, h3⟩
  rw [psiS, Complex.ofReal_sum]
  rw [← Finset.sum_filter, hset]
  exact (Finset.sum_subset (Finset.filter_subset _ _) (fun x hx hxnot => by
    have hxnot' : ¬ (x ≤ Nat.ceil V) := by
      intro hle; exact hxnot (Finset.mem_filter.mpr ⟨hx, hle⟩)
    rw [hM x (Nat.lt_of_not_le hxnot')]
    simp)).symm

end Work.LinnikAreas.Density4
