import Mathlib
import Submission.Work.LinnikAreas.RatioDefs

namespace Work.LinnikAreas

/-- For `n ∈ [1,N]`, the divisor set of `n` coincides with the divisors of `n` lying in `[1,N]`.
(Every divisor `d ≥ 1` of `n` satisfies `d ≤ n ≤ N`.) -/
lemma divisors_eq_filter_Icc {N n : ℕ} (hn : n ∈ Finset.Icc 1 N) :
    n.divisors = (Finset.Icc 1 N).filter (fun d => d ∣ n) := by
  obtain ⟨hn1, hnN⟩ := Finset.mem_Icc.mp hn
  ext d
  rw [Nat.mem_divisors, Finset.mem_filter, Finset.mem_Icc]
  constructor
  · rintro ⟨hdvd, _⟩
    exact ⟨⟨Nat.pos_of_dvd_of_pos hdvd hn1, (Nat.le_of_dvd hn1 hdvd).trans hnN⟩, hdvd⟩
  · rintro ⟨⟨hd1, _⟩, hdvd⟩
    exact ⟨hdvd, by omega⟩

/-- Divisor-sum interchange (Dirichlet hyperbola counting):
`Σ_{n ≤ N} Σ_{d | n} f d = Σ_{d ≤ N} f d · ⌊N/d⌋`, since exactly `⌊N/d⌋` multiples of `d`
lie in `[1,N]`. -/
lemma sum_divisors_eq_sum_div (N : ℕ) (f : ℕ → ℂ) :
    (∑ n ∈ Finset.Icc 1 N, ∑ d ∈ n.divisors, f d)
      = ∑ d ∈ Finset.Icc 1 N, f d * ((N / d : ℕ) : ℂ) := by
  have hIoc : Finset.Ioc 0 N = Finset.Icc 1 N := by
    ext x; simp [Finset.mem_Ioc, Finset.mem_Icc]; omega
  calc ∑ n ∈ Finset.Icc 1 N, ∑ d ∈ n.divisors, f d
      = ∑ n ∈ Finset.Icc 1 N, ∑ d ∈ (Finset.Icc 1 N).filter (fun d => d ∣ n), f d := by
        refine Finset.sum_congr rfl (fun n hn => ?_)
        rw [divisors_eq_filter_Icc hn]
    _ = ∑ n ∈ Finset.Icc 1 N, ∑ d ∈ Finset.Icc 1 N, (if d ∣ n then f d else 0) := by
        refine Finset.sum_congr rfl (fun n _ => ?_)
        rw [Finset.sum_filter]
    _ = ∑ d ∈ Finset.Icc 1 N, ∑ n ∈ Finset.Icc 1 N, (if d ∣ n then f d else 0) :=
        Finset.sum_comm
    _ = ∑ d ∈ Finset.Icc 1 N, f d * ((N / d : ℕ) : ℂ) := by
        refine Finset.sum_congr rfl (fun d _ => ?_)
        have hcard : ((Finset.Icc 1 N).filter (fun n => d ∣ n)).card = N / d := by
          rw [← hIoc, Nat.Ioc_filter_dvd_card_eq_div]
        have hfs : (∑ n ∈ Finset.Icc 1 N, (if d ∣ n then f d else 0))
            = f d * ∑ n ∈ Finset.Icc 1 N, (if d ∣ n then (1:ℂ) else 0) := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl (fun n _ => ?_)
          by_cases h : d ∣ n <;> simp [h]
        rw [hfs, Finset.sum_boole, hcard]

theorem efunAsumDiv {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (N : ℕ) :
    Work.LinnikAreas.Asum χ (N : ℝ)
      = ∑ d ∈ Finset.Icc 1 N, (χ (d : ZMod q) : ℂ) * ((N / d : ℕ) : ℂ) := by
  rw [Work.LinnikAreas.Asum_apply, Nat.floor_natCast]
  simp only [Work.LinnikAreas.lam]
  exact sum_divisors_eq_sum_div N (fun d => χ (d : ZMod q))

end Work.LinnikAreas
