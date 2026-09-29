import Mathlib

open Filter
open scoped Nat

namespace Work.OdeCont

theorem tsum_uniform {V : Type*} [NormedAddCommGroup V] [CompleteSpace V]
    (X : ℕ → ℂ → V) (S : Set ℂ) (B c : ℝ) (hB : 0 ≤ B) (hc : 0 ≤ c)
    (h : ∀ n z, z ∈ S → ‖X (n+1) z - X n z‖ ≤ B * c ^ n / n !) :
    TendstoUniformlyOn X (fun z => X 0 z + ∑' n, (X (n+1) z - X n z)) atTop S := by
  have hu : Summable (fun n : ℕ => B * c ^ n / (n ! : ℝ)) := by
    simpa [mul_div_assoc] using (Real.summable_pow_div_factorial c).mul_left B
  have hP : TendstoUniformlyOn (fun N z => ∑ n ∈ Finset.range N, (X (n+1) z - X n z))
      (fun z => ∑' n, (X (n+1) z - X n z)) atTop S :=
    tendstoUniformlyOn_tsum_nat hu (fun n z hz => h n z hz)
  rw [Metric.tendstoUniformlyOn_iff] at hP ⊢
  intro ε hε
  filter_upwards [hP ε hε] with N hN x hx
  rw [Finset.eq_sum_range_sub (fun n => X n x) N]
  exact (dist_add_left _ _ _).trans_lt (hN x hx)

end Work.OdeCont
