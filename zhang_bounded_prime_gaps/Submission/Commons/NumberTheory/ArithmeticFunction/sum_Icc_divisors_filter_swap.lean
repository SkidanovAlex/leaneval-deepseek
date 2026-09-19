import Mathlib
import Submission.Commons.NumberTheory.ArithmeticFunction.card_fibre_prod_lcm_le

namespace Commons.NumberTheory.ArithmeticFunction

theorem sum_Icc_divisors_filter_swap {M : Type*} [AddCommMonoid M] (y T : ℕ)
    (g : ℕ → ℕ → M) :
    (∑ n ∈ Finset.Icc 1 y, ∑ d ∈ n.divisors.filter (fun d => d ≤ T), g d (n / d))
      = ∑ d ∈ Finset.Icc 1 T, ∑ h ∈ Finset.Icc 1 (y / d), g d h := by
  have h1 : (∑ n ∈ Finset.Icc 1 y, ∑ d ∈ n.divisors.filter (fun d => d ≤ T), g d (n / d))
      = ∑ x ∈ (Finset.Icc 1 y).sigma (fun n => n.divisors.filter (fun d => d ≤ T)),
          g x.2 (x.1 / x.2) :=
    Finset.sum_sigma' (Finset.Icc 1 y)
      (fun n => n.divisors.filter (fun d => d ≤ T)) (fun n d => g d (n / d))
  have h2 : (∑ d ∈ Finset.Icc 1 T, ∑ h ∈ Finset.Icc 1 (y / d), g d h)
      = ∑ x ∈ (Finset.Icc 1 T).sigma (fun d => Finset.Icc 1 (y / d)), g x.1 x.2 :=
    Finset.sum_sigma' (Finset.Icc 1 T)
      (fun d => Finset.Icc 1 (y / d)) (fun d h => g d h)
  have h3 : (∑ x ∈ (Finset.Icc 1 y).sigma (fun n => n.divisors.filter (fun d => d ≤ T)),
          g x.2 (x.1 / x.2))
      = ∑ x ∈ (Finset.Icc 1 T).sigma (fun d => Finset.Icc 1 (y / d)), g x.1 x.2 := by
    refine Finset.sum_bij
      (fun (x : Σ _ : ℕ, ℕ)
        (_ : x ∈ (Finset.Icc 1 y).sigma (fun n => n.divisors.filter (fun d => d ≤ T))) =>
          (⟨x.2, x.1 / x.2⟩ : Σ _ : ℕ, ℕ)) ?_ ?_ ?_ ?_
    · rintro ⟨n, d⟩ hx
      have hn : n ∈ Finset.Icc 1 y := (Finset.mem_sigma.mp hx).1
      have hdfil : d ∈ n.divisors.filter (fun d => d ≤ T) := (Finset.mem_sigma.mp hx).2
      have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
      have hny : n ≤ y := (Finset.mem_Icc.mp hn).2
      have hdmem : d ∈ n.divisors := (Finset.mem_filter.mp hdfil).1
      have hdle : d ≤ T := (Finset.mem_filter.mp hdfil).2
      have hdvd : d ∣ n := (Nat.mem_divisors.mp hdmem).1
      have hnpos : 0 < n := by omega
      have hdpos : 0 < d := Nat.pos_of_dvd_of_pos hdvd hnpos
      have hdle_n : d ≤ n := Nat.le_of_dvd hnpos hdvd
      refine Finset.mem_sigma.mpr ⟨?_, ?_⟩
      · show d ∈ Finset.Icc 1 T
        exact Finset.mem_Icc.mpr ⟨Nat.succ_le_of_lt hdpos, hdle⟩
      · show n / d ∈ Finset.Icc 1 (y / d)
        exact Finset.mem_Icc.mpr
          ⟨(Nat.one_le_div_iff hdpos).mpr hdle_n, Nat.div_le_div_right hny⟩
    · rintro ⟨n₁, d₁⟩ hx₁ ⟨n₂, d₂⟩ hx₂ heq
      obtain ⟨hd0, hq⟩ := Sigma.mk.inj_iff.mp heq
      have hd : d₁ = d₂ := hd0
      have hq' : n₁ / d₁ = n₂ / d₂ := eq_of_heq hq
      have hdf₁ : d₁ ∈ n₁.divisors.filter (fun d => d ≤ T) := (Finset.mem_sigma.mp hx₁).2
      have hdmem₁ : d₁ ∈ n₁.divisors := (Finset.mem_filter.mp hdf₁).1
      have hdvd₁ : d₁ ∣ n₁ := (Nat.mem_divisors.mp hdmem₁).1
      have hdf₂ : d₂ ∈ n₂.divisors.filter (fun d => d ≤ T) := (Finset.mem_sigma.mp hx₂).2
      have hdmem₂ : d₂ ∈ n₂.divisors := (Finset.mem_filter.mp hdf₂).1
      have hdvd₂ : d₂ ∣ n₂ := (Nat.mem_divisors.mp hdmem₂).1
      have hn : n₁ = n₂ := by
        calc n₁ = d₁ * (n₁ / d₁) := (Nat.mul_div_cancel' hdvd₁).symm
          _ = d₁ * (n₂ / d₂) := by rw [hq']
          _ = d₂ * (n₂ / d₂) := by rw [hd]
          _ = n₂ := Nat.mul_div_cancel' hdvd₂
      rw [hn, hd]
    · rintro ⟨d, h⟩ hy
      have hyd : d ∈ Finset.Icc 1 T := (Finset.mem_sigma.mp hy).1
      have hyh : h ∈ Finset.Icc 1 (y / d) := (Finset.mem_sigma.mp hy).2
      have hd1 : 1 ≤ d := (Finset.mem_Icc.mp hyd).1
      have hdT : d ≤ T := (Finset.mem_Icc.mp hyd).2
      have hh1 : 1 ≤ h := (Finset.mem_Icc.mp hyh).1
      have hhy : h ≤ y / d := (Finset.mem_Icc.mp hyh).2
      have hdpos : 0 < d := by omega
      have hdh_le : d * h ≤ y := by
        have haux := (Nat.le_div_iff_mul_le hdpos).mp hhy
        rwa [Nat.mul_comm] at haux
      refine ⟨⟨d * h, d⟩, ?_, ?_⟩
      · refine Finset.mem_sigma.mpr ⟨?_, ?_⟩
        · show d * h ∈ Finset.Icc 1 y
          exact Finset.mem_Icc.mpr ⟨by nlinarith, hdh_le⟩
        · show d ∈ (d * h).divisors.filter (fun d => d ≤ T)
          exact Finset.mem_filter.mpr
            ⟨Nat.mem_divisors.mpr ⟨dvd_mul_right d h, by positivity⟩, hdT⟩
      · refine Sigma.ext rfl ?_
        exact heq_of_eq (Nat.mul_div_right h hdpos)
    · intro x hx
      rfl
  exact h1.trans (h3.trans h2.symm)

end Commons.NumberTheory.ArithmeticFunction
