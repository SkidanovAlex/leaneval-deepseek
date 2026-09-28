import Mathlib

namespace Work.HP.MDEstimates

/-- `∑ d ∈ m.divisors, μ d = 1` if `m = 1` and `0` otherwise. -/
lemma moebius_sum_divisors (m : ℕ) :
    ∑ d ∈ m.divisors, (ArithmeticFunction.moebius d : ℝ) = if m = 1 then 1 else 0 := by
  have h : ((ArithmeticFunction.moebius : ArithmeticFunction ℝ) * ArithmeticFunction.zeta) m
      = (1 : ArithmeticFunction ℝ) m := by
    rw [ArithmeticFunction.coe_moebius_mul_coe_zeta]
  rw [ArithmeticFunction.coe_mul_zeta_apply, ArithmeticFunction.one_apply] at h
  rw [← h]
  refine Finset.sum_congr rfl (fun d _ => ?_)
  rw [ArithmeticFunction.intCoe_apply]

/-- For `m ∈ Icc 1 K`, the divisors of `m` that are at most `K` are exactly all of `m`'s divisors. -/
lemma Icc_filter_dvd_eq_divisors {m K : ℕ} (hm : m ∈ Finset.Icc 1 K) :
    (Finset.Icc 1 K).filter (fun l => l ∣ m) = m.divisors := by
  have hm1 : 1 ≤ m := (Finset.mem_Icc.mp hm).1
  have hmK : m ≤ K := (Finset.mem_Icc.mp hm).2
  ext l
  simp only [Finset.mem_filter, Finset.mem_Icc, Nat.mem_divisors]
  constructor
  · rintro ⟨⟨-, -⟩, hdiv⟩
    exact ⟨hdiv, by omega⟩
  · rintro ⟨hdiv, -⟩
    have hpos : 0 < l := Nat.pos_of_dvd_of_pos hdiv (by omega)
    have hlm : l ≤ m := Nat.le_of_dvd (by omega) hdiv
    exact ⟨⟨by omega, by omega⟩, hdiv⟩

/-- For `1 ≤ l`, the sum of `F` over the multiples `l * k` with `k ∈ Icc 1 K` equals the sum of `F`
over the multiples of `l` that are themselves in `Icc 1 K`.  The terms with `l * k > K` vanish by
`hF`, and `k ↦ l * k` is a bijection onto the multiples of `l` in `Icc 1 K`. -/
lemma sum_Icc_mul_eq (K l : ℕ) (hl : 1 ≤ l) (F : ℕ → ℝ) (hF : ∀ n, K < n → F n = 0) :
    ∑ k ∈ Finset.Icc 1 K, F (l * k)
      = ∑ m ∈ (Finset.Icc 1 K).filter (fun m => l ∣ m), F m := by
  have hl0 : 0 < l := hl
  have hstep1 : ∑ k ∈ Finset.Icc 1 K, F (l * k)
      = ∑ k ∈ (Finset.Icc 1 K).filter (fun k => l * k ≤ K), F (l * k) := by
    refine (Finset.sum_subset (Finset.filter_subset _ _) ?_).symm
    intro k hk hkS
    have hkK : ¬ l * k ≤ K := fun h => hkS (Finset.mem_filter.mpr ⟨hk, h⟩)
    exact hF (l * k) (Nat.lt_of_not_le hkK)
  rw [hstep1]
  refine Finset.sum_bij (fun k _ => l * k) ?_ ?_ ?_ ?_
  · intro k hk
    obtain ⟨hkI, hkle⟩ := Finset.mem_filter.mp hk
    obtain ⟨hk1, hkK⟩ := Finset.mem_Icc.mp hkI
    exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr
      ⟨by have := Nat.mul_le_mul hl hk1; simpa using this, hkle⟩, dvd_mul_right l k⟩
  · intro a₁ _ a₂ _ h
    exact Nat.mul_left_cancel hl0 h
  · intro b hb
    obtain ⟨hbI, hbdvd⟩ := Finset.mem_filter.mp hb
    obtain ⟨hb1, hbK⟩ := Finset.mem_Icc.mp hbI
    refine ⟨b / l, ?_, ?_⟩
    · refine Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨?_, ?_⟩, ?_⟩
      · exact Nat.div_pos (Nat.le_of_dvd (by omega) hbdvd) hl0
      · exact (Nat.div_le_self b l).trans hbK
      · rw [Nat.mul_div_cancel' hbdvd]; exact hbK
    · exact Nat.mul_div_cancel' hbdvd
  · intro a _
    rfl

/-- Möbius inversion in "sums over multiples" form, at the level of a finite truncation.

Let `K : ℕ` and `F : ℕ → ℝ` with `F n = 0` for `n > K`.  Then
`∑_{l=1}^{K} μ(l) * ∑_{k=1}^{K} F(l*k) = F 1`.

This is the arithmetic core of the Möbius inversion for primitive lattice points: in the intended
application `F n` is the number of primitive lattice points of norm at most `T/n`, so that
`∑_{k} F(l*k)` is the number of nonzero lattice points of norm at most `T/l`.

ROUTE (elementary; uses only Mathlib, no `sorry` imports).
Since `F m = 0` for `m > K` and `K ≥ m` for every `m ∈ Finset.Icc 1 K`, one has, for `l ∈ Icc 1 K`,
`∑_{k ∈ Icc 1 K} F (l * k) = ∑_{m ∈ Icc 1 K} (if l ∣ m then F m else 0)` : the multiples `l*k ≤ K`
correspond bijectively to the multiples `m ≤ K` of `l` (with `k = m / l ∈ Icc 1 K` because
`1 ≤ m ≤ K`), and the remaining `k` contribute `0`.  Interchanging the two sums
(`Finset.sum_comm`) gives `∑_{m ∈ Icc 1 K} F m * (∑_{l ∈ Icc 1 K, l ∣ m} μ l)`, and for
`m ∈ Icc 1 K` the inner index set `{l ∈ Icc 1 K | l ∣ m}` is exactly `m.divisors`
(any `l ∣ m` satisfies `l ≤ m ≤ K`), so the inner sum is `∑_{l ∈ m.divisors} (μ l : ℝ)`, which
vanishes for `m ≠ 1` and equals `1` for `m = 1` (e.g. from
`ArithmeticFunction.sum_eq_iff_sum_mul_moebius_eq` with `f n = if n = 1 then (1:ℝ) else 0` and
`g = fun _ => 1`, plus `Nat.sum_divisorsAntidiagonal`).  Hence the total is `F 1`.

(For `K = 0` the left side is `0` and `hF` gives `F 1 = 0`; both sides agree.)

Please put this in `Submission/Work/HP/MDEstimates/moebius_multiples_sum.lean` inside
`namespace Work.HP.MDEstimates`, so the full name is `Work.HP.MDEstimates.moebius_multiples_sum`.
It should import only Mathlib. -/
theorem moebius_multiples_sum (K : ℕ) (F : ℕ → ℝ) (hF : ∀ n, K < n → F n = 0) :
    ∑ l ∈ Finset.Icc 1 K, (ArithmeticFunction.moebius l : ℝ) *
      (∑ k ∈ Finset.Icc 1 K, F (l * k)) = F 1 := by
  trans ∑ l ∈ Finset.Icc 1 K,
      ∑ m ∈ Finset.Icc 1 K, (if l ∣ m then (ArithmeticFunction.moebius l : ℝ) * F m else 0)
  · refine Finset.sum_congr rfl (fun l hl => ?_)
    have hl1 : 1 ≤ l := (Finset.mem_Icc.mp hl).1
    rw [sum_Icc_mul_eq K l hl1 F hF, Finset.mul_sum, ← Finset.sum_filter]
  · rw [Finset.sum_comm]
    trans ∑ m ∈ Finset.Icc 1 K, (if m = 1 then F m else 0)
    · refine Finset.sum_congr rfl (fun m hm => ?_)
      rw [← Finset.sum_filter, ← Finset.sum_mul, Icc_filter_dvd_eq_divisors hm,
        moebius_sum_divisors]
      by_cases h : m = 1 <;> simp [h]
    · rw [Finset.sum_ite_eq']
      by_cases h : 1 ∈ Finset.Icc 1 K
      · rw [ite_eq_left h]
      · have hK : K < 1 := by
          simp only [Finset.mem_Icc, le_refl, true_and] at h
          omega
        rw [ite_eq_right h, hF 1 hK]

end Work.HP.MDEstimates
