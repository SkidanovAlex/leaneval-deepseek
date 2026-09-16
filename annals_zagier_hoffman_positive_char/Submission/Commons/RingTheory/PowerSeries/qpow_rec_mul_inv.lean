import Mathlib.RingTheory.PowerSeries.Basic

namespace Commons.RingTheory.PowerSeries

open Finset

/-- For `q ≥ 2` and `m ≤ n`, the set of `j` with `q ^ j = m` is the same whether the bound on `j`
is `m` or `n`. -/
lemma filter_qpow_range_eq {q n m : ℕ} (hq : 2 ≤ q) (hmn : m ≤ n) :
    (Finset.range (m + 1)).filter (fun j => q ^ j = m)
      = (Finset.range (n + 1)).filter (fun j => q ^ j = m) := by
  ext j
  simp only [Finset.mem_filter, Finset.mem_range]
  constructor
  · rintro ⟨hj, hqj⟩
    exact ⟨by omega, hqj⟩
  · rintro ⟨hj, hqj⟩
    have hlt : j < q ^ j := Nat.lt_pow_self (by omega : 1 < q)
    omega

/-- The sum over pairs `(p₁, p₂)` with `p₁ ≤ n`, `p₂ ≤ n` and `q ^ p₂ = p₁` equals the sum over
`j ≤ n` with `q ^ j ≤ n`. -/
lemma sum_prod_filter_qpow {M : Type*} [AddCommMonoid M] (q n : ℕ)
    (f : ℕ → ℕ → M) :
    (∑ p ∈ ((Finset.range (n + 1)) ×ˢ (Finset.range (n + 1))).filter
        (fun p => q ^ p.2 = p.1), f p.1 p.2)
      = ∑ j ∈ (Finset.range (n + 1)).filter (fun j => q ^ j ≤ n), f (q ^ j) j := by
  apply Finset.sum_bij (fun p _ => p.2)
  · intro p hp
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range] at hp ⊢
    obtain ⟨⟨hp1, hp2⟩, hpq⟩ := hp
    exact ⟨hp2, by rw [hpq]; omega⟩
  · intro p hp p' hp' heq
    simp only [Finset.mem_filter, Finset.mem_product] at hp hp'
    obtain ⟨_, hpq⟩ := hp
    obtain ⟨_, hpq'⟩ := hp'
    have : p.1 = p'.1 := by rw [← hpq, heq, hpq']
    exact Prod.ext this heq
  · intro j hj
    simp only [Finset.mem_filter, Finset.mem_range] at hj
    obtain ⟨hj1, hj2⟩ := hj
    refine ⟨(q ^ j, j), ?_, rfl⟩
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range]
    exact ⟨⟨by omega, hj1⟩, trivial⟩
  · intro p hp
    simp only [Finset.mem_filter] at hp
    rw [hp.2]

/-- Reindexing the double sum `∑_{m ≤ n} ∑_{j : q^j = m}` as a sum over `j` with `q ^ j ≤ n`. -/
lemma sum_qpow_reindex {M : Type*} [AddCommMonoid M] (q n : ℕ) (hq : 2 ≤ q)
    (f : ℕ → ℕ → M) :
    (∑ m ∈ Finset.range (n + 1),
        ∑ j ∈ (Finset.range (m + 1)).filter (fun j => q ^ j = m), f m j)
      = ∑ j ∈ (Finset.range (n + 1)).filter (fun j => q ^ j ≤ n), f (q ^ j) j := by
  have h1 : (∑ m ∈ Finset.range (n + 1),
        ∑ j ∈ (Finset.range (m + 1)).filter (fun j => q ^ j = m), f m j)
      = (∑ m ∈ Finset.range (n + 1),
        ∑ j ∈ (Finset.range (n + 1)).filter (fun j => q ^ j = m), f m j) := by
    refine Finset.sum_congr rfl (fun m hm => ?_)
    have hmn : m ≤ n := by have h := Finset.mem_range.mp hm; omega
    rw [filter_qpow_range_eq hq hmn]
  rw [h1]
  calc
    (∑ m ∈ Finset.range (n + 1),
        ∑ j ∈ (Finset.range (n + 1)).filter (fun j => q ^ j = m), f m j)
        = ∑ m ∈ Finset.range (n + 1), ∑ j ∈ Finset.range (n + 1),
            (if q ^ j = m then f m j else 0) := by
          refine Finset.sum_congr rfl (fun m _ => ?_)
          exact Finset.sum_filter (fun j => q ^ j = m) (fun j => f m j)
    _ = ∑ p ∈ (Finset.range (n + 1) ×ˢ Finset.range (n + 1)),
          (if q ^ p.2 = p.1 then f p.1 p.2 else 0) := by
          exact (Finset.sum_product (Finset.range (n + 1)) (Finset.range (n + 1))
            (fun p : ℕ × ℕ => if q ^ p.2 = p.1 then f p.1 p.2 else 0)).symm
    _ = ∑ p ∈ ((Finset.range (n + 1) ×ˢ Finset.range (n + 1))).filter
            (fun p => q ^ p.2 = p.1), f p.1 p.2 := by
          exact (Finset.sum_filter (fun p : ℕ × ℕ => q ^ p.2 = p.1)
            (fun p => f p.1 p.2)).symm
    _ = ∑ j ∈ (Finset.range (n + 1)).filter (fun j => q ^ j ≤ n), f (q ^ j) j :=
          sum_prod_filter_qpow q n f

/-- Given `q ≥ 2`, a sequence `c` satisfying the `q`-power recursion is the inverse of
`1 - ∑_j u_j X^{q^j}`, i.e. the power series `∑ c_n X^n` multiplied by
`1 - ∑_j u_j X^{q^j}` is `1`. -/
theorem qpow_rec_mul_inv {k : Type*} [Field k] (q : ℕ) (hq : 2 ≤ q) (u c : ℕ → k)
    (h0 : c 0 = 1)
    (hrec : ∀ n, 1 ≤ n →
      c n = ∑ j ∈ (Finset.range (n + 1)).filter (fun j => q ^ j ≤ n), u j * c (n - q ^ j)) :
    PowerSeries.mk c *
      (1 - PowerSeries.mk
        (fun n => ∑ j ∈ (Finset.range (n + 1)).filter (fun j => q ^ j = n), u j)) = 1 := by
  classical
  set A : ℕ → k := fun n => ∑ j ∈ (Finset.range (n + 1)).filter (fun j => q ^ j = n), u j
    with hA
  set B : PowerSeries k := 1 - PowerSeries.mk A with hB
  have hBcoeff : ∀ m, PowerSeries.coeff m B
      = (if m = 0 then 1 else 0) - A m := by
    intro m
    rw [hB]
    simp [PowerSeries.coeff_mk]
  have hmain : ∀ n, PowerSeries.coeff n (PowerSeries.mk c * B)
      = c n - ∑ m ∈ Finset.range (n + 1), c (n - m) * A m := by
    intro n
    rw [PowerSeries.coeff_mul]
    rw [Nat.sum_antidiagonal_eq_sum_range_succ
      (fun i j => PowerSeries.coeff i (PowerSeries.mk c) * PowerSeries.coeff j B)]
    simp only [PowerSeries.coeff_mk]
    have hstep : (∑ i ∈ Finset.range (n + 1), c i * PowerSeries.coeff (n - i) B)
        = ∑ i ∈ Finset.range (n + 1),
            c i * ((if n - i = 0 then 1 else 0) - A (n - i)) := by
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [hBcoeff]
    rw [hstep]
    have hsplit : (∑ i ∈ Finset.range (n + 1),
            c i * ((if n - i = 0 then 1 else 0) - A (n - i)))
        = (∑ i ∈ Finset.range (n + 1), c i * (if n - i = 0 then 1 else 0))
          - ∑ i ∈ Finset.range (n + 1), c i * A (n - i) := by
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [mul_sub]
    rw [hsplit]
    have hconst : (∑ i ∈ Finset.range (n + 1),
          c i * (if n - i = 0 then (1 : k) else 0)) = c n := by
      have hc : (∑ i ∈ Finset.range (n + 1), c i * (if n - i = 0 then (1 : k) else 0))
          = ∑ i ∈ Finset.range (n + 1), (if i = n then c i else 0) := by
        refine Finset.sum_congr rfl (fun i hi => ?_)
        have hi' : i ≤ n := by have h := Finset.mem_range.mp hi; omega
        rcases eq_or_ne i n with hin | hin
        · subst hin; simp
        · have hni : n - i ≠ 0 := by omega
          simp [hin, hni]
      rw [hc, Finset.sum_ite_eq']
      simp
    have hrev : (∑ i ∈ Finset.range (n + 1), c i * A (n - i))
        = ∑ m ∈ Finset.range (n + 1), c (n - m) * A m := by
      refine Finset.sum_bij (fun i _ => n - i) ?_ ?_ ?_ ?_
      · intro i hi
        have hi' : i ≤ n := by have h := Finset.mem_range.mp hi; omega
        simp only [Finset.mem_range]; omega
      · intro i hi i' hi' heq
        have hi'' : i ≤ n := by have h := Finset.mem_range.mp hi; omega
        have hi''' : i' ≤ n := by have h := Finset.mem_range.mp hi'; omega
        omega
      · intro m hm
        have hm' : m ≤ n := by have h := Finset.mem_range.mp hm; omega
        refine ⟨n - m, ?_, ?_⟩
        · simp only [Finset.mem_range]; omega
        · show n - (n - m) = m
          omega
      · intro i hi
        have hi' : i ≤ n := by have h := Finset.mem_range.mp hi; omega
        show c i * A (n - i) = c (n - (n - i)) * A (n - i)
        rw [Nat.sub_sub_self hi']
    rw [hconst, hrev]
  have hsum : ∀ n, (∑ m ∈ Finset.range (n + 1), c (n - m) * A m)
      = ∑ j ∈ (Finset.range (n + 1)).filter (fun j => q ^ j ≤ n), u j * c (n - q ^ j) := by
    intro n
    have hexp : (∑ m ∈ Finset.range (n + 1), c (n - m) * A m)
        = ∑ m ∈ Finset.range (n + 1),
            ∑ j ∈ (Finset.range (m + 1)).filter (fun j => q ^ j = m), c (n - m) * u j := by
      refine Finset.sum_congr rfl (fun m _ => ?_)
      rw [hA, Finset.mul_sum]
    refine hexp.trans ?_
    refine (sum_qpow_reindex q n hq (fun m j => c (n - m) * u j)).trans ?_
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [mul_comm]
  apply PowerSeries.ext
  intro n
  rw [hmain n, hsum n, PowerSeries.coeff_one]
  rcases Nat.eq_zero_or_pos n with hn | hn
  · rw [hn]
    have hsum0 : (∑ j ∈ (Finset.range (0 + 1)).filter (fun j => q ^ j ≤ 0),
        u j * c (0 - q ^ j)) = 0 := by
      apply Finset.sum_eq_zero
      intro j hj
      simp only [Finset.mem_filter, Finset.mem_range] at hj
      have h1 : 1 ≤ q ^ j := Nat.one_le_pow j q (by omega)
      omega
    rw [hsum0, h0]
    simp
  · have hn1 : 1 ≤ n := by omega
    rw [hrec n hn1, sub_self, if_neg (by omega : ¬ n = 0)]

end Commons.RingTheory.PowerSeries