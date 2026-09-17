import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Data.Nat.Choose.Cast

namespace Commons.Algebra.Lie

open Finset

set_option linter.unusedSectionVars false

variable {R L : Type*} [Field R] [CharZero R] [LieRing L] [LieAlgebra R L]

/-! ### The truncated exponential of a locally nilpotent inner derivation -/

/-- The truncated exponential of the inner derivation `ad x`: `∑_{n<N} (ad x)ⁿ / n!`. -/
noncomputable def expAdTrunc (x : L) (N : ℕ) : L →ₗ[R] L :=
  ∑ n ∈ range N, ((n.factorial : R))⁻¹ • ((LieAlgebra.ad R L x) ^ n)

/-- The truncated exponential of `-ad x`: `∑_{n<N} (-1)ⁿ (ad x)ⁿ / n!`. -/
noncomputable def expNegAdTrunc (x : L) (N : ℕ) : L →ₗ[R] L :=
  ∑ n ∈ range N, (((-1 : R) ^ n) * ((n.factorial : R))⁻¹) • ((LieAlgebra.ad R L x) ^ n)

@[simp] lemma expAdTrunc_apply (x : L) (N : ℕ) (y : L) :
    expAdTrunc (R := R) x N y
      = ∑ n ∈ range N, ((n.factorial : R))⁻¹ • (((LieAlgebra.ad R L x) ^ n) y) := by
  simp [expAdTrunc]

@[simp] lemma expNegAdTrunc_apply (x : L) (N : ℕ) (y : L) :
    expNegAdTrunc (R := R) x N y
      = ∑ n ∈ range N, (((-1 : R) ^ n) * ((n.factorial : R))⁻¹)
          • (((LieAlgebra.ad R L x) ^ n) y) := by
  simp [expNegAdTrunc]

lemma ad_pow_eq_zero_of_le {x : L} {y : L} {N M : ℕ}
    (h : ((LieAlgebra.ad R L x)^N) y = 0) (hNM : N ≤ M) :
    ((LieAlgebra.ad R L x)^M) y = 0 := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hNM
  rw [Nat.add_comm, pow_add, Module.End.mul_apply, h, map_zero]

lemma ad_pow_ad_pow_apply (x : L) (m n : ℕ) (y : L) :
    (((LieAlgebra.ad R L x)^m) (((LieAlgebra.ad R L x)^n) y))
      = (((LieAlgebra.ad R L x)^n) (((LieAlgebra.ad R L x)^m) y)) := by
  rw [← Module.End.mul_apply, ← Module.End.mul_apply, ← pow_add, ← pow_add, Nat.add_comm]

lemma expAdTrunc_eq_of_le {x : L} {y : L} {N M : ℕ}
    (h : ((LieAlgebra.ad R L x)^N) y = 0) (hNM : N ≤ M) :
    expAdTrunc (R := R) x N y = expAdTrunc (R := R) x M y := by
  simp only [expAdTrunc_apply]
  refine sum_subset (fun n hn => by simp only [mem_range] at *; omega) ?_
  intro n hnM hnN
  rw [mem_range] at hnM
  simp only [mem_range, not_lt] at hnN
  rw [ad_pow_eq_zero_of_le h hnN, smul_zero]

lemma ad_pow_expAdTrunc (x : L) (m N : ℕ) (y : L) :
    (((LieAlgebra.ad R L x)^m) (expAdTrunc (R:=R) x N y))
      = expAdTrunc (R:=R) x N (((LieAlgebra.ad R L x)^m) y) := by
  simp only [expAdTrunc_apply, map_sum, map_smul]
  exact Finset.sum_congr rfl fun n _ => by rw [ad_pow_ad_pow_apply]

/-! ### Coefficient identities -/

lemma sum_alternating_choose (n : ℕ) :
    ∑ k ∈ range (n + 1), ((-1 : R) ^ k) * (n.choose k : R) = if n = 0 then 1 else 0 := by
  have h : ((∑ k ∈ range (n + 1), ((-1 : ℤ) ^ k) * (n.choose k : ℤ) : ℤ) : R)
      = ((if n = 0 then (1 : ℤ) else 0 : ℤ) : R) := by
    rw [Int.alternating_sum_range_choose]
  push_cast at h
  simpa using h

lemma inv_factorial_mul_choose (m k : ℕ) (hk : k ≤ m) :
    ((m.factorial : R))⁻¹ * (m.choose k : R)
      = ((k.factorial : R))⁻¹ * ((m - k).factorial : R)⁻¹ := by
  rw [Nat.cast_choose R hk, div_eq_mul_inv, mul_inv_rev, ← mul_assoc,
    inv_mul_cancel₀ (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero m)), one_mul, mul_comm]

lemma coeff_eq {m k l : ℕ} (h : k + l = m) :
    ((m.factorial : R))⁻¹ * (m.choose k : R)
      = ((k.factorial : R))⁻¹ * ((l.factorial : R))⁻¹ := by
  subst h
  rw [inv_factorial_mul_choose (k + l) k (Nat.le_add_right k l), Nat.add_sub_cancel_left]

lemma sum_alternating_conv (m : ℕ) (hm : 0 < m) :
    ∑ k ∈ range (m + 1), ((-1 : R)^k * ((k.factorial : R))⁻¹) * (((m - k).factorial : R))⁻¹
      = 0 := by
  have hterm : ∀ k ∈ range (m+1), ((-1 : R)^k * ((k.factorial : R))⁻¹) * (((m - k).factorial : R))⁻¹
      = ((m.factorial : R))⁻¹ * (((-1 : R)^k) * (m.choose k : R)) := by
    intro k hk
    rw [mem_range] at hk
    rw [mul_assoc, ← inv_factorial_mul_choose m k (by omega)]
    ring
  rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum, sum_alternating_choose m,
    if_neg (by omega), mul_zero]

/-! ### Reindexing lemmas for finset sums -/

lemma filter_prod_eq_antidiagonal {M K m : ℕ} (hM : m < M) (hK : m < K) :
    ((range M ×ˢ range K).filter (fun p : ℕ × ℕ => p.1 + p.2 = m)) = antidiagonal m := by
  ext p
  simp only [mem_filter, mem_product, mem_range, HasAntidiagonal.mem_antidiagonal]
  constructor
  · exact fun h => h.2
  · intro h
    exact ⟨⟨by omega, by omega⟩, h⟩

lemma sum_antidiagonal_eq_sum_product {A : Type*} [AddCommMonoid A] {Len : ℕ} {s : ℕ × ℕ → A}
    (hs : ∀ p, Len ≤ p.1 + p.2 → s p = 0) :
    ∑ m ∈ range Len, ∑ p ∈ antidiagonal m, s p = ∑ p ∈ range Len ×ˢ range Len, s p := by
  have h1 : ∑ m ∈ range Len, ∑ p ∈ antidiagonal m, s p
      = ∑ m ∈ range Len, ∑ p ∈ (range Len ×ˢ range Len).filter (fun p => p.1 + p.2 = m), s p :=
    Finset.sum_congr rfl fun m hm => by
      rw [mem_range] at hm
      rw [filter_prod_eq_antidiagonal hm hm]
  have hfib : ∑ p ∈ range Len ×ˢ range Len, s p
      = ∑ m ∈ range (Len + Len), ∑ p ∈ (range Len ×ˢ range Len).filter
          (fun p => p.1 + p.2 = m), s p :=
    (sum_fiberwise_of_maps_to (s := range Len ×ˢ range Len) (t := range (Len + Len))
      (g := fun p : ℕ × ℕ => p.1 + p.2)
      (fun p hp => by
        simp only [mem_product, mem_range] at hp
        exact mem_range.mpr (by omega)) s).symm
  have h2 : ∑ m ∈ range Len, ∑ p ∈ (range Len ×ˢ range Len).filter (fun p => p.1 + p.2 = m), s p
      = ∑ m ∈ range (Len + Len), ∑ p ∈ (range Len ×ˢ range Len).filter
          (fun p => p.1 + p.2 = m), s p := by
    refine sum_subset ?_ ?_
    · intro m hm
      simp only [mem_range] at hm
      exact mem_range.mpr (by omega)
    · intro m hm hmL
      simp only [mem_range] at hmL
      rw [Finset.sum_eq_zero]
      intro p hp
      rw [Finset.mem_filter] at hp
      exact hs p (by have := hp.2; omega)
  rw [h1, h2, ← hfib]

/-! ### The convolution identity -/

lemma sum_sum_smul_eq_of_conv {a b : ℕ → R} {u : ℕ → L} {M K N : ℕ} (hN : 0 < N)
    (hu : ∀ m, N ≤ m → u m = 0) (hMN : N ≤ M) (hKN : N ≤ K)
    (h0 : a 0 * b 0 = 1)
    (hconv : ∀ m, 0 < m → m < N → ∑ k ∈ range (m + 1), a k * b (m - k) = 0) :
    ∑ k ∈ range M, ∑ l ∈ range K, (a k * b l) • u (k + l) = u 0 := by
  rw [← Finset.sum_product']
  have h1 : ∑ p ∈ range M ×ˢ range K, (a p.1 * b p.2) • u (p.1 + p.2)
      = ∑ m ∈ range (M + K), ∑ p ∈ (range M ×ˢ range K).filter (fun p => p.1 + p.2 = m),
          (a p.1 * b p.2) • u (p.1 + p.2) :=
    (sum_fiberwise_of_maps_to
      (fun p hp => by simp only [mem_product, mem_range] at hp; simp only [mem_range]; omega) _).symm
  have h2 : ∑ m ∈ range (M + K), ∑ p ∈ (range M ×ˢ range K).filter (fun p => p.1 + p.2 = m),
          (a p.1 * b p.2) • u (p.1 + p.2)
      = ∑ m ∈ range (M + K),
          (∑ p ∈ (range M ×ˢ range K).filter (fun p => p.1 + p.2 = m), a p.1 * b p.2) • u m := by
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [Finset.sum_smul]
    refine Finset.sum_congr rfl fun p hp => ?_
    rw [(Finset.mem_filter.mp hp).2]
  have h3 : ∑ m ∈ range N, (∑ p ∈ (range M ×ˢ range K).filter (fun p => p.1 + p.2 = m),
        a p.1 * b p.2) • u m
      = ∑ m ∈ range (M + K), (∑ p ∈ (range M ×ˢ range K).filter (fun p => p.1 + p.2 = m),
        a p.1 * b p.2) • u m := by
    refine sum_subset (fun m hm => by simp only [mem_range] at *; omega) ?_
    intro m hm hmN
    simp only [mem_range] at hm
    rw [hu m (by simp only [mem_range] at hmN; omega), smul_zero]
  have h4 : ∀ m ∈ range N, ((∑ p ∈ (range M ×ˢ range K).filter (fun p => p.1 + p.2 = m),
        a p.1 * b p.2) • u m) = (∑ k ∈ range (m + 1), a k * b (m - k)) • u m := by
    intro m hm
    rw [mem_range] at hm
    congr 1
    rw [filter_prod_eq_antidiagonal (by omega) (by omega)]
    exact Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun k l => a k * b l) m
  have h5 : ∀ m ∈ range N, (∑ k ∈ range (m + 1), a k * b (m - k)) • u m
      = (if m = 0 then (1 : R) else 0) • u m := by
    intro m hm
    rw [mem_range] at hm
    rcases Nat.eq_zero_or_pos m with h | h
    · subst h
      rw [sum_range_one, tsub_zero, h0, if_pos rfl]
    · rw [hconv m h (by omega), if_neg (by omega), zero_smul]
  rw [h1, h2, ← h3, Finset.sum_congr rfl h4, Finset.sum_congr rfl h5,
    Finset.sum_eq_single 0]
  · simp
  · intro b hb hb0
    rw [if_neg hb0, zero_smul]
  · intro h
    exact absurd (mem_range.mpr hN) h

/-! ### Multiplicativity of the truncated exponential -/

lemma expAdTrunc_bracket (x y z : L) (N : ℕ)
    (hy : ((LieAlgebra.ad R L x)^N) y = 0) (hz : ((LieAlgebra.ad R L x)^N) z = 0) :
    expAdTrunc (R := R) x (2 * N) ⁅y, z⁆
      = ⁅expAdTrunc (R := R) x N y, expAdTrunc (R := R) x N z⁆ := by
  have hL : expAdTrunc (R := R) x (2 * N) ⁅y, z⁆
      = ∑ p ∈ range (2*N) ×ˢ range (2*N),
          (((p.1.factorial : R))⁻¹ * ((p.2.factorial : R))⁻¹)
            • ⁅((LieAlgebra.ad R L x)^p.1) y, ((LieAlgebra.ad R L x)^p.2) z⁆ := by
    rw [expAdTrunc_apply]
    have h1 : ∀ m ∈ range (2*N),
        ((m.factorial : R))⁻¹ • (((LieAlgebra.ad R L x)^m) ⁅y, z⁆)
        = ∑ p ∈ antidiagonal m, (((p.1.factorial : R))⁻¹ * ((p.2.factorial : R))⁻¹)
            • ⁅((LieAlgebra.ad R L x)^p.1) y, ((LieAlgebra.ad R L x)^p.2) z⁆ := by
      intro m _
      rw [LieAlgebra.ad_pow_lie R x y z m, Finset.smul_sum]
      refine Finset.sum_congr rfl fun p hp => ?_
      rw [← Nat.cast_smul_eq_nsmul R, smul_smul, coeff_eq (by simpa using hp)]
    rw [Finset.sum_congr rfl h1]
    exact sum_antidiagonal_eq_sum_product (Len := 2*N) (s := fun p =>
        (((p.1.factorial : R))⁻¹ * ((p.2.factorial : R))⁻¹)
            • ⁅((LieAlgebra.ad R L x)^p.1) y, ((LieAlgebra.ad R L x)^p.2) z⁆)
      (fun p hp => by
        by_cases h : N ≤ p.1
        · rw [ad_pow_eq_zero_of_le hy h, zero_lie, smul_zero]
        · rw [ad_pow_eq_zero_of_le hz (by omega), lie_zero, smul_zero])
  have hL2 : ∑ p ∈ range (2*N) ×ˢ range (2*N),
          (((p.1.factorial : R))⁻¹ * ((p.2.factorial : R))⁻¹)
            • ⁅((LieAlgebra.ad R L x)^p.1) y, ((LieAlgebra.ad R L x)^p.2) z⁆
      = ∑ p ∈ range N ×ˢ range N,
          (((p.1.factorial : R))⁻¹ * ((p.2.factorial : R))⁻¹)
            • ⁅((LieAlgebra.ad R L x)^p.1) y, ((LieAlgebra.ad R L x)^p.2) z⁆ := by
    refine (sum_subset ?_ ?_).symm
    · intro p hp
      simp only [mem_product, mem_range] at hp ⊢
      omega
    · intro p hp hp'
      simp only [mem_product, mem_range] at hp hp'
      have h : N ≤ p.1 ∨ N ≤ p.2 := by omega
      rcases h with h | h
      · rw [ad_pow_eq_zero_of_le hy h, zero_lie, smul_zero]
      · rw [ad_pow_eq_zero_of_le hz h, lie_zero, smul_zero]
  have hR : ⁅expAdTrunc (R := R) x N y, expAdTrunc (R := R) x N z⁆
      = ∑ p ∈ range N ×ˢ range N,
          (((p.1.factorial : R))⁻¹ * ((p.2.factorial : R))⁻¹)
            • ⁅((LieAlgebra.ad R L x)^p.1) y, ((LieAlgebra.ad R L x)^p.2) z⁆ := by
    simp only [expAdTrunc_apply]
    rw [sum_lie]
    have hinner : ∀ i ∈ range N,
        ⁅((i.factorial : R))⁻¹ • (((LieAlgebra.ad R L x)^i) y),
          ∑ j ∈ range N, ((j.factorial : R))⁻¹ • (((LieAlgebra.ad R L x)^j) z)⁆
        = ∑ j ∈ range N, (((i.factorial : R))⁻¹ * ((j.factorial : R))⁻¹)
            • ⁅((LieAlgebra.ad R L x)^i) y, ((LieAlgebra.ad R L x)^j) z⁆ := by
      intro i _
      rw [lie_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [smul_lie, lie_smul, smul_smul]
    rw [Finset.sum_congr rfl hinner]
    exact (Finset.sum_product' (range N) (range N) (fun i j =>
      (((i.factorial : R))⁻¹ * ((j.factorial : R))⁻¹)
        • ⁅((LieAlgebra.ad R L x)^i) y, ((LieAlgebra.ad R L x)^j) z⁆)).symm
  rw [hL, hL2, ← hR]

/-! ### The truncated exponential of `-ad x` and the two composition laws -/

lemma ad_pow_expNegAdTrunc (x : L) (m N : ℕ) (y : L) :
    (((LieAlgebra.ad R L x)^m) (expNegAdTrunc (R:=R) x N y))
      = expNegAdTrunc (R:=R) x N (((LieAlgebra.ad R L x)^m) y) := by
  simp only [expNegAdTrunc_apply, map_sum, map_smul]
  exact Finset.sum_congr rfl fun n _ => by rw [ad_pow_ad_pow_apply]

lemma expNegAdTrunc_eq_of_le {x : L} {y : L} {N M : ℕ}
    (h : ((LieAlgebra.ad R L x)^N) y = 0) (hNM : N ≤ M) :
    expNegAdTrunc (R := R) x N y = expNegAdTrunc (R := R) x M y := by
  simp only [expNegAdTrunc_apply]
  refine sum_subset (fun n hn => by simp only [mem_range] at *; omega) ?_
  intro n hnM hnN
  simp only [mem_range, not_lt] at hnN
  rw [ad_pow_eq_zero_of_le h hnN, smul_zero]

lemma expNegAdTrunc_expAdTrunc {x y : L} {N M K : ℕ} (hN : 0 < N)
    (h : ((LieAlgebra.ad R L x)^N) y = 0) (hMN : N ≤ M) (hKN : N ≤ K) :
    expNegAdTrunc (R := R) x M (expAdTrunc (R := R) x K y) = y := by
  have hstep : ∀ k ∈ range M,
      (((-1 : R)^k) * ((k.factorial : R))⁻¹)
          • (((LieAlgebra.ad R L x)^k) (expAdTrunc (R:=R) x K y))
      = ∑ l ∈ range K, ((((-1 : R)^k) * ((k.factorial : R))⁻¹) * ((l.factorial : R))⁻¹)
          • (((LieAlgebra.ad R L x)^(k+l)) y) := by
    intro k _
    rw [ad_pow_expAdTrunc, expAdTrunc_apply, Finset.smul_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [smul_smul, ← Module.End.mul_apply, ← pow_add, Nat.add_comm]
  rw [expNegAdTrunc_apply, Finset.sum_congr rfl hstep]
  have hmain := sum_sum_smul_eq_of_conv (M := M) (K := K) (N := N)
      (a := fun k => (-1 : R)^k * ((k.factorial : R))⁻¹)
      (b := fun l => ((l.factorial : R))⁻¹)
      (u := fun m => (((LieAlgebra.ad R L x)^m) y))
      hN (fun m hm => ad_pow_eq_zero_of_le h hm) hMN hKN
      (by rw [pow_zero, one_mul, Nat.factorial_zero, Nat.cast_one, inv_one, mul_one])
      (fun m hm _ => sum_alternating_conv m hm)
  rw [hmain, pow_zero, Module.End.one_apply]

lemma expAdTrunc_expNegAdTrunc {x y : L} {N M K : ℕ} (hN : 0 < N)
    (h : ((LieAlgebra.ad R L x)^N) y = 0) (hMN : N ≤ M) (hKN : N ≤ K) :
    expAdTrunc (R := R) x M (expNegAdTrunc (R := R) x K y) = y := by
  have hstep : ∀ k ∈ range M,
      ((k.factorial : R))⁻¹ • (((LieAlgebra.ad R L x)^k) (expNegAdTrunc (R:=R) x K y))
      = ∑ l ∈ range K, (((k.factorial : R))⁻¹ * (((-1 : R)^l) * ((l.factorial : R))⁻¹))
          • (((LieAlgebra.ad R L x)^(k+l)) y) := by
    intro k _
    rw [ad_pow_expNegAdTrunc, expNegAdTrunc_apply, Finset.smul_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [smul_smul, ← Module.End.mul_apply, ← pow_add, Nat.add_comm]
  rw [expAdTrunc_apply, Finset.sum_congr rfl hstep, Finset.sum_comm]
  rw [Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun k _ => by
    rw [mul_comm, Nat.add_comm]]
  have hmain := sum_sum_smul_eq_of_conv (M := K) (K := M) (N := N)
      (a := fun l => (-1 : R)^l * ((l.factorial : R))⁻¹)
      (b := fun k => ((k.factorial : R))⁻¹)
      (u := fun m => (((LieAlgebra.ad R L x)^m) y))
      hN (fun m hm => ad_pow_eq_zero_of_le h hm) hKN hMN
      (by rw [pow_zero, one_mul, Nat.factorial_zero, Nat.cast_one, inv_one, mul_one])
      (fun m hm _ => sum_alternating_conv m hm)
  rw [hmain, pow_zero, Module.End.one_apply]

lemma ad_pow_two_mul_bracket_eq_zero {x y z : L} {M : ℕ}
    (hy : ((LieAlgebra.ad R L x)^M) y = 0) (hz : ((LieAlgebra.ad R L x)^M) z = 0) :
    ((LieAlgebra.ad R L x)^(2*M)) ⁅y,z⁆ = 0 := by
  rw [LieAlgebra.ad_pow_lie R x y z (2*M)]
  refine Finset.sum_eq_zero fun p hp => ?_
  simp only [HasAntidiagonal.mem_antidiagonal] at hp
  rcases lt_or_ge p.1 M with h | h
  · rw [ad_pow_eq_zero_of_le hz (by omega), lie_zero, nsmul_zero]
  · rw [ad_pow_eq_zero_of_le hy h, zero_lie, nsmul_zero]

/-! ### The exponential map attached to a locally nilpotent inner derivation -/

section Assembly

variable (x : L) (hloc : ∀ y : L, ∃ n : ℕ, ((LieAlgebra.ad R L x)^n) y = 0)

/-- The canonical truncation index of the exponential series of `ad x` at `y`: the least `n`
with `(ad x)ⁿ y = 0`. -/
noncomputable def expAdIndex (y : L) : ℕ := by
  classical
  exact Nat.find (hloc y)

lemma ad_pow_expAdIndex (y : L) :
    ((LieAlgebra.ad R L x) ^ (expAdIndex x hloc y)) y = 0 := by
  classical
  rw [expAdIndex]
  exact Nat.find_spec (hloc y)

lemma expAdIndex_le {y : L} {n : ℕ} (h : ((LieAlgebra.ad R L x) ^ n) y = 0) :
    expAdIndex x hloc y ≤ n := by
  classical
  rw [expAdIndex]
  exact Nat.find_min' (hloc y) h

lemma expAdIndex_pos {y : L} (hy : y ≠ 0) : 0 < expAdIndex x hloc y := by
  classical
  rw [expAdIndex]
  refine Nat.pos_of_ne_zero fun hzero => hy ?_
  have := Nat.find_spec (hloc y)
  rw [hzero] at this
  simpa using this

lemma expAdIndex_zero : expAdIndex x hloc (0 : L) = 0 :=
  Nat.eq_zero_of_le_zero (expAdIndex_le x hloc (n := 0) (by simp))

/-- The (locally finite) exponential `exp (ad x)`. -/
noncomputable def expAdMap (y : L) : L :=
  expAdTrunc (R := R) x (expAdIndex x hloc y) y

/-- The (locally finite) exponential `exp (-ad x)`. -/
noncomputable def expNegAdMap (y : L) : L :=
  expNegAdTrunc (R := R) x (expAdIndex x hloc y) y

@[simp] lemma expAdMap_apply (y : L) :
    expAdMap x hloc y
      = ∑ n ∈ range (expAdIndex x hloc y), ((n.factorial : R))⁻¹
          • (((LieAlgebra.ad R L x)^n) y) := by
  rw [expAdMap, expAdTrunc_apply]

@[simp] lemma expNegAdMap_apply (y : L) :
    expNegAdMap x hloc y
      = ∑ n ∈ range (expAdIndex x hloc y), (((-1 : R)^n) * ((n.factorial : R))⁻¹)
          • (((LieAlgebra.ad R L x)^n) y) := by
  rw [expNegAdMap, expNegAdTrunc_apply]

lemma ad_pow_expAdMap (y : L) :
    ((LieAlgebra.ad R L x) ^ (expAdIndex x hloc y)) (expAdMap x hloc y) = 0 := by
  rw [expAdMap, ad_pow_expAdTrunc, ad_pow_expAdIndex, map_zero]

lemma ad_pow_expNegAdMap (y : L) :
    ((LieAlgebra.ad R L x) ^ (expAdIndex x hloc y)) (expNegAdMap x hloc y) = 0 := by
  rw [expNegAdMap, ad_pow_expNegAdTrunc, ad_pow_expAdIndex, map_zero]

/-- The first non-vanishing power of `ad x` applied to a truncation. -/
lemma ad_pow_pred_sum_eq {y : L} {n N : ℕ} (hn : 1 ≤ n)
    (h : ((LieAlgebra.ad R L x)^n) y = 0) (hN : n ≤ N) (c : ℕ → R) (hc : c 0 = 1) :
    ((LieAlgebra.ad R L x)^(n-1)) (∑ l ∈ range N, c l • (((LieAlgebra.ad R L x)^l) y))
      = ((LieAlgebra.ad R L x)^(n-1)) y := by
  rw [map_sum]
  have hsingle : (∑ l ∈ range N,
        ((LieAlgebra.ad R L x)^(n-1)) (c l • (((LieAlgebra.ad R L x)^l) y)))
      = ((LieAlgebra.ad R L x)^(n-1)) (c 0 • (((LieAlgebra.ad R L x)^0) y)) := by
    refine Finset.sum_eq_single 0 ?_ ?_
    · intro l hl hl0
      rw [mem_range] at hl
      rw [map_smul, ← Module.End.mul_apply, ← pow_add,
        ad_pow_eq_zero_of_le h (by omega), smul_zero]
    · intro h0
      exact absurd (mem_range.mpr (by omega)) h0
  rw [hsingle, hc, one_smul]
  simp

lemma ad_pow_pred_expAdMap {y : L} (hy : y ≠ 0) :
    ((LieAlgebra.ad R L x)^(expAdIndex x hloc y - 1)) (expAdMap x hloc y) ≠ 0 := by
  rw [expAdMap, expAdTrunc_apply,
    ad_pow_pred_sum_eq (x := x) (y := y) (n := expAdIndex x hloc y) (N := expAdIndex x hloc y)
      (expAdIndex_pos x hloc hy) (ad_pow_expAdIndex x hloc y) le_rfl
      (fun l => ((l.factorial : R))⁻¹)
      (by rw [Nat.factorial_zero, Nat.cast_one, inv_one])]
  intro hc
  have hle : expAdIndex x hloc y ≤ expAdIndex x hloc y - 1 := expAdIndex_le x hloc hc
  have hpos : 0 < expAdIndex x hloc y := expAdIndex_pos x hloc hy
  omega

lemma ad_pow_pred_expNegAdMap {y : L} (hy : y ≠ 0) :
    ((LieAlgebra.ad R L x)^(expAdIndex x hloc y - 1)) (expNegAdMap x hloc y) ≠ 0 := by
  rw [expNegAdMap, expNegAdTrunc_apply,
    ad_pow_pred_sum_eq (x := x) (y := y) (n := expAdIndex x hloc y) (N := expAdIndex x hloc y)
      (expAdIndex_pos x hloc hy) (ad_pow_expAdIndex x hloc y) le_rfl
      (fun l => (-1 : R)^l * ((l.factorial : R))⁻¹)
      (by rw [pow_zero, one_mul, Nat.factorial_zero, Nat.cast_one, inv_one])]
  intro hc
  have hle : expAdIndex x hloc y ≤ expAdIndex x hloc y - 1 := expAdIndex_le x hloc hc
  have hpos : 0 < expAdIndex x hloc y := expAdIndex_pos x hloc hy
  omega

lemma expAdIndex_expAdMap {y : L} (hy : y ≠ 0) :
    expAdIndex x hloc (expAdMap x hloc y) = expAdIndex x hloc y := by
  refine le_antisymm (expAdIndex_le x hloc (y := expAdMap x hloc y)
    (ad_pow_expAdMap x hloc y)) ?_
  by_contra hcon
  rw [not_le] at hcon
  have hle : expAdIndex x hloc (expAdMap x hloc y) ≤ expAdIndex x hloc y - 1 := by omega
  exact ad_pow_pred_expAdMap x hloc hy
    (ad_pow_eq_zero_of_le (x := x) (y := expAdMap x hloc y)
      (N := expAdIndex x hloc (expAdMap x hloc y)) (M := expAdIndex x hloc y - 1)
      (ad_pow_expAdIndex x hloc (expAdMap x hloc y)) hle)

lemma expAdIndex_expNegAdMap {y : L} (hy : y ≠ 0) :
    expAdIndex x hloc (expNegAdMap x hloc y) = expAdIndex x hloc y := by
  refine le_antisymm (expAdIndex_le x hloc (y := expNegAdMap x hloc y)
    (ad_pow_expNegAdMap x hloc y)) ?_
  by_contra hcon
  rw [not_le] at hcon
  have hle : expAdIndex x hloc (expNegAdMap x hloc y) ≤ expAdIndex x hloc y - 1 := by omega
  exact ad_pow_pred_expNegAdMap x hloc hy
    (ad_pow_eq_zero_of_le (x := x) (y := expNegAdMap x hloc y)
      (N := expAdIndex x hloc (expNegAdMap x hloc y)) (M := expAdIndex x hloc y - 1)
      (ad_pow_expAdIndex x hloc (expNegAdMap x hloc y)) hle)

lemma expAdMap_add (y z : L) :
    expAdMap x hloc (y + z) = expAdMap x hloc y + expAdMap x hloc z := by
  set M := expAdIndex x hloc (y + z) + expAdIndex x hloc y + expAdIndex x hloc z with hM
  have h1 : expAdIndex x hloc (y + z) ≤ M := by rw [hM]; omega
  have h2 : expAdIndex x hloc y ≤ M := by rw [hM]; omega
  have h3 : expAdIndex x hloc z ≤ M := by rw [hM]; omega
  rw [expAdMap, expAdMap, expAdMap,
    expAdTrunc_eq_of_le (ad_pow_expAdIndex x hloc (y+z)) h1,
    expAdTrunc_eq_of_le (ad_pow_expAdIndex x hloc y) h2,
    expAdTrunc_eq_of_le (ad_pow_expAdIndex x hloc z) h3]
  exact map_add _ _ _

lemma expAdMap_smul (r : R) (y : L) :
    expAdMap x hloc (r • y) = r • expAdMap x hloc y := by
  set M := expAdIndex x hloc (r • y) + expAdIndex x hloc y with hM
  have h1 : expAdIndex x hloc (r • y) ≤ M := by rw [hM]; omega
  have h2 : expAdIndex x hloc y ≤ M := by rw [hM]; omega
  rw [expAdMap, expAdMap,
    expAdTrunc_eq_of_le (ad_pow_expAdIndex x hloc (r • y)) h1,
    expAdTrunc_eq_of_le (ad_pow_expAdIndex x hloc y) h2]
  exact map_smul _ _ _

lemma expAdMap_lie (y z : L) :
    expAdMap x hloc ⁅y, z⁆ = ⁅expAdMap x hloc y, expAdMap x hloc z⁆ := by
  set M := expAdIndex x hloc ⁅y,z⁆ + expAdIndex x hloc y + expAdIndex x hloc z with hM
  have h1 : expAdIndex x hloc ⁅y, z⁆ ≤ M := by rw [hM]; omega
  have h2 : expAdIndex x hloc y ≤ M := by rw [hM]; omega
  have h3 : expAdIndex x hloc z ≤ M := by rw [hM]; omega
  have hMy : ((LieAlgebra.ad R L x)^M) y = 0 :=
    ad_pow_eq_zero_of_le (ad_pow_expAdIndex x hloc y) h2
  have hMz : ((LieAlgebra.ad R L x)^M) z = 0 :=
    ad_pow_eq_zero_of_le (ad_pow_expAdIndex x hloc z) h3
  have e1 : expAdMap x hloc ⁅y,z⁆ = expAdTrunc (R:=R) x (2*M) ⁅y,z⁆ :=
    expAdTrunc_eq_of_le (ad_pow_expAdIndex x hloc ⁅y,z⁆) (by omega)
  have e2 : expAdTrunc (R:=R) x (2*M) ⁅y,z⁆
      = ⁅expAdTrunc (R:=R) x M y, expAdTrunc (R:=R) x M z⁆ :=
    expAdTrunc_bracket x y z M hMy hMz
  have e3 : expAdTrunc (R:=R) x M y = expAdMap x hloc y :=
    (expAdTrunc_eq_of_le (ad_pow_expAdIndex x hloc y) h2).symm
  have e4 : expAdTrunc (R:=R) x M z = expAdMap x hloc z :=
    (expAdTrunc_eq_of_le (ad_pow_expAdIndex x hloc z) h3).symm
  rw [e1, e2, e3, e4]

lemma expNegAdMap_expAdMap (y : L) :
    expNegAdMap x hloc (expAdMap x hloc y) = y := by
  by_cases hy : y = 0
  · subst hy
    simp [expAdMap, expNegAdMap, expAdIndex_zero]
  · have hpos : 0 < expAdIndex x hloc y := expAdIndex_pos x hloc hy
    exact expNegAdTrunc_expAdTrunc (x := x) (y := y)
      (N := expAdIndex x hloc y) (M := expAdIndex x hloc (expAdMap x hloc y))
      (K := expAdIndex x hloc y) hpos (ad_pow_expAdIndex x hloc y)
      (le_of_eq (expAdIndex_expAdMap x hloc hy).symm) le_rfl

lemma expAdMap_expNegAdMap (y : L) :
    expAdMap x hloc (expNegAdMap x hloc y) = y := by
  by_cases hy : y = 0
  · subst hy
    simp [expNegAdMap, expAdMap, expAdIndex_zero]
  · have hpos : 0 < expAdIndex x hloc y := expAdIndex_pos x hloc hy
    exact expAdTrunc_expNegAdTrunc (x := x) (y := y)
      (N := expAdIndex x hloc y) (M := expAdIndex x hloc (expNegAdMap x hloc y))
      (K := expAdIndex x hloc y) hpos (ad_pow_expAdIndex x hloc y)
      (le_of_eq (expAdIndex_expNegAdMap x hloc hy).symm) le_rfl

end Assembly


/-! ### The main theorem -/

/-- **The exponential of a locally nilpotent inner derivation is a Lie algebra automorphism.**
For `x` in a Lie algebra `L` over a field of characteristic zero such that `ad x` is locally
nilpotent, the (locally finite) exponential series `∑ₙ (ad x)ⁿ y / n!` defines a Lie algebra
automorphism `Φ` of `L`, whose inverse is given by the same series with `x` replaced by `-x`.

This is the key construction underlying the "Weyl group action" on a Kac–Moody algebra: the
composite `exp(ad eᵢ) ∘ exp(ad(-fᵢ)) ∘ exp(ad eᵢ)` is the reflection automorphism. -/
theorem expAd_isLieEquiv {R L : Type*} [Field R] [CharZero R] [LieRing L] [LieAlgebra R L] (x : L)
    (hloc : ∀ y : L, ∃ n : ℕ, ((LieAlgebra.ad R L x)^n) y = 0) :
    ∃ Φ : L ≃ₗ⁅R⁆ L,
      (∀ y : L, ∃ N : ℕ,
        Φ y = ∑ n ∈ Finset.range (N + 1), (((n.factorial : R))⁻¹) • (((LieAlgebra.ad R L x)^n) y)) ∧
      (∀ y : L, ∃ N : ℕ,
        Φ.symm y = ∑ n ∈ Finset.range (N + 1),
          ((((-1 : R) ^ n) * ((n.factorial : R))⁻¹)) • (((LieAlgebra.ad R L x)^n) y)) := by
  let Φ : L ≃ₗ⁅R⁆ L :=
    LieEquiv.mk
      { toFun := expAdMap x hloc
        map_add' := expAdMap_add x hloc
        map_smul' := expAdMap_smul x hloc
        map_lie' := fun {y z} => expAdMap_lie x hloc y z }
      (expNegAdMap x hloc)
      (fun y => expNegAdMap_expAdMap x hloc y)
      (fun y => expAdMap_expNegAdMap x hloc y)
  refine ⟨Φ, fun y => ⟨expAdIndex x hloc y, ?_⟩, fun y => ⟨expAdIndex x hloc y, ?_⟩⟩
  · change expAdMap x hloc y = ∑ n ∈ Finset.range (expAdIndex x hloc y + 1),
        (((n.factorial : R))⁻¹) • (((LieAlgebra.ad R L x)^n) y)
    rw [expAdMap, expAdTrunc_apply, Finset.sum_range_succ, ad_pow_expAdIndex,
      smul_zero, add_zero]
  · change expNegAdMap x hloc y = ∑ n ∈ Finset.range (expAdIndex x hloc y + 1),
        ((((-1 : R) ^ n) * ((n.factorial : R))⁻¹)) • (((LieAlgebra.ad R L x)^n) y)
    rw [expNegAdMap, expNegAdTrunc_apply, Finset.sum_range_succ, ad_pow_expAdIndex,
      smul_zero, add_zero]
end Commons.Algebra.Lie