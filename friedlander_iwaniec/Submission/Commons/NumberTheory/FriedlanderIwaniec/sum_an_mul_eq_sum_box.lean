import Mathlib

namespace Commons.NumberTheory.FriedlanderIwaniec

/-- For every integer `z`, `|z| ≤ z ^ 2`. -/
private lemma int_abs_le_sq (z : ℤ) : |z| ≤ z ^ 2 := by
  have h : z.natAbs ≤ z.natAbs ^ 2 := Nat.le_self_pow (by norm_num) _
  rw [Int.abs_eq_natAbs]
  have hz : ((z.natAbs : ℤ)) ^ 2 = z ^ 2 := by
    rw [← Nat.cast_pow, ← Int.natAbs_pow, Int.natAbs_of_nonneg (by positivity)]
  rw [← hz]
  exact_mod_cast h

/-- For every integer `z`, `|z| ≤ z ^ 4`. -/
private lemma int_abs_le_pow_four (z : ℤ) : |z| ≤ z ^ 4 := by
  have h : z.natAbs ≤ z.natAbs ^ 4 := Nat.le_self_pow (by norm_num) _
  rw [Int.abs_eq_natAbs]
  have hz : ((z.natAbs : ℤ)) ^ 4 = z ^ 4 := by
    rw [← Nat.cast_pow, ← Int.natAbs_pow, Int.natAbs_of_nonneg (by positivity)]
  rw [← hz]
  exact_mod_cast h

/-- If `a ^ 2 + b ^ 4 = n ≤ x` then `(a, b)` lies in the box `[-x, x] × [-x, x]`. -/
private lemma mem_box_of_eq {x n : ℕ} (hn : n ≤ x) {p : ℤ × ℤ}
    (hp : p.1 ^ 2 + p.2 ^ 4 = (n : ℤ)) :
    p ∈ Finset.Icc (-(x : ℤ)) (x : ℤ) ×ˢ Finset.Icc (-(x : ℤ)) (x : ℤ) := by
  have hx' : p.1 ^ 2 + p.2 ^ 4 ≤ (x : ℤ) := by rw [hp]; exact_mod_cast hn
  have hb4 : (0 : ℤ) ≤ p.2 ^ 4 := by positivity
  have ha2 : (0 : ℤ) ≤ p.1 ^ 2 := by positivity
  have h1 : p.1 ^ 2 ≤ (x : ℤ) := by linarith
  have h2 : p.2 ^ 4 ≤ (x : ℤ) := by linarith
  rw [Finset.mem_product]
  constructor
  · rw [Finset.mem_Icc]
    exact abs_le.mp (le_trans (int_abs_le_sq p.1) h1)
  · rw [Finset.mem_Icc]
    exact abs_le.mp (le_trans (int_abs_le_pow_four p.2) h2)

theorem sum_an_mul_eq_sum_box (d x : ℕ) (f : ℕ → ℝ) (hx : 1 ≤ x)
    (hf0 : ∀ n, x < n → f n = 0) :
    (∑ n ∈ (Finset.range (x + 1)).filter (fun n => d ∣ n),
        (({p : ℤ × ℤ | p.1 ^ 2 + p.2 ^ 4 = (n : ℤ)}).ncard : ℝ) * f n)
      = ∑ p ∈ ((Finset.Icc (-(x : ℤ)) (x : ℤ)) ×ˢ (Finset.Icc (-(x : ℤ)) (x : ℤ))).filter
            (fun p => p.1 ^ 2 + p.2 ^ 4 ≤ (x : ℤ)),
          (if (d : ℤ) ∣ p.1 ^ 2 + p.2 ^ 4 then f ((p.1 ^ 2 + p.2 ^ 4).toNat) else 0) := by
  classical
  have _hx : 1 ≤ x := hx
  have _hf0 : ∀ n, x < n → f n = 0 := hf0
  set box : Finset (ℤ × ℤ) :=
    (Finset.Icc (-(x : ℤ)) (x : ℤ)) ×ˢ (Finset.Icc (-(x : ℤ)) (x : ℤ)) with hbox
  set N : Finset ℕ := (Finset.range (x + 1)).filter (fun n => d ∣ n) with hN
  -- Step 1: replace each fiber cardinality `ncard` by the cardinality inside the box.
  have hcard : ∀ n ∈ N, ({p : ℤ × ℤ | p.1 ^ 2 + p.2 ^ 4 = (n : ℤ)}).ncard
      = (box.filter (fun p => (p.1 ^ 2 + p.2 ^ 4).toNat = n)).card := by
    intro n hn
    have hnle : n ≤ x := by
      rw [hN, Finset.mem_filter, Finset.mem_range] at hn
      omega
    have hset : {p : ℤ × ℤ | p.1 ^ 2 + p.2 ^ 4 = (n : ℤ)}
        = ↑(box.filter (fun p => (p.1 ^ 2 + p.2 ^ 4).toNat = n)) := by
      ext p
      constructor
      · intro hp
        have hp' : p.1 ^ 2 + p.2 ^ 4 = (n : ℤ) := hp
        rw [Finset.mem_coe, Finset.mem_filter]
        exact ⟨by rw [hbox]; exact mem_box_of_eq hnle hp', by rw [hp', Int.toNat_natCast]⟩
      · intro hp
        rw [Finset.mem_coe, Finset.mem_filter] at hp
        obtain ⟨-, hpf⟩ := hp
        show p.1 ^ 2 + p.2 ^ 4 = (n : ℤ)
        have hnn : 0 ≤ p.1 ^ 2 + p.2 ^ 4 := by positivity
        calc p.1 ^ 2 + p.2 ^ 4 = (((p.1 ^ 2 + p.2 ^ 4).toNat : ℕ) : ℤ) :=
              (Int.toNat_of_nonneg hnn).symm
          _ = (n : ℤ) := by rw [hpf]
    rw [hset, Set.ncard_coe_finset]
  have hA1 : (∑ n ∈ N,
        (({p : ℤ × ℤ | p.1 ^ 2 + p.2 ^ 4 = (n : ℤ)}).ncard : ℝ) * f n)
      = ∑ n ∈ N, ((box.filter (fun p => (p.1 ^ 2 + p.2 ^ 4).toNat = n)).card : ℝ) * f n := by
    apply Finset.sum_congr rfl
    intro n hn
    rw [hcard n hn]
  -- Step 2: turn `card * f n` into a sum over the fiber.
  have hA2 : (∑ n ∈ N, ((box.filter (fun p => (p.1 ^ 2 + p.2 ^ 4).toNat = n)).card : ℝ) * f n)
      = ∑ n ∈ N, ∑ p ∈ box,
          (if (p.1 ^ 2 + p.2 ^ 4).toNat = n then f n else 0) := by
    apply Finset.sum_congr rfl
    intro n hn
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
  -- Step 3: swap the order of summation.
  have hA3 : (∑ n ∈ N, ∑ p ∈ box,
        (if (p.1 ^ 2 + p.2 ^ 4).toNat = n then f n else 0))
      = ∑ p ∈ box, ∑ n ∈ N,
          (if (p.1 ^ 2 + p.2 ^ 4).toNat = n then f n else 0) :=
    Finset.sum_comm
  -- Step 4: the inner sum over `N` collapses to a single value.
  have hA4 : (∑ p ∈ box, ∑ n ∈ N, (if (p.1 ^ 2 + p.2 ^ 4).toNat = n then f n else 0))
      = ∑ p ∈ box,
          (if (p.1 ^ 2 + p.2 ^ 4).toNat ∈ N then f ((p.1 ^ 2 + p.2 ^ 4).toNat) else 0) := by
    apply Finset.sum_congr rfl
    intro p hp
    exact Finset.sum_ite_eq N ((p.1 ^ 2 + p.2 ^ 4).toNat) f
  -- Step 5: identify membership in `N` with the pair condition.
  have hcond : ∀ p : ℤ × ℤ, ((p.1 ^ 2 + p.2 ^ 4).toNat ∈ N) ↔
      (p.1 ^ 2 + p.2 ^ 4 ≤ (x : ℤ) ∧ (d : ℤ) ∣ p.1 ^ 2 + p.2 ^ 4) := by
    intro p
    have hnn : 0 ≤ p.1 ^ 2 + p.2 ^ 4 := by positivity
    rw [hN, Finset.mem_filter, Finset.mem_range]
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨?_, ?_⟩
      · have h1' : (p.1 ^ 2 + p.2 ^ 4).toNat ≤ x := by omega
        calc p.1 ^ 2 + p.2 ^ 4 = (((p.1 ^ 2 + p.2 ^ 4).toNat : ℕ) : ℤ) :=
              (Int.toNat_of_nonneg hnn).symm
          _ ≤ (x : ℤ) := by exact_mod_cast h1'
      · have h2' : (d : ℤ) ∣ (((p.1 ^ 2 + p.2 ^ 4).toNat : ℕ) : ℤ) := by exact_mod_cast h2
        rwa [show (((p.1 ^ 2 + p.2 ^ 4).toNat : ℕ) : ℤ) = p.1 ^ 2 + p.2 ^ 4
              from Int.toNat_of_nonneg hnn] at h2'
    · rintro ⟨h1, h2⟩
      constructor
      · have : (p.1 ^ 2 + p.2 ^ 4).toNat ≤ x := Int.toNat_le.mpr h1
        omega
      · have h2' : (d : ℤ) ∣ (((p.1 ^ 2 + p.2 ^ 4).toNat : ℕ) : ℤ) := by
          rw [show (((p.1 ^ 2 + p.2 ^ 4).toNat : ℕ) : ℤ) = p.1 ^ 2 + p.2 ^ 4
                from Int.toNat_of_nonneg hnn]
          exact h2
        exact Int.natCast_dvd_natCast.mp h2'
  have hA5 : (∑ p ∈ box,
        (if (p.1 ^ 2 + p.2 ^ 4).toNat ∈ N then f ((p.1 ^ 2 + p.2 ^ 4).toNat) else 0))
      = ∑ p ∈ box,
          (if (p.1 ^ 2 + p.2 ^ 4 ≤ (x : ℤ) ∧ (d : ℤ) ∣ p.1 ^ 2 + p.2 ^ 4) then
            f ((p.1 ^ 2 + p.2 ^ 4).toNat) else 0) := by
    apply Finset.sum_congr rfl
    intro p hp
    simp only [hcond p]
  -- Step 6: rewrite the right-hand side in the same normal form.
  have hB : (∑ p ∈ box.filter (fun p => p.1 ^ 2 + p.2 ^ 4 ≤ (x : ℤ)),
        (if (d : ℤ) ∣ p.1 ^ 2 + p.2 ^ 4 then f ((p.1 ^ 2 + p.2 ^ 4).toNat) else 0))
      = ∑ p ∈ box,
          (if (p.1 ^ 2 + p.2 ^ 4 ≤ (x : ℤ) ∧ (d : ℤ) ∣ p.1 ^ 2 + p.2 ^ 4) then
            f ((p.1 ^ 2 + p.2 ^ 4).toNat) else 0) := by
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro p hp
    by_cases h1 : p.1 ^ 2 + p.2 ^ 4 ≤ (x : ℤ) <;>
      by_cases h2 : (d : ℤ) ∣ p.1 ^ 2 + p.2 ^ 4 <;> simp [h1, h2]
  rw [hA1, hA2, hA3, hA4, hA5, ← hB]

end Commons.NumberTheory.FriedlanderIwaniec
