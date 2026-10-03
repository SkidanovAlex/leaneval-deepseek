import Mathlib
import Submission.Commons.NumberTheory.FriedlanderIwaniec.card_sq_add_pow_four_natpairs

namespace Commons.NumberTheory.FriedlanderIwaniec

/-- `Nat.sqrt (Nat.sqrt x)` (the integer fourth root of `x`) is bounded above by
the real fourth root `x ^ (1/4)`. -/
lemma sqrt_sqrt_cast_le_rpow (x : ℕ) :
    ((Nat.sqrt (Nat.sqrt x) : ℕ) : ℝ) ≤ (x : ℝ) ^ (1 / 4 : ℝ) := by
  set n : ℕ := Nat.sqrt (Nat.sqrt x) with hn
  have h4 : n ^ 4 ≤ x := by
    have h1 : Nat.sqrt (Nat.sqrt x) ^ 2 ≤ Nat.sqrt x := Nat.sqrt_le' _
    have h2 : (Nat.sqrt x) ^ 2 ≤ x := Nat.sqrt_le' _
    calc n ^ 4 = (Nat.sqrt (Nat.sqrt x) ^ 2) ^ 2 := by rw [hn]; ring
      _ ≤ (Nat.sqrt x) ^ 2 := by exact Nat.pow_le_pow_left h1 2
      _ ≤ x := h2
  have h4R : (n : ℝ) ^ 4 ≤ (x : ℝ) := by exact_mod_cast h4
  have hnn : (0 : ℝ) ≤ (n : ℝ) := by positivity
  have hstep := Real.rpow_le_rpow (show (0:ℝ) ≤ (n:ℝ)^4 by positivity) h4R
    (show (0:ℝ) ≤ (1/4:ℝ) by norm_num)
  have heq : ((n:ℝ)^4) ^ (1/4:ℝ) = (n:ℝ) := by
    rw [← Real.rpow_natCast (n:ℝ) 4, ← Real.rpow_mul hnn]
    rw [show ((4:ℕ):ℝ) * (1/4:ℝ) = 1 by norm_num, Real.rpow_one]
  rw [heq] at hstep
  exact hstep

/-- The set of pairs `(a, b)` of naturals with `a ^ 2 + b ^ 4 = p` is finite. -/
lemma repr_set_finite (p : ℕ) :
    ({q : ℕ × ℕ | 1 ≤ q.1 ∧ 1 ≤ q.2 ∧ q.1 ^ 2 + q.2 ^ 4 = p} : Set (ℕ × ℕ)).Finite := by
  apply Set.Finite.subset
    (s := ((Finset.range (p+1) ×ˢ Finset.range (p+1) : Finset (ℕ×ℕ)) : Set (ℕ×ℕ)))
  · exact Finset.finite_toSet _
  · intro q hq
    have hq' : 1 ≤ q.1 ∧ 1 ≤ q.2 ∧ q.1 ^ 2 + q.2 ^ 4 = p := hq
    simp only [Finset.mem_coe, Finset.mem_product, Finset.mem_range]
    have hq1 : q.1 ≤ p := by
      have hsq : q.1 ^ 2 ≤ p := by
        calc q.1 ^ 2 ≤ q.1 ^ 2 + q.2 ^ 4 := Nat.le_add_right _ _
          _ = p := hq'.2.2
      rcases Nat.eq_zero_or_pos q.1 with h | h
      · omega
      · have : q.1 ≤ q.1 ^ 2 := Nat.le_self_pow (by norm_num : 2 ≠ 0) q.1
        omega
    have hq2 : q.2 ≤ p := by
      have hf4 : q.2 ^ 4 ≤ p := by
        calc q.2 ^ 4 ≤ q.1 ^ 2 + q.2 ^ 4 := Nat.le_add_left _ _
          _ = p := hq'.2.2
      rcases Nat.eq_zero_or_pos q.2 with h | h
      · omega
      · have : q.2 ≤ q.2 ^ 4 := Nat.le_self_pow (by norm_num : 4 ≠ 0) q.2
        omega
    exact ⟨Nat.lt_succ_of_le hq1, Nat.lt_succ_of_le hq2⟩

/-- For `p ≤ x`, the number of pairs `(a, b)` with `1 ≤ a`, `1 ≤ b` and
`a ^ 2 + b ^ 4 = p` is at most `x ^ (1/4) + 1`.

Indeed the second coordinate determines the first, and `b ^ 4 ≤ p ≤ x`
forces `b ≤ Nat.sqrt (Nat.sqrt x) ≤ x ^ (1/4)`. -/
lemma repr_ncard_le {x p : ℕ} (hpx : p ≤ x) :
    (({q : ℕ × ℕ | 1 ≤ q.1 ∧ 1 ≤ q.2 ∧ q.1 ^ 2 + q.2 ^ 4 = p} : Set (ℕ × ℕ)).ncard : ℝ)
      ≤ (x : ℝ) ^ (1 / 4 : ℝ) + 1 := by
  classical
  let R : Set (ℕ × ℕ) := {q : ℕ × ℕ | 1 ≤ q.1 ∧ 1 ≤ q.2 ∧ q.1 ^ 2 + q.2 ^ 4 = p}
  let T : Set ℕ := {b : ℕ | b ^ 4 ≤ x}
  change ((R.ncard : ℕ) : ℝ) ≤ (x : ℝ) ^ (1 / 4 : ℝ) + 1
  have hTfin : T.Finite := by
    apply Set.Finite.subset (s := (Finset.range (x+1) : Set ℕ)) (Finset.finite_toSet _)
    intro b hb
    have hb4 : b ^ 4 ≤ x := hb
    rw [Finset.mem_coe, Finset.mem_range]
    rcases Nat.eq_zero_or_pos b with hb0 | hbpos
    · omega
    · have : b ≤ b ^ 4 := Nat.le_self_pow (by norm_num : 4 ≠ 0) b
      omega
  have hmem : ∀ q ∈ R, q.2 ∈ T := by
    intro q hq
    have hq' : 1 ≤ q.1 ∧ 1 ≤ q.2 ∧ q.1 ^ 2 + q.2 ^ 4 = p := hq
    show q.2 ^ 4 ≤ x
    calc q.2 ^ 4 ≤ q.1 ^ 2 + q.2 ^ 4 := Nat.le_add_left _ _
      _ = p := hq'.2.2
      _ ≤ x := hpx
  have hinj : Set.InjOn (fun q : ℕ × ℕ => q.2) R := by
    intro q hq q' hq' heq
    have hq1 : 1 ≤ q.1 ∧ 1 ≤ q.2 ∧ q.1 ^ 2 + q.2 ^ 4 = p := hq
    have hq1' : 1 ≤ q'.1 ∧ 1 ≤ q'.2 ∧ q'.1 ^ 2 + q'.2 ^ 4 = p := hq'
    have heq' : q.2 = q'.2 := heq
    have hsq : q.1 ^ 2 = q'.1 ^ 2 := by
      have hh : q.1 ^ 2 + q.2 ^ 4 = q'.1 ^ 2 + q'.2 ^ 4 := by rw [hq1.2.2, hq1'.2.2]
      rw [heq'] at hh
      exact Nat.add_right_cancel hh
    have h1 : q.1 = q'.1 := by
      calc q.1 = Nat.sqrt (q.1 ^ 2) := (Nat.sqrt_eq' q.1).symm
        _ = Nat.sqrt (q'.1 ^ 2) := by rw [hsq]
        _ = q'.1 := Nat.sqrt_eq' q'.1
    exact Prod.ext h1 heq'
  have hle := Set.ncard_le_ncard_of_injOn (fun q : ℕ × ℕ => q.2) hmem hinj hTfin
  have hTeq : T = (Finset.range (Nat.sqrt (Nat.sqrt x) + 1) : Set ℕ) := by
    ext b
    change b ^ 4 ≤ x ↔ b ∈ (Finset.range (Nat.sqrt (Nat.sqrt x) + 1) : Set ℕ)
    rw [Finset.mem_coe, Finset.mem_range]
    exact pow_four_le_iff_lt_sqrt_sqrt_succ
  have hTcard : T.ncard = Nat.sqrt (Nat.sqrt x) + 1 := by
    rw [hTeq, Set.ncard_coe_finset, Finset.card_range]
  have hRcard : R.ncard ≤ Nat.sqrt (Nat.sqrt x) + 1 := by rw [← hTcard]; exact hle
  have hcast1 : ((R.ncard : ℕ) : ℝ) ≤ ((Nat.sqrt (Nat.sqrt x) + 1 : ℕ) : ℝ) := by
    exact_mod_cast hRcard
  have hcast2 : ((Nat.sqrt (Nat.sqrt x) + 1 : ℕ) : ℝ) ≤ (x : ℝ) ^ (1 / 4 : ℝ) + 1 := by
    have := sqrt_sqrt_cast_le_rpow x
    push_cast
    linarith
  calc ((R.ncard : ℕ) : ℝ) ≤ ((Nat.sqrt (Nat.sqrt x) + 1 : ℕ) : ℝ) := hcast1
    _ ≤ (x : ℝ) ^ (1 / 4 : ℝ) + 1 := hcast2

lemma prime_part_le_card_mul {x : ℕ} (hx : 1 ≤ x) :
    (∑ p ∈ (Finset.range (x + 1)).filter Nat.Prime,
        ArithmeticFunction.vonMangoldt p *
          (({q : ℕ × ℕ | 1 ≤ q.1 ∧ 1 ≤ q.2 ∧ q.1 ^ 2 + q.2 ^ 4 = p}.ncard : ℕ) : ℝ))
      ≤ Real.log x * ((x : ℝ) ^ (1 / 4 : ℝ) + 1) *
        (({p : ℕ | p ≤ x ∧ p.Prime ∧ ∃ a b : ℕ, 1 ≤ a ∧ 1 ≤ b ∧ p = a ^ 2 + b ^ 4}
            : Set ℕ).ncard : ℝ) := by
  classical
  let S : Set ℕ := {p : ℕ | p ≤ x ∧ p.Prime ∧ ∃ a b : ℕ, 1 ≤ a ∧ 1 ≤ b ∧ p = a ^ 2 + b ^ 4}
  let cnt : ℕ → ℕ := fun p =>
    ({q : ℕ × ℕ | 1 ≤ q.1 ∧ 1 ≤ q.2 ∧ q.1 ^ 2 + q.2 ^ 4 = p} : Set (ℕ × ℕ)).ncard
  let A : Finset ℕ := (Finset.range (x + 1)).filter Nat.Prime
  let B : Finset ℕ := A.filter (fun k => 0 < cnt k)
  change (∑ p ∈ A, ArithmeticFunction.vonMangoldt p * ((cnt p : ℕ) : ℝ))
      ≤ Real.log x * ((x : ℝ) ^ (1 / 4 : ℝ) + 1) * ((S.ncard : ℕ) : ℝ)
  have hBA : B ⊆ A := fun p hp => (Finset.mem_filter.mp hp).1
  have hmemA : ∀ p, p ∈ A → p ∈ Finset.range (x + 1) ∧ p.Prime :=
    fun p hp => Finset.mem_filter.mp hp
  have hmemB : ∀ p, p ∈ B → p ∈ A ∧ 0 < cnt p := fun p hp => Finset.mem_filter.mp hp
  have hsum_eq : (∑ p ∈ A, ArithmeticFunction.vonMangoldt p * ((cnt p : ℕ) : ℝ))
      = ∑ p ∈ B, ArithmeticFunction.vonMangoldt p * ((cnt p : ℕ) : ℝ) := by
    symm
    apply Finset.sum_subset hBA
    intro p hpA hpB
    have hcnt0 : cnt p = 0 := by
      by_contra h
      exact hpB (Finset.mem_filter.mpr (show p ∈ A ∧ 0 < cnt p from ⟨hpA, Nat.pos_of_ne_zero h⟩))
    simp [hcnt0]
  have hterm : ∀ p ∈ B, ArithmeticFunction.vonMangoldt p * ((cnt p : ℕ) : ℝ)
      ≤ Real.log x * ((x : ℝ) ^ (1 / 4 : ℝ) + 1) := by
    intro p hpB
    have hpA : p ∈ A := hBA hpB
    have hp_range : p ∈ Finset.range (x + 1) := (hmemA p hpA).1
    have hprime : p.Prime := (hmemA p hpA).2
    have hple : p ≤ x := by
      have := Finset.mem_range.mp hp_range
      omega
    have hvm : ArithmeticFunction.vonMangoldt p ≤ Real.log x := by
      rw [ArithmeticFunction.vonMangoldt_apply_prime hprime]
      apply Real.log_le_log
      · exact_mod_cast hprime.pos
      · exact_mod_cast hple
    have hcnt : ((cnt p : ℕ) : ℝ) ≤ (x : ℝ) ^ (1 / 4 : ℝ) + 1 :=
      repr_ncard_le (x := x) (p := p) hple
    have hlogx : 0 ≤ Real.log x := Real.log_nonneg (by exact_mod_cast hx)
    exact mul_le_mul hvm hcnt (by positivity) hlogx
  have hsum_le : (∑ p ∈ B, ArithmeticFunction.vonMangoldt p * ((cnt p : ℕ) : ℝ))
      ≤ ∑ p ∈ B, (Real.log x * ((x : ℝ) ^ (1 / 4 : ℝ) + 1)) :=
    Finset.sum_le_sum hterm
  have hconst : (∑ p ∈ B, (Real.log x * ((x : ℝ) ^ (1 / 4 : ℝ) + 1)))
      = (B.card : ℝ) * (Real.log x * ((x : ℝ) ^ (1 / 4 : ℝ) + 1)) := by
    rw [Finset.sum_const, nsmul_eq_mul]
  have hBsub : (B : Set ℕ) ⊆ S := by
    intro p hpB
    have hpA : p ∈ A := hBA hpB
    have hprime : p.Prime := (hmemA p hpA).2
    have hple : p ≤ x := by
      have := Finset.mem_range.mp (hmemA p hpA).1
      omega
    have hpos : 0 < cnt p := (hmemB p hpB).2
    have hpos' : 0 < ({q : ℕ × ℕ | 1 ≤ q.1 ∧ 1 ≤ q.2 ∧ q.1 ^ 2 + q.2 ^ 4 = p}
        : Set (ℕ × ℕ)).ncard := hpos
    have hne : ({q : ℕ × ℕ | 1 ≤ q.1 ∧ 1 ≤ q.2 ∧ q.1 ^ 2 + q.2 ^ 4 = p}
        : Set (ℕ × ℕ)).Nonempty := (Set.ncard_pos (repr_set_finite p)).mp hpos'
    obtain ⟨q, hq⟩ := hne
    have hq' : 1 ≤ q.1 ∧ 1 ≤ q.2 ∧ q.1 ^ 2 + q.2 ^ 4 = p := hq
    exact ⟨hple, hprime, q.1, q.2, hq'.1, hq'.2.1, hq'.2.2.symm⟩
  have hSfin : S.Finite := by
    apply Set.Finite.subset (s := (Finset.range (x + 1) : Set ℕ)) (Finset.finite_toSet _)
    intro p hp
    have hp' : p ≤ x ∧ p.Prime ∧ ∃ a b : ℕ, 1 ≤ a ∧ 1 ≤ b ∧ p = a ^ 2 + b ^ 4 := hp
    rw [Finset.mem_coe, Finset.mem_range]
    exact Nat.lt_succ_of_le hp'.1
  have hcard : ((B.card : ℕ) : ℝ) ≤ ((S.ncard : ℕ) : ℝ) := by
    have h := Set.ncard_le_ncard hBsub hSfin
    rw [Set.ncard_coe_finset] at h
    exact_mod_cast h
  have hc_nonneg : 0 ≤ Real.log x * ((x : ℝ) ^ (1 / 4 : ℝ) + 1) := by
    apply mul_nonneg (Real.log_nonneg (by exact_mod_cast hx))
    have : (0 : ℝ) ≤ (x : ℝ) ^ (1 / 4 : ℝ) := Real.rpow_nonneg (by positivity) _
    linarith
  calc (∑ p ∈ A, ArithmeticFunction.vonMangoldt p * ((cnt p : ℕ) : ℝ))
      = ∑ p ∈ B, ArithmeticFunction.vonMangoldt p * ((cnt p : ℕ) : ℝ) := hsum_eq
    _ ≤ ∑ p ∈ B, (Real.log x * ((x : ℝ) ^ (1 / 4 : ℝ) + 1)) := hsum_le
    _ = (B.card : ℝ) * (Real.log x * ((x : ℝ) ^ (1 / 4 : ℝ) + 1)) := hconst
    _ ≤ (S.ncard : ℝ) * (Real.log x * ((x : ℝ) ^ (1 / 4 : ℝ) + 1)) :=
        mul_le_mul_of_nonneg_right hcard hc_nonneg
    _ = Real.log x * ((x : ℝ) ^ (1 / 4 : ℝ) + 1) * (S.ncard : ℝ) := by ring

end Commons.NumberTheory.FriedlanderIwaniec
