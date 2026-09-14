import Mathlib
import Submission.Commons.NumberTheory.ArithmeticFunction.card_Omega_eq_le

namespace Commons.NumberTheory.Counting

open Finset

/-- Tuples of positive natural numbers whose product is at most `n`. -/
abbrev PosProdTuple (k n : ℕ) : Type := {a : Fin k → ℕ // (∀ i, 1 ≤ a i) ∧ ∏ i, a i ≤ n}

namespace PosProdTuple

variable {k n : ℕ}

theorem coord_le (a : PosProdTuple k n) (i : Fin k) : a.1 i ≤ n := by
  have h : a.1 i ≤ ∏ j, a.1 j := by
    have hh := Finset.single_le_prod' (f := a.1) (fun j _ => a.2.1 j) (Finset.mem_univ i)
    simpa using hh
  exact h.trans a.2.2

instance : Finite (PosProdTuple k n) :=
  Finite.of_injective
    (fun a : PosProdTuple k n => fun i => (⟨a.1 i, by have := coord_le a i; omega⟩ : Fin (n + 1)))
    (by
      intro a b h
      refine Subtype.ext (funext fun i => ?_)
      have := congrFun h i
      simpa using congrArg Fin.val this)

/-- The map `(j, b) ↦ (j :: b)`. -/
def consMap {k n : ℕ}
    (p : Sigma fun j : {j : ℕ // j ∈ Finset.Icc 1 n} => PosProdTuple k (n / j)) :
    PosProdTuple (k + 1) n :=
  ⟨Fin.cons p.1.1 (fun i => p.2.1 i), by
    refine ⟨fun i => ?_, ?_⟩
    · induction i using Fin.cases with
      | zero => simpa using (Finset.mem_Icc.mp p.1.2).1
      | succ j => simpa using p.2.2.1 j
    · rw [Fin.prod_univ_succ]
      simp only [Fin.cons_zero, Fin.cons_succ]
      have h := (Nat.le_div_iff_mul_le
        (show 0 < p.1.1 by have := (Finset.mem_Icc.mp p.1.2).1; omega)).mp p.2.2.2
      exact (Nat.mul_comm _ _).trans_le h⟩

theorem consMap_surjective (k n : ℕ) : Function.Surjective (consMap (k := k) (n := n)) := by
  intro a
  refine ⟨⟨⟨a.1 0, by simp [Finset.mem_Icc]; exact ⟨a.2.1 0, coord_le a 0⟩⟩,
      ⟨fun i => a.1 i.succ, fun i => a.2.1 i.succ, ?_⟩⟩, ?_⟩
  · refine (Nat.le_div_iff_mul_le (show 0 < a.1 0 by have := a.2.1 0; omega)).mpr ?_
    show (∏ i : Fin k, a.1 i.succ) * a.1 0 ≤ n
    have h := a.2.2
    rw [Fin.prod_univ_succ] at h
    simpa [Nat.mul_comm] using h
  · refine Subtype.ext ?_
    show Fin.cons (a.1 0) (fun i => a.1 i.succ) = a.1
    exact Fin.cons_self_tail a.1

theorem card_succ_le (k n : ℕ) :
    Nat.card (PosProdTuple (k + 1) n) ≤
      Nat.card (Sigma fun j : {j : ℕ // j ∈ Finset.Icc 1 n} => PosProdTuple k (n / j)) :=
  Nat.card_le_card_of_surjective (consMap (k := k) (n := n)) (consMap_surjective k n)

theorem card_succ_le_sum (k n : ℕ) :
    Nat.card (PosProdTuple (k + 1) n) ≤ ∑ j ∈ Finset.Icc 1 n, Nat.card (PosProdTuple k (n / j)) := by
  refine (card_succ_le k n).trans (le_of_eq ?_)
  rw [Nat.card_sigma]
  exact Finset.sum_coe_sort (Finset.Icc 1 n) (fun j => Nat.card (PosProdTuple k (n / j)))

theorem card_le_aux : ∀ (k : ℕ), 1 ≤ k → ∀ (n : ℕ), 1 ≤ n →
    (Nat.card (PosProdTuple k n) : ℝ) ≤ (n : ℝ) * (1 + Real.log n) ^ (k - 1) := by
  intro k hk
  induction k, hk using Nat.le_induction with
  | base =>
      intro n hn
      have hcard : Nat.card (PosProdTuple 1 n) ≤ n := by
        have hinj := Nat.card_le_card_of_injective
          (fun a : PosProdTuple 1 n => (⟨a.1 0 - 1, by have := coord_le a 0; omega⟩ : Fin n))
          (by
            intro a b h
            refine Subtype.ext (funext fun i => ?_)
            have h0 : a.1 0 = b.1 0 := by
              have h' : a.1 0 - 1 = b.1 0 - 1 := congrArg Fin.val h
              have ha := a.2.1 0
              have hb := b.2.1 0
              omega
            have hi : i = 0 := Subsingleton.elim i 0
            rw [hi]
            exact h0)
        simpa using hinj
      calc (Nat.card (PosProdTuple 1 n) : ℝ) ≤ (n : ℝ) := by exact_mod_cast hcard
        _ = (n : ℝ) * (1 + Real.log n) ^ ((1 : ℕ) - 1) := by norm_num
  | succ k hk ih =>
      intro n hn
      show (Nat.card (PosProdTuple (k + 1) n) : ℝ) ≤ (n : ℝ) * (1 + Real.log n) ^ k
      have hbn : 0 ≤ 1 + Real.log (n : ℝ) := by
        have := Real.log_nonneg (show (1 : ℝ) ≤ (n : ℝ) by exact_mod_cast hn)
        linarith
      have hsum : ∑ j ∈ Finset.Icc 1 n, ((n / j : ℕ) : ℝ) ≤ (n : ℝ) * (1 + Real.log n) := by
        calc ∑ j ∈ Finset.Icc 1 n, ((n / j : ℕ) : ℝ)
            ≤ ∑ j ∈ Finset.Icc 1 n, (n : ℝ) / (j : ℝ) := by
              apply Finset.sum_le_sum
              intro j hj
              exact Nat.cast_div_le
          _ = (n : ℝ) * ∑ j ∈ Finset.Icc 1 n, (1 / (j : ℝ)) := by
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro j hj
              ring
          _ ≤ (n : ℝ) * (1 + Real.log n) :=
              mul_le_mul_of_nonneg_left
                (Commons.NumberTheory.ArithmeticFunction.sum_inv_Icc_one_le_one_add_log n)
                (Nat.cast_nonneg n)
      calc (Nat.card (PosProdTuple (k + 1) n) : ℝ)
          ≤ ∑ j ∈ Finset.Icc 1 n, (Nat.card (PosProdTuple k (n / j)) : ℝ) := by
            exact_mod_cast card_succ_le_sum k n
        _ ≤ ∑ j ∈ Finset.Icc 1 n,
              ((n / j : ℕ) : ℝ) * (1 + Real.log ((n / j : ℕ) : ℝ)) ^ (k - 1) := by
            apply Finset.sum_le_sum
            intro j hj
            have hj1 : 1 ≤ j := (Finset.mem_Icc.mp hj).1
            have hj2 : j ≤ n := (Finset.mem_Icc.mp hj).2
            exact ih (n / j) (by have := Nat.div_pos hj2 (by omega : 0 < j); omega)
        _ ≤ ∑ j ∈ Finset.Icc 1 n, ((n / j : ℕ) : ℝ) * (1 + Real.log n) ^ (k - 1) := by
            apply Finset.sum_le_sum
            intro j hj
            have hj1 : 1 ≤ j := (Finset.mem_Icc.mp hj).1
            have hj2 : j ≤ n := (Finset.mem_Icc.mp hj).2
            have hpos : 1 ≤ n / j := by
              have := Nat.div_pos hj2 (by omega : 0 < j)
              omega
            have hlognn : Real.log ((n / j : ℕ) : ℝ) ≤ Real.log n := by
              apply Real.log_le_log
              · exact_mod_cast hpos
              · exact_mod_cast Nat.div_le_self n j
            have hbase : 0 ≤ 1 + Real.log ((n / j : ℕ) : ℝ) := by
              have := Real.log_nonneg (show (1 : ℝ) ≤ ((n / j : ℕ) : ℝ) by exact_mod_cast hpos)
              linarith
            exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hbase (by linarith) (k - 1))
              (Nat.cast_nonneg _)
        _ = (∑ j ∈ Finset.Icc 1 n, ((n / j : ℕ) : ℝ)) * (1 + Real.log n) ^ (k - 1) := by
            rw [Finset.sum_mul]
        _ ≤ ((n : ℝ) * (1 + Real.log n)) * (1 + Real.log n) ^ (k - 1) :=
            mul_le_mul_of_nonneg_right hsum (pow_nonneg hbn _)
        _ = (n : ℝ) * (1 + Real.log n) ^ k := by
            rw [mul_assoc, ← pow_succ', Nat.sub_add_cancel hk]

end PosProdTuple

/-- `max 1 |x|`, for `x : ℤ`, seen as a natural number. -/
theorem max_one_abs_int (x : ℤ) : max 1 |((x : ℤ) : ℝ)| = ((max 1 x.natAbs : ℕ) : ℝ) := by
  have h : |((x : ℤ) : ℝ)| = ((x.natAbs : ℕ) : ℝ) := by
    by_cases h0 : 0 ≤ x
    · rw [abs_of_nonneg (by exact_mod_cast h0 : (0 : ℝ) ≤ (x : ℝ)),
        ← Int.ofNat_natAbs_of_nonneg h0]
      norm_num
    · have h' : x < 0 := by omega
      have hx : ((x.natAbs : ℕ) : ℤ) = -x := by
        rw [← Int.natAbs_neg x]
        exact Int.ofNat_natAbs_of_nonneg (by omega)
      have hcast : ((x.natAbs : ℕ) : ℝ) = ((-x : ℤ) : ℝ) := by
        have := congrArg (fun a : ℤ => (a : ℝ)) hx
        simpa using this
      rw [abs_of_neg (by exact_mod_cast h' : (x : ℝ) < 0), hcast]
      push_cast
      ring
  rw [h, show (1 : ℝ) = ((1 : ℕ) : ℝ) from by norm_num, ← Nat.cast_max]

theorem prod_max_one_abs_int (k : ℕ) (x : Fin k → ℤ) :
    (∏ i, max 1 |((x i : ℤ) : ℝ)|) = ((∏ i, max 1 ((x i).natAbs) : ℕ) : ℝ) := by
  rw [Nat.cast_prod]
  exact Finset.prod_congr rfl (fun i _ => max_one_abs_int (x i))

/-- The sign of an integer, as an element of `Fin 3`: `0` for zero, `1` for positive,
`2` for negative. -/
def sgn3 (x : ℤ) : Fin 3 := if x = 0 then 0 else if 0 < x then 1 else 2

/-- Reconstruct an integer from `max 1 |x|` and the sign `sgn3 x`. -/
def unsgn (a : ℕ) (s : Fin 3) : ℤ := if s = 0 then 0 else if s = 1 then (a : ℤ) else -(a : ℤ)

theorem sgn3_eq_zero {x : ℤ} : sgn3 x = 0 ↔ x = 0 := by
  unfold sgn3
  split_ifs with h1 h2
  · exact ⟨fun _ => h1, fun _ => rfl⟩
  · exact ⟨fun h => absurd h (by decide), fun h => absurd h h1⟩
  · exact ⟨fun h => absurd h (by decide), fun h => absurd h h1⟩

theorem sgn3_eq_one {x : ℤ} : sgn3 x = 1 ↔ 0 < x := by
  unfold sgn3
  split_ifs with h1 h2
  · exact ⟨fun h => absurd h (by decide), fun h => by omega⟩
  · exact ⟨fun _ => h2, fun _ => rfl⟩
  · exact ⟨fun h => absurd h (by decide), fun h => by omega⟩

theorem sgn3_eq_two {x : ℤ} : sgn3 x = 2 ↔ x < 0 := by
  unfold sgn3
  split_ifs with h1 h2
  · exact ⟨fun h => absurd h (by decide), fun h => by omega⟩
  · exact ⟨fun h => absurd h (by decide), fun h => by omega⟩
  · exact ⟨fun _ => by omega, fun _ => rfl⟩

theorem unsgn_max_sgn (x : ℤ) : unsgn (max 1 x.natAbs) (sgn3 x) = x := by
  rcases lt_trichotomy x 0 with h | h | h
  · have hs : sgn3 x = 2 := (sgn3_eq_two).mpr h
    have hcast : ((x.natAbs : ℕ) : ℤ) = -x := by
      rw [← Int.natAbs_neg x]
      exact Int.ofNat_natAbs_of_nonneg (by omega)
    have hmax : max 1 x.natAbs = x.natAbs := max_eq_right (by omega)
    rw [hs, hmax, unsgn]
    split_ifs with h1 h2
    · exact absurd h1 (by decide)
    · exact absurd h2 (by decide)
    · omega
  · subst h
    rw [show max 1 (0 : ℤ).natAbs = 1 from by simp, show sgn3 (0 : ℤ) = 0 from by simp [sgn3],
      unsgn]
    simp
  · have hs : sgn3 x = 1 := (sgn3_eq_one).mpr h
    have hcast : ((x.natAbs : ℕ) : ℤ) = x := Int.ofNat_natAbs_of_nonneg (by omega)
    have hmax : max 1 x.natAbs = x.natAbs := max_eq_right (by omega)
    rw [hs, hmax, unsgn]
    split_ifs with h1 h2
    · exact absurd h1 (by decide)
    · omega
    · omega

/-- Counting integer vectors whose product of `max 1 |·|` is at most the real number `M`. -/
theorem card_int_le (k : ℕ) (M : ℝ) :
    Nat.card {x : Fin k → ℤ // (∏ i, max 1 |((x i : ℤ) : ℝ)|) ≤ M} ≤
      Nat.card (PosProdTuple k ⌊M⌋₊) * 3 ^ k := by
  have key : ∀ x : {x : Fin k → ℤ // (∏ i, max 1 |((x i : ℤ) : ℝ)|) ≤ M},
      ∏ i, max 1 ((x.1 i).natAbs) ≤ ⌊M⌋₊ := by
    intro x
    apply Nat.le_floor
    rw [← prod_max_one_abs_int k x.1]
    exact x.2
  calc Nat.card {x : Fin k → ℤ // (∏ i, max 1 |((x i : ℤ) : ℝ)|) ≤ M}
      ≤ Nat.card (PosProdTuple k ⌊M⌋₊ × (Fin k → Fin 3)) := by
        apply Nat.card_le_card_of_injective
          (f := fun x : {x : Fin k → ℤ // (∏ i, max 1 |((x i : ℤ) : ℝ)|) ≤ M} =>
            ((⟨fun i => max 1 ((x.1 i).natAbs), fun _ => le_max_left _ _, key x⟩ :
                PosProdTuple k ⌊M⌋₊),
              fun i => sgn3 (x.1 i)))
        intro x y h
        refine Subtype.ext (funext fun i => ?_)
        have h1 : max 1 ((x.1 i).natAbs) = max 1 ((y.1 i).natAbs) :=
          congrFun (congrArg Subtype.val (congrArg Prod.fst h)) i
        have h2 : sgn3 (x.1 i) = sgn3 (y.1 i) := congrFun (congrArg Prod.snd h) i
        calc x.1 i = unsgn (max 1 ((x.1 i).natAbs)) (sgn3 (x.1 i)) := (unsgn_max_sgn _).symm
          _ = unsgn (max 1 ((y.1 i).natAbs)) (sgn3 (y.1 i)) := by rw [h1, h2]
          _ = y.1 i := unsgn_max_sgn _
    _ = Nat.card (PosProdTuple k ⌊M⌋₊) * 3 ^ k := by
        rw [Nat.card_prod, Nat.card_fun, Nat.card_fin, Nat.card_fin]

namespace PosProdTuple

theorem card_le (k n : ℕ) (hn : 1 ≤ n) :
    (Nat.card (PosProdTuple k n) : ℝ) ≤ (n : ℝ) * (1 + Real.log n) ^ (k - 1) := by
  rcases k with _ | k
  · have hsub : Subsingleton (PosProdTuple 0 n) := ⟨fun a b => Subtype.ext (funext fun i => i.elim0)⟩
    have hcard : Nat.card (PosProdTuple 0 n) ≤ 1 :=
      Finite.card_le_one_iff_subsingleton.mpr hsub
    calc (Nat.card (PosProdTuple 0 n) : ℝ) ≤ 1 := by exact_mod_cast hcard
      _ ≤ (n : ℝ) * (1 + Real.log n) ^ ((0 : ℕ) - 1) := by
          rw [show (0 : ℕ) - 1 = 0 from rfl, pow_zero, mul_one]
          exact_mod_cast hn
  · exact card_le_aux (k + 1) (Nat.le_add_left 1 k) n hn

end PosProdTuple

theorem ncard_prod_max_one_abs_le (k : ℕ) (M : ℝ) (hM : 1 ≤ M) :
    (Nat.card {x : Fin k → ℤ // (∏ i, max 1 |((x i : ℤ) : ℝ)|) ≤ M} : ℝ) ≤
      (100 : ℝ) ^ k * M * (1 + Real.log M) ^ (k - 1) := by
  have hn1 : 1 ≤ ⌊M⌋₊ := Nat.le_floor (by simpa using hM)
  have hle := card_int_le k M
  have hpos := PosProdTuple.card_le k ⌊M⌋₊ hn1
  have hM0 : 0 ≤ M := le_trans zero_le_one hM
  have hnM : (⌊M⌋₊ : ℝ) ≤ M := Nat.floor_le hM0
  have hlogn : Real.log (⌊M⌋₊ : ℝ) ≤ Real.log M :=
    Real.log_le_log (by exact_mod_cast hn1) hnM
  have hbn : 0 ≤ 1 + Real.log (⌊M⌋₊ : ℝ) := by
    have := Real.log_nonneg (show (1 : ℝ) ≤ (⌊M⌋₊ : ℝ) by exact_mod_cast hn1)
    linarith
  have hbM : 0 ≤ 1 + Real.log M := by linarith
  have hpow : (1 + Real.log (⌊M⌋₊ : ℝ)) ^ (k - 1) ≤ (1 + Real.log M) ^ (k - 1) :=
    pow_le_pow_left₀ hbn (by linarith) _
  have h3 : (3 : ℝ) ^ k ≤ (100 : ℝ) ^ k := pow_le_pow_left₀ (by norm_num) (by norm_num) k
  have hA : (⌊M⌋₊ : ℝ) * (1 + Real.log (⌊M⌋₊ : ℝ)) ^ (k - 1) ≤
      M * (1 + Real.log M) ^ (k - 1) :=
    mul_le_mul hnM hpow (pow_nonneg hbn _) hM0
  have hMsum : 0 ≤ M * (1 + Real.log M) ^ (k - 1) := mul_nonneg hM0 (pow_nonneg hbM _)
  calc (Nat.card {x : Fin k → ℤ // (∏ i, max 1 |((x i : ℤ) : ℝ)|) ≤ M} : ℝ)
      ≤ ((Nat.card (PosProdTuple k ⌊M⌋₊) * 3 ^ k : ℕ) : ℝ) := by exact_mod_cast hle
    _ = (Nat.card (PosProdTuple k ⌊M⌋₊) : ℝ) * 3 ^ k := by push_cast; ring
    _ ≤ ((⌊M⌋₊ : ℝ) * (1 + Real.log (⌊M⌋₊ : ℝ)) ^ (k - 1)) * 3 ^ k :=
        mul_le_mul_of_nonneg_right hpos (pow_nonneg (by norm_num) k)
    _ ≤ (M * (1 + Real.log M) ^ (k - 1)) * 100 ^ k :=
        mul_le_mul hA h3 (pow_nonneg (by norm_num) k) hMsum
    _ = (100 : ℝ) ^ k * M * (1 + Real.log M) ^ (k - 1) := by ring

end Commons.NumberTheory.Counting
