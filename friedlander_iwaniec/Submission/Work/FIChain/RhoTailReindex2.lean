import Mathlib

/-!
# `Submission.Work.FIChain.RhoTailReindex2`

The `ρ`-tail reindexing of Friedlander–Iwaniec: the iterated sum
`∑_{c ≤ x} ∑_{n₁ ∈ T} ∑_{n ≤ x, c n₁ n ≤ x} F (c n₁ n)`
over the hyperbola `c · n₁ · n ≤ x` (with `n₁` ranging over an arbitrary set `T`
of positive integers) is bounded by the divisor-square weighted sum
`∑_{M ≤ x} F M · d(M)^2`.

Every triple `(c, n₁, n)` on the left has product `M = c n₁ n ≤ x` with `M ≥ 1`,
so each term contributes `F M` for some `M ∈ [1,x]`.  For fixed `M`, the number
of triples `(c, n₁, n)` of positive integers with `c n₁ n = M` and `n₁ ∈ T` is at
most the number of ordered pairs `(a,b)` of divisors of `M` (via `(c,n₁,n) ↦
(c, n₁)`, `n` being recovered as `M/(c n₁)`), hence at most `d(M)^2`.  Since
`F ≥ 0`, replacing each fibre count by the upper bound `d(M)^2` only increases
the sum.
-/

namespace Work.FIChain

open Finset

/-- Product of the three coordinates of a triple of naturals. -/
private def tprod (q : ℕ × ℕ × ℕ) : ℕ := q.1 * q.2.1 * q.2.2

/-- For every `M`, the number of ordered triples `(a,b,c)` of natural numbers with
`a * b * c = M` is at most `d(M)^2`.  The map `(a,b,c) ↦ (a,b)` is injective on
this set (the third coordinate is `M / (a b)`) and lands in `M.divisors × M.divisors`. -/
private theorem card_triples_le_tprod (M : ℕ) :
    (((Finset.Icc 1 M).product ((Finset.Icc 1 M).product (Finset.Icc 1 M))).filter
        (fun q => q.1 * q.2.1 * q.2.2 = M)).card ≤ (M.divisors.card) ^ 2 := by
  set S := ((Finset.Icc 1 M).product ((Finset.Icc 1 M).product (Finset.Icc 1 M))).filter
      (fun q => q.1 * q.2.1 * q.2.2 = M) with hS
  have hmem : ∀ q ∈ S, q.1 ∈ Finset.Icc 1 M ∧ q.2.1 ∈ Finset.Icc 1 M ∧
      q.2.2 ∈ Finset.Icc 1 M ∧ q.1 * q.2.1 * q.2.2 = M := by
    intro q hq
    rw [hS, Finset.mem_filter] at hq
    have hp := Finset.mem_product.mp hq.1
    have hp2 := Finset.mem_product.mp hp.2
    exact ⟨hp.1, hp2.1, hp2.2, hq.2⟩
  have hmap : Set.MapsTo (fun q : ℕ × ℕ × ℕ => (q.1, q.2.1)) ↑S
      ↑(M.divisors ×ˢ M.divisors) := by
    intro q hq
    obtain ⟨h1, h2, h3, hprod⟩ := hmem q hq
    have hM0 : M ≠ 0 := by
      have ha := (Finset.mem_Icc.mp h1)
      omega
    have d1 : q.1 ∣ M := ⟨q.2.1 * q.2.2, by rw [← hprod, Nat.mul_assoc]⟩
    have d2 : q.2.1 ∣ M := ⟨q.1 * q.2.2, by rw [← hprod]; ring⟩
    exact Finset.mem_product.mpr ⟨Nat.mem_divisors.mpr ⟨d1, hM0⟩,
        Nat.mem_divisors.mpr ⟨d2, hM0⟩⟩
  have hinj : Set.InjOn (fun q : ℕ × ℕ × ℕ => (q.1, q.2.1)) ↑S := by
    intro q hq q' hq' heq
    obtain ⟨h1, h2, h3, hprod⟩ := hmem q hq
    obtain ⟨h1', h2', h3', hprod'⟩ := hmem q' hq'
    have hpos : 0 < q.1 * q.2.1 := by
      have a := (Finset.mem_Icc.mp h1).1
      have b := (Finset.mem_Icc.mp h2).1
      positivity
    have e1 : q.1 = q'.1 := by simpa using congrArg Prod.fst heq
    have e2 : q.2.1 = q'.2.1 := by simpa using congrArg Prod.snd heq
    have hh2 : M = q.1 * q.2.1 * q'.2.2 := by rw [e1, e2, hprod']
    have hh : q.1 * q.2.1 * q.2.2 = q.1 * q.2.1 * q'.2.2 := hprod.trans hh2
    have e3 : q.2.2 = q'.2.2 := Nat.mul_left_cancel hpos hh
    obtain ⟨a1, a2, a3⟩ := q
    obtain ⟨b1, b2, b3⟩ := q'
    simp only [Prod.mk.injEq] at e1 e2 e3 ⊢
    exact ⟨e1, e2, e3⟩
  calc S.card ≤ (M.divisors ×ˢ M.divisors).card := Finset.card_le_card_of_injOn _ hmap hinj
    _ = M.divisors.card * M.divisors.card := Finset.card_product _ _
    _ = (M.divisors.card) ^ 2 := by ring

/-- The iterated sum over `c ∈ [1,x]`, `n₁ ∈ T`, `n ∈ [1,x]` with the hyperbola
condition `c n₁ n ≤ x` equals the single sum over the corresponding finset of
triples (with the same condition, rewritten through `tprod`). -/
private theorem reindex_pf2 (x : ℕ) (T : Finset ℕ) (F : ℕ → ℝ) :
    (∑ c ∈ Finset.Icc 1 x, ∑ n₁ ∈ T,
        ∑ n ∈ (Finset.Icc 1 x).filter (fun n => c * n₁ * n ≤ x), F (c * n₁ * n))
      = ∑ q ∈ ((Finset.Icc 1 x).product (T.product (Finset.Icc 1 x))).filter
              (fun q => tprod q ≤ x),
            F (tprod q) := by
  set A := Finset.Icc 1 x with hA
  have step1 : (∑ c ∈ A, ∑ n₁ ∈ T, ∑ n ∈ A.filter (fun n => c * n₁ * n ≤ x), F (c * n₁ * n))
      = ∑ c ∈ A, ∑ p ∈ (T.product A).filter (fun p => c * p.1 * p.2 ≤ x), F (c * p.1 * p.2) := by
    apply Finset.sum_congr rfl
    intro c hc
    have hi1 : (∑ n₁ ∈ T, ∑ n ∈ A.filter (fun n => c * n₁ * n ≤ x), F (c * n₁ * n))
        = ∑ n₁ ∈ T, ∑ n ∈ A, (if c * n₁ * n ≤ x then F (c * n₁ * n) else 0) := by
      apply Finset.sum_congr rfl; intro n₁ _
      exact Finset.sum_filter (s := A) (p := fun (n : ℕ) => c * n₁ * n ≤ x) (fun n => F (c * n₁ * n))
    have hi2 : (∑ n₁ ∈ T, ∑ n ∈ A, (if c * n₁ * n ≤ x then F (c * n₁ * n) else 0))
        = ∑ p ∈ T.product A, (if c * p.1 * p.2 ≤ x then F (c * p.1 * p.2) else 0) :=
      (Finset.sum_product T A (fun (p : ℕ × ℕ) => if c * p.1 * p.2 ≤ x then F (c * p.1 * p.2) else 0)).symm
    have hi3 : (∑ p ∈ T.product A, (if c * p.1 * p.2 ≤ x then F (c * p.1 * p.2) else 0))
        = ∑ p ∈ (T.product A).filter (fun p => c * p.1 * p.2 ≤ x), F (c * p.1 * p.2) :=
      (Finset.sum_filter (s := T.product A) (p := fun (p : ℕ × ℕ) => c * p.1 * p.2 ≤ x)
        (fun p => F (c * p.1 * p.2))).symm
    exact hi1.trans (hi2.trans hi3)
  have step2 : (∑ c ∈ A, ∑ p ∈ (T.product A).filter (fun p => c * p.1 * p.2 ≤ x), F (c * p.1 * p.2))
      = ∑ q ∈ (A.product (T.product A)).filter (fun q => tprod q ≤ x), F (tprod q) := by
    have hj1 : (∑ c ∈ A, ∑ p ∈ (T.product A).filter (fun p => c * p.1 * p.2 ≤ x), F (c * p.1 * p.2))
        = ∑ c ∈ A, ∑ p ∈ T.product A, (if c * p.1 * p.2 ≤ x then F (c * p.1 * p.2) else 0) := by
      apply Finset.sum_congr rfl; intro c _
      exact Finset.sum_filter (s := T.product A) (p := fun (p : ℕ × ℕ) => c * p.1 * p.2 ≤ x)
        (fun p => F (c * p.1 * p.2))
    have hj2 : (∑ c ∈ A, ∑ p ∈ T.product A, (if c * p.1 * p.2 ≤ x then F (c * p.1 * p.2) else 0))
        = ∑ q ∈ A.product (T.product A), (if tprod q ≤ x then F (tprod q) else 0) :=
      (Finset.sum_product A (T.product A)
        (fun (q : ℕ × ℕ × ℕ) => if tprod q ≤ x then F (tprod q) else 0)).symm
    have hj3 : (∑ q ∈ A.product (T.product A), (if tprod q ≤ x then F (tprod q) else 0))
        = ∑ q ∈ (A.product (T.product A)).filter (fun q => tprod q ≤ x), F (tprod q) :=
      (Finset.sum_filter (s := A.product (T.product A))
        (p := fun (q : ℕ × ℕ × ℕ) => tprod q ≤ x)
        (fun q => F (tprod q))).symm
    exact hj1.trans (hj2.trans hj3)
  exact step1.trans step2

/-- **Friedlander–Iwaniec `ρ`-tail reindexing.**

The iterated sum over the hyperbola `c · n₁ · n ≤ x` (with `n₁` ranging over an
arbitrary set `T` of positive integers) is bounded by the divisor-square weighted
sum over `M ≤ x`.  This is the discrete counting step converting the
`(c, n₁, n)`-sum into a sum over `M` with weight `d(M)^2`. -/
theorem RhoTailReindex2 (x : ℕ) (T : Finset ℕ) (hT : ∀ n₁ ∈ T, 1 ≤ n₁) (F : ℕ → ℝ)
    (hF : ∀ M, 0 ≤ F M) :
    (∑ c ∈ Finset.Icc 1 x, ∑ n₁ ∈ T,
        ∑ n ∈ (Finset.Icc 1 x).filter (fun n => c * n₁ * n ≤ x), F (c * n₁ * n))
      ≤ ∑ M ∈ Finset.Icc 1 x, F M * ((M.divisors.card : ℝ)) ^ 2 := by
  set A := Finset.Icc 1 x with hA
  have hreindex : (∑ c ∈ A, ∑ n₁ ∈ T, ∑ n ∈ A.filter (fun n => c * n₁ * n ≤ x), F (c * n₁ * n))
      = ∑ q ∈ (A.product (T.product A)).filter (fun q => tprod q ≤ x), F (tprod q) := by
    have h := reindex_pf2 x T F
    simpa [hA] using h
  rw [hreindex]
  set Tr := (A.product (T.product A)).filter (fun q => tprod q ≤ x) with hTr
  have hmap : ∀ q ∈ Tr, tprod q ∈ A := by
    intro q hq
    rw [hTr, Finset.mem_filter] at hq
    obtain ⟨hqmem, hqle⟩ := hq
    have hp := Finset.mem_product.mp hqmem
    rw [hA] at hp
    have hp2 := Finset.mem_product.mp hp.2
    rw [hA, Finset.mem_Icc]
    refine ⟨?_, hqle⟩
    rw [tprod]
    have h1 : 1 ≤ q.1 := (Finset.mem_Icc.mp hp.1).1
    have h2 : 1 ≤ q.2.1 := hT q.2.1 hp2.1
    have h3 : 1 ≤ q.2.2 := (Finset.mem_Icc.mp hp2.2).1
    calc (1 : ℕ) = 1 * 1 * 1 := by norm_num
      _ ≤ q.1 * q.2.1 * q.2.2 := by gcongr
  rw [← Finset.sum_fiberwise_of_maps_to (s := Tr) (t := A) (g := tprod) hmap
        (fun q => F (tprod q))]
  apply Finset.sum_le_sum
  intro M hM
  have hinner : (∑ q ∈ Tr.filter (fun q => tprod q = M), F (tprod q))
      = ((Tr.filter (fun q => tprod q = M)).card : ℝ) * F M := by
    have h1 : (∑ q ∈ Tr.filter (fun q => tprod q = M), F (tprod q))
        = ∑ q ∈ Tr.filter (fun q => tprod q = M), F M := by
      apply Finset.sum_congr rfl
      intro q hq
      rw [Finset.mem_filter] at hq
      rw [hq.2]
    rw [h1, Finset.sum_const, nsmul_eq_mul]
  rw [hinner, mul_comm (F M) ((M.divisors.card : ℝ) ^ 2)]
  apply mul_le_mul_of_nonneg_right
  · have hcard : (Tr.filter (fun q => tprod q = M)).card ≤ (M.divisors.card) ^ 2 := by
      refine le_trans (Finset.card_le_card ?_) (card_triples_le_tprod M)
      intro q hq
      obtain ⟨hqTr, hqPhi⟩ := Finset.mem_filter.mp hq
      rw [hTr] at hqTr
      obtain ⟨hqmem, hqle⟩ := Finset.mem_filter.mp hqTr
      have hp := Finset.mem_product.mp hqmem
      rw [hA] at hp
      have hp2 := Finset.mem_product.mp hp.2
      rw [tprod] at hqPhi
      have hMx : M ∈ Finset.Icc 1 x := by simpa [hA] using hM
      have hMpos : 0 < M := by have := (Finset.mem_Icc.mp hMx).1; omega
      have q1lo : 1 ≤ q.1 := (Finset.mem_Icc.mp hp.1).1
      have q21lo : 1 ≤ q.2.1 := hT q.2.1 hp2.1
      have q22lo : 1 ≤ q.2.2 := (Finset.mem_Icc.mp hp2.2).1
      have dvd1 : q.1 ∣ M := ⟨q.2.1 * q.2.2, by rw [← hqPhi, Nat.mul_assoc]⟩
      have dvd2 : q.2.1 ∣ M := ⟨q.1 * q.2.2, by rw [← hqPhi]; ring⟩
      have dvd3 : q.2.2 ∣ M := ⟨q.1 * q.2.1, by rw [← hqPhi]; ring⟩
      exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr
          ⟨by rw [Finset.mem_Icc]; exact ⟨q1lo, Nat.le_of_dvd hMpos dvd1⟩,
           Finset.mem_product.mpr
            ⟨by rw [Finset.mem_Icc]; exact ⟨q21lo, Nat.le_of_dvd hMpos dvd2⟩,
             by rw [Finset.mem_Icc]; exact ⟨q22lo, Nat.le_of_dvd hMpos dvd3⟩⟩⟩, hqPhi⟩
    rw [← Nat.cast_pow]
    exact_mod_cast hcard
  · exact hF M

end Work.FIChain
