import Mathlib
import Submission.Commons.NumberTheory.FriedlanderIwaniec.card_sq_add_pow_four_intpairs_asymptotic

namespace Commons.NumberTheory.FriedlanderIwaniec

/-- The fourth power of the absolute value of an integer is the fourth power itself. -/
private lemma int_natAbs_pow_four (a : ℤ) : ((a.natAbs : ℤ)) ^ 4 = a ^ 4 := by
  have h1 : ((a.natAbs : ℤ)) ^ 4 = ((a.natAbs ^ 4 : ℕ) : ℤ) := by rw [Nat.cast_pow]
  rw [h1, ← Int.natAbs_pow, Int.natAbs_of_nonneg (by positivity)]

theorem Aseq_eq_intpairs_ncard (x : ℕ) :
    (∑ n ∈ Finset.range (x + 1), ({p : ℤ × ℤ | p.1 ^ 2 + p.2 ^ 4 = (n : ℤ)}).ncard)
      = ({p : ℤ × ℤ | p.1 ^ 2 + p.2 ^ 4 ≤ (x : ℤ)}).ncard := by
  classical
  -- The set of integer pairs `(a,b)` with `a² + b⁴ ≤ x` is finite.
  have hFin : ({p : ℤ × ℤ | p.1 ^ 2 + p.2 ^ 4 ≤ (x : ℤ)}).Finite := by
    have hbig : ((((Finset.Icc (-(x : ℤ)) (x : ℤ) : Finset ℤ)) : Set ℤ) ×ˢ
        (((Finset.Icc (-(x : ℤ)) (x : ℤ) : Finset ℤ)) : Set ℤ)).Finite :=
      (Finset.finite_toSet _).prod (Finset.finite_toSet _)
    refine hbig.subset ?_
    intro p hp
    have hp' : p.1 ^ 2 + p.2 ^ 4 ≤ (x : ℤ) := hp
    have h2 : (0 : ℤ) ≤ p.2 ^ 4 := by positivity
    have h4 : (0 : ℤ) ≤ p.1 ^ 2 := by positivity
    have hp1 : p.1 ^ 2 ≤ (x : ℤ) := by linarith
    have hp2 : p.2 ^ 4 ≤ (x : ℤ) := by linarith
    rw [Set.mem_prod]
    constructor
    · rw [Finset.mem_coe, Finset.mem_Icc]
      have h' : ((p.1.natAbs ^ 2 : ℕ) : ℤ) ≤ (x : ℤ) := by
        rw [Nat.cast_pow, Int.natAbs_sq]; exact hp1
      have h'' : p.1.natAbs ^ 2 ≤ x := by exact_mod_cast h'
      have h : p.1.natAbs ≤ x :=
        le_trans (Nat.le_self_pow (by norm_num) p.1.natAbs) h''
      have hle : |p.1| ≤ (x : ℤ) := by
        rw [Int.abs_eq_natAbs]; exact_mod_cast h
      exact abs_le.mp hle
    · rw [Finset.mem_coe, Finset.mem_Icc]
      have h' : ((p.2.natAbs ^ 4 : ℕ) : ℤ) ≤ (x : ℤ) := by
        rw [Nat.cast_pow, int_natAbs_pow_four]; exact hp2
      have h'' : p.2.natAbs ^ 4 ≤ x := by exact_mod_cast h'
      have h : p.2.natAbs ≤ x :=
        le_trans (Nat.le_self_pow (by norm_num) p.2.natAbs) h''
      have hle : |p.2| ≤ (x : ℤ) := by
        rw [Int.abs_eq_natAbs]; exact_mod_cast h
      exact abs_le.mp hle
  let sf := hFin.toFinset
  have hmemSf : ∀ p : ℤ × ℤ, p ∈ sf ↔ p.1 ^ 2 + p.2 ^ 4 ≤ (x : ℤ) := by
    intro p
    show p ∈ hFin.toFinset ↔ _
    rw [Set.Finite.mem_toFinset]
    rfl
  -- map each pair to the natural number `a² + b⁴`
  let F : ℤ × ℤ → ℕ := fun p => (p.1 ^ 2 + p.2 ^ 4).toNat
  -- every pair counted lies in `range (x+1)`
  have hmap : Set.MapsTo F (↑sf : Set (ℤ × ℤ)) (↑(Finset.range (x + 1)) : Set ℕ) := by
    intro p hp
    have hpS : p.1 ^ 2 + p.2 ^ 4 ≤ (x : ℤ) := (hmemSf p).mp hp
    have hnn : (0 : ℤ) ≤ p.1 ^ 2 + p.2 ^ 4 := by positivity
    have htoNat : (p.1 ^ 2 + p.2 ^ 4).toNat ≤ x := by
      have : (((p.1 ^ 2 + p.2 ^ 4).toNat : ℤ)) ≤ (x : ℤ) := by
        rw [Int.toNat_of_nonneg hnn]; exact hpS
      exact_mod_cast this
    simp only [Finset.mem_coe, Finset.mem_range]
    show (p.1 ^ 2 + p.2 ^ 4).toNat < x + 1
    omega
  -- each fibre of `F` is exactly one level set
  have hterm : ∀ n ∈ Finset.range (x + 1),
      (sf.filter (fun p => F p = n)).card
        = ({p : ℤ × ℤ | p.1 ^ 2 + p.2 ^ 4 = (n : ℤ)}).ncard := by
    intro n hn
    have hnle : n ≤ x := Nat.lt_succ_iff.mp (Finset.mem_range.mp hn)
    have hset : (↑(sf.filter (fun p => F p = n)) : Set (ℤ × ℤ))
        = {p : ℤ × ℤ | p.1 ^ 2 + p.2 ^ 4 = (n : ℤ)} := by
      ext p
      simp only [Finset.mem_coe, Finset.mem_filter, Set.mem_ofPred_eq]
      constructor
      · rintro ⟨hp, hFn⟩
        have hnn : (0 : ℤ) ≤ p.1 ^ 2 + p.2 ^ 4 := by positivity
        have hFn' : (p.1 ^ 2 + p.2 ^ 4).toNat = n := hFn
        have h1 : p.1 ^ 2 + p.2 ^ 4 = ((p.1 ^ 2 + p.2 ^ 4).toNat : ℤ) :=
          (Int.toNat_of_nonneg hnn).symm
        rw [h1, hFn']
      · rintro h
        constructor
        · rw [hmemSf p, h]
          exact_mod_cast hnle
        · show (p.1 ^ 2 + p.2 ^ 4).toNat = n
          rw [h]
          exact Int.toNat_natCast n
    rw [← Set.ncard_coe_finset (sf.filter (fun p => F p = n)), hset]
  -- fiberwise decomposition of the finite set
  have hfib := Finset.card_eq_sum_card_fiberwise hmap
  have hsum : (∑ n ∈ Finset.range (x + 1),
        ({p : ℤ × ℤ | p.1 ^ 2 + p.2 ^ 4 = (n : ℤ)}).ncard)
      = ∑ n ∈ Finset.range (x + 1), (sf.filter (fun p => F p = n)).card :=
    Finset.sum_congr rfl (fun n hn => (hterm n hn).symm)
  have hcard : ({p : ℤ × ℤ | p.1 ^ 2 + p.2 ^ 4 ≤ (x : ℤ)}).ncard = sf.card :=
    Set.ncard_eq_toFinset_card _ hFin
  rw [hsum, ← hfib, hcard]

end Commons.NumberTheory.FriedlanderIwaniec
