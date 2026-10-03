import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Data.Int.Star
import Mathlib.Data.Set.Card

namespace Commons.NumberTheory.FriedlanderIwaniec

/-- The set of integer pairs `(a, b)` with `a ^ 2 + b ^ 4 ≤ x` is finite. -/
private lemma finite_intpairs_sq_add_pow_four_le (x : ℕ) :
    ({p : ℤ × ℤ | p.1 ^ 2 + p.2 ^ 4 ≤ (x : ℤ)} : Set (ℤ × ℤ)).Finite := by
  have hbig : ((Set.Icc (-((x : ℤ) + 1)) ((x : ℤ) + 1)) ×ˢ
      (Set.Icc (-((x : ℤ) + 1)) ((x : ℤ) + 1)) : Set (ℤ × ℤ)).Finite :=
    (Set.finite_Icc _ _).prod (Set.finite_Icc _ _)
  refine hbig.subset ?_
  intro p hp
  have hp' : p.1 ^ 2 + p.2 ^ 4 ≤ (x : ℤ) := hp
  have hp1 : p.1 ^ 2 ≤ (x : ℤ) := by
    have : (0 : ℤ) ≤ p.2 ^ 4 := by positivity
    linarith
  have hp2 : p.2 ^ 4 ≤ (x : ℤ) := by
    have : (0 : ℤ) ≤ p.1 ^ 2 := by positivity
    linarith
  have hb1 : (0 : ℤ) ≤ (x : ℤ) + 1 := by omega
  have hle_sq : (x : ℤ) ≤ ((x : ℤ) + 1) ^ 2 := by
    nlinarith [hb1, sq_nonneg (x : ℤ)]
  have hle_4 : (x : ℤ) ≤ ((x : ℤ) + 1) ^ 4 := by
    nlinarith [hb1, sq_nonneg (x : ℤ)]
  have hle1 : |p.1| ≤ (x : ℤ) + 1 := by
    have hsq : p.1 ^ 2 ≤ ((x : ℤ) + 1) ^ 2 := le_trans hp1 hle_sq
    have := (sq_le_sq.mp hsq : |p.1| ≤ |(x : ℤ) + 1|)
    rwa [abs_of_nonneg hb1] at this
  have hle2 : |p.2| ≤ (x : ℤ) + 1 := by
    have h4 : (|p.2|) ^ 4 ≤ ((x : ℤ) + 1) ^ 4 := by
      have : (|p.2|) ^ 4 = p.2 ^ 4 := by
        rw [← abs_pow, abs_of_nonneg (by positivity : (0 : ℤ) ≤ p.2 ^ 4)]
      rw [this]; exact le_trans hp2 hle_4
    exact (pow_le_pow_iff_left₀ (abs_nonneg _) hb1 (by norm_num)).mp h4
  rw [Set.mem_prod]
  exact ⟨abs_le.mp hle1, abs_le.mp hle2⟩

/-- **Lower bound for the number of integer pairs on `X² + Y⁴`.**

The number of integer pairs `(a, b)` with `a ^ 2 + b ^ 4 ≤ x` is at least
`(√√x) ^ 3 / 2 = x ^ (3/4) / 2`.

Indeed, the box of pairs `(a, b)` with `0 ≤ a ≤ ⌊√(x/2)⌋` and
`0 ≤ b ≤ ⌊(x/2) ^ (1/4)⌋` has `(⌊√(x/2)⌋ + 1) · (⌊(x/2) ^ (1/4)⌋ + 1)` elements,
all of which satisfy `a ^ 2 + b ^ 4 ≤ x/2 + x/2 = x`.  Writing `s = (x/2) ^ (1/4)`,
this count is `> s ^ 3 = x ^ (3/4) / 2 ^ (3/4) ≥ x ^ (3/4) / 2`. -/
theorem ncard_sq_add_pow_four_ge (x : ℕ) (hx : 1 ≤ x) :
    (Real.sqrt (Real.sqrt (x : ℝ))) ^ 3 / 2 ≤
      (({p : ℤ × ℤ | p.1 ^ 2 + p.2 ^ 4 ≤ (x : ℤ)}.ncard : ℕ) : ℝ) := by
  classical
  have hxR1 : (1 : ℝ) ≤ (x : ℝ) := by exact_mod_cast hx
  have hxR0 : (0 : ℝ) < (x : ℝ) := lt_of_lt_of_le zero_lt_one hxR1
  have hhalf0 : (0 : ℝ) ≤ (x : ℝ) / 2 := by positivity
  set s : ℝ := Real.sqrt (Real.sqrt ((x : ℝ) / 2)) with hsdef
  set A : ℕ := Nat.floor (Real.sqrt ((x : ℝ) / 2)) with hAdef
  set B : ℕ := Nat.floor s with hBdef
  have hs0 : 0 ≤ s := by rw [hsdef]; positivity
  have hY0 : 0 ≤ Real.sqrt (Real.sqrt (x : ℝ)) := Real.sqrt_nonneg _
  -- (1) fourth powers of `s` and of `Y = √√x`
  have hs2 : s ^ 2 = Real.sqrt ((x : ℝ) / 2) := by
    rw [hsdef]; exact Real.sq_sqrt (Real.sqrt_nonneg _)
  have hs4 : s ^ 4 = (x : ℝ) / 2 := by
    rw [show s ^ 4 = (s ^ 2) ^ 2 by ring, hs2, Real.sq_sqrt hhalf0]
  have hY2 : (Real.sqrt (Real.sqrt (x : ℝ))) ^ 2 = Real.sqrt (x : ℝ) :=
    Real.sq_sqrt (Real.sqrt_nonneg _)
  have hY4 : (Real.sqrt (Real.sqrt (x : ℝ))) ^ 4 = (x : ℝ) := by
    rw [show (Real.sqrt (Real.sqrt (x : ℝ))) ^ 4
          = ((Real.sqrt (Real.sqrt (x : ℝ))) ^ 2) ^ 2 by ring, hY2,
        Real.sq_sqrt (le_of_lt hxR0)]
  -- (2) `(√√x) ^ 3 ≤ 2 * s ^ 3`
  have hY3le : (Real.sqrt (Real.sqrt (x : ℝ))) ^ 3 ≤ 2 * s ^ 3 := by
    have h4 : ((Real.sqrt (Real.sqrt (x : ℝ))) ^ 3) ^ 4 ≤ (2 * s ^ 3) ^ 4 := by
      have hY4' : (Real.sqrt (Real.sqrt (x : ℝ))) ^ 4 = 2 * s ^ 4 := by
        rw [hY4, hs4]; ring
      calc ((Real.sqrt (Real.sqrt (x : ℝ))) ^ 3) ^ 4
          = ((Real.sqrt (Real.sqrt (x : ℝ))) ^ 4) ^ 3 := by ring
        _ = (2 * s ^ 4) ^ 3 := by rw [hY4']
        _ = 8 * s ^ 12 := by ring
        _ ≤ 16 * s ^ 12 := by nlinarith [pow_nonneg hs0 12]
        _ = (2 * s ^ 3) ^ 4 := by ring
    exact (pow_le_pow_iff_left₀ (pow_nonneg hY0 3) (by positivity) (by norm_num)).mp h4
  -- (3) `s ^ 3 ≤ (A + 1) * (B + 1)`
  have hA_le : (A : ℝ) ≤ Real.sqrt ((x : ℝ) / 2) := by
    rw [hAdef]; exact Nat.floor_le (Real.sqrt_nonneg _)
  have hB_le : (B : ℝ) ≤ s := by
    rw [hBdef]; exact Nat.floor_le hs0
  have hA_lt : Real.sqrt ((x : ℝ) / 2) < (A : ℝ) + 1 := by
    rw [hAdef]; exact Nat.lt_floor_add_one _
  have hB_lt : s < (B : ℝ) + 1 := by
    rw [hBdef]; exact Nat.lt_floor_add_one _
  have hs2_le : s ^ 2 ≤ (A : ℝ) + 1 := by rw [hs2]; linarith
  have hs_le : s ≤ (B : ℝ) + 1 := le_of_lt hB_lt
  have hs3_le : s ^ 3 ≤ ((A : ℝ) + 1) * ((B : ℝ) + 1) := by
    rw [show s ^ 3 = s ^ 2 * s by ring]
    exact mul_le_mul hs2_le hs_le hs0 (by positivity)
  -- (4) `A ^ 2 + B ^ 4 ≤ x`
  have hAre : (A : ℝ) ^ 2 ≤ (x : ℝ) / 2 := by
    have h1 : (A : ℝ) ^ 2 ≤ (Real.sqrt ((x : ℝ) / 2)) ^ 2 :=
      pow_le_pow_left₀ (Nat.cast_nonneg A) hA_le 2
    rwa [Real.sq_sqrt hhalf0] at h1
  have hBre : (B : ℝ) ^ 4 ≤ (x : ℝ) / 2 := by
    have h1 : (B : ℝ) ^ 4 ≤ s ^ 4 := pow_le_pow_left₀ (Nat.cast_nonneg B) hB_le 4
    rwa [hs4] at h1
  have hAB_int : (A : ℤ) ^ 2 + (B : ℤ) ^ 4 ≤ (x : ℤ) := by
    have : (A : ℝ) ^ 2 + (B : ℝ) ^ 4 ≤ (x : ℝ) := by linarith
    exact_mod_cast this
  -- (5) the box and its cardinality
  let F : Finset (ℤ × ℤ) := (Finset.Icc (0 : ℤ) (A : ℤ)) ×ˢ (Finset.Icc (0 : ℤ) (B : ℤ))
  have hFcard : F.card = (A + 1) * (B + 1) := by
    simp only [F, Finset.card_product, Int.card_Icc]
    norm_num
  have hFsub : (↑F : Set (ℤ × ℤ)) ⊆ {p : ℤ × ℤ | p.1 ^ 2 + p.2 ^ 4 ≤ (x : ℤ)} := by
    intro p hp
    simp only [F, Finset.mem_coe, Finset.mem_product, Finset.mem_Icc] at hp
    obtain ⟨⟨h1a, h1b⟩, ⟨h2a, h2b⟩⟩ := hp
    have hp1 : p.1 ^ 2 ≤ (A : ℤ) ^ 2 := pow_le_pow_left₀ h1a h1b 2
    have hp2 : p.2 ^ 4 ≤ (B : ℤ) ^ 4 := pow_le_pow_left₀ h2a h2b 4
    show p.1 ^ 2 + p.2 ^ 4 ≤ (x : ℤ)
    linarith [hAB_int]
  have hcard_le : F.card ≤ ({p : ℤ × ℤ | p.1 ^ 2 + p.2 ^ 4 ≤ (x : ℤ)}.ncard) := by
    have h := Set.ncard_le_ncard hFsub (finite_intpairs_sq_add_pow_four_le x)
    rwa [Set.ncard_coe_finset F] at h
  have hfinal : (((A + 1) * (B + 1) : ℕ) : ℝ)
      ≤ (({p : ℤ × ℤ | p.1 ^ 2 + p.2 ^ 4 ≤ (x : ℤ)}.ncard : ℕ) : ℝ) := by
    have h := hcard_le
    rw [hFcard] at h
    exact_mod_cast h
  calc (Real.sqrt (Real.sqrt (x : ℝ))) ^ 3 / 2
      = (Real.sqrt (Real.sqrt (x : ℝ))) ^ 3 / 2 := rfl
    _ ≤ s ^ 3 := by linarith [hY3le]
    _ ≤ ((A : ℝ) + 1) * ((B : ℝ) + 1) := hs3_le
    _ = (((A + 1) * (B + 1) : ℕ) : ℝ) := by push_cast; ring
    _ ≤ (({p : ℤ × ℤ | p.1 ^ 2 + p.2 ^ 4 ≤ (x : ℤ)}.ncard : ℕ) : ℝ) := hfinal

end Commons.NumberTheory.FriedlanderIwaniec