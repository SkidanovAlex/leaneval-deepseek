import Mathlib

/-!
# A uniform bound for the lattice sum `∑_{t ∈ ℤ} 1 / (1 + |v + t|)²`

For every real number `v` the series `t ↦ 1 / (1 + |v + t|)²` over `t ∈ ℤ` is summable, and its
sum is bounded by a constant which does not depend on `v`:

`∑_{t ∈ ℤ} 1 / (1 + |v + t|)² ≤ 2 ∑_{k ∈ ℕ} 1 / (1 + k²)`.

The proof shifts `v` by the integer `⌊v⌋`, so that the fractional part `u = v - ⌊v⌋` lies in
`[0,1)`, and splits the `ℤ`-sum into its nonnegative and its negative half.  On the nonnegative
half `|u + n| = u + n ≥ n`, while on the negative half, writing the index as `-(n+1)`, one has
`|u - (n+1)| = n + 1 - u ≥ n`; in both cases the summand is dominated by `1/(1+n²)`.
-/

open scoped BigOperators

namespace Work.Analysis.RubioDeFrancia

/-- The comparison series `∑_{k ∈ ℕ} 1/(1+k²)` is summable. -/
private lemma summable_one_div_one_add_sq_nat :
    Summable (fun k : ℕ => 1 / (1 + (k : ℝ) ^ 2)) := by
  have hbase : Summable (fun k : ℕ => 1 / ((k : ℝ) + 1) ^ 2) := by
    have h := (summable_nat_add_iff 1).2
      ((Real.summable_one_div_nat_pow (p := 2)).2 (by norm_num : (1 : ℕ) < 2))
    simpa only [Nat.cast_add, Nat.cast_one] using h
  refine Summable.of_nonneg_of_le (fun k => by positivity) (fun k => ?_) (hbase.mul_left 2)
  have hden : ((k : ℝ) + 1) ^ 2 / 2 ≤ 1 + (k : ℝ) ^ 2 := by
    nlinarith [sq_nonneg ((k : ℝ) - 1)]
  have hmain := one_div_le_one_div_of_le
    (show (0 : ℝ) < ((k : ℝ) + 1) ^ 2 / 2 by positivity) hden
  calc 1 / (1 + (k : ℝ) ^ 2) ≤ 1 / (((k : ℝ) + 1) ^ 2 / 2) := hmain
    _ = 2 * (1 / ((k : ℝ) + 1) ^ 2) := by rw [one_div_div]; ring

/-- On the nonnegative half, for `u ≥ 0` the summand is dominated by `1/(1+n²)`. -/
private lemma shifted_pos_le (u : ℝ) (hu0 : 0 ≤ u) (n : ℕ) :
    1 / (1 + |u + (n : ℝ)|) ^ 2 ≤ 1 / (1 + (n : ℝ) ^ 2) := by
  have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have hle : (n : ℝ) ≤ |u + (n : ℝ)| := by
    rw [abs_of_nonneg (by positivity)]
    linarith
  have hden : 1 + (n : ℝ) ^ 2 ≤ (1 + |u + (n : ℝ)|) ^ 2 := by
    have h₀ : 1 + (n : ℝ) ^ 2 ≤ (1 + (n : ℝ)) ^ 2 := by nlinarith [hn]
    have h₁ : (1 + (n : ℝ)) ^ 2 ≤ (1 + |u + (n : ℝ)|) ^ 2 :=
      pow_le_pow_left₀ (by positivity) (by linarith) 2
    linarith
  exact one_div_le_one_div_of_le (by positivity) hden

/-- On the negative half, for `u < 1` the summand at `-(n+1)` is dominated by `1/(1+n²)`. -/
private lemma shifted_neg_le (u : ℝ) (hu1 : u < 1) (n : ℕ) :
    1 / (1 + |u - ((n : ℝ) + 1)|) ^ 2 ≤ 1 / (1 + (n : ℝ) ^ 2) := by
  have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have h1n : (1 : ℝ) ≤ (n : ℝ) + 1 := by linarith
  have hle0 : u - ((n : ℝ) + 1) ≤ 0 := by linarith
  have habs : |u - ((n : ℝ) + 1)| = ((n : ℝ) + 1) - u := by
    rw [abs_of_nonpos hle0]; ring
  rw [habs]
  have hle : (n : ℝ) ≤ ((n : ℝ) + 1) - u := by linarith
  have hden : 1 + (n : ℝ) ^ 2 ≤ (1 + (((n : ℝ) + 1) - u)) ^ 2 := by
    have h₀ : 1 + (n : ℝ) ^ 2 ≤ (1 + (n : ℝ)) ^ 2 := by nlinarith [hn]
    have h₁ : (1 + (n : ℝ)) ^ 2 ≤ (1 + (((n : ℝ) + 1) - u)) ^ 2 :=
      pow_le_pow_left₀ (by positivity) (by linarith) 2
    linarith
  exact one_div_le_one_div_of_le (by positivity) hden

/-- The same bound as `shifted_neg_le`, with the negative index of `ℤ` written as an integer. -/
private lemma shifted_negSucc_le (u : ℝ) (hu1 : u < 1) (n : ℕ) :
    1 / (1 + |u + (((-(↑n + 1)) : ℤ) : ℝ)|) ^ 2 ≤ 1 / (1 + (n : ℝ) ^ 2) := by
  have hcast : (((-(↑n + 1)) : ℤ) : ℝ) = -((n : ℝ) + 1) := by
    simp only [Int.cast_neg, Int.cast_add, Int.cast_one, Int.cast_natCast]
  have harg : u + (((-(↑n + 1)) : ℤ) : ℝ) = u - ((n : ℝ) + 1) := by
    rw [hcast]; ring
  rw [harg]
  exact shifted_neg_le u hu1 n

/-- For `u ∈ [0,1)` the shifted lattice sum is summable and bounded by `2 ∑_k 1/(1+k²)`. -/
private lemma shifted_bound (u : ℝ) (hu0 : 0 ≤ u) (hu1 : u < 1) :
    Summable (fun n : ℤ => 1 / (1 + |u + (n : ℝ)|) ^ 2) ∧
      ∑' n : ℤ, 1 / (1 + |u + (n : ℝ)|) ^ 2
        ≤ 2 * (∑' k : ℕ, 1 / (1 + (k : ℝ) ^ 2)) := by
  have hcomp : Summable (fun k : ℕ => 1 / (1 + (k : ℝ) ^ 2)) :=
    summable_one_div_one_add_sq_nat
  have h1 : Summable (fun n : ℕ => (fun z : ℤ => 1 / (1 + |u + (z : ℝ)|) ^ 2) (↑n)) := by
    simpa only [Int.cast_natCast] using
      (Summable.of_nonneg_of_le (fun n : ℕ => by positivity) (shifted_pos_le u hu0) hcomp :
        Summable (fun n : ℕ => 1 / (1 + |u + (n : ℝ)|) ^ 2))
  have h2 : Summable (fun n : ℕ =>
      (fun z : ℤ => 1 / (1 + |u + (z : ℝ)|) ^ 2) (-(↑n + 1))) :=
    Summable.of_nonneg_of_le (fun n : ℕ => by positivity) (shifted_negSucc_le u hu1) hcomp
  have hsumm : Summable (fun n : ℤ => 1 / (1 + |u + (n : ℝ)|) ^ 2) :=
    Summable.of_nat_of_neg_add_one (f := fun z : ℤ => 1 / (1 + |u + (z : ℝ)|) ^ 2) h1 h2
  have key : (∑' n : ℤ, 1 / (1 + |u + (n : ℝ)|) ^ 2)
      = (∑' n : ℕ, (fun z : ℤ => 1 / (1 + |u + (z : ℝ)|) ^ 2) (↑n))
        + (∑' n : ℕ, (fun z : ℤ => 1 / (1 + |u + (z : ℝ)|) ^ 2) (-(↑n + 1))) :=
    tsum_of_nat_of_neg_add_one (f := fun z : ℤ => 1 / (1 + |u + (z : ℝ)|) ^ 2) h1 h2
  have hA : (∑' n : ℕ, (fun z : ℤ => 1 / (1 + |u + (z : ℝ)|) ^ 2) (↑n))
      ≤ ∑' k : ℕ, 1 / (1 + (k : ℝ) ^ 2) :=
    Summable.tsum_le_tsum
      (f := fun n : ℕ => (fun z : ℤ => 1 / (1 + |u + (z : ℝ)|) ^ 2) (↑n))
      (g := fun k : ℕ => 1 / (1 + (k : ℝ) ^ 2))
      (fun n => by simpa using shifted_pos_le u hu0 n) h1 hcomp
  have hB : (∑' n : ℕ, (fun z : ℤ => 1 / (1 + |u + (z : ℝ)|) ^ 2) (-(↑n + 1)))
      ≤ ∑' k : ℕ, 1 / (1 + (k : ℝ) ^ 2) :=
    Summable.tsum_le_tsum
      (f := fun n : ℕ => (fun z : ℤ => 1 / (1 + |u + (z : ℝ)|) ^ 2) (-(↑n + 1)))
      (g := fun k : ℕ => 1 / (1 + (k : ℝ) ^ 2))
      (fun n => shifted_negSucc_le u hu1 n) h2 hcomp
  refine ⟨hsumm, ?_⟩
  rw [key]
  linarith

theorem tsum_inv_one_add_abs_sq_le :
    ∃ S : ℝ, 0 < S ∧ ∀ v : ℝ,
      Summable (fun t : ℤ => 1 / (1 + |v + (t : ℝ)|) ^ 2) ∧
      ∑' t : ℤ, 1 / (1 + |v + (t : ℝ)|) ^ 2 ≤ S := by
  refine ⟨2 * (∑' k : ℕ, 1 / (1 + (k : ℝ) ^ 2)), ?_, ?_⟩
  · have hle : (1 : ℝ) ≤ ∑' k : ℕ, 1 / (1 + (k : ℝ) ^ 2) := by
      have h := summable_one_div_one_add_sq_nat.le_tsum 0 (fun j hj => by positivity)
      simpa using h
    linarith
  · intro v
    set m : ℤ := ⌊v⌋ with hm
    set u : ℝ := v - (m : ℝ) with hu
    have hu0 : 0 ≤ u := by
      rw [hu, hm]
      have := Int.floor_le v
      linarith
    have hu1 : u < 1 := by
      rw [hu, hm]
      have := Int.lt_floor_add_one v
      linarith
    have hvu : v = u + (m : ℝ) := by
      rw [hu]; ring
    have harg : ∀ t : ℤ, v + (t : ℝ) = u + ((t + m : ℤ) : ℝ) := by
      intro t
      rw [hvu]
      push_cast
      ring
    obtain ⟨hsumm', hbnd'⟩ := shifted_bound u hu0 hu1
    have hsumm : Summable (fun t : ℤ => 1 / (1 + |v + (t : ℝ)|) ^ 2) := by
      have h := (Equiv.summable_iff (Equiv.addRight m)
        (f := fun z : ℤ => 1 / (1 + |u + (z : ℝ)|) ^ 2)).mpr hsumm'
      have hfun : ((fun z : ℤ => 1 / (1 + |u + (z : ℝ)|) ^ 2) ∘ (Equiv.addRight m))
          = fun t : ℤ => 1 / (1 + |v + (t : ℝ)|) ^ 2 := by
        funext t
        simp only [Function.comp_apply, Equiv.coe_addRight]
        rw [harg t]
      rwa [hfun] at h
    refine ⟨hsumm, ?_⟩
    have hbij : (∑' t : ℤ, 1 / (1 + |v + (t : ℝ)|) ^ 2)
        = ∑' n : ℤ, 1 / (1 + |u + (n : ℝ)|) ^ 2 := by
      have hre : (∑' t : ℤ, 1 / (1 + |v + (t : ℝ)|) ^ 2)
          = ∑' t : ℤ, (fun z : ℤ => 1 / (1 + |u + (z : ℝ)|) ^ 2) ((Equiv.addRight m) t) := by
        apply tsum_congr
        intro t
        simp only [Equiv.coe_addRight]
        rw [harg t]
      calc (∑' t : ℤ, 1 / (1 + |v + (t : ℝ)|) ^ 2)
          = ∑' t : ℤ, (fun z : ℤ => 1 / (1 + |u + (z : ℝ)|) ^ 2) ((Equiv.addRight m) t) := hre
        _ = ∑' z : ℤ, 1 / (1 + |u + (z : ℝ)|) ^ 2 :=
            Equiv.tsum_eq (Equiv.addRight m) (fun z : ℤ => 1 / (1 + |u + (z : ℝ)|) ^ 2)
    rw [hbij]
    exact hbnd'

end Work.Analysis.RubioDeFrancia
