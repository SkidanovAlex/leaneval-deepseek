import Mathlib
import Submission.Work.ZeroDensity.Jutila.S3GSharpDefs

/-!
# Sub-multiplicativity of `σ_{-1/2}(c) = Σ_{d ∣ c} 1/√d`

`Work.ZeroDensity.Jutila.s3Sig c = Σ_{d ∣ c} 1/√d` is the `σ_{-1/2}` factor appearing in the
sharp `S₃` estimates.  This file proves the elementary inequality

`s3Sig (a * b) ≤ s3Sig a * s3Sig b`   (`CzSigMul`)

used for the products `rt` of the two-sided `S₃` summations.

The argument is a direct divisor-splitting injection.  Every divisor `n ∣ a·b` is written as
`n = gcd(n,a) · (n / gcd(n,a))`, with `gcd(n,a) ∣ a` and `n / gcd(n,a) ∣ b` (coprimality of the
two quotients after dividing out the gcd).  Since `1/√(de) = (1/√d)(1/√e)`, the sum over
`n ∣ a·b` is therefore the sum of the pair weights over the *image* of this injection inside
`a.divisors × b.divisors`, hence at most the full double sum, which is `s3Sig a * s3Sig b`.
-/

namespace Work.ZeroDensity.Jutila.LzAux

open Finset

noncomputable section

/-- `(1/√m)·(1/√k) = 1/√(mk)`, so that the pair weight splits a product of divisor weights. -/
lemma cz_one_div_sqrt_mul (m k : ℕ) :
    (1 / Real.sqrt (m : ℝ)) * (1 / Real.sqrt (k : ℝ))
      = 1 / Real.sqrt ((m * k : ℕ) : ℝ) := by
  have h : Real.sqrt ((m * k : ℕ) : ℝ) = Real.sqrt (m : ℝ) * Real.sqrt (k : ℝ) := by
    rw [Nat.cast_mul, Real.sqrt_mul (Nat.cast_nonneg m) (k : ℝ)]
  rw [h]
  simp only [one_div]
  rw [mul_inv_rev, mul_comm]

/-- The divisor splitting `n ↦ (gcd n a, n / gcd n a)` for divisors of a product. -/
def czSplit (a n : ℕ) : ℕ × ℕ := (n.gcd a, n / n.gcd a)

/-- The pair weight `(d,e) ↦ (1/√d)·(1/√e)`. -/
def czPair (p : ℕ × ℕ) : ℝ := (1 / Real.sqrt (p.1 : ℝ)) * (1 / Real.sqrt (p.2 : ℝ))

/-- The pair weight of the splitting of `n` is the weight of `n`, since `n = gcd n a · (n / gcd n a)`. -/
lemma czPair_split {a n : ℕ} (h : n.gcd a * (n / n.gcd a) = n) :
    czPair (czSplit a n) = 1 / Real.sqrt (n : ℝ) := by
  have hh := cz_one_div_sqrt_mul (n.gcd a) (n / n.gcd a)
  simp only [czPair, czSplit] at hh ⊢
  rw [h] at hh
  exact hh

/-- If `n ≠ 0` divides `a·b`, then the complementary factor `n / gcd n a` divides `b`. -/
lemma cz_div_gcd_dvd_of_dvd_mul {n a b : ℕ} (hn : n ≠ 0) (h : n ∣ a * b) :
    n / n.gcd a ∣ b := by
  have hgn : n.gcd a ∣ n := Nat.gcd_dvd_left n a
  have hga : n.gcd a ∣ a := Nat.gcd_dvd_right n a
  have hgpos : 0 < n.gcd a := Nat.pos_of_dvd_of_pos hgn (Nat.pos_of_ne_zero hn)
  have hcop : Nat.Coprime (n / n.gcd a) (a / n.gcd a) := Nat.coprime_div_gcd_div_gcd hgpos
  have h1 : n.gcd a * (n / n.gcd a) ∣ n.gcd a * (a / n.gcd a * b) := by
    rw [Nat.mul_div_cancel' hgn, ← mul_assoc, Nat.mul_div_cancel' hga]
    exact h
  exact hcop.dvd_of_dvd_mul_left (Nat.dvd_of_mul_dvd_mul_left hgpos h1)

/-- `σ_{-1/2}` is sub-multiplicative: `Σ_{d ∣ ab} 1/√d ≤ (Σ_{d ∣ a} 1/√d)(Σ_{d ∣ b} 1/√d)`. -/
theorem CzSigMul (a b : ℕ) :
    Work.ZeroDensity.Jutila.s3Sig (a * b)
      ≤ Work.ZeroDensity.Jutila.s3Sig a * Work.ZeroDensity.Jutila.s3Sig b := by
  classical
  have hmono : ∑ n ∈ (a * b).divisors, (1 / Real.sqrt (n : ℝ))
      ≤ ∑ p ∈ a.divisors ×ˢ b.divisors, czPair p := by
    -- the splitting map is injective on the divisors of `a * b`
    have hinj : Set.InjOn (czSplit a) (↑((a * b).divisors) : Set ℕ) := by
      intro n _ m _ hnm
      have h1 : n.gcd a = m.gcd a := congrArg Prod.fst hnm
      have h2 : n / n.gcd a = m / m.gcd a := congrArg Prod.snd hnm
      rw [← Nat.mul_div_cancel' (Nat.gcd_dvd_left n a), h2, h1,
        Nat.mul_div_cancel' (Nat.gcd_dvd_left m a)]
    -- ... and lands in the divisor pairs
    have hmem : ∀ n ∈ (a * b).divisors, czSplit a n ∈ a.divisors ×ˢ b.divisors := by
      intro n hn
      obtain ⟨hdvd, habne⟩ := Nat.mem_divisors.mp hn
      have ha : a ≠ 0 := fun h => habne (by rw [h, Nat.zero_mul])
      have hb : b ≠ 0 := fun h => habne (by rw [h, Nat.mul_zero])
      have hn0 : n ≠ 0 := (Nat.pos_of_mem_divisors hn).ne'
      exact Finset.mem_product.mpr
        ⟨Nat.mem_divisors.mpr ⟨Nat.gcd_dvd_right n a, ha⟩,
         Nat.mem_divisors.mpr ⟨cz_div_gcd_dvd_of_dvd_mul hn0 hdvd, hb⟩⟩
    have hsubset : (a * b).divisors.image (czSplit a) ⊆ a.divisors ×ˢ b.divisors := by
      intro p hp
      obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hp
      exact hmem n hn
    have hnonneg : ∀ p ∈ a.divisors ×ˢ b.divisors, 0 ≤ czPair p := by
      intro p _
      simp only [czPair]
      exact mul_nonneg (one_div_nonneg.mpr (Real.sqrt_nonneg _))
        (one_div_nonneg.mpr (Real.sqrt_nonneg _))
    calc ∑ n ∈ (a * b).divisors, (1 / Real.sqrt (n : ℝ))
        = ∑ n ∈ (a * b).divisors, czPair (czSplit a n) := by
          refine Finset.sum_congr rfl fun n _ => ?_
          exact (czPair_split (Nat.mul_div_cancel' (Nat.gcd_dvd_left n a))).symm
      _ = ∑ p ∈ (a * b).divisors.image (czSplit a), czPair p := (Finset.sum_image hinj).symm
      _ ≤ ∑ p ∈ a.divisors ×ˢ b.divisors, czPair p :=
          Finset.sum_le_sum_of_subset_of_nonneg hsubset (fun p hp _ => hnonneg p hp)
  calc Work.ZeroDensity.Jutila.s3Sig (a * b)
      = ∑ n ∈ (a * b).divisors, (1 / Real.sqrt (n : ℝ)) := by
        simp only [Work.ZeroDensity.Jutila.s3Sig]
    _ ≤ ∑ p ∈ a.divisors ×ˢ b.divisors, czPair p := hmono
    _ = Work.ZeroDensity.Jutila.s3Sig a * Work.ZeroDensity.Jutila.s3Sig b := by
        simp only [Work.ZeroDensity.Jutila.s3Sig, Finset.sum_product, Finset.sum_mul_sum,
          czPair]

end

end Work.ZeroDensity.Jutila.LzAux
