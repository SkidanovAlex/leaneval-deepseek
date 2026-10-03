/-
# `Submission.Work.FIArea7.KStarDiscDefs` — vocabulary for the *disc* version of *FI* (22.4)

*FI* Prop. 22.1 bounds the box sum `K*(N) = Σ∧_{z ∈ B, (z,w)=1} ψ(z)[wz]` (`Work.FIArea7.KStar_bound`).
Prop. 23.2 needs the same bound when the box `B` is replaced by the **disc** `|z|² ≤ N`, i.e.

  `K∗(N) = Σ∧_{z : |z|² ≤ N, (z,w)=1} ψ(z)[wz]`  (`Work.FIArea7.KStarDisc`).

Written fibre by fibre over `r = Re z` (`Work.FIArea7.KStarDisc`), this is the sum of the fibres
`KInnerStar (discFib N r) w k chi r` over `r ∈ Icc (-(discSqrt N)) (discSqrt N)`, where the *radius*
`discFib N r = ⌊√(N - r²)⌋` now depends on `r` (it is `≤ discSqrt N = ⌊√N⌋`).

Besides the vocabulary (`discSqrt`, `discFib`, `goodR`) this file proves the two elementary
estimates the assembly needs:

* `log_discFib_le` — `log(2 + |r|q) ≤ 2 log(2 + √q·N)` for `|r| ≤ ⌊√N⌋`, the log comparison that
  replaces the *FI* §22 `log(2 + |r|q) ≤ 2log(2 + √q·(2R+1))` (`Work.FIArea7.KSum_arith_helpers`);
* `discSqrt_mul_sqrt_le` — `⌊√N⌋·√⌊√N⌋ ≤ N^{3/4}` (since `⌊√N⌋ ≤ √N`).
-/
import Mathlib
import Submission.Work.FIArea7.prop232Defs

set_option autoImplicit false

namespace Work.FIArea7

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-- `⌊√N⌋` as an integer: the half-width of the `r`-range of the disc sum `K∗(N)`. -/
def discSqrt (N : ℕ) : ℤ := ((Nat.sqrt N : ℕ) : ℤ)

/-- The half-width of the fibre `Re z = r` of the disc `|z|² ≤ N`, i.e. `⌊√(N - r²)⌋`. -/
def discFib (N : ℕ) (r : ℤ) : ℤ := ((Nat.sqrt (N - r.natAbs ^ 2) : ℕ) : ℤ)

/-- The "good" real parts `r` for *FI* §22: some prime `p ∤ 4dq` divides `r` to an odd power, so
that the Jacobi character `(· | |r|)` occurring in the fibre is non-trivial and
Pólya–Vinogradov applies (`Work.FIArea7.KInnerStar_good_bound_exists`). -/
def goodR (d q : ℕ) (r : ℤ) : Prop :=
  ∃ p : ℕ, p.Prime ∧ ¬ (p : ℤ) ∣ (4 * (d : ℤ) * (q : ℤ)) ∧ Odd (r.natAbs.factorization p)

@[simp] theorem discSqrt_def (N : ℕ) : discSqrt N = ((Nat.sqrt N : ℕ) : ℤ) := rfl

@[simp] theorem discFib_def (N : ℕ) (r : ℤ) :
    discFib N r = ((Nat.sqrt (N - r.natAbs ^ 2) : ℕ) : ℤ) := rfl

/-- `K∗(N)` is, by definition, the sum of its fibres `KInnerStar` at the varying radius
`discFib N r`. -/
theorem KStarDisc_eq_sum (N : ℕ) (w : GaussianInt) (k : ℤ) (chi : GaussianInt → ℂ) :
    KStarDisc N w k chi = ∑ r ∈ Finset.Icc (-(discSqrt N)) (discSqrt N),
      KInnerStar (discFib N r) w k chi r := rfl

/-- The fibre radius is non-negative. -/
theorem discFib_nonneg (N : ℕ) (r : ℤ) : 0 ≤ discFib N r := Nat.cast_nonneg _

/-- `discSqrt` is non-negative. -/
theorem discSqrt_nonneg (N : ℕ) : 0 ≤ discSqrt N := Nat.cast_nonneg _

/-- `1 ≤ ⌊√N⌋` for `1 ≤ N`. -/
theorem one_le_discSqrt {N : ℕ} (hN : 1 ≤ N) : 1 ≤ discSqrt N := by
  rw [discSqrt_def]
  exact_mod_cast (le_trans (le_of_eq Nat.sqrt_one.symm) (Nat.sqrt_le_sqrt hN))

/-- `r ∈ Icc (-⌊√N⌋) ⌊√N⌋ → 1 ≤ |r| ≤ ⌊√N⌋` (for `r ≠ 0`). -/
theorem natAbs_le_discSqrt {N : ℕ} {r : ℤ}
    (hr : r ∈ Finset.Icc (-(discSqrt N)) (discSqrt N)) : r.natAbs ≤ Nat.sqrt N := by
  rw [Finset.mem_Icc] at hr
  rw [discSqrt_def] at hr
  omega

/-- The fibre radius is at most the half-width of the `r`-range (in fact at most `discSqrt N`
always). -/
theorem discFib_le_discSqrt (N : ℕ) (r : ℤ) : discFib N r ≤ discSqrt N := by
  rw [discFib_def, discSqrt_def]
  exact_mod_cast (Nat.sqrt_le_sqrt (Nat.sub_le N (r.natAbs ^ 2)))

/-- `|r| ≤ √N` for `r` in the `r`-range of the disc sum. -/
theorem cast_natAbs_le_sqrt {N : ℕ} {r : ℤ}
    (hr : r ∈ Finset.Icc (-(discSqrt N)) (discSqrt N)) :
    (r.natAbs : ℝ) ≤ Real.sqrt (N : ℝ) := by
  have h1 : r.natAbs ≤ Nat.sqrt N := natAbs_le_discSqrt hr
  have h2 : (r.natAbs : ℝ) ≤ (Nat.sqrt N : ℝ) := by exact_mod_cast h1
  have h3 : (Nat.sqrt N : ℝ) ≤ Real.sqrt (N : ℝ) := by
    apply Real.le_sqrt_of_sq_le
    rw [← Nat.cast_pow]
    exact_mod_cast (by simpa [pow_two] using Nat.sqrt_le N)
  linarith

/-- A "good" `r` is non-zero (`r` is divisible by a prime to an odd power). -/
theorem goodR_ne_zero {d q : ℕ} {r : ℤ} (h : goodR d q r) : r ≠ 0 := by
  obtain ⟨p, hp, _, hodd⟩ := h
  intro h0
  rw [h0] at hodd
  simp at hodd

/-- **The log comparison of the disc sum.**  For `r` in the `r`-range of the disc
(`|r| ≤ ⌊√N⌋ ≤ √N`),

  `log(2 + |r|·q) ≤ 2·log(2 + √q·N)`.

Indeed `|r|q ≤ √N·q ≤ N·q ≤ qN² ≤ (2 + √q·N)²`, and `log((2+s)²) = 2 log(2+s)`.  This replaces the
comparison `Work.FIArea7.KSum_arith_helpers` (6) of the box version, where the corresponding
quantity is `log(2 + √q·(2⌊√N⌋+1))`. -/
theorem log_discFib_le (q : ℕ) (N : ℕ) (r : ℤ) (hN : 1 ≤ N)
    (hr : r ∈ Finset.Icc (-(discSqrt N)) (discSqrt N)) :
    Real.log (2 + (r.natAbs : ℝ) * (q : ℝ))
      ≤ 2 * Real.log (2 + Real.sqrt (q : ℝ) * (N : ℝ)) := by
  set A : ℝ := Real.sqrt (q : ℝ) * (N : ℝ) with hA
  have hq0 : (0 : ℝ) ≤ (q : ℝ) := Nat.cast_nonneg _
  have hA0 : 0 ≤ A := by rw [hA]; positivity
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hle_sqrtN : Real.sqrt (N : ℝ) ≤ (N : ℝ) := by
    have h1 : Real.sqrt (N : ℝ) ≤ Real.sqrt ((N : ℝ) ^ 2) :=
      Real.sqrt_le_sqrt (by nlinarith [hN1])
    rwa [Real.sqrt_sq (by linarith : (0 : ℝ) ≤ (N : ℝ))] at h1
  have hkey : 2 + (r.natAbs : ℝ) * (q : ℝ) ≤ (2 + A) ^ 2 := by
    have h1 : (r.natAbs : ℝ) ≤ Real.sqrt (N : ℝ) := cast_natAbs_le_sqrt hr
    have h2 : (r.natAbs : ℝ) * (q : ℝ) ≤ Real.sqrt (N : ℝ) * (q : ℝ) :=
      mul_le_mul_of_nonneg_right h1 hq0
    have h3 : Real.sqrt (N : ℝ) * (q : ℝ) ≤ (N : ℝ) * (q : ℝ) :=
      mul_le_mul_of_nonneg_right hle_sqrtN hq0
    have h4 : (N : ℝ) * (q : ℝ) ≤ (q : ℝ) * (N : ℝ) ^ 2 := by
      have hN2 : (N : ℝ) ≤ (N : ℝ) ^ 2 := by nlinarith [hN1]
      calc (N : ℝ) * (q : ℝ) ≤ (N : ℝ) ^ 2 * (q : ℝ) :=
            mul_le_mul_of_nonneg_right hN2 hq0
        _ = (q : ℝ) * (N : ℝ) ^ 2 := by ring
    have h5 : (2 + A) ^ 2 = 4 + 4 * A + A ^ 2 := by ring
    have hA2 : A ^ 2 = (q : ℝ) * (N : ℝ) ^ 2 := by rw [hA, mul_pow, Real.sq_sqrt hq0]
    rw [h5, hA2]; linarith
  have hpos : 0 < 2 + (r.natAbs : ℝ) * (q : ℝ) := by positivity
  calc Real.log (2 + (r.natAbs : ℝ) * (q : ℝ)) ≤ Real.log ((2 + A) ^ 2) :=
        Real.log_le_log hpos hkey
    _ = 2 * Real.log (2 + A) := by rw [Real.log_pow]; norm_num

/-- **`⌊√N⌋^{3/2} ≤ N^{3/4}`** (the radius `⌊√N⌋` of the disc sum is `≤ √N`). -/
theorem discSqrt_mul_sqrt_le (N : ℕ) (hN : 1 ≤ N) :
    (discSqrt N : ℝ) * Real.sqrt (discSqrt N : ℝ) ≤ (N : ℝ) ^ ((3 : ℝ) / 4) := by
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have ht0 : (0 : ℝ) < (N : ℝ) := by linarith
  have hs0 : (0 : ℝ) ≤ (Nat.sqrt N : ℝ) := by positivity
  have hsle : (Nat.sqrt N : ℝ) ≤ Real.sqrt (N : ℝ) := by
    apply Real.le_sqrt_of_sq_le
    rw [← Nat.cast_pow]
    exact_mod_cast (by simpa [pow_two] using Nat.sqrt_le N)
  have key : (Nat.sqrt N : ℝ) * Real.sqrt (Nat.sqrt N : ℝ)
      ≤ Real.sqrt (N : ℝ) * Real.sqrt (Real.sqrt (N : ℝ)) :=
    mul_le_mul hsle (Real.sqrt_le_sqrt hsle) (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have hrhs : Real.sqrt (N : ℝ) * Real.sqrt (Real.sqrt (N : ℝ)) = (N : ℝ) ^ ((3 : ℝ) / 4) := by
    have h2 : Real.sqrt (Real.sqrt (N : ℝ)) = (((N : ℝ) ^ (1/2 : ℝ)) ^ (1/2 : ℝ)) := by
      rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow]
    have h3 : (((N : ℝ) ^ (1/2 : ℝ)) ^ (1/2 : ℝ)) = (N : ℝ) ^ (1/4 : ℝ) := by
      rw [← Real.rpow_mul ht0.le]; congr 1; norm_num
    rw [h2, h3, Real.sqrt_eq_rpow, ← Real.rpow_add ht0]
    congr 1
    norm_num
  have hcast : ((discSqrt N : ℤ) : ℝ) = (Nat.sqrt N : ℝ) := by simp [discSqrt_def]
  rw [hcast]
  linarith [key, hrhs]

end

end Work.FIArea7
