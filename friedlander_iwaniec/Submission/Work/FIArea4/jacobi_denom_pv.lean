import Mathlib
import Submission.Work.FIPlan.Interface
import Submission.Work.FIArea4.pv_dirichlet
import Submission.Work.FIArea4.JacobiChar
import Submission.Work.FIArea4.jacobiChar_isPrimitive
import Submission.Work.FIArea4.polya_vinogradov
import Submission.Work.FIArea4.jacobi_neg_one_exists

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.FIArea4

open scoped BigOperators
open Finset

set_option linter.style.haveILetI false

attribute [local instance] Classical.propDecidable

noncomputable section

/-! ### Elementary arithmetic of `J(4n | ·)` -/

/-- `16n` and `4n` have the same prime divisors, so coprimality to one is coprimality to the other. -/
lemma coprime_sixteen_mul_iff_coprime_four_mul (n m : ℕ) :
    Nat.Coprime m (16 * n) ↔ Nat.Coprime m (4 * n) := by
  constructor
  · intro h
    exact Nat.Coprime.coprime_dvd_right (⟨4, by ring⟩ : 4 * n ∣ 16 * n) h
  · intro h
    rw [show 16 * n = 4 * (4 * n) by ring, Nat.coprime_mul_iff_right]
    exact ⟨Nat.Coprime.coprime_dvd_right (Nat.dvd_mul_right 4 n) h, h⟩

/-- An `m` coprime to `16n` is odd (`n ≥ 1`). -/
lemma odd_of_coprime_sixteen_mul {n m : ℕ} (h : Nat.Coprime m (16 * n)) : Odd m :=
  Nat.coprime_two_right.mp
    (Nat.Coprime.coprime_dvd_right (show 2 ∣ 16 * n by exact ⟨8 * n, by ring⟩) h)

/-- `J(4n | m) = 0` for `m ≥ 1` exactly when `m` is not coprime to `16n`. -/
lemma jacobiSym_four_mul_eq_zero_iff {n m : ℕ} (_hn : 1 ≤ n) (hm : 1 ≤ m) :
    jacobiSym (4 * n : ℤ) m = 0 ↔ ¬ Nat.Coprime m (16 * n) := by
  rw [jacobiSym.eq_zero_iff]
  have hcast : (4 * (n : ℤ)) = ((4 * n : ℕ) : ℤ) := by push_cast; ring
  constructor
  · rintro ⟨-, hgcd⟩ hc
    apply hgcd
    rw [hcast, Int.gcd_natCast_natCast, Nat.gcd_comm]
    exact Nat.coprime_iff_gcd_eq_one.mp ((coprime_sixteen_mul_iff_coprime_four_mul n m).mp hc)
  · intro hc
    refine ⟨by omega, ?_⟩
    rw [hcast, Int.gcd_natCast_natCast]
    intro hcontra
    exact hc ((coprime_sixteen_mul_iff_coprime_four_mul n m).mpr (Nat.coprime_comm.mp hcontra))

/-- Periodicity of `J(4n | ·)` modulo `16n` on odd arguments (`jacobiSym.mod_right`). -/
lemma jacobiSym_four_mul_period {n m : ℕ} (hm : Odd m) :
    jacobiSym (4 * n : ℤ) m = jacobiSym (4 * n : ℤ) (m % (16 * n)) := by
  have h := jacobiSym.mod_right (4 * n : ℤ) hm
  rw [show ((4 * n : ℤ)).natAbs = 4 * n by rw [Int.natAbs_mul, Int.natAbs_natCast]; rfl] at h
  simpa [show 4 * (4 * n) = 16 * n by ring] using h

/-! ### The Dirichlet character `a ↦ J(4n | a)` of level `16n` -/

lemma natCoprime_val_of_isUnit {n : ℕ} [NeZero n] {a : ZMod (16 * n)} (ha : IsUnit a) :
    Nat.Coprime a.val (16 * n) :=
  (ZMod.isUnit_iff_coprime a.val (16 * n)).mp (by rwa [ZMod.natCast_zmod_val])

lemma val_ne_zero_of_isUnit {n : ℕ} [NeZero n] {a : ZMod (16 * n)} (ha : IsUnit a) :
    a.val ≠ 0 := by
  intro h0
  have hc := natCoprime_val_of_isUnit ha
  rw [h0, Nat.Coprime, Nat.gcd_zero_left] at hc
  have hn : 1 ≤ n := NeZero.pos n
  omega

lemma val_odd_of_isUnit {n : ℕ} [NeZero n] {a : ZMod (16 * n)} (ha : IsUnit a) :
    Odd a.val :=
  odd_of_coprime_sixteen_mul (natCoprime_val_of_isUnit ha)

/-- **The Dirichlet character of level `16n` whose values on `m : ℕ` are `J(4n | m)`**:
`a ↦ J(4n | a.val)`, and `0` at the non-units of `ZMod (16n)`.  (The vanishing at `0 : ZMod (16n)`
is forced by the multiplicative structure, since Mathlib's convention gives `J(4n | 0) = 1`.) -/
def jacobiDenomChar (n : ℕ) [NeZero n] : DirichletCharacter ℂ (16 * n) where
  toMonoidHom :=
    { toFun := fun a => if IsUnit a then (jacobiSym (4 * n : ℤ) a.val : ℂ) else 0
      map_one' := by
        rw [if_pos isUnit_one]
        have hmod : (1 : ZMod (16 * n)).val = 1 := by
          rw [show (1 : ZMod (16 * n)) = ((1 : ℕ) : ZMod (16 * n)) from by simp,
            ZMod.val_natCast, Nat.mod_eq_of_lt (by have := NeZero.pos n; omega)]
        rw [hmod, jacobiSym.one_right]
        norm_num
      map_mul' := fun x y => by
        by_cases hx : IsUnit x
        · by_cases hy : IsUnit y
          · have hxy : IsUnit (x * y) := hx.mul hy
            rw [if_pos hx, if_pos hy, if_pos hxy]
            haveI : NeZero x.val := ⟨val_ne_zero_of_isUnit hx⟩
            haveI : NeZero y.val := ⟨val_ne_zero_of_isUnit hy⟩
            have hodd : Odd (x.val * y.val) := (val_odd_of_isUnit hx).mul (val_odd_of_isUnit hy)
            have hper := jacobiSym_four_mul_period (n := n) hodd
            rw [ZMod.val_mul, ← hper, jacobiSym.mul_right]
            push_cast
            ring
          · have hxy : ¬ IsUnit (x * y) := fun h => hy (IsUnit.mul_iff.mp h).2
            rw [if_pos hx, if_neg hy, if_neg hxy]
            ring
        · have hxy : ¬ IsUnit (x * y) := fun h => hx (IsUnit.mul_iff.mp h).1
          rw [if_neg hx, if_neg hxy]
          ring }
  map_nonunit' := fun a ha => by
    show (if IsUnit a then (jacobiSym (4 * n : ℤ) a.val : ℂ) else 0) = 0
    rw [if_neg ha]

@[simp] lemma jacobiDenomChar_apply (n : ℕ) [NeZero n] (a : ZMod (16 * n)) :
    jacobiDenomChar n a
      = if IsUnit a then (jacobiSym (4 * n : ℤ) a.val : ℂ) else 0 := rfl

/-- On naturals, the character of level `16n` takes the values of the Jacobi symbol `J(4n | m)`. -/
lemma jacobiDenomChar_apply_nat {n m : ℕ} [NeZero n] (hm : 1 ≤ m) :
    jacobiDenomChar n (m : ZMod (16 * n)) = (jacobiSym (4 * n : ℤ) m : ℂ) := by
  show (if IsUnit (m : ZMod (16 * n)) then (jacobiSym (4 * n : ℤ) (m : ZMod (16 * n)).val : ℂ)
      else 0) = (jacobiSym (4 * n : ℤ) m : ℂ)
  by_cases hc : Nat.Coprime m (16 * n)
  · rw [if_pos ((ZMod.isUnit_iff_coprime m (16 * n)).mpr hc), ZMod.val_natCast]
    exact_mod_cast (jacobiSym_four_mul_period (odd_of_coprime_sixteen_mul hc)).symm
  · rw [if_neg (fun h => hc ((ZMod.isUnit_iff_coprime m (16 * n)).mp h))]
    rw [jacobiSym_four_mul_eq_zero_iff (NeZero.pos n) hm |>.mpr hc]
    norm_num

/-- The character of level `16n` is not the principal character when `n` is not a square. -/
lemma jacobiDenomChar_ne_one {n : ℕ} [NeZero n] (hn : 1 ≤ n)
    (hnsq : ∀ k : ℕ, n ≠ k ^ 2) : jacobiDenomChar n ≠ 1 := by
  intro hcontra
  obtain ⟨u, huodd, hucop, hJu⟩ := jacobi_neg_one_exists n hn hnsq
  have hcop16 : Nat.Coprime u (16 * n) := by
    rw [coprime_sixteen_mul_iff_coprime_four_mul, Nat.coprime_mul_iff_right]
    refine ⟨?_, hucop⟩
    have h2 : Nat.Coprime u 2 := Nat.coprime_two_right.mpr huodd
    simpa using h2.pow_right 2
  have hu1 : 1 ≤ u := by rcases huodd with ⟨k, hk⟩; omega
  have hunit : IsUnit (u : ZMod (16 * n)) := (ZMod.isUnit_iff_coprime u (16 * n)).mpr hcop16
  have hval : jacobiDenomChar n (u : ZMod (16 * n)) = -1 := by
    rw [jacobiDenomChar_apply_nat hu1]
    have hmul := jacobiSym.mul_left (4 : ℤ) (n : ℤ) u
    rw [jacobiSym.at_four huodd, hJu, mul_neg, mul_one] at hmul
    have hJ : jacobiSym (4 * n : ℤ) u = -1 := by simpa using hmul
    rw [hJ]
    norm_num
  rw [hcontra, MulChar.one_apply hunit] at hval
  norm_num at hval

/-- The conductor of the character of level `16n` exceeds `1` when `n` is no square. -/
lemma conductor_jacobiDenomChar_gt_one {n : ℕ} [NeZero n] (hn : 1 ≤ n)
    (hnsq : ∀ k : ℕ, n ≠ k ^ 2) : 1 < (jacobiDenomChar n).conductor := by
  have hne := jacobiDenomChar_ne_one hn hnsq
  have h1 : (jacobiDenomChar n).conductor ≠ 1 :=
    fun h => hne (DirichletCharacter.eq_one_iff_conductor_eq_one.mpr h)
  have h0 : (jacobiDenomChar n).conductor ≠ 0 := DirichletCharacter.conductor_ne_zero _
  omega

/-! ### Pólya–Vinogradov in the denominator variable -/

/-- **Pólya–Vinogradov for the Jacobi symbol in the denominator variable.**
For `n ≥ 1` which is not a perfect square, `m ↦ J(4n | m)` (`J` the Jacobi symbol, evaluated with
Mathlib's convention `jacobiSym a b = ∏_{p | b} legendreSym p a ^ (b.factorization p)`, so that
`J(4n | m) = 0` for even `m`) is the values of a non-principal Dirichlet character of level `16n`
(`J(4n | m) = J(4n | m % 16n)` by `jacobiSym.mod_right`, multiplicative in `m` by
`jacobiSym.mul_right`, and vanishing exactly on the non-units of `ZMod (16n)`), so its partial sums
are `O(√n log n)` *uniformly in the length* `M`. -/
theorem jacobi_denom_pv :
    ∃ C : ℝ, 0 < C ∧ ∀ (n M : ℕ), 1 ≤ n → (∀ k : ℕ, n ≠ k ^ 2) →
      |∑ m ∈ Finset.Icc 1 M, (jacobiSym (4 * n : ℤ) m : ℝ)|
        ≤ C * Real.sqrt n * (Real.log n + 2) := by
  obtain ⟨C₀, hC₀pos, hC₀⟩ := pv_dirichlet
  refine ⟨12 * C₀, by positivity, ?_⟩
  intro n M hn hnsq
  haveI : NeZero n := ⟨by omega⟩
  haveI : NeZero (16 * n) := ⟨by omega⟩
  have hcast : ((16 * n : ℕ) : ℝ) = 16 * (n : ℝ) := by push_cast; ring
  have hlog : Real.log ((16 * n : ℕ) : ℝ) + 1 ≤ 3 * (Real.log n + 2) := by
    rw [hcast, Real.log_mul (by norm_num) (by rw [Nat.cast_ne_zero]; omega)]
    have hlog16 : Real.log (16 : ℝ) ≤ 4 := by
      have h : Real.log (2 : ℝ) ≤ 1 := by
        have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num)
        linarith
      have h16 : (16 : ℝ) = 2 ^ (4 : ℕ) := by norm_num
      rw [h16, Real.log_pow]
      push_cast
      linarith
    have hn0 : (0 : ℝ) ≤ Real.log n := Real.log_nonneg (by exact_mod_cast hn)
    linarith
  have hsqrt : Real.sqrt ((16 * n : ℕ) : ℝ) = 4 * Real.sqrt n := by
    rw [hcast, Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 16)]
    norm_num
  have hbound := hC₀ (16 * n) M (jacobiDenomChar n) (conductor_jacobiDenomChar_gt_one hn hnsq)
  have hsum : ∑ m ∈ Finset.Icc 1 M, jacobiDenomChar n (m : ZMod (16 * n))
      = (((∑ m ∈ Finset.Icc 1 M, (jacobiSym (4 * n : ℤ) m : ℝ)) : ℝ) : ℂ) := by
    rw [Complex.ofReal_sum]
    refine Finset.sum_congr rfl (fun m hm => ?_)
    have hm1 : 1 ≤ m := (Finset.mem_Icc.mp hm).1
    rw [jacobiDenomChar_apply_nat hm1]
    push_cast
    ring
  calc |∑ m ∈ Finset.Icc 1 M, (jacobiSym (4 * n : ℤ) m : ℝ)|
      = ‖∑ m ∈ Finset.Icc 1 M, jacobiDenomChar n (m : ZMod (16 * n))‖ := by
        rw [hsum, Complex.norm_real, Real.norm_eq_abs]
    _ ≤ C₀ * Real.sqrt ((16 * n : ℕ) : ℝ) * (Real.log ((16 * n : ℕ) : ℝ) + 1) := hbound
    _ = C₀ * (4 * Real.sqrt n) * (Real.log ((16 * n : ℕ) : ℝ) + 1) := by rw [hsqrt]
    _ ≤ C₀ * (4 * Real.sqrt n) * (3 * (Real.log n + 2)) := by
        have h1 : (0 : ℝ) ≤ C₀ * (4 * Real.sqrt n) := by positivity
        exact mul_le_mul_of_nonneg_left hlog h1
    _ = 12 * C₀ * Real.sqrt n * (Real.log n + 2) := by ring

end

end Work.FIArea4
