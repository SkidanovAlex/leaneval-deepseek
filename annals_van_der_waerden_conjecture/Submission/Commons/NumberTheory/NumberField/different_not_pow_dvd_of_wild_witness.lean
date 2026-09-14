import Mathlib.Algebra.Ring.IsFormallyReal
import Submission.Commons.NumberTheory.NumberField.tame_different

open scoped NumberField BigOperators
set_option autoImplicit false
set_option maxHeartbeats 0
-- `hsup` is part of the requested statement (used implicitly by the ideal decomposition);
-- the two `haveI`s below really are typeclass instances.
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

namespace Commons.NumberTheory.NumberField

/-!
# `different_not_pow_dvd_of_wild_witness`

Wild (higher-ramification) analogue of `not_dvd_pow_of_witness` (tame half of Dedekind's
different theorem), needed for the van der Waerden conjecture.

If the rational prime `p` splits in the ring of integers of a number field `K` as
`(p) = P^e · Q` with `P` a maximal ideal over `(p)` of ramification index `e`, and there is a
"wild witness at level `k`": an element `y` in `Q^(k+1)` whose integer trace is not divisible by
`p^(k+1)`, then `P^(e*(k+1))` does **not** divide the different ideal of `K`.

Proof (contrapositive): if `P^(e*(k+1)) ∣ differentIdeal`, then every element of the fractional
ideal `(P^(e*(k+1)))⁻¹` has integer trace (`intTrace_mem_of_dvd_pow_different`).  But
`y / p^(k+1)` belongs to `(P^(e*(k+1)))⁻¹`, because `y ∈ Q^(k+1)` and
`(p^(k+1)) = P^(e*(k+1)) · Q^(k+1)` imply `y · P^(e*(k+1)) ⊆ p^(k+1) 𝓞 K`; hence
`p^(k+1) ∣ Tr(y)`, contradicting the witness hypothesis.
-/

theorem different_not_pow_dvd_of_wild_witness {K : Type*} [Field K] [NumberField K]
    (p : ℕ) [Fact (Nat.Prime p)] (P : Ideal (NumberField.RingOfIntegers K))
    [P.IsMaximal] [P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ))]
    (Q : Ideal (NumberField.RingOfIntegers K)) (hsup : P ⊔ Q = ⊤)
    (hspl : (Ideal.span ({(p : ℤ)} : Set ℤ)).map (algebraMap ℤ (NumberField.RingOfIntegers K)) =
      P ^ P.ramificationIdx ℤ * Q)
    (k : ℕ) (y : NumberField.RingOfIntegers K) (hyQ : (y : NumberField.RingOfIntegers K) ∈ Q ^ (k + 1))
    (hy : ¬ (p : ℤ) ^ (k + 1) ∣ Algebra.intTrace ℤ (NumberField.RingOfIntegers K) y) :
    ¬ P ^ (P.ramificationIdx ℤ * (k + 1)) ∣ differentIdeal ℤ (NumberField.RingOfIntegers K) := by
  classical
  intro hdiv
  haveI : P.IsPrime := (inferInstance : P.IsMaximal).isPrime
  let S := NumberField.RingOfIntegers K
  let n : ℕ := k + 1
  let e : ℕ := P.ramificationIdx ℤ * n
  let pZ : Ideal ℤ := Ideal.span ({(p : ℤ)} : Set ℤ)
  let f : ℤ →+* S := algebraMap ℤ S
  haveI : P.LiesOver (TameDifferent.p₀ p) := by
    simpa [TameDifferent.p₀] using ‹P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ))›
  have hPbot : P ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot (TameDifferent.p₀_ne_bot p) P
  have hpK0 : (p : K) ≠ 0 := by exact_mod_cast (Nat.Prime.ne_zero (Fact.out : Nat.Prime p))
  have hpℚ0 : (p : ℚ) ≠ 0 := by exact_mod_cast (Nat.Prime.ne_zero (Fact.out : Nat.Prime p))
  have hpKn0 : (p : K) ^ n ≠ 0 := pow_ne_zero n hpK0
  have hpℚn0 : (p : ℚ) ^ n ≠ 0 := pow_ne_zero n hpℚ0
  have he0 : e ≠ 0 := by
    dsimp [e, n]
    exact mul_ne_zero (Ideal.ramificationIdx_pos (q := P) (R := ℤ)).ne' (Nat.succ_ne_zero k)
  let x : K := (y : K) * ((p : K) ^ n)⁻¹
  have hyP : ∀ m ∈ P ^ e, (y : S) * m ∈ (pZ.map f) ^ n := by
    intro m hm
    have hprod : Q ^ n * P ^ e = (pZ.map f) ^ n := by
      dsimp [n, e, pZ, f]
      calc
        Q ^ (k+1) * P ^ (P.ramificationIdx ℤ * (k+1))
            = P ^ (P.ramificationIdx ℤ * (k+1)) * Q ^ (k+1) := by rw [mul_comm]
        _ = (P ^ P.ramificationIdx ℤ) ^ (k+1) * Q ^ (k+1) := by rw [pow_mul]
        _ = (P ^ P.ramificationIdx ℤ * Q) ^ (k+1) := by rw [← mul_pow]
        _ = (pZ.map f) ^ (k+1) := by rw [← hspl]
    have hmem : (y : S) * m ∈ Q ^ n * P ^ e := Ideal.mul_mem_mul hyQ hm
    rwa [hprod] at hmem
  have hPef : ((P ^ e : Ideal S) : FractionalIdeal (nonZeroDivisors S) K) ≠ 0 := by
    simpa using (pow_ne_zero e hPbot)
  have hx : x ∈ ((P ^ e : Ideal S)⁻¹ : FractionalIdeal (nonZeroDivisors S) K) := by
    apply (FractionalIdeal.mem_inv_iff
      (I := ((P ^ e : Ideal S) : FractionalIdeal (nonZeroDivisors S) K)) hPef).mpr
    intro a ha
    rcases (FractionalIdeal.mem_coeIdeal (S := nonZeroDivisors S) (x := a) (I := P ^ e)).mp ha with ⟨m, hm, rfl⟩
    have hyPm : (y : S) * m ∈ (pZ.map f) ^ n := hyP m hm
    have hspan : (pZ.map f) ^ n = Ideal.span ({(p : S) ^ n} : Set S) := by
      dsimp [pZ, f]
      rw [← Ideal.map_pow, Ideal.span_singleton_pow]
      simp [Ideal.map_span]
    rcases (Ideal.mem_span_singleton.mp (by simpa [hspan] using hyPm)) with ⟨c, hc⟩
    have hcK : ((y * m : S) : K) = (p : K) ^ n * (c : K) := by
      calc
        ((y * m : S) : K) = (((p : S) ^ n * c : S) : K) := congrArg (algebraMap S K) hc
        _ = ((p : S) ^ n : K) * (c : K) := by simp
        _ = (p : K) ^ n * (c : K) := by simp
    have hx' : x * (m : K) = (c : K) := by
      dsimp [x]
      calc
        ((y : K) * ((p : K) ^ n)⁻¹) * (m : K) = ((y : K) * (m : K)) * ((p : K) ^ n)⁻¹ := by ring
        _ = ((y * m : S) : K) * ((p : K) ^ n)⁻¹ := by congr 1
        _ = (((p : K) ^ n) * (c : K)) * ((p : K) ^ n)⁻¹ := by rw [hcK]
        _ = (c : K) := by field_simp [hpKn0]
    refine (FractionalIdeal.mem_one_iff (P := K) (R := S) (S := nonZeroDivisors S)).mpr ⟨c, hx'.symm⟩
  have htr := intTrace_mem_of_dvd_pow_different (K := K) P hPbot e he0 hdiv x hx
  rcases htr with ⟨z, hz⟩
  have htrY : Algebra.trace ℚ K (y : K) = (Algebra.intTrace ℤ S y : ℚ) :=
    (Algebra.algebraMap_intTrace (A := ℤ) (K := ℚ) (L := K) (B := S) y).symm
  have hpcast : (p : K) = algebraMap ℚ K (p : ℚ) := by norm_num
  have hpcastn : (p : K) ^ n = algebraMap ℚ K ((p : ℚ) ^ n) := by
    rw [hpcast]
    rw [map_pow]
  have hpinv : ((p : K) ^ n)⁻¹ = algebraMap ℚ K (((p : ℚ) ^ n)⁻¹) := by
    apply mul_left_cancel₀ hpKn0
    calc
      (p : K) ^ n * ((p : K) ^ n)⁻¹ = 1 := mul_inv_cancel₀ hpKn0
      _ = (p : K) ^ n * algebraMap ℚ K (((p : ℚ) ^ n)⁻¹) := by
        rw [hpcastn, ← map_mul]
        rw [mul_inv_cancel₀ hpℚn0]
        simp
  have hsmul : x = ((p : ℚ) ^ n)⁻¹ • (y : K) := by
    dsimp [x]
    rw [hpinv, mul_comm, ← Algebra.smul_def]
  have htrX : Algebra.trace ℚ K x = (((p : ℚ) ^ n)⁻¹) * Algebra.trace ℚ K (y : K) := by
    rw [hsmul, LinearMap.map_smul, smul_eq_mul]
  have hmain : (p : ℚ) ^ n * (z : ℚ) = (Algebra.intTrace ℤ S y : ℚ) := by
    calc
      (p : ℚ) ^ n * (z : ℚ) = (p : ℚ) ^ n * Algebra.trace ℚ K x := by
        exact congrArg (fun t : ℚ => (p : ℚ) ^ n * t) hz
      _ = Algebra.trace ℚ K (y : K) := by
        rw [htrX, htrY]
        field_simp [hpℚn0]
      _ = (Algebra.intTrace ℤ S y : ℚ) := htrY
  refine hy ⟨z, ?_⟩
  have hz' : (((p : ℤ) ^ n * z : ℤ) : ℚ) = (Algebra.intTrace ℤ S y : ℚ) := by
    rw [Int.cast_mul, Int.cast_pow]
    norm_num
    exact hmain
  exact_mod_cast hz'.symm

end Commons.NumberTheory.NumberField