import Mathlib
import Submission.NK.Chebotarev.SqrtInCyclotomic
import Submission.NK.Chebotarev.QuadraticGaussSumInCyclotomic
import Submission.NK.Chebotarev.ExistsSqEqNatCastOfPrimeSqrt
import Submission.NK.Chebotarev.ExistsSqEqPrimeOfPrimitiveRoot
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Square roots of rationals inside cyclotomic fields

The **quadratic case of Kronecker–Weber** says that every quadratic field `ℚ(√d)` is contained in a
cyclotomic field `ℚ(ζ_n)`.  In the form needed by the Čebotarev chapter we prove the stronger, fully
explicit statement that *every* rational `d` has a square root in some cyclotomic field:
`NK.Chebotarev.ExistsSqrtInCyclotomic`.

The argument is the classical one.

* `√(-1) = ζ_4` and `√2 = ζ_8 + ζ_8⁻¹` live in `ℚ(ζ_8)`; more generally, if `8 ∣ N` then
  `ℚ(ζ_N)` contains `√(-1)` and `√2`
  (`exists_sq_eq_neg_one_in_cyclotomic`, `exists_sq_eq_two_in_cyclotomic`).
* For an odd prime `p`, the quadratic Gauss sum shows that `ℚ(ζ_p, i) = ℚ(ζ_{4p})` contains `√p`
  (`NK.Chebotarev.ExistsSqEqPrimeOfPrimitiveRoot`, from
  `NK.Chebotarev.QuadraticGaussSumInCyclotomic`).
* A finite product of squares is a square, so `√m` for `m = ±∏ p^{e_p}` is a product of the
  `√p` and of `√(-1)` (`NK.Chebotarev.ExistsSqEqNatCastOfPrimeSqrt`).  Collecting everything,
  `ℚ(ζ_{8|m|})` contains `√m` (`exists_sq_eq_intCast_in_cyclotomic`).
* Finally `√(a/b) = √(ab)/b`, so every rational has a square root in a cyclotomic field at
  universe level `0` (`nonempty_sqrtInCyclotomic_zero`), and the statement follows at every
  universe level by transporting the field along `ULift`
  (`isCyclotomicExtension_ulift`, `nonempty_sqrtInCyclotomic_ulift`).
-/

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

universe u v

namespace NK.Chebotarev

/-! ## Extracting primitive roots of the divisors of the level

Inside `ℚ(ζ_N)` the element `ω ^ (N / d)` is a primitive `d`-th root of unity for every `d ∣ N`.
This is the only arithmetic input needed to move the Gauss sum for `p` from `ℚ(ζ_p)` into
`ℚ(ζ_N)`. -/

theorem isPrimitiveRoot_pow_div {F : Type*} [Field F] {N d : ℕ} {ω : F}
    (hω : IsPrimitiveRoot ω N) (hN : N ≠ 0) (hd : d ≠ 0) (hdiv : d ∣ N) :
    IsPrimitiveRoot (ω ^ (N / d)) d := by
  have hNd : N / d ≠ 0 :=
    Nat.div_ne_zero_iff.mpr ⟨hd, Nat.le_of_dvd (Nat.pos_of_ne_zero hN) hdiv⟩
  have := hω.pow_of_dvd (p := N / d) hNd (Nat.div_dvd_of_dvd hdiv)
  rwa [Nat.div_div_self hdiv hN] at this

/-! ## `√(-1)` and `√2` in `ℚ(ζ_N)` when `8 ∣ N` -/

/-- If `8 ∣ N` and `N ≠ 0` then `ℚ(ζ_N)` contains a square root of `-1`, namely `ζ_N ^ (N/4)`. -/
theorem exists_sq_eq_neg_one_in_cyclotomic (N : ℕ) [NeZero N] (h8 : 8 ∣ N) :
    ∃ i : CyclotomicField N ℚ, i ^ 2 = -1 := by
  haveI : IsCyclotomicExtension {N} ℚ (CyclotomicField N ℚ) :=
    CyclotomicField.isCyclotomicExtension N ℚ
  obtain ⟨ω, hω⟩ := IsCyclotomicExtension.exists_isPrimitiveRoot ℚ (CyclotomicField N ℚ)
    (Set.mem_singleton N) (NeZero.ne N)
  have h4 : 4 ∣ N := dvd_trans (by norm_num) h8
  refine ⟨ω ^ (N / 4), ?_⟩
  have hζ : IsPrimitiveRoot (ω ^ (N / 4)) 4 :=
    isPrimitiveRoot_pow_div hω (NeZero.ne N) (by norm_num) h4
  have h2 : IsPrimitiveRoot ((ω ^ (N / 4)) ^ 2) 2 := by
    have := hζ.pow_of_dvd (p := 2) (by norm_num) (by norm_num : 2 ∣ 4)
    simpa using this
  exact h2.eq_neg_one_of_two_right

/-- If `8 ∣ N` and `N ≠ 0` then `ℚ(ζ_N)` contains a square root of `2`, namely `ζ_8 + ζ_8⁻¹` for
`ζ_8 = ζ_N ^ (N/8)`. -/
theorem exists_sq_eq_two_in_cyclotomic (N : ℕ) [NeZero N] (h8 : 8 ∣ N) :
    ∃ s : CyclotomicField N ℚ, s ^ 2 = 2 := by
  haveI : IsCyclotomicExtension {N} ℚ (CyclotomicField N ℚ) :=
    CyclotomicField.isCyclotomicExtension N ℚ
  obtain ⟨ω, hω⟩ := IsCyclotomicExtension.exists_isPrimitiveRoot ℚ (CyclotomicField N ℚ)
    (Set.mem_singleton N) (NeZero.ne N)
  have hβ : IsPrimitiveRoot (ω ^ (N / 8)) 8 :=
    isPrimitiveRoot_pow_div hω (NeZero.ne N) (by norm_num) h8
  refine ⟨ω ^ (N / 8) + (ω ^ (N / 8))⁻¹, ?_⟩
  -- `β = ζ_8` satisfies `β ^ 4 = -1`, hence `β ^ 2 + (β ^ 2)⁻¹ = 0`
  have hβne : ω ^ (N / 8) ≠ 0 := hβ.ne_zero (by norm_num)
  have h4 : IsPrimitiveRoot ((ω ^ (N / 8)) ^ 2) 4 := by
    have := hβ.pow_of_dvd (p := 2) (by norm_num) (by norm_num : 2 ∣ 8)
    simpa using this
  have h2 : IsPrimitiveRoot (((ω ^ (N / 8)) ^ 2) ^ 2) 2 := by
    have := h4.pow_of_dvd (p := 2) (by norm_num) (by norm_num : 2 ∣ 4)
    simpa using this
  have hb2 : ((ω ^ (N / 8)) ^ 2) ^ 2 = -1 := h2.eq_neg_one_of_two_right
  have hb4 : (ω ^ (N / 8)) ^ 4 = -1 := by
    rw [← pow_mul] at hb2; norm_num at hb2; exact hb2
  have h3 : (ω ^ (N / 8)) ^ 2 + ((ω ^ (N / 8)) ^ 2)⁻¹ = 0 := by
    have hb2ne : (ω ^ (N / 8)) ^ 2 ≠ 0 := pow_ne_zero 2 hβne
    have hmul : ((ω ^ (N / 8)) ^ 2 + ((ω ^ (N / 8)) ^ 2)⁻¹) * (ω ^ (N / 8)) ^ 2 = 0 := by
      field_simp
      rw [hb4]; ring
    exact (mul_eq_zero.mp hmul).resolve_right hb2ne
  -- `(β + β⁻¹) ^ 2 = β ^ 2 + 2 * β * β⁻¹ + β⁻² = 2`
  rw [add_sq, inv_pow]
  have hmid : 2 * ω ^ (N / 8) * (ω ^ (N / 8))⁻¹ = 2 := by
    rw [mul_assoc, mul_inv_cancel₀ hβne, mul_one]
  rw [hmid]
  linear_combination h3

/-! ## A square root of an integer inside `ℚ(ζ_{8|m|})` -/

/-- **`ℚ(ζ_{8|m|})` contains a square root of the integer `m`.**  The primes dividing `m` are the
primes dividing `8|m|`, so `ℚ(ζ_{8|m|})` contains `√p` for each of them (Gauss sum, together with
`√(-1)` and `√2` from the level `8`), and a product of square roots is a square root of the
product. -/
theorem exists_sq_eq_intCast_in_cyclotomic (m : ℤ) :
    ∃ x : CyclotomicField (8 * m.natAbs) ℚ,
      x ^ 2 = (m : CyclotomicField (8 * m.natAbs) ℚ) := by
  rcases eq_or_ne m 0 with rfl | hm
  · exact ⟨0, by norm_num⟩
  have hposM : 0 < m.natAbs := Int.natAbs_pos.mpr hm
  have hNpos : 0 < 8 * m.natAbs := by omega
  haveI : NeZero (8 * m.natAbs) := ⟨hNpos.ne'⟩
  haveI : IsCyclotomicExtension {8 * m.natAbs} ℚ (CyclotomicField (8 * m.natAbs) ℚ) :=
    CyclotomicField.isCyclotomicExtension (8 * m.natAbs) ℚ
  obtain ⟨ω, hω⟩ := IsCyclotomicExtension.exists_isPrimitiveRoot ℚ
    (CyclotomicField (8 * m.natAbs) ℚ) (Set.mem_singleton _) (NeZero.ne (8 * m.natAbs))
  obtain ⟨i, hi⟩ := exists_sq_eq_neg_one_in_cyclotomic (8 * m.natAbs) (dvd_mul_right 8 _)
  obtain ⟨s, hs⟩ := exists_sq_eq_two_in_cyclotomic (8 * m.natAbs) (dvd_mul_right 8 _)
  -- for every prime `p ∣ m.natAbs`, `ℚ(ζ_{8|m|})` contains a square root of `p`
  have hprime : ∀ p : ℕ, Nat.Prime p → p ∣ m.natAbs →
      ∃ x : CyclotomicField (8 * m.natAbs) ℚ,
        x ^ 2 = (p : CyclotomicField (8 * m.natAbs) ℚ) := by
    intro p hp hpdiv
    have hpN : p ∣ 8 * m.natAbs := dvd_mul_of_dvd_right hpdiv 8
    rcases eq_or_ne p 2 with rfl | hp2
    · exact ⟨s, by simpa using hs⟩
    · haveI : Fact p.Prime := ⟨hp⟩
      have hζ : IsPrimitiveRoot (ω ^ ((8 * m.natAbs) / p)) p :=
        isPrimitiveRoot_pow_div hω hNpos.ne' hp.ne_zero hpN
      exact ExistsSqEqPrimeOfPrimitiveRoot p hp2 hζ hi
  obtain ⟨y, hy⟩ := ExistsSqEqNatCastOfPrimeSqrt m.natAbs hprime
  rcases lt_trichotomy m 0 with hneg | hzer | hpos
  · -- `m < 0`: multiply the square root of `|m|` by `√(-1)`
    refine ⟨y * i, ?_⟩
    have hnm : (m.natAbs : ℤ) = -m := by
      rw [← Int.natAbs_neg]
      exact Int.natAbs_of_nonneg (by omega)
    have hZ : -((m.natAbs : ℤ)) = m := by omega
    have key : (m : CyclotomicField (8 * m.natAbs) ℚ)
        = ((-((m.natAbs : ℤ)) : ℤ) : CyclotomicField (8 * m.natAbs) ℚ) :=
      congrArg (fun z : ℤ => (z : CyclotomicField (8 * m.natAbs) ℚ)) hZ.symm
    have hcast : (m : CyclotomicField (8 * m.natAbs) ℚ)
        = -((m.natAbs : ℕ) : CyclotomicField (8 * m.natAbs) ℚ) := by
      rw [key, Int.cast_neg, Int.cast_natCast]
    rw [hcast, mul_pow, hy, hi]
    ring
  · exact absurd hzer hm
  · -- `m > 0`: the square root of `|m| = m` itself
    have hnm : (m.natAbs : ℤ) = m := Int.natAbs_of_nonneg (le_of_lt hpos)
    have key : (((m.natAbs : ℤ)) : CyclotomicField (8 * m.natAbs) ℚ)
        = (m : CyclotomicField (8 * m.natAbs) ℚ) :=
      congrArg (fun z : ℤ => (z : CyclotomicField (8 * m.natAbs) ℚ)) hnm
    have hcast : ((m.natAbs : ℕ) : CyclotomicField (8 * m.natAbs) ℚ)
        = (m : CyclotomicField (8 * m.natAbs) ℚ) := by
      rw [← Int.cast_natCast, key]
    exact ⟨y, by rw [hy, hcast]⟩

/-! ## Every rational has a square root in a cyclotomic field -/

/-- **Universe level `0` form.**  For `d = a / b` with `b ≠ 0` we have `√d = √(ab) / b`, and
`√(ab) ∈ ℚ(ζ_{8|ab|})` by `exists_sq_eq_intCast_in_cyclotomic`. -/
theorem nonempty_sqrtInCyclotomic_zero (d : ℚ) : Nonempty (SqrtInCyclotomic.{0} d) := by
  rcases eq_or_ne d 0 with rfl | hd
  · -- `d = 0`: the trivial cyclotomic field `ℚ(ζ_1) = ℚ`
    haveI : IsCyclotomicExtension {1} ℚ (CyclotomicField 1 ℚ) :=
      CyclotomicField.isCyclotomicExtension 1 ℚ
    exact ⟨{ n := 1, hn := one_pos, F := CyclotomicField 1 ℚ, x := 0, x_sq := by simp }⟩
  · set a : ℤ := d.num with ha
    set b : ℕ := d.den with hb
    have hbpos : 0 < b := by rw [hb]; exact d.pos
    have hdeq : d = (a : ℚ) / (b : ℚ) := by
      rw [ha, hb]; exact (Rat.num_div_den d).symm
    set m : ℤ := a * b with hm
    have hmne : m ≠ 0 := by
      rw [hm]
      intro h
      have hbZ : (b : ℤ) ≠ 0 := by exact_mod_cast hbpos.ne'
      have ha0 : a = 0 := (mul_eq_zero.mp h).resolve_right hbZ
      rw [ha0] at hdeq
      simp at hdeq
      exact hd hdeq
    have hd2 : d = (m : ℚ) / (b : ℚ) ^ 2 := by
      rw [hdeq, hm]
      push_cast
      field_simp
    obtain ⟨y, hy⟩ := exists_sq_eq_intCast_in_cyclotomic m
    have hNpos : 0 < 8 * m.natAbs := by
      have := Int.natAbs_pos.mpr hmne
      omega
    haveI : NeZero (8 * m.natAbs) := ⟨hNpos.ne'⟩
    haveI : IsCyclotomicExtension {8 * m.natAbs} ℚ (CyclotomicField (8 * m.natAbs) ℚ) :=
      CyclotomicField.isCyclotomicExtension (8 * m.natAbs) ℚ
    refine ⟨{ n := 8 * m.natAbs, hn := hNpos, F := CyclotomicField (8 * m.natAbs) ℚ,
              x := y / (b : CyclotomicField (8 * m.natAbs) ℚ), x_sq := ?_ }⟩
    have hbF : (b : CyclotomicField (8 * m.natAbs) ℚ) ≠ 0 :=
      Nat.cast_ne_zero.mpr hbpos.ne'
    calc (y / (b : CyclotomicField (8 * m.natAbs) ℚ)) ^ 2
        = y ^ 2 / (b : CyclotomicField (8 * m.natAbs) ℚ) ^ 2 := by rw [div_pow]
      _ = (m : CyclotomicField (8 * m.natAbs) ℚ)
            / (b : CyclotomicField (8 * m.natAbs) ℚ) ^ 2 := by rw [hy]
      _ = algebraMap ℚ (CyclotomicField (8 * m.natAbs) ℚ)
            ((m : ℚ) / (b : ℚ) ^ 2) := by
          rw [map_div₀, map_pow, map_natCast, map_intCast]
      _ = algebraMap ℚ (CyclotomicField (8 * m.natAbs) ℚ) d := by rw [← hd2]

/-! ## Transport to an arbitrary universe level -/

/-- `IsCyclotomicExtension` transfers along the algebra equivalence `ULift.algEquiv`. -/
theorem isCyclotomicExtension_ulift {S : Set ℕ} {A : Type*} {B : Type v} [CommRing A] [CommRing B]
    [Algebra A B] (h : IsCyclotomicExtension S A B) :
    IsCyclotomicExtension S A (ULift.{u} B) := by
  letI := h
  exact IsCyclotomicExtension.equiv S A B (ULift.algEquiv (R := A) (A := B)).symm

/-- **Universe lifting.**  A square root of `d` in a cyclotomic field can be moved to any universe
level by transporting the field along `ULift`. -/
theorem nonempty_sqrtInCyclotomic_ulift (d : ℚ) (h : Nonempty (SqrtInCyclotomic.{0} d)) :
    Nonempty (SqrtInCyclotomic.{u} d) := by
  obtain ⟨S⟩ := h
  -- fix the `Algebra ℚ (ULift S.F)` instance, so that the local cyclotomic and number field
  -- structures below are stated for the *transported* algebra structure `ULift.algebra`
  letI : Algebra ℚ (ULift.{u} S.F) := ULift.algebra
  haveI : IsCyclotomicExtension {S.n} ℚ (ULift.{u} S.F) := by
    letI := S.cycloF
    exact IsCyclotomicExtension.equiv {S.n} ℚ S.F (ULift.algEquiv (R := ℚ) (A := S.F)).symm
  haveI : NumberField (ULift.{u} S.F) :=
    NumberField.of_ringEquiv S.F (ULift.{u} S.F) (ULift.ringEquiv (R := S.F)).symm
  refine ⟨{ n := S.n, hn := S.hn, F := ULift.{u} S.F, x := ULift.up S.x, x_sq := ?_ }⟩
  apply ULift.down_injective
  simp only [ULift.pow_down, ULift.down_algebraMap]
  exact S.x_sq

/-- **Every rational number has a square root in a cyclotomic field**, at every universe level. -/
theorem ExistsSqrtInCyclotomic (d : ℚ) : Nonempty (NK.Chebotarev.SqrtInCyclotomic.{u} d) := by
  exact nonempty_sqrtInCyclotomic_ulift d (nonempty_sqrtInCyclotomic_zero d)

end NK.Chebotarev
