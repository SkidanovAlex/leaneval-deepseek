import Mathlib

/-!
# Frobenius is surjective on localisations away from one element

If `R` is a perfect ring of characteristic `p` (a prime), then the Frobenius endomorphism
`x ↦ x ^ p` of `R` is bijective.  We show that the same holds for the localisation `R[1/f]`
away from a single element `f`: the localisation of a perfect ring away from one element is
again perfect.

The point is that the only denominators occuring are powers of `f`, and `f` itself has a
`p`-th root `c` in `R` (as does every element).  Explicitly, if `x = a / f ^ n`, pick `b` with
`b ^ p = a` and `c` with `c ^ p = f`; then `b / c ^ n` is a `p`-th root of `x`, and
`b / c ^ n = b * f ^ (-n) * c ^ (n * (p - 1))` with the right hand side manifestly an element
of `R[1/f]`.
-/

namespace Work.DSM5b

/-- Localising a perfect ring of characteristic `p` away from one element keeps Frobenius
surjective: for any `R`-algebra `S` that is the localisation of `R` away from `f`, every element
of `S` is a `p`-th power. -/
theorem frobenius_surjective_away_aux (p : ℕ) [Fact p.Prime] {R : Type*} [CommRing R] [CharP R p]
    [PerfectRing R p] (f : R) {S : Type*} [CommRing S] [Algebra R S] [IsLocalization.Away f S]
    (x : S) : ∃ y : S, y ^ p = x := by
  -- Write `x * f ^ n = a` with `a : R`.
  obtain ⟨n, a, hs⟩ := IsLocalization.Away.surj (x := f) x
  -- Choose `p`-th roots of `a` and of `f`.  Note that `f = 0` is allowed.
  obtain ⟨b, hb⟩ : ∃ b : R, b ^ p = a := ⟨_, frobeniusEquiv_symm_pow_p R p a⟩
  obtain ⟨c, hc⟩ : ∃ c : R, c ^ p = f := ⟨_, frobeniusEquiv_symm_pow_p R p f⟩
  -- `algebraMap f ^ n` is a unit of `S`.
  have hz : IsUnit (algebraMap R S f ^ n) :=
    IsUnit.pow n (IsLocalization.Away.algebraMap_isUnit (x := f))
  have hp1 : 1 ≤ p := (Fact.out : p.Prime).one_le
  -- `algebraMap (c ^ n)` is a `p`-th root of `algebraMap f ^ n`.
  have hv : (algebraMap R S (c ^ n)) ^ p = algebraMap R S f ^ n := by
    rw [← map_pow, ← map_pow, ← hc]
    congr 1
    rw [← pow_mul, ← pow_mul, mul_comm]
  -- Candidate root: `b * (f ^ n)⁻¹ * c ^ (n * (p - 1))`, which is `b / c ^ n` in `S`.
  refine ⟨algebraMap R S b * ↑(hz.unit)⁻¹ * (algebraMap R S (c ^ n)) ^ (p - 1), ?_⟩
  -- Multiplying the candidate by `algebraMap (c ^ n)` gives `algebraMap b`.
  have hyv : algebraMap R S b * ↑(hz.unit)⁻¹ * (algebraMap R S (c ^ n)) ^ (p - 1) *
      (algebraMap R S (c ^ n)) = algebraMap R S b := by
    rw [mul_assoc, ← pow_succ, Nat.sub_add_cancel hp1, hv, mul_assoc, IsUnit.val_inv_mul hz,
      mul_one]
  have hwp : (algebraMap R S b) ^ p = x * algebraMap R S f ^ n := by
    rw [← map_pow, hb]
    exact hs.symm
  -- Hence its `p`-th power agrees with `x` after multiplying by the unit `algebraMap f ^ n`.
  have hyz : (algebraMap R S b * ↑(hz.unit)⁻¹ * (algebraMap R S (c ^ n)) ^ (p - 1)) ^ p *
      (algebraMap R S f ^ n) = x * algebraMap R S f ^ n := by
    have e1 := congrArg (fun t => (algebraMap R S b * ↑(hz.unit)⁻¹ *
      (algebraMap R S (c ^ n)) ^ (p - 1)) ^ p * t) hv.symm
    have e2 := (mul_pow (algebraMap R S b * ↑(hz.unit)⁻¹ * (algebraMap R S (c ^ n)) ^ (p - 1))
      (algebraMap R S (c ^ n)) p).symm
    have e3 := congrArg (fun t => t ^ p) hyv
    exact e1.trans (e2.trans (e3.trans hwp))
  have hZ : algebraMap R S f ^ n * ↑(hz.unit)⁻¹ = 1 := IsUnit.mul_val_inv hz
  -- Cancel the unit `algebraMap f ^ n`.
  calc (algebraMap R S b * ↑(hz.unit)⁻¹ * (algebraMap R S (c ^ n)) ^ (p - 1)) ^ p
      = (algebraMap R S b * ↑(hz.unit)⁻¹ * (algebraMap R S (c ^ n)) ^ (p - 1)) ^ p * 1 :=
        (mul_one _).symm
    _ = (algebraMap R S b * ↑(hz.unit)⁻¹ * (algebraMap R S (c ^ n)) ^ (p - 1)) ^ p *
        (algebraMap R S f ^ n * ↑(hz.unit)⁻¹) :=
          congrArg (fun t => (algebraMap R S b * ↑(hz.unit)⁻¹ *
            (algebraMap R S (c ^ n)) ^ (p - 1)) ^ p * t) hZ.symm
    _ = (algebraMap R S b * ↑(hz.unit)⁻¹ * (algebraMap R S (c ^ n)) ^ (p - 1)) ^ p *
        (algebraMap R S f ^ n) * ↑(hz.unit)⁻¹ := (mul_assoc _ _ _).symm
    _ = x * (algebraMap R S f ^ n) * ↑(hz.unit)⁻¹ :=
          congrArg (fun t => t * ↑(hz.unit)⁻¹) hyz
    _ = x * (algebraMap R S f ^ n * ↑(hz.unit)⁻¹) := mul_assoc _ _ _
    _ = x * 1 := congrArg (fun t => x * t) hZ
    _ = x := mul_one _

/-- Frobenius is surjective on a localisation away from a single element of a perfect ring of
characteristic `p`. -/
theorem frobenius_surjective_away (p : ℕ) [Fact p.Prime] {R : Type*} [CommRing R] [CharP R p]
    [PerfectRing R p] (f : R) (x : Localization.Away f) :
    ∃ y : Localization.Away f, y ^ p = x :=
  frobenius_surjective_away_aux p f x

end Work.DSM5b
