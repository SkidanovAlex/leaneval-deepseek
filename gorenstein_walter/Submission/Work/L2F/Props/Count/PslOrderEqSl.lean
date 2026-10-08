/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Elements of order an odd prime in `PSL(2,F)` and in `SL(2,F)`

For a finite field `F` of odd characteristic and an odd prime `r`, the number of elements of
`PSL(2,F)` of order `r` equals the number of elements of `SL(2,F)` of order `r`
(`PslOrderEqSl`).

The reason is purely group theoretic.  The canonical map `π : SL(2,F) → PSL(2,F)` is the
quotient by the centre `Z = {1, -1}`; in odd characteristic `Z` has two elements.  For any group
`G` with a central subgroup `N` of exponent `2` and any odd prime `r`, `π : G → G ⧸ N` restricts
to a bijection between the elements of order `r`:

* if `orderOf x = r` then `orderOf (π x) = r`, because `orderOf (π x) ∣ r` and `π x ≠ 1`
  (an `x` of order `r` cannot be central, as then `x ^ 2 = 1`);
* injectivity: `π x = π y` gives `y = x * z` with `z ∈ N` central; `z ^ 2 = 1` and `r` odd give
  `y ^ r = z`, so `z = 1` since `orderOf y = r`;
* surjectivity: for `y` of order `r` and any lift `x`, the element `x * x ^ r` still maps to `y`
  and has `r`-th power `1` (here `x ^ r ∈ N` and `(x ^ r) ^ r = x ^ r`), whence order `r`.

The general statement is `ncard_orderOf_quot_center_eq`; the target theorem is its
specialisation to `G = SL(2,F)`, using `Work.PSL2.card_center_SL2`.
-/
import Mathlib
import Submission.Work.L2F.Props.Count.Defs
import Submission.Work.L2F.Props.Count.CenterCardTwoSqEqOne
import Submission.Work.PSL2.Card

open scoped MatrixGroups

namespace Work.L2F.Props.Count

/-! ## The general group-theoretic bijection -/

/-- If `N` is a central subgroup of exponent (dividing) `2` and `x`, `y` are two elements of odd
order `r` with the same image in `G ⧸ N`, then `x = y`.

`π x = π y` means `y = x * z` with `z ∈ N`.  Since `z` is central it commutes with `x`, so
`y ^ r = x ^ r * z ^ r = z ^ r = z` (using `z ^ 2 = 1` and `r` odd); but `orderOf y = r` forces
`y ^ r = 1`, hence `z = 1`. -/
theorem QuotCentralInjective {G : Type*} [Group G] (N : Subgroup G) [N.Normal]
    (hNc : N ≤ Subgroup.center G) (hN2 : ∀ w ∈ N, w ^ 2 = 1)
    {r : ℕ} (hro : Odd r) {x y : G} (hx : orderOf x = r) (hy : orderOf y = r)
    (h : QuotientGroup.mk' N x = QuotientGroup.mk' N y) : x = y := by
  obtain ⟨z, hzN, hzy⟩ := (QuotientGroup.mk'_eq_mk' N).mp h
  have hcomm : Commute x z := (Subgroup.mem_center_iff.mp (hNc hzN) x)
  have hwr : z ^ r = z := by
    obtain ⟨k, hk⟩ := hro
    rw [hk, pow_succ, pow_mul, hN2 z hzN, one_pow, one_mul]
  have hxr : x ^ r = 1 := by rw [← hx]; exact pow_orderOf_eq_one x
  have hy1 : y ^ r = 1 := by rw [← hy]; exact pow_orderOf_eq_one y
  have h1 : y ^ r = z := by rw [← hzy, hcomm.mul_pow, hxr, hwr, one_mul]
  rw [h1] at hy1
  rw [← hzy, hy1, mul_one]

/-- Every element of order an odd prime `r` of `G ⧸ N` (with `N` central of exponent dividing `2`)
has a lift of order `r`.

For any lift `x` of `y`, the element `x ^ r` lies in `N`, so it commutes with `x` and satisfies
`(x ^ r) ^ 2 = 1`.  Writing `w = x ^ r`, the element `x * w` still maps to `y` and
`(x * w) ^ r = x ^ r * w ^ r = w * w = 1`, while `x * w ≠ 1` because its image is `y ≠ 1`; as `r`
is prime this forces `orderOf (x * w) = r`. -/
theorem QuotCentralLift {G : Type*} [Group G] (N : Subgroup G) [N.Normal]
    (hNc : N ≤ Subgroup.center G) (hN2 : ∀ w ∈ N, w ^ 2 = 1)
    {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) {y : G ⧸ N} (hy : orderOf y = r) :
    ∃ x : G, QuotientGroup.mk' N x = y ∧ orderOf x = r := by
  obtain ⟨x, hx⟩ := QuotientGroup.mk'_surjective N y
  have hro : Odd r := hr.odd_of_ne_two hr2
  set w := x ^ r with hwdef
  have hwN : w ∈ N := by
    rw [← QuotientGroup.ker_mk' N, MonoidHom.mem_ker, hwdef, map_pow, hx,
      show (y : G ⧸ N) ^ r = 1 from by rw [← hy]; exact pow_orderOf_eq_one y]
  have hw1 : QuotientGroup.mk' N w = 1 :=
    MonoidHom.mem_ker.mp (by rwa [QuotientGroup.ker_mk' N])
  have hcomm : Commute x w := (Subgroup.mem_center_iff.mp (hNc hwN) x)
  have hwr : w ^ r = w := by
    obtain ⟨k, hk⟩ := hro
    rw [hk, pow_succ, pow_mul, hN2 w hwN, one_pow, one_mul]
  have hpow : (x * w) ^ r = 1 := by
    rw [hcomm.mul_pow, ← hwdef, hwr, ← pow_two, hN2 w hwN]
  have hyne : y ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at hy
    exact hr.ne_one hy.symm
  have hne1 : x * w ≠ 1 := by
    intro h1
    have h2 : (QuotientGroup.mk' N) (x * w) = 1 := by rw [h1, map_one]
    have h3 : (QuotientGroup.mk' N) x = (QuotientGroup.mk' N) (x * w) := by
      rw [map_mul, hw1, mul_one]
    exact hyne (by rw [← hx, h3, h2])
  refine ⟨x * w, ?_, ?_⟩
  · rw [map_mul, hx, hw1, mul_one]
  · have hdvd : orderOf (x * w) ∣ r := orderOf_dvd_iff_pow_eq_one.mpr hpow
    rcases hr.eq_one_or_self_of_dvd _ hdvd with h | h
    · exact absurd (orderOf_eq_one_iff.mp h) hne1
    · exact h

/-- If the centre of `G` has exactly two elements, then for an odd prime `r` the quotient map
`G → G ⧸ Z(G)` induces a bijection between the elements of order `r`, hence the two sets have the
same cardinality. -/
theorem ncard_orderOf_quot_center_eq {G : Type*} [Group G]
    (hZ : Nat.card (Subgroup.center G) = 2) (r : ℕ) (hr : r.Prime) (hr2 : r ≠ 2) :
    Nat.card {y : G ⧸ Subgroup.center G // orderOf y = r}
      = Nat.card {x : G // orderOf x = r} := by
  have hN2 : ∀ w ∈ Subgroup.center G, w ^ 2 = 1 := CenterCardTwoSqEqOne _ hZ
  have hro : Odd r := hr.odd_of_ne_two hr2
  have hφ : ∀ x : {x : G // orderOf x = r},
      orderOf ((QuotientGroup.mk' (Subgroup.center G)) x.1) = r := by
    rintro ⟨a, ha⟩
    have hdvd : orderOf ((QuotientGroup.mk' (Subgroup.center G)) a) ∣ r := by
      rw [← ha]; exact orderOf_map_dvd _ a
    rcases hr.eq_one_or_self_of_dvd _ hdvd with h | h
    · exfalso
      have hker : a ∈ Subgroup.center G := by
        rw [← QuotientGroup.ker_mk' (Subgroup.center G), MonoidHom.mem_ker]
        exact orderOf_eq_one_iff.mp h
      have h2' : a ^ 2 = 1 := hN2 a hker
      have hdvd2 : r ∣ 2 := by rw [← ha]; exact orderOf_dvd_iff_pow_eq_one.mpr h2'
      rcases (Nat.dvd_prime Nat.prime_two).mp hdvd2 with h1 | h1
      · exact hr.ne_one h1
      · exact hr2 h1
    · exact h
  let φ : {x : G // orderOf x = r} → {y : G ⧸ Subgroup.center G // orderOf y = r} :=
    fun x => ⟨(QuotientGroup.mk' (Subgroup.center G)) x.1, hφ x⟩
  have hbij : Function.Bijective φ := by
    constructor
    · rintro ⟨x, hx⟩ ⟨y, hy⟩ hxy
      have hval : (QuotientGroup.mk' (Subgroup.center G)) x
          = (QuotientGroup.mk' (Subgroup.center G)) y :=
        congrArg Subtype.val hxy
      exact Subtype.ext (QuotCentralInjective (Subgroup.center G) le_rfl hN2 hro hx hy hval)
    · rintro ⟨y, hy⟩
      obtain ⟨x, hx1, hx2⟩ := QuotCentralLift (Subgroup.center G) le_rfl hN2 hr hr2 hy
      exact ⟨⟨x, hx2⟩, Subtype.ext hx1⟩
  exact Nat.card_congr (Equiv.ofBijective φ hbij).symm

/-! ## The target statement -/

/-- For a finite field `F` of odd characteristic and an odd prime `r`, the elements of order `r`
of `PSL(2,F) = SL(2,F)/{±1}` are in bijection with those of `SL(2,F)`. -/
theorem PslOrderEqSl (F : Type*) [Field F] [Fintype F] (h2 : (2 : F) ≠ 0)
    (r : ℕ) (hr : r.Prime) (hr2 : r ≠ 2) :
    Nat.card {y : Matrix.ProjectiveSpecialLinearGroup (Fin 2) F // orderOf y = r}
      = Nat.card {x : Matrix.SpecialLinearGroup (Fin 2) F // orderOf x = r} := by
  have hc : ringChar F ≠ 2 := by
    intro h
    have hdvd : ringChar F ∣ 2 := ⟨1, by rw [h]⟩
    exact h2 ((ringChar.spec F 2).mpr hdvd)
  exact ncard_orderOf_quot_center_eq (G := Matrix.SpecialLinearGroup (Fin 2) F)
    (Work.PSL2.card_center_SL2 F hc) r hr hr2

end Work.L2F.Props.Count
