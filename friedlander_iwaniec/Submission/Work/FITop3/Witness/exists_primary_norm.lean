/-
# `Submission.Work.FITop3.Witness.exists_primary_norm`

Every product of primes `≡ 1 (mod 4)` is the norm of a nonzero **primary** Gaussian integer.

This is the witness construction underlying the Friedlander–Iwaniec plan: primary Gaussian
integers are exactly the elements `≡ 1 mod 2(1+i)`; they form a submonoid; and every prime
`p ≡ 1 (mod 4)` splits as `p = π π̄` with exactly one primary associate `π`.

The proof is an induction on the list `L`:
* `[]` — the element `1` is primary of norm `1`;
* `p :: t` — take a primary witness `x` of norm `p` (from Fermat's two-squares theorem together
  with `Commons.NumberTheory.GaussianInt.primary_associate_exists_unique`), a primary witness `y`
  of norm `t.prod` (induction), and multiply; `IsPrimary` is closed under multiplication and
  `gnorm` is multiplicative.
-/
import Mathlib
import Submission.Work.FITop3.Defs3
import Submission.Commons.NumberTheory.GaussianInt.primary_associate_exists_unique

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

namespace Work.FITop3.Witness

open Work.FIPlan

/-! ## Elementary API of `Work.FIPlan.IsPrimary` and `Work.FIPlan.gnorm` -/

/-- The norm `gnorm z = |z|²` is multiplicative. -/
lemma gnorm_mul (z w : GaussianInt) : gnorm (z * w) = gnorm z * gnorm w := by
  simp only [gnorm, Zsqrtd.norm_mul, Int.natAbs_mul]

/-- `gnorm 1 = 1`. -/
lemma gnorm_one : gnorm (1 : GaussianInt) = 1 := by
  norm_num [gnorm, Zsqrtd.norm_def]

/-- `1` is primary. -/
lemma isPrimary_one : IsPrimary (1 : GaussianInt) := by
  refine ⟨?_, ?_, ?_⟩
  · exact odd_one
  · exact ⟨0, by norm_num⟩
  · exact Int.ModEq.refl 0

/-- **Primary elements are closed under multiplication**: `z ≡ w ≡ 1 mod 2(1+i)` implies
`zw ≡ 1 mod 2(1+i)`.  Concretely, for `z = a + bi`, `w = c + di` with `a, c` odd, `b ≡ a-1` and
`d ≡ c-1` modulo `4`, one has `re(zw) = ac - bd` odd, `im(zw) = ad + bc` even, and
`ad + bc - (ac - bd - 1) = 2(ac - a - c + 1) = 2(a-1)(c-1) ≡ 0 (mod 4)`. -/
lemma isPrimary_mul {z w : GaussianInt} (hz : IsPrimary z) (hw : IsPrimary w) :
    IsPrimary (z * w) := by
  obtain ⟨hzo, hze, hzc⟩ := hz
  obtain ⟨hwo, hwe, hwc⟩ := hw
  have hre : (z * w).re = z.re * w.re - z.im * w.im := by
    rw [Zsqrtd.re_mul]; ring
  have him : (z * w).im = z.re * w.im + z.im * w.re := by
    rw [Zsqrtd.im_mul]
  refine ⟨?_, ?_, ?_⟩
  · rw [hre]
    exact (hzo.mul hwo).sub_even (hze.mul_right w.im)
  · rw [him]
    exact (hwe.mul_left z.re).add (hze.mul_right w.re)
  · rw [him, hre]
    have L1 : z.re * w.im ≡ z.re * (w.re - 1) [ZMOD 4] := Int.ModEq.mul_left z.re hwc
    have L2 : z.im * w.re ≡ (z.re - 1) * w.re [ZMOD 4] := Int.ModEq.mul_right w.re hzc
    have hmid : z.re * (w.re - 1) + (z.re - 1) * w.re
        ≡ (z.re * w.re - (z.re - 1) * (w.re - 1)) - 1 [ZMOD 4] := by
      rw [Int.modEq_iff_dvd]
      obtain ⟨k, hk⟩ := hzo
      obtain ⟨l, hl⟩ := hwo
      use -2 * k * l
      rw [hk, hl]; ring
    have hR : z.re * w.re - z.im * w.im - 1
        ≡ z.re * w.re - (z.re - 1) * (w.re - 1) - 1 [ZMOD 4] :=
      ((Int.ModEq.refl (z.re * w.re)).sub (Int.ModEq.mul hzc hwc)).sub (Int.ModEq.refl 1)
    exact (L1.add L2).trans (hmid.trans hR.symm)

/-! ## A prime `≡ 1 (mod 4)` is the norm of a primary element -/

/-- For a prime `p ≡ 1 (mod 4)`, there is a nonzero primary Gaussian integer of norm `p`.
Indeed `p = a² + b²` (Fermat); `z₀ = a + bi` has odd norm `p`, so it has a primary associate `w`
(`primary_associate_exists_unique`), whose norm is still `p`. -/
lemma exists_primary_of_prime (p : ℕ) (hp : p.Prime) (h4 : p % 4 = 1) :
    ∃ z : GaussianInt, z ≠ 0 ∧ IsPrimary z ∧ gnorm z = p := by
  have hne3 : p % 4 ≠ 3 := by omega
  have hp2 : p ≠ 2 := by omega
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨a, b, hab⟩ := Nat.Prime.sq_add_sq (p := p) hne3
  let z0 : GaussianInt := ⟨(a : ℤ), (b : ℤ)⟩
  have hab' : (a : ℤ) ^ 2 + (b : ℤ) ^ 2 = (p : ℤ) := by exact_mod_cast hab
  have hznorm : z0.norm = (p : ℤ) := by
    rw [Zsqrtd.norm_def]
    nlinarith [hab']
  have hz0ne : z0 ≠ 0 := by
    intro h
    rw [h, Zsqrtd.norm_zero] at hznorm
    exact absurd hznorm (by exact_mod_cast (show (0 : ℕ) ≠ p from Ne.symm hp.ne_zero))
  have hodd : Odd z0.norm.natAbs := by
    rw [hznorm, Int.natAbs_natCast]
    exact hp.odd_of_ne_two hp2
  obtain ⟨w, ⟨hwassoc, hwre, hwe, hwc⟩, -⟩ :=
    Commons.NumberTheory.GaussianInt.primary_associate_exists_unique hz0ne hodd
  refine ⟨w, ?_, ?_, ?_⟩
  · intro h
    obtain ⟨u, hu⟩ := hwassoc
    rw [h, zero_mul] at hu
    exact hz0ne hu.symm
  · refine ⟨hwre, hwe, ?_⟩
    have hcast : ((w.im : ℤ) : ZMod 4) = (((w.re - 1 : ℤ)) : ZMod 4) := by
      rw [hwc]; push_cast; ring
    exact (ZMod.intCast_eq_intCast_iff _ _ 4).mp hcast
  · have hg : gnorm w = gnorm z0 := by
      obtain ⟨u, hu⟩ := hwassoc
      have h1 : z0.norm.natAbs = w.norm.natAbs := by
        rw [← hu, Zsqrtd.norm_mul, Int.natAbs_mul,
          Zsqrtd.norm_eq_one_iff.mpr (Units.isUnit u), mul_one]
      exact h1.symm
    rw [hg]
    simp only [gnorm, hznorm, Int.natAbs_natCast]

/-! ## The main statement -/

theorem exists_primary_norm (L : List ℕ) (hL : ∀ p ∈ L, Nat.Prime p)
    (h4 : ∀ p ∈ L, p % 4 = 1) :
    ∃ z : GaussianInt, z ≠ 0 ∧ Work.FIPlan.IsPrimary z ∧ Work.FIPlan.gnorm z = L.prod := by
  induction L with
  | nil => exact ⟨1, one_ne_zero, isPrimary_one, gnorm_one⟩
  | cons p t ih =>
    have hp : p.Prime := hL p (by simp)
    have hp4 : p % 4 = 1 := h4 p (by simp)
    have hLt : ∀ q ∈ t, Nat.Prime q := fun q hq => hL q (by simp [hq])
    have h4t : ∀ q ∈ t, q % 4 = 1 := fun q hq => h4 q (by simp [hq])
    obtain ⟨y, hyne, hyp, hyn⟩ := ih hLt h4t
    obtain ⟨x, hxne, hxp, hxn⟩ := exists_primary_of_prime p hp hp4
    exact ⟨x * y, mul_ne_zero hxne hyne, isPrimary_mul hxp hyp,
      by rw [gnorm_mul, hxn, hyn, List.prod_cons]⟩

end Work.FITop3.Witness
