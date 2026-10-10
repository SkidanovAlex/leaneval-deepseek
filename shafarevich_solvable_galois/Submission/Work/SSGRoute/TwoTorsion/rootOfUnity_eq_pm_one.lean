import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.RingTheory.SimpleRing.Principal
import Submission.Work.SSGRoute.TwoTorsion.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute.TwoTorsion

variable {Ω : Type*} [Field Ω] [IsAlgClosed Ω]

/-- A "positive" fixed root of unity is `1`.

Here `normSet c` plays the role of a positivity cone on the fixed field of `c`.  Given that
`normSet c` is closed under addition (`hadd`) and under multiplication, and that `0 ∉ normSet c`,
an element `x` fixed by `c` that lies in `normSet c` and satisfies `x ^ n = 1` must equal `1`:

if `x ≠ 1` then the fixed element `x - 1` is either a norm or the negative of a norm --- this is
the trichotomy `mem_or_neg_mem_normSet` furnished by algebraic closedness of `Ω` (a square root of
`x - 1` is either fixed or anti-fixed).  In the first case one shows by induction that
`x ^ k - 1 ∈ normSet c` for all `k ≥ 1`, in the second that `1 - x ^ k ∈ normSet c`; evaluating at
`k = n` and using `x ^ n = 1` produces `0 ∈ normSet c`, a contradiction. -/
lemma pow_eq_one_of_mem_normSet_fixed {c : Ω ≃+* Ω}
    (hadd : ∀ w ∈ normSet c, ∀ w' ∈ normSet c, w + w' ∈ normSet c)
    {x : Ω} (hx : c x = x) (hxP : x ∈ normSet c) {n : ℕ} (hn : 1 ≤ n) (hxn : x ^ n = 1) :
    x = 1 := by
  by_contra hx1
  have hdfix : c (x - 1) = x - 1 := by rw [map_sub, hx, map_one]
  have hd0 : x - 1 ≠ 0 := sub_ne_zero.mpr hx1
  rcases mem_or_neg_mem_normSet hdfix hd0 with hd | hd
  · -- `x - 1 ∈ normSet c`: show `x ^ k - 1 ∈ normSet c` for all `k ≥ 1`.
    have hkey : ∀ k : ℕ, x ^ (k + 1) - 1 ∈ normSet c := by
      intro k
      induction k with
      | zero => simpa using hd
      | succ j ih =>
        have hstep : x ^ (j + 1 + 1) - 1 = x * (x ^ (j + 1) - 1) + (x - 1) := by
          rw [pow_succ]; ring
        rw [hstep]
        exact hadd _ (normSet.mul_mem hxP ih) _ hd
    have h := hkey (n - 1)
    rw [Nat.sub_add_cancel hn, hxn, sub_self] at h
    exact zero_notMem_normSet h
  · -- `1 - x ∈ normSet c`: show `1 - x ^ k ∈ normSet c` for all `k ≥ 1`.
    have hd' : (1 : Ω) - x ∈ normSet c := by simpa [neg_sub] using hd
    have hkey : ∀ k : ℕ, 1 - x ^ (k + 1) ∈ normSet c := by
      intro k
      induction k with
      | zero => simpa using hd'
      | succ j ih =>
        have hstep : 1 - x ^ (j + 1 + 1) = (1 - x) + x * (1 - x ^ (j + 1)) := by
          rw [pow_succ]; ring
        rw [hstep]
        exact hadd _ hd' _ (normSet.mul_mem hxP ih)
    have h := hkey (n - 1)
    rw [Nat.sub_add_cancel hn, hxn, sub_self] at h
    exact zero_notMem_normSet h

/-- A root of unity fixed by `c` is `±1`.

The fixed field of `c` is formally real because `normSet c` is a positivity cone on it: it contains
`1`, is closed under addition (`hadd`) and multiplication, and does not contain `0`.  A root of
unity fixed by `c` is either a norm or the negative of a norm (`mem_or_neg_mem_normSet`); in the
former case `pow_eq_one_of_mem_normSet_fixed` gives `ζ = 1`, in the latter `ζ ^ 2` is a positive
fixed root of unity, whence `ζ ^ 2 = 1` and `ζ = ±1`. -/
theorem rootOfUnity_eq_pm_one {Ω : Type*} [Field Ω] [IsAlgClosed Ω] [CharZero Ω]
    (c : Ω ≃+* Ω) (hneg : (-1 : Ω) ∉ normSet c)
    (hadd : ∀ w ∈ normSet c, ∀ w' ∈ normSet c, w + w' ∈ normSet c)
    {ζ : Ω} {n : ℕ} (hn : 1 ≤ n) (hfix : c ζ = ζ) (hζ : ζ ^ n = 1) : ζ = 1 ∨ ζ = -1 := by
  have hζ0 : ζ ≠ 0 := by
    rintro rfl
    rw [zero_pow (by omega : n ≠ 0)] at hζ
    exact zero_ne_one hζ
  rcases mem_or_neg_mem_normSet hfix hζ0 with hζP | hnegζP
  · exact Or.inl (pow_eq_one_of_mem_normSet_fixed hadd hfix hζP hn hζ)
  · -- `-ζ` is a norm, so `ζ ^ 2 = ζ * c ζ` is a positive fixed element with `(ζ ^ 2) ^ n = 1`.
    have hsqP : ζ ^ 2 ∈ normSet c := by
      rw [pow_two]
      exact ⟨ζ, hζ0, by rw [hfix]⟩
    have hsqfix : c (ζ ^ 2) = ζ ^ 2 := by rw [map_pow, hfix]
    have hsqn : (ζ ^ 2) ^ n = 1 := by
      rw [pow_two, mul_pow, hζ]
      simp
    have h2 : ζ ^ 2 = 1 := pow_eq_one_of_mem_normSet_fixed hadd hsqfix hsqP hn hsqn
    have hfac : (ζ - 1) * (ζ + 1) = 0 := by
      have : (ζ - 1) * (ζ + 1) = ζ ^ 2 - 1 := by ring
      rw [this, h2, sub_self]
    rcases mul_eq_zero.mp hfac with h | h
    · exact Or.inl (sub_eq_zero.mp h)
    · exact Or.inr (eq_neg_of_add_eq_zero_left h)

end Work.SSGRoute.TwoTorsion
