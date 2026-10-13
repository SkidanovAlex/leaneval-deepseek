import Mathlib
import Submission.Work.DSM1p.Family
import Submission.Work.DSNORM.Main
import Submission.Work.DSREG.Main

namespace Work.DSM1p.Family

/-- **Root extraction from a `p`-th power of a divisibility relation.**

If `A` is a nonzerodivisor element of a domain `S` which is integrally closed in its fraction
field `K`, and `b ^ n = A ^ n * c` with `n > 0`, then `A` divides `b`: indeed `b / A ∈ K` is a
root of `X ^ n - c`, hence integral over `S`, hence lies in `S`.

This is the abstract content of the `stage` divisibility statement: a regular local ring is
integrally closed (`Work.DSNORM.isIntegrallyClosed_of_isRegularLocalRing`). -/
lemma exists_mul_eq_of_pow_eq_pow_mul {S K : Type*} [CommRing S] [IsDomain S] [Field K]
    [Algebra S K] [IsFractionRing S K] [IsIntegrallyClosed S]
    {A b c : S} {n : ℕ} (hn : 0 < n) (h : b ^ n = A ^ n * c) :
    ∃ w : S, b = A * w := by
  by_cases hA : A = 0
  · subst hA
    have hbn : b ^ n = 0 := by
      simpa [zero_pow (Nat.pos_iff_ne_zero.mp hn)] using h
    have hb : b = 0 := eq_zero_of_pow_eq_zero hbn
    exact ⟨0, by simp [hb]⟩
  · have hA' : A ∈ nonZeroDivisors S := mem_nonZeroDivisors_of_ne_zero hA
    set x : K := IsLocalization.mk' K b ⟨A, hA'⟩ with hxdef
    have hspec : algebraMap S K A * x = algebraMap S K b := IsLocalization.mk'_spec' K b ⟨A, hA'⟩
    have hAne : algebraMap S K A ≠ 0 :=
      fun hh => hA (IsFractionRing.injective S K (by simpa using hh))
    have h2 : algebraMap S K (A ^ n) * x ^ n = algebraMap S K (A ^ n) * algebraMap S K c := by
      calc algebraMap S K (A ^ n) * x ^ n
          = (algebraMap S K A) ^ n * x ^ n := by rw [map_pow]
        _ = (algebraMap S K A * x) ^ n := by rw [mul_pow]
        _ = (algebraMap S K b) ^ n := by rw [hspec]
        _ = algebraMap S K (b ^ n) := by rw [map_pow]
        _ = algebraMap S K (A ^ n * c) := by rw [h]
        _ = algebraMap S K (A ^ n) * algebraMap S K c := by rw [map_mul]
    have hAne' : algebraMap S K (A ^ n) ≠ 0 := by
      rw [map_pow]
      exact pow_ne_zero n hAne
    have hx : x ^ n = algebraMap S K c := mul_left_cancel₀ hAne' h2
    have hint : IsIntegral S (x ^ n) := by
      rw [hx]
      exact isIntegral_algebraMap
    obtain ⟨y, hy⟩ := IsIntegrallyClosed.exists_algebraMap_eq_of_isIntegral_pow hn hint
    refine ⟨y, ?_⟩
    have key : algebraMap S K (A * y) = algebraMap S K b := by
      rw [map_mul, hy, hspec]
    exact (IsFractionRing.injective S K key).symm

theorem stage_dvd_pow (R : Type*) [CommRing R] (p : ℕ) [Fact p.Prime] {d : ℕ} (x : Fin d → R)
    (hp : IsSMulRegular R p) (n : ℕ) [IsRegularLocalRing (Work.DSM1p.FamTower R p x n)]
    (b : Work.DSM1p.FamTower R p x n) (k : ℕ)
    (h : ∃ c : Work.DSM1p.FamTower R p x n,
      b ^ p = (p : Work.DSM1p.FamTower R p x n) ^ (k * p) * c) :
    ∃ w : Work.DSM1p.FamTower R p x n, b = (p : Work.DSM1p.FamTower R p x n) ^ k * w := by
  haveI : IsDomain (Work.DSM1p.FamTower R p x n) :=
    Work.DSREG.isDomain_of_isRegularLocalRing _
  haveI : IsIntegrallyClosed (Work.DSM1p.FamTower R p x n) :=
    Work.DSNORM.isIntegrallyClosed_of_isRegularLocalRing _
  obtain ⟨c, hc⟩ := h
  rcases Nat.eq_zero_or_pos k with hk | hk
  · subst hk
    exact ⟨b, by simp⟩
  · have hc' : b ^ p = ((p : Work.DSM1p.FamTower R p x n) ^ k) ^ p * c := by
      rw [hc, pow_mul]
    exact exists_mul_eq_of_pow_eq_pow_mul (S := Work.DSM1p.FamTower R p x n)
      (K := FractionRing (Work.DSM1p.FamTower R p x n)) (Fact.out : p.Prime).pos hc'

end Work.DSM1p.Family
