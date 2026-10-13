import Mathlib
import Submission.Work.DSCOH.LocBasisDefs
import Submission.Work.DSCOH.lmb_isRegular_subS

namespace Work.DSCOH

/-- The localization map `M → M[1/X_S]` is injective on the distinguished fractions
`m / X_S^k`: an element of `A[X₀,…,X_{n-1}]` whose class in the chart localization at `S`
vanishes is already zero.  Indeed `subS S` consists of products of variables, all of which are
non-zero-divisors, so the localization is injective. -/
theorem lmb_mk_den_eq_zero {A : Type*} [CommRing A] {n : ℕ} {S : Finset (Fin n)} {k : ℕ}
    {m : Poly A n} (h : LocalizedModule.mk m (den (A := A) S k) = 0) : m = 0 := by
  -- `mk m (den S k)` is `mk' mkLinearMap m (den S k)`, and `mk' f m s = 0` amounts to
  -- `f m = 0` up to multiplication by an element of the submonoid.
  have h' : IsLocalizedModule.mk' (LocalizedModule.mkLinearMap (subS (A := A) S) (Poly A n)) m
      (den (A := A) S k) = 0 := by
    rw [← IsLocalizedModule.mk_eq_mk']
    exact h
  obtain ⟨s', hs'⟩ := (IsLocalizedModule.mk'_eq_zero'
    (f := LocalizedModule.mkLinearMap (subS (A := A) S) (Poly A n))
    (m := m) (den (A := A) S k)).mp h'
  -- `s'` is a product of variables, hence a non-zero-divisor.
  have hs'' : (s' : Poly A n) * m = 0 := by
    simpa only [Submonoid.smul_def, smul_eq_mul] using hs'
  exact (lmb_isRegular_subS S s').left (by simp [hs''])

end Work.DSCOH
