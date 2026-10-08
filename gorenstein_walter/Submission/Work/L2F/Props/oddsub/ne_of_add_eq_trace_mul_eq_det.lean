import Mathlib

namespace Work.L2F.Props.oddsub

theorem ne_of_add_eq_trace_mul_eq_det (F L : Type*) [Field F] [Field L] [Algebra F L]
    (tr de : F) (lam mu : L) (hsum : lam + mu = algebraMap F L tr)
    (hprod : lam * mu = algebraMap F L de)
    (h2 : (2 : F) ≠ 0 ∧ tr ^ 2 - 4 * de ≠ 0 ∨ (2 : F) = 0 ∧ tr ≠ 0) : lam ≠ mu := by
  intro h
  subst h
  -- Now `mu` has been replaced by `lam`, so `lam` is a double root.
  have hroot : tr ^ 2 - 4 * de = 0 := by
    apply FaithfulSMul.algebraMap_injective F L
    rw [map_zero]
    have key : algebraMap F L (tr ^ 2 - 4 * de) = 0 := by
      have e1 : algebraMap F L tr = lam + lam := hsum.symm
      have e2 : algebraMap F L de = lam * lam := hprod.symm
      have hcast : algebraMap F L (tr ^ 2 - 4 * de)
          = (algebraMap F L tr) ^ 2 - 4 * (algebraMap F L de) := by
        simp only [map_sub, map_mul, map_pow, map_ofNat]
      rw [hcast, e1, e2]
      ring
    exact key
  rcases h2 with ⟨_h2ne, hdisc⟩ | ⟨h2eq, htrne⟩
  · exact hdisc hroot
  · -- characteristic 2: `4 = 0`, so `tr ^ 2 = 0`, hence `tr = 0`.
    have h4 : (4 : F) = 0 := by rw [show (4 : F) = 2 * 2 by norm_num, h2eq, mul_zero]
    have htr2 : tr ^ 2 = 0 := by
      have hh := hroot
      rw [h4, zero_mul, sub_zero] at hh
      exact hh
    exact htrne (sq_eq_zero_iff.mp htr2)

end Work.L2F.Props.oddsub
