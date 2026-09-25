import Mathlib

namespace NK.GlobalCFT.IdeleClassGroup

theorem norm_pow_le_norm_of_exp_le {K : Type*} [Field K] [NumberField K]
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) {π : K}
    (hπ : IsDedekindDomain.HeightOneSpectrum.valuation K q π = WithZero.exp (-1 : ℤ))
    {N : ℕ} {y : (q.adicCompletion K)ˣ}
    (hy : WithZero.exp (-(N : ℤ)) ≤ Valued.v (R := q.adicCompletion K) (y : q.adicCompletion K)) :
    ‖(π : q.adicCompletion K)‖ ^ N ≤ ‖(y : q.adicCompletion K)‖ := by
  have hv : Valued.v (R := q.adicCompletion K) (π : q.adicCompletion K) =
      WithZero.exp (-1 : ℤ) := by
    rw [IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
    exact hπ
  calc ‖(π : q.adicCompletion K)‖ ^ N
      = ‖(π : q.adicCompletion K) ^ N‖ := (norm_pow _ _).symm
    _ ≤ ‖(y : q.adicCompletion K)‖ := by
        rw [Valued.toNormedField.norm_le_iff, map_pow, hv]
        rw [← WithZero.exp_nsmul]
        simpa using hy

end NK.GlobalCFT.IdeleClassGroup
