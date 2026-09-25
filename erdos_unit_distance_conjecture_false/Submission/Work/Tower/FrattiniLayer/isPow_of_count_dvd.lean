import Mathlib

namespace Work.Tower.FrattiniLayer

/-- If `R` is a Dedekind domain with field of fractions `K` and `I` is a nonzero fractional
ideal whose valuation at every height-one prime is divisible by `n`, then `I` is an `n`-th
power of a fractional ideal: take `J = ∏ᶠ v, v ^ (val_v(I) / n)` and compare factorizations
via `FractionalIdeal.count`. -/
theorem isPow_of_count_dvd {R K : Type*} [CommRing R] [IsDedekindDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K] (n : ℕ) (hn : 0 < n)
    {I : FractionalIdeal (nonZeroDivisors R) K} (hI : I ≠ 0)
    (h : ∀ v : IsDedekindDomain.HeightOneSpectrum R,
      (n : ℤ) ∣ FractionalIdeal.count K v I) :
    ∃ J : FractionalIdeal (nonZeroDivisors R) K, J ^ n = I := by
  classical
  -- The candidate exponents.
  set exps : IsDedekindDomain.HeightOneSpectrum R → ℤ :=
    fun v => FractionalIdeal.count K v I / (n : ℤ) with hexps_def
  have hexps : ∀ v, (n : ℤ) * exps v = FractionalIdeal.count K v I := by
    intro v
    rw [hexps_def]
    exact Int.mul_ediv_cancel' (h v)
  -- The exponents are eventually zero, since the valuations of `I` are.
  have hev : ∀ᶠ v : IsDedekindDomain.HeightOneSpectrum R in Filter.cofinite, exps v = 0 := by
    filter_upwards [FractionalIdeal.finite_factors I] with v hv
    rw [hexps_def]
    simp [hv]
  -- Candidate `n`-th root.
  set J : FractionalIdeal (nonZeroDivisors R) K :=
    ∏ᶠ v : IsDedekindDomain.HeightOneSpectrum R,
      (v.asIdeal : FractionalIdeal (nonZeroDivisors R) K) ^ exps v with hJdef
  have hcount : ∀ v, FractionalIdeal.count K v J = exps v :=
    fun v => FractionalIdeal.count_finprod K v exps hev
  have hJ : J ≠ 0 := by
    rw [hJdef]
    apply finprod_induction (fun x => x ≠ 0) one_ne_zero
      (fun x y hx hy => mul_ne_zero hx hy)
    intro v
    exact zpow_ne_zero _ (FractionalIdeal.coeIdeal_ne_zero.mpr v.ne_bot)
  refine ⟨J, ?_⟩
  have hcountn : ∀ v, FractionalIdeal.count K v (J ^ n) = FractionalIdeal.count K v I := by
    intro v
    rw [FractionalIdeal.count_pow, hcount v, hexps v]
  -- Two nonzero fractional ideals with the same valuations are equal.
  calc J ^ n
      = ∏ᶠ v : IsDedekindDomain.HeightOneSpectrum R,
          (v.asIdeal : FractionalIdeal (nonZeroDivisors R) K) ^
            FractionalIdeal.count K v (J ^ n) :=
        (FractionalIdeal.finprod_heightOneSpectrum_factorization' K (pow_ne_zero n hJ)).symm
    _ = ∏ᶠ v : IsDedekindDomain.HeightOneSpectrum R,
          (v.asIdeal : FractionalIdeal (nonZeroDivisors R) K) ^
            FractionalIdeal.count K v I := by
        apply finprod_congr
        intro v
        rw [hcountn v]
    _ = I := FractionalIdeal.finprod_heightOneSpectrum_factorization' K hI

end Work.Tower.FrattiniLayer
