import Mathlib.RingTheory.DedekindDomain.AdicValuation
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute

/-- **The core localization step.** Let `R` be a Dedekind domain with fraction field `K`, `P` a
height-one prime, and let `ψ : R →+* R` satisfy `ψ x - x ∈ P` for all `x : R` (an "inertia"
condition), realised on `K` by a ring endomorphism `φ` (i.e. `φ ∘ algebraMap = algebraMap ∘ ψ`).
Then for every `y : K` in `valuationSubringAtPrime K P` (that is, `P.valuation K y ≤ 1`), the
difference `φ y - y` lies in the maximal ideal of the local ring at `P`, i.e. has
`P.valuation K`-value `< 1`.

Proof sketch: write `y = n/d` with `n : R`, `d ∈ P.primeCompl` using
`IsDedekindDomain.HeightOneSpectrum.exists_primeCompl_mul_eq_of_integer`. Then
`φ y - y = (ψ n · d - n · ψ d) / (ψ d · d)`; the numerator lies in `P` since it is
`d·(ψ n - n) - n·(ψ d - d)`, and both `d` and `ψ d` are units at `P` (`ψ d ∉ P` follows from
`ψ d - d ∈ P` and `d ∉ P`), so `P.valuation K (ψ d · d) = 1`. Hence
`P.valuation K (φ y - y) = P.valuation K (algebraMap R K (ψ n * d - n * ψ d))`, which is `< 1` by
`IsDedekindDomain.HeightOneSpectrum.valuation_lt_one_iff_mem`. -/
theorem valuation_lt_one_of_inertia {R K : Type*} [CommRing R] [IsDedekindDomain R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    (P : IsDedekindDomain.HeightOneSpectrum R) (φ : K →+* K) (ψ : R →+* R)
    (hφ : ∀ x : R, φ (algebraMap R K x) = algebraMap R K (ψ x))
    (hψ : ∀ x : R, ψ x - x ∈ P.asIdeal)
    {y : K} (hy : P.valuation K y ≤ 1) : P.valuation K (φ y - y) < 1 := by
  -- Write `y = n / d` with `n : R` and `d ∈ P.primeCompl`.
  obtain ⟨n, d, hnd⟩ := P.exists_primeCompl_mul_eq_of_integer y hy
  have hd_notmem : (d : R) ∉ P.asIdeal := d.2
  -- `ψ d ∉ P`, since otherwise `d = ψ d - (ψ d - d) ∈ P`.
  have hψd_notmem : ψ (d : R) ∉ P.asIdeal := by
    intro h
    exact hd_notmem (by
      have h2 := P.asIdeal.sub_mem h (hψ (d : R))
      simpa using h2)
  -- Both `d` and `ψ d` are units at `P`, i.e. have valuation `1`.
  have hval_d : P.valuation K (algebraMap R K (d : R)) = 1 :=
    (P.valuation_eq_one_iff_notMem).mpr hd_notmem
  have hval_ψd : P.valuation K (algebraMap R K (ψ (d : R))) = 1 :=
    (P.valuation_eq_one_iff_notMem).mpr hψd_notmem
  -- The image of `y` satisfies `φ y * ψ d = ψ n`.
  have hφy : φ y * algebraMap R K (ψ (d : R)) = algebraMap R K (ψ n) := by
    rw [← hφ (d : R), ← map_mul, hnd, hφ n]
  -- The key identity `(φ y - y) * (ψ d * d) = ψ n * d - n * ψ d`.
  have key : (φ y - y) * (algebraMap R K (ψ (d : R)) * algebraMap R K (d : R)) =
      algebraMap R K (ψ n * (d : R) - n * ψ (d : R)) := by
    rw [map_sub, map_mul, map_mul, ← hφy, ← hnd]
    ring
  -- Multiplying by an element of valuation `1` does not change the valuation.
  have hprod : P.valuation K ((φ y - y) * (algebraMap R K (ψ (d : R)) * algebraMap R K (d : R)))
      = P.valuation K (φ y - y) := by
    simp [map_mul, hval_ψd, hval_d]
  have hmain : P.valuation K (φ y - y)
      = P.valuation K (algebraMap R K (ψ n * (d : R) - n * ψ (d : R))) := by
    rw [← hprod, key]
  rw [hmain]
  refine (P.valuation_lt_one_iff_mem _).mpr ?_
  -- `ψ n * d - n * ψ d = d * (ψ n - n) - n * (ψ d - d) ∈ P`.
  have h1 : (d : R) * (ψ n - n) ∈ P.asIdeal := P.asIdeal.mul_mem_left _ (hψ n)
  have h2 : n * (ψ (d : R) - (d : R)) ∈ P.asIdeal := P.asIdeal.mul_mem_left _ (hψ (d : R))
  have h3 : (d : R) * (ψ n - n) - n * (ψ (d : R) - (d : R)) ∈ P.asIdeal :=
    P.asIdeal.sub_mem h1 h2
  convert h3 using 1
  ring

end Work.SSGRoute
