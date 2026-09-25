import Mathlib

set_option linter.style.haveILetI false
set_option linter.unusedVariables false

namespace Work.Tower

open NumberField Module

/-- For a number field `K` which is Galois over `ℚ`, the discriminant of `K` is a square *in* `K`:
there is `d : K` with `d ^ 2 = discr K`. Indeed, for any `ℚ`-basis `b` of `K` enumerated along the
Galois group, the "Vandermonde" determinant `det (σ (b i))` squares to the discriminant, because
the trace of `b i * b j` is the sum of its Galois conjugates. -/
theorem exists_sq_eq_algebraMap_discr (K : Type*) [Field K] [NumberField K] [IsGalois ℚ K] :
    ∃ d : K, d ^ 2 = algebraMap ℚ K (NumberField.discr K) := by
  classical
  let ι := Module.Free.ChooseBasisIndex ℤ (𝓞 K)
  let b : Module.Basis ι ℚ K := integralBasis K
  have hcard : Fintype.card ι = Fintype.card Gal(K/ℚ) := by
    rw [← Module.finrank_eq_card_basis b, ← Nat.card_eq_fintype_card,
      IsGalois.card_aut_eq_finrank ℚ K]
  let e : ι ≃ Gal(K/ℚ) := Fintype.equivOfCardEq hcard
  let M : Matrix Gal(K/ℚ) Gal(K/ℚ) K := fun σ τ => σ (b (e.symm τ))
  have hMM : M.transpose * M = (Algebra.traceMatrix ℚ (⇑b ∘ ⇑e.symm)).map (algebraMap ℚ K) := by
    ext σ τ
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply,
      Algebra.traceMatrix_apply, Algebra.traceForm_apply, Function.comp_apply]
    rw [trace_eq_sum_automorphisms (b (e.symm σ) * b (e.symm τ))]
    refine Finset.sum_congr rfl fun ρ _ => ?_
    rw [map_mul]
  refine ⟨M.det, ?_⟩
  have h1 : algebraMap ℚ K (Algebra.discr ℚ b) = M.det ^ 2 := by
    rw [← Algebra.discr_reindex ℚ b e]
    rw [Algebra.discr_def, RingHom.map_det, RingHom.mapMatrix_apply, ← hMM, Matrix.det_mul,
      Matrix.det_transpose, pow_two]
  rw [← h1, ← NumberField.coe_discr K, map_intCast]

/-- Arithmetic extraction: if `x ^ m` is a divisor of `r ^ (r - 2)` where `r` is a prime with
`3 * m = r - 1`, if `x ≠ 1` and `x` is a perfect square, then `x = r ^ 2`. Indeed `x = r ^ k`
with `1 ≤ k`, `k * m ≤ r - 2 = 3 * m - 1`, so `k ≤ 2`, and `k = 1` is excluded because a prime
is not a square. -/
theorem sq_eq_prime_sq_of_dvd {r x m : ℕ} (hr : Nat.Prime r) (hm : 3 * m = r - 1)
    (hdiv : x ^ m ∣ r ^ (r - 2)) (hx : x ≠ 1) (hsq : IsSquare x) : x = r ^ 2 := by
  have hm1 : m ≠ 0 := by have := hr.two_le; omega
  have hx0 : x ≠ 0 := by
    rintro rfl
    obtain ⟨c, hc⟩ := hdiv
    rw [zero_pow hm1, zero_mul] at hc
    exact (pow_ne_zero _ hr.ne_zero) hc
  obtain hk : x = r ^ x.primeFactorsList.length :=
    Nat.eq_prime_pow_of_unique_prime_dvd hx0 (fun {d} hd hdx => by
      have hdm : d ∣ x ^ m := dvd_pow hdx hm1
      have hdr : d ∣ r := hd.dvd_of_dvd_pow (dvd_trans hdm hdiv)
      exact (Nat.prime_dvd_prime_iff_eq hd hr).mp hdr)
  set k := x.primeFactorsList.length with hkdef
  have hk1 : 1 ≤ k := by
    rcases Nat.eq_zero_or_pos k with h | h
    · exfalso
      rw [h, pow_zero] at hk
      exact hx hk
    · exact h
  have hkle : k * m ≤ r - 2 := by
    have h2 : x ^ m ≤ r ^ (r - 2) := Nat.le_of_dvd (pow_pos hr.pos _) hdiv
    have h3 : x ^ m = r ^ (k * m) := by rw [hk, pow_mul]
    rw [h3] at h2
    exact (Nat.pow_le_pow_iff_right hr.one_lt).mp h2
  have hk2 : k ≤ 2 := by
    by_contra hcon
    have hcon' : 3 ≤ k := by omega
    have h1 : r - 1 ≤ k * m := by
      rw [← hm]
      exact Nat.mul_le_mul_right m hcon'
    omega
  have hkne : k ≠ 1 := by
    intro hk1'
    rw [hk1', pow_one] at hk
    rw [hk] at hsq
    exact (Nat.prime_iff.mp hr).not_isSquare hsq
  have hk2' : k = 2 := by omega
  rw [hk, hk2']

/-- For a prime `r ≡ 1 (mod 3)`, the cubic subfield `F ⊆ ℚ(ζ_r)` has discriminant of absolute
value `r ^ 2`.

Since `F/ℚ` is abelian (as a subfield of the cyclotomic field `ℚ(ζ_r)`), the tower formula for
the different ideal gives
`r ^ (r - 2) = |disc ℚ(ζ_r)| = |disc F| ^ ((r-1)/3) * N(different of ℚ(ζ_r)/F)`,
so `|disc F|` is a power `r ^ a` of `r`, with `a * (r-1)/3 ≤ r - 2`, hence `a ≤ 2`.
Moreover `disc F` is a square in `ℚ`: the Vandermonde determinant exhibits a square root of
`disc F` inside `F`, and taking norms gives that `(disc F) ^ 3 = (disc F) ^ [F : ℚ]` is a square,
so `disc F` itself is a square. Hence `a = 2` and `|disc F| = r ^ 2`. -/
theorem CubicDiscriminant (r : ℕ) (hr : Nat.Prime r) (hr3 : r % 3 = 1)
    (F : IntermediateField ℚ (CyclotomicField r ℚ))
    (h3 : Module.finrank ℚ ↥F = 3) (hreal : NumberField.IsTotallyReal ↥F) :
    |NumberField.discr ↥F| = (r : ℤ) ^ 2 := by
  haveI : Fact (Nat.Prime r) := ⟨hr⟩
  haveI : NeZero r := ⟨hr.ne_zero⟩
  haveI hcyc : IsCyclotomicExtension {r} ℚ (CyclotomicField r ℚ) :=
    CyclotomicField.isCyclotomicExtension r ℚ
  haveI hab : IsAbelianGalois ℚ (CyclotomicField r ℚ) :=
    IsCyclotomicExtension.isAbelianGalois {r} ℚ (CyclotomicField r ℚ)
  have hmul : 3 * ((r - 1) / 3) = r - 1 := by omega
  have hL : Module.finrank ℚ (CyclotomicField r ℚ) = r - 1 := by
    rw [IsCyclotomicExtension.Rat.finrank r (CyclotomicField r ℚ), Nat.totient_prime hr]
  have hm : Module.finrank ↥F (CyclotomicField r ℚ) = (r - 1) / 3 := by
    have h := Module.finrank_mul_finrank ℚ ↥F (CyclotomicField r ℚ)
    rw [h3, hL] at h
    rw [← h, Nat.mul_div_cancel_left _ (by norm_num : 0 < 3)]
  have hdiscL : (NumberField.discr (CyclotomicField r ℚ)).natAbs = r ^ (r - 2) := by
    rw [IsCyclotomicExtension.Rat.discr_prime r (CyclotomicField r ℚ)]
    simp only [Int.natAbs_mul, Int.natAbs_pow, Int.natAbs_natCast]
    norm_num
  have htower := NumberField.natAbs_discr_eq_absNorm_differentIdeal_mul_natAbs_discr_pow
    ↥F (𝓞 ↥F) (CyclotomicField r ℚ) (𝓞 (CyclotomicField r ℚ))
  rw [hm, hdiscL] at htower
  have hdiv : (NumberField.discr ↥F).natAbs ^ ((r - 1) / 3) ∣ r ^ (r - 2) := by
    refine ⟨Ideal.absNorm (differentIdeal (𝓞 ↥F) (𝓞 (CyclotomicField r ℚ))), ?_⟩
    rw [htower]; exact mul_comm _ _
  have hx1 : (NumberField.discr ↥F).natAbs ≠ 1 := by
    have h := NumberField.abs_discr_gt_two (K := ↥F) (by rw [h3]; norm_num)
    rw [← Int.natCast_natAbs] at h
    omega
  obtain ⟨d, hd⟩ := exists_sq_eq_algebraMap_discr ↥F
  have hsq3 : IsSquare ((NumberField.discr ↥F : ℚ) ^ 3) := by
    refine ⟨Algebra.norm ℚ d, ?_⟩
    have h := congrArg (Algebra.norm ℚ) hd
    simp only [map_pow] at h
    rw [Algebra.norm_algebraMap, h3] at h
    rw [← h, pow_two]
  have hsq : IsSquare ((NumberField.discr ↥F : ℚ)) := by
    obtain ⟨q, hq⟩ := hsq3
    have hx0' : (NumberField.discr ↥F : ℚ) ≠ 0 := by
      rw [Int.cast_ne_zero]; exact NumberField.discr_ne_zero ↥F
    refine ⟨q / (NumberField.discr ↥F : ℚ), ?_⟩
    field_simp
    nlinarith [hq]
  have hsqZ : IsSquare (NumberField.discr ↥F) := Rat.isSquare_intCast_iff.mp hsq
  have hsqNat : IsSquare (NumberField.discr ↥F).natAbs := by
    obtain ⟨m, hm'⟩ := hsqZ
    rw [hm', Int.natAbs_mul]
    exact ⟨m.natAbs, rfl⟩
  have hres := sq_eq_prime_sq_of_dvd hr hmul hdiv hx1 hsqNat
  rw [← Int.natCast_natAbs, hres, Nat.cast_pow]

end Work.Tower
