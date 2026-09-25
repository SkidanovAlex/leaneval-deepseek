import Mathlib
import Submission.Work.Tower.CMAdjoin.Basic
import Submission.Work.Tower.CMAdjoin.minpoly_iotaInt
import Submission.Work.Tower.CMAdjoin.four_mem_conductor
import Submission.Work.Tower.CMAdjoin.isSquare_neg_one_zmod
import Submission.Work.Tower.CMAdjoin.quotient_X_sq_add_one_equiv_prod

/-!
# Splitting of a prime of residue field `𝔽_q` (`q ≡ 1 mod 4`) in `L(i)`

For a totally real number field `L`, a prime `q ≡ 1 (mod 4)` and a prime ideal `𝔮` of `𝓞 L`
with residue field `𝔽_q`, the prime `𝔮` splits as a product `𝔔₀ 𝔔₁` of two distinct primes
of `𝓞 (L(i))`, each again with residue field `𝔽_q`.

This is the splitting input of paper Proposition 3.8, Step 4, used to show that rational
primes `≡ 1 (mod 4)` splitting completely in `L` still split completely in `L(i)`.

The proof is the Kummer–Dedekind theorem (`KummerDedekind.quotMapEquivQuotQuotMap`) for the
generator `i = iotaInt L` of `𝓞 (L(i))` over `𝓞 L` (whose minimal polynomial is `X ^ 2 + 1`):
since `4` lies in the conductor (`four_mem_conductor`), the conductor is coprime to `𝔮`,
so `𝓞 (L(i)) ⧸ 𝔮 ≅ (𝓞 L ⧸ 𝔮)[X] / (X ^ 2 + 1) ≅ 𝔽_q × 𝔽_q` because `q ≡ 1 (mod 4)` makes
`X ^ 2 + 1 = (X - r)(X + r)` split with distinct roots in `𝔽_q`.  The two factors of the
product give the two primes.

-/

open NumberField Polynomial

open scoped Classical

namespace Work.Tower.CMAdjoin

/-- If the quotient of a commutative ring by an ideal `I` is a product `F × F` of a field with
itself, then `I` is the product of two distinct primes with quotient `F`: the kernels of the two
components of the quotient. -/
theorem exists_primes_of_quotient_prod_aux {S : Type*} [CommRing S] {I : Ideal S} {F : Type*}
    [Field F] (e : S ⧸ I ≃+* F × F) :
    ∃ 𝔔₀ 𝔔₁ : Ideal S, 𝔔₀.IsPrime ∧ 𝔔₁.IsPrime ∧ 𝔔₀ ≠ 𝔔₁ ∧
      I = 𝔔₀ * 𝔔₁ ∧ Nonempty (S ⧸ 𝔔₀ ≃+* F) ∧ Nonempty (S ⧸ 𝔔₁ ≃+* F) := by
  set φ₀ : S →+* F := (RingHom.fst F F).comp (e.toRingHom.comp (Ideal.Quotient.mk I)) with hφ₀
  set φ₁ : S →+* F := (RingHom.snd F F).comp (e.toRingHom.comp (Ideal.Quotient.mk I)) with hφ₁
  have hsurj₀ : Function.Surjective φ₀ := by
    intro y
    obtain ⟨z, hz⟩ := Ideal.Quotient.mk_surjective (e.symm (y, 0))
    exact ⟨z, by rw [hφ₀]; simp only [RingHom.comp_apply]; rw [hz]; simp⟩
  have hsurj₁ : Function.Surjective φ₁ := by
    intro y
    obtain ⟨z, hz⟩ := Ideal.Quotient.mk_surjective (e.symm (0, y))
    exact ⟨z, by rw [hφ₁]; simp only [RingHom.comp_apply]; rw [hz]; simp⟩
  have hprime₀ : (RingHom.ker φ₀).IsPrime := RingHom.ker_isPrime φ₀
  have hprime₁ : (RingHom.ker φ₁).IsPrime := RingHom.ker_isPrime φ₁
  have hmax₀ : (RingHom.ker φ₀).IsMaximal := RingHom.ker_isMaximal_of_surjective φ₀ hsurj₀
  have hmax₁ : (RingHom.ker φ₁).IsMaximal := RingHom.ker_isMaximal_of_surjective φ₁ hsurj₁
  have hne : RingHom.ker φ₀ ≠ RingHom.ker φ₁ := by
    intro hker
    obtain ⟨w, hw⟩ := Ideal.Quotient.mk_surjective (e.symm ((1 : F), 0))
    have h0 : φ₀ w = 1 := by
      rw [hφ₀]; simp only [RingHom.comp_apply]; rw [hw]; simp
    have h1 : φ₁ w = 0 := by
      rw [hφ₁]; simp only [RingHom.comp_apply]; rw [hw]; simp
    have hw0 : w ∈ RingHom.ker φ₀ := by rw [hker]; exact RingHom.mem_ker.mpr h1
    rw [RingHom.mem_ker] at hw0
    rw [hw0] at h0
    exact one_ne_zero h0.symm
  have hpair : φ₀.prod φ₁ = e.toRingHom.comp (Ideal.Quotient.mk I) := by
    ext x <;> simp [hφ₀, hφ₁, RingHom.prod_apply, RingHom.coe_fst, RingHom.coe_snd]
  have hkerprod : RingHom.ker (φ₀.prod φ₁) = RingHom.ker φ₀ ⊓ RingHom.ker φ₁ := by
    ext x
    simp only [Ideal.mem_inf, RingHom.mem_ker, RingHom.prod_apply, Prod.mk_eq_zero]
  have hsup : RingHom.ker φ₀ ⊔ RingHom.ker φ₁ = ⊤ := hmax₀.coprime_of_ne hmax₁ hne
  have hprod : I = RingHom.ker φ₀ * RingHom.ker φ₁ := by
    have hI : I = RingHom.ker φ₀ ⊓ RingHom.ker φ₁ := by
      rw [← hkerprod, hpair, RingHom.ker_comp_of_injective (Ideal.Quotient.mk I) e.injective,
        Ideal.mk_ker]
    rw [hI, Ideal.mul_eq_inf_of_coprime hsup]
  exact ⟨RingHom.ker φ₀, RingHom.ker φ₁, hprime₀, hprime₁, hne, hprod,
    ⟨RingHom.quotientKerEquivOfSurjective hsurj₀⟩,
    ⟨RingHom.quotientKerEquivOfSurjective hsurj₁⟩⟩

theorem exists_two_primes_over (L : Type*) [Field L] [NumberField L]
    [NumberField.IsTotallyReal L] (q : ℕ) (hq : q.Prime) (h4 : q % 4 = 1)
    (𝔮 : Ideal (NumberField.RingOfIntegers L)) (h𝔮 : 𝔮.IsPrime)
    (hres : Nonempty (NumberField.RingOfIntegers L ⧸ 𝔮 ≃+* ZMod q)) :
    ∃ 𝔔₀ 𝔔₁ : Ideal (NumberField.RingOfIntegers (Work.Tower.CMAdjoin.cmAdjoin L)),
      𝔔₀.IsPrime ∧ 𝔔₁.IsPrime ∧ 𝔔₀ ≠ 𝔔₁ ∧ 𝔔₀.LiesOver 𝔮 ∧ 𝔔₁.LiesOver 𝔮 ∧
      Nonempty (NumberField.RingOfIntegers (Work.Tower.CMAdjoin.cmAdjoin L) ⧸ 𝔔₀ ≃+* ZMod q) ∧
      Nonempty (NumberField.RingOfIntegers (Work.Tower.CMAdjoin.cmAdjoin L) ⧸ 𝔔₁ ≃+* ZMod q) ∧
      𝔮.map (algebraMap (NumberField.RingOfIntegers L)
        (NumberField.RingOfIntegers (Work.Tower.CMAdjoin.cmAdjoin L))) = 𝔔₀ * 𝔔₁ := by
  classical
  haveI : Fact q.Prime := ⟨hq⟩
  haveI : NeZero q := ⟨hq.ne_zero⟩
  obtain ⟨e⟩ := hres
  -- `4` lies in the conductor, viewed in `𝓞 L`
  have h4mem : (4 : 𝓞 L) ∈ (conductor (𝓞 L) (iotaInt L)).comap
      (algebraMap (𝓞 L) (𝓞 (cmAdjoin L))) := by
    rw [Ideal.mem_comap]
    exact four_mem_conductor L
  -- `q` lies in `𝔮`, since the quotient is `ZMod q`
  have hqmem : (q : 𝓞 L) ∈ 𝔮 := by
    have hz : Ideal.Quotient.mk 𝔮 (q : 𝓞 L) = 0 := by
      rw [show Ideal.Quotient.mk 𝔮 (q : 𝓞 L) = ((q : ℕ) : 𝓞 L ⧸ 𝔮) from map_natCast _ q]
      apply e.injective
      rw [map_zero, map_natCast, ZMod.natCast_self]
    exact Ideal.Quotient.eq_zero_iff_mem.mp hz
  -- coprimality of the conductor with `𝔮`
  have hcond : (conductor (𝓞 L) (iotaInt L)).comap (algebraMap (𝓞 L) (𝓞 (cmAdjoin L))) ⊔ 𝔮 = ⊤ := by
    rw [Ideal.eq_top_iff_one]
    obtain ⟨m, hm⟩ : ∃ m : ℕ, q = 4 * m + 1 := ⟨q / 4, by omega⟩
    have hq_cast : (q : 𝓞 L) = 4 * (m : 𝓞 L) + 1 := by rw [hm]; push_cast; ring
    have h1 : (1 : 𝓞 L) = (q : 𝓞 L) * 1 + (m : 𝓞 L) * (-(4 : 𝓞 L)) := by rw [hq_cast]; ring
    rw [h1]
    apply Ideal.add_mem
    · exact Ideal.mem_sup_right (Ideal.mul_mem_right (I := 𝔮) (1 : 𝓞 L) hqmem)
    · exact Ideal.mem_sup_left (Ideal.mul_mem_left _ (m : 𝓞 L) (neg_mem h4mem))
  -- `𝔮` is maximal, since its quotient is the field `ZMod q`
  have hmax : 𝔮.IsMaximal := by
    have hker : RingHom.ker (e.toRingHom.comp (Ideal.Quotient.mk 𝔮)) = 𝔮 := by
      rw [RingHom.ker_comp_of_injective (Ideal.Quotient.mk 𝔮) e.injective, Ideal.mk_ker]
    rw [← hker]
    exact RingHom.ker_isMaximal_of_surjective _
      (e.surjective.comp Ideal.Quotient.mk_surjective)
  haveI : 𝔮.IsMaximal := hmax
  -- Kummer–Dedekind
  have eKD := KummerDedekind.quotMapEquivQuotQuotMap (R := 𝓞 L) (S := 𝓞 (cmAdjoin L))
      (x := iotaInt L) (I := 𝔮) hcond (Algebra.IsIntegral.isIntegral (iotaInt L))
  have eKD' : 𝓞 (cmAdjoin L) ⧸ (𝔮.map (algebraMap (𝓞 L) (𝓞 (cmAdjoin L)))) ≃+*
      (𝓞 L ⧸ 𝔮)[X] ⧸ Ideal.span {(Polynomial.X ^ 2 + 1 : (𝓞 L ⧸ 𝔮)[X])} :=
    eKD.trans (Ideal.quotEquivOfEq (by rw [minpoly_iotaInt L]; simp))
  -- transport the quotient `𝓞 L ⧸ 𝔮 ≅ ZMod q` to the polynomial coefficient ring
  have eP : (𝓞 L ⧸ 𝔮)[X] ⧸ Ideal.span {(Polynomial.X ^ 2 + 1 : (𝓞 L ⧸ 𝔮)[X])} ≃+*
      (ZMod q)[X] ⧸ Ideal.span {(Polynomial.X ^ 2 + 1 : (ZMod q)[X])} :=
    Ideal.quotientEquiv _ _ (Polynomial.mapEquiv e) (by
      have hfix : (↑(Polynomial.mapEquiv e) : (𝓞 L ⧸ 𝔮)[X] →+* (ZMod q)[X])
          (Polynomial.X ^ 2 + 1 : (𝓞 L ⧸ 𝔮)[X]) = (Polynomial.X ^ 2 + 1 : (ZMod q)[X]) := by
        rw [RingEquiv.coe_toRingHom, Polynomial.mapEquiv_apply]
        simp
      rw [Ideal.map_span, Set.image_singleton, hfix])
  -- the splitting `X ^ 2 + 1 = (X - r) (X + r)` in `𝔽_q`
  obtain ⟨r₀, hr₀⟩ := isSquare_neg_one_zmod hq h4
  have hr₀' : r₀ ^ 2 = -1 := by rw [pow_two]; exact hr₀.symm
  have h2 : (2 : ZMod q) ≠ 0 := by
    have h : ((2 : ℕ) : ZMod q) ≠ 0 := by
      rw [Ne, CharP.cast_eq_zero_iff (ZMod q) q 2]
      intro hdvd
      have hq2 : q = 2 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp hdvd
      rw [hq2] at h4
      norm_num at h4
    simpa using h
  have eProd := Classical.choice (quotient_X_sq_add_one_equiv_prod (ZMod q) r₀ hr₀' h2)
  have efinal : 𝓞 (cmAdjoin L) ⧸ (𝔮.map (algebraMap (𝓞 L) (𝓞 (cmAdjoin L)))) ≃+*
      ZMod q × ZMod q := eKD'.trans (eP.trans eProd)
  obtain ⟨𝔔₀, 𝔔₁, hp₀, hp₁, hne, hprod, ⟨res₀⟩, ⟨res₁⟩⟩ :=
    exists_primes_of_quotient_prod_aux efinal
  refine ⟨𝔔₀, 𝔔₁, hp₀, hp₁, hne, ?_, ?_, ⟨res₀⟩, ⟨res₁⟩, hprod⟩
  · rw [Ideal.liesOver_iff_dvd_map hp₀.ne_top]
    exact ⟨𝔔₁, hprod⟩
  · rw [Ideal.liesOver_iff_dvd_map hp₁.ne_top]
    exact ⟨𝔔₀, by rw [hprod, mul_comm]⟩

end Work.Tower.CMAdjoin
